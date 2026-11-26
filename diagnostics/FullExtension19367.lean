import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19367.Functional

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents


abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next (m) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

/-! ## NOT-free circuits give NOT-free Runs (a copy of run_live with the NOT branch removed) -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem run_nil {α inv meet join y t} (h : @Run α inv meet join y t []) : False := by
  have key : ∀ t ws, @Run α inv meet join y t ws → ws ≠ [] := by
    intro t ws h
    induction h using Run.fold with
    | done => simp
    | perm hp _ ih => exact fun he => ih (List.Perm.eq_nil (he ▸ hp))
    | one => simp
    | two => simp
  exact key t [] h rfl

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | lf : BT
  | nd : BT → List ℕ → BT → BT

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem leqL_self : ∀ a : List ℕ, leqL a a = true
  | [] => rfl
  | a :: s => by simp [leqL, leqL_self s]

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def BT.mem : BT → List ℕ → Bool
  | .lf, _ => false
  | .nd l k r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.toList : BT → List (List ℕ)
  | .lf => []
  | .nd l k r => l.toList ++ k :: r.toList

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .lf, x, h => by simp [BT.mem] at h
  | .nd l k r, x, hm => by
      simp only [BT.mem, Bool.or_eq_true] at hm
      simp only [BT.toList, List.mem_append, List.mem_cons]
      rcases hm with he | hm
      · exact Or.inr (Or.inl (leqL_eq x k he))
      · split at hm
        · exact Or.inl (BT.mem_toList l x hm)
        · exact Or.inr (Or.inr (BT.mem_toList r x hm))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) :
    (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover {p : List ℕ → List (ℕ × ℕ) → Bool} (T : BT) (L : List (List ℕ × List (ℕ × ℕ)))
    (hK : T.toList = L.map Prod.fst) (hL : L.all (fun kh => p kh.1 kh.2) = true) :
    ∀ x, T.mem x = true → ∃ h, p x h = true := by
  intro x hx
  have h1 := BT.mem_toList T x hx
  rw [hK, List.mem_map] at h1
  obtain ⟨kh, hkh, rfl⟩ := h1
  exact ⟨kh.2, List.all_eq_true.1 hL kh hkh⟩

/-- bit `i` is set when some wire differs at points `i` and `d + i` -/
def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)

/-- the union of the wires that are false at point `q` -/
def accM (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => bif Nat.testBit w q then accM q t else Nat.lor w (accM q t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem accM_of (q p : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit p = true →
    w.testBit q = false → (accM q ws).testBit p = true
  | [], w, hw, _, _ => by simp at hw
  | u :: t, w, hw, hp, hq => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · have e : accM q (w :: t) = w ||| accM q t := by simp [accM, hq]
        rw [e, Nat.testBit_or, hp, Bool.true_or]
      · have ih := accM_of q p t w hw' hp hq
        cases hu : Nat.testBit u q
        · have e : accM q (u :: t) = u ||| accM q t := by simp [accM, hu]
          rw [e, Nat.testBit_or, ih, Bool.or_true]
        · have e : accM q (u :: t) = accM q t := by simp [accM, hu]
          rw [e, ih]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem land_of {R X : ℕ} (h : ∀ i, R.testBit i = true → X.testBit i = true) :
    Nat.beq (Nat.land R X) R = true := by
  have he : (R &&& X) = R := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : R.testBit i
    · rfl
    · rw [h i hi]; rfl
  exact Nat.beq_eq_true_eq _ _ ▸ he

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def monoOK (pM : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pM.all fun qp => Nat.beq (Nat.land qp.2 (accM qp.1 ws)) qp.2

def via (y : ℕ) (pD pM : List (ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws &&
    (ws.length != t + 1 || monoOK pM ws)

/-- `pD` entries `(d, R)`: every bit `i` of `R` has `y i ≠ y (d + i)`, both inside the mask.
`pM` entries `(q, P)`: `y q` is false and every bit of `P` is a true point of `y`. -/
def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem via_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} (hp : prsOK m y pD pM = true) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : via y pD pM t ws = true := by
  simp only [prsOK, Bool.and_eq_true, List.all_eq_true] at hp
  have hl := run_len h
  simp only [via, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨by rw [Nat.ble_eq]; exact hl, ?_⟩, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · right; rw [zero_done h rfl]; exact leqL_self _
    · left; simp only [bne_iff_ne, ne_eq]; omega
  · simp only [distOK, List.all_eq_true]
    intro dr hdr
    apply land_of
    intro i hi
    have h12 := hp.1 dr hdr
    have hy : (y ^^^ (y >>> dr.1)).testBit i = true := land_sub h12.1 hi
    have hmx : (m ^^^ (m >>> dr.1)).testBit i = false := land_zero h12.2 hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftRight] at hy hmx
    have hmm : m.testBit i = m.testBit (dr.1 + i) := by
      cases h1 : m.testBit i <;> cases h2 : m.testBit (dr.1 + i) <;> simp_all
    by_contra hc
    have hall : ∀ w ∈ ws, w.testBit i = w.testBit (dr.1 + i) := by
      intro w hw
      by_contra hne
      exact hc (accD_of dr.1 i ws w hw hne)
    have := run_bits h i (dr.1 + i) hmm hall
    rw [this] at hy; simp at hy
  · by_cases hlen : ws.length = t + 1
    · right
      simp only [monoOK, List.all_eq_true]
      intro qp hqp
      have h1 := hp.2 qp hqp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      apply land_of
      intro p hpP
      have hyp : y.testBit p = true := land_sub h1.1 hpP
      by_contra hc
      have hle : ∀ w ∈ ws, w.testBit p ≤ w.testBit qp.1 := by
        intro w hw
        cases h2 : w.testBit p
        · exact Bool.false_le _
        · cases h3 : w.testBit qp.1
          · exact absurd (accM_of qp.1 p ws w hw h2 h3) hc
          · exact le_refl _
      have := bits_le h hlen p qp.1 hle
      rw [hyp, h1.2] at this
      exact absurd this (by decide)
    · left; simpa using hlen

/-- a bit map of tables: bit `k` of `actL pi w` is bit `pi[k]` of `w` (a symmetry of the target) -/
def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem run_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : NatRun m y t (ws.map (actL pi)) := by
  have h2 := Run.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

/-- a successor not stored as it is may be stored up to the symmetry named by its hint -/
def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List (ℕ × ℕ)) (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.lookup tag with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) (T : BT) (t : ℕ)
    (ih : ∀ ws, NatRun m y t ws → T.mem (t :: isort ws) = false)
    (h : List (ℕ × ℕ)) (tag : ℕ) {ys : List ℕ} (hys : NatRun m y t ys) : hfind G T t h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (run_act pi hm hy hys)
    · rfl
  · rfl



abbrev U4 := Bool × Bool × Bool × Bool
abbrev UBank := Bool × Bool × Bool × Bool
def unot (a : U4) : U4 := (!a.1, !a.2.1, !a.2.2.1, !a.2.2.2)
def uand (a b : U4) : U4 := (a.1 && b.1, a.2.1 && b.2.1, a.2.2.1 && b.2.2.1, a.2.2.2 && b.2.2.2)
def uor (a b : U4) : U4 := (a.1 || b.1, a.2.1 || b.2.1, a.2.2.1 || b.2.2.1, a.2.2.2 || b.2.2.2)
def uempty : UBank := (true,true,true,true)
def ucons (a : U4) (r : UBank) : UBank :=
  let quiet := (a.1 == a.2.1) && (a.2.2.1 == a.2.2.2)
  let lo := !a.1 || a.2.1
  let lo' := !a.2.2.1 || a.2.2.2
  let ok := (lo || lo') && ((!a.2.1 || a.1) || (!a.2.2.2 || a.2.2.1))
  (quiet && r.1,(quiet && r.2.1) || (ok && r.1),lo && r.2.2.1,lo' && r.2.2.2)
def uvalid (r : UBank) : Bool :=
  (!r.1 || (r.2.1 && r.2.2.1 && r.2.2.2)) &&
  (!r.2.1 || (r.2.2.1 || r.2.2.2))
def ucost (r : UBank) : Nat := if r.2.1 then 2 else if r.2.2.1 || r.2.2.2 then 1 else 0
def ucalc : List U4 → UBank
  | [] => uempty
  | a :: r => ucons a (ucalc r)
def ukeep (k : Bool) (a : U4) (r : UBank) : UBank := if k then ucons a r else r
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ucalc_ok (xs : List U4) : uvalid (ucalc xs) = true := by
  have c : ∀ (a : U4) (r : UBank), uvalid r = true → uvalid (ucons a r) = true := by decide +kernel
  induction xs with
  | nil => rfl
  | cons a r ih => exact c _ _ ih
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ucalc_perm {xs ys : List U4} (p : xs.Perm ys) : ucalc xs = ucalc ys := by
  have c : ∀ (a b : U4) (r : UBank), ucons a (ucons b r) = ucons b (ucons a r) := by decide +kernel
  induction p with
  | nil => rfl
  | cons a p ih => exact congrArg (ucons a) ih
  | swap a b r => exact c _ _ _
  | trans p q hp hq => exact hp.trans hq
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ucalc_keep (k : Bool) (a : U4) (r : List U4) : ucalc (kept k a r) = ukeep k a (ucalc r) := by
  cases k <;> rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem uoneCost : ∀ (a : U4) (r : UBank) (neg save : Bool), uvalid r = true →
    ucost (ucons a r) ≤ 1 + save.toNat + ucost (ucons (if neg then unot a else a) (ukeep save a r)) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem utwoCost : ∀ (a b : U4) (r : UBank) (op ka kb : Bool), uvalid r = true →
    ucost (ucons a (ucons b r)) ≤ ka.toNat + kb.toNat +
      ucost (ucons (if op then uand a b else uor a b) (ukeep ka a (ukeep kb b r))) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem len_keep4 (k : Bool) (a : U4) (r : List U4) : (kept k a r).length = r.length + k.toNat := by
  cases k <;> simp [kept]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem unate_run {t xs} (h : Run unot uand uor (true,false,true,false) t xs) :
    xs.length + ucost (ucalc xs) ≤ t + 1 := by
  induction h using Run.fold with
  | done => decide
  | perm hp _ ih => rwa [← hp.length_eq, ← ucalc_perm hp]
  | @one s a r neg save h ih =>
    have hc := uoneCost a (ucalc r) neg save (ucalc_ok r)
    simp only [List.length_cons, ucalc, ucalc_keep, len_keep4] at ih ⊢
    omega
  | @two s a b r op ka kb h ih =>
    have hc := utwoCost a b (ucalc r) op ka kb (ucalc_ok r)
    simp only [List.length_cons, ucalc, ucalc_keep, len_keep4] at ih ⊢
    omega
def probe (p n q m : Nat) (w : Nat) : U4 := (w.testBit p,w.testBit n,w.testBit q,w.testBit m)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem probe_run {M Y t xs} (h : NatRun M Y t xs) (p n q m : Nat)
    (hf : probe p n q m M = (true,true,true,true)) (hy : probe p n q m Y = (true,false,true,false)) :
    xs.length + ucost (ucalc (xs.map (probe p n q m))) ≤ t+1 := by
  have eqs : M.testBit p = true ∧ M.testBit n = true ∧ M.testBit q = true ∧ M.testBit m = true := by
    simpa [probe, Prod.mk.injEq] using hf
  have hi : ∀ a, probe p n q m (a ^^^ M) = unot (probe p n q m a) := by
    intro a
    simp [probe, unot, Nat.testBit_xor, eqs.1, eqs.2.1, eqs.2.2.1, eqs.2.2.2]
  have hm : ∀ a b, probe p n q m (a &&& b) = uand (probe p n q m a) (probe p n q m b) := by
    intros; simp [probe,uand,Nat.testBit_and]
  have hj : ∀ a b, probe p n q m (a ||| b) = uor (probe p n q m a) (probe p n q m b) := by
    intros; simp [probe,uor,Nat.testBit_or]
  have hh := Run.map (probe p n q m) hi hm hj h
  rw [hy] at hh
  simpa using unate_run hh

def ucheck (M Y t : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  if hint = 0 then true else
  let z := hint - 1
  let f := probe (z/32768) ((z/1024)%32) ((z/32)%32) (z%32)
  if f M = (true,true,true,true) ∧ f Y = (true,false,true,false) then
    Nat.ble (ws.length + ucost (ucalc (ws.map f))) (t+1)
  else true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ucheck_sound {M Y t ws} (h : NatRun M Y t ws) (i : Nat) : ucheck M Y t ws i = true := by
  unfold ucheck
  split
  · rfl
  · dsimp only
    split
    · rename_i hh
      exact Nat.ble_eq.mpr (probe_run h _ _ _ _ hh.1 hh.2)
    · rfl
def probeRoots : List (List Nat × Nat) := []
def urootHint (ws : List Nat) : Nat := (probeRoots.lookup (isort ws)).getD 0

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && ucheck m y t ys ((h.lookup tag).getD 0) && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closure_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true) :
    ∀ t ws, NatRun m y t ws → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp [stepOK] at hs
  | succ t ih =>
    intro ws hw
    cases hm : T.mem ((t + 1) :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp only [stepOK, Bool.not_eq_true'] at hs
      have hperm : (isort ws).Perm ws := List.perm_insertionSort _ _
      have hr : NatRun m y (t + 1) (isort ws) := Run.perm hperm.symm hw
      have hn := next_complete hr t rfl (isort ws) (List.Perm.refl _)
        (fun tag ys => via y pD pM t ys && ucheck m y t ys ((h.lookup tag).getD 0) && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ucheck_sound hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || !ucheck m y cap zs (urootHint zs) || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK m y pD pM G T cap) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hmem := List.all_eq_true.1 hi _ (List.mem_sublists.2 hsub)
  revert hr hmem
  cases ws with
  | nil => intro hr _; exact run_nil hr
  | cons a r =>
    intro hr hmem
    have hcap : NatRun m y cap (a :: r) := extend_run hr hs'
    have hd := via_sound hp hcap
    have hc := closure_sound T hp hG hT cap (a :: r) hcap
    have hg : (G.any fun pi => T.mem (cap :: isort ((a :: r).map (actL pi)))) = false := by
      rw [List.any_eq_false]
      intro pi hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hpi
      rw [closure_sound T hp hG hT cap _ (run_act pi hm hy hcap)]
      simp
    unfold rootOK at hmem
    rw [hd, ucheck_sound hcap, hc, hg] at hmem
    simp at hmem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_cert {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK m y pD pM G T cap) = true) :
    ∀ s, HasCircuitSize n f s → lb ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hr : NatRun m (encL f l) s' (ws.map fun a => encL a l) :=
    Run.map (fun a : BFn n => encL a l) (fun a => by rw [hm]; exact encL_inv a l)
      (fun a b => encL_and a b l) (fun a b => encL_or a b l) hrun
  rw [hy] at hr
  have hsub' : (ws.map fun a => encL a l).Sublist xs := by rw [← hxs]; exact hsub.map _
  exact cert_core hp hG hT hi (by omega) hsub' hr



def pairCode (p : Fin 5 × Fin 5) : Nat := 2 ^ p.1.val ||| 2 ^ (5 + p.2.val)
def reference (x : Fin 10 → Bool) : Bool :=
  (x 1 || x 5 || x 0 || x 6 || x 7) && !((x 1 || x 5) && (x 0 || x 6 || x 7 || x 8))
def pairInput (i j : Fin 5) := PEqualNP.Represents.oneEach i j
theorem codeInputs : ∀ p : Fin 5 × Fin 5, List.ofFn (pt 10 (pairCode p)) = pairInput p.1 p.2 := by decide +kernel
theorem graphRow : ∀ i j : Fin 5, reference (pt 10 (pairCode (i,j))) =
   (7577150 : ℕ).testBit (5 * i.val + j.val) := by decide +kernel
def samplePairs : List (Fin 5 × Fin 5) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def M_ : ℕ := 33554431
def Y_ : ℕ := 7577150
def PD_ : List (ℕ × ℕ) := [(1, 4870433), (2, 7305649), (3, 4058617), (4, 1353693), (5, 719), (6, 151622), (7, 227586), (8, 126368), (9, 42993), (10, 729), (11, 4173), (12, 6407), (13, 3490), (14, 2032), (15, 729), (16, 77), (17, 7), (18, 34), (19, 48), (20, 25), (21, 13), (22, 7), (23, 2)]
def PM_ : List (ℕ × ℕ) := [(0, 7577150), (6, 7577150), (7, 7577150), (8, 7577150), (13, 7577150), (14, 7577150), (18, 7577150), (19, 7577150), (23, 7577150), (24, 7577150)]
def G_ : List (List ℕ) := [[0, 2, 1, 3, 4, 5, 7, 6, 8, 9, 10, 12, 11, 13, 14, 15, 17, 16, 18, 19, 20, 22, 21, 23, 24], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24, 15, 16, 17, 18, 19], [0, 2, 1, 3, 4, 5, 7, 6, 8, 9, 10, 12, 11, 13, 14, 20, 22, 21, 23, 24, 15, 17, 16, 18, 19], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 18, 19, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24], [0, 2, 1, 3, 4, 5, 7, 6, 8, 9, 15, 17, 16, 18, 19, 10, 12, 11, 13, 14, 20, 22, 21, 23, 24], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 10, 11, 12, 13, 14], [0, 2, 1, 3, 4, 5, 7, 6, 8, 9, 15, 17, 16, 18, 19, 20, 22, 21, 23, 24, 10, 12, 11, 13, 14], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 20, 21, 22, 23, 24, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], [0, 2, 1, 3, 4, 5, 7, 6, 8, 9, 20, 22, 21, 23, 24, 10, 12, 11, 13, 14, 15, 17, 16, 18, 19], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 20, 21, 22, 23, 24, 15, 16, 17, 18, 19, 10, 11, 12, 13, 14], [0, 2, 1, 3, 4, 5, 7, 6, 8, 9, 20, 22, 21, 23, 24, 15, 17, 16, 18, 19, 10, 12, 11, 13, 14]]
def hintValues : Array Nat := #[0,1,3,5,7,32903,32935,32943,39073,39233,40097,41121,41255,41281,46241,46247,46248,46369,46377,46401,46439,47265,47271,47393,47399,47425,47431,47463,47470,47623,51681,52385,52583,52590,52705,52743,65672,65704,71841,73889,79009,79169,80033,80193,80231,80232,98473,98663,104481,104609,104769,104815,104929,105089,105633,105793,105953,106657,106817,106977,107137,111777,111783,111784,111785,111913,111937,112097,112257,112801,112961,112979,112984,112999,116897,117039,117057,117095,117217,117377,122017,122177,122337,122497,131111,131407,137249,145441,145569,145697,145729,145767,150849,151009,151047,163879,163880,163881,163887,163911,163943,164167,164199,164206,170017,170049,170081,170113,170273,170281,170287,170351,171041,171073,171105,172065,172071,172097,172104,172129,172161,177185,177191,177192,177217,177224,177249,177511,178209,178215,178216,178241,178247,178248,178273,178279,178305,178503,178529,178535,178542,178568,182305,182337,183329,183335,183361,183368,183393,183425,301231,301377,301423,303143,303144,303176,303463,308263,308264,308265,308296,308297,308329,308583,308743,309281,309287,309288,309289,309313,309319,309320,309345,309351,309353,309377,309383,309384,309415,309575,309607,309608,309639,309640,309767,313383,313416,314401,314407,314408,314440,314478,314695,314696,314727,314734,314887,320167,327783,327790,335905,335937,335969,341025,341057,342049,342081,342113,342145,366639,366735,366895,368807,368935,373927,374945,374951,375079,407713,407720,491635,530484]
def decodeHints (xs : List Nat) : List (Nat × Nat) := xs.map fun w => (w / 256, hintValues[w % 256]?.getD 0)
def keyAt (xs : List (List Nat × List (Nat × Nat))) (i : Nat) : List Nat := (xs.getD i ([],[])).1
noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,1083105,6494431],(decodeHints [115,523,1139,1651])),([3,1083361,6494687],(decodeHints [121,526,1145,1657])),([3,6494431,32471326],(decodeHints [11,609,1035,1651])),([3,8659934,17318431],(decodeHints [6,520,1030,1542])),([3,17318431,24894497],(decodeHints [8,607,1032,1542])),([4,31,1082913,25977848],(decodeHints [50,616,1074,1586,2098,2610,18952,21041])),([4,31,1083105,6494406],(decodeHints [57,631,1081,1593,2105,2617,18804,19059])),([4,31,1083361,6494662],(decodeHints [61,638,1085,1597,2109,2621,18810,19065])),([4,31,6494406,32471326],(decodeHints [57,724,1081,1593,2105,2617,14649,15060])),([4,31,8659934,17318416],(decodeHints [8,518,1032,1544,2056,2568,18694,18950])),([4,31,9742313,15153614],(decodeHints [49,648,1073,1585,2097,2609])),([4,31,9742313,18400817],(decodeHints [49,648,1073,1585,2097,2609])),([4,31,17318416,24894497],(decodeHints [8,662,1032,1544,2056,2568,14600,14998])),([4,31,18400817,23812118],(decodeHints [49,618,1073,1585,2097,2609])),([4,33,8659967,17318431],(decodeHints [104,538,1128,1640,2152,2664,14952,15720])),([4,193,1083361,6494431,8659208],(decodeHints [14464,18560,24710])),([4,256,1083361,6494431],(decodeHints [121,633,1145,1550,2169,2681,14969,15737,18809,19065])),([4,287,1083361,6494406],(decodeHints [61,638,1085,1597,2109,2621,18810,19065])),([4,543,1082401,25977848],(decodeHints [50,616,1074,1586,2098,2610,18952,21041])),([4,704,1082401,6494431],(decodeHints [153,627,1177,1689,2201,2713,14745,14963])),([4,736,1082401,6494431],(decodeHints [153,712,1177,1689,2201,2713,14745,15048])),([4,990,8659208,17318431],(decodeHints [6,520,1030,1542,2054,2566,14598,14856,20742])),([4,992,1082401,6494687],(decodeHints [157,715,1181,1693,2205,2717,14749,15051])),([4,992,1082913,6494431],(decodeHints [115,627,1139,1555,2163,2675,14606,19039,19827])),([4,1082401,6494431,33553695],(decodeHints [200,524,1224,1736,2248,2713,19059,19912])),([4,1082401,8659967,16236000],(decodeHints [104,539,1128,1640,2152,2664,14952,15720])),([4,1082401,8659967,17318431],(decodeHints [104,539,1128,1640,2152,2664,14952,15720])),([4,1082401,9742335,17318431],(decodeHints [104,539,1128,1640,2152,2664,14952,15720])),([4,1082401,17318431,24894464],(decodeHints [104,520,1128,1640,2152,2664,18696,18952])),([4,1083105,2164802,4329631],(decodeHints [117,724,1141,1653,2165,2677,20851,21108])),([4,1083361,2164802,4329887],(decodeHints [124,726,1148,1660,2172,2684,20857,21114])),([4,1083361,2164831,4329860],(decodeHints [121,526,1145,1657,2169,2681,20857,21113])),([4,1083361,6494431,8659208],(decodeHints [128,533,1152,1664,2176,2688,18709,20089,21120])),([4,1083361,6494431,8659231],(decodeHints [128,527,1152,1664,2176,2688,20090,21120])),([4,1083361,6494431,10824010],(decodeHints [129,526,1153,1665,2177,2689,20089,21120])),([4,1083361,6494431,10824031],(decodeHints [128,528,1152,1664,2176,2688,20091,21120])),([4,1083361,6494431,15153614],(decodeHints [129,526,1153,1665,2177,2689,20089,21120])),([4,1083361,6494431,18400817],(decodeHints [129,526,1153,1665,2177,2689,19982,21120])),([4,1083361,6494431,24895223],(decodeHints [128,533,1152,1664,2176,2688,19840,19982,21120])),([4,1083361,8659208,27060000],(decodeHints [128,610,1152,1664,2176,2688,14638,15993,21888])),([4,1083361,8659231,18400831],(decodeHints [128,533,1152,1664,2176,2688])),([4,2164802,4329631,32471326],(decodeHints [212,551,1236,1748,2260,2677,14804,14887])),([4,2164831,9742313,12988812],(decodeHints [21,640,1045,1557,2069,2581])),([4,6494431,8659208,9742313],(decodeHints [21,558,1045,1557,2069,2581,21013,21781])),([4,6494431,8659208,32471070],(decodeHints [21,610,1045,1557,2069,2688,14855,20750,21013])),([4,8659208,17318431,33553441],(decodeHints [8,520,1032,1631,2056,2566,14696,18990,19720])),([4,8659967,17318431,32472030],(decodeHints [27,520,1051,1563,2075,2664,19739,19974])),([4,9742313,18400817,33554400],(decodeHints [136,618,1160,1672,2184,2609])),([5,1,1082431,8659944,17318416],(decodeHints [180,692,1204,1716,2228,2712,3252,3764,15028,15796,18840,19124,21172,25012,25268,27316])),([5,27,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25192,26930,27186])),([5,31,33,8659944,17318416],(decodeHints [104,616,1128,1715,2152,2664,3176,3688,14693,18952,21041,25192,27059,27315])),([5,31,33,8659967,17318416],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,18952,19720,21000,21768,24936,25192,26888,27144])),([5,31,256,1083361,6494406],(decodeHints [61,638,1085,1597,2109,2621,3133,3645,14653,14974,21053,21821,24954,25209,26941,27197])),([5,31,512,1082401,25977848],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,14642,14952,20786,21042,25096,27186,27954,29233])),([5,31,704,1082401,6494406],(decodeHints [57,668,1081,1593,2105,2617,3129,3641,14649,15004,20793,21049,24985,25244,28985,29241])),([5,31,736,1082401,6494406],(decodeHints [58,668,1082,1594,2106,2618,3130,3642,14687,14856,20793,21050,24985,25244,28986,29242])),([5,31,736,1082401,25977624],(decodeHints [58,668,1082,1594,2106,2618,3130,3642,14687,14856,20793,25244,28986,29242])),([5,31,990,8659208,17318416],(decodeHints [8,518,1032,1544,2056,2568,3080,3592,18950,20744,21000,24838,25094,28936,29192])),([5,31,992,1082401,6494662],(decodeHints [66,675,1090,1602,2114,2626,3138,3650,14687,14856,20797,21058,24989,25251,28994,29250])),([5,31,992,1082401,25977368],(decodeHints [66,675,1090,1602,2114,2626,3138,3650,14687,14856,20797,25251,28994,29250])),([5,31,992,1082657,25977624],(decodeHints [66,675,1090,1602,2114,2626,3138,3650,14687,14856,20797,25251])),([5,31,992,1082913,6494406],(decodeHints [66,631,1090,1602,2114,2626,3138,3650,14687,14856,20797,24951,25203,27202,27961,28994,29250])),([5,31,992,1082913,25977624],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,14687,14856,20797,25192,26938,27202,29250])),([5,31,992,7576807,9741609],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,26937]))]
noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,992,7576807,15153614],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,21058])),([5,31,992,7576807,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,21058])),([5,31,992,7576807,23812822],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,27961])),([5,31,992,9741609,15153614],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,20793,21058])),([5,31,992,9741609,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,20793,21058])),([5,31,992,9741609,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,20793])),([5,31,992,9742313,18400817],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,14692,14897,15921,20785,21058,21826,26941,27954])),([5,31,992,9764137,25977624],(decodeHints [66,708,1090,1602,2114,2626,3138,3650,14687,14856,20793])),([5,31,992,15153614,23812822],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,27202,27961])),([5,31,992,15153614,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,27202])),([5,31,992,18400817,23812822],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,27202,27961])),([5,31,992,18400817,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,27202])),([5,31,992,18400817,25977848],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,14658,14952,21810,27202,27970])),([5,31,992,18415153,25977624],(decodeHints [76,676,1100,1612,2124,2636,3148,3660,14687,14856,27212])),([5,31,992,23812822,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,14687,14856,21817])),([5,31,1023,9741609,18400817],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,14856,15624,20744])),([5,31,1023,9741609,25977624],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,14856,15624,20744,22024])),([5,31,1023,18400817,25977624],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,14856,15624,22024])),([5,31,31744,9742313,18400817],(decodeHints [49,661,1073,1585,2097,2609,3121,3633,14791,14914,15921,20785,21809,26929,27953])),([5,31,33825,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25192,26930,27186])),([5,31,1082401,6494406,33553695],(decodeHints [58,714,1082,1594,2106,2618,3130,3642,18890,19144,20794,21050,25146,25914,27193,27962])),([5,31,1082401,8659912,17318416],(decodeHints [49,692,1073,1585,2097,2609,3121,3633,16050,19124,20785,21041,25268,26929,27185])),([5,31,1082401,8659936,17318416],(decodeHints [90,616,1114,1626,2138,2650,3162,3674,18792,18952,21080,25192,26970,27226])),([5,31,1082401,8659944,15153614],(decodeHints [50,720,1074,1586,2098,2610,3122,3634,18952,20786,21041,25293,26930,27186])),([5,31,1082401,8659944,16236000],(decodeHints [104,616,1128,1716,2152,2664,3176,3688,14772,18792,19048,21098,24936,25138,27161])),([5,31,1082401,8659944,16236015],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25138,27186,27954])),([5,31,1082401,8659944,16236031],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25138,25906,27186,27954])),([5,31,1082401,8659944,17318400],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,24936,25192,26930,27186])),([5,31,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25192,26930,27186])),([5,31,1082401,8659944,17318417],(decodeHints [107,619,1131,1716,2155,2667,3179,3691,14772,19051,21172,25192,27186])),([5,31,1082401,8659944,17318418],(decodeHints [25,617,1049,1561,2073,2585,3097,3609,18982,21013,25192,26905,27161])),([5,31,1082401,8659944,17318424],(decodeHints [90,616,1114,1626,2138,2650,3162,3674,18792,18952,21080,25192,26970,27226])),([5,31,1082401,8659944,17318431],(decodeHints [104,616,1128,1716,2152,2664,3176,3688,14772,18792,19048,21098,25192,25960,27161])),([5,31,1082401,8659944,17318448],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,16009,19124,20786,21042,25268,26930,27186])),([5,31,1082401,8659944,17319440],(decodeHints [52,616,1076,1588,2100,2612,3124,3636,18952,21041,25113,27186])),([5,31,1082401,8659944,18400817],(decodeHints [50,720,1074,1586,2098,2610,3122,3634,18952,20786,21041,25113,27186,27954])),([5,31,1082401,8659944,18400831],(decodeHints [25,717,1049,1561,2073,2585,3097,3609,18893,19149,20761,21013,25113,25881,27161,27929])),([5,31,1082401,8659945,17318416],(decodeHints [49,618,1073,1585,2097,2609,3121,3633,18952,21041,21809,25194,26929,27185])),([5,31,1082401,8659946,17318416],(decodeHints [9,617,1033,1545,2057,2569,3081,3593,18952,21000,25193,26889,27145])),([5,31,1082401,8659960,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,24936,25192,26930,27186])),([5,31,1082401,8659967,16236015],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,18952,19720,21000,21768,25096,25864,27144,27912])),([5,31,1082401,8659967,17318416],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,18952,19720,21000,21768,24936,25192,26888,27144])),([5,31,1082401,8659967,17318431],(decodeHints [104,616,1128,1716,2152,2664,3176,3688,14772,15643,18792,19048,19816,21096,21864,24936,25192,25960,27341])),([5,31,1082401,8659967,18400817],(decodeHints [8,720,1032,1544,2056,2568,3080,3592,18952,19720,21000,25293,27144,27912])),([5,31,1082401,8660968,17318416],(decodeHints [52,616,1076,1588,2100,2612,3124,3636,18952,21041,25192,26932,27188])),([5,31,1082401,9742313,16236015],(decodeHints [49,618,1073,1585,2097,2609,3121,3633,18952,21041,21809,25137,27185,27953])),([5,31,1082401,9742313,17318416],(decodeHints [49,618,1073,1585,2097,2609,3121,3633,18952,21041,21809,25194,26929,27185])),([5,31,1082401,9742313,17318431],(decodeHints [106,618,1130,1716,2154,2666,3178,3690,14772,18794,19048,21098,21866,25194,25962,27157])),([5,31,1082401,9742313,18400817],(decodeHints [49,692,1073,1585,2097,2609,3121,3633,15023,16011,18952,20785,21041,21809,25109,26929,27185,27953])),([5,31,1082401,9742335,17318416],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,18952,19720,21000,21768,24936,25192,26888,27144])),([5,31,1082401,16236015,24894487],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18994,21042,21810,25178,27185])),([5,31,1082401,17318416,23812118],(decodeHints [49,618,1073,1585,2097,2609,3121,3633,19050,20785,21041,25192,26929,27185])),([5,31,1082401,17318416,24894464],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,18792,19048,20744,21000,24936,25178,26888,27144])),([5,31,1082401,17318416,24894487],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,19048,20786,21042,25178,27185])),([5,31,1082401,17318416,24894495],(decodeHints [90,616,1114,1626,2138,2650,3162,3674,19048,20826,21082,25178,25946,27224])),([5,31,1082401,17318416,24894519],(decodeHints [49,664,1073,1585,2097,2609,3121,3633,16022,19096,20785,21041,25176,27185,27953])),([5,31,1082401,17318431,24894487],(decodeHints [104,616,1128,1688,2152,2664,3176,3688,14743,19048,19816,21017,25192,25960,27288])),([5,31,1082401,18400817,24894487],(decodeHints [50,720,1074,1586,2098,2610,3122,3634,18969,21042,21810,25178,27185,27954])),([5,31,1082401,25977368,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,19048,20802,21058,25154,25922,27197])),([5,31,1082401,25977624,33553695],(decodeHints [58,616,1082,1594,2106,2618,3130,3642,19048,20794,21050,25146,25914,27193])),([5,31,1082409,8659944,17318416],(decodeHints [90,616,1114,1626,2138,2650,3162,3674,18736,25192,26970,27226])),([5,31,1082417,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,24919,26930])),([5,31,1082913,8659208,17318896],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,19048,20802,21058,25096,27197,28994,29242])),([5,31,1082913,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25192,26930,27186,28978,29234]))]
noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,1083105,2164802,4329604],(decodeHints [57,631,1081,1593,2105,2617,3129,3641,18432,18804,19059,24950,25205,28985,29241])),([5,31,1083361,2164802,4329860],(decodeHints [61,638,1085,1597,2109,2621,3133,3645,18810,19065,24957,25212,28989,29245])),([5,31,1083361,6494406,8659208],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,18817,19072,25222,26937,28221,28989,29245])),([5,31,1083361,6494406,8659231],(decodeHints [134,646,1158,1752,2182,2694,3206,3718,14808,18822,19072,25222,25990,28287,29056,29318])),([5,31,1083361,6494406,10824010],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,18817,19075,25222,28221,29245])),([5,31,1083361,6494406,15153614],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,18817,19080,21053,25222,28221,29245,30013])),([5,31,1083361,6494406,18400817],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,18817,19080,21053,25157,28221,28989,29245])),([5,31,1083361,6494406,24895223],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,18817,19072,25157,27961,28221,29245,30013])),([5,31,1083361,6494431,8659208],(decodeHints [128,640,1152,1752,2176,2688,3200,3712,14807,15745,18816,19072,19840,24960,25216,25984,27096,28281,29056,29312])),([5,31,1083361,8659208,15153614],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,19080,20793,21053,25216,29245,30013])),([5,31,1083361,8659208,18400817],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,19080,20793,21053,25109,28989,29245])),([5,31,1083361,8659208,18400831],(decodeHints [21,640,1045,1557,2069,2581,3093,3605,18816,19072,20757,21013,25109,25877,28949,29205])),([5,31,1083361,8659208,27060025],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,19078,20793,22077,25109,25917,29245,30013])),([5,31,1083361,8659231,18400817],(decodeHints [136,648,1160,1647,2184,2696,3208,3720,14703,19080,19848,21006,24968,25216,28942,29312])),([5,31,1083361,8659944,18400817],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,18958,20786,21053,25113,27954,28989])),([5,31,1083361,9741609,18400817],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,14856,18958,20793,21053,25109,28989])),([5,31,1083361,9741609,25977624],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,14856,19005,20793,22077,25260])),([5,31,1083361,9742313,18400817],(decodeHints [61,623,1085,1597,2109,2621,3133,3645,14897,16011,18958,20785,21053,21821,25109,26941,27953,28989])),([5,31,1083361,10824010,12988812],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,19072,25219])),([5,31,1083361,18400817,24895223],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,18965,25176,27197,27961,29245,30013])),([5,31,1083361,18400817,25977624],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,14856,19013,22077,25105,27197,29245])),([5,31,1083361,18400817,27060025],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,19013,22077,25102,25917,27197,29245,30013])),([5,31,1084449,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25192,26930,27186])),([5,31,1098785,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25192,26930])),([5,31,2164802,4329604,32471326],(decodeHints [57,724,1081,1593,2105,2617,3129,3641,14336,14649,15060,18900,19156,20793,21049])),([5,31,2164802,9742313,12988812],(decodeHints [54,728,1078,1590,2102,2614,3126,3638,14646,15064,26934,27190])),([5,31,2164802,9742313,18400817],(decodeHints [54,648,1078,1590,2102,2614,3126,3638,14646,14984,15921,20785,21814,26934,27190,27953])),([5,31,3247203,8659944,18400817],(decodeHints [55,720,1079,1591,2103,2615,3127,3639,18952,20786,27954])),([5,31,3247203,8659944,19483218],(decodeHints [55,625,1079,1591,2103,2615,3127,3639,18952])),([5,31,6494406,8659208,9742313],(decodeHints [57,728,1081,1593,2105,2617,3129,3641,14649,15064,20793,21049,29241,30009])),([5,31,6494406,8659208,32471070],(decodeHints [61,728,1085,1597,2109,2621,3133,3645,14653,15064,19160,20797,21053,28989,29241])),([5,31,8659208,9742313,18400817],(decodeHints [57,648,1081,1593,2105,2617,3129,3641,14984,15960,20785,21049,21817,25109,26937,27193,27953])),([5,31,8659208,9742313,27060025],(decodeHints [57,558,1081,1593,2105,2617,3129,3641,21049,21817,25109,25913,27193,27961])),([5,31,8659208,17318416,33553441],(decodeHints [8,662,1032,1544,2056,2568,3080,3592,14998,18696,19094,20744,21000,27144,27912])),([5,31,8659208,18400817,32471070],(decodeHints [61,623,1085,1597,2109,2621,3133,3645,14959,18965,20797,21053,27193,27965])),([5,31,8659912,17318416,32472030],(decodeHints [49,692,1073,1585,2097,2609,3121,3633,15028,19124,26290,27185,27953,29233,30001])),([5,31,8659944,9741609,18400817],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,14856,20793,21042,25113,30002])),([5,31,8659944,9741609,25977624],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,14856,20793,25135])),([5,31,8659944,9742313,18400817],(decodeHints [50,720,1074,1586,2098,2610,3122,3634,14897,15960,20785,21042,21810,25113,26929,27954,30002])),([5,31,8659944,15153614,17318416],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,14856,27186,28978,29234])),([5,31,8659944,16236015,18400817],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,14856,21042,30002,30258])),([5,31,8659944,16236015,32472030],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,14856,18994,27953,30002,30258])),([5,31,8659944,17318416,18400817],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,14856,21042,29234,30002])),([5,31,8659944,17318416,32472030],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,14856,19124,27953,29234,30002])),([5,31,8659944,17318416,32473054],(decodeHints [52,691,1076,1588,2100,2612,3124,3636,14856,19123,27953,29236,30004])),([5,31,8659944,17318431,32472030],(decodeHints [180,692,1204,1688,2228,2740,3252,3688,14643,15028,19124,19892,26036,28084,29977])),([5,31,8659944,17318896,18400817],(decodeHints [66,652,1090,1602,2114,2626,3138,3650,14988,21042,30002])),([5,31,8659944,18400817,19483218],(decodeHints [55,692,1079,1591,2103,2615,3127,3639,14856,27186,30258])),([5,31,8659944,18400817,25977624],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,14856,27186,30258])),([5,31,8659944,18400817,25977848],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,14952,21810,27186,27954,30258])),([5,31,8659944,18400817,32472030],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,14856,18969,27186,27953,30002,30258])),([5,31,8659967,17318416,18400817],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,14856,15624,18779,28168,29192,29960])),([5,31,8659967,17318416,32472030],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,14856,15624,18779,19124,27912,28168,29192,29960])),([5,31,9741609,9742313,18400817],(decodeHints [57,692,1081,1593,2105,2617,3129,3641,14905,16011,18952,20785,21049,21817,26937,27953])),([5,31,9741609,9742313,25977624],(decodeHints [57,621,1081,1593,2105,2617,3129,3641,14905,18952,21049,21817])),([5,31,9741609,18400817,33553439],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,25154,25922,27193,27970])),([5,31,9741609,25977624,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,25154,25922,27193])),([5,31,9742313,17318416,18400817],(decodeHints [49,692,1073,1585,2097,2609,3121,3633,14856,19033,20017,21041,22065,28209,28977,29233,30001])),([5,31,9742313,17318416,32472030],(decodeHints [49,692,1073,1585,2097,2609,3121,3633,14856,19124,27953,28209,29233,30001])),([5,31,9742313,18400817],(decodeHints [392,904,1329,1841,2353,2865,15153,16267,19288,20360,21297,22321])),([5,31,17318416,18400817,24894487],(decodeHints [50,597,1074,1586,2098,2610,3122,3634,21042,21810,25178,27954])),([5,31,17318416,24894487,32472030],(decodeHints [50,664,1074,1586,2098,2610,3122,3634,15000,19034,27186,27954,30001])),([5,31,18400817,25977624,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,25154,25922,30018])),([5,33,1023,8659208,17318431],(decodeHints [104,538,1128,1640,2152,2664,3176,3688,14952,15720,18714,19063,20840,21096,29032]))]
noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1082401,8659944,17318416],(decodeHints [50,614,1074,1586,2098,2610,3122,3634,15973,20786,25190,26930,27186])),([5,256,992,1082401,6494431],(decodeHints [157,669,1181,1739,2205,2717,3229,3741,15005,15773,18845,19101,20893,21195,24989,25245])),([5,256,1083361,2164802,4329631],(decodeHints [124,636,1148,1750,2172,2684,3196,3708,14972,15740,18432,18812,19068,24956,25212,29049,29306])),([5,287,992,1082401,6494406],(decodeHints [65,674,1089,1601,2113,2625,3137,3649,20797,21056,24989,25247,28993,29249])),([5,287,992,1082401,25977624],(decodeHints [65,674,1089,1601,2113,2625,3137,3649,20797,25106,28993,29249])),([5,287,1083361,2164802,4329604],(decodeHints [61,638,1085,1597,2109,2621,3133,3645,18432,18810,19065,24957,25212,28989,29245])),([5,512,992,1082401,6494431],(decodeHints [115,627,1139,1651,2163,2579,3187,3699,14963,15731,18707,19059,20750,24947,25203,27231,28019])),([5,543,992,1082401,6494406],(decodeHints [66,631,1090,1602,2114,2626,3138,3650,14856,20797,24951,25203,27202,27961,28994,29250])),([5,543,992,1082401,25977624],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,14856,20797,25192,26938,27202,28994,29250])),([5,543,1082401,8659208,17318896],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,19048,20802,21058,25096,27197,28994,29242])),([5,543,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25192,26930,27186,28978,29234])),([5,736,1082401,2164802,4329631],(decodeHints [155,713,1179,1691,2203,2715,3227,3739,14747,15049,20891,21147,29082,29337])),([5,992,1023,9741609,18400817],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,14943,15711,19044])),([5,992,1023,9741609,25977624],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,14943,15711,22120])),([5,992,1023,18400817,25977624],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,14943,15711,22120,25154])),([5,992,1082401,2164802,4329887],(decodeHints [160,716,1184,1696,2208,2720,3232,3744,14752,15052,20896,21152,29086,29341])),([5,992,1082401,2164831,4329860],(decodeHints [157,715,1181,1693,2205,2717,3229,3741,14749,15051,27037,27293,29085,29341])),([5,992,1082401,6494431,8659208],(decodeHints [166,717,1190,1702,2214,2726,3238,3750,14758,15053,25037,26269,27046,27302,29350])),([5,992,1082401,6494431,8659231],(decodeHints [180,717,1204,1716,2228,2740,3252,3764,14772,15053,21172,25037,26269,27316,29350])),([5,992,1082401,6494431,8682760],(decodeHints [188,715,1212,1724,2236,2748,3260,3772,14780,15051,25032,26269,27324,29372])),([5,992,1082401,6494431,9741609],(decodeHints [166,631,1190,1702,2214,2726,3238,3750,14758,24951,26269,27302,28070,29350])),([5,992,1082401,6494431,10824010],(decodeHints [166,718,1190,1702,2214,2726,3238,3750,14758,15054,26270,27046,27302,29350])),([5,992,1082401,6494431,10824031],(decodeHints [166,717,1190,1702,2214,2726,3238,3750,14758,15053,21158,26270,27302,29350])),([5,992,1082401,6494431,15153614],(decodeHints [166,720,1190,1702,2214,2726,3238,3750,14758,15056,19039,26315,27046,27302,29350])),([5,992,1082401,6494431,16236015],(decodeHints [166,627,1190,1702,2214,2726,3238,3750,14758,19039,26227,27302,28070,29350])),([5,992,1082401,6494431,17318416],(decodeHints [166,627,1190,1702,2214,2726,3238,3750,14758,19039,26227,27046,27302,29350])),([5,992,1082401,6494431,17318431],(decodeHints [180,627,1204,1716,2228,2740,3252,3764,14772,19048,21172,26227,27316,29350])),([5,992,1082401,6494431,17333776],(decodeHints [157,627,1181,1693,2205,2717,3229,3741,14749,19039,26227,27293,29341])),([5,992,1082401,6494431,18400817],(decodeHints [166,720,1190,1702,2214,2726,3238,3750,14758,15056,19039,26315,27302,28070,29350])),([5,992,1082401,6494431,19483218],(decodeHints [166,629,1190,1702,2214,2726,3238,3750,14758,26227,27046,27302,29350])),([5,992,1082401,6494431,19483231],(decodeHints [166,627,1190,1702,2214,2726,3238,3750,14758,21158,26227,27302,29350])),([5,992,1082401,6494431,23812822],(decodeHints [166,631,1190,1702,2214,2726,3238,3750,14758,26022,26227,27046,27302,29350])),([5,992,1082401,6494431,23812831],(decodeHints [166,627,1190,1702,2214,2726,3238,3750,14758,21158,26022,26227,27302,29350,30118])),([5,992,1082401,6494431,24895223],(decodeHints [166,717,1190,1702,2214,2726,3238,3750,14758,15053,26022,26315,27302,28070,29350])),([5,992,1082401,6495231,17318416],(decodeHints [95,616,1119,1631,2143,2655,3167,3679,19039,19807,24936,26207,26975,27231,30303])),([5,992,1082401,8659208,27060000],(decodeHints [166,717,1190,1702,2214,2726,3238,3750,14758,15053,18893,20125,20902,21158,30118])),([5,992,1082401,8659231,16236000],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,14772,18792,19048,21172,27316])),([5,992,1082401,8659231,17318431],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,14772,18792,19048,21172,27316])),([5,992,1082401,8659231,18400831],(decodeHints [180,717,1204,1716,2228,2740,3252,3764,14772,15053,18893,19149,27316,28084])),([5,992,1082401,8659967,17318431],(decodeHints [104,616,1128,1564,2152,2664,3176,3688,14700,15643,18792,19048,19816,21096,21864,24936,25960,27341])),([5,992,1082401,9741631,17318431],(decodeHints [180,627,1204,1716,2228,2740,3252,3764,14772,18803,19048,21172,21940])),([5,992,1082401,10824031,19483231],(decodeHints [166,624,1190,1702,2214,2726,3238,3750,14758,21158,27302])),([5,992,1082401,17318416,27060000],(decodeHints [166,627,1190,1702,2214,2726,3238,3750,14758,20083,20902,21158,25192,30118])),([5,992,1082401,17318431,24895200],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,14772,21172,25268,26036,27316])),([5,992,1082913,2164802,4329631],(decodeHints [117,629,1141,1577,2165,2677,3189,3701,14632,19049,20742,21096,25183,29043,29301])),([5,992,1083361,6494431,8659208],(decodeHints [205,717,1229,1558,2253,2765,3277,3789,14613,15053,15821,18893,19840,25037,25984,26315,26902,28363,29389])),([5,992,1113121,8659231,17318431],(decodeHints [196,616,1220,1732,2244,2756,3268,3780,14702,18792,19048])),([5,992,2164831,5412005,9741609],(decodeHints [166,536,1190,1702,2214,2726,3238,3750,24853])),([5,992,2164831,5412005,12988812],(decodeHints [166,536,1190,1702,2214,2726,3238,3750,18966])),([5,992,2164831,5412005,18400817],(decodeHints [166,531,1190,1702,2214,2726,3238,3750,14943,18963])),([5,992,2164831,5412005,21648020],(decodeHints [166,531,1190,1702,2214,2726,3238,3750,14943])),([5,992,2164831,9741609,12988812],(decodeHints [166,536,1190,1702,2214,2726,3238,3750,18709,18966])),([5,992,2164831,9741609,18400817],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,14943,18745,19010])),([5,992,2164831,9741609,25977624],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,14943,18745])),([5,992,2164831,18400817,21648020],(decodeHints [166,531,1190,1702,2214,2726,3238,3750,14943,25220])),([5,992,2164831,18400817,25977624],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,14943,25223])),([5,992,6494431,8659208,9741609],(decodeHints [166,536,1190,1702,2214,2726,3238,3750,18712,24853,25110,29350,30118])),([5,992,6494431,8659208,23812822],(decodeHints [166,536,1190,1702,2214,2726,3238,3750,18712,25217,26022,29094,29350])),([5,992,6494431,8659208,32472030],(decodeHints [166,536,1190,1702,2214,2726,3238,3750,18712,20125,21158,25217,26022,29350,30118])),([5,992,6494431,15153614,17318416],(decodeHints [166,531,1190,1702,2214,2726,3238,3750,14943,25107,29094,29350])),([5,992,6494431,17318416,18400817],(decodeHints [166,531,1190,1702,2214,2726,3238,3750,14943,18963,29350,30118])),([5,992,6494431,17318416,32472030],(decodeHints [166,531,1190,1702,2214,2726,3238,3750,14943,19987,21158,26022,29350,30118])),([5,992,8659231,17318431,32472030],(decodeHints [180,540,1204,1716,2228,2740,3252,3764,14772,14876,26036,28084,30132])),([5,992,9741609,18400817,33554400],(decodeHints [180,720,1204,1716,2228,2740,3252,3650,14772,15056,25268,26036]))]
noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([5,992,9741609,25977624,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3650,14701,25268,26036])),([5,992,18400817,25977624,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3650,19048,25268,26036])),([5,1023,1082401,6494406,17318431],(decodeHints [73,631,1097,1609,2121,2633,3145,3657,14711,19048,20809,21065,26120,28955])),([5,1023,1082401,8659208,16236000],(decodeHints [27,616,1051,1563,2075,2587,3099,3611,14696,15976,18792,19048,20763,21019,29979])),([5,1023,1082401,8659208,17318431],(decodeHints [27,616,1051,1563,2075,2587,3099,3611,14696,15976,18792,19048,20763,21019,28955])),([5,1023,1082401,8659231,17318431],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,14696,15976,18792,19048,21172,27316,28955])),([5,1023,1082401,8659944,17318431],(decodeHints [104,616,1128,1587,2152,2664,3176,3688,14696,15976,18792,19048,21098,25960,27161,29032])),([5,1023,1082401,8659967,17318431],(decodeHints [104,616,1128,1544,2152,2664,3176,3688,14696,15643,15976,18792,19048,19816,21096,21864,24936,25960,29032])),([5,1023,1082401,9741609,17318431],(decodeHints [27,631,1051,1563,2075,2587,3099,3611,14711,18807,19048,21019,21787,28955])),([5,1023,1082401,17318431,24895223],(decodeHints [27,616,1051,1563,2075,2587,3099,3611,14696,15976,25115,25883,27163,27931,29211])),([5,1023,1082401,17318431,25977624],(decodeHints [73,616,1097,1609,2121,2633,3145,3657,14696,15976,19976,25192,26953,27209,29211])),([5,1023,1082401,17318431,25977631],(decodeHints [27,616,1051,1563,2075,2587,3099,3611,14696,15976,20072,21019,25192,27163,29211,29979])),([5,1023,1113121,8659208,17318431],(decodeHints [35,616,1059,1571,2083,2595,3107,3619,14696,15976,18792,19048,20771,28963])),([5,1023,6494406,8659208,17318896],(decodeHints [66,517,1090,1602,2114,2626,3138,3650,14597,15877,20802,21058])),([5,1023,8659208,9741609,17318431],(decodeHints [27,558,1051,1563,2075,2587,3099,3611,14638,18734,20072,21019,21787])),([5,1023,8659208,17318431,32472030],(decodeHints [27,520,1051,1563,2075,2587,3099,3611,14619,14856,20763,25883,26118,27163,27931])),([5,1023,8659208,17318896,18400817],(decodeHints [66,596,1090,1602,2114,2626,3138,3650,14932,20802,26198,26946,27202])),([5,2079,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25192,26930,27186])),([5,31744,1082401,8659967,17318431],(decodeHints [104,616,1128,1569,2152,2664,3176,3688,14625,14952,15720,18792,19816,21096,21864,24936,25960])),([5,31744,1083361,6494431,8659208],(decodeHints [144,656,1168,1567,2192,2704,3216,3728,14730,15744,18832,19840,24976,25232,25984,26911,28302,29328])),([5,31744,8659208,17318431,33522721],(decodeHints [209,520,1233,1745,2257,2769,3281,3590,14663,20945,24840,25096,27345])),([5,1047552,8659208,17318431,32539681],(decodeHints [209,520,1233,1745,2257,2769,3281,3590,14664,20945,24840,25096,27345])),([5,1082401,1082431,8659944,17318431],(decodeHints [180,692,1204,1716,2228,2711,3252,3764,15028,15796,18839,19124,20840,21172,26036,28008])),([5,1082401,1083361,6494431,8659208],(decodeHints [166,678,1190,1557,2214,2726,3238,3750,14613,15014,15782,18853,19841,24998,25254,25984,26901,28317,29350])),([5,1082401,1083361,6494431,17318416],(decodeHints [166,678,1190,1550,2214,2726,3238,3750,15014,15782,18853,24998,25254,28174,29350])),([5,1082401,1083361,8659231,17318431],(decodeHints [180,692,1204,1564,2228,2740,3252,3764,15028,15796,18853,19124,20840,21100,24997,25268])),([5,1082401,1083391,8659208,17318431],(decodeHints [104,539,1128,1640,2152,2664,3176,3688,14952,15720,18715,19063,20840,21096,29032])),([5,1082401,2164802,4329631,33553695],(decodeHints [201,725,1225,1737,2249,2761,3273,3739,14598,14952,20936,21193,25205,26057])),([5,1082401,2164802,8659967,17318431],(decodeHints [113,556,1137,1649,2161,2673,3185,3697,14598,14952,15976,19057,19825,20840,21873,26992,28009])),([5,1082401,2164831,8659944,12988812],(decodeHints [205,536,1229,1741,2253,2765,3277,3789,18710,18965,24856,25201])),([5,1082401,2164831,8659944,17318431],(decodeHints [112,692,1136,1648,2160,2672,3184,3696,14952,19058,20840,25293,28008])),([5,1082401,2164831,8659944,19483218],(decodeHints [113,536,1137,1649,2161,2673,3185,3697,19058,24856,25293])),([5,1082401,6494431,8659208,8659944],(decodeHints [205,536,1229,1741,2253,2765,3277,3789,18712,18968,24854,25109,29389,30157])),([5,1082401,6494431,8659208,33553439],(decodeHints [205,536,1229,1741,2253,2765,3277,3750,18712,19063,21197,25216,26061,29131,29389])),([5,1082401,6494431,17318416,33553439],(decodeHints [115,531,1139,1651,2163,2675,3187,3750,18707,19152,21107,25209,28008,29043])),([5,1082401,8659208,8659967,17318431],(decodeHints [104,539,1128,1640,2152,2664,3176,3688,14638,14967,15976,19048,19816,20840,21096,21864,26984,28008])),([5,1082401,8659208,17318431,33553408],(decodeHints [104,520,1128,1640,2152,2664,3176,3611,14638,14967,20840,24840,25096,27240,28008])),([5,1082401,8659231,8659944,17318431],(decodeHints [104,692,1128,1640,2152,2664,3176,3688,14963,19050,20840,21096,25293,28008])),([5,1082401,8659231,8659967,17318431],(decodeHints [104,692,1128,1640,2152,2664,3176,3688,14963,15899,19048,19816,20840,21096,21864,25293,26984,28008])),([5,1082401,8659231,17318431,33553439],(decodeHints [104,540,1128,1640,2152,2664,3176,3764,14963,19149,25116,27240,28008])),([5,1082401,8659936,17318416,33554400],(decodeHints [104,692,1128,1640,2152,2664,3176,3674,15028,18868,19152,27240,28008,30056])),([5,1082401,8659944,8659967,17318431],(decodeHints [104,563,1128,1640,2152,2664,3176,3688,14954,15899,19048,19816,20840,21096,21864,25293,26984,28008,30056])),([5,1082401,8659944,16236015,33554400],(decodeHints [104,692,1128,1640,2152,2664,3176,3634,14954,19048,19816,28008,30056])),([5,1082401,8659944,17318400,33554400],(decodeHints [104,692,1128,1640,2152,2664,3176,3634,14954,18868,19124,28008,29288,30056])),([5,1082401,8659944,17318416,33554400],(decodeHints [104,692,1128,1640,2152,2664,3176,3634,14954,18868,19152,28008,30056])),([5,1082401,8659944,17318416,33554402],(decodeHints [105,678,1129,1641,2153,2665,3177,3634,14954,18854,19152,28009,30057])),([5,1082401,8659944,17318431,33554400],(decodeHints [104,692,1128,1640,2152,2664,3176,3688,14954,19149,25268,27240,28008,30056,30312])),([5,1082401,8659944,18400817,33554400],(decodeHints [208,692,1232,1744,2256,2768,3280,3634,14800,15028,19152,19920,28112,30157])),([5,1082401,8659967,17318416,17318431],(decodeHints [104,603,1128,1640,2152,2664,3176,3688,14952,15720,18779,19035,20072,21096,22120,28168,29032,29288,30056])),([5,1082401,8659967,17318416,33554400],(decodeHints [104,692,1128,1640,2152,2664,3176,3592,14952,15720,18868,19152,28008,28264,29288,30056])),([5,1082401,8659967,17318431],(decodeHints [283,795,1384,1896,2408,2920,15208,16155,19227,20251,21352,22376])),([5,1082401,9742313,17318416,33554400],(decodeHints [106,692,1130,1642,2154,2666,3178,3633,14954,15722,18868,19124,28008,30058])),([5,1082401,17318416,24894487,33554400],(decodeHints [104,664,1128,1640,2152,2664,3176,3634,14677,15056,19096,28008,30056])),([5,1082431,1083361,8659208,17318431],(decodeHints [23,677,1047,1559,2071,2583,3095,3607,18853,19109,20759,21015,28951,29207])),([5,1082431,1083361,8659231,17318416],(decodeHints [165,677,1189,1688,2213,2725,3237,3749,24997,25253,29093,29349])),([5,1083361,2164802,4329631,8659208],(decodeHints [131,728,1155,1667,2179,2691,3203,3715,20864,21121,25048,26236,27011,27267,29315])),([5,1083361,2164802,4329631,8659231],(decodeHints [131,728,1155,1667,2179,2691,3203,3715,20864,21123,26237,27008,27267,29315])),([5,1083361,2164802,4329631,10824010],(decodeHints [131,554,1155,1667,2179,2691,3203,3715,14890,20867,21121,26236,27267,28035,29315])),([5,1083361,2164802,4329631,12988812],(decodeHints [133,728,1157,1669,2181,2693,3205,3717,20480,20864,21121,26236,27013,27269,29315])),([5,1083361,2164802,4329631,12988831],(decodeHints [131,728,1155,1667,2179,2691,3203,3715,19160,20480,20864,21123,26239,27008,27267,29315,30083])),([5,1083361,2164802,4329631,18400817],(decodeHints [133,552,1157,1669,2181,2693,3205,3717,14888,20866,21121,26152,27013,27269,29315])),([5,1083361,2164802,4329631,24895223],(decodeHints [131,728,1155,1667,2179,2691,3203,3715,20864,21121,25987,26326,27267,28035,29315])),([5,1083361,2164802,6494431,8659208],(decodeHints [129,554,1153,1665,2177,2689,3201,3713,14890,16000,20864,21121,21889,24874,26234,27009,27265,28032,29313])),([5,1083361,2164802,8659208,29224800],(decodeHints [131,728,1155,1667,2179,2691,3203,3715,18904,20092,20867,21123,27265,28032,30083]))]
noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([5,1083361,2164831,4329631,8659208],(decodeHints [128,728,1152,1664,2176,2688,3200,3712,20864,21120,25048,26233,27008,27264,29056,29312])),([5,1083361,2164831,6494406,8659208],(decodeHints [129,573,1153,1665,2177,2689,3201,3713,20865,21120,24889,26234,27265,29057,29313])),([5,1083361,2164831,6494431,8659208],(decodeHints [128,731,1152,1664,2176,2688,3200,3712,15066,16002,20864,21120,21888,25051,26233,27008,27264,28032,29056,29312])),([5,1083361,2164831,8659208,12988812],(decodeHints [128,533,1152,1664,2176,2688,3200,3712,18709,18965,21120,27264,29312,30080])),([5,1083361,2164831,8659208,18400817],(decodeHints [129,573,1153,1665,2177,2689,3201,3713,18745,19005,21121,27264,29057,29313])),([5,1083361,2164831,8659208,29224827],(decodeHints [128,533,1152,1664,2176,2688,3200,3712,18709,20089,21120,27264,28032,29312,30080])),([5,1083361,6494406,6494431,8659208],(decodeHints [129,573,1153,1665,2177,2689,3201,3713,14909,16000,20864,21121,21889,24889,26234,27009,27265,28032,29313])),([5,1083361,6494406,8659208,33554400],(decodeHints [136,728,1160,1672,2184,2696,3208,3645,18904,20094,20872,21128,27265,28032,30086])),([5,1083361,6494431,8659208,17318416],(decodeHints [165,573,1189,1701,2213,2725,3237,3749,18745,20089,21157,25224,26240,27301,28288,29093,29349,30336])),([5,1083361,8659208,18400817,33554400],(decodeHints [136,623,1160,1672,2184,2696,3208,3645,14728,14959,20872,21128,28040,30080])),([5,2164802,4329631,8659208,9742313],(decodeHints [216,554,1240,1752,2264,2776,3288,3800,14808,14890,18432,18730,18986,29400,30168])),([5,2164802,4329631,8659208,32471070],(decodeHints [216,554,1240,1752,2264,2776,3288,3715,14808,14890,18730,18986,21208,29142,29400])),([5,8659944,17318416,18400817,33554400],(decodeHints [180,597,1204,1716,2228,2740,3252,3634,14952,21172,21940,26036])),([5,8659944,17318416,32472030,33554400],(decodeHints [180,664,1204,1716,2228,2664,3252,3634,19892,21172,21940,26036,28084])),([6,0,31,1082401,8659944,17318416],(decodeHints [50,562,1074,1640,2098,2610,3122,3634,4146,4658,14696,14898,15666,18738,18994,19762,24882,25138,25906,27144,29233,33074,33330,34098,35432,37170,37426])),([6,1,31,1082401,8659944,17318416],(decodeHints [180,692,1204,1716,2228,2740,3252,3736,4276,4788,14696,15028,15796,18738,19124,19892,20916,21172,24984,25268,25906,27316,29364,30131,33204,33460,34098,35508,37300,37556])),([6,1,992,1082431,8659208,17318416],(decodeHints [180,692,1204,1688,2228,2740,3252,3764,4276,4788,14744,15028,19124,19892,20916,25012,25268,27060,27288,29364,33204,33460,37556,39348,39604])),([6,2,31,1082401,8659944,17318416],(decodeHints [50,562,1074,1641,2098,2610,3122,3634,4146,4658,14696,14898,15666,18738,18994,19762,24882,25138,25906,27174,29233,33074,33330,34098,35433,37170,37426])),([6,8,31,1082401,8659944,17318416],(decodeHints [90,602,1114,1640,2138,2650,3162,3674,4186,4698,14696,14938,15706,18778,19034,19762,24882,25178,25946,26984,27144,29272,33114,33370,34098,35432,37210,37466])),([6,16,31,1082401,8659944,17318416],(decodeHints [50,562,1074,1640,2098,2610,3122,3634,4146,4658,14696,14898,15666,18738,18994,19762,24882,25138,25906,27144,29233,33074,33330,34098,35176,35432,37170,37426])),([6,27,992,1082401,8659208,17318416],(decodeHints [66,682,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25258,26938,27202,28994,29250,33450,37186,37442,39234,39490])),([6,31,31,1082401,8659944,17318416],(decodeHints [104,616,2152,2740,3176,3688,4200,4712,12648,12904,13672,13928,18868,19892,24936,25192,25946,29290,33128,33384,34098,37300,37584])),([6,31,32,1082401,8659944,17318416],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,4146,4658,14642,15028,15922,20147,20786,21042,21810,25268,26930,27186,27954,28978,29234,33460,35122,35378,36146,37170,37426])),([6,31,33,992,8659208,17318416],(decodeHints [104,616,1128,1715,2152,2664,3176,3688,4200,4712,14693,18792,18952,21053,25192,27059,27255,29032,29288,33384,35251,35507,39272,39528])),([6,31,33,1023,8659208,17318416],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,4104,4616,18952,19720,21000,21768,25192,26888,27144,28936,29192,33128,33384,35080,35336,39176,39432])),([6,31,64,1082401,8659944,17318416],(decodeHints [55,624,1079,1591,2103,2615,3127,3639,4151,4663,14647,14960,15922,20791,21047,21810,25098,26930,27191,27959,29238,33392,35127,35383,36146,37175,37431])),([6,31,256,992,1082401,6494406],(decodeHints [66,675,1090,1602,2114,2626,3138,3650,4162,4674,14658,15011,18783,18952,21058,21826,26946,27202,28989,29250,33181,33443,35138,35394,39234,39490])),([6,31,256,992,1082401,25977624],(decodeHints [66,675,1090,1602,2114,2626,3138,3650,4162,4674,14658,15011,18783,18952,21058,21826,26946,27202,28989,33443,35394,36162,39234,39490])),([6,31,256,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,14642,14952,15922,20786,21042,21810,25096,26930,27186,27954,29233,33384,35122,35378,36146,37170,37426])),([6,31,256,1083361,2164802,4329604],(decodeHints [61,638,1085,1597,2109,2621,3133,3645,4157,4669,14653,14974,21053,21821,24576,24954,25209,26624,26941,27197,33149,33404,35133,35389,39229,39485])),([6,31,512,992,1082401,6494406],(decodeHints [66,631,1090,1602,2114,2626,3138,3650,4162,4674,14658,14967,18783,18952,21058,21826,26946,27202,28989,33143,33395,35138,35394,37442,38201,39234,39490])),([6,31,512,992,1082401,25977624],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14658,14952,18783,18952,21058,21826,26946,27202,28989,33384,35394,36162,37178,37442,39234,39490])),([6,31,512,1082401,8659208,17318896],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14658,14952,20802,21058,25192,26946,27202,28994,29250,33288,35394,36162,37437,39234,39482])),([6,31,512,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,14642,14952,15922,20786,21042,21810,25096,26930,27186,27954,29233,33384,35122,35378,36146,37170,37426,39218,39474])),([6,31,736,1082401,2164802,4329604],(decodeHints [58,668,1082,1594,2106,2618,3130,3642,4154,4666,14687,14856,20793,21050,24576,24985,25244,28986,29242,33179,33436,37178,37434,39226,39482])),([6,31,736,1082401,8659208,17318416],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,4154,4666,14687,14856,20793,25268,26938,27194,28986,29242,33460,37178,37434,39226,39482])),([6,31,736,1082401,17318416,24895223],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,4154,4666,14687,14856,20793,25268,28986,29242,33370,35386,36154,37434,38202,39482,40250])),([6,31,960,1082401,8659208,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,14653,15028,20146,20797,21053,25268,26937,27197,28989,29245,33460,37181,37437,39229,39485])),([6,31,960,8659208,17318416,32472030],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,14653,15028,19124,20793,21053,25268,28989,29245,34482,35389,36157,37437,38205,39485,40253])),([6,31,992,31744,9741609,18400817],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,14687,14856,18884,19010,20034,20814,21070,22082,26937,27214,28994,30030,37196,38211])),([6,31,992,31744,9741609,25977624],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,14687,14856,18884,19010,20034,20814,21070,22082,26937,28994,29262,30030,37187,38220])),([6,31,992,31744,18400817,25977624],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,14687,14856,18884,19010,20034,20814,21070,22082,29004,29262,30019,35406,37187,38220])),([6,31,992,33825,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,27202,28994,29250,33460,37186,37442,39234,39490])),([6,31,992,1014750,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,21821,25268,26938,27202,28994,33460,37186,39234,39490])),([6,31,992,1082401,2164802,4329860],(decodeHints [66,675,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,24989,25251,28994,29250,33184,33443,37186,37442,39234,39490])),([6,31,992,1082401,6494406,8659208],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,24998,25268,28994,29250,33460,35130,36418,37186,37442,39234,39490])),([6,31,992,1082401,6494406,8659231],(decodeHints [180,692,1204,1743,2228,2740,3252,3764,4276,4788,14799,15028,18868,20916,21199,25012,25268,29108,29364,33460,34228,35279,36418,37442,39348,39604])),([6,31,992,1082401,6494406,8682760],(decodeHints [67,708,1091,1603,2115,2627,3139,3651,4163,4675,14687,14856,20797,21059,25020,25284,28995,29251,33346,35131,36418,37442,39491])),([6,31,992,1082401,6494406,9741609],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,24998,25268,28994,29250,33346,35129,36418,37442,38210,39234,39490])),([6,31,992,1082401,6494406,10824010],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,24998,25268,28994,29250,33460,36418,37186,37442,39490])),([6,31,992,1082401,6494406,15153614],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,24998,25268,27202,28994,29250,33460,36418,37186,37442,39490,40258])),([6,31,992,1082401,6494406,16236015],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,24998,25268,27202,28994,29250,33346,36418,37442,38210,39490,40258])),([6,31,992,1082401,6494406,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,24998,25268,27202,28994,29250,33460,36418,37186,37442,39234,39490])),([6,31,992,1082401,6494406,17318431],(decodeHints [180,692,1204,1655,2228,2740,3252,3764,4276,4788,14711,15028,18868,20916,25012,25268,27242,29108,29364,33460,34228,36418,37446,39348,39604])),([6,31,992,1082401,6494406,17333776],(decodeHints [78,676,1102,1614,2126,2638,3150,3662,4174,4686,14687,14856,20810,24989,25252,27214,29006,29262,33346,36418,37452,39502])),([6,31,992,1082401,6494406,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,24998,25268,27202,28994,29250,33350,36418,37442,38210,39234,39490])),([6,31,992,1082401,6494406,19483218],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,24998,25268,28994,29250,33460,36418,37186,37442,39490])),([6,31,992,1082401,6494406,23812822],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,24998,25268,28994,29250,33460,36153,36418,37186,37442,39490,40258])),([6,31,992,1082401,6494406,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,24998,25268,28994,29250,33350,36154,36418,37442,38210,39490,40258])),([6,31,992,1082401,6494431,8659208],(decodeHints [180,692,1204,1741,2228,2740,3252,3764,4276,4788,14797,15028,15782,18868,19878,20916,21197,24998,25268,26036,29364,33204,33460,34214,35277,36515,37300,37556,39348,39604])),([6,31,992,1082401,6494431,17318416],(decodeHints [180,692,1204,1651,2228,2740,3252,3764,4276,4788,14707,15028,15782,18868,19878,20916,24998,25268,26036,27240,29364,33204,33460,34214,36467,37300,37556,39348,39604])),([6,31,992,1082401,6495206,17318416],(decodeHints [66,618,1090,1602,2114,2626,3138,3650,4162,4674,14658,14954,20802,24938,25192,27202,27970,29250,33386,35138,36418,37186,37442,39234,40514])),([6,31,992,1082401,7576807,8659208],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,29250,30018,33460,35130,36418,37186,37442,39234,39490])),([6,31,992,1082401,7576807,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,27202,29250,30018,33460,36418,37186,37442,39234,39490]))]
noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,1082401,8658952,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26946,27202,28994,29250,33460,37186,37442,39234,39490])),([6,31,992,1082401,8659200,17318416],(decodeHints [90,692,1114,1626,2138,2650,3162,3674,4186,4698,14687,14856,20824,25012,25268,26970,27226,29018,29274,33460,37210,37466,39258,39514])),([6,31,992,1082401,8659208,15153614],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,25268,26938,27202,28994,29250,33460,37186,37442,39490,40258])),([6,31,992,1082401,8659208,16236000],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25012,25268,26984,27240,29108,29364,33204,33346,37401,39604,40372])),([6,31,992,1082401,8659208,16236015],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,27202,28994,29250,33346,37442,38210,39490,40258])),([6,31,992,1082401,8659208,16236031],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,27202,28994,29250,33346,34114,37442,38210,39490,40258])),([6,31,992,1082401,8659208,17318400],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,27202,28994,29250,33204,33460,37186,37442,39234,39490])),([6,31,992,1082401,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,27202,28994,29250,33460,37186,37442,39234,39490])),([6,31,992,1082401,8659208,17318417],(decodeHints [180,692,1204,1643,2228,2740,3252,3764,4276,4788,14699,15028,18868,20916,25268,26987,27243,29108,29364,33460,37442,39348,39604])),([6,31,992,1082401,8659208,17318418],(decodeHints [25,692,1049,1561,2073,2585,3097,3609,4121,4633,14691,14886,20757,25268,26905,27161,28953,29209,33460,37145,37401,39193,39449])),([6,31,992,1082401,8659208,17318424],(decodeHints [90,692,1114,1626,2138,2650,3162,3674,4186,4698,14687,14856,20824,25012,25268,26970,27226,29018,29274,33460,37210,37466,39238,39490])),([6,31,992,1082401,8659208,17318431],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25012,25268,26984,27240,29108,29364,33460,34228,37401,39348,39604])),([6,31,992,1082401,8659208,17318448],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14658,15028,20105,20802,21058,25268,26938,27202,28994,29250,33460,37186,37442,39234,39490])),([6,31,992,1082401,8659208,17318672],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26946,28994,29250,33460,37186,37442,39490])),([6,31,992,1082401,8659208,17319440],(decodeHints [67,692,1091,1603,2115,2627,3139,3651,4163,4675,14687,14856,20797,25268,26939,27203,28995,29251,33305,37442,39235,39491])),([6,31,992,1082401,8659208,17326608],(decodeHints [76,692,1100,1612,2124,2636,3148,3660,4172,4684,14687,14856,20810,25268,26938,27212,29004,29260,33460,37196,37452,39244,39490])),([6,31,992,1082401,8659208,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,25268,26938,27202,28994,29250,33305,37442,38210,39234,39490])),([6,31,992,1082401,8659208,18400831],(decodeHints [25,692,1049,1561,2073,2585,3097,3609,4121,4633,14617,15028,20757,21017,25012,25268,26905,27161,28953,29209,33305,34073,37401,38169,39193,39449])),([6,31,992,1082401,8659208,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,28226,28994,29250,33460,37186,37442,39490,40258])),([6,31,992,1082401,8659208,25977631],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25268,26984,28323,29108,29364,33460,34228,37401,39604,40372])),([6,31,992,1082401,8659208,27060025],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,25268,26938,28226,28994,29250,33305,34114,37442,38210,39490,40258])),([6,31,992,1082401,8659209,17318416],(decodeHints [180,692,1204,1642,2228,2740,3252,3764,4276,4788,14698,15028,18868,20916,25268,26986,27242,29250,33460,37300,37556,39348,39604])),([6,31,992,1082401,8659210,17318416],(decodeHints [19,692,1043,1555,2067,2579,3091,3603,4115,4627,14689,14859,20750,25268,26893,27155,28947,29203,33460,37139,37395,39187,39443])),([6,31,992,1082401,8659224,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,27202,28994,29250,33204,33460,37186,37442,39234,39490])),([6,31,992,1082401,8659231,16236015],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25268,26036,26984,27240,29203,33460,34228,37556,38324,39604,40372])),([6,31,992,1082401,8659231,17318416],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25268,26036,26984,27240,29203,33204,33460,37300,37556,39348,39604])),([6,31,992,1082401,8659231,17318431],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,15796,18868,19892,20916,25012,25268,26036,26984,27240,29364,33204,33460,34228,37556,39348,39604])),([6,31,992,1082401,8659231,18400817],(decodeHints [180,692,1204,1744,2228,2740,3252,3764,4276,4788,14800,15028,18868,20916,21200,25268,26036,27088,27344,29203,33204,33460,37556,38324,39187,39604])),([6,31,992,1082401,8659231,25977624],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25268,26036,26984,28226,29250,33460,34228,37300,37556,39604,40258])),([6,31,992,1082401,8659231,25977631],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25268,26036,26984,28323,29364,33460,34228,37556,39604,40372])),([6,31,992,1082401,8659240,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14658,15028,20802,25268,26938,27202,29250,33460,37186,37442,39234,39490])),([6,31,992,1082401,8659272,17318416],(decodeHints [66,693,1090,1602,2114,2626,3138,3650,4162,4674,14688,14858,20797,25269,26930,27202,28994,29250,33461,37186,37442,39234,39490])),([6,31,992,1082401,8659720,17318416],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25192,26938,27202,28994,29250,33384,35138,37186,37442,39234])),([6,31,992,1082401,8659944,16236015],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14658,14952,15922,20802,21810,25192,26930,27202,27970,29250,33346,35122,36162,37442,38210,40258])),([6,31,992,1082401,8659944,17318416],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14658,14952,15922,20802,21810,25192,26930,27202,27970,29250,33384,35138,36146,37186,37442,39234])),([6,31,992,1082401,8659944,17318431],(decodeHints [104,616,1128,1640,2152,2712,3176,3688,4200,4712,14696,14952,15976,18839,20888,21940,24936,25192,26984,27240,28008,29290,33384,34152,35176,36200,37401,39272])),([6,31,992,1082401,8659944,18400817],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,4162,4674,14658,15056,15922,20802,21058,21810,25296,26930,27202,27970,28994,29250,33305,35138,36146,37442,38210,39234])),([6,31,992,1082401,8659967,17318416],(decodeHints [104,616,1128,1640,2152,2712,3176,3688,4200,4712,14687,14856,15880,18840,20750,21940,25192,25960,26888,27240,28008,29203,30056,33128,33384,35176,36104,37205,37584,39272])),([6,31,992,1082401,8660232,17318416],(decodeHints [67,692,1091,1603,2115,2627,3139,3651,4163,4675,14687,14856,20797,25107,26939,27203,29250,33460,37187,37443,39235,39491])),([6,31,992,1082401,8675592,17318416],(decodeHints [66,706,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25282,26938,27202,28994,29250,33474,37186,37442,39234,39490])),([6,31,992,1082401,8682760,25977624],(decodeHints [67,708,1091,1603,2115,2627,3139,3651,4163,4675,14687,14856,20797,25154,26939,28226,28995,29250,33476,37187,37443,40258])),([6,31,992,1082401,9741609,16236015],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25107,26937,27202,29250,30018,33346,37442,38210,39490,40258])),([6,31,992,1082401,9741609,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25107,26937,27202,29250,30018,33460,37186,37442,39234,39490])),([6,31,992,1082401,9741609,17318431],(decodeHints [180,692,1204,1655,2228,2740,3252,3764,4276,4788,14711,15028,18868,20916,25012,25268,26999,27242,29364,30132,33460,34228,37401,39348,39449])),([6,31,992,1082401,9741609,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20148,20797,21058,22082,25107,26937,27202,28994,29250,30018,33305,37186,37442,38210,39234,39490])),([6,31,992,1082401,9741609,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20148,20797,21058,22082,25154,26937,28226,28994,29250,30018,33460,37186,37442,38210,39490,40258])),([6,31,992,1082401,9741609,27060025],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25154,26937,28226,29250,30018,33305,34114,37442,38210,39490,40258])),([6,31,992,1082401,9741631,17318416],(decodeHints [19,692,1043,1555,2067,2579,3091,3603,4115,4627,14689,14859,20750,25107,25875,26891,27155,29203,29971,33204,33460,37139,37395,39187,39443])),([6,31,992,1082401,9742313,17318416],(decodeHints [66,618,1090,1602,2114,2626,3138,3650,4162,4674,14692,14897,15921,20797,21810,25107,26929,27202,27970,29250,30018,33386,35138,36145,37186,37442,39234])),([6,31,992,1082401,10824010,12988812],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,25268,28994,29250,33460,37186,37442])),([6,31,992,1082401,10824010,19483218],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,28994,29250,33460,37186,37442])),([6,31,992,1082401,10824010,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,28226,28994,29250,33460,37186,37442,40258])),([6,31,992,1082401,16236015,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25154,29250,30018,33370,35394,36154,37442,38210,40258,40514])),([6,31,992,1082401,16236015,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25154,28226,29250,30018,33460,35394,37186,37442,40258,40514])),([6,31,992,1082401,17318416,23812822],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,28994,29250,33460,35394,36153,37186,37442,39490,40258])),([6,31,992,1082401,17318416,24894487],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14658,14952,15922,20802,21810,25192,26946,27954,28994,29250,33370,35138,35394,36146,37442,39490])),([6,31,992,1082401,17318416,24895200],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25012,25268,29108,29364,33204,33370,35508,36276,37395,39604,40372])),([6,31,992,1082401,17318416,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,28994,29250,33370,35394,36154,37442,38210,39490,40258])),([6,31,992,1082401,17318416,24895231],(decodeHints [90,692,1114,1626,2138,2650,3162,3674,4186,4698,14687,14856,20824,25268,29018,29274,33370,34138,35418,36186,37466,38234,39514,40282])),([6,31,992,1082401,17318416,24895479],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,28994,29250,33370,35394,36162,37442,38210,39490,40258])),([6,31,992,1082401,17318416,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,28226,28994,29250,33460,35394,37186,37442,39490,40258])),([6,31,992,1082401,17318416,25977631],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25268,28264,29108,29364,33460,34228,35432,37395,39604,40372])),([6,31,992,1082401,17318416,25977848],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14658,14952,20802,25192,27954,28226,28994,29250,33384,35394,36162,37442,39490,40258])),([6,31,992,1082401,17318416,27060025],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,28226,28994,29250,33299,34114,35394,37442,38210,39490,40258]))]
noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,1082401,17318431,24895223],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25268,26036,29209,33460,34228,35508,36276,37556,38324,39604,40372])),([6,31,992,1082401,17318431,25977624],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25268,26036,28226,29254,33460,34228,35432,37300,37556,39604,40262])),([6,31,992,1082401,17318431,25977631],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,18868,20916,25268,26036,28264,29364,33460,34228,35432,37556,39604,40372])),([6,31,992,1082401,17333776,25977624],(decodeHints [78,676,1102,1614,2126,2638,3150,3662,4174,4686,14687,14856,20810,25154,28226,29006,29260,33444,35406,37198,37454,40268])),([6,31,992,1082401,18400817,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,25113,29250,30018,33370,35394,36154,37442,38210,39490,40258])),([6,31,992,1082401,18400817,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20148,20797,21058,22082,25158,28226,28994,29250,30018,33460,35394,37186,37442,38210,39490,40258])),([6,31,992,1082401,18400817,27060025],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,21058,25158,28226,29250,30018,33299,34114,35394,37442,38210,39490,40258])),([6,31,992,1082401,19483218,21648020],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,28994,29250,33460,37186,37442])),([6,31,992,1082401,19483218,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,28226,28994,29250,33460,37186,37442,40258])),([6,31,992,1082401,24895223,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25158,27962,28226,29250,30018,33460,37186,37442,40258,40514])),([6,31,992,1082409,8659208,17318416],(decodeHints [90,692,1114,1626,2138,2650,3162,3674,4186,4698,14687,14856,20824,25012,26970,27226,28994,33460,37210,37466,39258,39514])),([6,31,992,1082417,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,27202,28994,29250,33204,37186,39234,39490])),([6,31,992,1082657,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26946,28994,33460,37186,37442,39234,39490])),([6,31,992,1082913,2164802,4329604],(decodeHints [66,631,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,24576,24951,25203,27202,28994,29250,33143,33397,35394,37186,37442,39234,39490])),([6,31,992,1082913,8659208,17318416],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25192,26938,27202,28994,29250,33384,35138,35394,37186,37442,39234,39490])),([6,31,992,1083361,6494406,8659208],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,4162,4674,14658,15056,15933,20797,21058,21826,25040,25293,26946,27965,28994,33487,35138,36157,36418,37186,38466,39234,39490])),([6,31,992,1083361,8659208,18400817],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,4162,4674,14658,15056,15933,20797,21058,21826,25296,26946,27202,27965,28994,29250,33305,35133,36162,38210,39234,39490])),([6,31,992,1084449,8659208,17318416],(decodeHints [66,694,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25270,26938,27202,28994,29250,33462,37186,37442,39234,39490])),([6,31,992,1090593,8659208,17318416],(decodeHints [76,692,1100,1612,2124,2636,3148,3660,4172,4684,14687,14856,20810,25268,26938,27212,28994,33460,37196,37452,39244,39500])),([6,31,992,1098785,8659208,17318416],(decodeHints [66,706,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25282,26938,27202,28994,29250,33474,37186,39234,39490])),([6,31,992,1113121,8659208,16236015],(decodeHints [76,708,1100,1612,2124,2636,3148,3660,4172,4684,14687,14856,20810,25284,26938,27212,28994,33356,38220,39500,40268])),([6,31,992,1113121,8659208,17318416],(decodeHints [76,708,1100,1612,2124,2636,3148,3660,4172,4684,14687,14856,20810,25284,26938,27212,28994,33476,37196,39244,39500])),([6,31,992,1113121,8659208,17318431],(decodeHints [196,708,1220,1640,2244,2756,3268,3780,4292,4804,14696,15044,18884,20846,25028,25284,26984,27240,29124,33476,34244,39364,39620])),([6,31,992,1113121,8659208,25977624],(decodeHints [76,708,1100,1612,2124,2636,3148,3660,4172,4684,14687,14856,20810,25284,26938,28236,28994,29260,33476,37186,39500,40268])),([6,31,992,1113121,8659231,17318416],(decodeHints [196,708,1220,1640,2244,2756,3268,3780,4292,4804,14696,15044,18884,20846,25284,26052,26984,27240,33220,33476,37304,39364,39620])),([6,31,992,1113121,8659944,17318416],(decodeHints [76,616,1100,1612,2124,2636,3148,3660,4172,4684,14668,14952,21810,25192,27212,27980,33384,35148,37196,39244])),([6,31,992,1113121,17318416,24895223],(decodeHints [76,708,1100,1612,2124,2636,3148,3660,4172,4684,14687,14856,20810,25284,29004,33372,35404,36154,38210,39500,40268])),([6,31,992,1113121,17318416,25977624],(decodeHints [76,708,1100,1612,2124,2636,3148,3660,4172,4684,14687,14856,20810,25284,28236,29004,29260,33476,35404,37186,39500,40268])),([6,31,992,2096161,8659208,17318416],(decodeHints [81,709,1105,1617,2129,2641,3153,3665,4177,4689,14687,14856,20816,25285,26938,27217,28994,33477,37201,39249,39505])),([6,31,992,2164802,5412005,9741609],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,28994,29250,35129,37186,37442])),([6,31,992,2164802,5412005,12988812],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,27202,28994,29250,37186,37442])),([6,31,992,2164802,5412005,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,21058,27202,28994,29250,37186,37442])),([6,31,992,2164802,5412005,21648020],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,21058,28994,29250,37186,37442])),([6,31,992,2164802,9741609,12988812],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,26937,27202,28994,29250,37186,37442])),([6,31,992,2164802,9741609,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,20034,21058,22082,26937,27202,28994,29250,30018,37186,37442,38210])),([6,31,992,2164802,9741609,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,20034,21058,22082,26937,28994,29250,30018,37186,37442,38210])),([6,31,992,2164802,12988812,21648020],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,28994,29250,35394,37186,37442])),([6,31,992,2164802,12988812,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,28994,29250,35394,37186,37442])),([6,31,992,2164802,18400817,21648020],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,21058,28994,29250,35394,37186,37442])),([6,31,992,2164802,18400817,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,20034,21058,22082,28994,29250,30018,35394,37186,37442,38210])),([6,31,992,2164802,21648020,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,28994,29250,37186,37442])),([6,31,992,3247203,5412005,8659208],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,33460,35130,36418,37186,37442,39234,39490])),([6,31,992,3247203,5412005,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,33460,36418,37186,37442,39234,39490])),([6,31,992,3247203,6494406,8659208],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,21058,24998,28994,33460,35130,36418,37186,37442,39234,39490])),([6,31,992,3247203,6494406,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,24998,28994,33460,36418,37186,37442,39234,39490])),([6,31,992,3247203,8659208,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,21058,25268,26938,27202,28994,29250,38210,39234,39490])),([6,31,992,3247203,8659208,19483218],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,25268,26938,27202,28994,29250,39234,39490])),([6,31,992,3247203,9741609,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,26937,30018,33460,37186,37442,39234,39490])),([6,31,992,3247203,10824010,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,33460,37186,37442,39234,39490])),([6,31,992,6494406,7576807,8659208],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,27202,29250,30018,33460,35130,36418,37186,37442,39234,39490])),([6,31,992,6494406,7576807,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,29250,30018,33460,36418,37186,37442,39234,39490])),([6,31,992,6494406,8659208,9741609],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,26938,28994,29250,35129,35394,37186,37442,39490,40258])),([6,31,992,6494406,8659208,16236015],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,26938,28994,29250,35394,37442,38210,39490,40258])),([6,31,992,6494406,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,26938,28994,29250,35394,37186,37442,39234,39490])),([6,31,992,6494406,8659208,17318896],(decodeHints [66,518,1090,1602,2114,2626,3138,3650,4162,4674,14658,14854,18754,20802,26946,28994,29250,35394,36162,37442,39490])),([6,31,992,6494406,8659208,19483218],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,26938,28994,29250,35394,37442,39234,39490])),([6,31,992,6494406,8659208,23812822],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,26938,28994,29250,35394,36153,37442,38210,39234,39490])),([6,31,992,6494406,8659208,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,25268,26938,28226,28994,29250,35394,37186,37442,39490,40258])),([6,31,992,6494406,8659208,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,25268,26938,28226,28994,29250,35394,36157,37442,38210,39490,40258])),([6,31,992,6494406,10824010,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,29250,35394,37186,37442,39234,39490])),([6,31,992,6494406,15153614,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,21058,29250,30018,35394,37186,37442,39234,39490])),([6,31,992,6494406,17318416,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,21058,27202,28994,29250,37186,37442,39490,40258])),([6,31,992,6494406,17318416,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,27202,28994,29250,36154,37442,38210,39490,40258])),([6,31,992,6494406,17318416,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,25268,28226,28994,29250,37186,37442,39490,40258]))]
noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,6494406,17318416,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18854,19124,21058,25268,28226,28994,29250,36157,37442,38210,39490,40258])),([6,31,992,6520006,8659208,17318416],(decodeHints [78,704,1102,1614,2126,2638,3150,3662,4174,4686,14687,14856,18876,26939,28995,35406,37198,39246,39502])),([6,31,992,8659208,9741609,16236015],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20794,26937,29250,30018,33346,37442,38210,39490,40258])),([6,31,992,8659208,9741609,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20794,26937,29250,30018,33460,37186,37442,39234,39490])),([6,31,992,8659208,9741609,17318431],(decodeHints [180,692,1204,1582,2228,2740,3252,3764,4276,4788,14638,15028,18868,20916,25012,26926,29364,30132,33460,34228,37556,39449])),([6,31,992,8659208,9741609,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20058,20794,21058,22082,26937,27202,28994,29250,30018,33305,37186,37442,38210,39490,40258])),([6,31,992,8659208,9741609,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20058,20794,21058,22082,26937,28994,29250,30018,33460,37186,37442,38210,39234,39490])),([6,31,992,8659208,9741609,27060025],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20794,26937,27202,29250,30018,33305,34114,37442,38210,39490,40258])),([6,31,992,8659208,9764137,17318416],(decodeHints [66,708,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20794,26937,29250,30018,33476,37186,37442,39234])),([6,31,992,8659208,15153614,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20794,21058,29250,30018,35394,37186,37442,39234,39490])),([6,31,992,8659208,16236015,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20794,21058,27202,29250,30018,37186,37442,40258,40514])),([6,31,992,8659208,16236015,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20794,21058,25154,29250,30018,36157,37442,38210,40258,40514])),([6,31,992,8659208,17318416,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20794,21058,27202,28994,29250,37186,37442,39490,40258])),([6,31,992,8659208,17318416,18415153],(decodeHints [76,696,1100,1612,2124,2636,3148,3660,4172,4684,14687,14856,19128,20794,21068,27212,29004,29260,37442,39500,40268])),([6,31,992,8659208,17318416,23812822],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20794,25268,28994,29250,36153,37186,37442,39490,40258])),([6,31,992,8659208,17318416,27060025],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20794,27202,28994,29250,34114,37442,38210,39490,40258])),([6,31,992,8659208,17318416,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20794,21058,25268,28994,29250,36157,37442,38210,39490,40258])),([6,31,992,8659208,17318416,32473054],(decodeHints [67,691,1091,1603,2115,2627,3139,3651,4163,4675,14687,14856,19123,20795,21059,25267,28995,29251,36157,37443,38211,39491,40259])),([6,31,992,8659208,17318431,32472030],(decodeHints [180,692,1204,1688,2228,2740,3252,3764,4276,4788,14744,15028,18868,19124,20916,21144,25268,26036,29108,29364,34228,36276,37556,38324,40217])),([6,31,992,8659208,17318896,18400817],(decodeHints [66,597,1090,1602,2114,2626,3138,3650,4162,4674,14658,14933,19029,20802,21058,27202,27970,28994,29250,36162,37186,37442,40258])),([6,31,992,8659208,18400817,19483218],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20794,21058,28994,29250,35394,37186,37442,40514])),([6,31,992,8659208,18400817,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20058,20794,21058,22082,28994,29250,30018,35394,37186,37442,38210,39234,40514])),([6,31,992,8659208,18400817,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20794,21058,25113,28994,29250,35394,36157,37442,38210,40258,40514])),([6,31,992,8659208,19483218,21648020],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20794,28994,29250,37186,37442])),([6,31,992,8659208,25977624,27060025],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20794,22082,27202,29250,30018,34114,37442,38210,39490,40258])),([6,31,992,8659208,25977624,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20794,22082,25268,29250,30018,36157,37442,38210,39490,40258])),([6,31,992,8659231,17318416,18400817],(decodeHints [180,692,1204,1621,2228,2740,3252,3764,4276,4788,14677,15028,19124,19892,20916,21077,25012,27221,29108,33204,37139,39604,40372])),([6,31,992,8659231,17318416,32472030],(decodeHints [180,692,1204,1688,2228,2740,3252,3764,4276,4788,14744,15028,19124,19892,20916,21144,25012,25268,29108,29364,34228,36276,38163,39604,40372])),([6,31,992,8659944,17318416,18400817],(decodeHints [66,597,1090,1602,2114,2626,3138,3650,4162,4674,14658,14933,15922,19029,20786,21058,21826,26946,27202,27954,28994,29250,35138,36146,37186,39490,40258])),([6,31,992,8659944,17318416,32472030],(decodeHints [66,664,1090,1602,2114,2626,3138,3650,4162,4674,14658,15000,15922,19096,20786,21058,21826,25240,26946,27954,28994,35122,36162,38210,39490,40258])),([6,31,992,9741609,10824010,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20793,30274,33460,37186,37442,39234,39490])),([6,31,992,9741609,17318416,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18963,20793,21058,25268,26178,27202,28226,28994,29250,30274,37186,38466,39234,39490,40258])),([6,31,992,9741609,17318416,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20793,25268,28994,29250,36154,38210,38466,39490,40258])),([6,31,992,9741609,17318416,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20793,25268,26178,27202,28226,28994,29250,30274,37186,38466,39234,39490,40258])),([6,31,992,9741609,17318416,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,18963,20793,21058,25268,28994,29250,36157,38210,38466,39490,40258])),([6,31,992,9741609,18400817],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,15312,16194,19266,20404,21314,22338,25434,26548,27458,28482,29506,30530])),([6,31,992,9741609,25977624],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,15208,16194,19266,20404,21314,22338,25524,26548,27458,28482,29506,30530])),([6,31,992,10824010,12988812,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,35394,37186,37442,39234,39490])),([6,31,992,17318416,18400817,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,21058,29250,30018,33370,35394,36154,37442,38210,39490,40258])),([6,31,992,17318416,18400817,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,20034,21058,22082,28994,29250,30018,33460,35394,37186,37442,38210,39234,39490])),([6,31,992,17318416,18400817,27060025],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,21058,29250,30018,33299,34114,35394,37442,38210,39490,40258])),([6,31,992,17318416,24895223,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,25178,27202,27962,29250,30018,36157,37442,38210,40258,40514])),([6,31,992,17318416,25977624,27060025],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,22082,29250,30018,34114,37442,38210,39490,40258])),([6,31,992,17318416,25977624,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,19124,22082,25268,27202,29250,30018,36157,37442,38210,39490,40258])),([6,31,992,18400817,25977624],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,15208,16194,19290,20404,21314,22338,25524,26548,27458,28482,29506,30530])),([6,31,993,1082401,8659208,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,14856,19109,20797,22077,25268,26937,27197,28989,29245,33460,37181,37437,39229,39485])),([6,31,994,1082401,8659208,17318416],(decodeHints [9,692,1033,1545,2057,2569,3081,3593,4105,4617,14856,20744,25268,26889,27145,28937,29193,33460,37129,37385,39177,39433])),([6,31,1000,1082401,8659208,17318416],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,4154,4666,14856,20793,25268,26938,27186,28986,29242,33460,37178,37434,39226,39482])),([6,31,1008,1082401,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,27202,28994,29250,33115,33460,37186,37442,39234,39490])),([6,31,1023,1082401,6494406,8659208],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,25268,28936,29192,33460,35080,36360,37128,37384,39176,39432])),([6,31,1023,1082401,6494406,17318416],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,25268,27144,28936,29192,33115,33460,36360,37128,37384,39176,39432])),([6,31,1023,1082401,8659208,16236015],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,22024,25268,26888,27144,28936,29192,33288,34056,37384,38152,39432,40200])),([6,31,1023,1082401,8659208,17318416],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,22024,25268,26888,27144,28936,29192,33115,33460,37128,37384,39176,39432])),([6,31,1023,1082401,8659208,17318431],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,14696,15028,15796,18868,19739,20840,22120,25012,25268,25883,26984,27240,29108,29364,33051,33460,34228,37556,39348,39604])),([6,31,1023,1082401,8659208,18400817],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,25268,26888,27144,28936,29192,33460,37384,38152,39176,39432])),([6,31,1023,1082401,8659208,25977624],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,22024,25268,26888,28168,28936,29192,33460,37128,37384,39432,40200])),([6,31,1023,1082401,8659231,17318416],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,15028,15796,18868,20840,22120,25268,26036,26984,27144,29195,33204,33460,37300,37556,39348,39604])),([6,31,1023,1082401,8659944,17318416],(decodeHints [104,616,1128,1640,2152,2712,3176,3688,4200,4712,14952,15720,15976,18791,20786,21940,22120,25096,25946,26984,27144,27954,29233,33128,33384,35176,36146,37205,37584,39272])),([6,31,1023,1082401,8659967,17318416],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,15976,20744,21768,22024,25096,25864,26888,27144,27912,29192,29960,33128,33384,35080,36104,37128,37384,39176])),([6,31,1023,1082401,9741609,17318416],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,25099,26888,27144,29192,29960,33115,33460,37128,37384,39176,39432])),([6,31,1023,1082401,17318416,24895223],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,22024,24923,25268,28936,29192,33288,35336,36104,37384,38152,39432,40200])),([6,31,1023,1082401,17318416,25977624],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,22024,24923,25268,28168,28936,29192,33460,35336,37128,37384,39432,40200])),([6,31,1023,1113121,8659208,17318416],(decodeHints [8,708,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,22024,25284,26888,27144,28936,33118,33476,37128,39176,39432])),([6,31,1023,6494406,8659208,17318416],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,22024,26888,28936,29192,33115,37128,37384,39176,39432]))]
noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1023,8659208,9741609,17318416],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,20744,26888,28168,29192,29960,33115,33460,37128,37384,39176,39432])),([6,31,1023,8659208,17318416,18400817],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,19124,20744,21000,24923,28936,29192,36360,37128,37384,39432,40200])),([6,31,1023,8659208,17318416,32472030],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,14856,15624,19124,20744,21000,24923,25268,28936,29192,36104,36360,37384,38152,39432,40200])),([6,31,1024,1082401,8659944,17318416],(decodeHints [52,616,1076,1588,2100,2612,3124,3636,4148,4660,14644,14952,15922,20786,21044,21812,25096,26932,27188,27954,29233,33384,35124,35380,36146,37172,37428])),([6,31,2016,1082401,8659208,17318416],(decodeHints [67,692,1091,1603,2115,2627,3139,3651,4163,4675,14687,14856,20797,25268,26939,27203,28995,29251,33460,37187,37443,39235,39491])),([6,31,2048,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,14642,14952,15922,20786,21042,21810,25096,26930,27186,27954,29233,33384,35122,35378,36146,37170,37426])),([6,31,8192,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,14642,14952,15922,20786,21042,21810,25096,26930,27186,27954,29233,33384,35122,35378,36146,37170,37426])),([6,31,9184,1082401,8659208,17318416],(decodeHints [76,692,1100,1612,2124,2636,3148,3660,4172,4684,14687,14856,20810,25268,26938,27212,29004,29260,33460,37196,37452,39244,39500])),([6,31,16384,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,14642,14952,15922,20786,21042,21810,25096,26930,27186,27954,29233,33384,35122,35378,36146,37170,37426])),([6,31,31744,1082401,8659944,16236015],(decodeHints [52,616,1076,1588,2100,2612,3124,3636,4148,4660,14791,14914,15922,20786,21044,21812,25096,26932,27954,29233,33332,35122,36148,37428,38196])),([6,31,31744,1082401,8659944,17318416],(decodeHints [52,616,1076,1588,2100,2612,3124,3636,4148,4660,14791,14914,15922,20786,21044,21812,25096,26932,27954,29233,33384,35124,36146,37172,37428])),([6,31,31744,1082401,8659944,17318431],(decodeHints [104,616,1128,1640,2152,2755,3176,3688,4200,4712,14696,14952,15976,18883,20931,21096,21864,24936,25192,26984,28008,29290,33384,34152,35176,36200,37410])),([6,31,31744,1082401,8659944,18400817],(decodeHints [52,720,1076,1588,2100,2612,3124,3636,4148,4660,14791,14914,15922,20786,21812,25096,26932,27954,28980,29233,33314,35122,36148,37428,38196])),([6,31,31744,1082401,8659967,17318416],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,4104,4616,14600,14952,15880,20744,21000,21768,25096,25864,26888,27912,29192,29960,33128,33384,35080,36104,37128,37384])),([6,31,31744,1082401,9742313,17318416],(decodeHints [49,618,1073,1585,2097,2609,3121,3633,4145,4657,14791,14914,15921,20785,21809,25096,26929,27953,29233,30001,33386,35121,36145,37169,37425])),([6,31,31744,1082401,17318416,24894487],(decodeHints [52,616,1076,1588,2100,2612,3124,3636,4148,4660,14791,14914,15922,20786,21044,21812,25192,26932,27954,28980,29236,33373,35122,36148,37425])),([6,31,31744,1083361,6494406,8659208],(decodeHints [74,661,1098,1610,2122,2634,3146,3658,4170,4682,14791,14914,15933,20810,21821,24977,25232,26954,27965,33428,35133,35402,36170,37177,38474,39242,39498])),([6,31,31744,1083361,8659208,18400817],(decodeHints [74,661,1098,1610,2122,2634,3146,3658,4170,4682,14791,14914,15933,20810,21821,25237,26941,27978,28985,29258,33311,35146,36157,39242,39498])),([6,31,31744,1113121,8659944,17318416],(decodeHints [52,616,1076,1588,2100,2612,3124,3636,4148,4660,14644,14952,21044,21812,25096,27954,33384,35124,37172])),([6,31,31744,8659208,17318416,33522721],(decodeHints [8,723,1032,1544,2056,2568,3080,3592,4104,4616,14791,14914,19155,20744,25042,25299,28936,29192,35080,35336,37384])),([6,31,31744,8659944,17318416,18400817],(decodeHints [52,707,1076,1588,2100,2612,3124,3636,4148,4660,14791,14914,15922,18952,20788,21810,26932,27954,29236,35122,35380,36148,39476,40244])),([6,31,31744,8659944,17318416,32472030],(decodeHints [52,707,1076,1588,2100,2612,3124,3636,4148,4660,14791,14914,15922,18952,20788,21810,25283,26932,27954,35124,35380,36146,38193,39476,40244])),([6,31,31775,1082401,8659944,17318416],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14914,15682,15976,20802,21810,25192,26930,27970,29250,33384,35138,36146,37186,37442])),([6,31,32736,1082401,8659944,17318416],(decodeHints [78,616,1102,1614,2126,2638,3150,3662,4174,4686,14790,14898,15922,20812,21812,25192,26932,27980,29262,33384,35150,36146,37198,37454])),([6,31,32736,1113121,8659208,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,14687,14856,20810,25284,26939,29006,33476,39246,39502])),([6,31,1047552,1082401,8659944,17318416],(decodeHints [53,616,1077,1589,2101,2613,3125,3637,4149,4661,14791,14914,15922,20786,21045,21813,25096,26933,27954,29233,33384,35125,36146,37173,37429])),([6,31,1047552,8659208,17318416,32539681],(decodeHints [8,723,1032,1544,2056,2568,3080,3592,4104,4616,14791,14914,19155,20744,25042,25299,28936,29192,35080,35336,37384])),([6,31,1048575,1082401,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,14898,15666,15976,20786,21810,22066,25096,26930,27954,29233,33384,35122,36146,37170,37426])),([6,31,1082401,1082401,8659944,17318416],(decodeHints [50,692,1074,1586,3122,3634,4146,4658,15028,16052,16690,16946,17714,17970,25096,26930,27185,27954,33460,35122,35378,36146])),([6,31,1082401,1082431,8659944,17318416],(decodeHints [180,692,1204,1716,2228,2740,3252,3736,4276,4788,15796,16052,19124,19892,20072,21172,21940,22066,24984,25268,27032,27316,28978,29364,30042,33204,33460,35252,35508,37210,37556,38194])),([6,31,1082401,1083361,6494406,8659208],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,15023,16011,18952,20797,21053,21821,24998,25268,26941,27197,27965,33460,35133,35389,36157,37177,38461,39229,39485])),([6,31,1082401,1083361,6494406,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,15020,18952,21053,21821,24998,25268,26941,27197,29245,33460,35133,35389,38461,39229,39485])),([6,31,1082401,1083361,8659208,16236015],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,15013,18952,21053,21821,25268,26941,27197,28985,29245,33341,35389,36157,39485,40253])),([6,31,1082401,1083361,8659208,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,15013,18952,21053,21821,25268,26941,27197,28985,29245,33460,35133,35389,39229,39485])),([6,31,1082401,1083361,8659208,17318431],(decodeHints [180,692,1204,1716,2228,2712,3252,3764,4276,4788,14772,15013,18796,19048,21172,21940,25012,25268,27060,27316,29108,29336,33460,34228,35095,35349,39348,39604])),([6,31,1082401,1083361,8659208,18400817],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,15023,16011,18952,20797,21053,21821,25268,26941,27197,27965,28985,29245,33301,35133,35389,36157,39229,39485])),([6,31,1082401,1083361,8659208,25977624],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,15013,18952,21053,21821,25268,26941,27197,28985,30269,33460,35133,35389,39485,40253])),([6,31,1082401,1083361,8659231,17318416],(decodeHints [180,692,1204,1716,2228,2712,3252,3764,4276,4788,14772,15013,18840,19048,21172,21940,25268,26036,27045,27150,29032,29198,33204,33460,35252,35508,39348,39604])),([6,31,1082401,1083361,8659944,17318416],(decodeHints [66,664,1090,1602,2114,2626,3138,3650,4162,4674,15000,18994,20148,21058,21826,22066,25102,27197,27970,28978,29245,30018,33432,35138,35394,37186,38194,39234])),([6,31,1082401,1083361,9741609,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,15020,18952,21053,21821,25102,27197,27965,28985,29245,33460,35133,35389,39229,39485])),([6,31,1082401,1083361,9742313,17318416],(decodeHints [61,664,1085,1597,2109,2621,3133,3645,4157,4669,15000,18993,20148,21053,21821,22065,25102,27197,27965,28977,29245,30013,33432,35133,35389,37181,38193,39229])),([6,31,1082401,1083361,17318416,24895223],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,15013,18952,21053,21821,25268,26941,27197,33368,35389,36157,37437,38201,39485,40253])),([6,31,1082401,1083361,17318416,25977624],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,15013,18952,21053,21821,25268,26941,27197,30269,33460,35133,35389,37437,39485,40253])),([6,31,1082401,1083391,8659208,17318416],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,4104,4616,18952,19720,21000,21768,25192,26888,27144,28936,29192,33128,33384,35080,35336,39176,39432])),([6,31,1082401,1113121,8659944,17318416],(decodeHints [50,707,1074,1586,2098,2610,3122,3634,4146,4658,15043,19010,20148,21042,21810,22066,25096,27185,27954,28978,30002,33475,35122,35378,37170,38194])),([6,31,1082401,2164802,4329604,33553695],(decodeHints [58,714,1082,1594,2106,2618,3130,3642,4154,4666,18432,18890,19144,20794,21050,25034,25289,26938,27194,28986,29242,33338,34106,35385,36154])),([6,31,1082401,2164802,8659944,12988812],(decodeHints [55,720,1079,1591,2103,2615,3127,3639,4151,4663,18896,19149,20791,21047,25096,26935,27190,33486,35127,35383,37175,37431])),([6,31,1082401,2164802,8659944,16236015],(decodeHints [55,625,1079,1591,2103,2615,3127,3639,4151,4663,18801,19056,20018,20791,21047,22066,25096,27190,28978,30007,33335,35383,36151,37170,37431,38199])),([6,31,1082401,2164802,8659944,17318416],(decodeHints [55,625,1079,1591,2103,2615,3127,3639,4151,4663,18801,19056,20018,20791,21047,22066,25096,27190,28978,30007,33393,35127,35383,37175,37431,38194])),([6,31,1082401,2164802,8659944,17318431],(decodeHints [113,625,1137,1716,2161,2673,3185,3697,4209,4721,14772,18801,19056,20073,20742,21096,22120,24945,25201,27250,29033,30064,33393,34161,35371,37232,37489,38249])),([6,31,1082401,2164802,8659944,18400817],(decodeHints [55,720,1079,1591,2103,2615,3127,3639,4151,4663,18896,19152,20018,20791,21047,22066,25096,26935,27190,28978,30007,33323,35383,36151,37175,37431,38194])),([6,31,1082401,2164802,8659944,19483218],(decodeHints [55,625,1079,1591,2103,2615,3127,3639,4151,4663,18801,19057,20791,21047,25096,27190,33393,35127,35383,37431,38199])),([6,31,1082401,2164802,8659967,17318416],(decodeHints [8,625,1032,1544,2056,2568,3080,3592,4104,4616,19056,20006,20744,21000,22024,25096,25864,27144,27912,28936,29960,33137,33393,35080,35336,37128,37384,38152])),([6,31,1082401,2164802,9742313,17318416],(decodeHints [54,626,1078,1590,2102,2614,3126,3638,4150,4662,18802,19058,20017,20790,21046,22065,25096,27190,27958,28977,30006,33394,35126,35382,37174,37430,38193])),([6,31,1082401,2164802,17318416,24894487],(decodeHints [55,625,1079,1591,2103,2615,3127,3639,4151,4663,18801,19056,20018,20791,21047,22066,25201,26935,27191,28983,29239,30002,33370,35382,37175,38194])),([6,31,1082401,2164831,8659944,17318416],(decodeHints [112,624,1136,1716,2160,2672,3184,3696,4208,4720,14772,19056,19824,20072,21042,22196,25200,25968,27250,29032,30002,33136,33392,35252,35536,37232,37488,38194])),([6,31,1082401,2165730,4330468,17318416],(decodeHints [66,618,1090,1602,2114,2626,3138,3650,4162,4674,18794,19048,21058,24938,25193,27202,33386,35138,35394,37186,38466,39234,40514])),([6,31,1082401,2165730,8659944,17318416],(decodeHints [66,617,1090,1602,2114,2626,3138,3650,4162,4674,18793,19048,20018,21058,22066,25193,27202,28978,30018,33385,35138,35394,37186,38194,39234])),([6,31,1082401,2194498,8659944,17318416],(decodeHints [56,625,1080,1592,2104,2616,3128,3640,4152,4664,18801,18994,20018,20792,21047,22068,25096,27190,28980,30007,33393,35128,35384,37176,38194])),([6,31,1082401,3247203,8659944,17318416],(decodeHints [55,616,1079,1591,2103,2615,3127,3639,4151,4663,18994,20072,21047,21815,22066,25096,27190,28978,30007,33384,35127,35383,37175,37431,38194])),([6,31,1082401,6494406,8659208,8659944],(decodeHints [58,720,1082,1594,2106,2618,3130,3642,4154,4666,18896,19149,20794,21050,25296,26938,27194,28986,29242,33288,35130,35385,39482,40250])),([6,31,1082401,6494406,8659208,33553439],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,4162,4674,18896,19149,20802,21058,25295,26946,27202,28994,29250,33346,34114,35389,36162,39234,39482])),([6,31,1082401,6494406,8659944,17318416],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,4154,4666,14895,18746,19059,20018,20794,21050,22066,25096,27193,27962,28978,30010,33400,35130,35386,37178,37434,38194,40506])),([6,31,1082401,6494406,17318416,33553439],(decodeHints [66,631,1090,1602,2114,2626,3138,3650,4162,4674,18807,19059,20802,21058,25207,26946,27202,28994,29250,33346,34114,35389,38210,39234]))]
noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1082401,8658952,17318416,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,19048,20802,21058,25192,26946,27202,28994,29250,33346,34114,35389,37442,38210])),([6,31,1082401,8659208,8659944,16236015],(decodeHints [58,616,1082,1594,2106,2618,3130,3642,4154,4666,19048,20058,20794,21050,22066,25096,27193,28978,29242,30010,33338,35386,36154,37170,37434,38202])),([6,31,1082401,8659208,8659944,17318416],(decodeHints [58,616,1082,1594,2106,2618,3130,3642,4154,4666,19048,20058,20794,21050,22066,25096,27193,28978,29242,30010,33384,35130,35386,37178,37434,38194])),([6,31,1082401,8659208,8659944,17318431],(decodeHints [104,616,1128,1716,2152,2664,3176,3688,4200,4712,14772,18792,19048,20072,20916,21172,22120,24936,25192,27316,29032,29288,30056,33384,34152,35353,37224,37480,38248])),([6,31,1082401,8659208,8659944,18400817],(decodeHints [58,720,1082,1594,2106,2618,3130,3642,4154,4666,19152,20058,20794,21050,22066,25096,26938,27193,28978,29242,30010,33305,35386,36154,37178,37434,38194])),([6,31,1082401,8659208,8659944,25977624],(decodeHints [58,616,1082,1594,2106,2618,3130,3642,4154,4666,19048,20794,21050,25096,27193,29242,30010,33384,35130,35386,37434,38202])),([6,31,1082401,8659208,8659967,17318416],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,4104,4616,19048,19976,20744,21000,22024,25096,25864,27144,27912,28936,29192,29960,33128,33384,35080,35336,37128,37384,38152])),([6,31,1082401,8659208,9742313,17318416],(decodeHints [57,692,1081,1593,2105,2617,3129,3641,4153,4665,15013,19050,20056,20793,21049,22065,25096,27193,27961,28977,29241,30009,33460,35129,35385,37177,37433,38193])),([6,31,1082401,8659208,16236015,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,19048,20802,21058,25154,27202,27970,29250,30018,33346,34114,35389,37434,38210])),([6,31,1082401,8659208,17318416,24894487],(decodeHints [58,616,1082,1594,2106,2618,3130,3642,4154,4666,19048,20058,20794,21050,22066,25192,26938,27194,28986,29242,30002,33370,35385,37178,37434,38194])),([6,31,1082401,8659208,17318416,32471070],(decodeHints [61,664,1085,1597,2109,2621,3133,3645,4157,4669,15000,19096,20797,21053,25240,26941,27197,28989,29245,33384,35133,35389,37433,38205])),([6,31,1082401,8659208,17318416,33553408],(decodeHints [8,616,1032,1544,2056,2568,3080,3592,4104,4616,19048,20744,21000,24936,25192,26888,27144,28936,29192,33128,33346,35080,35336,37384,38152])),([6,31,1082401,8659208,17318416,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,19048,20802,21058,25192,26946,27202,28994,29250,33346,34114,35389,37434,38210])),([6,31,1082401,8659208,17318416,33553471],(decodeHints [61,664,1085,1597,2109,2621,3133,3645,4157,4669,16022,19096,20797,21053,25240,26941,27197,28989,29245,33341,34109,35389,36157,37433,38205])),([6,31,1082401,8659208,17318416,33553695],(decodeHints [58,616,1082,1594,2106,2618,3130,3642,4154,4666,19048,20794,21050,25192,26938,27194,28986,29242,33338,34106,35385,37434,38202])),([6,31,1082401,8659208,17318431,33553439],(decodeHints [104,616,1128,1688,2152,2664,3176,3688,4200,4788,14743,18792,19048,20782,21111,25192,25960,27161,29032,29288,33384,34152,35480,37480,38248])),([6,31,1082401,8659208,18400817,33553439],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,4162,4674,19152,20802,21058,25113,27202,27970,28994,29250,33346,34114,35389,36162,37434,38210])),([6,31,1082401,8659208,25977624,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,19048,20802,21058,25192,26946,27202,29250,30018,33346,34114,35389,37186,37434])),([6,31,1082401,8659231,8659944,17318416],(decodeHints [104,616,1128,1716,2152,2664,3176,3688,4200,4712,14772,19048,19816,20072,21050,22196,25192,25960,27242,29032,29288,30010,33128,33384,35252,35536,37224,37480,38194])),([6,31,1082401,8659231,8659967,17318416],(decodeHints [104,616,1128,1716,2152,2664,3176,3688,4200,4712,14772,19048,19816,20072,21003,22196,25192,25960,27240,28008,28936,29288,30056,33128,33384,35252,35536,37224,37480,38152])),([6,31,1082401,8659231,17318416,33553439],(decodeHints [104,616,1128,1688,2152,2664,3176,3688,4200,4788,14744,19048,19816,21011,24936,25192,26965,27344,29032,29288,33384,34152,35480,37480,38248])),([6,31,1082401,8659944,8659944,17318416],(decodeHints [50,616,1074,1586,2098,2610,4146,4658,19048,20058,21042,22066,22834,23090,23858,24114,33384,35122,35378,37170,38194])),([6,31,1082401,8659944,8659967,17318416],(decodeHints [104,616,1128,1688,2152,2664,3176,3688,4200,4712,14744,18952,19816,19976,21041,22196,25192,25960,26216,27186,28008,28340,28936,29288,30056,30258,33128,33384,35157,35536,37224,38152,39272,40242])),([6,31,1082401,8659944,8682760,17318416],(decodeHints [59,616,1083,1595,2107,2619,3131,3643,4155,4667,18952,21049,25146,26202,26939,27194,28212,29236,30266,33384,35131,35387,39227,40242])),([6,31,1082401,8659944,8683496,17318416],(decodeHints [52,616,1076,1588,2100,2612,3124,3636,4148,4660,19048,21044,25138,26202,27186,28212,29236,30004,30258,33384,35124,35380,39220,40242])),([6,31,1082401,8659944,9741609,17318416],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,4154,4666,14895,18952,21049,21818,25146,26292,27194,27962,28210,28985,29234,30266,33460,35130,35386,39226,39482,40242])),([6,31,1082401,8659944,9742313,17318416],(decodeHints [50,664,1074,1586,2098,2610,3122,3634,4146,4658,15000,18993,20056,21041,21810,22066,25138,26292,27186,27954,28210,28977,29234,30002,30258,33432,35122,35378,37170,38193,39218,40242])),([6,31,1082401,8659944,10824010,17318416],(decodeHints [50,625,1074,1586,2098,2610,3122,3634,4146,4658,18952,21041,25200,26202,26930,27186,28210,29234,30258,33393,35122,35378,39218,39474,40242])),([6,31,1082401,8659944,10824682,17318416],(decodeHints [50,617,1074,1586,2098,2610,3122,3634,4146,4658,19049,21042,25192,26202,27186,28210,29234,30002,30258,33385,35122,35378,37170,39218,40242])),([6,31,1082401,8659944,16236015],(decodeHints [360,872,1330,1842,2354,2866,3378,3890,15284,16308,19304,20314,21298,22322,25394,26472,27442,28466,29490,30514])),([6,31,1082401,8659944,16236015,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,18952,21041,25138,26216,27186,27954,28210,29234,30258,33384,34354,35122,35378,36402,37426,38450,39218,39474,40242,40498])),([6,31,1082401,8659944,17318416],(decodeHints [360,872,1330,1842,2354,2866,3378,3890,15284,16308,19304,20314,21298,22322,25448,26418,27442,28466,29490,30514])),([6,31,1082401,8659944,17318416,17318416],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,18952,21041,25192,26162,26930,27186,28210,29234,30258,31026,31282,32050,32306])),([6,31,1082401,8659944,17318416,17318431],(decodeHints [104,616,1128,1716,2152,2664,3176,3688,4200,4712,14772,18792,19048,21098,25192,25960,26216,27060,27316,28264,29288,30312,33384,34152,34408,35418,36532,37480,38490,39272,39528,40296,40498])),([6,31,1082401,8659944,17318416,17318896],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,19048,21058,25192,26946,27202,30274,33384,34354,35394,36402,37426,38466,39490,40258,40498])),([6,31,1082401,8659944,17318416,17333776],(decodeHints [52,616,1076,1588,2100,2612,3124,3636,4148,4660,18952,21041,25192,26932,27188,33346,34354,35124,35378,36404,37428,38450,39476,40244,40498])),([6,31,1082401,8659944,17318416,18400817],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,4146,4658,15028,16052,18952,20786,21041,21810,25268,26162,26930,27186,27954,28210,29234,30258,33370,34484,35122,35378,36146,36402,37426,38450,39218,39474,40242,40498])),([6,31,1082401,8659944,17318416,19483218],(decodeHints [55,625,1079,1591,2103,2615,3127,3639,4151,4663,18952,21046,25201,26935,27191,33392,34354,35127,35383,36402,37426,38455,39479,40247,40498])),([6,31,1082401,8659944,17318416,24894487],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,19048,20058,21042,22066,25192,26930,27186,28978,30002,33370,34408,35378,36402,37170,37426,38194,38450,39474,40498])),([6,31,1082401,8659944,17318416,24895223],(decodeHints [58,616,1082,1594,2106,2618,3130,3642,4154,4666,18952,21049,25192,26938,27194,33330,34408,35386,36154,36402,37426,38202,38458,39482,40250,40498])),([6,31,1082401,8659944,17318416,25977624],(decodeHints [58,616,1082,1594,2106,2618,3130,3642,4154,4666,18952,21049,25192,26938,27194,30266,33384,34408,35130,35386,36402,37426,38458,39482,40250,40498])),([6,31,1082401,8659944,17318416,25977848],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,19048,21042,25192,26930,27186,30002,30258,33384,34408,35378,36402,37426,38194,38450,39474,40242,40498])),([6,31,1082401,8659944,17318416,29224827],(decodeHints [50,616,1074,1586,2098,2610,3122,3634,4146,4658,18952,21041,25192,26930,27186,33330,34098,34408,35378,36146,36402,37426,38450,39474,40242,40498])),([6,31,1082401,8659944,17318416,32472030],(decodeHints [50,692,1074,1586,2098,2610,3122,3634,4146,4658,15028,16052,18952,20786,21041,21810,25268,26930,27186,27954,33460,34484,35122,35378,36146,36402,37426,38193,38450,39474,40242,40498])),([6,31,1082401,8659944,17318416,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,19048,21058,25192,26946,27202,28994,33346,34114,34408,35394,36402,37426,38210,38466,39490,40498])),([6,31,1082401,8659944,17318416,33554400],(decodeHints [104,616,1128,1716,2152,2664,3176,3688,4200,4712,14772,15796,18792,19048,19816,21098,24936,25192,25960,27060,27344,33128,33330,34152,34354,35508,36532,37480,38248,38490,39528,40296,40498])),([6,31,1082401,8659944,17318431],(decodeHints [360,872,1460,1972,2408,2920,3432,3944,15284,16308,19304,20328,21400,22452,25448,26472,27572,28596,29544,30568])),([6,31,1082401,8659944,18400817],(decodeHints [464,976,1330,1842,2354,2866,3378,3890,15284,16308,19408,20314,21298,22322,25434,26576,27442,28466,29490,30514])),([6,31,1082401,8659967,17318416],(decodeHints [360,872,1288,1800,2312,2824,3336,3848,15284,16308,19208,20328,21256,22280,25448,26376,27400,28424,29448,30472])),([6,31,1082401,9741609,9742313,17318416],(decodeHints [57,631,1081,1593,2105,2617,3129,3641,4153,4665,19001,20074,21049,21817,22065,25096,27193,27961,28977,29241,30009,33399,35129,35385,37177,37433,38193])),([6,31,1082401,9741609,17318416,33553439],(decodeHints [66,631,1090,1602,2114,2626,3138,3650,4162,4674,18963,21058,21826,25207,26946,27202,28994,29250,33346,34114,35389,37433,38210])),([6,31,1082401,9742313,17318416],(decodeHints [362,874,1329,1841,2353,2865,3377,3889,15284,16308,19249,20330,21297,22321,25450,26417,27441,28465,29489,30513])),([6,31,1082401,17318416,24894487],(decodeHints [360,872,1330,1842,2354,2866,3378,3890,15256,16280,19304,20274,21298,22322,25434,26472,27442,28466,29490,30514])),([6,31,1082401,17318416,24895223,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,19048,20802,21058,25178,27202,27970,29250,30018,33346,34114,35389,40258,40506])),([6,31,1082401,17318416,25977624,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,19048,20802,21058,25192,26946,27202,29250,30018,33346,34114,35389,37186,40258])),([6,31,1082431,1083361,8659208,17318416],(decodeHints [165,677,1189,1701,2213,2712,3237,3749,4261,4773,15013,15781,19892,21821,24997,25253,26941,27301,29093,29336,33189,33445,35160,35493,39333,39589])),([6,31,1083361,1113121,8659208,17318416],(decodeHints [74,708,1098,1610,2122,2634,3146,3658,4170,4682,14856,19005,20810,22077,25284,26937,27210,28989,33476,37194,39242,39498])),([6,31,1083361,2164802,4329604,8659208],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,4157,4669,18432,18817,19072,24965,25219,28989,29245,33414,35129,36413,37181,37437,39229,39485])),([6,31,1083361,2164802,4329604,8659231],(decodeHints [134,646,1158,1752,2182,2694,3206,3718,4230,4742,14808,18432,18822,19072,24966,25219,29062,29318,33414,34182,36479,37248,37510,39299,39558])),([6,31,1083361,2164802,4329604,10824010],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,4157,4669,18432,18817,19080,21053,24965,25219,28989,29245,33414,36413,37437,38205,39229,39485])),([6,31,1083361,2164802,4329604,18400817],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,4157,4669,18432,18817,19080,21053,24965,25224,27197,28989,29245,33349,36413,37181,37437,39229,39485])),([6,31,1083361,2164802,4329604,24895223],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,4157,4669,18432,18817,19072,24965,25219,28989,29245,33349,36153,36413,37437,38205,39485,40253])),([6,31,1083361,2164802,4329631,8659208],(decodeHints [131,643,1155,1752,2179,2691,3203,3715,4227,4739,14808,15749,18819,19072,19843,24963,25219,25987,29056,29315,33155,33411,34179,35288,36476,37251,37507,39299,39555])),([6,31,1083361,2164802,6494406,8659208],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,4157,4669,18817,19080,20029,21053,22077,24961,25219,28989,29245,30013,33414,35129,36413,37181,37437,38205,39229,39485]))]
noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1083361,2164802,8659208,12988812],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,4157,4669,18817,19072,25224,26937,27197,28989,29245,33411,37181,37437,39485,40253])),([6,31,1083361,2164802,8659208,18400817],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,4157,4669,18817,19080,20029,21053,22077,25224,26937,27197,28989,29245,30013,33322,37181,37437,38205,39229,39485])),([6,31,1083361,2164802,8659208,29224827],(decodeHints [61,648,1085,1597,2109,2621,3133,3645,4157,4669,18817,19072,25222,26937,28221,28989,29245,33322,34109,37437,38205,39485,40253])),([6,31,1083361,6494406,8659208,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,14856,18854,19109,22077,25260,26937,28221,28989,29245,33369,34365,35389,36413,37181,37437,38461,39229,39485,40509])),([6,31,1083361,8659208,9741609,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,14856,19116,20793,22077,25149,26937,28221,29245,30013,33460,37181,37437,39229,39485])),([6,31,1083361,8659208,17318416,18400817],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,14856,19124,20793,21053,25177,26173,27197,28221,28989,29245,30269,33368,36413,37181,37437,39229,39485,40253])),([6,31,1083361,8659208,17318416,32472030],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,14856,19124,20793,21053,25268,28989,29245,33445,36157,36413,37437,38205,39485,40253])),([6,31,1083361,8659208,18400817],(decodeHints [392,904,1341,1853,2365,2877,3389,3901,15215,16267,19336,20312,21309,22333,25432,26504,27453,28477,29501,30525])),([6,31,1113121,1114081,8659208,17318416],(decodeHints [74,622,1098,1610,2122,2634,3146,3658,4170,4682,14958,18952,21066,21834,25198,26954,28985,33390,39242,39498])),([6,31,1113121,8659208,8659944,17318416],(decodeHints [58,616,1082,1594,2106,2618,3130,3642,4154,4666,19048,20794,22066,25096,27193,29242,30010,33384,35130,37178,37434])),([6,31,1113121,8659208,17318416,33553439],(decodeHints [76,616,1100,1612,2124,2636,3148,3660,4172,4684,19048,20802,25192,26956,29004,29260,33356,34124,35402,37434,38220])),([6,31,2164802,3247203,8659944,17318416],(decodeHints [55,518,1079,1591,2103,2615,3127,3639,4151,4663,14647,21047,21815,25096,33286,35127,35383,37175,37431])),([6,31,2164802,4329604,8659208,9742313],(decodeHints [57,728,1081,1593,2105,2617,3129,3641,4153,4665,14336,14649,15064,18904,19160,20793,21049,26624,26937,27193,28985,29241,39481,40249])),([6,31,2164802,4329604,8659208,32471070],(decodeHints [61,728,1085,1597,2109,2621,3133,3645,4157,4669,14336,14653,15064,18904,19160,20797,21053,25304,26941,27197,28989,29245,39229,39481])),([6,31,2164802,8659944,12988812,17318416],(decodeHints [55,518,1079,1591,2103,2615,3127,3639,4151,4663,14647,18952,26935,27191,35127,35383,37431,39223,39479])),([6,31,2164802,8659944,17318416,18400817],(decodeHints [55,692,1079,1591,2103,2615,3127,3639,4151,4663,14647,15028,15922,18952,20786,21815,26935,27191,27954,29239,35127,35383,36146,39479,40247])),([6,31,2164802,8659944,17318416,32472030],(decodeHints [55,692,1079,1591,2103,2615,3127,3639,4151,4663,14647,15028,15922,18952,20786,21815,25268,26935,27191,27954,35122,35383,36151,38198,39479,40247])),([6,31,6494406,8659208,8659944,17318416],(decodeHints [58,518,1082,1594,2106,2618,3130,3642,4154,4666,14650,18950,20794,21050,25096,29242,30010,35130,35386,37178,37434,39482])),([6,31,6494406,8659208,17318416,33553439],(decodeHints [66,518,1090,1602,2114,2626,3138,3650,4162,4674,14658,20802,21058,26946,27202,28994,29250,33346,34114,37434,40258])),([6,31,8659208,8659944,9741609,17318416],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,4154,4666,14895,18952,21050,21818,27194,27962,28985,33460,35130,35386,39226,39482])),([6,31,8659208,8659944,17318416,18400817],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,4154,4666,15028,15962,18952,20786,21050,21818,26938,27194,27954,29242,35130,35386,36146,39482,40250])),([6,31,8659208,8659944,17318416,32472030],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,4154,4666,15028,15962,18952,20786,21050,21818,25268,26938,27194,27954,35122,35386,36154,38201,39482,40250])),([6,31,8659208,9741609,9742313,17318416],(decodeHints [57,558,1081,1593,2105,2617,3129,3641,4153,4665,19001,21049,21817,25096,27193,27961,29241,30009,33326,35129,35385,37177,37433])),([6,31,8659208,9741609,17318416,33553439],(decodeHints [66,558,1090,1602,2114,2626,3138,3650,4162,4674,21058,21826,25134,26946,27202,28994,29250,33346,34114,35386,37433])),([6,31,8659208,17318416,18400817,33553439],(decodeHints [66,597,1090,1602,2114,2626,3138,3650,4162,4674,14933,20802,21058,26946,27202,29250,30018,33346,34114,35386,36162,38210])),([6,31,8659208,17318416,32472030,33553439],(decodeHints [66,664,1090,1602,2114,2626,3138,3650,4162,4674,15000,19096,20802,21058,27202,27970,29250,30018,33346,34114,35386,36162,40509])),([6,31,8659944,17318416,18400817],(decodeHints [436,948,1330,1842,2354,2866,3378,3890,15189,16218,19380,20274,21298,22322,25434,26548,27442,28466,29490,30514])),([6,31,8659944,17318416,32472030],(decodeHints [436,948,1330,1842,2354,2866,3378,3890,15256,16218,19380,20274,21298,22322,25524,26548,27442,28466,29490,30514])),([6,33,992,1023,8659208,17318416],(decodeHints [104,607,1128,1640,2152,2664,3176,3688,4200,4712,19048,19816,21096,21864,24927,25207,27240,29288,33119,33375,35176,39272,39528])),([6,63,992,1082401,8659208,17318416],(decodeHints [66,614,1090,1602,2114,2626,3138,3650,4162,4674,14687,20069,21058,25190,26938,27202,28994,29250,33382,37186,37442,39234,39490])),([6,95,992,1082401,8659208,17318416],(decodeHints [66,678,1090,1602,2114,2626,3138,3650,4162,4674,14687,20797,25254,26938,27202,28994,29250,33304,37186,37442,39234,39490])),([6,256,992,1082401,2164802,4329631],(decodeHints [160,672,1184,1740,2208,2720,3232,3744,4256,4768,15008,15776,18848,19104,20896,21196,24576,24992,25248,29088,29344,33184,33440,39326,39581])),([6,287,992,1082401,2164802,4329604],(decodeHints [65,674,1089,1601,2113,2625,3137,3649,4161,4673,20797,21056,24576,24989,25247,28993,29249,33184,33441,37185,37441,39233,39489])),([6,287,992,1082401,8659208,17318416],(decodeHints [66,686,1090,1602,2114,2626,3138,3650,4162,4674,14687,20797,25256,27202,28994,29250,33454,37186,37442,39234,39490])),([6,512,992,1082401,2164802,4329631],(decodeHints [117,629,1141,1653,2165,2601,3189,3701,4213,4725,14965,15733,18729,19061,20776,24949,25205,27241,28934,29288,33141,33397,35423,39283,39541])),([6,543,992,1082401,2164802,4329604],(decodeHints [66,631,1090,1602,2114,2626,3138,3650,4162,4674,14856,20797,24951,25203,27202,28994,29250,33143,33397,35394,37186,37442,39234,39490])),([6,543,992,1082401,8659208,17318416],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25192,26938,27202,28994,29250,33384,35138,35394,37186,37442,39234,39490])),([6,992,1023,1082401,6494406,8659208],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,19010,26975,29023,29279,34399,36447,37215,37471,39263,39519])),([6,992,1023,1082401,6494406,17318416],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,25154,26975,27231,29023,29279,33090,34399,36447,37215,37471,39263,39519])),([6,992,1023,1082401,8659208,16236015],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,22120,25154,27231,29023,29279,34143,37471,38239,39519,40287])),([6,992,1023,1082401,8659208,17318416],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,22120,25154,27231,29023,29279,33090,37215,37471,39263,39519])),([6,992,1023,1082401,8659208,17318431],(decodeHints [104,616,1128,1640,2152,2712,3176,3688,4200,4712,14696,14952,15720,18796,19739,20840,22120,24936,25192,25883,26984,27240,28974,29303,33128,34075,36200,37401,39272,39528])),([6,992,1023,1082401,8659208,18400817],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,19010,25154,27231,29023,29279,37471,38239,39263,39519])),([6,992,1023,1082401,8659208,25977624],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,22120,26207,28255,29023,29279,37215,37471,39519,40287])),([6,992,1023,1082401,8659231,17318416],(decodeHints [104,616,1128,1640,2152,2712,3176,3688,4200,4712,14952,15720,18840,20840,22120,25183,25876,27231,28072,29281,33128,35240,37205,37584,39272,39528])),([6,992,1023,1082401,8659944,17318416],(decodeHints [66,578,1090,1640,2114,2626,3138,3650,4162,4674,14914,15682,18754,22120,25154,25922,27231,29284,33090,37186,37442,39234])),([6,992,1023,1082401,8659967,17318416],(decodeHints [95,616,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,20831,22120,25183,25951,27231,27999,29279,30056,33128,35167,37215,37471,39263])),([6,992,1023,1082401,9741609,17318416],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,25188,27231,29279,30047,33090,37215,37471,39263,39519])),([6,992,1023,1082401,17318416,24895223],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,22120,24898,29023,29279,33375,35423,37471,38239,39519,40287])),([6,992,1023,1082401,17318416,25977624],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,22120,24898,26207,28255,29023,29279,33346,35423,37215,37471,39519,40287])),([6,992,1023,1113121,8659208,17318416],(decodeHints [95,588,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,22120,25164,27231,29023,33100,37215,39263,39519])),([6,992,1023,6494406,8659208,17318416],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,20831,22022,29023,29279,33090,33346,37215,37471,39263,39519])),([6,992,1023,8659208,9741609,17318416],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,28264,29279,30047,33090,37215,37471,39263,39519])),([6,992,1023,8659208,17318416,18400817],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,19010,21087,24898,25154,29023,29279,36456,37215,37471,39519,40287])),([6,992,1023,8659208,17318416,32472030],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,14943,15711,19010,21087,24898,29023,29279,36358,37471,38239,39519,40287])),([6,992,2079,1082401,8659208,17318416],(decodeHints [182,578,1206,1718,2230,2742,3254,3766,4278,4790,14600,14943,18749,24890,25154,27318,29110,29366,35510,37302,37558,39350,39606])),([6,992,31744,1082401,6494431,8659208],(decodeHints [188,717,1212,1724,2236,2748,3260,3772,4284,4796,14803,15028,16038,18876,19149,20924,21926,27068,28070,33229,34489,35260,35516,36262,37308,37564,39612])),([6,992,31744,1082401,6494431,17318416],(decodeHints [188,627,1212,1724,2236,2748,3260,3772,4284,4796,14803,15028,16038,18876,20924,21926,25183,27068,28070,34419,35238,35516,36284,37308,37564,39612])),([6,992,31744,1082401,8659231,17318431],(decodeHints [196,616,1220,1732,2244,2756,3268,3780,4292,4804,14803,15028,16052,18884,20932,21188,21940,24936,25192,27076,28084,29380,35256,36290,37572])),([6,992,1082401,1082431,8659208,17318431],(decodeHints [180,663,1204,1716,2228,2740,3252,3764,4276,4788,14772,14999,18868,19048,21172,21940,25012,25239,27060,27316,29108,29364,36276,38324,39348,39604])),([6,992,1082401,1082431,8659231,17318416],(decodeHints [180,664,1204,1716,2228,2740,3252,3764,4276,4788,14772,15000,18868,19048,21172,21940,25012,25240,28084,30132,35252,35508,37300,37556,39348,39604])),([6,992,1082401,2164802,4329631,8659208],(decodeHints [171,718,1195,1707,2219,2731,3243,3755,4267,4779,14763,15054,20907,21163,29095,29350,33230,34464,35243,35499,37291,37547,39595])),([6,992,1082401,2164802,4329631,8659231],(decodeHints [180,718,1204,1716,2228,2740,3252,3764,4276,4788,14772,15054,20916,21172,27316,29108,29364,33230,34464,35508,37300,37556,39595])),([6,992,1082401,2164802,4329631,8682760],(decodeHints [190,716,1214,1726,2238,2750,3262,3774,4286,4798,14782,15052,20926,21182,29117,29372,33225,34464,35518,37566,39614]))]
noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([6,992,1082401,2164802,4329631,9741609],(decodeHints [171,631,1195,1707,2219,2731,3243,3755,4267,4779,14763,20480,20907,21163,29095,29350,33143,34464,35499,36267,37291,37547,39595])),([6,992,1082401,2164802,4329631,10824010],(decodeHints [171,718,1195,1707,2219,2731,3243,3755,4267,4779,14763,15054,19150,20480,20907,21163,29099,29350,34464,35243,35499,37547,38315,39595])),([6,992,1082401,2164802,4329631,12988812],(decodeHints [171,720,1195,1707,2219,2731,3243,3755,4267,4779,14763,15056,20907,21163,25183,28672,29099,29350,34467,35243,35499,37291,37547,39595])),([6,992,1082401,2164802,4329631,12988831],(decodeHints [171,718,1195,1707,2219,2731,3243,3755,4267,4779,14763,15054,20907,21163,25294,27307,28672,29095,29355,34467,35499,37287,37547,39595,40363])),([6,992,1082401,2164802,4329631,16236015],(decodeHints [171,629,1195,1707,2219,2731,3243,3755,4267,4779,14763,19049,20907,21163,25183,29095,29350,34421,35499,36267,37547,38315,39595])),([6,992,1082401,2164802,4329631,17318416],(decodeHints [171,629,1195,1707,2219,2731,3243,3755,4267,4779,14763,19049,20907,21163,25183,29095,29350,34421,35243,35499,37291,37547,39595])),([6,992,1082401,2164802,4329631,17318431],(decodeHints [180,629,1204,1716,2228,2740,3252,3764,4276,4788,14772,19049,20916,21172,25201,27316,29108,29364,34421,35508,37300,37556,39595])),([6,992,1082401,2164802,4329631,17333776],(decodeHints [160,629,1184,1696,2208,2720,3232,3744,4256,4768,14752,19049,20896,21152,25183,29086,29341,34421,35488,37536,39584])),([6,992,1082401,2164802,4329631,18400817],(decodeHints [171,720,1195,1707,2219,2731,3243,3755,4267,4779,14763,15056,19152,20480,20907,21163,25183,29095,29350,34508,35499,36267,37291,37547,39595])),([6,992,1082401,2164802,4329631,19483218],(decodeHints [171,629,1195,1707,2219,2731,3243,3755,4267,4779,14763,20480,20907,21163,25183,29099,29350,34421,35243,35499,37547,38315,39595])),([6,992,1082401,2164802,4329631,21648020],(decodeHints [171,631,1195,1707,2219,2731,3243,3755,4267,4779,14763,19050,20907,21163,28672,29099,29350,34421,35243,35499,37291,37547,39595])),([6,992,1082401,2164802,4329631,21648031],(decodeHints [171,629,1195,1707,2219,2731,3243,3755,4267,4779,14763,19049,20907,21163,27307,28672,29095,29355,34421,35499,37287,37547,39595,40363])),([6,992,1082401,2164802,4329631,24895223],(decodeHints [171,718,1195,1707,2219,2731,3243,3755,4267,4779,14763,15054,20907,21163,29095,29350,34219,34508,35499,36267,37547,38315,39595])),([6,992,1082401,2164802,4330495,17318416],(decodeHints [95,625,1119,1631,2143,2655,3167,3679,4191,4703,19049,20831,21087,25183,25951,29023,29279,33137,34399,35167,35423,37215,37471,40543])),([6,992,1082401,2164802,6494431,8659208],(decodeHints [166,718,1190,1702,2214,2726,3238,3750,4262,4774,14758,15054,19150,20135,20902,21158,22182,29094,29350,30118,33230,34461,35238,35494,37286,37542,38310,39590])),([6,992,1082401,2164802,6494431,17318416],(decodeHints [166,629,1190,1702,2214,2726,3238,3750,4262,4774,14758,19061,20135,20902,21158,22182,25183,29094,29350,30118,34421,35238,35494,37286,37542,38310,39590])),([6,992,1082401,2164802,8659208,29224800],(decodeHints [171,718,1195,1707,2219,2731,3243,3755,4267,4779,14763,15054,20907,21163,25038,26272,27051,27307,29099,29355,37542,38311,40363])),([6,992,1082401,2164802,8659231,17318431],(decodeHints [180,625,1204,1716,2228,2740,3252,3764,4276,4788,14772,19049,20149,20916,21172,22196,24945,25201,27316,29108,29364,30132,35508,37300,37556,38324])),([6,992,1082401,2164802,17318416,29224800],(decodeHints [171,629,1195,1707,2219,2731,3243,3755,4267,4779,14763,19049,20907,21163,26229,27051,27307,29099,29355,33460,37542,38311,40363])),([6,992,1082401,2164831,4329631,8659208],(decodeHints [180,717,1204,1716,2228,2740,3252,3764,4276,4788,14772,15053,21172,27316,29095,29350,33229,34467,35252,35508,37300,37556,39348,39604])),([6,992,1082401,2164831,4329631,17318416],(decodeHints [180,627,1204,1716,2228,2740,3252,3764,4276,4788,14772,19048,21172,25200,27316,29095,29350,34419,35252,35508,37300,37556,39348,39604])),([6,992,1082401,2164831,4330468,17318416],(decodeHints [112,624,1136,1555,2160,2672,3184,3696,4208,4720,14611,19048,25200,25968,27249,29032,29296,33136,34416,35091,35536,37488,39338,40560])),([6,992,1082401,2164831,5412005,8659208],(decodeHints [166,625,1190,1702,2214,2726,3238,3750,4262,4774,14758,27302,28070,29350,33137,34461,35238,35494,37542,39334,39590])),([6,992,1082401,2164831,5412005,17318416],(decodeHints [166,625,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,25201,27302,28070,29350,34417,35238,35494,37542,39334,39590])),([6,992,1082401,2164831,6494406,8659208],(decodeHints [166,720,1190,1702,2214,2726,3238,3750,4262,4774,14758,15056,19039,27046,27302,29094,29350,33232,34461,35238,35494,37542,39334,39590])),([6,992,1082401,2164831,6494406,17318416],(decodeHints [166,631,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,25202,27046,27302,29094,29350,34423,35238,35494,37542,39334,39590])),([6,992,1082401,2164831,6494431,8659208],(decodeHints [166,717,1190,1702,2214,2726,3238,3750,4262,4774,14758,15053,19149,20135,21158,22182,27302,29094,29350,30118,33229,34461,35238,35494,37286,37542,38310,39334,39590])),([6,992,1082401,2164831,6494431,17318416],(decodeHints [166,627,1190,1702,2214,2726,3238,3750,4262,4774,14758,19059,20135,21158,22182,25200,27302,29094,29350,30118,34419,35238,35494,37286,37542,38310,39334,39590])),([6,992,1082401,2164831,8659208,12988812],(decodeHints [166,717,1190,1702,2214,2726,3238,3750,4262,4774,14758,15053,25037,25293,27046,27302,29350,35238,35494,37542,39590,40358])),([6,992,1082401,2164831,8659208,16236015],(decodeHints [166,624,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,24944,25200,27046,27302,29350,35494,36262,37542,39590,40358])),([6,992,1082401,2164831,8659208,17318416],(decodeHints [166,624,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,24944,25200,27046,27302,29350,35238,35494,37542,39334,39590])),([6,992,1082401,2164831,8659208,17318431],(decodeHints [180,624,1204,1716,2228,2740,3252,3764,4276,4788,14772,19048,21172,24944,25200,27060,27316,29108,29364,35508,37542,38324,39348,39604])),([6,992,1082401,2164831,8659208,18400817],(decodeHints [166,720,1190,1702,2214,2726,3238,3750,4262,4774,14758,15056,19039,25040,25296,27046,27302,29350,35494,36262,37542,39334,39590])),([6,992,1082401,2164831,8659208,19483218],(decodeHints [166,625,1190,1702,2214,2726,3238,3750,4262,4774,14758,24945,25201,27046,27302,29350,35238,35494,37542,39334,39590])),([6,992,1082401,2164831,8659208,19483231],(decodeHints [166,624,1190,1702,2214,2726,3238,3750,4262,4774,14758,21158,24944,25200,27046,27302,29094,29350,35494,37542,38310,39334,39590])),([6,992,1082401,2164831,8659208,25977624],(decodeHints [166,624,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,24944,26269,27046,27302,29350,35238,35494,37542,39590,40358])),([6,992,1082401,2164831,8659208,29224827],(decodeHints [166,717,1190,1702,2214,2726,3238,3750,4262,4774,14758,15053,25037,26269,27046,27302,29350,35494,36262,37542,38310,39590,40358])),([6,992,1082401,2164831,8659231,17318416],(decodeHints [180,624,1204,1716,2228,2740,3252,3764,4276,4788,14772,19048,21172,24944,25200,27316,29350,30132,35252,35508,37300,37556,39348,39604])),([6,992,1082401,2164831,8659944,17318416],(decodeHints [112,624,1136,1602,2160,2672,3184,3696,4208,4720,14658,19048,19824,25200,25968,27250,29296,33136,35138,35536,37488,39341])),([6,992,1082401,2164831,9741609,17318416],(decodeHints [166,631,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,24951,25202,27302,28070,29350,35238,35494,37542,39334,39590])),([6,992,1082401,2164831,10824010,17318416],(decodeHints [166,625,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,25201,27046,27302,29350,35238,35494,37542,39334,39590])),([6,992,1082401,2164831,10824031,17318416],(decodeHints [166,624,1190,1702,2214,2726,3238,3750,4262,4774,14758,19056,21158,25200,27302,29350,30118,35238,35494,37286,37542,39334,39590])),([6,992,1082401,2164831,17318416,21648020],(decodeHints [166,627,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,27046,27302,29350,33450,35238,35494,37542,39590,40358])),([6,992,1082401,2164831,17318416,24895223],(decodeHints [166,624,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,27046,27302,29350,33446,34214,35494,36262,37542,39590,40358])),([6,992,1082401,2164831,17318416,25977624],(decodeHints [166,624,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,26224,27046,27302,29350,33453,35238,35494,37542,39590,40358])),([6,992,1082401,2164831,17318416,29224827],(decodeHints [166,627,1190,1702,2214,2726,3238,3750,4262,4774,14758,19039,26227,27046,27302,29350,33446,35494,36262,37542,38310,39590,40358])),([6,992,1082401,2165759,8659208,17318416],(decodeHints [95,616,1119,1631,2143,2655,3167,3679,4191,4703,19039,19807,21864,25192,26975,27231,29279,33128,35167,35423,39263,39519])),([6,992,1082401,6494406,6494431,8659208],(decodeHints [166,720,1190,1702,2214,2726,3238,3750,4262,4774,14758,15056,19152,20173,20902,21158,22182,25183,29094,29350,30118,33232,34461,35238,35494,37286,37542,38310,39590])),([6,992,1082401,6494406,6494431,17318416],(decodeHints [166,631,1190,1702,2214,2726,3238,3750,4262,4774,14758,19063,20083,20902,21158,22182,25183,29094,29350,30118,34423,35238,35494,37286,37542,38310,39590])),([6,992,1082401,6494406,8659208,33554400],(decodeHints [180,720,1204,1716,2228,2740,3252,3764,4276,4674,14772,15056,20916,21172,25040,26275,27060,27316,29108,29364,33460,34228,37542,38324,40372])),([6,992,1082401,6494406,17318416,33554400],(decodeHints [180,631,1204,1716,2228,2740,3252,3764,4276,4674,14772,19050,20916,21172,26231,27060,27316,29108,29364,33460,34228,37542,38324,40372])),([6,992,1082401,6494431,8659208,17318416],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,4262,4774,14758,14910,19039,21926,24890,25203,26278,27046,27302,28326,29350,30374,33456,34509,35238,35494,36518,37542,38566,39334,39590,40358,40614])),([6,992,1082401,6494431,17318416],(decodeHints [371,883,1446,1958,2470,2982,3494,4006,15123,16294,19315,20339,21414,22438,25459,26483,27558,28582,29606,30630])),([6,992,1082401,8659200,17318416,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4698,14772,18792,19048,20916,21172,27060,27316,29108,29364,33460,34228,37556,38324,40372])),([6,992,1082401,8659208,8659231,17318431],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4788,14772,18792,19048,20148,20916,21172,22196,24936,25192,27316,29108,29364,30132,35508,37300,38324,40372])),([6,992,1082401,8659208,16236015,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4674,14772,18792,19048,20916,21172,27316,28084,29364,30132,33460,34228,38324,40372])),([6,992,1082401,8659208,17318400,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4674,14772,18792,19048,20916,21172,27060,27316,29108,29364,33460,34228,38324,39604,40372])),([6,992,1082401,8659208,17318416,29224800],(decodeHints [167,616,1191,1703,2215,2727,3239,3751,4263,4775,14759,18792,19048,20903,21159,27047,27303,29095,29351,33460,38311,40359])),([6,992,1082401,8659208,17318416,33553408],(decodeHints [95,616,1119,1631,2143,2655,3167,3679,4191,4703,19048,20831,21087,24936,26975,27231,29023,29279,33128,33460,35167,38239])),([6,992,1082401,8659208,17318416,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4674,14772,18792,19048,20916,21172,27060,27316,29108,29364,33460,34228,38324,40372])),([6,992,1082401,8659208,17318416,33554402],(decodeHints [166,617,1190,1702,2214,2726,3238,3750,4262,4674,14758,18793,19049,20902,21158,27046,27302,29094,29350,33446,34214,38310,40358])),([6,992,1082401,8659208,17318431,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4788,14772,18792,19048,20916,21172,27316,29108,29364,33460,34228,35508,37556,38324,40372,40628])),([6,992,1082401,8659208,18400817,33554400],(decodeHints [180,720,1204,1716,2228,2740,3252,3764,4276,4674,14772,15056,18896,19152,20916,21172,27316,28084,29108,29364,33460,34228,38324,40372])),([6,992,1082401,8659208,25977624,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4674,14772,18792,20131,20916,21172,27060,27316,29364,30132,33460,34228,38324,40372]))]
noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([6,992,1082401,8659231,17318416,17318431],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4788,14772,18792,19048,21172,25192,26216,27060,27316,28340,29364,30388,33448,35508,38580,39348,39604,40372])),([6,992,1082401,8659231,17318416,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4788,14772,18792,19048,21172,27060,27316,29108,29364,33460,34228,35508,38324,38580,39604,40372])),([6,992,1082401,8659231,17318431],(decodeHints [360,872,1460,1972,2484,2996,3508,4020,15132,16308,19304,20404,21428,22452,25448,26472,27572,28596,29620,30644])),([6,992,1082401,8659944,17318416,33554400],(decodeHints [104,616,1128,1688,2152,2664,3176,3688,4200,4674,14744,15796,18792,19048,19816,21098,24936,25960,26965,27344,29032,33128,33384,34152,38248,40296])),([6,992,1082401,9741609,17318416,33554400],(decodeHints [180,631,1204,1716,2228,2740,3252,3764,4276,4674,14772,18807,19050,21172,21940,27060,27316,29108,29364,33460,34228,38324,40372])),([6,992,1082401,17318416,24895223,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4674,14772,20916,21172,25268,26036,27316,28084,29364,30132,33460,34228,38324,40372])),([6,992,1082401,17318416,25977624,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4674,14772,20072,20916,21172,25192,27060,27316,29364,30132,33460,34228,38324,40372])),([6,992,1083361,2164802,4329631,8659208],(decodeHints [206,718,1230,1752,2254,2766,3278,3790,4302,4814,14808,15054,15822,18894,19843,20742,25038,25987,29133,29390,33230,34179,34508,35288,36556,37326,37582,39630])),([6,992,1113121,8659208,17318416,33554400],(decodeHints [196,616,1220,1732,2244,2756,3268,3780,4292,4684,14702,18792,19048,20932,27064,29124,29380,33476,34244,38340,40388])),([6,992,2164802,3247203,4329631,8659208],(decodeHints [171,518,1195,1707,2219,2731,3243,3755,4267,4779,18950,21163,21931,27302,33030,34464,34816,35243,35499,37291,37547,39595])),([6,992,2164802,3247203,4329631,17318416],(decodeHints [171,518,1195,1707,2219,2731,3243,3755,4267,4779,21163,21931,25183,27302,34310,34816,35243,35499,37291,37547,39595])),([6,992,2164802,4329631,8659208,9741609],(decodeHints [171,729,1195,1707,2219,2731,3243,3755,4267,4779,20903,21158,25049,26624,27051,27307,33241,33496,35243,35499,39595,40363])),([6,992,2164802,4329631,8659208,21648020],(decodeHints [171,518,1195,1707,2219,2731,3243,3755,4267,4779,21158,24838,27051,27307,33413,35243,35499,39339,39595])),([6,992,2164802,4329631,8659208,32472030],(decodeHints [171,729,1195,1707,2219,2731,3243,3755,4267,4779,20903,21158,25049,26272,27051,27307,29355,33413,34219,35499,36267,39595,40363])),([6,992,2164802,4329631,12988812,17318416],(decodeHints [171,518,1195,1707,2219,2731,3243,3755,4267,4779,19039,21158,27051,27307,33286,35243,35499,39339,39595])),([6,992,2164802,4329631,17318416,18400817],(decodeHints [171,553,1195,1707,2219,2731,3243,3755,4267,4779,14889,19039,20903,21158,25129,26624,27051,27307,35243,35499,39595,40363])),([6,992,2164802,4329631,17318416,32472030],(decodeHints [171,553,1195,1707,2219,2731,3243,3755,4267,4779,14889,19039,20903,21158,26153,27051,27307,29355,34219,35499,36267,39595,40363])),([6,992,2164831,6494406,8659208,17318416],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,4262,4774,14943,20902,24890,29094,29350,33346,37286,37542,39334,39590])),([6,992,2164831,8659208,9741609,17318416],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,4262,4774,14943,18746,24889,29350,30118,35494,37286,37542,39334,39590])),([6,992,2164831,8659208,17318416,18400817],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,4262,4774,14943,18746,19010,21158,25154,29094,29350,37286,37542,39590,40358])),([6,992,2164831,8659208,17318416,32472030],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,4262,4774,14943,18746,19010,21158,27302,29094,29350,34214,37542,38310,39590,40358])),([6,992,6494406,6494431,8659208,17318416],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,4262,4774,14910,19039,21158,21926,24890,27046,27302,33346,35238,35494,39334,39590])),([6,992,6494406,8659208,17318416,33554400],(decodeHints [180,518,1204,1716,2228,2740,3252,3764,4276,4674,18694,20916,21172,25094,27060,27316,29108,29364,33460,34228,35494])),([6,992,8659208,9741609,17318416,33554400],(decodeHints [180,558,1204,1716,2228,2740,3252,3764,4276,4674,14772,18734,21172,21940,27060,27316,29108,29364,33460,34228,40372])),([6,992,8659208,17318416,18400817,33554400],(decodeHints [180,597,1204,1716,2228,2740,3252,3764,4276,4674,14772,14933,19029,20916,21172,27060,27316,29364,30132,33460,34228,36276])),([6,992,8659208,17318416,32472030,33554400],(decodeHints [180,664,1204,1716,2228,2740,3252,3764,4276,4674,14772,15000,20916,21172,26036,27316,28084,29364,30132,33460,34228,36276,38324])),([6,1023,31744,1082401,8659208,17318431],(decodeHints [35,616,1059,1571,2083,2595,3107,3619,4131,4643,14801,14875,15899,18792,20072,20771,21027,21787,24936,25192,26915,27931,28963,29219,35101,36128,39203])),([6,1023,31775,1082401,8659208,17318416],(decodeHints [66,520,1090,1602,2114,2626,3138,3650,4162,4674,15880,20072,25096,28994,29250,35138,37186,37442,39234,39490])),([6,1023,32736,1082401,8659208,17318416],(decodeHints [77,607,1101,1613,2125,2637,3149,3661,4173,4685,15967,20072,25183,29005,29261,35149,37197,37453,39245,39501])),([6,1023,1082401,2164802,4329604,17318431],(decodeHints [73,631,1097,1609,2121,2633,3145,3657,4169,4681,14711,19048,20809,21065,25201,26953,27209,29001,29257,34312,37147,39212])),([6,1023,1082401,2164802,8659208,17318431],(decodeHints [44,625,1068,1580,2092,2604,3116,3628,4140,4652,14705,15985,19048,20013,20780,21036,22043,24945,25201,26924,27180,28972,29228,29979,37147,38188,39212])),([6,1023,1082401,8659208,17318416,17318431],(decodeHints [91,616,1115,1627,2139,2651,3163,3675,4187,4699,14696,15976,18792,19048,20827,21083,25192,26139,26971,27227,28187,29019,29275,30235,34312,37211,39195,39515,40283])),([6,1023,1082401,8659208,17318416,17318896],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,15976,19048,20802,21058,26178,26946,27202,28994,29250,34399,37186,39490,40258])),([6,1023,1082401,8659208,17318416,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4703,15976,19048,20802,21058,26946,27202,28994,29250,34114,34312,38210,39490])),([6,1023,1082401,8659208,17318416,33554400],(decodeHints [180,616,1204,1716,2228,2740,3252,3764,4276,4616,14696,15976,18792,19048,20916,21172,27060,27316,29108,29364,34228,34399,38324,39515,40372])),([6,1023,1082401,8659208,17318431],(decodeHints [360,872,1307,1819,2331,2843,3355,3867,15208,16155,19304,20251,21275,22299,25448,26472,27419,28443,29467,30491])),([6,1023,2164802,4329604,8659208,17318896],(decodeHints [66,517,1090,1602,2114,2626,3138,3650,4162,4674,14597,15877,18693,20004,20802,21058,26946,27202,28994,29250])),([6,31744,31775,1082401,8659944,17318416],(decodeHints [199,564,1223,1735,2247,2759,3271,3783,4295,4807,15047,15815,18996,29383,37319,37575])),([6,31744,1015808,8659208,17318431,32539681],(decodeHints [209,733,1233,1745,2257,2769,3281,3793,4305,4817,14801,15069,18909,20945,29137,32770,33245,33501,35281,35537,37585])),([6,31744,1082401,8659208,17318431,33521664],(decodeHints [209,616,1233,1745,2257,2769,3281,3793,4305,4817,14339,14801,14952,18792,20945,21201,29137,33128,33384,35281,35537,37585])),([6,31744,1082401,8659944,17318416,33554400],(decodeHints [104,616,1128,1731,2152,2664,3176,3688,4200,4660,14787,14952,15720,18792,19816,21098,24936,25960,27075,27344,33128,33384,34152,38248,40296])),([6,31744,1083361,2164802,4329631,8659208],(decodeHints [146,658,1170,1752,2194,2706,3218,3730,4242,4754,14731,15747,18834,19843,24978,25987,29072,29329,33170,33426,34179,35288,36495,37266,37522,39570])),([6,31775,32736,1082401,8659208,17318416],(decodeHints [75,703,1099,1611,2123,2635,3147,3659,4171,4683,29003,29259,37195,37451,39243,39499])),([6,1082401,1083361,2164802,4329631,8659208],(decodeHints [171,683,1195,1753,2219,2731,3243,3755,4267,4779,14808,15019,15787,18859,19115,19843,25001,25989,29095,29350,33195,33451,34179,35289,36512,37291,37547,39595])),([6,1082401,1083361,2164802,4329631,17318416],(decodeHints [171,683,1195,1576,2219,2731,3243,3755,4267,4779,15019,15787,18859,19115,21032,25001,29095,29350,33195,33451,36392,37291,37547,39595])),([6,1082401,1083361,2164831,8659208,17318416],(decodeHints [166,678,1190,1597,2214,2726,3238,3750,4262,4774,15014,15782,18853,24998,25254,26937,27197,29350,33190,33446,37542,39334,39590])),([6,1082401,1083361,8659208,17318416,33554400],(decodeHints [180,692,1204,1688,2228,2740,3252,3764,4276,4669,15028,15796,18868,19124,20916,21144,25012,25268,29108,29364,34213,36200,38324,40372])),([6,1082401,2164802,2164831,8659944,17318416],(decodeHints [113,567,1137,1649,2161,2673,3185,3697,4209,4721,14647,14903,21105,21873,25202,28016,33079,33488,35185,35441,37489])),([6,1082401,2164802,4329631,8659208,8659944],(decodeHints [206,729,1230,1742,2254,2766,3278,3790,4302,4814,14598,14952,20941,21198,25049,25305,26624,27086,27342,33240,33497,39630,40398])),([6,1082401,2164802,4329631,8659208,33553439],(decodeHints [206,729,1230,1742,2254,2766,3278,3790,4302,4779,14598,14952,20941,21198,25049,25207,27086,27342,29390,33411,34254,39372,39630])),([6,1082401,2164802,4329631,17318416,33553439],(decodeHints [117,553,1141,1653,2165,2677,3189,3701,4213,4779,14598,14952,20851,21109,24873,25296,26997,27253,29301,33404,36201,38257,39285])),([6,1082401,2164802,8659944,17318416,33554400],(decodeHints [113,692,1137,1649,2161,2673,3185,3697,4209,4663,14598,14952,15976,19058,20841,21872,25012,25296,26993,27249,28008,35177,35441,36208,38257,40305])),([6,1082401,2164831,8659208,8659944,17318416],(decodeHints [112,570,1136,1648,2160,2672,3184,3696,4208,4720,18746,19002,22128,25145,29296,30064,33082,33488,35440,37232,37488])),([6,1082401,2164831,8659208,17318416,33553439],(decodeHints [112,578,1136,1648,2160,2672,3184,3696,4208,4774,18754,19063,21104,24898,25296,27248,29040,29296,33341,36200,37488,38256])),([6,1082401,8659208,8659944,17318416,33554400],(decodeHints [104,692,1128,1640,2152,2664,3176,3688,4200,4666,14772,15028,15976,19124,20840,21096,21864,25012,25296,26984,27240,28008,35176,36200,38248,40296])),([6,1082401,8659208,17318416,33553439,33554400],(decodeHints [104,664,1128,1640,2152,2664,3176,3764,4200,4674,14638,14967,18773,19152,20840,21096,25240,27240,28008,36200,38248,40296,40552])),([6,1082401,8659944,17318416,33554400],(decodeHints [436,948,1384,1896,2408,2920,3432,3944,15256,16308,19380,20328,21352,22376,25524,26548,27496,28520,29544,30568])),([6,1083361,2164802,2164831,4329604,8659208],(decodeHints [129,573,1153,1665,2177,2689,3201,3713,4225,4737,14909,16000,20480,20864,21121,21889,27009,27265,28032,29057,29313,33081,34426,34816,35201,35457,36224,37505,39297,39553])),([6,1083361,2164802,4329604,8659208,33554400],(decodeHints [136,728,1160,1672,2184,2696,3208,3720,4232,4669,20872,21128,25048,26238,27016,27272,29064,29320,35457,36224,37509,38275,40326])),([6,1083361,2164802,4329631,8659208,17318416],(decodeHints [169,573,1193,1705,2217,2729,3241,3753,4265,4777,16037,20901,21158,24889,26236,27049,27305,29353,33416,34435,35241,35497,36483,37545,38531,39337,39593,40579])),([7,0,31,992,1082401,8659208,17318416],(decodeHints [66,578,1090,1716,2114,2626,3138,3650,4162,4674,5186,5698,14772,14914,15682,18754,19010,19778,20831,21000,24898,25154,25922,28989,33090,33346,34114,35508,37178,37442,39234,39490,43330,43586,44354,45748,49474,49730,51522,51778])),([7,1,31,992,1082401,8659208,17318416],(decodeHints [180,692,1204,1716,2228,2712,3252,3764,4276,4788,5300,5812,14772,15028,15796,18840,19124,19778,20888,21172,24898,25268,26036,27060,27316,29108,30387,33204,33460,34114,35508,37300,37528,39348,39604,43444,43700,44354,45748,49588,49844,51636,51892])),([7,2,31,992,1082401,8659208,17318416],(decodeHints [66,578,1090,1716,2114,2626,3138,3650,4162,4674,5186,5698,14772,14914,15682,18754,19010,19778,20835,21030,24898,25154,25922,28989,33090,33346,34114,35508,37178,37442,39234,39490,43330,43586,44354,45748,49474,49730,51522,51778])),([7,8,31,992,1082401,8659208,17318416],(decodeHints [90,602,1114,1716,2138,2650,3162,3674,4186,4698,5210,5722,14772,14938,15706,18778,19034,19778,20831,21000,24922,25178,25922,29016,33090,33370,34138,35252,35508,37210,37466,39258,39514,43354,43610,44354,45748,49498,49754,51546,51802]))]
noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([7,16,31,992,1082401,8659208,17318416],(decodeHints [66,578,1090,1716,2114,2626,3138,3650,4162,4674,5186,5698,14772,14914,15682,18754,19010,19778,20831,21000,24898,25154,25922,28989,33090,33346,34114,35508,37178,37442,39234,39490,43330,43586,44354,45492,45748,49474,49730,51522,51778])),([7,31,31,992,1082401,8659208,17318416],(decodeHints [180,692,2228,2664,3252,3764,4276,4788,5300,5812,12724,12980,13748,14004,18792,19124,19778,25012,26036,29108,33204,33460,34138,37224,37480,39348,39604,43444,43700,44354,49588,49844,51636,51892])),([7,31,32,992,1082401,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,15028,15938,18754,19124,20802,21058,21826,26291,26946,27202,27970,28994,29250,33460,35138,35394,36162,37178,37442,39234,39490,43700,45378,45634,46402,49474,49730,51522,51778])),([7,31,64,992,1082401,8659208,17318416],(decodeHints [66,693,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,15029,15938,18784,18954,20802,21058,21826,26946,27202,27970,28989,33461,35138,35394,36162,37178,37442,39234,39490,43701,45378,45634,46402,49474,49730,51522,51778])),([7,31,256,992,1082401,2164802,4329604],(decodeHints [66,675,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,15011,18783,18952,21058,21826,26946,27202,28989,29250,32768,33181,33443,34816,35138,35394,39234,39490,43424,43683,45378,45634,49474,49730,51522,51778])),([7,31,256,992,1082401,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,15028,15938,18783,18952,20802,21058,21826,26946,27202,27970,28989,33460,35138,35394,36162,37186,37442,39234,39490,43700,45378,45634,46402,49474,49730,51522,51778])),([7,31,512,992,1082401,2164802,4329604],(decodeHints [66,631,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,14967,18783,18952,21058,21826,26946,27202,28989,32768,33143,33395,35138,35394,37442,39234,39490,43383,43637,45378,45634,47682,49474,49730,51522,51778])),([7,31,512,992,1082401,8659208,17318416],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,14952,15938,18783,18952,20802,21058,21826,26946,27202,27970,28989,33384,35138,35394,36162,37178,37442,39234,39490,43624,45378,45634,46402,47426,47682,49474,49730,51522,51778])),([7,31,992,992,1082401,8659208,17318416],(decodeHints [66,616,1090,1602,3138,3650,4162,4674,5186,5698,14658,14952,15938,16706,16962,17730,17986,26946,27970,33384,35138,35394,36162,39234,39490,43624,45378,46402,49474,49730,51522,51778])),([7,31,992,1023,1082401,8659208,17318416],(decodeHints [104,616,1128,1640,2152,2664,3176,3736,4200,4712,5224,5736,14687,14856,15711,15880,18783,19048,19816,20148,20744,21096,21864,22082,24984,26008,27032,28084,29032,30132,30312,33128,33384,34143,35176,35432,36104,37224,37480,38234,39214,39543,43368,43624,44383,45416,46344,47464,48450,49493,49872,51560,51816])),([7,31,992,1024,1082401,8659208,17318416],(decodeHints [67,692,1091,1603,2115,2627,3139,3651,4163,4675,5187,5699,14687,14856,18868,19124,20034,20803,21059,22082,26941,28994,29251,30019,33460,35131,35395,37187,37443,38210,39235,39491,43700,47427,47683,48450,49475,49731,51523,51779])),([7,31,992,2048,1082401,8659208,17318416],(decodeHints [66,694,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18870,19126,20034,20802,21058,22082,26941,28994,29250,30018,33462,35130,35394,37186,37442,38210,39234,39490,43702,47426,47682,48450,49474,49730,51522,51778])),([7,31,992,8192,1082401,8659208,17318416],(decodeHints [76,692,1100,1612,2124,2636,3148,3660,4172,4684,5196,5708,14687,14856,18868,19124,20034,20812,21068,22082,26954,29004,29260,30018,33460,35130,35404,37186,37452,38220,39244,39500,43700,47436,47692,48450,49484,49740,51532,51788])),([7,31,992,16384,1082401,8659208,17318416],(decodeHints [66,706,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18882,19138,20034,20802,21058,22082,26941,28994,29250,30018,33474,35130,35394,37186,37442,38210,39234,39490,43714,47426,47682,48450,49474,49730,51522,51778])),([7,31,992,31744,1082401,6494406,8659208],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26954,27214,29004,30019,33212,33476,37198,38210,39246,39502,43716,45371,46670,47427,47694,48460,49486,49742,51534,51790])),([7,31,992,31744,1082401,6494406,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26954,29004,30019,33212,33476,35406,37198,38210,39246,39502,43716,46670,47438,47694,48450,49486,49742,51534,51790])),([7,31,992,31744,1082401,8659208,16236015],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26954,29004,29262,30019,33476,35131,35406,37187,38220,39246,39502,43598,47426,48462,49742,50510,51790,52558])),([7,31,992,31744,1082401,8659208,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26954,29004,29262,30019,33476,35131,35406,37187,38220,39246,39502,43716,47438,48450,49486,49742,51534,51790])),([7,31,992,31744,1082401,8659208,17318431],(decodeHints [196,708,1220,1640,2244,2756,3268,3780,4292,4804,5316,5828,14696,15044,18884,19140,20148,20947,21172,22196,25028,27076,29124,29380,30132,33220,33476,35176,35432,37316,38324,39364,39620,43716,44484,47544,48578,49698,51652,51908])),([7,31,992,31744,1082401,8659208,18400817],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26954,27214,29004,30019,33476,35131,35406,37187,38220,39246,39502,43554,47436,48451,49742,50510,51534,51790])),([7,31,992,31744,1082401,8659208,25977624],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26954,29004,29262,30019,33476,35131,36430,37187,37454,38220,39246,39502,43716,47427,48460,49486,49742,51790,52558])),([7,31,992,31744,1082401,8659231,17318416],(decodeHints [196,708,1220,1640,2244,2756,3268,3780,4292,4804,5316,5828,14696,15044,18884,19140,20148,20947,21172,22196,25028,27076,29124,29380,30132,33476,34244,35176,35432,37316,38324,39454,43460,43716,47544,48578,49604,49860,51652,51908])),([7,31,992,31744,1082401,8659944,17318416],(decodeHints [78,616,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14670,14952,15924,18887,19010,20034,20814,21070,21812,22082,26958,27956,29004,29262,30019,33384,35124,35406,36174,37187,38220,39502,43624,45390,46388,47438,48450,49486,49742,51534])),([7,31,992,31744,1082401,9741609,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26954,29004,30019,33310,35129,35406,37186,38222,39502,40270,43716,47438,48450,49486,49742,51534,51790])),([7,31,992,31744,1082401,17318416,24895223],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26954,29004,29262,30019,33476,37198,38210,39246,39502,43613,45646,46395,47436,48451,49742,50510,51790,52558])),([7,31,992,31744,1082401,17318416,25977624],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26954,29004,29262,30019,33476,36430,37198,37454,38210,39246,39502,43716,45646,47427,48460,49486,49742,51790,52558])),([7,31,992,31744,1113121,8659208,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19140,20044,20814,21070,22092,26954,29004,29262,30030,33476,35131,35406,37198,38220,39246,43716,47438,48460,49486,51534,51790])),([7,31,992,31744,2065441,8659208,17318416],(decodeHints [82,709,1106,1618,2130,2642,3154,3666,4178,4690,5202,5714,14687,14856,18885,19010,20034,20818,21074,22082,26960,29009,29266,30019,33477,35131,35410,37187,38225,39246,43717,47442,48450,49490,51538,51794])),([7,31,992,31744,6494406,8659208,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,25020,29006,29262,30018,35131,37187,38220,39246,39502,45646,47438,48450,49486,49742,51534,51790])),([7,31,992,31744,8659208,9741609,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,26939,28995,30028,35129,37186,37454,38222,39502,40270,43716,47438,48450,49486,49742,51534,51790])),([7,31,992,31744,8659208,17318416,18400817],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,25284,26939,27214,28995,30028,35406,37198,38210,39246,39502,47436,47694,48451,49486,49742,51790,52558])),([7,31,992,31744,8659208,17318416,32472030],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18884,19010,20034,20814,21070,22082,25284,26939,27214,28995,30028,33476,37198,38210,39246,39502,46410,47427,47694,48460,49742,50510,51790,52558])),([7,31,992,31775,1082401,8659208,17318416],(decodeHints [66,708,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,15044,19010,19778,20148,20802,21058,22082,26946,28994,30018,33476,35138,35394,37186,38210,39234,39490,43716,47426,48450,49474,49730,51522,51778])),([7,31,992,32736,1082401,8659208,17318416],(decodeHints [78,692,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14670,15028,18868,19010,20034,21070,21838,22082,26958,29004,30019,33460,35150,35406,37187,38220,39246,39502,43700,47438,48450,49486,49742,51534,51790])),([7,31,992,1047552,1082401,8659208,17318416],(decodeHints [83,709,1107,1619,2131,2643,3155,3667,4179,4691,5203,5715,14687,14856,18885,19010,20034,20819,21075,22082,26960,29009,29267,30020,33477,35132,35411,37188,38225,39251,39507,43717,47443,48450,49491,49747,51539,51795])),([7,31,992,1048575,1082401,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,19010,19778,20148,21058,21826,22082,26941,28994,30018,30274,33460,35130,35394,37186,38210,39234,39490,43700,47426,48450,49474,49730,51522,51778])),([7,31,992,1082401,1082401,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,4162,4674,5186,5698,14687,14856,19124,20148,20797,21058,22082,22850,23106,23874,24130,33460,35130,35394,37186,37442,38210,43700,47426,47682,48450,51522,51778])),([7,31,992,1082401,1082431,8659208,17318416],(decodeHints [180,692,1204,1688,2228,2740,3252,3764,4276,4788,5300,5812,14744,15028,19892,20148,20916,21144,25268,26036,26292,27060,27240,28226,29364,30132,30274,33204,33460,35252,35480,37300,37556,39234,39604,40282,43444,43700,47540,47796,49498,49844,50498,51636,51892])),([7,31,992,1082401,1083361,8659208,17318416],(decodeHints [66,664,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,15000,15933,19096,20797,21826,22082,25192,26292,26941,27202,27970,28226,29250,30018,30274,33432,35138,35394,36157,37186,37442,39234,39490,40258,43672,45378,46397,47426,47682,49474,50498,51522,51778])),([7,31,992,1082401,1113121,8659208,17318416],(decodeHints [76,708,1100,1612,2124,2636,3148,3660,4172,4684,5196,5708,14687,14856,19140,20164,20810,21068,22092,25154,26292,26954,27212,28226,29004,29260,30028,30274,33476,35130,35404,37196,37452,38220,39234,40268,43716,47436,47692,48460,49484,50498,51532,51788])),([7,31,992,1082401,2164802,4329604,8659208],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,21058,24576,24998,25268,28994,29250,33195,33460,37186,37442,39234,39490,43700,45370,46658,47426,47682,49474,49730,51522,51778])),([7,31,992,1082401,2164802,4329604,8659231],(decodeHints [180,692,1204,1743,2228,2740,3252,3764,4276,4788,5300,5812,14799,15028,18868,20916,21199,24576,25012,25268,29108,29364,33204,33460,37300,37556,39348,39604,43700,44468,45519,46658,47682,49588,49844,51636,51892])),([7,31,992,1082401,2164802,4329604,8682760],(decodeHints [67,708,1091,1603,2115,2627,3139,3651,4163,4675,5187,5699,14687,14856,20797,21059,24576,25020,25284,28995,29251,33214,33476,37187,37443,39235,39491,43586,45371,46658,47682,49731,51779])),([7,31,992,1082401,2164802,4329604,9741609],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24576,24998,25268,28672,28994,29250,33195,33460,37186,37442,39234,39490,43586,45369,46658,47682,48450,49474,49730,51522,51778])),([7,31,992,1082401,2164802,4329604,10824010],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,21058,24576,24998,25268,27202,28672,28994,29250,33195,33460,37186,37442,39234,39490,43700,46658,47426,47682,49730,50498,51522,51778])),([7,31,992,1082401,2164802,4329604,16236015],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24576,24998,25268,27202,28994,29250,33195,33460,35394,37186,37442,39234,39490,43586,46658,47682,48450,49730,50498,51778,52546])),([7,31,992,1082401,2164802,4329604,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24576,24998,25268,27202,28994,29250,33195,33460,35394,37186,37442,39234,39490,43700,46658,47426,47682,49474,49730,51522,51778])),([7,31,992,1082401,2164802,4329604,17318431],(decodeHints [180,692,1204,1655,2228,2740,3252,3764,4276,4788,5300,5812,14711,15028,18868,20916,24576,25012,25268,27242,29108,29364,33204,33460,35442,37300,37556,39348,39604,43700,44468,46658,47686,49588,49844,51636,51892])),([7,31,992,1082401,2164802,4329604,17333776],(decodeHints [78,676,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,20810,24576,24989,25252,27214,29006,29262,33184,33444,35406,37198,37454,39246,39502,43586,46658,47692,49742,51790])),([7,31,992,1082401,2164802,4329604,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,21058,24576,24998,25268,27202,28672,28994,29250,33195,33460,35394,37186,37442,39234,39490,43590,46658,47682,48450,49474,49730,51522,51778])),([7,31,992,1082401,2164802,4329604,19483218],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24576,24998,25268,28672,28994,29250,33195,33460,35394,37186,37442,39234,39490,43700,46658,47426,47682,49730,50498,51522,51778])),([7,31,992,1082401,2164802,4329604,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,21058,24576,24998,25268,28994,29250,33195,33460,37186,37442,39234,39490,43590,46394,46658,47682,48450,49730,50498,51778,52546])),([7,31,992,1082401,2164802,4329631,8659208],(decodeHints [180,692,1204,1742,2228,2740,3252,3764,4276,4788,5300,5812,14798,15028,15787,18868,19883,20916,21198,25012,25268,26027,29108,29364,33195,33460,34228,37556,39348,39604,43444,43700,44459,45518,46755,47540,47796,49588,49844,51636,51892])),([7,31,992,1082401,2164802,4329631,17318416],(decodeHints [180,692,1204,1653,2228,2740,3252,3764,4276,4788,5300,5812,14709,15028,15787,18868,19883,20916,25012,25268,26027,27241,29108,29364,33195,33460,34228,35441,37556,39348,39604,43444,43700,44459,46709,47540,47796,49588,49844,51636,51892])),([7,31,992,1082401,2164802,4330468,17318416],(decodeHints [66,626,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,14962,20802,24946,25200,26946,27202,28994,29250,33138,33393,35394,36162,37442,39234,39490,43634,45378,46658,47426,47682,49474,49730,51522,52802])),([7,31,992,1082401,2164802,5412005,8659208],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,28994,29250,33460,37442,38210,39234,39490,43700,45370,46658,47426,47682,49474,49730,51522,51778])),([7,31,992,1082401,2164802,5412005,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,27202,28994,29250,33460,35394,37442,38210,39234,39490,43700,46658,47426,47682,49474,49730,51522,51778])),([7,31,992,1082401,2164802,6494406,8659208],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,21058,24998,25268,26178,27202,28226,28994,29250,30274,33190,33460,37186,37442,39234,39490,40258,43700,45370,46658,47426,47682,49474,49730,50498,51522,51778])),([7,31,992,1082401,2164802,6494406,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,26178,27202,28226,28994,29250,30274,33190,33460,35394,37186,37442,39234,39490,40258,43700,46658,47426,47682,49474,49730,50498,51522,51778])),([7,31,992,1082401,2164802,8659208,12988812],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,21058,24998,25268,28994,29250,33460,35130,35394,37186,37442,39234,39490,43700,47426,47682,49474,49730,51778,52546])),([7,31,992,1082401,2164802,8659208,16236015],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,26178,27202,28226,28994,29250,30274,33460,35130,35394,37186,37442,39234,39490,40258,43586,47682,48450,49474,49730,50498,51778,52546])),([7,31,992,1082401,2164802,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,26178,27202,28226,28994,29250,30274,33460,35130,35394,37186,37442,39234,39490,40258,43700,47426,47682,49474,49730,50498,51522,51778])),([7,31,992,1082401,2164802,8659208,17318431],(decodeHints [180,692,1204,1649,2228,2740,3252,3764,4276,4788,5300,5812,14705,15028,18868,20916,25012,25268,26292,27241,28341,29108,29364,30388,33204,33460,35185,35441,37300,37556,39348,39604,40372,43700,44468,47659,49588,49844,50612,51636,51892])),([7,31,992,1082401,2164802,8659208,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,21058,24998,25268,26178,27202,28226,28994,29250,30274,33460,35130,35394,37186,37442,39234,39490,40258,43563,47682,48450,49474,49730,50498,51522,51778]))]
noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,1082401,2164802,8659208,19483218],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,28994,29250,33460,35130,35394,37186,37442,39234,39490,43700,47426,47682,49730,50498,51522,51778])),([7,31,992,1082401,2164802,8659208,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,26178,27202,28226,28994,29250,30274,33460,35130,36418,37186,37442,39234,39490,40258,43700,47426,47682,49474,49730,50498,51778,52546])),([7,31,992,1082401,2164802,8659208,29224827],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,21058,24998,25268,28994,29250,33460,35130,36418,37186,37442,39234,39490,43563,44354,47682,48450,49730,50498,51778,52546])),([7,31,992,1082401,2164802,8659231,17318416],(decodeHints [180,692,1204,1649,2228,2740,3252,3764,4276,4788,5300,5812,14705,15028,18868,20916,25012,25268,26292,27241,28341,29108,29364,30388,33460,34228,35185,35441,37417,39348,39604,40372,43444,43700,47540,47796,49588,49844,50612,51636,51892])),([7,31,992,1082401,2164802,8659944,17318416],(decodeHints [66,625,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,14961,15927,20802,21815,24945,25200,26178,26946,27202,27959,28226,28994,29250,30274,33393,35127,35394,36162,37442,39234,39490,40258,43633,45378,46391,47426,47682,49474,49730,50498,51522])),([7,31,992,1082401,2164802,9741609,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,26178,27202,28226,28994,29250,30274,33321,35129,35394,37442,38210,39234,39490,40258,43700,47426,47682,49474,49730,50498,51522,51778])),([7,31,992,1082401,2164802,10824010,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,27202,28994,29250,33460,35394,37186,37442,39490,40258,43700,47426,47682,49474,49730,51522,51778])),([7,31,992,1082401,2164802,17318416,21648020],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,27202,28994,29250,33460,37186,37442,39234,39490,43700,45634,47426,47682,49474,49730,51778,52546])),([7,31,992,1082401,2164802,17318416,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,26178,27202,28226,28994,29250,30274,33460,37186,37442,39234,39490,40258,43610,45634,46394,47682,48450,49474,49730,50498,51778,52546])),([7,31,992,1082401,2164802,17318416,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,26178,27202,28226,28994,29250,30274,33460,36418,37186,37442,39234,39490,40258,43700,45634,47426,47682,49474,49730,50498,51778,52546])),([7,31,992,1082401,2164802,17318416,29224827],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,24998,25268,27202,28994,29250,33460,36418,37186,37442,39234,39490,43561,44354,45634,47682,48450,49730,50498,51778,52546])),([7,31,992,1082401,2164831,8659208,17318416],(decodeHints [180,692,1204,1648,2228,2740,3252,3764,4276,4788,5300,5812,14704,15028,15782,18868,19878,20916,24998,25268,26036,26292,27240,28226,29364,30388,33204,33460,34214,35184,35440,37300,37556,39348,39604,40282,43444,43700,44454,47540,47796,49588,49844,50498,51636,51892])),([7,31,992,1082401,2165730,8659208,17318416],(decodeHints [66,617,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,14953,20802,24937,25192,26178,27202,27970,28226,29250,30274,33385,35138,35394,37186,37442,39234,39490,40258,43625,45378,47426,47682,49474,50498,51522,51778])),([7,31,992,1082401,2194498,8659208,17318416],(decodeHints [78,706,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,20810,25020,25154,26178,27214,28226,29006,29260,30275,33474,35131,35406,37198,37454,39235,40268,43714,47438,47694,49486,50498,51534,51790])),([7,31,992,1082401,3247203,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,25268,26292,27202,28226,29250,30018,30274,33460,35130,35394,37186,37442,39234,39490,40258,43700,47426,47682,49474,49730,50498,51522,51778])),([7,31,992,1082401,6494406,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,19124,20148,20797,21058,22082,24998,25268,26178,27202,28226,28994,29250,30018,30274,33460,34394,35130,35394,36418,37186,37442,38210,38466,39234,39490,40258,40514,43700,44610,45634,46658,47426,47682,48450,48706,49474,49730,50498,50754,51522,51778,52546,52802])),([7,31,992,1082401,6494406,17318416],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15223,16194,19380,20404,21314,22338,25524,26434,27458,28482,29506,30530,33716,34626,35650,36674,37698,38722,39746,40770])),([7,31,992,1082401,8659208,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,5186,5698,14687,14856,20797,25268,26202,26938,27202,28226,28994,29250,30274,31042,31298,32066,32322,43700,47426,47682,49474,49730,50498])),([7,31,992,1082401,8659208,8659231,17318416],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,5300,5812,14696,15028,18868,20916,25268,26036,26292,26984,27240,28340,29108,29364,30388,33460,34228,34484,35176,35432,36418,37442,38580,39348,39604,40372,40514,43444,43700,47540,47796,49588,49844,50612,51636,51892,52546])),([7,31,992,1082401,8659208,8659944,17318416],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,14952,15930,20802,21818,25192,26202,26938,27202,27970,28226,28994,29250,30274,33384,34394,35130,35394,36162,36418,37442,38466,39234,39490,40258,40514,43624,45378,46394,47426,47682,49474,49730,50498,51522,52546])),([7,31,992,1082401,8659208,8682760,17318416],(decodeHints [67,708,1091,1603,2115,2627,3139,3651,4163,4675,5187,5699,14687,14856,20797,25284,26939,27203,28995,29251,33346,34394,35131,35395,36418,37187,37442,38467,39491,40259,40514,43716,47427,47683,49475,49731,51523,52546])),([7,31,992,1082401,8659208,9741609,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,19124,20148,20797,21058,22082,25268,26202,26938,27202,28226,28994,29250,30018,30274,33346,34484,35129,35394,36418,37186,37442,38210,38466,39234,39490,40258,40514,43700,47426,47682,48450,49474,49730,50498,51522,51778,52546])),([7,31,992,1082401,8659208,10824010,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,25268,26938,27202,28994,29250,33460,34394,35394,36418,37186,37442,38466,39490,40258,40514,43700,47426,47682,49474,49730,51522,51778,52546])),([7,31,992,1082401,8659208,16236015],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15208,16194,19380,20404,21314,22338,25524,26458,27458,28482,29506,30530,33602,34740,35650,36674,37698,38722,39746,40770])),([7,31,992,1082401,8659208,16236015,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,25268,26938,27202,28994,29250,33346,34484,35394,36418,37442,38210,38466,39490,40258,40514,43700,44610,45634,46658,47426,47682,48706,49474,49730,50754,51522,51778,52546,52802])),([7,31,992,1082401,8659208,17318416],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15208,16194,19380,20404,21314,22338,25524,26458,27458,28482,29506,30530,33716,34626,35650,36674,37698,38722,39746,40770])),([7,31,992,1082401,8659208,17318416,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,14687,14856,20797,25268,26938,27202,28994,29250,33460,34370,35394,36418,37186,37442,38466,39234,39490,40514,41282,41538,42306,42562])),([7,31,992,1082401,8659208,17318416,17318431],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,5300,5812,14696,15028,18868,20916,25012,25268,26984,27240,29108,29364,33460,34228,34484,35432,36456,37300,37556,38580,39348,39604,40628,43700,44468,44724,45672,46658,47706,48820,49588,49844,50778,51636,51892,52660,52802])),([7,31,992,1082401,8659208,17318416,17318896],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,14952,20802,25192,26946,27202,28994,29250,33384,36162,36418,37186,37442,39234,39490,43624,44610,45634,46402,46658,47682,48706,49474,49730,50754,51778,52546,52802])),([7,31,992,1082401,8659208,17318416,17333776],(decodeHints [78,696,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,20810,25272,26939,27214,29006,29262,33464,35406,37198,37454,39246,39502,43586,44610,45646,46658,47438,47692,48707,49731,50764,51790,52558,52802])),([7,31,992,1082401,8659208,17318416,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,19124,20148,20797,21058,22082,25268,26938,27202,28994,29250,30018,33460,34370,35394,36418,37186,37442,38210,38466,39234,39490,40514,43610,44724,45634,46658,47426,47682,48450,48706,49474,49730,50754,51522,51778,52546,52802])),([7,31,992,1082401,8659208,17318416,19483218],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,25268,26938,27202,28994,29250,33460,37186,37442,39234,39490,43700,44610,45634,46658,47426,47682,48706,49474,49730,50754,51778,52546,52802])),([7,31,992,1082401,8659208,17318416,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,25268,26202,26938,27202,28226,28994,29250,30274,33460,37186,37442,39234,39490,40258,43610,44724,45634,46394,46658,47682,48450,48706,49474,49730,50498,50754,51778,52546,52802])),([7,31,992,1082401,8659208,17318416,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,25268,26202,26938,27202,28226,28994,29250,30274,33460,34370,35394,36418,37186,37442,38466,39234,39490,40258,40514,43700,44724,45634,46658,47426,47682,48706,49474,49730,50498,50754,51522,51778,52546,52802])),([7,31,992,1082401,8659208,17318416,29224827],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,20797,25268,26938,27202,28994,29250,33460,37186,37442,39234,39490,43586,44354,44724,45634,46658,47682,48450,48706,49730,50498,50754,51778,52546,52802])),([7,31,992,1082401,8659208,17318416,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,19124,20148,20797,21058,22082,25268,26938,27202,28994,29250,30018,33460,37186,37442,38210,39234,39490,43700,44724,45634,46397,46658,47426,47682,48450,48706,49730,50498,50754,51778,52546,52802])),([7,31,992,1082401,8659208,17318416,33553439],(decodeHints [66,616,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,14952,15938,20802,21826,25192,26946,27202,27970,28994,29250,33384,35138,36162,37186,37442,39234,39490,43586,44354,44724,45378,45634,46402,46658,47682,48706,49730,50498,50754,51778,52802])),([7,31,992,1082401,8659208,17318416,33554400],(decodeHints [180,692,1204,1640,2228,2740,3252,3764,4276,4788,5300,5812,14696,15028,15796,18868,19892,20916,25012,25268,26036,26984,27240,29108,29364,33204,33460,34228,37300,37556,39348,39604,43444,43586,44468,44610,45748,46516,46658,47796,48820,49844,50612,50778,51892,52660,52802])),([7,31,992,1082401,8659208,17318431],(decodeHints [436,948,1384,1896,2484,2996,3508,4020,4532,5044,15208,16308,19380,20404,21400,22452,25524,26548,27496,28596,29620,30644,33716,34740,35688,36712,37812,38836,39860,40884])),([7,31,992,1082401,8659208,18400817],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15312,16194,19380,20404,21314,22338,25524,26458,27458,28482,29506,30530,33626,34740,35650,36674,37698,38722,39746,40770])),([7,31,992,1082401,8659208,25977624],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15208,16194,19380,20404,21314,22338,25524,26458,27458,28482,29506,30530,33716,34740,35650,36674,37698,38722,39746,40770])),([7,31,992,1082401,8659231,17318416],(decodeHints [436,948,1384,1896,2484,2996,3508,4020,4532,5044,15208,16308,19380,20404,21400,22452,25524,26548,27496,28596,29620,30644,33716,34740,35688,36712,37812,38836,39860,40884])),([7,31,992,1082401,8659944,17318416],(decodeHints [360,872,1346,1858,2370,2882,3394,3906,4418,4930,15208,16194,19352,20376,21314,22338,25448,26458,27458,28482,29506,30530,33640,34626,35650,36674,37698,38722,39746,40770])),([7,31,992,1082401,9741609,17318416],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15223,16194,19380,20404,21314,22338,25410,26548,27458,28482,29506,30530,33716,34626,35650,36674,37698,38722,39746,40770])),([7,31,992,1082401,17318416,24895223],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15208,16194,19380,20404,21314,22338,25524,26434,27458,28482,29506,30530,33626,34740,35650,36674,37698,38722,39746,40770])),([7,31,992,1082401,17318416,25977624],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15208,16194,19380,20404,21314,22338,25524,26434,27458,28482,29506,30530,33716,34740,35650,36674,37698,38722,39746,40770])),([7,31,992,1083361,2164802,4329604,8659208],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,15056,15933,20797,21058,21826,24576,25040,25293,26946,27965,28994,33232,33486,35138,36157,37186,39234,39490,43727,45378,46397,46658,47426,48706,49474,49730,51522,51778])),([7,31,992,1113121,2164802,8659208,17318416],(decodeHints [76,708,1100,1612,2124,2636,3148,3660,4172,4684,5196,5708,14687,14856,20810,25020,25284,26188,27212,28236,29004,29260,30284,33476,35130,35404,37186,39244,39500,40268,43716,47436,49484,49740,50508,51532,51788])),([7,31,992,1113121,8659208,17318416],(decodeHints [452,964,1356,1868,2380,2563,2892,3404,3916,4428,4940,15208,16204,19396,20420,21324,22348,25540,26460,27468,28492,29516,30540,33732,34636,35660,36684,37708,38732,39756,40780])),([7,31,992,2164802,3247203,4329604,8659208],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,27202,29250,30018,33195,33460,37186,37442,39234,39490,43700,45370,46658,47104,47426,47682,49474,49730,51522,51778])),([7,31,992,2164802,3247203,4329604,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,29250,30018,33195,33460,35394,37186,37442,39234,39490,43700,46658,47104,47426,47682,49474,49730,51522,51778])),([7,31,992,2164802,3247203,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,29250,30018,33460,35130,35394,37186,37442,39234,39490,43700,47426,47682,49474,49730,51522,51778])),([7,31,992,2164802,4329604,8659208,9741609],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18432,18854,19124,25003,25268,28994,29250,35130,36864,37186,37442,39234,39490,45369,45634,47426,47682,49474,49730,51778,52546])),([7,31,992,2164802,4329604,8659208,16236015],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,25003,28994,29250,35130,37186,37442,39234,39490,45634,47682,48450,49730,50498,51778,52546])),([7,31,992,2164802,4329604,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,25003,28994,29250,35130,37186,37442,39234,39490,45634,47426,47682,49474,49730,51522,51778])),([7,31,992,2164802,4329604,8659208,17318896],(decodeHints [66,518,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,14854,18754,20802,24838,26946,28994,29250,35138,37186,37442,39234,39490,45634,46402,47682,49730,51778])),([7,31,992,2164802,4329604,8659208,19483218],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18432,18854,19124,25003,28994,29250,35130,36864,37186,37442,39234,39490,45634,47682,48450,49474,49730,51522,51778])),([7,31,992,2164802,4329604,8659208,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,25003,28994,29250,33460,35130,36418,36864,37186,37442,39234,39490,45634,47426,47682,49474,49730,51778,52546])),([7,31,992,2164802,4329604,8659208,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18432,18854,19124,25003,25268,28994,29250,33460,35130,36418,37186,37442,39234,39490,45634,46397,47682,48450,49730,50498,51778,52546])),([7,31,992,2164802,4329604,10824010,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18432,18854,19124,21058,25003,28994,29250,37442,38210,39234,39490,45634,47104,47426,47682,49474,49730,51522,51778])),([7,31,992,2164802,4329604,17318416,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18432,18854,19124,21058,25003,25268,27202,28994,29250,35394,36864,37186,37442,39234,39490,47426,47682,49474,49730,51778,52546])),([7,31,992,2164802,4329604,17318416,24895223],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,25003,28994,29250,35394,37186,37442,39234,39490,46394,47682,48450,49730,50498,51778,52546])),([7,31,992,2164802,4329604,17318416,25977624],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,25003,28994,29250,33460,36418,36864,37186,37442,39234,39490,47426,47682,49474,49730,51778,52546])),([7,31,992,2164802,4329604,17318416,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18432,18854,19124,21058,25003,25268,27202,28994,29250,33460,36418,37186,37442,39234,39490,46397,47682,48450,49730,50498,51778,52546]))]
noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,2164802,4357252,8659208,17318416],(decodeHints [78,705,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14687,14856,18876,25022,29006,29262,35131,37198,37454,39235,45646,47438,47694,49486,51534,51790])),([7,31,992,2164802,6494406,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,19124,20034,21058,22082,24998,28994,29250,30018,35130,37186,37442,38210,39234,39490,45634,47426,47682,48450,49474,49730,51522,51778])),([7,31,992,2164802,8659208,9741609,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,19124,20034,21058,22082,26938,28994,29250,30018,35129,37186,37442,38210,39490,40258,43700,47426,47682,48450,49474,49730,51522,51778])),([7,31,992,2164802,8659208,12988812,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,25268,26938,27202,28994,29250,37186,37442,39490,40258,45634,47426,47682,49474,49730,51522,51778])),([7,31,992,2164802,8659208,17318416,18400817],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,19124,20034,21058,22082,25268,26938,27202,28994,29250,30018,35394,37186,37442,38210,39234,39490,47426,47682,48450,49474,49730,51778,52546])),([7,31,992,2164802,8659208,17318416,21648020],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,26938,28994,29250,33460,37186,37442,39234,39490,47426,47682,49474,49730,51778,52546])),([7,31,992,2164802,8659208,17318416,29224827],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,26938,28994,29250,35394,37186,37442,39234,39490,44354,47682,48450,49730,50498,51778,52546])),([7,31,992,2164802,8659208,17318416,32472030],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14687,14856,18854,19124,20034,21058,22082,25268,26938,27202,28994,29250,30018,33460,37186,37442,38210,39234,39490,46397,47426,47682,48450,49730,50498,51778,52546])),([7,31,992,6494406,8659208,17318416],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15110,16194,19380,20290,21314,22338,25524,26458,27458,28482,29506,30530,33716,34626,35650,36674,37698,38722,39746,40770])),([7,31,992,8659208,9741609,17318416],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15150,16194,19380,20314,21314,22338,25410,26548,27458,28482,29506,30530,33716,34626,35650,36674,37698,38722,39746,40770])),([7,31,992,8659208,17318416,18400817],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15189,16194,19380,20314,21314,22338,25524,26434,27458,28482,29506,30530,33626,34740,35650,36674,37698,38722,39746,40770])),([7,31,992,8659208,17318416,32472030],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15256,16194,19380,20314,21314,22338,25524,26434,27458,28482,29506,30530,33716,34740,35650,36674,37698,38722,39746,40770])),([7,31,1023,31744,1082401,8659208,17318416],(decodeHints [8,708,1032,1544,2056,2568,3080,3592,4104,4616,5128,5640,14856,15624,18884,19140,19976,20744,21000,22024,26888,28168,28936,29192,29960,33476,35080,35336,37128,38152,39176,39432,43358,43716,47368,48392,49416,49672,51464,51720])),([7,31,1023,1082401,2164802,4329604,8659208],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,5128,5640,14856,15624,20744,25268,28936,29192,33460,37128,37384,39176,39432,43700,45320,46600,47368,47624,49416,49672,51464,51720])),([7,31,1023,1082401,2164802,4329604,17318416],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,5128,5640,14856,15624,20744,25268,27144,28936,29192,33460,35336,37128,37384,39176,39432,43355,43700,46600,47368,47624,49416,49672,51464,51720])),([7,31,1023,1082401,2164802,8659208,17318416],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,5128,5640,14856,15624,20744,22024,25268,26150,27144,28168,28936,29192,30216,33460,35080,35336,37128,37384,39176,39432,40200,43355,43700,47368,47624,49416,49672,50440,51464,51720])),([7,31,1023,1082401,8659208,17318416],(decodeHints [436,948,1288,1800,2312,2824,3336,3848,4360,4872,15112,16308,19380,20404,21256,22280,25524,26376,27400,28424,29448,30472,33716,34568,35592,36616,37640,38664,39688,40712])),([7,31,1023,2164802,4329604,8659208,17318416],(decodeHints [8,692,1032,1544,2056,2568,3080,3592,4104,4616,5128,5640,14856,15624,22024,28168,28936,29192,35080,37128,37384,39176,39432,43355,47368,47624,49416,49672,51464,51720])),([7,31,31744,32736,1082401,8659208,17318416],(decodeHints [78,723,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14670,15059,18899,18952,21070,21838,26958,27214,29002,33491,35150,37179,39246,39502,43731,49486,49742,51534,51790])),([7,31,31744,1015808,1082401,8659944,17318416],(decodeHints [53,616,1077,1589,2101,2613,3125,3637,4149,4661,5173,5685,14791,14914,15922,18908,19022,20020,20789,21045,21810,22068,26930,27189,27957,28980,29237,30005,33288,35125,36146,37173,38196,39473,43624,45365,46386,47413,48436,49461,49717])),([7,31,31744,1015808,8659208,17318416,32539681],(decodeHints [8,723,1032,1544,2056,2568,3080,3592,4104,4616,5128,5640,14791,14914,18899,19022,20744,21000,25299,26888,28936,33234,33491,39176,39432,45058,45320,45576,47368,47624,49672])),([7,31,31744,1082401,1083361,8659208,17318416],(decodeHints [74,708,1098,1610,2122,2634,3146,3658,4170,4682,5194,5706,14791,14914,15933,19131,20810,21066,21821,25096,26954,27210,27965,29258,30026,33476,35133,36170,37194,37450,39225,39498,43716,45386,46397,47434,47690,51530,51786])),([7,31,31744,1082401,2164802,8659944,17318416],(decodeHints [56,625,1080,1592,2104,2616,3128,3640,4152,4664,5176,5688,14791,14914,15927,20791,21048,21816,24945,25200,26164,26936,27192,27959,28212,28984,29240,30260,33288,35128,36151,37430,39220,40248,43633,45368,46391,47416,47672,49464,49720,50484])),([7,31,31744,1082401,8659208,8659944,17318416],(decodeHints [59,616,1083,1595,2107,2619,3131,3643,4155,4667,5179,5691,14791,14914,15930,20794,21051,21819,25192,26205,26939,27195,27962,28212,28987,29243,30260,33288,35131,35387,36154,37433,39220,39483,40251,43624,45371,46394,47419,47675,49467,49723,50484])),([7,31,31744,1082401,8659208,17318416,33521664],(decodeHints [8,723,1032,1544,2056,2568,3080,3592,4104,4616,5128,5640,14791,14914,20483,20744,21000,25299,26888,28936,29192,33234,33491,37128,37384,39176,39432,43475,43598,45320,45576,47368,47624,49672])),([7,31,31744,1082401,8659208,17318416,33553439],(decodeHints [78,616,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,14791,14914,15938,20812,21070,21827,25192,26947,27980,29006,29262,33384,35150,36162,37198,37454,39246,39502,43598,44366,45378,45646,46414,47690,49723,50510])),([7,31,31744,1082401,8659944,17318416],(decodeHints [360,872,1332,1539,1844,2356,2868,3380,3892,4404,4916,15208,16180,19395,20419,21300,22324,25448,26461,27444,28468,29492,30516,33640,34612,35636,36660,37684,38708,39732,40756])),([7,31,31744,1083361,2164802,4329604,8659208],(decodeHints [74,661,1098,1610,2122,2634,3146,3658,4170,4682,5194,5706,14791,14914,15933,20810,21821,24576,24977,25232,26954,27965,33171,33426,35146,36157,39242,39498,43668,45373,45642,46410,47417,48714,49482,49738,51530,51786])),([7,31,1082401,1083361,2164802,4329604,8659208],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,5181,5693,15023,16011,18952,20797,21053,21821,24576,24998,25268,26941,27197,27965,33195,33460,35133,35389,36157,39229,39485,43700,45373,45629,46397,47417,48701,49469,49725,51517,51773])),([7,31,1082401,1083361,2164802,4329604,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,5181,5693,15020,18952,21053,21821,24576,24998,25268,26941,27197,29245,33195,33460,35133,35389,37437,39229,39485,43700,45373,45629,48701,49469,49725,51517,51773])),([7,31,1082401,1083361,2164802,8659208,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,5181,5693,15017,18952,21053,21821,24998,25268,26173,26941,27197,28221,29245,30269,33460,35133,35389,37177,37437,39229,39485,40253,43700,45373,45629,49469,49725,50493,51517,51773])),([7,31,1082401,1083361,8659208,17318416],(decodeHints [436,948,1341,1853,2365,2877,3389,3901,4413,4925,15284,16308,19352,20404,21309,22333,25524,26456,27453,28477,29501,30525,33716,34621,35645,36669,37693,38717,39741,40765])),([7,31,1082401,2164802,4329604,8659208,8659944],(decodeHints [58,720,1082,1594,2106,2618,3130,3642,4154,4666,5178,5690,18432,18896,19149,20794,21050,25040,25294,26938,27194,28986,29242,33488,35130,35386,36864,37178,37434,39226,39482,43528,45370,45625,51770,52538])),([7,31,1082401,2164802,4329604,8659208,33553439],(decodeHints [66,720,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,18432,18896,19149,20802,21058,25040,25294,26946,27202,28994,29250,33487,35138,35394,37186,37442,39234,39490,43586,44354,45629,46402,51522,51770])),([7,31,1082401,2164802,4329604,8659944,17318416],(decodeHints [58,692,1082,1594,2106,2618,3130,3642,4154,4666,5178,5690,14895,18746,19059,20018,20794,21050,22066,24890,25205,26167,26938,27194,28215,28986,29242,30002,30263,33288,35385,36154,37170,38202,39223,40250,43640,45370,45626,47418,47674,48434,49466,49722,50487,52794])),([7,31,1082401,2164802,4329604,17318416,33553439],(decodeHints [66,631,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,18432,18807,19059,20802,21058,24951,25205,26946,27202,28994,29250,33399,35138,35394,37186,37442,39234,39490,43586,44354,45629,48450,50498,51522])),([7,31,1082401,2164802,8659208,8659944,17318416],(decodeHints [58,625,1082,1594,2106,2618,3130,3642,4154,4666,5178,5690,18801,19056,20026,20794,21050,22074,25201,26202,26938,27194,28215,28986,29242,30010,30263,33288,35385,37178,38202,39223,39482,40250,43633,45370,45626,47418,47674,48442,49466,49722,50487])),([7,31,1082401,2164802,8659208,17318416,33553439],(decodeHints [66,625,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,18801,19056,20034,20802,21058,22082,25201,26946,27202,28994,29250,30018,33393,35138,35394,37186,37442,38210,39234,39490,43586,44354,45629,47426,48450,49722,50498])),([7,31,1082401,2164802,8659944,17318416],(decodeHints [369,881,1335,1847,2359,2560,2871,3383,3895,4407,4919,15284,16308,19313,20279,21303,22327,25457,26458,27447,28471,29495,30519,33649,34615,35639,36663,37687,38711,39735,40759])),([7,31,1082401,8659208,8659944,17318416],(decodeHints [360,872,1338,1850,2362,2874,3386,3898,4410,4922,15284,16308,19304,20314,21306,22330,25448,26458,27450,28474,29498,30522,33640,34618,35642,36666,37690,38714,39738,40762])),([7,31,1082401,8659208,17318416,33553439],(decodeHints [360,872,1346,1858,2370,2882,3394,3906,4418,4930,15256,16280,19304,20314,21314,22338,25448,26434,27458,28482,29506,30530,33602,34664,35650,36674,37698,38722,39746,40770])),([7,31,1082401,8659944,17318416],[]),([7,31,1083361,2164802,4329604,8659208,17318416],(decodeHints [61,692,1085,1597,2109,2621,3133,3645,4157,4669,5181,5693,14856,18432,18854,19109,22077,25003,25257,28221,28989,29245,33452,35129,36413,37181,37437,39229,39485,43609,44605,45629,46653,47421,47677,48701,49469,49725,50749,51517,51773,52797])),([7,31,2164802,4329604,8659208,8659944,17318416],(decodeHints [58,518,1082,1594,2106,2618,3130,3642,4154,4666,5178,5690,14650,18694,20794,21050,25094,26624,26938,27194,28986,29242,33288,39482,40250,45370,45626,47418,47674,49466,49722,51770])),([7,31,2164802,4329604,8659208,17318416,33553439],(decodeHints [66,518,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,14658,18694,20802,21058,26946,27202,28994,29250,35138,35394,37186,37442,39234,39490,43586,44354,49722,52546])),([7,992,1023,31744,1082401,8659208,17318416],(decodeHints [95,590,1119,1631,2143,2655,3167,3679,4191,4703,5215,5727,14943,15711,18766,19022,20063,20831,21087,22111,28264,29023,29279,30047,33358,35423,37215,38239,39263,39519,43342,47455,48479,49503,49759,51551,51807])),([7,992,1023,1082401,2164802,4329604,8659208],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,5215,5727,14943,15711,19010,26975,29023,29279,35167,37215,37471,39263,39519,44639,46687,47455,47711,49503,49759,51551,51807])),([7,992,1023,1082401,2164802,4329604,17318416],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,5215,5727,14943,15711,25154,26624,26975,27231,29023,29279,33346,35167,35423,37215,37471,39263,39519,43330,44639,46687,47455,47711,49503,49759,51551,51807])),([7,992,1023,1082401,2164802,8659208,17318416],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,5215,5727,14943,15711,22129,25154,26208,26975,27231,28255,29023,29279,30303,33346,35423,37215,37471,39263,39519,40287,43330,47455,47711,49503,49759,50527,51551,51807])),([7,992,1023,1082401,8659208,17318416],(decodeHints [322,834,1375,1887,2399,2911,3423,3935,4447,4959,15199,16194,19266,20290,21343,22367,25410,26463,27487,28511,29535,30559,33602,34655,35679,36703,37727,38751,39775,40799])),([7,992,1023,2164802,4329604,8659208,17318416],(decodeHints [95,578,1119,1631,2143,2655,3167,3679,4191,4703,5215,5727,14943,15711,20831,22022,26975,28197,29023,29279,37215,37471,39263,39519,43330,43586,47455,47711,49503,49759,51551,51807])),([7,992,31744,31775,1082401,8659208,17318416],(decodeHints [196,711,1220,1732,2244,2756,3268,3780,4292,4804,5316,5828,14670,14926,18887,19039,21188,21956,25031,27332,33223,33479,39364,39620,49604,49860,51652,51908])),([7,992,31744,1082401,2164802,4329631,8659208],(decodeHints [190,718,1214,1726,2238,2750,3262,3774,4286,4798,5310,5822,14803,15028,16043,18878,19150,20926,21931,27070,28075,29118,29374,35262,36267,39357,39612,43470,44730,45502,45758,46507,47550,47806,49598,49854,51902])),([7,992,31744,1082401,2164802,4329631,17318416],(decodeHints [190,629,1214,1726,2238,2750,3262,3774,4286,4798,5310,5822,14803,15028,16043,18878,20926,21931,25193,27070,28075,29118,29374,33375,35262,36267,39357,39612,44661,45483,45758,46526,47550,47806,49598,49854,51902])),([7,992,31744,1082401,2164831,8659208,17318416],(decodeHints [188,624,1212,1724,2236,2748,3260,3772,4284,4796,5308,5820,14803,15028,16038,18876,20924,21180,21926,25183,27068,27324,28070,33136,33392,35260,36262,37308,37564,39612,45478,46524,47548,47804,49852,51644,51900])),([7,992,31744,1082401,8659208,17318416,33521664],(decodeHints [95,711,1119,1631,2143,2655,3167,3679,4191,4703,5215,5727,14803,15028,21087,25287,29023,29279,33223,37215,37471,39263,39519,43463,43716,45407,45663,47455])),([7,992,31744,1082401,8659208,17318416,33554400],(decodeHints [196,616,1220,1732,2244,2756,3268,3780,4292,4804,5316,5710,14803,15028,16052,18884,20932,21188,21940,24936,25192,27076,28084,29124,29380,35256,36290,37316,37572,39364,39620,43716,44484,45492,45764,46532,50628,52676])),([7,992,1082401,2164802,2164831,4329604,8659208],(decodeHints [166,720,1190,1702,2214,2726,3238,3750,4262,4774,5286,5798,14758,15056,19152,20151,20902,21158,22182,25183,28672,29094,29350,30118,35238,35494,37286,37542,38310,39334,39590,43472,44701,45478,45734,47104,47526,47782,48550,49830,51622,51878])),([7,992,1082401,2164802,2164831,4329604,17318416],(decodeHints [166,631,1190,1702,2214,2726,3238,3750,4262,4774,5286,5798,14758,19063,20151,20902,21158,22182,25183,28672,29094,29350,30118,33394,35238,35494,37286,37542,38310,39334,39590,44663,45478,45734,47104,47526,47782,48550,49830,51622,51878])),([7,992,1082401,2164802,2164831,8659208,17318416],(decodeHints [166,625,1190,1702,2214,2726,3238,3750,4262,4774,5286,5798,14758,19057,20151,20902,21158,22182,25183,29094,29350,30118,33137,33393,35238,35494,37286,37542,38310,39590,45478,45734,47526,47782,48550,49830,51622,51878])),([7,992,1082401,2164802,4329604,8659208,33554400],(decodeHints [180,720,1204,1716,2228,2740,3252,3764,4276,4788,5300,5698,14772,15056,20916,21172,27060,27316,29108,29364,33232,34467,35252,35508,37300,37556,39348,39604,43700,44468,47782,48564,49835,50612,52660])),([7,992,1082401,2164802,4329604,17318416,33554400],(decodeHints [180,631,1204,1716,2228,2740,3252,3764,4276,4788,5300,5698,14772,19050,20916,21172,25202,27060,27316,29108,29364,34423,35252,35508,37300,37556,39348,39604,43700,44468,47782,48564,49835,50612,52660])),([7,992,1082401,2164802,4329631,8659208,17318416],(decodeHints [171,578,1195,1707,2219,2731,3243,3755,4267,4779,5291,5803,14763,14911,19049,20135,20907,21163,22183,25183,28075,29095,29350,30123,33082,33397,34475,35243,35499,36523,37291,37547,38311,38571,39595,40619,43697,44750,45483,45739,46763,47531,47787,48551,48811,49835,50859,51627,51883,52651,52907])),([7,992,1082401,2164802,4329631,17318416],(decodeHints [373,885,1451,1963,2475,2560,2987,3499,4011,4523,5035,15145,16299,18944,19317,20395,20992,21419,22443,25461,26548,27563,28587,28928,29611,30635,33653,34677,35755,36779,37120,37803,38827,39851,40875]))]
noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([7,992,1082401,2164802,8659208,17318416,33554400],(decodeHints [180,625,1204,1716,2228,2740,3252,3764,4276,4788,5300,5698,14772,19049,20149,20916,21172,22196,24945,25201,27060,27316,29108,29364,30132,35252,35508,37300,37556,38324,39348,39604,43700,44468,47540,47782,48564,50612,52660])),([7,992,1082401,2164831,8659208,17318416],(decodeHints [368,880,1446,1958,2470,2560,2982,3494,4006,4518,5030,15170,16294,19312,20407,21414,22438,25456,26534,27558,28582,29606,30630,33648,34672,35750,36774,37798,38822,39846,40870])),([7,992,1082401,8659208,17318416,33554400],(decodeHints [360,872,1460,1972,2484,2996,3508,4020,4532,5044,15256,16308,19304,20404,21428,22452,25448,26472,27572,28596,29620,30644,33716,34664,35764,36788,37812,38836,39860,40884])),([7,992,2164802,2164831,4329604,8659208,17318416],(decodeHints [166,578,1190,1702,2214,2726,3238,3750,4262,4774,5286,5798,14910,19039,21158,21926,27046,27302,29094,33082,34816,35238,35494,39334,39590,43586,45056,45478,45734,49574,49830,51622,51878])),([7,992,2164802,4329604,8659208,17318416,33554400],(decodeHints [180,518,1204,1716,2228,2740,3252,3764,4276,4788,5300,5698,20916,21172,24838,27060,27316,29108,29364,33286,35252,35508,37300,37556,39348,39604,43700,44468,45734,47787])),([7,31744,1015808,1082401,8659208,17318431,32505856],(decodeHints [209,733,1233,1745,2257,2769,3281,3793,4305,4817,5329,5841,14340,14801,15069,18435,18909,19165,20481,20945,21201,25053,27089,29137,29393,39377,43010,43485,43741,45521,45777,47569,47825,49873])),([8,31,992,31744,1015808,1082401,8659208,17318416],(decodeHints [83,709,1107,1619,2131,2643,3155,3667,4179,4691,5203,5715,6227,6739,14687,14856,18885,19010,20034,20819,21075,22082,25029,25166,26190,26963,27219,28238,29011,29267,30018,30286,35152,36866,37201,37459,38212,39250,39507,40271,43717,45372,45651,47428,48465,49487,50514,51539,51795,56005,59731,60738,61779,62798,63827,64083,65875,66131])),([8,31,992,31744,1082401,2164802,4329604,8659208],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,6222,6734,14687,14856,18884,19010,20034,20814,21070,22082,26954,27214,29004,30019,32768,33212,33476,37198,38210,39246,39502,43454,43716,47438,48450,49486,49742,51534,51790,56004,57659,58958,59715,59982,60748,61774,62030,63822,64078,65870,66126])),([8,31,992,31744,1082401,2164802,4329604,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,6222,6734,14687,14856,18884,19010,20034,20814,21070,22082,26954,29004,30019,32768,33212,33476,35406,37198,38210,39246,39502,43454,43716,45646,47438,48450,49486,49742,51534,51790,56004,58958,59726,59982,60738,61774,62030,63822,64078,65870,66126])),([8,31,992,31744,1082401,2164802,8659208,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,6222,6734,14687,14856,18884,19010,20034,20814,21070,22082,26954,29004,29262,30019,33212,33476,34382,35406,36430,37198,37454,38210,38478,39246,39502,40526,43716,45371,45646,47427,48460,49486,49742,51534,51790,52558,56004,59726,60738,61774,62030,63822,64078,64846,65870,66126])),([8,31,992,31744,1082401,8659208,17318416],(decodeHints [452,964,1358,1870,2382,2563,2894,3406,3918,4430,4942,5454,5966,15208,16206,19396,20302,21326,22350,25540,26564,27470,28494,29518,30542,33732,34653,35662,36686,37710,38734,39758,40782,43972,44878,45902,46926,47950,48974,49998,51022,52046,53070])),([8,31,992,31744,2164802,4329604,8659208,17318416],(decodeHints [78,708,1102,1614,2126,2638,3150,3662,4174,4686,5198,5710,6222,6734,14687,14856,18884,19010,20034,20814,21070,22082,25020,28672,29006,29262,30018,33214,37198,37454,38210,39246,39502,45371,47427,48460,49486,49742,51534,51790,57934,59726,60738,61774,62030,63822,64078,65870,66126])),([8,31,992,1082401,2164802,4329604,8659208,17318416],(decodeHints [66,692,1090,1602,2114,2626,3138,3650,4162,4674,5186,5698,6210,6722,14687,14856,19124,20148,20797,21058,22082,24576,24998,25268,26178,27202,28226,28994,29250,30018,30274,33195,33460,34370,35394,36418,37186,37442,38210,38466,39234,39490,40258,40514,43700,44634,45370,45634,46658,47426,47682,48450,48706,49474,49730,50498,50754,51522,51778,52546,52802,55988,56898,57922,58946,59714,59970,60738,60994,61762,62018,62786,63042,63810,64066,64834,65090,65858,66114,66882,67138])),([8,31,992,1082401,2164802,4329604,17318416],(decodeHints [436,948,1346,1858,2370,2882,3394,3584,3906,4418,4930,5442,5954,15223,16194,19380,20404,21314,22338,24576,25088,25524,26434,27136,27458,28482,29184,29506,30530,33024,33716,34626,35650,36674,37120,37698,38722,39168,39746,40770,43956,44866,45890,46914,47938,48962,49408,49986,51010,51712,52034,53058])),([8,31,992,1082401,2164802,8659208,17318416],(decodeHints [436,948,1346,1858,2370,2882,3394,3584,3906,4418,4930,5442,5954,15217,16194,19380,20404,21314,22338,25524,26434,27458,28482,29506,30530,33716,34650,35650,36674,37698,38722,39746,40770,43956,44866,45890,46914,47938,48962,49986,51010,52034,53058])),([8,31,992,1082401,8659208,17318416],[]),([8,31,992,2164802,4329604,8659208,17318416],(decodeHints [436,948,1346,1858,2370,2560,2882,3394,3906,4418,4930,5442,5954,15110,16194,19380,20290,21314,22338,24832,25524,26434,27458,28482,28928,29506,30530,33716,34650,35650,36674,37120,37698,38722,39424,39746,40770,43956,44866,45890,46914,47360,47938,48962,49664,49986,51010,52034,53058])),([8,31,31744,1015808,1082401,8659208,17318416,32505856],(decodeHints [8,723,1032,1544,2056,2568,3080,3592,4104,4616,5128,5640,6152,6664,14791,14914,18899,19022,20484,20744,21000,26627,26888,27144,28673,28936,29192,33491,35080,37128,39176,39432,43474,43731,49416,49672,51464,51720,55763,55891,57346,57608,57864,59656,59912,61704,61960,64008])),([8,992,31744,1015808,1082401,8659208,17318416,32505856],(decodeHints [95,711,1119,1631,2143,2655,3167,3679,4191,4703,5215,5727,6239,6751,14803,15028,18887,19140,20484,20831,21087,27231,29279,33479,39263,39519,43463,49503,49759,51551,51807,55751,56005,57346,57695,57951,59743,59999,61791]))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_0 0) BT.lf) (keyAt K_0 1) BT.lf) (keyAt K_0 2) (BT.nd BT.lf (keyAt K_0 3) BT.lf)) (keyAt K_0 4) (BT.nd (BT.nd BT.lf (keyAt K_0 5) BT.lf) (keyAt K_0 6) (BT.nd BT.lf (keyAt K_0 7) BT.lf))) (keyAt K_0 8) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_0 9) BT.lf) (keyAt K_0 10) BT.lf) (keyAt K_0 11) (BT.nd BT.lf (keyAt K_0 12) BT.lf)) (keyAt K_0 13) (BT.nd (BT.nd BT.lf (keyAt K_0 14) BT.lf) (keyAt K_0 15) (BT.nd BT.lf (keyAt K_0 16) BT.lf)))) (keyAt K_0 17) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_0 18) BT.lf) (keyAt K_0 19) BT.lf) (keyAt K_0 20) (BT.nd BT.lf (keyAt K_0 21) BT.lf)) (keyAt K_0 22) (BT.nd (BT.nd BT.lf (keyAt K_0 23) BT.lf) (keyAt K_0 24) (BT.nd BT.lf (keyAt K_0 25) BT.lf))) (keyAt K_0 26) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_0 27) BT.lf) (keyAt K_0 28) (BT.nd BT.lf (keyAt K_0 29) BT.lf)) (keyAt K_0 30) (BT.nd (BT.nd BT.lf (keyAt K_0 31) BT.lf) (keyAt K_0 32) (BT.nd BT.lf (keyAt K_0 33) BT.lf))))) (keyAt K_0 34) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_0 35) BT.lf) (keyAt K_0 36) BT.lf) (keyAt K_0 37) (BT.nd BT.lf (keyAt K_0 38) BT.lf)) (keyAt K_0 39) (BT.nd (BT.nd BT.lf (keyAt K_0 40) BT.lf) (keyAt K_0 41) (BT.nd BT.lf (keyAt K_0 42) BT.lf))) (keyAt K_0 43) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_0 44) BT.lf) (keyAt K_0 45) BT.lf) (keyAt K_0 46) (BT.nd BT.lf (keyAt K_0 47) BT.lf)) (keyAt K_0 48) (BT.nd (BT.nd BT.lf (keyAt K_0 49) BT.lf) (keyAt K_0 50) (BT.nd BT.lf (keyAt K_0 51) BT.lf)))) (keyAt K_0 52) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_0 53) BT.lf) (keyAt K_0 54) BT.lf) (keyAt K_0 55) (BT.nd BT.lf (keyAt K_0 56) BT.lf)) (keyAt K_0 57) (BT.nd (BT.nd BT.lf (keyAt K_0 58) BT.lf) (keyAt K_0 59) (BT.nd BT.lf (keyAt K_0 60) BT.lf))) (keyAt K_0 61) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_0 62) BT.lf) (keyAt K_0 63) (BT.nd BT.lf (keyAt K_1 0) BT.lf)) (keyAt K_1 1) (BT.nd (BT.nd BT.lf (keyAt K_1 2) BT.lf) (keyAt K_1 3) (BT.nd BT.lf (keyAt K_1 4) BT.lf)))))) (keyAt K_1 5) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_1 6) BT.lf) (keyAt K_1 7) BT.lf) (keyAt K_1 8) (BT.nd BT.lf (keyAt K_1 9) BT.lf)) (keyAt K_1 10) (BT.nd (BT.nd BT.lf (keyAt K_1 11) BT.lf) (keyAt K_1 12) (BT.nd BT.lf (keyAt K_1 13) BT.lf))) (keyAt K_1 14) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_1 15) BT.lf) (keyAt K_1 16) BT.lf) (keyAt K_1 17) (BT.nd BT.lf (keyAt K_1 18) BT.lf)) (keyAt K_1 19) (BT.nd (BT.nd BT.lf (keyAt K_1 20) BT.lf) (keyAt K_1 21) (BT.nd BT.lf (keyAt K_1 22) BT.lf)))) (keyAt K_1 23) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_1 24) BT.lf) (keyAt K_1 25) BT.lf) (keyAt K_1 26) (BT.nd BT.lf (keyAt K_1 27) BT.lf)) (keyAt K_1 28) (BT.nd (BT.nd BT.lf (keyAt K_1 29) BT.lf) (keyAt K_1 30) (BT.nd BT.lf (keyAt K_1 31) BT.lf))) (keyAt K_1 32) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_1 33) BT.lf) (keyAt K_1 34) (BT.nd BT.lf (keyAt K_1 35) BT.lf)) (keyAt K_1 36) (BT.nd (BT.nd BT.lf (keyAt K_1 37) BT.lf) (keyAt K_1 38) (BT.nd BT.lf (keyAt K_1 39) BT.lf))))) (keyAt K_1 40) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_1 41) BT.lf) (keyAt K_1 42) BT.lf) (keyAt K_1 43) (BT.nd BT.lf (keyAt K_1 44) BT.lf)) (keyAt K_1 45) (BT.nd (BT.nd BT.lf (keyAt K_1 46) BT.lf) (keyAt K_1 47) (BT.nd BT.lf (keyAt K_1 48) BT.lf))) (keyAt K_1 49) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_1 50) BT.lf) (keyAt K_1 51) (BT.nd BT.lf (keyAt K_1 52) BT.lf)) (keyAt K_1 53) (BT.nd (BT.nd BT.lf (keyAt K_1 54) BT.lf) (keyAt K_1 55) (BT.nd BT.lf (keyAt K_1 56) BT.lf)))) (keyAt K_1 57) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_1 58) BT.lf) (keyAt K_1 59) BT.lf) (keyAt K_1 60) (BT.nd BT.lf (keyAt K_1 61) BT.lf)) (keyAt K_1 62) (BT.nd (BT.nd BT.lf (keyAt K_1 63) BT.lf) (keyAt K_2 0) (BT.nd BT.lf (keyAt K_2 1) BT.lf))) (keyAt K_2 2) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_2 3) BT.lf) (keyAt K_2 4) (BT.nd BT.lf (keyAt K_2 5) BT.lf)) (keyAt K_2 6) (BT.nd (BT.nd BT.lf (keyAt K_2 7) BT.lf) (keyAt K_2 8) (BT.nd BT.lf (keyAt K_2 9) BT.lf))))))) (keyAt K_2 10) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_2 11) BT.lf) (keyAt K_2 12) BT.lf) (keyAt K_2 13) (BT.nd BT.lf (keyAt K_2 14) BT.lf)) (keyAt K_2 15) (BT.nd (BT.nd BT.lf (keyAt K_2 16) BT.lf) (keyAt K_2 17) (BT.nd BT.lf (keyAt K_2 18) BT.lf))) (keyAt K_2 19) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_2 20) BT.lf) (keyAt K_2 21) BT.lf) (keyAt K_2 22) (BT.nd BT.lf (keyAt K_2 23) BT.lf)) (keyAt K_2 24) (BT.nd (BT.nd BT.lf (keyAt K_2 25) BT.lf) (keyAt K_2 26) (BT.nd BT.lf (keyAt K_2 27) BT.lf)))) (keyAt K_2 28) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_2 29) BT.lf) (keyAt K_2 30) BT.lf) (keyAt K_2 31) (BT.nd BT.lf (keyAt K_2 32) BT.lf)) (keyAt K_2 33) (BT.nd (BT.nd BT.lf (keyAt K_2 34) BT.lf) (keyAt K_2 35) (BT.nd BT.lf (keyAt K_2 36) BT.lf))) (keyAt K_2 37) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_2 38) BT.lf) (keyAt K_2 39) (BT.nd BT.lf (keyAt K_2 40) BT.lf)) (keyAt K_2 41) (BT.nd (BT.nd BT.lf (keyAt K_2 42) BT.lf) (keyAt K_2 43) (BT.nd BT.lf (keyAt K_2 44) BT.lf))))) (keyAt K_2 45) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_2 46) BT.lf) (keyAt K_2 47) BT.lf) (keyAt K_2 48) (BT.nd BT.lf (keyAt K_2 49) BT.lf)) (keyAt K_2 50) (BT.nd (BT.nd BT.lf (keyAt K_2 51) BT.lf) (keyAt K_2 52) (BT.nd BT.lf (keyAt K_2 53) BT.lf))) (keyAt K_2 54) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_2 55) BT.lf) (keyAt K_2 56) (BT.nd BT.lf (keyAt K_2 57) BT.lf)) (keyAt K_2 58) (BT.nd (BT.nd BT.lf (keyAt K_2 59) BT.lf) (keyAt K_2 60) (BT.nd BT.lf (keyAt K_2 61) BT.lf)))) (keyAt K_2 62) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_2 63) BT.lf) (keyAt K_3 0) BT.lf) (keyAt K_3 1) (BT.nd BT.lf (keyAt K_3 2) BT.lf)) (keyAt K_3 3) (BT.nd (BT.nd BT.lf (keyAt K_3 4) BT.lf) (keyAt K_3 5) (BT.nd BT.lf (keyAt K_3 6) BT.lf))) (keyAt K_3 7) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_3 8) BT.lf) (keyAt K_3 9) (BT.nd BT.lf (keyAt K_3 10) BT.lf)) (keyAt K_3 11) (BT.nd (BT.nd BT.lf (keyAt K_3 12) BT.lf) (keyAt K_3 13) (BT.nd BT.lf (keyAt K_3 14) BT.lf)))))) (keyAt K_3 15) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_3 16) BT.lf) (keyAt K_3 17) BT.lf) (keyAt K_3 18) (BT.nd BT.lf (keyAt K_3 19) BT.lf)) (keyAt K_3 20) (BT.nd (BT.nd BT.lf (keyAt K_3 21) BT.lf) (keyAt K_3 22) (BT.nd BT.lf (keyAt K_3 23) BT.lf))) (keyAt K_3 24) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_3 25) BT.lf) (keyAt K_3 26) BT.lf) (keyAt K_3 27) (BT.nd BT.lf (keyAt K_3 28) BT.lf)) (keyAt K_3 29) (BT.nd (BT.nd BT.lf (keyAt K_3 30) BT.lf) (keyAt K_3 31) (BT.nd BT.lf (keyAt K_3 32) BT.lf)))) (keyAt K_3 33) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_3 34) BT.lf) (keyAt K_3 35) BT.lf) (keyAt K_3 36) (BT.nd BT.lf (keyAt K_3 37) BT.lf)) (keyAt K_3 38) (BT.nd (BT.nd BT.lf (keyAt K_3 39) BT.lf) (keyAt K_3 40) (BT.nd BT.lf (keyAt K_3 41) BT.lf))) (keyAt K_3 42) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_3 43) BT.lf) (keyAt K_3 44) (BT.nd BT.lf (keyAt K_3 45) BT.lf)) (keyAt K_3 46) (BT.nd (BT.nd BT.lf (keyAt K_3 47) BT.lf) (keyAt K_3 48) (BT.nd BT.lf (keyAt K_3 49) BT.lf))))) (keyAt K_3 50) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_3 51) BT.lf) (keyAt K_3 52) BT.lf) (keyAt K_3 53) (BT.nd BT.lf (keyAt K_3 54) BT.lf)) (keyAt K_3 55) (BT.nd (BT.nd BT.lf (keyAt K_3 56) BT.lf) (keyAt K_3 57) (BT.nd BT.lf (keyAt K_3 58) BT.lf))) (keyAt K_3 59) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_3 60) BT.lf) (keyAt K_3 61) (BT.nd BT.lf (keyAt K_3 62) BT.lf)) (keyAt K_3 63) (BT.nd (BT.nd BT.lf (keyAt K_4 0) BT.lf) (keyAt K_4 1) (BT.nd BT.lf (keyAt K_4 2) BT.lf)))) (keyAt K_4 3) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_4 4) BT.lf) (keyAt K_4 5) BT.lf) (keyAt K_4 6) (BT.nd BT.lf (keyAt K_4 7) BT.lf)) (keyAt K_4 8) (BT.nd (BT.nd BT.lf (keyAt K_4 9) BT.lf) (keyAt K_4 10) (BT.nd BT.lf (keyAt K_4 11) BT.lf))) (keyAt K_4 12) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_4 13) BT.lf) (keyAt K_4 14) (BT.nd BT.lf (keyAt K_4 15) BT.lf)) (keyAt K_4 16) (BT.nd (BT.nd BT.lf (keyAt K_4 17) BT.lf) (keyAt K_4 18) (BT.nd BT.lf (keyAt K_4 19) BT.lf)))))))) (keyAt K_4 20) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_4 21) BT.lf) (keyAt K_4 22) BT.lf) (keyAt K_4 23) (BT.nd BT.lf (keyAt K_4 24) BT.lf)) (keyAt K_4 25) (BT.nd (BT.nd BT.lf (keyAt K_4 26) BT.lf) (keyAt K_4 27) (BT.nd BT.lf (keyAt K_4 28) BT.lf))) (keyAt K_4 29) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_4 30) BT.lf) (keyAt K_4 31) BT.lf) (keyAt K_4 32) (BT.nd BT.lf (keyAt K_4 33) BT.lf)) (keyAt K_4 34) (BT.nd (BT.nd BT.lf (keyAt K_4 35) BT.lf) (keyAt K_4 36) (BT.nd BT.lf (keyAt K_4 37) BT.lf)))) (keyAt K_4 38) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_4 39) BT.lf) (keyAt K_4 40) BT.lf) (keyAt K_4 41) (BT.nd BT.lf (keyAt K_4 42) BT.lf)) (keyAt K_4 43) (BT.nd (BT.nd BT.lf (keyAt K_4 44) BT.lf) (keyAt K_4 45) (BT.nd BT.lf (keyAt K_4 46) BT.lf))) (keyAt K_4 47) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_4 48) BT.lf) (keyAt K_4 49) (BT.nd BT.lf (keyAt K_4 50) BT.lf)) (keyAt K_4 51) (BT.nd (BT.nd BT.lf (keyAt K_4 52) BT.lf) (keyAt K_4 53) (BT.nd BT.lf (keyAt K_4 54) BT.lf))))) (keyAt K_4 55) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_4 56) BT.lf) (keyAt K_4 57) BT.lf) (keyAt K_4 58) (BT.nd BT.lf (keyAt K_4 59) BT.lf)) (keyAt K_4 60) (BT.nd (BT.nd BT.lf (keyAt K_4 61) BT.lf) (keyAt K_4 62) (BT.nd BT.lf (keyAt K_4 63) BT.lf))) (keyAt K_5 0) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_5 1) BT.lf) (keyAt K_5 2) BT.lf) (keyAt K_5 3) (BT.nd BT.lf (keyAt K_5 4) BT.lf)) (keyAt K_5 5) (BT.nd (BT.nd BT.lf (keyAt K_5 6) BT.lf) (keyAt K_5 7) (BT.nd BT.lf (keyAt K_5 8) BT.lf)))) (keyAt K_5 9) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_5 10) BT.lf) (keyAt K_5 11) BT.lf) (keyAt K_5 12) (BT.nd BT.lf (keyAt K_5 13) BT.lf)) (keyAt K_5 14) (BT.nd (BT.nd BT.lf (keyAt K_5 15) BT.lf) (keyAt K_5 16) (BT.nd BT.lf (keyAt K_5 17) BT.lf))) (keyAt K_5 18) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_5 19) BT.lf) (keyAt K_5 20) (BT.nd BT.lf (keyAt K_5 21) BT.lf)) (keyAt K_5 22) (BT.nd (BT.nd BT.lf (keyAt K_5 23) BT.lf) (keyAt K_5 24) (BT.nd BT.lf (keyAt K_5 25) BT.lf)))))) (keyAt K_5 26) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_5 27) BT.lf) (keyAt K_5 28) BT.lf) (keyAt K_5 29) (BT.nd BT.lf (keyAt K_5 30) BT.lf)) (keyAt K_5 31) (BT.nd (BT.nd BT.lf (keyAt K_5 32) BT.lf) (keyAt K_5 33) (BT.nd BT.lf (keyAt K_5 34) BT.lf))) (keyAt K_5 35) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_5 36) BT.lf) (keyAt K_5 37) BT.lf) (keyAt K_5 38) (BT.nd BT.lf (keyAt K_5 39) BT.lf)) (keyAt K_5 40) (BT.nd (BT.nd BT.lf (keyAt K_5 41) BT.lf) (keyAt K_5 42) (BT.nd BT.lf (keyAt K_5 43) BT.lf)))) (keyAt K_5 44) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_5 45) BT.lf) (keyAt K_5 46) BT.lf) (keyAt K_5 47) (BT.nd BT.lf (keyAt K_5 48) BT.lf)) (keyAt K_5 49) (BT.nd (BT.nd BT.lf (keyAt K_5 50) BT.lf) (keyAt K_5 51) (BT.nd BT.lf (keyAt K_5 52) BT.lf))) (keyAt K_5 53) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_5 54) BT.lf) (keyAt K_5 55) (BT.nd BT.lf (keyAt K_5 56) BT.lf)) (keyAt K_5 57) (BT.nd (BT.nd BT.lf (keyAt K_5 58) BT.lf) (keyAt K_5 59) (BT.nd BT.lf (keyAt K_5 60) BT.lf))))) (keyAt K_5 61) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_5 62) BT.lf) (keyAt K_5 63) BT.lf) (keyAt K_6 0) (BT.nd BT.lf (keyAt K_6 1) BT.lf)) (keyAt K_6 2) (BT.nd (BT.nd BT.lf (keyAt K_6 3) BT.lf) (keyAt K_6 4) (BT.nd BT.lf (keyAt K_6 5) BT.lf))) (keyAt K_6 6) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_6 7) BT.lf) (keyAt K_6 8) (BT.nd BT.lf (keyAt K_6 9) BT.lf)) (keyAt K_6 10) (BT.nd (BT.nd BT.lf (keyAt K_6 11) BT.lf) (keyAt K_6 12) (BT.nd BT.lf (keyAt K_6 13) BT.lf)))) (keyAt K_6 14) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_6 15) BT.lf) (keyAt K_6 16) BT.lf) (keyAt K_6 17) (BT.nd BT.lf (keyAt K_6 18) BT.lf)) (keyAt K_6 19) (BT.nd (BT.nd BT.lf (keyAt K_6 20) BT.lf) (keyAt K_6 21) (BT.nd BT.lf (keyAt K_6 22) BT.lf))) (keyAt K_6 23) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_6 24) BT.lf) (keyAt K_6 25) (BT.nd BT.lf (keyAt K_6 26) BT.lf)) (keyAt K_6 27) (BT.nd (BT.nd BT.lf (keyAt K_6 28) BT.lf) (keyAt K_6 29) (BT.nd BT.lf (keyAt K_6 30) BT.lf))))))) (keyAt K_6 31) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_6 32) BT.lf) (keyAt K_6 33) BT.lf) (keyAt K_6 34) (BT.nd BT.lf (keyAt K_6 35) BT.lf)) (keyAt K_6 36) (BT.nd (BT.nd BT.lf (keyAt K_6 37) BT.lf) (keyAt K_6 38) (BT.nd BT.lf (keyAt K_6 39) BT.lf))) (keyAt K_6 40) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_6 41) BT.lf) (keyAt K_6 42) BT.lf) (keyAt K_6 43) (BT.nd BT.lf (keyAt K_6 44) BT.lf)) (keyAt K_6 45) (BT.nd (BT.nd BT.lf (keyAt K_6 46) BT.lf) (keyAt K_6 47) (BT.nd BT.lf (keyAt K_6 48) BT.lf)))) (keyAt K_6 49) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_6 50) BT.lf) (keyAt K_6 51) BT.lf) (keyAt K_6 52) (BT.nd BT.lf (keyAt K_6 53) BT.lf)) (keyAt K_6 54) (BT.nd (BT.nd BT.lf (keyAt K_6 55) BT.lf) (keyAt K_6 56) (BT.nd BT.lf (keyAt K_6 57) BT.lf))) (keyAt K_6 58) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_6 59) BT.lf) (keyAt K_6 60) (BT.nd BT.lf (keyAt K_6 61) BT.lf)) (keyAt K_6 62) (BT.nd (BT.nd BT.lf (keyAt K_6 63) BT.lf) (keyAt K_7 0) (BT.nd BT.lf (keyAt K_7 1) BT.lf))))) (keyAt K_7 2) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_7 3) BT.lf) (keyAt K_7 4) BT.lf) (keyAt K_7 5) (BT.nd BT.lf (keyAt K_7 6) BT.lf)) (keyAt K_7 7) (BT.nd (BT.nd BT.lf (keyAt K_7 8) BT.lf) (keyAt K_7 9) (BT.nd BT.lf (keyAt K_7 10) BT.lf))) (keyAt K_7 11) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_7 12) BT.lf) (keyAt K_7 13) (BT.nd BT.lf (keyAt K_7 14) BT.lf)) (keyAt K_7 15) (BT.nd (BT.nd BT.lf (keyAt K_7 16) BT.lf) (keyAt K_7 17) (BT.nd BT.lf (keyAt K_7 18) BT.lf)))) (keyAt K_7 19) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_7 20) BT.lf) (keyAt K_7 21) BT.lf) (keyAt K_7 22) (BT.nd BT.lf (keyAt K_7 23) BT.lf)) (keyAt K_7 24) (BT.nd (BT.nd BT.lf (keyAt K_7 25) BT.lf) (keyAt K_7 26) (BT.nd BT.lf (keyAt K_7 27) BT.lf))) (keyAt K_7 28) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_7 29) BT.lf) (keyAt K_7 30) (BT.nd BT.lf (keyAt K_7 31) BT.lf)) (keyAt K_7 32) (BT.nd (BT.nd BT.lf (keyAt K_7 33) BT.lf) (keyAt K_7 34) (BT.nd BT.lf (keyAt K_7 35) BT.lf)))))) (keyAt K_7 36) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_7 37) BT.lf) (keyAt K_7 38) BT.lf) (keyAt K_7 39) (BT.nd BT.lf (keyAt K_7 40) BT.lf)) (keyAt K_7 41) (BT.nd (BT.nd BT.lf (keyAt K_7 42) BT.lf) (keyAt K_7 43) (BT.nd BT.lf (keyAt K_7 44) BT.lf))) (keyAt K_7 45) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_7 46) BT.lf) (keyAt K_7 47) BT.lf) (keyAt K_7 48) (BT.nd BT.lf (keyAt K_7 49) BT.lf)) (keyAt K_7 50) (BT.nd (BT.nd BT.lf (keyAt K_7 51) BT.lf) (keyAt K_7 52) (BT.nd BT.lf (keyAt K_7 53) BT.lf)))) (keyAt K_7 54) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_7 55) BT.lf) (keyAt K_7 56) BT.lf) (keyAt K_7 57) (BT.nd BT.lf (keyAt K_7 58) BT.lf)) (keyAt K_7 59) (BT.nd (BT.nd BT.lf (keyAt K_7 60) BT.lf) (keyAt K_7 61) (BT.nd BT.lf (keyAt K_7 62) BT.lf))) (keyAt K_7 63) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_8 0) BT.lf) (keyAt K_8 1) (BT.nd BT.lf (keyAt K_8 2) BT.lf)) (keyAt K_8 3) (BT.nd (BT.nd BT.lf (keyAt K_8 4) BT.lf) (keyAt K_8 5) (BT.nd BT.lf (keyAt K_8 6) BT.lf))))) (keyAt K_8 7) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_8 8) BT.lf) (keyAt K_8 9) BT.lf) (keyAt K_8 10) (BT.nd BT.lf (keyAt K_8 11) BT.lf)) (keyAt K_8 12) (BT.nd (BT.nd BT.lf (keyAt K_8 13) BT.lf) (keyAt K_8 14) (BT.nd BT.lf (keyAt K_8 15) BT.lf))) (keyAt K_8 16) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_8 17) BT.lf) (keyAt K_8 18) (BT.nd BT.lf (keyAt K_8 19) BT.lf)) (keyAt K_8 20) (BT.nd (BT.nd BT.lf (keyAt K_8 21) BT.lf) (keyAt K_8 22) (BT.nd BT.lf (keyAt K_8 23) BT.lf)))) (keyAt K_8 24) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_8 25) BT.lf) (keyAt K_8 26) BT.lf) (keyAt K_8 27) (BT.nd BT.lf (keyAt K_8 28) BT.lf)) (keyAt K_8 29) (BT.nd (BT.nd BT.lf (keyAt K_8 30) BT.lf) (keyAt K_8 31) (BT.nd BT.lf (keyAt K_8 32) BT.lf))) (keyAt K_8 33) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_8 34) BT.lf) (keyAt K_8 35) (BT.nd BT.lf (keyAt K_8 36) BT.lf)) (keyAt K_8 37) (BT.nd (BT.nd BT.lf (keyAt K_8 38) BT.lf) (keyAt K_8 39) (BT.nd BT.lf (keyAt K_8 40) BT.lf))))))))) (keyAt K_8 41) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_8 42) BT.lf) (keyAt K_8 43) BT.lf) (keyAt K_8 44) (BT.nd BT.lf (keyAt K_8 45) BT.lf)) (keyAt K_8 46) (BT.nd (BT.nd BT.lf (keyAt K_8 47) BT.lf) (keyAt K_8 48) (BT.nd BT.lf (keyAt K_8 49) BT.lf))) (keyAt K_8 50) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_8 51) BT.lf) (keyAt K_8 52) BT.lf) (keyAt K_8 53) (BT.nd BT.lf (keyAt K_8 54) BT.lf)) (keyAt K_8 55) (BT.nd (BT.nd BT.lf (keyAt K_8 56) BT.lf) (keyAt K_8 57) (BT.nd BT.lf (keyAt K_8 58) BT.lf)))) (keyAt K_8 59) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_8 60) BT.lf) (keyAt K_8 61) BT.lf) (keyAt K_8 62) (BT.nd BT.lf (keyAt K_8 63) BT.lf)) (keyAt K_9 0) (BT.nd (BT.nd BT.lf (keyAt K_9 1) BT.lf) (keyAt K_9 2) (BT.nd BT.lf (keyAt K_9 3) BT.lf))) (keyAt K_9 4) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_9 5) BT.lf) (keyAt K_9 6) (BT.nd BT.lf (keyAt K_9 7) BT.lf)) (keyAt K_9 8) (BT.nd (BT.nd BT.lf (keyAt K_9 9) BT.lf) (keyAt K_9 10) (BT.nd BT.lf (keyAt K_9 11) BT.lf))))) (keyAt K_9 12) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_9 13) BT.lf) (keyAt K_9 14) BT.lf) (keyAt K_9 15) (BT.nd BT.lf (keyAt K_9 16) BT.lf)) (keyAt K_9 17) (BT.nd (BT.nd BT.lf (keyAt K_9 18) BT.lf) (keyAt K_9 19) (BT.nd BT.lf (keyAt K_9 20) BT.lf))) (keyAt K_9 21) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_9 22) BT.lf) (keyAt K_9 23) BT.lf) (keyAt K_9 24) (BT.nd BT.lf (keyAt K_9 25) BT.lf)) (keyAt K_9 26) (BT.nd (BT.nd BT.lf (keyAt K_9 27) BT.lf) (keyAt K_9 28) (BT.nd BT.lf (keyAt K_9 29) BT.lf)))) (keyAt K_9 30) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_9 31) BT.lf) (keyAt K_9 32) BT.lf) (keyAt K_9 33) (BT.nd BT.lf (keyAt K_9 34) BT.lf)) (keyAt K_9 35) (BT.nd (BT.nd BT.lf (keyAt K_9 36) BT.lf) (keyAt K_9 37) (BT.nd BT.lf (keyAt K_9 38) BT.lf))) (keyAt K_9 39) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_9 40) BT.lf) (keyAt K_9 41) (BT.nd BT.lf (keyAt K_9 42) BT.lf)) (keyAt K_9 43) (BT.nd (BT.nd BT.lf (keyAt K_9 44) BT.lf) (keyAt K_9 45) (BT.nd BT.lf (keyAt K_9 46) BT.lf)))))) (keyAt K_9 47) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_9 48) BT.lf) (keyAt K_9 49) BT.lf) (keyAt K_9 50) (BT.nd BT.lf (keyAt K_9 51) BT.lf)) (keyAt K_9 52) (BT.nd (BT.nd BT.lf (keyAt K_9 53) BT.lf) (keyAt K_9 54) (BT.nd BT.lf (keyAt K_9 55) BT.lf))) (keyAt K_9 56) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_9 57) BT.lf) (keyAt K_9 58) BT.lf) (keyAt K_9 59) (BT.nd BT.lf (keyAt K_9 60) BT.lf)) (keyAt K_9 61) (BT.nd (BT.nd BT.lf (keyAt K_9 62) BT.lf) (keyAt K_9 63) (BT.nd BT.lf (keyAt K_10 0) BT.lf)))) (keyAt K_10 1) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_10 2) BT.lf) (keyAt K_10 3) BT.lf) (keyAt K_10 4) (BT.nd BT.lf (keyAt K_10 5) BT.lf)) (keyAt K_10 6) (BT.nd (BT.nd BT.lf (keyAt K_10 7) BT.lf) (keyAt K_10 8) (BT.nd BT.lf (keyAt K_10 9) BT.lf))) (keyAt K_10 10) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_10 11) BT.lf) (keyAt K_10 12) (BT.nd BT.lf (keyAt K_10 13) BT.lf)) (keyAt K_10 14) (BT.nd (BT.nd BT.lf (keyAt K_10 15) BT.lf) (keyAt K_10 16) (BT.nd BT.lf (keyAt K_10 17) BT.lf))))) (keyAt K_10 18) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_10 19) BT.lf) (keyAt K_10 20) BT.lf) (keyAt K_10 21) (BT.nd BT.lf (keyAt K_10 22) BT.lf)) (keyAt K_10 23) (BT.nd (BT.nd BT.lf (keyAt K_10 24) BT.lf) (keyAt K_10 25) (BT.nd BT.lf (keyAt K_10 26) BT.lf))) (keyAt K_10 27) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_10 28) BT.lf) (keyAt K_10 29) (BT.nd BT.lf (keyAt K_10 30) BT.lf)) (keyAt K_10 31) (BT.nd (BT.nd BT.lf (keyAt K_10 32) BT.lf) (keyAt K_10 33) (BT.nd BT.lf (keyAt K_10 34) BT.lf)))) (keyAt K_10 35) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_10 36) BT.lf) (keyAt K_10 37) BT.lf) (keyAt K_10 38) (BT.nd BT.lf (keyAt K_10 39) BT.lf)) (keyAt K_10 40) (BT.nd (BT.nd BT.lf (keyAt K_10 41) BT.lf) (keyAt K_10 42) (BT.nd BT.lf (keyAt K_10 43) BT.lf))) (keyAt K_10 44) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_10 45) BT.lf) (keyAt K_10 46) (BT.nd BT.lf (keyAt K_10 47) BT.lf)) (keyAt K_10 48) (BT.nd (BT.nd BT.lf (keyAt K_10 49) BT.lf) (keyAt K_10 50) (BT.nd BT.lf (keyAt K_10 51) BT.lf))))))) (keyAt K_10 52) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_10 53) BT.lf) (keyAt K_10 54) BT.lf) (keyAt K_10 55) (BT.nd BT.lf (keyAt K_10 56) BT.lf)) (keyAt K_10 57) (BT.nd (BT.nd BT.lf (keyAt K_10 58) BT.lf) (keyAt K_10 59) (BT.nd BT.lf (keyAt K_10 60) BT.lf))) (keyAt K_10 61) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_10 62) BT.lf) (keyAt K_10 63) BT.lf) (keyAt K_11 0) (BT.nd BT.lf (keyAt K_11 1) BT.lf)) (keyAt K_11 2) (BT.nd (BT.nd BT.lf (keyAt K_11 3) BT.lf) (keyAt K_11 4) (BT.nd BT.lf (keyAt K_11 5) BT.lf)))) (keyAt K_11 6) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_11 7) BT.lf) (keyAt K_11 8) BT.lf) (keyAt K_11 9) (BT.nd BT.lf (keyAt K_11 10) BT.lf)) (keyAt K_11 11) (BT.nd (BT.nd BT.lf (keyAt K_11 12) BT.lf) (keyAt K_11 13) (BT.nd BT.lf (keyAt K_11 14) BT.lf))) (keyAt K_11 15) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_11 16) BT.lf) (keyAt K_11 17) (BT.nd BT.lf (keyAt K_11 18) BT.lf)) (keyAt K_11 19) (BT.nd (BT.nd BT.lf (keyAt K_11 20) BT.lf) (keyAt K_11 21) (BT.nd BT.lf (keyAt K_11 22) BT.lf))))) (keyAt K_11 23) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_11 24) BT.lf) (keyAt K_11 25) BT.lf) (keyAt K_11 26) (BT.nd BT.lf (keyAt K_11 27) BT.lf)) (keyAt K_11 28) (BT.nd (BT.nd BT.lf (keyAt K_11 29) BT.lf) (keyAt K_11 30) (BT.nd BT.lf (keyAt K_11 31) BT.lf))) (keyAt K_11 32) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_11 33) BT.lf) (keyAt K_11 34) (BT.nd BT.lf (keyAt K_11 35) BT.lf)) (keyAt K_11 36) (BT.nd (BT.nd BT.lf (keyAt K_11 37) BT.lf) (keyAt K_11 38) (BT.nd BT.lf (keyAt K_11 39) BT.lf)))) (keyAt K_11 40) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_11 41) BT.lf) (keyAt K_11 42) BT.lf) (keyAt K_11 43) (BT.nd BT.lf (keyAt K_11 44) BT.lf)) (keyAt K_11 45) (BT.nd (BT.nd BT.lf (keyAt K_11 46) BT.lf) (keyAt K_11 47) (BT.nd BT.lf (keyAt K_11 48) BT.lf))) (keyAt K_11 49) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_11 50) BT.lf) (keyAt K_11 51) (BT.nd BT.lf (keyAt K_11 52) BT.lf)) (keyAt K_11 53) (BT.nd (BT.nd BT.lf (keyAt K_11 54) BT.lf) (keyAt K_11 55) (BT.nd BT.lf (keyAt K_11 56) BT.lf)))))) (keyAt K_11 57) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_11 58) BT.lf) (keyAt K_11 59) BT.lf) (keyAt K_11 60) (BT.nd BT.lf (keyAt K_11 61) BT.lf)) (keyAt K_11 62) (BT.nd (BT.nd BT.lf (keyAt K_11 63) BT.lf) (keyAt K_12 0) (BT.nd BT.lf (keyAt K_12 1) BT.lf))) (keyAt K_12 2) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_12 3) BT.lf) (keyAt K_12 4) BT.lf) (keyAt K_12 5) (BT.nd BT.lf (keyAt K_12 6) BT.lf)) (keyAt K_12 7) (BT.nd (BT.nd BT.lf (keyAt K_12 8) BT.lf) (keyAt K_12 9) (BT.nd BT.lf (keyAt K_12 10) BT.lf)))) (keyAt K_12 11) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_12 12) BT.lf) (keyAt K_12 13) BT.lf) (keyAt K_12 14) (BT.nd BT.lf (keyAt K_12 15) BT.lf)) (keyAt K_12 16) (BT.nd (BT.nd BT.lf (keyAt K_12 17) BT.lf) (keyAt K_12 18) (BT.nd BT.lf (keyAt K_12 19) BT.lf))) (keyAt K_12 20) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_12 21) BT.lf) (keyAt K_12 22) (BT.nd BT.lf (keyAt K_12 23) BT.lf)) (keyAt K_12 24) (BT.nd (BT.nd BT.lf (keyAt K_12 25) BT.lf) (keyAt K_12 26) (BT.nd BT.lf (keyAt K_12 27) BT.lf))))) (keyAt K_12 28) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_12 29) BT.lf) (keyAt K_12 30) BT.lf) (keyAt K_12 31) (BT.nd BT.lf (keyAt K_12 32) BT.lf)) (keyAt K_12 33) (BT.nd (BT.nd BT.lf (keyAt K_12 34) BT.lf) (keyAt K_12 35) (BT.nd BT.lf (keyAt K_12 36) BT.lf))) (keyAt K_12 37) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_12 38) BT.lf) (keyAt K_12 39) (BT.nd BT.lf (keyAt K_12 40) BT.lf)) (keyAt K_12 41) (BT.nd (BT.nd BT.lf (keyAt K_12 42) BT.lf) (keyAt K_12 43) (BT.nd BT.lf (keyAt K_12 44) BT.lf)))) (keyAt K_12 45) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_12 46) BT.lf) (keyAt K_12 47) BT.lf) (keyAt K_12 48) (BT.nd BT.lf (keyAt K_12 49) BT.lf)) (keyAt K_12 50) (BT.nd (BT.nd BT.lf (keyAt K_12 51) BT.lf) (keyAt K_12 52) (BT.nd BT.lf (keyAt K_12 53) BT.lf))) (keyAt K_12 54) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_12 55) BT.lf) (keyAt K_12 56) (BT.nd BT.lf (keyAt K_12 57) BT.lf)) (keyAt K_12 58) (BT.nd (BT.nd BT.lf (keyAt K_12 59) BT.lf) (keyAt K_12 60) (BT.nd BT.lf (keyAt K_12 61) BT.lf)))))))) (keyAt K_12 62) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_12 63) BT.lf) (keyAt K_13 0) BT.lf) (keyAt K_13 1) (BT.nd BT.lf (keyAt K_13 2) BT.lf)) (keyAt K_13 3) (BT.nd (BT.nd BT.lf (keyAt K_13 4) BT.lf) (keyAt K_13 5) (BT.nd BT.lf (keyAt K_13 6) BT.lf))) (keyAt K_13 7) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_13 8) BT.lf) (keyAt K_13 9) BT.lf) (keyAt K_13 10) (BT.nd BT.lf (keyAt K_13 11) BT.lf)) (keyAt K_13 12) (BT.nd (BT.nd BT.lf (keyAt K_13 13) BT.lf) (keyAt K_13 14) (BT.nd BT.lf (keyAt K_13 15) BT.lf)))) (keyAt K_13 16) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_13 17) BT.lf) (keyAt K_13 18) BT.lf) (keyAt K_13 19) (BT.nd BT.lf (keyAt K_13 20) BT.lf)) (keyAt K_13 21) (BT.nd (BT.nd BT.lf (keyAt K_13 22) BT.lf) (keyAt K_13 23) (BT.nd BT.lf (keyAt K_13 24) BT.lf))) (keyAt K_13 25) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_13 26) BT.lf) (keyAt K_13 27) (BT.nd BT.lf (keyAt K_13 28) BT.lf)) (keyAt K_13 29) (BT.nd (BT.nd BT.lf (keyAt K_13 30) BT.lf) (keyAt K_13 31) (BT.nd BT.lf (keyAt K_13 32) BT.lf))))) (keyAt K_13 33) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_13 34) BT.lf) (keyAt K_13 35) BT.lf) (keyAt K_13 36) (BT.nd BT.lf (keyAt K_13 37) BT.lf)) (keyAt K_13 38) (BT.nd (BT.nd BT.lf (keyAt K_13 39) BT.lf) (keyAt K_13 40) (BT.nd BT.lf (keyAt K_13 41) BT.lf))) (keyAt K_13 42) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_13 43) BT.lf) (keyAt K_13 44) BT.lf) (keyAt K_13 45) (BT.nd BT.lf (keyAt K_13 46) BT.lf)) (keyAt K_13 47) (BT.nd (BT.nd BT.lf (keyAt K_13 48) BT.lf) (keyAt K_13 49) (BT.nd BT.lf (keyAt K_13 50) BT.lf)))) (keyAt K_13 51) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_13 52) BT.lf) (keyAt K_13 53) BT.lf) (keyAt K_13 54) (BT.nd BT.lf (keyAt K_13 55) BT.lf)) (keyAt K_13 56) (BT.nd (BT.nd BT.lf (keyAt K_13 57) BT.lf) (keyAt K_13 58) (BT.nd BT.lf (keyAt K_13 59) BT.lf))) (keyAt K_13 60) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_13 61) BT.lf) (keyAt K_13 62) (BT.nd BT.lf (keyAt K_13 63) BT.lf)) (keyAt K_14 0) (BT.nd (BT.nd BT.lf (keyAt K_14 1) BT.lf) (keyAt K_14 2) (BT.nd BT.lf (keyAt K_14 3) BT.lf)))))) (keyAt K_14 4) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_14 5) BT.lf) (keyAt K_14 6) BT.lf) (keyAt K_14 7) (BT.nd BT.lf (keyAt K_14 8) BT.lf)) (keyAt K_14 9) (BT.nd (BT.nd BT.lf (keyAt K_14 10) BT.lf) (keyAt K_14 11) (BT.nd BT.lf (keyAt K_14 12) BT.lf))) (keyAt K_14 13) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_14 14) BT.lf) (keyAt K_14 15) BT.lf) (keyAt K_14 16) (BT.nd BT.lf (keyAt K_14 17) BT.lf)) (keyAt K_14 18) (BT.nd (BT.nd BT.lf (keyAt K_14 19) BT.lf) (keyAt K_14 20) (BT.nd BT.lf (keyAt K_14 21) BT.lf)))) (keyAt K_14 22) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_14 23) BT.lf) (keyAt K_14 24) BT.lf) (keyAt K_14 25) (BT.nd BT.lf (keyAt K_14 26) BT.lf)) (keyAt K_14 27) (BT.nd (BT.nd BT.lf (keyAt K_14 28) BT.lf) (keyAt K_14 29) (BT.nd BT.lf (keyAt K_14 30) BT.lf))) (keyAt K_14 31) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_14 32) BT.lf) (keyAt K_14 33) (BT.nd BT.lf (keyAt K_14 34) BT.lf)) (keyAt K_14 35) (BT.nd (BT.nd BT.lf (keyAt K_14 36) BT.lf) (keyAt K_14 37) (BT.nd BT.lf (keyAt K_14 38) BT.lf))))) (keyAt K_14 39) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_14 40) BT.lf) (keyAt K_14 41) BT.lf) (keyAt K_14 42) (BT.nd BT.lf (keyAt K_14 43) BT.lf)) (keyAt K_14 44) (BT.nd (BT.nd BT.lf (keyAt K_14 45) BT.lf) (keyAt K_14 46) (BT.nd BT.lf (keyAt K_14 47) BT.lf))) (keyAt K_14 48) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_14 49) BT.lf) (keyAt K_14 50) (BT.nd BT.lf (keyAt K_14 51) BT.lf)) (keyAt K_14 52) (BT.nd (BT.nd BT.lf (keyAt K_14 53) BT.lf) (keyAt K_14 54) (BT.nd BT.lf (keyAt K_14 55) BT.lf)))) (keyAt K_14 56) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_14 57) BT.lf) (keyAt K_14 58) BT.lf) (keyAt K_14 59) (BT.nd BT.lf (keyAt K_14 60) BT.lf)) (keyAt K_14 61) (BT.nd (BT.nd BT.lf (keyAt K_14 62) BT.lf) (keyAt K_14 63) (BT.nd BT.lf (keyAt K_15 0) BT.lf))) (keyAt K_15 1) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_15 2) BT.lf) (keyAt K_15 3) (BT.nd BT.lf (keyAt K_15 4) BT.lf)) (keyAt K_15 5) (BT.nd (BT.nd BT.lf (keyAt K_15 6) BT.lf) (keyAt K_15 7) (BT.nd BT.lf (keyAt K_15 8) BT.lf))))))) (keyAt K_15 9) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_15 10) BT.lf) (keyAt K_15 11) BT.lf) (keyAt K_15 12) (BT.nd BT.lf (keyAt K_15 13) BT.lf)) (keyAt K_15 14) (BT.nd (BT.nd BT.lf (keyAt K_15 15) BT.lf) (keyAt K_15 16) (BT.nd BT.lf (keyAt K_15 17) BT.lf))) (keyAt K_15 18) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_15 19) BT.lf) (keyAt K_15 20) BT.lf) (keyAt K_15 21) (BT.nd BT.lf (keyAt K_15 22) BT.lf)) (keyAt K_15 23) (BT.nd (BT.nd BT.lf (keyAt K_15 24) BT.lf) (keyAt K_15 25) (BT.nd BT.lf (keyAt K_15 26) BT.lf)))) (keyAt K_15 27) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_15 28) BT.lf) (keyAt K_15 29) BT.lf) (keyAt K_15 30) (BT.nd BT.lf (keyAt K_15 31) BT.lf)) (keyAt K_15 32) (BT.nd (BT.nd BT.lf (keyAt K_15 33) BT.lf) (keyAt K_15 34) (BT.nd BT.lf (keyAt K_15 35) BT.lf))) (keyAt K_15 36) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_15 37) BT.lf) (keyAt K_15 38) (BT.nd BT.lf (keyAt K_15 39) BT.lf)) (keyAt K_15 40) (BT.nd (BT.nd BT.lf (keyAt K_15 41) BT.lf) (keyAt K_15 42) (BT.nd BT.lf (keyAt K_15 43) BT.lf))))) (keyAt K_15 44) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_15 45) BT.lf) (keyAt K_15 46) BT.lf) (keyAt K_15 47) (BT.nd BT.lf (keyAt K_15 48) BT.lf)) (keyAt K_15 49) (BT.nd (BT.nd BT.lf (keyAt K_15 50) BT.lf) (keyAt K_15 51) (BT.nd BT.lf (keyAt K_15 52) BT.lf))) (keyAt K_15 53) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_15 54) BT.lf) (keyAt K_15 55) (BT.nd BT.lf (keyAt K_15 56) BT.lf)) (keyAt K_15 57) (BT.nd (BT.nd BT.lf (keyAt K_15 58) BT.lf) (keyAt K_15 59) (BT.nd BT.lf (keyAt K_15 60) BT.lf)))) (keyAt K_15 61) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_15 62) BT.lf) (keyAt K_15 63) BT.lf) (keyAt K_16 0) (BT.nd BT.lf (keyAt K_16 1) BT.lf)) (keyAt K_16 2) (BT.nd (BT.nd BT.lf (keyAt K_16 3) BT.lf) (keyAt K_16 4) (BT.nd BT.lf (keyAt K_16 5) BT.lf))) (keyAt K_16 6) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_16 7) BT.lf) (keyAt K_16 8) (BT.nd BT.lf (keyAt K_16 9) BT.lf)) (keyAt K_16 10) (BT.nd (BT.nd BT.lf (keyAt K_16 11) BT.lf) (keyAt K_16 12) (BT.nd BT.lf (keyAt K_16 13) BT.lf)))))) (keyAt K_16 14) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_16 15) BT.lf) (keyAt K_16 16) BT.lf) (keyAt K_16 17) (BT.nd BT.lf (keyAt K_16 18) BT.lf)) (keyAt K_16 19) (BT.nd (BT.nd BT.lf (keyAt K_16 20) BT.lf) (keyAt K_16 21) (BT.nd BT.lf (keyAt K_16 22) BT.lf))) (keyAt K_16 23) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_16 24) BT.lf) (keyAt K_16 25) BT.lf) (keyAt K_16 26) (BT.nd BT.lf (keyAt K_16 27) BT.lf)) (keyAt K_16 28) (BT.nd (BT.nd BT.lf (keyAt K_16 29) BT.lf) (keyAt K_16 30) (BT.nd BT.lf (keyAt K_16 31) BT.lf)))) (keyAt K_16 32) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_16 33) BT.lf) (keyAt K_16 34) BT.lf) (keyAt K_16 35) (BT.nd BT.lf (keyAt K_16 36) BT.lf)) (keyAt K_16 37) (BT.nd (BT.nd BT.lf (keyAt K_16 38) BT.lf) (keyAt K_16 39) (BT.nd BT.lf (keyAt K_16 40) BT.lf))) (keyAt K_16 41) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_16 42) BT.lf) (keyAt K_16 43) (BT.nd BT.lf (keyAt K_16 44) BT.lf)) (keyAt K_16 45) (BT.nd (BT.nd BT.lf (keyAt K_16 46) BT.lf) (keyAt K_16 47) (BT.nd BT.lf (keyAt K_16 48) BT.lf))))) (keyAt K_16 49) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_16 50) BT.lf) (keyAt K_16 51) BT.lf) (keyAt K_16 52) (BT.nd BT.lf (keyAt K_16 53) BT.lf)) (keyAt K_16 54) (BT.nd (BT.nd BT.lf (keyAt K_16 55) BT.lf) (keyAt K_16 56) (BT.nd BT.lf (keyAt K_16 57) BT.lf))) (keyAt K_16 58) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_16 59) BT.lf) (keyAt K_16 60) (BT.nd BT.lf (keyAt K_16 61) BT.lf)) (keyAt K_16 62) (BT.nd (BT.nd BT.lf (keyAt K_16 63) BT.lf) (keyAt K_17 0) (BT.nd BT.lf (keyAt K_17 1) BT.lf)))) (keyAt K_17 2) (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_17 3) BT.lf) (keyAt K_17 4) BT.lf) (keyAt K_17 5) (BT.nd BT.lf (keyAt K_17 6) BT.lf)) (keyAt K_17 7) (BT.nd (BT.nd BT.lf (keyAt K_17 8) BT.lf) (keyAt K_17 9) (BT.nd BT.lf (keyAt K_17 10) BT.lf))) (keyAt K_17 11) (BT.nd (BT.nd (BT.nd BT.lf (keyAt K_17 12) BT.lf) (keyAt K_17 13) (BT.nd BT.lf (keyAt K_17 14) BT.lf)) (keyAt K_17 15) (BT.nd (BT.nd BT.lf (keyAt K_17 16) BT.lf) (keyAt K_17 17) (BT.nd BT.lf (keyAt K_17 18) BT.lf))))))))))


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = (((((K_0 ++ K_1) ++ (K_2 ++ K_3)) ++ ((K_4 ++ K_5) ++ (K_6 ++ (K_7 ++ K_8)))) ++ (((K_9 ++ K_10) ++ (K_11 ++ K_12)) ++ ((K_13 ++ K_14) ++ (K_15 ++ (K_16 ++ K_17)))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app c_0 c_1) (all_app c_2 c_3)) (all_app (all_app c_4 c_5) (all_app c_6 (all_app c_7 c_8)))) (all_app (all_app (all_app c_9 c_10) (all_app c_11 c_12)) (all_app (all_app c_13 c_14) (all_app c_15 (all_app c_16 c_17)))))

def wide0 : Nat := (24019198298973798 + 72057594037927936 * (219902325589 + 72057594037927936 * (56294995329024 + 72057594037927936 * (14411518804230144 + 72057594037927936 * (9607678632394752 + 72057594037927936 * (14411298905260066 + 72057594037927936 * (14355223812256563 + 72057594037927936 * (3355443 + 72057594037927936 * (858993459 + 72057594037927936 * (24019271313417728 + 72057594037927936 * (56294995350869 + 72057594037927936 * (14411518804230144 + 72057594037927936 * (14411517948592128 + 72057594037927936 * (9607532603506739 + 72057594037927936 * (14355223812252194 + 72057594037927936 * (3355443 + 72057594037927936 * (858993459 + 72057594037927936 * 219902325504)))))))))))))))))
def wide1 : Nat := (24019198585304951 + 72057594037927936 * (219902325589 + 72057594037927936 * (56294995329024 + 72057594037927936 * (14411518804230144 + 72057594037927936 * (14411517948592128 + 72057594037927936 * (14411298905260083 + 72057594037927936 * (14355223812256563 + 72057594037927936 * (3355443 + 72057594037927936 * (858993459 + 72057594037927936 * (24019344614192896 + 72057594037927936 * (56294995350869 + 72057594037927936 * (14411518804230144 + 72057594037927936 * (14411517948592128 + 72057594037927936 * (14411298905260083 + 72057594037927936 * (14355223812256563 + 72057594037927936 * (3355443 + 72057594037927936 * (858993459 + 72057594037927936 * 219902325504)))))))))))))))))
def wide2 : Nat := (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * 43690))))))))))))))))))
def wide3 : Nat := (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * (57646075230342348 + 72057594037927936 * 52428))))))))))))))))))
def wide4 : Nat := (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * (67818912035696880 + 72057594037927936 * 61680))))))))))))))))))
def wide5 : Nat := (280379743338240 + 72057594037927936 * (71777214294589695 + 72057594037927936 * (280379743338240 + 72057594037927936 * (71777214294589695 + 72057594037927936 * (280379743338240 + 72057594037927936 * (71777214294589695 + 72057594037927936 * (280379743338240 + 72057594037927936 * (71777214294589695 + 72057594037927936 * (280379743338240 + 72057594037927936 * (71777214294589695 + 72057594037927936 * (280379743338240 + 72057594037927936 * (71777214294589695 + 72057594037927936 * (280379743338240 + 72057594037927936 * (71777214294589695 + 72057594037927936 * (280379743338240 + 72057594037927936 * (71777214294589695 + 72057594037927936 * (280379743338240 + 72057594037927936 * (71777214294589695 + 72057594037927936 * 65280))))))))))))))))))
def wide6 : Nat := (71776123356119040 + 72057594037927936 * (1099494850815 + 72057594037927936 * (281470681808895 + 72057594037927936 * (72056494543077120 + 72057594037927936 * (71776123356119040 + 72057594037927936 * (1099494850815 + 72057594037927936 * (281470681808895 + 72057594037927936 * (72056494543077120 + 72057594037927936 * (71776123356119040 + 72057594037927936 * (1099494850815 + 72057594037927936 * (281470681808895 + 72057594037927936 * (72056494543077120 + 72057594037927936 * (71776123356119040 + 72057594037927936 * (1099494850815 + 72057594037927936 * (281470681808895 + 72057594037927936 * (72056494543077120 + 72057594037927936 * (71776123356119040 + 72057594037927936 * (1099494850815 + 72057594037927936 * 65535))))))))))))))))))
def wide7 : Nat := (72057589742960640 + 72057594037927936 * (72056494526300415 + 72057594037927936 * (71776119061282815 + 72057594037927936 * (16777215 + 72057594037927936 * (4294967295 + 72057594037927936 * (1099511627520 + 72057594037927936 * (281474976645120 + 72057594037927936 * (72057594021150720 + 72057594037927936 * (72057589742960640 + 72057594037927936 * (72056494526300415 + 72057594037927936 * (71776119061282815 + 72057594037927936 * (16777215 + 72057594037927936 * (4294967295 + 72057594037927936 * (1099511627520 + 72057594037927936 * (281474976645120 + 72057594037927936 * (72057594021150720 + 72057594037927936 * (72057589742960640 + 72057594037927936 * (72056494526300415 + 72057594037927936 * 65535))))))))))))))))))
def wide8 : Nat := (48038395452622984 + 72057594037927936 * (72057374135602346 + 72057594037927936 * (72001299042598911 + 72057594037927936 * (57646075233697791 + 72057594037927936 * (57646076089335807 + 72057594037927936 * (57646295132667852 + 72057594037927936 * (57702370225671372 + 72057594037927936 * (72057594034572492 + 72057594037927936 * (72057593178934476 + 72057594037927936 * (48038249423735039 + 72057594037927936 * (72001299042577066 + 72057594037927936 * (57646075233697791 + 72057594037927936 * (57646076089335807 + 72057594037927936 * (57646295132667852 + 72057594037927936 * (57702370225671372 + 72057594037927936 * (72057594034572492 + 72057594037927936 * (72057593178934476 + 72057594037927936 * (72057374135602431 + 72057594037927936 * 65535))))))))))))))))))
def wide9 : Nat := (72057593178934476 + 72057594037927936 * (72057374135602431 + 72057594037927936 * (72001299042598911 + 72057594037927936 * (57646075233697791 + 72057594037927936 * (57646076089335807 + 72057594037927936 * (57646295132667852 + 72057594037927936 * (57702370225671372 + 72057594037927936 * (72057594034572492 + 72057594037927936 * (72057593178934476 + 72057594037927936 * (72057374135602431 + 72057594037927936 * (72001299042598911 + 72057594037927936 * (57646075233697791 + 72057594037927936 * (57646076089335807 + 72057594037927936 * (57646295132667852 + 72057594037927936 * (57702370225671372 + 72057594037927936 * (72057594034572492 + 72057594037927936 * (72057593178934476 + 72057594037927936 * (72057374135602431 + 72057594037927936 * 65535))))))))))))))))))
def wide10 : Nat := (0 + 72057594037927936 * (72057594037927680 + 72057594037927936 * (65535 + 72057594037927936 * (72057594021150720 + 72057594037927936 * (4294967295 + 72057594037927936 * (72056494526300160 + 72057594037927936 * (281474976710655 + 72057594037927936 * (0 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (255 + 72057594037927936 * (72057594037862400 + 72057594037927936 * (16777215 + 72057594037927936 * (72057589742960640 + 72057594037927936 * (1099511627775 + 72057594037927936 * (71776119061217280 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (0 + 72057594037927936 * (72057594037927680 + 72057594037927936 * 65535))))))))))))))))))
def wide11 : Nat := (48038396025285290 + 72057594037927936 * (72057594037927850 + 72057594037927936 * (48038396025307135 + 72057594037927936 * (72057594032335530 + 72057594037927936 * (48038397456941055 + 72057594037927936 * (72057227534052010 + 72057594037927936 * (48132221017522175 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (48038396025285375 + 72057594037927936 * (72057594037906090 + 72057594037927936 * (48038396030877695 + 72057594037927936 * (72057592606272170 + 72057594037927936 * (48038762529161215 + 72057594037927936 * (71963769045691050 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (72057594037927850 + 72057594037927936 * 65535))))))))))))))))))
def wide12 : Nat := (0 + 72057594037927936 * (0 + 72057594037927936 * (72057594037862400 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (4294967295 + 72057594037927936 * (0 + 72057594037927936 * (71776119061217280 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (255 + 72057594037927936 * (0 + 72057594037927936 * (72057594021150720 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (1099511627775 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * 65535))))))))))))))))))
def wide13 : Nat := (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (72057594037906090 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (48038397456941055 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (71963769045691050 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (48038396025285375 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (72057594032335530 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (48038762529161215 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (48038396025285290 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * 65535))))))))))))))))))
def wide14 : Nat := (0 + 72057594037927936 * (72057594037927680 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (4294967295 + 72057594037927936 * (72056494526300160 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (255 + 72057594037927936 * (72057594037862400 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (1099511627775 + 72057594037927936 * (71776119061217280 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * 65535))))))))))))))))))
def wide15 : Nat := (48038396025285290 + 72057594037927936 * (72057594037927850 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (48038397456941055 + 72057594037927936 * (72057227534052010 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (48038396025285375 + 72057594037927936 * (72057594037906090 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (48038762529161215 + 72057594037927936 * (71963769045691050 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * 65535))))))))))))))))))
def wide16 : Nat := (72057593751596782 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (67253754721730559 + 72057594037927936 * (72057594037927918 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057520737152767 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (67253827736174591 + 72057594037927936 * (72057594037923566 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * 65535))))))))))))))))))
def wide17 : Nat := (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (72057589742960640 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (255 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (72056494526300160 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * 65535))))))))))))))))))
def wide18 : Nat := (48038396025285290 + 72057594037927936 * (72057594037927850 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (48038396025285375 + 72057594037927936 * (72057594037906090 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * 65535))))))))))))))))))
def wide19 : Nat := (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (0 + 72057594037927936 * (72057594037927680 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * (72057594037927935 + 72057594037927936 * 65535))))))))))))))))))
def FMask : Nat := (2 ^ 1024 - 1)
def expected : Nat := wide0
def clip (w : Nat) := actL points w
def smaller (ws : List Nat) := ws.map clip

theorem maskClip : actL points FMask = M_ := by decide +kernel
theorem pchecks : prsOK M_ Y_ PD_ PM_ = true := by decide +kernel
theorem gchecks : symOK M_ Y_ G_ = true := by decide +kernel

theorem transfer {t z ws} (h : NatRun FMask z t ws) (hz : clip z = Y_) :
    NatRun M_ Y_ t (smaller ws) := by
  have hr := Run.map (actL points) (inv' := (· ^^^ M_)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, maskClip]) (fun a b => actL_and points a b)
    (fun a b => actL_or points a b) h
  change actL points z = Y_ at hz
  rwa [hz] at hr

theorem losing {t ws} (h : NatRun M_ Y_ t ws) : T_cert.mem (t :: isort ws) = false :=
  closure_sound T_cert pchecks gchecks hT_cert t ws h

noncomputable def possible (t : Nat) (tag : Nat) (h : List (Nat × Nat)) (ws : List Nat) : Bool :=
  let z := smaller ws
  via Y_ PD_ PM_ t z && ucheck M_ Y_ t z ((h.lookup tag).getD 0) &&
    !T_cert.mem (t :: isort z) && !hfind G_ T_cert t h tag z

theorem possible_of {t z ws} (h : NatRun FMask z t ws) (hz : clip z = Y_)
    (k : Nat) (hints : List (Nat × Nat)) : possible t k hints ws = true := by
  have hp := transfer h hz
  simp [possible, via_sound pchecks hp, ucheck_sound hp, losing hp,
    hfind_false gchecks T_cert t (fun _ hw => losing hw) hints k hp]

noncomputable def fullStep (W : BT) : List Nat → List (Nat × Nat) → Bool
  | [], _ => false
  | 0 :: ws, _ => leqL ws [expected]
  | (t + 1) :: ws, h => !(next FMask (t+2-ws.length) ws
      (fun tag ys => possible t tag h ys && !W.mem (t :: isort ys)))
noncomputable def WK_0 : List (List ℕ × List (ℕ × ℕ)) := [([0,wide0],[]),([1,wide1,wide16],[]),([2,wide1,wide9,wide15],[]),([2,wide8,wide16],[]),([3,wide8,wide9,wide15],(decodeHints [18553])),([3,wide9,wide16,wide18],(decodeHints [21625])),([4,wide9,wide15,wide16,wide17],(decodeHints [19584,21632,29817])),([4,wide9,wide15,wide18],(decodeHints [128,519,1152,1664,2176,2688,21120,21888])),([5,wide3,wide7,wide15,wide18],(decodeHints [166,717,1190,1702,2214,2726,3238,3750,14758,15053,19149,21158,26315,27302,29350,30118])),([5,wide9,wide15,wide17],(decodeHints [277,789,1408,1920,2432,2944,19221,20352,21376,22400])),([6,wide2,wide9,wide14,wide17],(decodeHints [392,904,1341,1853,2365,2877,3389,3901,15320,16267,19336,20285,21309,22333,25480,26456,27453,28477,29501,30525])),([6,wide3,wide7,wide15,wide17],(decodeHints [461,973,1446,1958,2470,2982,3494,4006,15128,16294,19405,20429,21414,22438,25549,26534,27558,28582,29606,30630])),([6,wide9,wide10,wide13,wide17],(decodeHints [472,984,1411,1536,1923,2435,2947,3459,3971,15146,16259,19416,20363,20736,21379,22403,25560,26499,26880,27523,28547,29571,30595])),([6,wide9,wide11,wide12,wide17],(decodeHints [0,277,512,789,1024,1408,1536,1920,2048,2432,2944,3072,3456,3584,3968,15323,16269,19221,20352,20736,21376,22400,24832,25365,26112,26496,27136,27520,28544,29184,29568,30592])),([7,wide2,wide3,wide7,wide14,wide17],(decodeHints [436,948,1346,1858,2370,2882,3394,3906,4418,4930,15312,16194,19380,20404,21314,22338,25524,26434,27458,28482,29506,30530,33716,34650,35650,36674,37698,38722,39746,40770])),([7,wide2,wide9,wide10,wide12,wide17],(decodeHints [392,904,1341,1853,2365,2560,2877,3389,3901,4413,4925,15320,16267,18944,19336,20285,21309,22333,24832,25480,26429,27453,28477,28928,29501,30525,33672,34648,35645,36669,37120,37693,38717,39424,39741,40765])),([7,wide3,wide7,wide10,wide13,wide17],(decodeHints [462,974,1451,1963,2475,2560,2987,3499,4011,4523,5035,15321,16299,19406,20395,20992,21419,22443,25550,26548,27563,28587,28928,29611,30635,33742,34731,35755,36779,37120,37803,38827,39851,40875])),([7,wide3,wide7,wide11,wide12,wide17],(decodeHints [0,461,512,973,1024,1446,1536,1958,2048,2470,2560,2982,3072,3494,4006,4096,4518,4608,5030,14592,14848,15128,16294,19405,20407,21414,22438,25549,26534,26880,27558,28582,28928,29606,30630,33024,33741,34304,34726,35072,35328,35750,36774,37376,37798,38822,39424,39846,40870])),([8,wide2,wide3,wide7,wide10,wide12,wide17],(decodeHints [436,948,1346,1858,2370,2882,3394,3584,3906,4418,4930,5442,5954,15312,16194,19380,20404,21314,22338,25088,25524,26434,27458,28482,29184,29506,30530,33024,33716,34626,35650,36674,37120,37698,38722,39168,39746,40770,43956,44890,45890,46914,47938,48962,49408,49986,51010,51712,52034,53058]))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def Winning_ : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt WK_0 0) BT.lf) (keyAt WK_0 1) BT.lf) (keyAt WK_0 2) (BT.nd BT.lf (keyAt WK_0 3) BT.lf)) (keyAt WK_0 4) (BT.nd (BT.nd (BT.nd BT.lf (keyAt WK_0 5) BT.lf) (keyAt WK_0 6) BT.lf) (keyAt WK_0 7) (BT.nd BT.lf (keyAt WK_0 8) BT.lf))) (keyAt WK_0 9) (BT.nd (BT.nd (BT.nd (BT.nd BT.lf (keyAt WK_0 10) BT.lf) (keyAt WK_0 11) BT.lf) (keyAt WK_0 12) (BT.nd BT.lf (keyAt WK_0 13) BT.lf)) (keyAt WK_0 14) (BT.nd (BT.nd (BT.nd BT.lf (keyAt WK_0 15) BT.lf) (keyAt WK_0 16) BT.lf) (keyAt WK_0 17) (BT.nd BT.lf (keyAt WK_0 18) BT.lf))))


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wcheck_0 : WK_0.all (fun kh => fullStep Winning_ kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hWKeys : Winning_.toList = (WK_0).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hWinning : ∀ x, Winning_.mem x = true → ∃ h, (fullStep Winning_) x h = true :=
  cover (p := fullStep Winning_) Winning_ _ hWKeys wcheck_0

theorem forced {z : Nat} (hz : clip z = Y_) :
    ∀ t ws, NatRun FMask z t ws → Winning_.mem (t :: isort ws) = true → z = expected := by
  intro t
  induction t with
  | zero =>
    intro ws hr hm
    obtain ⟨h,hh⟩ := hWinning _ hm
    have he : isort ws = [expected] := leqL_eq _ _ hh
    have hr' : NatRun FMask z 0 (isort ws) := Run.perm (List.perm_insertionSort _ _).symm hr
    have id := zero_done hr' rfl
    rw [he] at id
    simpa using id.symm
  | succ t ih =>
    intro ws hr hm
    by_contra hneq
    obtain ⟨h,hs⟩ := hWinning _ hm
    simp only [fullStep, Bool.not_eq_true'] at hs
    have hr' : NatRun FMask z (t+1) (isort ws) := Run.perm (List.perm_insertionSort _ _).symm hr
    have hn := next_complete hr' t rfl (isort ws) (List.Perm.refl _)
      (fun tag ys => possible t tag h ys && !Winning_.mem (t :: isort ys))
      (fun tag ys hy => by
        have hnmem : Winning_.mem (t :: isort ys) = false := by
          cases hval : Winning_.mem (t :: isort ys)
          · rfl
          · exact (hneq (ih ys hy hval)).elim
        simp [possible_of hy hz tag h, hnmem])
    rw [hn] at hs
    cases hs

def fullPoints := List.range 1024
def rawFull : List Nat := (List.ofFn fun (i : Fin 10) (x : Fin 10 → Bool) => x i).map
  (fun a => encL a fullPoints)
def rootHints : List (List Nat × Nat) := [([31, 992, 1015808, 1082401, 8659208, 17318416], 3), ([31, 992, 1082401, 8659208, 17318416, 32505856], 7), ([31, 992, 1082401, 4329604, 8659208, 17318416], 0), ([31, 992, 31744, 1082401, 8659208, 17318416, 32505856], 1), ([31, 992, 31744, 1082401, 4329604, 8659208, 17318416], 0), ([31, 992, 1015808, 1082401, 8659208, 17318416, 32505856], 5), ([31, 992, 1015808, 1082401, 2164802, 4329604, 8659208], 3), ([31, 992, 1015808, 1082401, 2164802, 4329604, 17318416], 3), ([31, 992, 1015808, 1082401, 2164802, 8659208, 17318416], 3), ([31, 992, 1015808, 1082401, 4329604, 8659208, 17318416], 4), ([31, 992, 1015808, 2164802, 4329604, 8659208, 17318416], 3), ([31, 992, 1082401, 2164802, 4329604, 8659208, 32505856], 7), ([31, 992, 1082401, 2164802, 4329604, 17318416, 32505856], 7), ([31, 992, 1082401, 2164802, 8659208, 17318416, 32505856], 7), ([31, 992, 1082401, 4329604, 8659208, 17318416, 32505856], 8), ([31, 992, 2164802, 4329604, 8659208, 17318416, 32505856], 7), ([31, 992, 31744, 1015808, 1082401, 8659208, 17318416, 32505856], 170017), ([31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208], 122497), ([31, 992, 31744, 1015808, 1082401, 2164802, 4329604, 17318416], 122497), ([31, 992, 31744, 1015808, 1082401, 2164802, 8659208, 17318416], 122497), ([31, 992, 31744, 1015808, 1082401, 4329604, 8659208, 17318416], 122497), ([31, 992, 31744, 1015808, 2164802, 4329604, 8659208, 17318416], 122497), ([31, 992, 31744, 1082401, 2164802, 4329604, 8659208, 32505856], 117217), ([31, 992, 31744, 1082401, 2164802, 4329604, 17318416, 32505856], 117217), ([31, 992, 31744, 1082401, 2164802, 8659208, 17318416, 32505856], 117217), ([31, 992, 31744, 1082401, 4329604, 8659208, 17318416, 32505856], 117217), ([31, 992, 31744, 2164802, 4329604, 8659208, 17318416, 32505856], 117217), ([31, 992, 31744, 1082401, 2164802, 4329604, 8659208, 17318416], 117217), ([31, 992, 1015808, 1082401, 2164802, 4329604, 8659208, 32505856], 111937), ([31, 992, 1015808, 1082401, 2164802, 4329604, 17318416, 32505856], 111937), ([31, 992, 1015808, 1082401, 2164802, 8659208, 17318416, 32505856], 111937), ([31, 992, 1015808, 1082401, 4329604, 8659208, 17318416, 32505856], 111937), ([31, 992, 1015808, 2164802, 4329604, 8659208, 17318416, 32505856], 111937), ([31, 992, 1015808, 1082401, 2164802, 4329604, 8659208, 17318416], 111937), ([31, 992, 1082401, 2164802, 4329604, 8659208, 17318416, 32505856], 111937), ([31, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32505856], 39073), ([31, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32505856], 39073), ([31, 31744, 1015808, 1082401, 2164802, 8659208, 17318416, 32505856], 39073), ([31, 31744, 1015808, 1082401, 4329604, 8659208, 17318416, 32505856], 39073), ([31, 31744, 1015808, 2164802, 4329604, 8659208, 17318416, 32505856], 39073), ([992, 31744, 1015808, 1082401, 2164802, 4329604, 8659208, 32505856], 163879), ([992, 31744, 1015808, 1082401, 2164802, 4329604, 17318416, 32505856], 163879), ([992, 31744, 1015808, 1082401, 2164802, 8659208, 17318416, 32505856], 163879), ([992, 31744, 1015808, 1082401, 4329604, 8659208, 17318416, 32505856], 163879), ([992, 31744, 1015808, 2164802, 4329604, 8659208, 17318416, 32505856], 163879)]
def rootInfo (ws : List Nat) := [(0, (rootHints.lookup (isort (smaller ws))).getD 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawFullEq : rawFull = [wide2, wide3, wide4, wide5, wide6, wide7, wide10, wide12, wide17, wide19] := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem roots : rawFull.sublists.all
    (fun zs => !possible 8 0 (rootInfo zs) zs || Winning_.mem (8 :: isort zs)) = true := by
  rw [rawFullEq]
  decide +kernel

theorem indexBit (f : BFn 10) (i : Nat) (hi : i < 1024) :
    (encL f fullPoints).testBit i = f (pt 10 i) := by
  rw [encL_testBit, List.getD_eq_getElem _ _ (by simp [fullPoints,hi])]
  simp [fullPoints]

theorem clip_full (f : BFn 10) (l : List Nat) (small : ∀ j ∈ l, j < 1024) :
    actL l (encL f fullPoints) = encL f l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [actL, encL]
    rw [indexBit f a (small a (by simp)), ih (fun j hj => small j (by simp [hj]))]

theorem pointBound : ∀ j ∈ points, j < 1024 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem referenceFull : encL reference fullPoints = expected := by decide +kernel
def address (x : Fin 10 → Bool) : Nat := (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) + (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) + (if x 6 then 64 else 0) + (if x 7 then 128 else 0) + (if x 8 then 256 else 0) + (if x 9 then 512 else 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem addressOK : ∀ x : Fin 10 → Bool, address x < 1024 ∧ pt 10 (address x) = x := by decide +kernel
theorem allPoints (x : Fin 10 → Bool) : ∃ i : Fin 1024, pt 10 i.val = x :=
  ⟨⟨address x, (addressOK x).1⟩, (addressOK x).2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem uniqueCircuit (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 8)
    (hr : ∀ i j : Fin 5, C.eval (pairInput i j) =
      (7577150 : ℕ).testBit (5 * i.val + j.val)) :
    ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = reference x := by
  let f : BFn 10 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 5 × Fin 5) : f (pt 10 (pairCode p)) = reference (pt 10 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 10 (pairCode (i,j)))) = _
    rw [codeInputs, graphRow]
    exact hr i j
  have encode : encL f points = Y_ := by
    calc
      encL f points = encL reference points := by
        apply enc_congr_rows
        intro v hv
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hv
        exact he p
      _ = Y_ := by decide +kernel
  have hn : ∃ x y : Fin 10 → Bool, f x ≠ f y := by
    refine ⟨pt 10 (pairCode (0,0)),pt 10 (pairCode (0,1)),?_⟩
    rw [he (0,0),he (0,1)]
    decide +kernel
  have hz : clip (encL f fullPoints) = Y_ := (clip_full f points pointBound).trans encode
  obtain ⟨s,hs',ws,hsub,hrun⟩ := exists_run f hn 8 ⟨C,hf,hs,fun _ => rfl⟩
  have hfull : NatRun FMask (encL f fullPoints) s (ws.map (fun a => encL a fullPoints)) :=
    Run.map (fun a : BFn 10 => encL a fullPoints)
      (fun a => by rw [show FMask = 2 ^ fullPoints.length - 1 by decide +kernel]; exact encL_inv a fullPoints)
      (fun a b => encL_and a b fullPoints) (fun a b => encL_or a b fullPoints) hrun
  have hsub' : (ws.map (fun a => encL a fullPoints)).Sublist rawFull := hsub.map _
  have hforce : encL f fullPoints = expected := by
    cases hw : ws.map (fun a => encL a fullPoints) with
    | nil => rw [hw] at hfull; exact (run_nil hfull).elim
    | cons a as =>
      rw [hw] at hfull hsub'
      have h9 := extend_run hfull hs'
      have hroot := List.all_eq_true.mp roots _ (List.mem_sublists.2 hsub')
      have vp := possible_of h9 hz 0 (rootInfo (a::as))
      change (!possible 8 0 (rootInfo (a::as)) (a::as) || Winning_.mem (8 :: isort (a::as))) = true at hroot
      rw [vp] at hroot
      exact forced hz 8 _ h9 (by simpa using hroot)
  rw [← referenceFull] at hforce
  intro x
  obtain ⟨i,rfl⟩ := allPoints x
  have bit := congrArg (fun w : Nat => w.testBit i.val) hforce
  change (encL f fullPoints).testBit i.val = (encL reference fullPoints).testBit i.val at bit
  rw [indexBit f _ i.isLt,indexBit reference _ i.isLt] at bit
  exact bit

end PEqualNP.Outside.L_meta_19367.Functional

open PEqualNP.Outside.L_meta_19367.Functional in
theorem PEqualNP.Outside.L_meta_19367 (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 8)
    (hr : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577150 : ℕ).testBit (5 * u.val + v.val)) C) :
    ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = reference x :=
  uniqueCircuit C hf hs hr
