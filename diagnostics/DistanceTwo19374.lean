import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19374.Robust

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
namespace Slice0
def probeRoots : List (List Nat × Nat) := [([15,496,3584,8225,61440,70160,148546],474343),([15,496,3584,35080,61440,70160,262276],235059),([15,496,3584,8225,70160,148546,458752],474343),([15,496,3584,35080,70160,262276,458752],235059),([15,496,3584,8225,70160,148546,262276],474375),([15,496,3584,8225,35080,70160,148546],477415),([15,496,3584,8225,35080,70160,262276],235987),([15,496,3584,35080,70160,148546,262276],234931),([15,496,3584,8225,35080,148546,262276],248230),([15,496,8225,61440,70160,148546,458752],474343),([15,496,35080,61440,70160,262276,458752],235059),([15,3584,8225,61440,70160,148546,458752],563443),([15,3584,35080,61440,70160,262276,458752],562419),([496,3584,8225,61440,70160,148546,458752],474343),([496,3584,35080,61440,70160,262276,458752],235059)]
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
  (x 1 || x 5 || x 0 || x 6 || x 7) && !((x 1 || x 5 || x 2) && (x 0 || x 6 || x 7))
def pairInput (i j : Fin 5) := PEqualNP.Represents.oneEach i j
theorem codeInputs : ∀ p : Fin 5 × Fin 5, List.ofFn (pt 10 (pairCode p)) = pairInput p.1 p.2 := by decide +kernel
theorem graphRow : ∀ i j : Fin 5, reference (pt 10 (pairCode (i,j))) =
   (7571262 : ℕ).testBit (5 * i.val + j.val) := by decide +kernel
def samplePairs : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 2), (2, 4), (3, 0), (3, 1), (3, 2), (3, 4), (4, 0), (4, 2), (4, 3)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) = (7571262 : ℕ).testBit (5 * p.1.val + p.2.val)
def M_ : ℕ := 524287

def Y_ : ℕ := 226207

def XS_ : List ℕ := [15, 496, 3584, 61440, 458752, 70160, 8225, 148546, 262276, 35080]

def PD_ : List (ℕ × ℕ) := [(1, 182864), (2, 110456), (3, 7660), (4, 17574), (5, 10243), (6, 7761), (7, 1400), (8, 236), (9, 550), (10, 323), (11, 241), (12, 40), (13, 4), (14, 18), (15, 9), (16, 4), (17, 2), (18, 1)]

def PM_ : List (ℕ × ℕ) := [(5, 226207), (6, 226207), (10, 226207), (11, 226207), (15, 226207), (18, 226207)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,496,70175,298892] BT.lf) [4,3584,70640,156783] BT.lf) [5,15,496,70160,298892] (BT.nd (BT.nd BT.lf [5,15,3584,70640,156771] BT.lf) [5,496,3584,70160,156783] BT.lf)) [5,496,3584,70175,156771] (BT.nd (BT.nd (BT.nd BT.lf [5,496,3584,70175,297356] BT.lf) [5,496,35080,70175,265860] BT.lf) [5,496,36616,70175,262276] (BT.nd (BT.nd BT.lf [5,3584,8225,70640,148559] BT.lf) [5,3584,8239,70640,148546] BT.lf))) [6,15,496,3584,70160,156771] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,496,3584,70160,297356] BT.lf) [6,15,496,35080,70160,265860] BT.lf) [6,15,496,36616,70160,262276] (BT.nd (BT.nd BT.lf [6,15,3584,8225,70640,148546] BT.lf) [6,496,3584,8225,70160,148559] BT.lf)) [6,496,3584,8225,70175,148546] (BT.nd (BT.nd (BT.nd BT.lf [6,496,3584,8239,70160,148546] BT.lf) [6,496,3584,35080,70175,262276] BT.lf) [7,15,496,3584,8225,70160,148546] (BT.nd BT.lf [7,15,496,3584,35080,70160,262276] BT.lf))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([4,496,70175,298892],[(0,234923),(2,431339),(4,234923),(6,234923),(8,234923),(10,436454),(57,234923),(82,234923)]),([4,3584,70640,156783],[(0,15494),(2,15494),(4,15494),(6,5264),(8,15494),(10,136208),(57,15494),(74,15494),(77,11398)]),([5,15,496,70160,298892],[(0,234923),(2,234923),(4,234923),(6,431339),(8,234923),(10,234923),(12,234923),(14,436454),(57,234923),(58,234923),(73,234923),(74,234923),(81,234923),(98,234923),(101,234507),(114,234923)]),([5,15,3584,70640,156771],[(0,441478),(2,441478),(4,441478),(6,441478),(8,441478),(10,431248),(12,441478),(14,136624),(57,441478),(58,441478),(73,441478),(74,441478),(81,441478),(97,146438),(98,441478),(106,441478),(109,437382)]),([5,496,3584,70160,156783],[(0,15590),(2,5360),(4,15590),(6,15590),(8,15590),(10,15590),(12,15590),(14,234512),(57,15590),(58,15590),(73,15590),(74,15494),(81,15590),(106,15590),(109,11494),(113,244742),(114,15590)]),([5,496,3584,70175,156771],[(0,441574),(2,431344),(4,441574),(6,441574),(8,441574),(10,441574),(12,441574),(14,234928),(57,441574),(58,441574),(73,441574),(74,441478),(81,441574),(106,441574),(109,437478),(113,244742),(114,441574)]),([5,496,3584,70175,297356],[(0,234928),(2,431344),(4,234928),(6,234928),(8,234928),(10,234928),(12,234928),(14,441574),(57,234928),(58,234928),(73,234928),(81,234928),(105,241062),(106,234928),(114,234928)]),([5,496,35080,70175,265860],[(0,234923),(2,431339),(4,234923),(6,441606),(8,234923),(10,234923),(12,234923),(14,436454),(73,234923),(81,234923),(105,267696),(106,234923),(114,234923)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([5,496,36616,70175,262276],[(0,234931),(2,431347),(4,234931),(6,436486),(8,234931),(10,234931),(12,234931),(14,444646),(73,234931),(81,234931),(105,267691),(106,234931),(114,234931)]),([5,3584,8225,70640,148559],[(0,48263),(2,48263),(4,48263),(6,136624),(8,48263),(10,39056),(12,48263),(14,137264),(57,48263),(58,48263),(73,48263),(98,48263),(101,44167),(105,441478),(106,48263)]),([5,3584,8239,70640,148546],[(0,474247),(2,474247),(4,474247),(6,136208),(8,474247),(10,5264),(12,474247),(14,137680),(57,474247),(58,474247),(73,474247),(98,474247),(101,470151),(105,15494),(106,474247)]),([6,15,496,3584,70160,156771],[(0,441574),(2,441574),(4,441574),(6,431344),(8,441574),(10,441574),(12,441574),(14,441574),(16,441574),(18,234928),(57,441574),(58,441574),(73,441574),(74,441574),(81,441574),(82,441574),(97,441574),(98,441574),(105,441574),(106,441478),(113,441574),(129,244742),(130,441574),(146,441574),(149,437478),(153,245158),(154,441574)]),([6,15,496,3584,70160,297356],[(0,234928),(2,234928),(4,234928),(6,431344),(8,234928),(10,234928),(12,234928),(14,234928),(16,234928),(18,441574),(57,234928),(58,234928),(73,234928),(74,234928),(81,234928),(82,234928),(97,234928),(98,234928),(105,234928),(113,234928),(130,234928),(133,234512),(145,241062),(146,234928),(153,245158),(154,234928)]),([6,15,496,35080,70160,265860],[(0,234923),(2,234923),(4,234923),(6,431339),(8,234923),(10,441606),(12,234923),(14,234923),(16,234923),(18,436454),(57,234923),(58,234923),(74,234923),(97,234923),(98,234923),(105,234923),(113,234923),(114,234923),(130,234923),(145,267696),(146,234923),(154,234923)]),([6,15,496,36616,70160,262276],[(0,234931),(2,234931),(4,234931),(6,431347),(8,234931),(10,436486),(12,234931),(14,234931),(16,234931),(18,444646),(57,234931),(58,234931),(74,234931),(97,234931),(98,234931),(105,234931),(113,234931),(130,234931),(145,267691),(146,234931),(153,267691),(154,234931)]),([6,15,3584,8225,70640,148546],[(0,474247),(2,474247),(4,474247),(6,474247),(8,474247),(10,136624),(12,474247),(14,431248),(16,474247),(18,137680),(57,474247),(58,474247),(73,474247),(74,474247),(81,474247),(82,474247),(97,474247),(98,474247),(105,474247),(129,146471),(130,474247),(138,474247),(141,470151),(145,441478),(146,474247)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([6,496,3584,8225,70160,148559],[(0,48359),(2,39152),(4,48359),(6,48359),(8,48359),(10,234928),(12,48359),(14,48359),(16,48359),(18,235568),(57,48359),(58,48359),(81,48359),(82,48359),(97,48359),(98,48263),(105,48359),(113,48359),(114,48359),(138,48359),(141,44263),(145,441574),(146,48359),(153,441574),(154,48359)]),([6,496,3584,8225,70175,148546],[(0,474343),(2,431344),(4,474343),(6,474343),(8,474343),(10,234928),(12,474343),(14,474343),(16,474343),(18,235984),(57,474343),(58,474343),(81,474343),(82,474343),(97,474343),(98,474247),(105,474343),(113,474343),(114,474343),(138,474343),(141,470247),(145,441574),(146,474343),(153,441574),(154,474343)]),([6,496,3584,8239,70160,148546],[(0,474343),(2,5360),(4,474343),(6,474343),(8,474343),(10,234512),(12,474343),(14,474343),(16,474343),(18,235984),(57,474343),(58,474343),(81,474343),(82,474343),(97,474343),(98,474247),(105,474343),(113,474343),(114,474343),(138,474343),(141,470247),(145,15590),(146,474343),(153,15590),(154,474343)]),([6,496,3584,35080,70175,262276],[(0,234931),(2,431347),(4,234931),(6,234931),(8,234931),(10,441606),(12,234931),(14,234931),(16,234931),(18,444646),(57,234931),(58,234931),(81,234931),(82,234931),(97,234931),(105,234931),(113,234931),(137,267696),(138,234931),(145,267696),(146,234931),(154,234931)]),([7,15,496,3584,8225,70160,148546],[(0,474343),(2,474343),(4,474343),(6,431344),(8,474343),(10,474343),(12,474343),(14,234928),(16,474343),(18,474343),(20,474343),(22,235984),(57,474343),(58,474343),(73,474343),(74,474343),(81,474343),(82,474343),(97,474343),(98,474343),(113,474343),(114,474343),(129,474343),(130,474343),(137,474343),(138,474247),(145,474343),(153,474343),(154,474343),(169,441574),(170,474343),(186,474343),(189,470247),(193,441574),(194,474343),(201,441574),(202,474343)]),([7,15,496,3584,35080,70160,262276],[(0,234931),(2,234931),(4,234931),(6,431347),(8,234931),(10,234931),(12,234931),(14,441606),(16,234931),(18,234931),(20,234931),(22,444646),(57,234931),(58,234931),(73,234931),(74,234931),(81,234931),(82,234931),(98,234931),(113,234931),(114,234931),(129,234931),(130,234931),(137,234931),(145,234931),(153,234931),(154,234931),(170,234931),(185,267696),(186,234931),(193,267696),(194,234931),(201,267696),(202,234931)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((K_0 ++ (K_1 ++ K_2))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app c_0 (all_app c_1 c_2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coreLower (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 7) (hr : Matches C) : False := by
  let f : BFn 10 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 5 × Fin 5) (hp : p ∈ samplePairs) : f (pt 10 (pairCode p)) = reference (pt 10 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 10 (pairCode (i,j)))) = _
    rw [codeInputs, graphRow]
    exact hr (i,j) hp
  have encode : encL f points = Y_ := by
    calc
      encL f points = encL reference points := by
        apply enc_congr_rows
        intro v hv
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
        exact he p hp
      _ = Y_ := by decide +kernel
  have nc : ∃ x y : Fin 10 → Bool, f x ≠ f y := by
    refine ⟨pt 10 (pairCode (1, 1)),pt 10 (pairCode (0, 1)),?_⟩
    rw [he (1, 1) (by decide +kernel),he (0, 1) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 7 8 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 7 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end Slice0

namespace Slice1
def probeRoots : List (List Nat × Nat) := [([7,56,1984,30720,34889,69760,131346],575653),([7,56,1984,30720,34889,69760,270884],168499),([7,56,1984,17408,30720,34889,270884],168334),([7,56,1984,34889,69760,131346,491520],575653),([7,56,1984,34889,69760,270884,491520],168499),([7,56,1984,17408,34889,270884,491520],168334),([7,56,1984,34889,69760,131346,270884],177701),([7,56,1984,17408,34889,69760,131346],570533),([7,56,1984,17408,34889,69760,270884],168494),([7,56,1984,17408,34889,131346,270884],177701),([7,56,1984,17408,69760,131346,270884],65738),([7,56,30720,34889,69760,131346,491520],575653),([7,56,30720,34889,69760,270884,491520],168499),([7,56,17408,30720,34889,270884,491520],168334),([7,1984,30720,34889,69760,131346,491520],561331),([7,1984,30720,34889,69760,270884,491520],561331),([7,1984,17408,30720,34889,270884,491520],528563),([56,1984,30720,34889,69760,131346,491520],491603),([56,1984,30720,34889,69760,270884,491520],491603),([56,1984,17408,30720,34889,270884,491520],491603)]
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
  (x 1 || x 5 || x 0 || x 6 || x 7) && !((x 1 || x 5 || x 2) && (x 0 || x 6 || x 7))
def pairInput (i j : Fin 5) := PEqualNP.Represents.oneEach i j
theorem codeInputs : ∀ p : Fin 5 × Fin 5, List.ofFn (pt 10 (pairCode p)) = pairInput p.1 p.2 := by decide +kernel
theorem graphRow : ∀ i j : Fin 5, reference (pt 10 (pairCode (i,j))) =
   (7571262 : ℕ).testBit (5 * i.val + j.val) := by decide +kernel
def samplePairs : List (Fin 5 × Fin 5) := [(0, 0), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) = (7571262 : ℕ).testBit (5 * p.1.val + p.2.val)
def M_ : ℕ := 524287

def Y_ : ℕ := 235630

def XS_ : List ℕ := [7, 56, 1984, 30720, 491520, 34889, 69760, 131346, 270884, 17408]

def PD_ : List (ℕ × ℕ) := [(1, 152665), (2, 97909), (3, 60259), (4, 8680), (5, 1197), (6, 5647), (7, 3934), (8, 1014), (9, 418), (10, 136), (11, 29), (12, 87), (13, 50), (15, 9), (16, 5), (17, 3)]

def PM_ : List (ℕ × ℕ) := [(0, 235630), (4, 235630), (7, 235630), (8, 235630), (9, 235630), (10, 235630), (13, 235630), (14, 235630), (18, 235630)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1984,34937,201111] BT.lf) [5,7,56,34889,288740] BT.lf) [5,7,1984,34937,201106] (BT.nd BT.lf [5,56,1984,34889,201111] BT.lf)) [5,1984,34889,69816,131351] (BT.nd (BT.nd (BT.nd BT.lf [5,1984,34937,69760,131351] BT.lf) [5,1984,34937,69767,131346] BT.lf) [6,7,56,1984,34889,201106] (BT.nd BT.lf [6,7,56,1984,34889,288292] BT.lf))) [6,7,56,17408,34889,272356] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,56,18368,34889,270884] BT.lf) [6,7,1984,17464,34889,270884] BT.lf) [6,7,1984,34889,69816,131346] (BT.nd BT.lf [6,7,1984,34937,69760,131346] BT.lf)) [6,56,1984,34889,69760,131351] (BT.nd (BT.nd BT.lf [6,56,1984,34889,69767,131346] BT.lf) [7,7,56,1984,17408,34889,270884] (BT.nd BT.lf [7,7,56,1984,34889,69760,131346] BT.lf))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([4,1984,34937,201111],[(0,46177),(2,46177),(4,46177),(6,32878),(8,46177),(10,98350),(57,46177),(74,46177),(77,42081)]),([5,7,56,34889,288740],[(0,168328),(2,360520),(4,168328),(6,397480),(8,168328),(10,32869),(12,168328),(14,400549),(57,168328),(58,168328),(81,168328),(98,168328),(114,168328)]),([5,7,1984,34937,201106],[(0,406629),(2,98382),(4,406629),(6,406629),(8,406629),(10,65646),(12,406629),(14,102798),(57,406629),(58,406629),(81,406629),(97,78945),(98,406629),(106,406629),(109,402533)]),([5,56,1984,34889,201111],[(0,46245),(2,37038),(4,46245),(6,46245),(8,46245),(10,32970),(12,46245),(14,167982),(57,46245),(58,46245),(73,46177),(74,46181),(81,46245),(106,46245),(109,42149)]),([5,1984,34889,69816,131351],[(0,46245),(2,46245),(4,46245),(6,32970),(8,46245),(10,37038),(12,46245),(14,167982),(57,46245),(74,46245),(81,46181),(82,46177),(98,46245)]),([5,1984,34937,69760,131351],[(0,46177),(2,46177),(4,46177),(6,32878),(8,46177),(10,46177),(12,46177),(14,98350),(57,46177),(74,46177),(81,46177),(82,46177),(98,46177),(113,111649),(114,46177)]),([5,1984,34937,69767,131346],[(0,570469),(2,570469),(4,570469),(6,65646),(8,570469),(10,98382),(12,570469),(14,102958),(57,570469),(74,570469),(98,570469),(113,78945),(114,570469)]),([6,7,56,1984,34889,201106],[(0,406693),(2,360526),(4,406693),(6,397486),(8,406693),(10,406693),(12,406693),(14,65738),(16,406693),(18,168334),(57,406693),(58,406693),(73,406693),(74,406693),(81,406693),(82,406693),(105,406693),(106,406629),(113,406693),(129,79201),(130,406693),(146,406693),(149,402597),(153,205889),(154,406693)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,56,1984,34889,288292],[(0,168334),(2,360526),(4,168334),(6,397486),(8,168334),(10,168334),(12,168334),(14,32869),(16,168334),(18,406693),(57,168334),(58,168334),(73,168334),(74,168334),(81,168334),(82,168334),(105,168334),(113,168334),(130,168334),(145,102433),(146,168334),(153,102433),(154,168334)]),([6,7,56,17408,34889,272356],[(0,168328),(2,360520),(4,168328),(6,397480),(8,168328),(10,168328),(12,168328),(14,32869),(16,168328),(18,400549),(57,168328),(58,168328),(73,168328),(74,168328),(81,168328),(82,168328),(105,168328),(113,168328),(114,168328),(130,168328),(145,102433),(146,168328),(154,168328)]),([6,7,56,18368,34889,270884],[(0,168334),(2,360526),(4,168334),(6,397486),(8,168334),(10,168334),(12,168334),(14,32869),(16,168334),(18,406693),(57,168334),(58,168334),(73,168334),(74,168334),(81,168334),(82,168334),(105,168334),(113,168334),(130,168334),(145,102433),(146,168334),(153,102433),(154,168334)]),([6,7,1984,17464,34889,270884],[(0,168334),(2,360526),(4,168334),(6,168334),(8,168334),(10,397486),(12,168334),(14,32869),(16,168334),(18,406693),(57,168334),(58,168334),(73,168334),(74,168334),(81,168334),(82,168334),(105,168334),(113,168334),(130,168334),(137,102433),(138,168334),(153,102433),(154,168334)]),([6,7,1984,34889,69816,131346],[(0,570533),(2,360526),(4,570533),(6,570533),(8,570533),(10,65738),(12,570533),(14,561326),(16,570533),(18,168494),(57,570533),(58,570533),(81,570533),(97,570533),(98,570533),(106,570533),(113,570469),(114,570533),(129,79201),(130,570533),(138,570533),(145,205889),(146,570533)]),([6,7,1984,34937,69760,131346],[(0,570469),(2,98382),(4,570469),(6,570469),(8,570469),(10,65646),(12,570469),(14,570469),(16,570469),(18,102958),(57,570469),(58,570469),(81,570469),(97,570469),(98,570469),(106,570469),(113,570469),(114,570469),(129,78945),(130,570469),(138,570469),(153,111681),(154,570469)]),([6,56,1984,34889,69760,131351],[(0,46245),(2,37038),(4,46245),(6,46245),(8,46245),(10,32970),(12,46245),(14,46245),(16,46245),(18,167982),(57,46245),(58,46245),(73,46177),(74,46181),(81,46245),(97,46245),(98,46245),(106,46245),(113,46245),(114,46245),(138,46245),(153,205857),(154,46245)]),([6,56,1984,34889,69767,131346],[(0,570533),(2,561326),(4,570533),(6,570533),(8,570533),(10,65738),(12,570533),(14,360526),(16,570533),(18,168494),(57,570533),(58,570533),(73,570533),(74,570469),(81,570533),(97,570533),(98,570533),(106,570533),(138,570533),(145,205889),(146,570533),(153,79201),(154,570533)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([7,7,56,1984,17408,34889,270884],[(0,168334),(2,360526),(4,168334),(6,397486),(8,168334),(10,168334),(12,168334),(14,168334),(16,168334),(18,32869),(20,168334),(22,406693),(57,168334),(58,168334),(73,168334),(74,168334),(81,168334),(82,168334),(97,168334),(98,168334),(105,168334),(106,168334),(113,168334),(114,168334),(137,168334),(145,168334),(153,168334),(154,168334),(170,168334),(185,102433),(186,168334),(193,102433),(194,168334),(201,102433),(202,168334)]),([7,7,56,1984,34889,69760,131346],[(0,570533),(2,360526),(4,570533),(6,561326),(8,570533),(10,570533),(12,570533),(14,65738),(16,570533),(18,570533),(20,570533),(22,168494),(57,570533),(58,570533),(73,570533),(74,570533),(81,570533),(82,570533),(105,570533),(106,570469),(113,570533),(129,570533),(130,570533),(137,570533),(138,570533),(146,570533),(153,570533),(154,570533),(169,79201),(170,570533),(186,570533),(193,205889),(194,570533),(201,205889),(202,570533)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((K_0 ++ (K_1 ++ K_2))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app c_0 (all_app c_1 c_2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coreLower (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 7) (hr : Matches C) : False := by
  let f : BFn 10 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 5 × Fin 5) (hp : p ∈ samplePairs) : f (pt 10 (pairCode p)) = reference (pt 10 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 10 (pairCode (i,j)))) = _
    rw [codeInputs, graphRow]
    exact hr (i,j) hp
  have encode : encL f points = Y_ := by
    calc
      encL f points = encL reference points := by
        apply enc_congr_rows
        intro v hv
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
        exact he p hp
      _ = Y_ := by decide +kernel
  have nc : ∃ x y : Fin 10 → Bool, f x ≠ f y := by
    refine ⟨pt 10 (pairCode (0, 0)),pt 10 (pairCode (0, 2)),?_⟩
    rw [he (0, 0) (by decide +kernel),he (0, 2) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 7 8 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 7 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end Slice1

namespace Slice2
def probeRoots : List (List Nat × Nat) := [([7,56,1984,2121,8448,63488,69776],407717),([7,56,1984,2121,16898,63488,164900],168336),([7,56,1984,2121,8448,69776,196608],407717),([7,56,1984,2121,16898,164900,196608],168336),([7,56,1984,2121,8448,16898,69776],408741),([7,56,1984,2121,8448,69776,164900],205857),([7,56,1984,2121,16898,69776,164900],179589),([7,56,1984,2121,8448,16898,164900],168336),([7,56,1984,8448,16898,69776,164900],65739),([7,56,2121,8448,63488,69776,196608],407717),([7,56,2121,16898,63488,164900,196608],168336),([7,1984,2121,8448,63488,69776,196608],528562),([7,1984,2121,16898,63488,164900,196608],528562),([56,1984,2121,8448,63488,69776,196608],407717),([56,1984,2121,16898,63488,164900,196608],168336)]
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
  (x 1 || x 5 || x 0 || x 6 || x 7) && !((x 1 || x 5 || x 2) && (x 0 || x 6 || x 7))
def pairInput (i j : Fin 5) := PEqualNP.Represents.oneEach i j
theorem codeInputs : ∀ p : Fin 5 × Fin 5, List.ofFn (pt 10 (pairCode p)) = pairInput p.1 p.2 := by decide +kernel
theorem graphRow : ∀ i j : Fin 5, reference (pt 10 (pairCode (i,j))) =
   (7571262 : ℕ).testBit (5 * i.val + j.val) := by decide +kernel
def samplePairs : List (Fin 5 × Fin 5) := [(0, 0), (0, 3), (0, 4), (1, 0), (1, 1), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 4)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) = (7571262 : ℕ).testBit (5 * p.1.val + p.2.val)
def M_ : ℕ := 262143

def Y_ : ℕ := 79982

def XS_ : List ℕ := [7, 56, 1984, 63488, 196608, 2121, 69776, 8448, 16898, 164900]

def PD_ : List (ℕ × ℕ) := [(1, 107609), (2, 30325), (3, 8035), (4, 11240), (5, 4525), (6, 3215), (7, 542), (8, 342), (9, 242), (10, 32), (11, 73), (12, 61), (13, 7), (14, 10), (15, 4), (16, 3)]

def PM_ : List (ℕ × ℕ) := [(0, 79982), (4, 79982), (7, 79982), (8, 79982), (9, 79982), (10, 79982), (14, 79982), (15, 79982), (17, 79982)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1984,2169,78231] BT.lf) [5,7,56,2121,182246] BT.lf) [5,7,1984,2169,78224] (BT.nd BT.lf [5,56,1984,2121,78231] BT.lf)) [5,1984,2121,8504,69783] (BT.nd (BT.nd (BT.nd BT.lf [5,1984,2169,8448,69783] BT.lf) [5,1984,2169,8455,69776] BT.lf) [6,7,56,1984,2121,78224] (BT.nd BT.lf [6,7,56,1984,2121,181798] BT.lf))) [6,7,56,2121,16898,165860] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,56,2121,18370,164900] BT.lf) [6,7,1984,2121,8504,69776] BT.lf) [6,7,1984,2121,16954,164900] (BT.nd BT.lf [6,7,1984,2169,8448,69776] BT.lf)) [6,56,1984,2121,8448,69783] (BT.nd (BT.nd BT.lf [6,56,1984,2121,8455,69776] BT.lf) [7,7,56,1984,2121,8448,69776] (BT.nd BT.lf [7,7,56,1984,2121,16898,164900] BT.lf))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([4,1984,2169,78231],[(0,47201),(2,47201),(4,47201),(6,32879),(8,47201),(10,98351),(57,47201),(74,47201),(77,42081)]),([5,7,56,2121,182246],[(0,168328),(2,360488),(4,168328),(6,397480),(8,168328),(10,168328),(12,168328),(14,400549),(57,168328),(58,168328),(74,33160),(81,168328),(98,168328),(114,168328)]),([5,7,1984,2169,78224],[(0,407653),(2,98351),(4,407653),(6,407653),(8,407653),(10,32879),(12,407653),(14,102799),(57,407653),(58,407653),(81,407653),(97,47201),(98,407653),(106,407653),(109,402533)]),([5,56,1984,2121,78231],[(0,47269),(2,37039),(4,47269),(6,47269),(8,47269),(10,32970),(12,47269),(14,167983),(57,47269),(58,47269),(73,47201),(74,47205),(81,47269),(106,47269),(109,42149)]),([5,1984,2121,8504,69783],[(0,47269),(2,47269),(4,47269),(6,32970),(8,47269),(10,37039),(12,47269),(14,167983),(57,47269),(74,47269),(81,47205),(82,47201),(98,47269)]),([5,1984,2169,8448,69783],[(0,47201),(2,47201),(4,47201),(6,32879),(8,47201),(10,47201),(12,47201),(14,98351),(57,47201),(74,47201),(81,47201),(82,47201),(98,47201),(113,112673),(114,47201)]),([5,1984,2169,8455,69776],[(0,407653),(2,407653),(4,407653),(6,32879),(8,407653),(10,98351),(12,407653),(14,102799),(57,407653),(74,407653),(98,407653),(113,47201),(114,407653)]),([6,7,56,1984,2121,78224],[(0,407717),(2,360495),(4,407717),(6,397487),(8,407717),(10,407717),(12,407717),(14,32970),(16,407717),(18,168335),(57,407717),(58,407717),(73,407717),(74,407717),(81,407717),(82,407717),(105,407717),(106,407653),(113,407717),(129,47457),(130,407717),(146,407717),(149,402597),(153,205857),(154,407717)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,56,1984,2121,181798],[(0,168335),(2,360495),(4,168335),(6,397487),(8,168335),(10,168335),(12,168335),(14,168335),(16,168335),(18,407717),(57,168335),(58,168335),(73,168335),(74,168335),(81,168335),(82,168335),(98,33167),(105,168335),(113,168335),(130,168335),(145,173445),(146,168335),(153,32970),(154,168335)]),([6,7,56,2121,16898,165860],[(0,168328),(2,360495),(4,168328),(6,397480),(8,168328),(10,168328),(12,168328),(14,168328),(16,168328),(18,400549),(57,168328),(58,168328),(74,65928),(81,168328),(98,168328),(105,168328),(106,168328),(113,168328),(114,168328),(130,168328),(146,168328),(153,171397),(154,168328)]),([6,7,56,2121,18370,164900],[(0,168336),(2,360488),(4,168336),(6,397488),(8,168336),(10,168336),(12,168336),(14,168336),(16,168336),(18,408741),(57,168336),(58,168336),(74,65936),(81,168336),(98,168336),(105,168336),(106,168336),(114,168336),(130,168336),(145,65739),(146,168336),(153,174469),(154,168336)]),([6,7,1984,2121,8504,69776],[(0,407717),(2,360495),(4,407717),(6,407717),(8,407717),(10,32970),(12,407717),(14,397487),(16,407717),(18,168335),(57,407717),(58,407717),(81,407717),(97,407717),(98,407717),(106,407717),(113,407653),(114,407717),(129,47457),(130,407717),(138,407717),(145,205857),(146,407717)]),([6,7,1984,2121,16954,164900],[(0,168336),(2,360485),(4,168336),(6,168336),(8,168336),(10,168336),(12,168336),(14,397488),(16,168336),(18,408741),(57,168336),(58,168336),(74,65936),(81,168336),(98,168336),(105,168336),(106,168336),(114,168336),(130,168336),(137,174469),(138,168336),(145,65739),(146,168336)]),([6,7,1984,2169,8448,69776],[(0,407653),(2,98351),(4,407653),(6,407653),(8,407653),(10,32879),(12,407653),(14,407653),(16,407653),(18,102799),(57,407653),(58,407653),(81,407653),(97,407653),(98,407653),(106,407653),(113,407653),(114,407653),(129,47201),(130,407653),(138,407653),(153,112673),(154,407653)]),([6,56,1984,2121,8448,69783],[(0,47269),(2,37039),(4,47269),(6,47269),(8,47269),(10,32970),(12,47269),(14,47269),(16,47269),(18,167983),(57,47269),(58,47269),(73,47201),(74,47205),(81,47269),(97,47269),(98,47269),(106,47269),(113,47269),(114,47269),(138,47269),(153,205857),(154,47269)]),([6,56,1984,2121,8455,69776],[(0,407717),(2,397487),(4,407717),(6,407717),(8,407717),(10,32970),(12,407717),(14,360495),(16,407717),(18,168335),(57,407717),(58,407717),(73,407717),(74,407653),(81,407717),(97,407717),(98,407717),(106,407717),(138,407717),(145,205857),(146,407717),(153,47457),(154,407717)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([7,7,56,1984,2121,8448,69776],[(0,407717),(2,360495),(4,407717),(6,397487),(8,407717),(10,407717),(12,407717),(14,32970),(16,407717),(18,407717),(20,407717),(22,168335),(57,407717),(58,407717),(73,407717),(74,407717),(81,407717),(82,407717),(105,407717),(106,407653),(113,407717),(129,407717),(130,407717),(137,407717),(138,407717),(146,407717),(153,407717),(154,407717),(169,47457),(170,407717),(186,407717),(193,205857),(194,407717),(201,205857),(202,407717)]),([7,7,56,1984,2121,16898,164900],[(0,168336),(2,360495),(4,168336),(6,397488),(8,168336),(10,168336),(12,168336),(14,168336),(16,168336),(18,168336),(20,168336),(22,408741),(57,168336),(58,168336),(73,168336),(74,168336),(81,168336),(82,168336),(98,65936),(105,168336),(113,168336),(130,168336),(137,168336),(138,168336),(145,168336),(146,168336),(153,168336),(154,168336),(170,168336),(185,174469),(186,168336),(193,65739),(194,168336),(201,179589),(202,168336)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((K_0 ++ (K_1 ++ K_2))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app c_0 (all_app c_1 c_2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coreLower (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 7) (hr : Matches C) : False := by
  let f : BFn 10 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 5 × Fin 5) (hp : p ∈ samplePairs) : f (pt 10 (pairCode p)) = reference (pt 10 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 10 (pairCode (i,j)))) = _
    rw [codeInputs, graphRow]
    exact hr (i,j) hp
  have encode : encL f points = Y_ := by
    calc
      encL f points = encL reference points := by
        apply enc_congr_rows
        intro v hv
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
        exact he p hp
      _ = Y_ := by decide +kernel
  have nc : ∃ x y : Fin 10 → Bool, f x ≠ f y := by
    refine ⟨pt 10 (pairCode (0, 0)),pt 10 (pairCode (0, 3)),?_⟩
    rw [he (0, 0) (by decide +kernel),he (0, 3) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 7 8 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 7 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end Slice2

namespace Slice3
def probeRoots : List (List Nat × Nat) := [([31,224,7936,8192,16641,33314,74820],541927),([31,224,7936,8192,16641,133256,266256],234994),([31,224,7936,16641,33314,74820,507904],541927),([31,224,7936,16641,133256,266256,507904],234994),([31,224,7936,16641,33314,74820,133256],274561),([31,224,7936,16641,33314,74820,266256],443623),([31,224,7936,16641,33314,133256,266256],235954),([31,224,7936,16641,74820,133256,266256],234994),([31,224,7936,33314,74820,133256,266256],131341),([31,224,8192,16641,33314,74820,507904],541927),([31,224,8192,16641,133256,266256,507904],234994),([31,7936,8192,16641,33314,74820,507904],496882),([31,7936,8192,16641,133256,266256,507904],496882),([224,7936,8192,16641,33314,74820,507904],458866),([224,7936,8192,16641,133256,266256,507904],458866),([224,7936,16641,33314,74820,133256,507904],458866),([224,7936,16641,33314,74820,266256,507904],458866),([224,7936,16641,33314,133256,266256,507904],458866),([224,7936,16641,74820,133256,266256,507904],458866),([224,7936,33314,74820,133256,266256,507904],458866)]
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
  (x 1 || x 5 || x 0 || x 6 || x 7) && !((x 1 || x 5 || x 2) && (x 0 || x 6 || x 7))
def pairInput (i j : Fin 5) := PEqualNP.Represents.oneEach i j
theorem codeInputs : ∀ p : Fin 5 × Fin 5, List.ofFn (pt 10 (pairCode p)) = pairInput p.1 p.2 := by decide +kernel
theorem graphRow : ∀ i j : Fin 5, reference (pt 10 (pairCode (i,j))) =
   (7571262 : ℕ).testBit (5 * i.val + j.val) := by decide +kernel
def samplePairs : List (Fin 5 × Fin 5) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) = (7571262 : ℕ).testBit (5 * p.1.val + p.2.val)
def M_ : ℕ := 524287

def Y_ : ℕ := 123294

def XS_ : List ℕ := [31, 224, 7936, 8192, 507904, 16641, 33314, 74820, 133256, 266256]

def PD_ : List (ℕ × ℕ) := [(1, 69969), (2, 104953), (3, 56749), (4, 32647), (5, 11922), (6, 1560), (7, 605), (8, 127), (9, 366), (10, 486), (11, 162), (13, 17), (14, 25), (15, 13), (16, 7), (17, 2)]

def PM_ : List (ℕ × ℕ) := [(0, 123294), (5, 123294), (6, 123294), (9, 123294), (10, 123294), (11, 123294), (12, 123294), (17, 123294), (18, 123294)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7936,16865,108159] BT.lf) [5,31,224,16641,401304] BT.lf) [5,31,7936,16865,108134] (BT.nd (BT.nd BT.lf [5,224,7936,16641,108159] BT.lf) [5,7936,16865,33314,74847] BT.lf)) [5,7936,16865,33343,74820] (BT.nd (BT.nd (BT.nd BT.lf [5,7936,16865,399512,507904] BT.lf) [6,31,224,7936,16641,108134] BT.lf) [6,31,224,7936,16641,399512] (BT.nd (BT.nd BT.lf [6,31,224,16641,133256,270096] BT.lf) [6,31,224,16641,139144,266256] BT.lf))) [6,31,7936,16641,133256,266480] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,7936,16865,33314,74820] BT.lf) [6,224,7936,16641,33314,74847] BT.lf) [6,224,7936,16641,33343,74820] (BT.nd (BT.nd BT.lf [6,224,7936,16641,108134,507904] BT.lf) [6,224,7936,16641,399512,507904] BT.lf)) [6,7936,16865,133256,266256,507904] (BT.nd (BT.nd (BT.nd BT.lf [7,31,224,7936,16641,33314,74820] BT.lf) [7,31,224,7936,16641,133256,266256] BT.lf) [7,224,7936,16641,33314,74820,507904] (BT.nd BT.lf [7,224,7936,16641,133256,266256,507904] BT.lf))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([4,7936,16865,108159],[(0,50401),(2,50401),(4,50401),(6,33010),(8,50401),(10,229426),(57,50401),(74,50401),(77,44257)]),([5,31,224,16641,401304],[(0,234922),(2,458858),(4,234922),(6,431338),(8,234922),(10,33034),(12,234922),(14,435430),(57,234922),(58,234922),(81,234922),(82,234922),(98,234922),(114,234922)]),([5,31,7936,16865,108134],[(0,443622),(2,229490),(4,443622),(6,443622),(8,443622),(10,98546),(12,443622),(14,234930),(57,443622),(58,443622),(81,443622),(97,115937),(98,443622),(106,443622),(109,437478)]),([5,224,7936,16641,108159],[(0,50406),(2,38130),(4,50406),(6,50406),(8,50406),(10,33036),(12,50406),(14,234546),(57,50406),(58,50406),(73,50406),(74,50406),(81,50406),(106,50406),(109,44262)]),([5,7936,16865,33314,74847],[(0,83169),(2,83169),(4,83169),(6,65778),(8,83169),(10,234994),(12,83169),(14,229458),(57,83169),(74,83169),(98,83169),(113,509158),(114,83169)]),([5,7936,16865,33343,74820],[(0,443623),(2,443623),(4,443623),(6,33010),(8,443623),(10,229426),(12,443623),(14,235954),(57,443623),(74,443623),(98,443623),(113,50401),(114,443623)]),([5,7936,16865,399512,507904],[(0,458866),(2,42241),(4,458866),(6,458866),(8,458866),(10,458866),(12,458866),(14,229874),(74,458866),(81,458866),(97,262186),(98,458866),(105,271393)]),([6,31,224,7936,16641,108134],[(0,443622),(2,458866),(4,443622),(6,431346),(8,443622),(10,443622),(12,443622),(14,98572),(16,443622),(18,234930),(57,443622),(58,443622),(73,443622),(74,443622),(81,443622),(82,443622),(105,443622),(106,443622),(113,443622),(129,116161),(130,443622),(146,443622),(149,437478),(153,273505),(154,443622)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,224,7936,16641,399512],[(0,234930),(2,458866),(4,234930),(6,431346),(8,234930),(10,234930),(12,234930),(14,33034),(16,234930),(18,443622),(57,234930),(58,234930),(73,234930),(74,234930),(81,234930),(82,234930),(105,234930),(106,234930),(113,234930),(130,234930),(145,271393),(146,234930),(153,271393),(154,234930)]),([6,31,224,16641,133256,270096],[(0,234930),(2,458866),(4,234930),(6,431346),(8,234930),(10,33034),(12,234930),(14,443622),(16,234930),(18,234930),(57,234930),(58,234930),(81,234930),(82,234930),(98,234930),(113,271393),(114,234930),(130,234930),(137,247206),(138,234930),(146,234930),(153,234930),(154,271393)]),([6,31,224,16641,139144,266256],[(0,234922),(2,458858),(4,234922),(6,431338),(8,234922),(10,33034),(12,234922),(14,435430),(16,234922),(18,234922),(57,234922),(58,234922),(81,234922),(82,234922),(98,234922),(114,234922),(130,234922),(137,239014),(138,234922),(145,271393),(146,234922),(153,234922),(154,271393)]),([6,31,7936,16641,133256,266480],[(0,247206),(2,458866),(4,247206),(6,247206),(8,247206),(10,33034),(12,247206),(14,443622),(16,247206),(18,431346),(57,247206),(58,247206),(81,247206),(98,247206),(105,241062),(106,247206),(113,247206),(114,247206),(130,247206),(137,234930),(138,247206),(145,271393),(146,247206)]),([6,31,7936,16865,33314,74820],[(0,443623),(2,229490),(4,443623),(6,443623),(8,443623),(10,98546),(12,443623),(14,234994),(16,443623),(18,235954),(57,443623),(58,443623),(81,443623),(97,443623),(98,443623),(106,443623),(129,115937),(130,443623),(138,443623),(153,509158),(154,443623)]),([6,224,7936,16641,33314,74847],[(0,83175),(2,71922),(4,83175),(6,83175),(8,83175),(10,65804),(12,83175),(14,234994),(16,83175),(18,235602),(57,83175),(58,83175),(73,83175),(74,83175),(81,83175),(106,83175),(113,83175),(114,83175),(138,83175),(153,509158),(154,83175)]),([6,224,7936,16641,33343,74820],[(0,443623),(2,38130),(4,443623),(6,443623),(8,443623),(10,33036),(12,443623),(14,234546),(16,443623),(18,235954),(57,443623),(58,443623),(73,443623),(74,443623),(81,443623),(106,443623),(138,443623),(145,273441),(146,443623),(153,50406),(154,443623)]),([6,224,7936,16641,108134,507904],[(0,458866),(2,458866),(4,458866),(6,42241),(8,458866),(10,458866),(12,458866),(14,458866),(16,458866),(18,509158),(57,458866),(58,458866),(73,458866),(74,458866),(101,458866),(106,458866),(113,458866),(114,458866),(129,496882),(130,458866),(137,262186),(138,458866),(154,458866)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([6,224,7936,16641,399512,507904],[(0,458866),(2,458866),(4,458866),(6,42241),(8,458866),(10,458866),(12,458866),(14,458866),(16,458866),(18,234994),(57,458866),(58,458866),(73,458866),(74,458866),(97,458866),(106,458866),(113,458866),(114,458866),(129,496882),(130,458866),(137,262186),(138,458866),(145,271393)]),([6,7936,16865,133256,266256,507904],[(0,458866),(2,42241),(4,458866),(6,458866),(8,458866),(10,458866),(12,458866),(14,458866),(16,458866),(18,229874),(74,458866),(81,458866),(98,458866),(105,458866),(106,458866),(113,458866),(114,458866),(129,262186),(130,458866),(137,271393),(157,458866)]),([7,31,224,7936,16641,33314,74820],[(0,443623),(2,458866),(4,443623),(6,432370),(8,443623),(10,443623),(12,443623),(14,98572),(16,443623),(18,234994),(20,443623),(22,235954),(57,443623),(58,443623),(73,443623),(74,443623),(81,443623),(82,443623),(105,443623),(106,443623),(113,443623),(129,443623),(130,443623),(146,443623),(153,443623),(154,443623),(169,116161),(170,443623),(186,443623),(193,273505),(194,443623),(201,509158),(202,443623)]),([7,31,224,7936,16641,133256,266256],[(0,234930),(2,458866),(4,234930),(6,431346),(8,234930),(10,234930),(12,234930),(14,33034),(16,234930),(18,443622),(20,234930),(22,234930),(57,234930),(58,234930),(73,234930),(74,234930),(81,234930),(82,234930),(105,234930),(106,234930),(113,234930),(130,234930),(145,271393),(146,234930),(153,271393),(154,234930),(170,234930),(177,247206),(178,234930),(185,234930),(186,234930),(193,271393),(194,234930),(201,234930),(202,271393)]),([7,224,7936,16641,33314,74820,507904],[(0,458866),(2,458866),(4,458866),(6,42241),(8,458866),(10,458866),(12,458866),(14,458866),(16,458866),(18,458866),(20,458866),(22,541927),(57,458866),(58,458866),(73,458866),(74,458866),(106,458866),(113,458866),(114,458866),(138,458866),(145,458866),(146,458866),(153,458866),(154,458866),(169,496882),(170,458866),(177,262186),(178,458866),(194,458866),(202,458866)]),([7,224,7936,16641,133256,266256,507904],[(0,458866),(2,458866),(4,458866),(6,42241),(8,458866),(10,458866),(12,458866),(14,458866),(16,458866),(18,458866),(20,458866),(22,234994),(57,458866),(58,458866),(73,458866),(74,458866),(97,458866),(106,458866),(113,458866),(114,458866),(129,458866),(130,458866),(138,458866),(145,458866),(146,458866),(153,458866),(154,458866),(169,496882),(170,458866),(177,262186),(178,458866),(185,271393),(205,458866)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((K_0 ++ (K_1 ++ K_2))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app c_0 (all_app c_1 c_2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coreLower (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 7) (hr : Matches C) : False := by
  let f : BFn 10 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 5 × Fin 5) (hp : p ∈ samplePairs) : f (pt 10 (pairCode p)) = reference (pt 10 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 10 (pairCode (i,j)))) = _
    rw [codeInputs, graphRow]
    exact hr (i,j) hp
  have encode : encL f points = Y_ := by
    calc
      encL f points = encL reference points := by
        apply enc_congr_rows
        intro v hv
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
        exact he p hp
      _ = Y_ := by decide +kernel
  have nc : ∃ x y : Fin 10 → Bool, f x ≠ f y := by
    refine ⟨pt 10 (pairCode (0, 0)),pt 10 (pairCode (0, 1)),?_⟩
    rw [he (0, 0) (by decide +kernel),he (0, 1) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 7 8 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 7 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end Slice3

namespace Slice4
def probeRoots : List (List Nat × Nat) := [([7,248,768,15360,16393,34066,67616],372934),([7,248,768,15360,16393,135744,270468],233806),([7,248,768,16393,34066,67616,507904],372934),([7,248,768,16393,135744,270468,507904],233806),([7,248,768,16393,34066,67616,135744],373990),([7,248,768,16393,34066,67616,270468],372934),([7,248,768,16393,34066,135744,270468],234862),([7,248,768,16393,67616,135744,270468],233806),([7,248,768,34066,67616,135744,270468],65998),([7,248,15360,16393,34066,67616,507904],372934),([7,248,15360,16393,135744,270468,507904],233806),([7,768,15360,16393,34066,67616,507904],495826),([7,768,15360,16393,135744,270468,507904],495826),([248,768,15360,16393,34066,67616,507904],458834),([248,768,15360,16393,135744,270468,507904],458835)]
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
  (x 1 || x 5 || x 0 || x 6 || x 7) && !((x 1 || x 5 || x 2) && (x 0 || x 6 || x 7))
def pairInput (i j : Fin 5) := PEqualNP.Represents.oneEach i j
theorem codeInputs : ∀ p : Fin 5 × Fin 5, List.ofFn (pt 10 (pairCode p)) = pairInput p.1 p.2 := by decide +kernel
theorem graphRow : ∀ i j : Fin 5, reference (pt 10 (pairCode (i,j))) =
   (7571262 : ℕ).testBit (5 * i.val + j.val) := by decide +kernel
def samplePairs : List (Fin 5 × Fin 5) := [(0, 0), (0, 1), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) = (7571262 : ℕ).testBit (5 * p.1.val + p.2.val)
def M_ : ℕ := 524287

def Y_ : ℕ := 117966

def XS_ : List ℕ := [7, 248, 768, 15360, 507904, 16393, 34066, 67616, 135744, 270468]

def PD_ : List (ℕ × ℕ) := [(1, 76457), (2, 114685), (3, 62807), (4, 20482), (5, 680), (6, 3069), (7, 3927), (8, 1282), (9, 40), (10, 189), (11, 247), (12, 82), (14, 9), (15, 13), (16, 7), (17, 2)]

def PM_ : List (ℕ × ℕ) := [(0, 117966), (4, 117966), (5, 117966), (8, 117966), (9, 117966), (12, 117966), (13, 117966), (17, 117966), (18, 117966)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,768,16633,101687] BT.lf) [5,7,248,16393,406468] (BT.nd BT.lf [5,7,768,16633,101682] BT.lf)) [5,248,768,16393,101687] (BT.nd (BT.nd BT.lf [5,768,16633,34066,67623] BT.lf) [5,768,16633,34071,67616] (BT.nd BT.lf [6,7,248,768,16393,101682] BT.lf))) [6,7,248,768,16393,406212] (BT.nd (BT.nd (BT.nd BT.lf [6,7,248,16393,135744,271236] BT.lf) [6,7,248,16393,136000,270468] (BT.nd BT.lf [6,7,768,16633,34066,67616] BT.lf)) [6,248,768,16393,34066,67623] (BT.nd (BT.nd BT.lf [6,248,768,16393,34071,67616] BT.lf) [7,7,248,768,16393,34066,67616] (BT.nd BT.lf [7,7,248,768,16393,135744,270468] BT.lf))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([4,768,16633,101687],[(0,45153),(2,45153),(4,45153),(6,32877),(8,45153),(10,98349),(57,45153),(58,45153),(74,45153),(77,42081)]),([5,7,248,16393,406468],[(0,201033),(2,458825),(4,201033),(6,331977),(8,201033),(10,32869),(12,201033),(14,336069),(57,201033),(58,201033),(81,201033),(98,201033),(113,102433),(114,201033)]),([5,7,768,16633,101682],[(0,340069),(2,98381),(4,340069),(6,340069),(8,340069),(10,65645),(12,340069),(14,102733),(57,340069),(58,340069),(81,340069),(82,340069),(97,77921),(98,340069),(106,340069),(109,336997)]),([5,248,768,16393,101687],[(0,45253),(2,37069),(4,45253),(6,45253),(8,45253),(10,33229),(12,45253),(14,200749),(57,45253),(58,45253),(73,45153),(74,45157),(81,45253),(82,45253),(106,45253),(109,42181)]),([5,768,16633,34066,67623],[(0,77921),(2,77921),(4,77921),(6,65645),(8,77921),(10,102733),(12,77921),(14,98381),(57,77921),(58,77921),(74,77921),(77,74849),(97,340069),(98,77921),(113,340069),(114,77921)]),([5,768,16633,34071,67616],[(0,372838),(2,372838),(4,372838),(6,32877),(8,372838),(10,98349),(12,372838),(14,103789),(57,372838),(58,372838),(74,372838),(77,369766),(97,45153),(98,372838),(113,45153),(114,372838)]),([6,7,248,768,16393,101682],[(0,340165),(2,458829),(4,340165),(6,331981),(8,340165),(10,340165),(12,340165),(14,65997),(16,340165),(18,201037),(57,340165),(58,340165),(73,340165),(74,340165),(81,340165),(82,340165),(105,340165),(106,340069),(113,340165),(114,340165),(129,78273),(130,340165),(146,340165),(149,337093),(153,471105),(154,340165)]),([6,7,248,768,16393,406212],[(0,201037),(2,458829),(4,201037),(6,331981),(8,201037),(10,201037),(12,201037),(14,32869),(16,201037),(18,340165),(57,201037),(58,201037),(73,201037),(74,201037),(81,201037),(82,201037),(105,201037),(113,201037),(114,201037),(130,201037),(145,102433),(146,201037),(153,102433),(154,201037)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,248,16393,135744,271236],[(0,233801),(2,458825),(4,233801),(6,331981),(8,233801),(10,32869),(12,233801),(14,340165),(16,233801),(18,336101),(57,233801),(58,233801),(81,233801),(97,233801),(98,233801),(113,233801),(114,233801),(130,233801),(145,102433),(146,233801),(153,201037),(154,233801)]),([6,7,248,16393,136000,270468],[(0,233806),(2,458830),(4,233806),(6,331977),(8,233806),(10,32869),(12,233806),(14,336069),(16,233806),(18,341221),(57,233806),(58,233806),(81,233806),(97,233806),(98,233806),(113,233806),(114,233806),(130,233806),(145,102433),(146,233806),(153,201033),(154,233806)]),([6,7,768,16633,34066,67616],[(0,372838),(2,98381),(4,372838),(6,372838),(8,372838),(10,65645),(12,372838),(14,102733),(16,372838),(18,103789),(57,372838),(58,372838),(81,372838),(82,372838),(97,372838),(98,372838),(106,372838),(109,369766),(129,77921),(130,372838),(137,340069),(138,372838),(153,340069),(154,372838)]),([6,248,768,16393,34066,67623],[(0,78022),(2,70861),(4,78022),(6,78022),(8,78022),(10,65997),(12,78022),(14,201037),(16,78022),(18,201805),(57,78022),(58,78022),(73,77921),(74,77926),(81,78022),(82,78022),(106,78022),(109,74950),(113,78022),(114,78022),(137,340165),(138,78022),(153,340165),(154,78022)]),([6,248,768,16393,34071,67616],[(0,372934),(2,37069),(4,372934),(6,372934),(8,372934),(10,33229),(12,372934),(14,200749),(16,372934),(18,202093),(57,372934),(58,372934),(73,372934),(74,372838),(81,372934),(82,372934),(106,372934),(109,369862),(137,45253),(138,372934),(145,471073),(146,372934),(153,45253),(154,372934)]),([7,7,248,768,16393,34066,67616],[(0,372934),(2,458829),(4,372934),(6,331981),(8,372934),(10,372934),(12,372934),(14,65997),(16,372934),(18,201037),(20,372934),(22,202093),(57,372934),(58,372934),(73,372934),(74,372934),(81,372934),(82,372934),(105,372934),(106,372838),(113,372934),(114,372934),(129,372934),(130,372934),(146,372934),(149,369862),(153,372934),(154,372934),(169,78273),(170,372934),(185,340165),(186,372934),(193,471105),(194,372934),(201,340165),(202,372934)]),([7,7,248,768,16393,135744,270468],[(0,233806),(2,458830),(4,233806),(6,331981),(8,233806),(10,233806),(12,233806),(14,32869),(16,233806),(18,340165),(20,233806),(22,341221),(57,233806),(58,233806),(73,233806),(74,233806),(81,233806),(82,233806),(105,233806),(113,233806),(114,233806),(129,233806),(130,233806),(145,233806),(146,233806),(153,233806),(154,233806),(170,233806),(185,201037),(186,233806),(193,102433),(194,233806),(201,201037),(202,233806)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((K_0 ++ K_1)).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app c_0 c_1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coreLower (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 7) (hr : Matches C) : False := by
  let f : BFn 10 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 5 × Fin 5) (hp : p ∈ samplePairs) : f (pt 10 (pairCode p)) = reference (pt 10 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 10 (pairCode (i,j)))) = _
    rw [codeInputs, graphRow]
    exact hr (i,j) hp
  have encode : encL f points = Y_ := by
    calc
      encL f points = encL reference points := by
        apply enc_congr_rows
        intro v hv
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
        exact he p hp
      _ = Y_ := by decide +kernel
  have nc : ∃ x y : Fin 10 → Bool, f x ≠ f y := by
    refine ⟨pt 10 (pairCode (0, 0)),pt 10 (pairCode (0, 1)),?_⟩
    rw [he (0, 0) (by decide +kernel),he (0, 1) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 7 8 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 7 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end Slice4

abbrev Cell := Fin 5 × Fin 5
def samples : Fin 5 → List Cell := ![Slice0.samplePairs,Slice1.samplePairs,Slice2.samplePairs,Slice3.samplePairs,Slice4.samplePairs]
def value (C : Circuit) (q : Cell) := C.eval (PEqualNP.Represents.oneEach q.1 q.2)
def desired (q : Cell) := (7571262 : ℕ).testBit (5*q.1.val+q.2.val)
def errors (C : Circuit) : Finset Cell := Finset.univ.filter fun q => value C q ≠ desired q
set_option maxHeartbeats 0 in
theorem omitted : ∀ q : Cell, ∃ i : Fin 5, q ∉ samples i := by decide +kernel

theorem rejected (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 7) (i : Fin 5) :
    ¬ ∀ p ∈ samples i, value C p = desired p := by
  have cs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cs with rfl | rfl | rfl | rfl | rfl
  · exact Slice0.coreLower C hf hs
  · exact Slice1.coreLower C hf hs
  · exact Slice2.coreLower C hf hs
  · exact Slice3.coreLower C hf hs
  · exact Slice4.coreLower C hf hs

theorem missOther (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 7) (q : Cell) :
    ∃ p, p ≠ q ∧ p ∈ errors C := by
  classical
  obtain ⟨i,hi⟩ := omitted q
  have bad := rejected C hf hs i
  push_neg at bad
  obtain ⟨p,hp,he⟩ := bad
  exact ⟨p,fun eq => hi (eq ▸ hp),Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩

theorem two (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 7) : 2 ≤ (errors C).card := by
  obtain ⟨p,_,hp⟩ := missOther C hf hs (0,0)
  obtain ⟨q,hq,hq'⟩ := missOther C hf hs p
  exact Finset.one_lt_card.mpr ⟨p,hp,q,hq',Ne.symm hq⟩
def close : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [10, 15]⟩], 16⟩
theorem closeLegal : FanInTwo close := by
  intro g hg
  simp only [close,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem sharp : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧ (errors C).card = 2 :=
  ⟨close,closeLegal,by decide +kernel,by decide +kernel⟩
end PEqualNP.Outside.L_meta_19374.Robust

open PEqualNP.Outside.L_meta_19374.Robust in
theorem PEqualNP.Outside.L_meta_19374 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 7 → 2 ≤ (errors C).card) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 7 ∧ (errors C).card = 2) := ⟨two,sharp⟩
