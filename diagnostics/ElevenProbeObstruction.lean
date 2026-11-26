import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23615.Short

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

def ugood (m y t : Nat) (ws : List Nat) (hs : List (Nat × Nat)) : Bool :=
  if ws.length = t then hs.all (fun x => x.1 != 1024 || ucheck m y t ws x.2) else true
theorem ugood_sound {m y t ws} (h : NatRun m y t ws) (hs : List (Nat × Nat)) :
    ugood m y t ws hs = true := by
  unfold ugood
  split
  · apply List.all_eq_true.mpr
    intro x _
    simp [ucheck_sound h]
  · rfl
def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && ugood m y t ys h && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

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
        (fun tag ys => via y pD pM t ys && ugood m y t ys h && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ugood_sound hys, ih ys hys, hfind_false hG T t ih h tag hys])
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



def pairCode (p : Fin 6 × Fin 6) : Nat := 2 ^ p.1.val ||| 2 ^ p.2.val
def reference (x : Fin 6 → Bool) : Bool :=
  (x 1 && !(x 0 || x 3 || x 5)) || (x 0 && (x 4 || x 5)) || (x 2 && x 3)
def pairInput (i j : Fin 6) := List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)
theorem codeInputs : ∀ p : Fin 6 × Fin 6, List.ofFn (pt 6 (pairCode p)) = pairInput p.1 p.2 := by
  decide +kernel
theorem graphRow : ∀ i j : Fin 6, reference (pt 6 (pairCode (i,j))) =
    (34224 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel
def samplePairs : List (Fin 6 × Fin 6) := [(0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 5), (2, 2), (2, 3), (3, 5)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def M_ : ℕ := 2047

def Y_ : ℕ := 568

def XS_ : List ℕ := [31, 226, 768, 1604, 8, 1168]

def PD_ : List (ℕ × ℕ) := [(1, 804), (2, 182), (3, 127), (4, 27), (5, 41), (6, 16), (7, 12), (8, 2), (9, 1)]

def PM_ : List (ℕ × ℕ) := [(0, 568), (1, 568), (2, 568), (6, 568), (7, 568), (8, 568), (10, 568)]

def G_ : List (List ℕ) := []



abbrev Hints := List (Nat × Nat)
abbrev Row := List Nat × Hints
def localTree (a : Array Row) : Nat → Nat → Nat → BT
  | 0, _, _ => .lf
  | f+1, i, n =>
    if n = 0 then .lf else
    let h := n / 2
    let k := (a[i+h]?.getD ([],[])).1
    .nd (localTree a f i h) k (localTree a f (i+h+1) (n-h-1))
def blockTree (rs : List Row) : BT := localTree rs.toArray 9 0 rs.length
def Covered (p : List Nat → Hints → Bool) (T : BT) : Prop :=
  ∀ x, T.mem x = true → ∃ h, p x h = true
theorem coveredNode {p : List Nat → Hints → Bool} {l r : BT} {k : List Nat} {h : Hints}
    (hl : Covered p l) (hr : Covered p r) (hk : p k h = true) : Covered p (.nd l k r) := by
  intro x hx
  simp only [BT.mem, Bool.or_eq_true] at hx
  rcases hx with hx | hx
  · rw [leqL_eq x k hx]
    exact ⟨h, hk⟩
  · split at hx
    · exact hl x hx
    · exact hr x hx
theorem coveredBlock {p : List Nat → Hints → Bool} (rs : List Row)
    (hk : (blockTree rs).toList = rs.map Prod.fst)
    (hv : rs.all (fun kh => p kh.1 kh.2) = true) : Covered p (blockTree rs) :=
  cover _ _ hk hv

def b0 : List Row := [([3,607,1944],[(1024,98472),(1024,105633)]),([3,787,1748],[(1024,131171),(1024,133217)]),([3,792,1759],[(1024,98473),(1024,106657)]),([3,795,1756],[(1024,98467),(1024,100513)]),([3,799,1752],[(1024,98471),(1024,104609)]),([3,920,1631],[(1024,98472),(1024,105633)]),([4,4,799,1756],[(1024,98471),(1024,104609)]),([4,8,607,1936],[(1024,131240),(1024,138401)]),([4,8,784,1759],[(1024,131241),(1024,139425)]),([4,8,795,1748],[(1024,131235),(1024,133281)]),([4,8,799,1744],[(1024,131239),(1024,137377)])]
def b1 : List Row := [([4,12,799,1748],[(1024,131171),(1024,133217),(1024,137377)]),([4,16,776,1759],[(1024,98473),(1024,106657)]),([4,19,768,1748],[(1024,98435),(1024,131171),(1024,297065)]),([4,24,768,1759],[(1024,295081),(1024,303265)]),([4,27,768,1756],[(1024,98467),(1024,163939),(1024,297129)]),([4,27,776,1748],[(1024,98473),(1024,131235),(1024,163945)]),([4,31,291,1274],[(1024,99495),(1024,100647),(1024,164967),(1024,301155)]),([4,31,443,920],[(1024,98472),(1024,163944),(1024,171105),(1024,302247)]),([4,31,576,1944],[(1024,98472),(1024,163944),(1024,302247)]),([4,31,580,1944],[(1024,98472),(1024,163944),(1024,302247)]),([4,31,584,1936],[(1024,98471),(1024,131240),(1024,163943)])]
def t0 : BT := .nd (blockTree b0) [4,8,912,1631] (blockTree b1)
def b2 : List Row := [([4,31,772,1756],[(1024,98471),(1024,163943),(1024,301155)]),([4,31,773,1756],[(1024,99495),(1024,164967),(1024,301155)]),([4,31,776,1744],[(1024,98473),(1024,131239),(1024,163945)]),([4,31,780,1748],[(1024,98435),(1024,131171),(1024,163945)]),([4,31,792,1748],[(1024,98473),(1024,106657),(1024,163945),(1024,303271)]),([4,31,792,1756],[(1024,100521),(1024,106663),(1024,303271)]),([4,31,920,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,302247)]),([4,31,1176,1232,1766],[(1024,98471),(1024,172136)]),([4,31,1176,1240,1766],[(1024,98471),(1024,99495),(1024,172136)]),([4,31,1232,1240,1766],[(1024,98471),(1024,172135)]),([4,31,1240,1766],[(1024,98471),(1024,99495),(1024,163943),(1024,170081),(1024,172135)])]
def b3 : List Row := [([4,31,1274,1756],[(1024,99495),(1024,100647),(1024,164967)]),([4,31,1274,1756,1766],[(1024,98471)]),([4,31,1467,1944],[(1024,98472),(1024,163944),(1024,170280)]),([4,95,1168,1176,1766],[(1024,98472),(1024,172136)]),([4,95,1176,1766],[(1024,98472),(1024,99496),(1024,163944),(1024,171105),(1024,172136)]),([4,144,776,1631],[(1024,98473),(1024,106657),(1024,171137)]),([4,152,768,1631],[(1024,105633),(1024,171105),(1024,295081)]),([4,224,1168,1608],[(1024,98443),(1024,104609),(1024,131179)]),([4,224,1176,1600],[(1024,98472),(1024,105633),(1024,295019)]),([4,226,1174,1612],[(1024,98435),(1024,104609),(1024,131171)])]
def t1 : BT := .nd (blockTree b2) [4,31,1266,1748,1774] (blockTree b3)
def t2 : BT := .nd t0 [4,31,768,1752] t1
def b4 : List Row := [([4,226,1183,1604,1790],[(1024,295011)]),([4,226,1183,1756,1860],[]),([4,232,1168,1600],[(1024,131176),(1024,138337),(1024,295015)]),([4,234,1174,1604],[(1024,131170),(1024,132193),(1024,295015)]),([4,247,1168,1631],[(1024,98443),(1024,106657),(1024,131179)]),([4,255,416,1176],[(1024,98472),(1024,105633),(1024,171105),(1024,295019)]),([4,255,424,1168],[(1024,105601),(1024,131176),(1024,138337),(1024,295017)]),([4,255,871,1631],[(1024,105633),(1024,171105),(1024,295019)]),([4,255,1168,1623],[(1024,131176),(1024,138337),(1024,295017)]),([4,255,1176,1631],[(1024,98472),(1024,105633),(1024,295019)]),([4,443,795,1176],[(1024,98472),(1024,105633),(1024,163944),(1024,166177),(1024,171105),(1024,295075)])]
def b5 : List Row := [([4,543,1604,1944],[(1024,98472),(1024,105633)]),([4,576,799,1176],[(1024,98472),(1024,163944),(1024,170273),(1024,171105),(1024,295079)]),([4,584,799,1168],[(1024,98471),(1024,131240),(1024,163943),(1024,170081),(1024,171137)]),([4,607,768,871],[(1024,98472),(1024,163944),(1024,171105),(1024,172321)]),([4,607,768,1176],[(1024,98472),(1024,163944),(1024,171105),(1024,172321),(1024,295081)]),([4,607,776,879],[(1024,131240),(1024,163945),(1024,171137),(1024,172129)]),([4,607,776,1168],[(1024,98473),(1024,131240),(1024,163945),(1024,171137),(1024,172129)]),([4,768,1176,1759,1766],[]),([4,768,1631,1895],[(1024,105633),(1024,171105)]),([4,768,1744,2024],[(1024,98439),(1024,131175)])]
def t3 : BT := .nd (blockTree b4) [4,447,799,1176] (blockTree b5)
def b6 : List Row := [([4,768,1752,2016],[(1024,98471),(1024,163943)]),([4,768,1756,1759,1766],[]),([4,768,1756,2020],[(1024,98467),(1024,163939)]),([4,776,1631,1903],[(1024,106657),(1024,171137)]),([4,776,1744,2016],[(1024,131239),(1024,163945)]),([4,776,1748,2020],[(1024,131235),(1024,163945)]),([4,787,1168,1604],[(1024,131176),(1024,295011)]),([4,792,1168,1631],[(1024,98473),(1024,106657)]),([4,792,1176,1631],[(1024,98473),(1024,106657),(1024,108713),(1024,303265)]),([4,792,1183,1604],[(1024,106657),(1024,303271)]),([4,795,1168,1612],[(1024,98467),(1024,131240)])]
def b7 : List Row := [([4,799,1168,1608],[(1024,98471),(1024,131240)]),([4,799,1172,1612],[(1024,98435),(1024,131171)]),([4,799,1176,1600],[(1024,98472),(1024,295079)]),([4,799,1180,1604],[(1024,98472),(1024,295011)]),([4,799,1604,1688],[(1024,98472),(1024,105633)]),([4,799,1631,1944],[(1024,98472),(1024,106657),(1024,106663)]),([4,799,1756,1944],[(1024,105633),(1024,106663)]),([4,1024,1631,1944],[(1024,98472),(1024,105633)]),([4,1032,1631,1936],[(1024,131179),(1024,138401)]),([4,1055,1604,1944],[(1024,98472),(1024,302187)])]
def t4 : BT := .nd (blockTree b6) [4,795,1176,1604] (blockTree b7)
def t5 : BT := .nd t3 [4,768,1748,2028] t4
def t6 : BT := .nd t2 [4,226,1182,1604] t5
def b8 : List Row := [([4,1176,1631,1766,1944],[(1024,98473)]),([4,1176,1631,1792],[(1024,105633),(1024,295019)]),([4,1274,1756,2016],[(1024,99495),(1024,164967)]),([5,4,8,799,1748],[(1024,131239),(1024,137377)]),([5,4,31,768,1756],[(1024,98471),(1024,163943),(1024,301225)]),([5,4,31,776,1748],[(1024,98473),(1024,131239),(1024,163945)]),([5,4,799,1168,1612],[(1024,98471),(1024,131240)]),([5,4,799,1176,1604],[(1024,98472),(1024,295079)]),([5,6,226,1168,1612],[(1024,98443),(1024,104609),(1024,131179)]),([5,6,226,1176,1604],[(1024,98472),(1024,105633),(1024,295019)]),([5,6,234,1168,1604],[(1024,131176),(1024,138337),(1024,295015)])]
def b9 : List Row := [([5,7,226,1176,1604],[(1024,105641),(1024,106664),(1024,303211)]),([5,8,16,768,1759],[(1024,295081),(1024,303265)]),([5,8,27,768,1748],[(1024,131235),(1024,163971),(1024,297129)]),([5,8,31,299,1266],[(1024,132263),(1024,133415),(1024,164999),(1024,170114),(1024,301187)]),([5,8,31,443,912],[(1024,131240),(1024,163976),(1024,170280),(1024,171137),(1024,302247)]),([5,8,31,576,1936],[(1024,131240),(1024,163976),(1024,302247)]),([5,8,31,580,1936],[(1024,131240),(1024,163976),(1024,302247)]),([5,8,31,768,1744],[(1024,131239),(1024,163975),(1024,301225)]),([5,8,31,772,1748],[(1024,131239),(1024,163975),(1024,301187)]),([5,8,31,781,1748],[(1024,132263),(1024,164999),(1024,301187)]),([5,8,31,784,1748],[(1024,133289),(1024,139431),(1024,303271)])]
def t7 : BT := .nd (blockTree b8) [5,7,226,871,1604] (blockTree b9)
def b10 : List Row := [([5,8,31,1168,1232,1766],[(1024,98471),(1024,131239),(1024,132263),(1024,172168)]),([5,8,31,1232,1766],[(1024,131239),(1024,132263),(1024,163975),(1024,170113),(1024,172167)]),([5,8,31,1266,1748],[(1024,132263),(1024,133415),(1024,164999)]),([5,8,31,1266,1748,1766],[(1024,98471),(1024,98599),(1024,131239)]),([5,8,31,1266,1756],[(1024,132263),(1024,133415),(1024,164999)]),([5,8,31,1274,1748],[(1024,132263),(1024,133415),(1024,164999)]),([5,8,31,1274,1756],[(1024,99495),(1024,100647),(1024,132263),(1024,133415),(1024,164999)]),([5,8,31,1467,1936],[(1024,131240),(1024,163976),(1024,170280)]),([5,8,95,1168,1766],[(1024,131240),(1024,132264),(1024,163976),(1024,171137),(1024,172168)]),([5,8,144,768,1631],[(1024,138401),(1024,171137),(1024,295081)]),([5,8,224,1168,1600],[(1024,131240),(1024,138401),(1024,295051)])]
def b11 : List Row := [([5,8,226,1183,1604,1782],[(1024,131170),(1024,131171),(1024,295043)]),([5,8,226,1183,1748,1860],[(1024,98435)]),([5,8,255,416,1168],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,295051)]),([5,8,255,879,1631],[(1024,138401),(1024,171137),(1024,295051)]),([5,8,255,1168,1631],[(1024,131240),(1024,138401),(1024,295051)]),([5,8,255,1176,1631],[(1024,98472),(1024,105633),(1024,131240),(1024,138401),(1024,295051)]),([5,8,443,795,1168],[(1024,131240),(1024,138401),(1024,163976),(1024,166177),(1024,171137),(1024,295075)]),([5,8,447,799,1168],[(1024,131240),(1024,138401),(1024,163976),(1024,170273),(1024,171137),(1024,295079)]),([5,8,543,1604,1936],[(1024,131240),(1024,138401)]),([5,8,576,799,1168],[(1024,131240),(1024,138401),(1024,163976),(1024,170273),(1024,171137),(1024,295079)])]
def t8 : BT := .nd (blockTree b10) [5,8,226,1174,1604] (blockTree b11)
def t9 : BT := .nd t7 [5,8,31,912,1604] t8
def b12 : List Row := [([5,8,607,768,1168],[(1024,131240),(1024,163976),(1024,171137),(1024,172321),(1024,295081)]),([5,8,768,1168,1759,1766],[(1024,106658)]),([5,8,768,1631,1903],[(1024,138401),(1024,171137)]),([5,8,768,1744,2016],[(1024,131239),(1024,163975)]),([5,8,768,1748,1759,1766],[(1024,106658)]),([5,8,768,1748,2020],[(1024,131235),(1024,163971)]),([5,8,784,1168,1631],[(1024,131241),(1024,139425),(1024,141481),(1024,303265)]),([5,8,784,1183,1604],[(1024,139425),(1024,303271)]),([5,8,795,1168,1604],[(1024,131240),(1024,295075)]),([5,8,799,1168,1600],[(1024,131240),(1024,295079)]),([5,8,799,1172,1604],[(1024,131240),(1024,295043)])]
def b13 : List Row := [([5,8,799,1631,1936],[(1024,131240),(1024,139425),(1024,139431)]),([5,8,799,1748,1936],[(1024,138401),(1024,139431)]),([5,8,1024,1631,1936],[(1024,131240),(1024,138401)]),([5,8,1055,1604,1936],[(1024,131240),(1024,302219)]),([5,8,1168,1631,1766,1936],[(1024,98603),(1024,106658),(1024,131241)]),([5,8,1168,1631,1792],[(1024,138401),(1024,295051)]),([5,8,1266,1748,2016],[(1024,132263),(1024,164999)]),([5,12,31,768,1748],[(1024,131171),(1024,133217),(1024,163975),(1024,301225)]),([5,12,799,1168,1604],[(1024,131240),(1024,295011),(1024,297057)]),([5,14,226,1168,1604],[(1024,99489),(1024,131240),(1024,164961),(1024,295011)])]
def t10 : BT := .nd (blockTree b12) [5,8,799,1604,1680] (blockTree b13)
def b14 : List Row := [([5,16,31,776,1748],[(1024,98473),(1024,106657),(1024,163945),(1024,303271)]),([5,16,776,1168,1631],[(1024,98473),(1024,106657)]),([5,16,776,1183,1604],[(1024,106657),(1024,303271)]),([5,19,768,1168,1604],[(1024,98440),(1024,131176),(1024,138337),(1024,297065),(1024,303203)]),([5,23,226,1168,1612],[(1024,104617),(1024,106635),(1024,106663),(1024,131179)]),([5,23,226,1168,1631],[(1024,98443),(1024,104617),(1024,106658),(1024,106663),(1024,131179)]),([5,23,226,1176,1604],[(1024,105641),(1024,106664),(1024,303211)]),([5,23,234,1168,1604],[(1024,131176),(1024,301161),(1024,303207)]),([5,23,255,1168,1604],[(1024,98440),(1024,131176),(1024,138337),(1024,301161),(1024,303207)]),([5,23,443,768,1168],[(1024,98440),(1024,104745),(1024,105601),(1024,106791),(1024,131176),(1024,301161),(1024,303207)]),([5,23,768,879,1604],[(1024,98440),(1024,105601),(1024,138337),(1024,303207)])]
def b15 : List Row := [([5,23,768,1168,1623],[(1024,131176),(1024,301161),(1024,303201),(1024,303207)]),([5,23,768,1168,1748],[(1024,98440),(1024,301161),(1024,303207)]),([5,23,768,1604,1748],[(1024,98440),(1024,131175),(1024,131176),(1024,301161)]),([5,23,768,1604,1936],[(1024,98440),(1024,131176),(1024,303207)]),([5,23,791,1168,1604],[(1024,131176),(1024,295015),(1024,301161),(1024,303207)]),([5,23,1168,1279,1604],[(1024,98440),(1024,106791),(1024,131176),(1024,138337),(1024,303207)]),([5,23,1168,1604,1936],[(1024,98440),(1024,131176),(1024,131177),(1024,297065),(1024,301161),(1024,303207)]),([5,24,31,768,1748],[(1024,297129),(1024,301225),(1024,303271)]),([5,24,31,768,1756],[(1024,297129),(1024,301225),(1024,303271)]),([5,24,226,1183,1604],[(1024,170281),(1024,172327),(1024,301225),(1024,303271)])]
def t11 : BT := .nd (blockTree b14) [5,23,768,1168,1604] (blockTree b15)
def t12 : BT := .nd t10 [5,15,226,1176,1604] t11
def t13 : BT := .nd t9 [5,8,607,768,879] t12
def t14 : BT := .nd t6 [4,1168,1631,1800] t13
def b16 : List Row := [([5,24,768,1176,1631],[(1024,295081),(1024,303265)]),([5,24,768,1183,1604],[(1024,297129),(1024,301225),(1024,303271)]),([5,27,443,768,1176],[(1024,98472),(1024,163944),(1024,166185),(1024,171105),(1024,172323),(1024,297129),(1024,303267)]),([5,27,443,776,1168],[(1024,98473),(1024,131240),(1024,163945),(1024,166185),(1024,171137),(1024,172129),(1024,303267)]),([5,27,768,1168,1612],[(1024,98467),(1024,131240),(1024,163939),(1024,297129)]),([5,27,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,297129),(1024,303267)]),([5,27,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303267)]),([5,31,64,1168,1176,1766],[(1024,98471),(1024,98472),(1024,172136)]),([5,31,64,1176,1766],[(1024,98472),(1024,99496),(1024,163944),(1024,171105),(1024,172136)]),([5,31,72,1168,1766],[(1024,98471),(1024,131240),(1024,132264),(1024,163943),(1024,170081),(1024,171137),(1024,172135),(1024,172168)]),([5,31,98,871,1604],[(1024,164968),(1024,301225),(1024,303271),(1024,305249)])]
def b17 : List Row := [([5,31,103,768,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,170281),(1024,171105),(1024,303271)]),([5,31,103,776,1604],[(1024,106657),(1024,131240),(1024,163945),(1024,170281),(1024,171105),(1024,171137),(1024,303271)]),([5,31,103,1168,1604],[(1024,98473),(1024,106657),(1024,163945),(1024,170281),(1024,302247),(1024,303271)]),([5,31,103,1176,1604],[(1024,105633),(1024,163944),(1024,170281),(1024,301225),(1024,302247),(1024,303271)]),([5,31,111,776,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,170281),(1024,171137),(1024,303271)]),([5,31,111,1176,1604],[(1024,98603),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([5,31,144,443,776],[(1024,98473),(1024,131240),(1024,163945),(1024,171137),(1024,172129),(1024,303271)]),([5,31,144,776,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,303271)]),([5,31,152,443,768],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,172327),(1024,297129),(1024,301225),(1024,303271)]),([5,31,152,768,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,301225),(1024,303271)]),([5,31,192,768,1176,1604],[(1024,98472),(1024,303271)])]
def t15 : BT := .nd (blockTree b16) [5,31,98,1176,1604] (blockTree b17)
def b18 : List Row := [([5,31,224,1176,1604],[(1024,98472),(1024,295019),(1024,301225),(1024,303211),(1024,303271)]),([5,31,226,291,1176],[(1024,98603),(1024,100651),(1024,164971),(1024,170281),(1024,172327),(1024,301225),(1024,303271),(1024,305251)]),([5,31,226,299,1176],[(1024,98603),(1024,165003),(1024,170281),(1024,172327),(1024,301225),(1024,303271),(1024,305249)]),([5,31,226,416,1176],[(1024,98472),(1024,170281),(1024,171105),(1024,172327),(1024,295019),(1024,301225),(1024,303271)]),([5,31,226,424,1168],[(1024,98601),(1024,131240),(1024,171137),(1024,172327),(1024,295017),(1024,301225),(1024,303201)]),([5,31,226,435,1176],[(1024,98472),(1024,100520),(1024,164971),(1024,170281),(1024,171107),(1024,172327),(1024,301225),(1024,303271)]),([5,31,226,443,871],[(1024,98472),(1024,171105),(1024,171113),(1024,301225),(1024,303271),(1024,305249),(1024,305251)]),([5,31,226,443,1176],[(1024,98472),(1024,108841),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([5,31,226,447,1176],[(1024,98472),(1024,108841),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([5,31,226,576,1176],[(1024,98472),(1024,164971),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([5,31,226,580,871],[(1024,98472),(1024,164971),(1024,170281),(1024,171105),(1024,301225),(1024,303271)])]
def b19 : List Row := [([5,31,226,584,1168],[(1024,98471),(1024,131240),(1024,165003),(1024,170081),(1024,171137),(1024,172327),(1024,301225)]),([5,31,226,871,1604],[(1024,171105),(1024,301225),(1024,303211),(1024,303271)]),([5,31,226,871,1612],[(1024,164971),(1024,171105),(1024,171107),(1024,301225),(1024,303271)]),([5,31,226,871,1631],[(1024,171105),(1024,295019),(1024,301225),(1024,303266),(1024,303271)]),([5,31,226,871,1748],[(1024,165003),(1024,171105),(1024,301225),(1024,303271),(1024,305249)]),([5,31,226,871,1756],[(1024,98472),(1024,164971),(1024,171105),(1024,301225),(1024,303271),(1024,305251)]),([5,31,226,1168,1240,1604],[(1024,98471),(1024,98472),(1024,98603),(1024,303211)]),([5,31,226,1168,1604,1688],[(1024,98472),(1024,172136)]),([5,31,226,1168,1604,1790],[(1024,295011)]),([5,31,226,1168,1608],[(1024,98443),(1024,98471),(1024,131240),(1024,301225)])]
def t16 : BT := .nd (blockTree b18) [5,31,226,580,1176] (blockTree b19)
def t17 : BT := .nd t15 [5,31,200,768,1168,1604] t16
def b20 : List Row := [([5,31,226,1168,1623],[(1024,131240),(1024,295017),(1024,301225),(1024,303201)]),([5,31,226,1168,1748,1774],[(1024,98435)]),([5,31,226,1168,1756,1860],[(1024,98472)]),([5,31,226,1172,1612],[(1024,98435),(1024,131171),(1024,301225)]),([5,31,226,1176,1232,1604],[(1024,98472),(1024,303211),(1024,303271)]),([5,31,226,1176,1240,1604],[(1024,98472),(1024,99496),(1024,100651),(1024,303211),(1024,303271)]),([5,31,226,1176,1467],[(1024,98472),(1024,164971),(1024,170281),(1024,301225)]),([5,31,226,1176,1600],[(1024,98472),(1024,295019),(1024,301225),(1024,303211),(1024,303271)]),([5,31,226,1176,1604],[(1024,98472),(1024,301225),(1024,303211),(1024,303271)]),([5,31,226,1176,1604,1688],[(1024,99496),(1024,172136),(1024,303271)]),([5,31,226,1176,1604,1790],[(1024,99496),(1024,295079),(1024,303271)])]
def b21 : List Row := [([5,31,226,1176,1606],[(1024,98472),(1024,295019),(1024,301225),(1024,303211),(1024,303266),(1024,303271)]),([5,31,226,1176,1612],[(1024,100520),(1024,164971),(1024,301225),(1024,303271)]),([5,31,226,1176,1620],[(1024,98472),(1024,165003),(1024,301225),(1024,303271)]),([5,31,226,1176,1628],[(1024,100520),(1024,164971),(1024,301225),(1024,303271)]),([5,31,226,1176,1631],[(1024,98472),(1024,295019),(1024,301225),(1024,303266),(1024,303271)]),([5,31,226,1176,1732],[(1024,98603),(1024,301225),(1024,303211),(1024,303271)]),([5,31,226,1176,1748],[(1024,98603),(1024,165003),(1024,301225),(1024,303271)]),([5,31,226,1176,1756],[(1024,100651),(1024,164971),(1024,301225),(1024,303271)]),([5,31,226,1176,1756,1766],[(1024,98471),(1024,98475),(1024,303271)]),([5,31,226,1176,1756,1860],[(1024,99496),(1024,303271)])]
def t18 : BT := .nd (blockTree b20) [5,31,226,1176,1604,2012] (blockTree b21)
def b22 : List Row := [([5,31,226,1178,1604],[(1024,98472),(1024,99497),(1024,295019),(1024,303211),(1024,303271)]),([5,31,226,1180,1604],[(1024,98472),(1024,295011),(1024,301225),(1024,303203)]),([5,31,226,1232,1240,1604],[(1024,98472),(1024,98603),(1024,303211)]),([5,31,226,1240,1604],[(1024,98471),(1024,98472),(1024,99496),(1024,100651),(1024,171105),(1024,303211)]),([5,31,226,1266,1612,1748],[(1024,132195)]),([5,31,226,1274,1604,1756],[(1024,98472),(1024,99496),(1024,303271)]),([5,31,226,1274,1748],[(1024,98603),(1024,132263),(1024,165003),(1024,303271)]),([5,31,226,1274,1756],[(1024,99495),(1024,99499),(1024,100651),(1024,164971),(1024,303271)]),([5,31,230,1168,1612],[(1024,98443),(1024,98471),(1024,100521),(1024,131240)]),([5,31,230,1176,1604],[(1024,98472),(1024,295019),(1024,301225),(1024,303211),(1024,303271)]),([5,31,232,1168,1604],[(1024,131240),(1024,295015),(1024,301153),(1024,303207),(1024,303243),(1024,303271)])]
def b23 : List Row := [([5,31,234,443,1176],[(1024,98472),(1024,99496),(1024,164968),(1024,170281),(1024,171106),(1024,172327),(1024,301225),(1024,303271)]),([5,31,234,871,1604],[(1024,164968),(1024,171106),(1024,301225),(1024,303271)]),([5,31,234,879,1612],[(1024,99467),(1024,99495),(1024,164967),(1024,171137),(1024,301155)]),([5,31,234,1168,1606],[(1024,131240),(1024,295015),(1024,301153),(1024,303202)]),([5,31,234,1168,1612],[(1024,99467),(1024,99495),(1024,131240),(1024,164967),(1024,301155)]),([5,31,234,1168,1756],[(1024,99495),(1024,133419),(1024,164967),(1024,301155)]),([5,31,234,1170,1604],[(1024,131170),(1024,132193),(1024,295015),(1024,303207),(1024,303243),(1024,303271)]),([5,31,234,1176,1604],[(1024,99496),(1024,164968),(1024,301225),(1024,303271)]),([5,31,234,1176,1612],[(1024,105611),(1024,131240),(1024,301225),(1024,303271)]),([5,31,234,1176,1631],[(1024,99496),(1024,105634),(1024,295051),(1024,301225),(1024,303271)])]
def t19 : BT := .nd (blockTree b22) [5,31,234,435,1168] (blockTree b23)
def t20 : BT := .nd t18 [5,31,226,1176,1759] t19
def t21 : BT := .nd t17 [5,31,226,1168,1612,2004] t20
def b24 : List Row := [([5,31,234,1176,1756],[(1024,99495),(1024,133419),(1024,164968),(1024,301225),(1024,303271)]),([5,31,234,1266,1604,1748],[(1024,303271)]),([5,31,234,1266,1748],[(1024,132195),(1024,132263),(1024,133218),(1024,165003),(1024,303271)]),([5,31,242,1176,1604],[(1024,98472),(1024,165000),(1024,301225),(1024,303271)]),([5,31,247,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303271)]),([5,31,250,1176,1604],[(1024,99496),(1024,164968),(1024,301225),(1024,303271)]),([5,31,255,443,1176],[(1024,98472),(1024,163944),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([5,31,255,871,1604],[(1024,105633),(1024,163944),(1024,171105),(1024,301225),(1024,303271)]),([5,31,255,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)]),([5,31,255,1176,1612],[(1024,100520),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([5,31,255,1176,1631],[(1024,98472),(1024,105633),(1024,105639),(1024,301225),(1024,303265),(1024,303271)])]
def b25 : List Row := [([5,31,255,1176,1756],[(1024,100651),(1024,163944),(1024,301225),(1024,303271)]),([5,31,291,768,1176],[(1024,105633),(1024,163944),(1024,170281),(1024,172327),(1024,301225),(1024,303271)]),([5,31,291,768,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,172327),(1024,301225),(1024,303203)]),([5,31,299,768,1176],[(1024,138401),(1024,163976),(1024,170281),(1024,172327),(1024,301225),(1024,303271)]),([5,31,299,768,1612],[(1024,98435),(1024,131171),(1024,138401),(1024,163976),(1024,301225)]),([5,31,299,776,1168],[(1024,98473),(1024,163945),(1024,170281),(1024,172129),(1024,303271)]),([5,31,299,776,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,172129),(1024,303235)]),([5,31,416,768,1176],[(1024,98472),(1024,170281),(1024,171105),(1024,172327),(1024,295081),(1024,301225),(1024,303271)]),([5,31,416,776,1168],[(1024,98473),(1024,131240),(1024,170281),(1024,171137),(1024,172129),(1024,303271)]),([5,31,424,768,1168],[(1024,98601),(1024,131176),(1024,131240),(1024,171137),(1024,172327),(1024,295017),(1024,301225),(1024,303201)])]
def t22 : BT := .nd (blockTree b24) [5,31,255,1176,1748] (blockTree b25)
def b26 : List Row := [([5,31,435,768,1748],[(1024,131171),(1024,163976),(1024,301225)]),([5,31,435,776,1168],[(1024,100521),(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172131),(1024,303271)]),([5,31,443,768,871],[(1024,98472),(1024,163944),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([5,31,443,768,1176],[(1024,98472),(1024,163944),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([5,31,443,768,1756],[(1024,98471),(1024,98472),(1024,163944),(1024,301225),(1024,303271)]),([5,31,443,768,1944],[(1024,98472),(1024,163944),(1024,170281)]),([5,31,443,776,879],[(1024,98473),(1024,131240),(1024,163945),(1024,171137),(1024,172129),(1024,303271)]),([5,31,443,776,1168],[(1024,98473),(1024,131240),(1024,163945),(1024,170281),(1024,171137),(1024,172129),(1024,303271)]),([5,31,443,776,1176],[(1024,98472),(1024,106664),(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([5,31,443,776,1748],[(1024,98473),(1024,131239),(1024,131240),(1024,163945),(1024,303271)]),([5,31,443,776,1936],[(1024,131177),(1024,131240),(1024,163976),(1024,170281)])]
def b27 : List Row := [([5,31,443,799,1176],[(1024,98472),(1024,105641),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([5,31,443,1168,1271],[(1024,131240),(1024,163945),(1024,170281),(1024,172129),(1024,303271)]),([5,31,443,1168,1944],[(1024,98472),(1024,98473),(1024,163945),(1024,170281)]),([5,31,443,1176,1266],[(1024,98472),(1024,165000),(1024,170281),(1024,172327),(1024,303271)]),([5,31,443,1176,1274],[(1024,99496),(1024,164968),(1024,170281),(1024,172327),(1024,303271)]),([5,31,443,1176,1279],[(1024,98472),(1024,163944),(1024,170281),(1024,172323),(1024,172327),(1024,303271)]),([5,31,443,1176,1821],[(1024,98472),(1024,105641),(1024,301225)]),([5,31,443,1176,1936],[(1024,98603),(1024,163976),(1024,297129),(1024,301225)]),([5,31,443,1176,1944],[(1024,98472),(1024,98473),(1024,163944),(1024,170281),(1024,297129),(1024,301225)]),([5,31,447,768,1176],[(1024,98472),(1024,163944),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)])]
def t23 : BT := .nd (blockTree b26) [5,31,443,776,1944] (blockTree b27)
def t24 : BT := .nd t22 [5,31,435,768,1176] t23
def b28 : List Row := [([5,31,512,1176,1860],[(1024,98472),(1024,105633),(1024,163944),(1024,171105)]),([5,31,512,1604,1944],[(1024,98472),(1024,105633),(1024,163944),(1024,171105)]),([5,31,520,1168,1860],[(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([5,31,520,1604,1936],[(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([5,31,576,768,1176],[(1024,98472),(1024,163944),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([5,31,576,776,1168],[(1024,98473),(1024,131240),(1024,163945),(1024,170281),(1024,171137),(1024,172129),(1024,303271)]),([5,31,580,768,871],[(1024,98472),(1024,163944),(1024,170281),(1024,171105),(1024,172327)]),([5,31,580,768,1176],[(1024,98472),(1024,163944),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([5,31,580,776,879],[(1024,131240),(1024,163945),(1024,170281),(1024,171137),(1024,172129)]),([5,31,580,776,1168],[(1024,98473),(1024,131240),(1024,163945),(1024,170281),(1024,171137),(1024,172129),(1024,303271)]),([5,31,584,768,1168],[(1024,98471),(1024,131240),(1024,163943),(1024,170081),(1024,171137),(1024,172327),(1024,301225)])]
def b29 : List Row := [([5,31,768,871,1612],[(1024,163947),(1024,171105),(1024,171107),(1024,303271)]),([5,31,768,871,1631],[(1024,171105),(1024,301225),(1024,303265),(1024,303271)]),([5,31,768,871,1748],[(1024,163976),(1024,171105),(1024,301225),(1024,303271)]),([5,31,768,871,1756],[(1024,98472),(1024,163944),(1024,171105),(1024,301225),(1024,303271)]),([5,31,768,1168,1608],[(1024,98471),(1024,131240),(1024,163943),(1024,301225)]),([5,31,768,1168,1623],[(1024,131240),(1024,301225),(1024,303201),(1024,303207)]),([5,31,768,1172,1612],[(1024,98435),(1024,131171),(1024,163943),(1024,301225)]),([5,31,768,1176,1467],[(1024,98472),(1024,163944),(1024,166185),(1024,170281),(1024,301225)]),([5,31,768,1176,1600],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)]),([5,31,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)])]
def t25 : BT := .nd (blockTree b28) [5,31,768,871,1604] (blockTree b29)
def b30 : List Row := [([5,31,768,1176,1612],[(1024,100520),(1024,163947),(1024,301225),(1024,303271)]),([5,31,768,1176,1620],[(1024,98472),(1024,163944),(1024,301225),(1024,303271)]),([5,31,768,1176,1628],[(1024,100520),(1024,163947),(1024,301225),(1024,303271)]),([5,31,768,1176,1631],[(1024,98472),(1024,301225),(1024,303265),(1024,303271)]),([5,31,768,1176,1732],[(1024,297129),(1024,301225),(1024,303208),(1024,303271)]),([5,31,768,1176,1748],[(1024,163976),(1024,301225),(1024,303271)]),([5,31,768,1176,1748,1766],[(1024,98471),(1024,303271)]),([5,31,768,1176,1756],[(1024,163944),(1024,301225),(1024,303271)]),([5,31,768,1176,1756,1766],[(1024,98471),(1024,303271)]),([5,31,768,1176,1759],[(1024,301225),(1024,303265),(1024,303271)]),([5,31,768,1180,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303203)])]
def b31 : List Row := [([5,31,768,1274,1756],[(1024,99495),(1024,100647),(1024,104609),(1024,164967),(1024,170082)]),([5,31,768,1604,1688],[(1024,98472),(1024,163944),(1024,302249),(1024,305321)]),([5,31,768,1604,1756],[(1024,98471),(1024,98472),(1024,163944),(1024,301225)]),([5,31,768,1604,1895],[(1024,163944),(1024,171105),(1024,303271)]),([5,31,768,1604,1944],[(1024,98472),(1024,163944),(1024,303271)]),([5,31,768,1604,2012],[(1024,98472),(1024,163944),(1024,303203)]),([5,31,768,1612,1748],[(1024,98435),(1024,131171),(1024,163976)]),([5,31,768,1612,1944],[(1024,98472),(1024,100520),(1024,163947),(1024,303271)]),([5,31,768,1612,2004],[(1024,98435),(1024,131171),(1024,163976)]),([5,31,768,1631,1944],[(1024,98472),(1024,303265),(1024,303271)])]
def t26 : BT := .nd (blockTree b30) [5,31,768,1240,1604] (blockTree b31)
def t27 : BT := .nd t25 [5,31,768,1176,1606] t26
def t28 : BT := .nd t24 [5,31,447,776,1168] t27
def t29 : BT := .nd t21 [5,31,234,1176,1748] t28
def t30 : BT := .nd t14 [5,24,768,1168,1631] t29
def b32 : List Row := [([5,31,768,1748,1868],[(1024,98435),(1024,131171),(1024,138401),(1024,163976)]),([5,31,768,1748,1944],[(1024,98473),(1024,163976),(1024,170281),(1024,303271)]),([5,31,768,1756,1766],[(1024,98471),(1024,163943),(1024,170081),(1024,172131),(1024,301225)]),([5,31,768,1756,1860],[(1024,98471),(1024,98472),(1024,105633),(1024,163944),(1024,171105)]),([5,31,768,1756,1944],[(1024,100521),(1024,163944),(1024,170281),(1024,302249),(1024,303271)]),([5,31,770,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,296103),(1024,301225),(1024,303271)]),([5,31,772,1168,1612],[(1024,98471),(1024,131240),(1024,163943),(1024,301155)]),([5,31,772,1176,1604],[(1024,98472),(1024,163944),(1024,301225),(1024,303271)]),([5,31,773,1176,1604],[(1024,99496),(1024,164968),(1024,301225),(1024,303271)]),([5,31,776,871,1604],[(1024,138401),(1024,163976),(1024,171137),(1024,303271)]),([5,31,776,879,1604],[(1024,106657),(1024,163945),(1024,171137),(1024,303271)])]
def b33 : List Row := [([5,31,776,879,1631],[(1024,98473),(1024,106657),(1024,106663),(1024,171137),(1024,303271)]),([5,31,776,879,1748],[(1024,98473),(1024,131240),(1024,163945),(1024,171137),(1024,303271)]),([5,31,776,1168,1467],[(1024,98473),(1024,131240),(1024,163945),(1024,166185),(1024,170281)]),([5,31,776,1168,1600],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303271)]),([5,31,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303271)]),([5,31,776,1168,1606],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303271)]),([5,31,776,1168,1612],[(1024,100521),(1024,106663),(1024,131240),(1024,138401),(1024,163976),(1024,303271)]),([5,31,776,1168,1620],[(1024,98473),(1024,133288),(1024,163945),(1024,303271)]),([5,31,776,1168,1631],[(1024,98473),(1024,106657),(1024,106663),(1024,131240),(1024,303271)]),([5,31,776,1168,1732],[(1024,98473),(1024,106657),(1024,163945),(1024,303240),(1024,303271)]),([5,31,776,1168,1748],[(1024,98473),(1024,163945),(1024,303271)])]
def t31 : BT := .nd (blockTree b32) [5,31,776,879,1612] (blockTree b33)
def b34 : List Row := [([5,31,776,1168,1759],[(1024,98473),(1024,106657),(1024,106663),(1024,303271)]),([5,31,776,1172,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303235)]),([5,31,776,1176,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([5,31,776,1176,1612],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([5,31,776,1176,1631],[(1024,131240),(1024,301225),(1024,303265),(1024,303271)]),([5,31,776,1176,1748],[(1024,163976),(1024,301225),(1024,303271)]),([5,31,776,1176,1756],[(1024,163976),(1024,301225),(1024,303271)]),([5,31,776,1232,1604],[(1024,98473),(1024,106657),(1024,131239),(1024,131240),(1024,163945),(1024,171137),(1024,172129)]),([5,31,776,1266,1748],[(1024,98473),(1024,132263),(1024,164969),(1024,170114),(1024,303203)]),([5,31,776,1604,1680],[(1024,98473),(1024,131240),(1024,163945)]),([5,31,776,1604,1748],[(1024,98473),(1024,131239),(1024,131240),(1024,163945)])]
def b35 : List Row := [([5,31,776,1604,1903],[(1024,163945),(1024,171137),(1024,303271)]),([5,31,776,1604,1936],[(1024,131177),(1024,131240),(1024,163976),(1024,303271)]),([5,31,776,1604,1944],[(1024,98472),(1024,131240),(1024,163945),(1024,303271)]),([5,31,776,1604,2004],[(1024,131177),(1024,131240),(1024,163976),(1024,303235)]),([5,31,776,1604,2012],[(1024,98472),(1024,131240),(1024,163945),(1024,303235)]),([5,31,776,1612,1748],[(1024,131171),(1024,131239),(1024,131240),(1024,163976),(1024,301225)]),([5,31,776,1612,1756],[(1024,100521),(1024,131239),(1024,131240),(1024,163976)]),([5,31,776,1612,1936],[(1024,131240),(1024,163976),(1024,303271)]),([5,31,776,1612,1944],[(1024,100520),(1024,131240),(1024,163976),(1024,303271)]),([5,31,776,1631,1936],[(1024,131240),(1024,303265),(1024,303271)])]
def t32 : BT := .nd (blockTree b34) [5,31,776,1604,1756] (blockTree b35)
def t33 : BT := .nd t31 [5,31,776,1168,1756] t32
def b36 : List Row := [([5,31,776,1748,1766],[(1024,98473),(1024,106658),(1024,131239),(1024,164969),(1024,170113)]),([5,31,776,1748,1860],[(1024,131239),(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([5,31,776,1748,1868],[(1024,98435),(1024,131239),(1024,131240),(1024,163945),(1024,171137)]),([5,31,776,1748,1936],[(1024,98473),(1024,133225),(1024,163976),(1024,170281),(1024,303271)]),([5,31,776,1748,1944],[(1024,98473),(1024,163945),(1024,170281),(1024,303271)]),([5,31,780,1168,1604],[(1024,98473),(1024,131240),(1024,163945),(1024,303203)]),([5,31,781,1176,1604],[(1024,98472),(1024,165000),(1024,301225),(1024,303271)]),([5,31,784,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)]),([5,31,791,1168,1604],[(1024,131240),(1024,295015),(1024,301153),(1024,303207),(1024,303271)]),([5,31,792,1168,1604],[(1024,98473),(1024,106657),(1024,163945),(1024,303271)]),([5,31,792,1176,1604],[(1024,297129),(1024,301225),(1024,303271)])]
def b37 : List Row := [([5,31,799,1176,1604],[(1024,98472),(1024,295079),(1024,301225),(1024,303271)]),([5,31,799,1176,1612],[(1024,100520),(1024,295079),(1024,301225),(1024,303271)]),([5,31,799,1176,1631],[(1024,98472),(1024,301225),(1024,303271)]),([5,31,799,1176,1748],[(1024,295079),(1024,301225),(1024,303271)]),([5,31,799,1176,1756],[(1024,295079),(1024,301225),(1024,303271)]),([5,31,799,1604,1756],[(1024,98471),(1024,98472),(1024,301217),(1024,301225)]),([5,31,799,1604,1944],[(1024,98472),(1024,297128),(1024,303271)]),([5,31,799,1612,1748],[(1024,98435),(1024,131171)]),([5,31,871,1266,1604],[(1024,165000),(1024,171105),(1024,172327),(1024,303271)]),([5,31,871,1274,1604],[(1024,164968),(1024,171106),(1024,172327),(1024,303271)])]
def t34 : BT := .nd (blockTree b36) [5,31,799,871,1604] (blockTree b37)
def b38 : List Row := [([5,31,871,1604,1821],[(1024,105641),(1024,301225),(1024,303271)]),([5,31,871,1604,1936],[(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([5,31,871,1604,1944],[(1024,98472),(1024,98473),(1024,163944),(1024,297129),(1024,301225),(1024,303271)]),([5,31,879,1271,1604],[(1024,106657),(1024,163945),(1024,171137),(1024,172129),(1024,303271)]),([5,31,879,1604,1944],[(1024,98472),(1024,98473),(1024,131240),(1024,163945),(1024,303271)]),([5,31,896,1176,1604],[(1024,297129),(1024,301225),(1024,302179),(1024,302247),(1024,303211),(1024,303271)]),([5,31,904,1168,1604],[(1024,98473),(1024,106657),(1024,163945),(1024,302211),(1024,302247),(1024,303243),(1024,303271)]),([5,31,994,1604,1944],[(1024,98472),(1024,302187),(1024,302247)]),([5,31,1002,1604,1944],[(1024,98472),(1024,99496),(1024,164968),(1024,302247)]),([5,31,1024,1604,1944],[(1024,98472),(1024,163944),(1024,302247)]),([5,31,1032,1604,1936],[(1024,131240),(1024,163976),(1024,302247)])]
def b39 : List Row := [([5,31,1168,1266,1604,1774],[(1024,98434)]),([5,31,1168,1271,1604],[(1024,106657),(1024,131240),(1024,163945),(1024,172129),(1024,303271)]),([5,31,1168,1271,1612],[(1024,106663),(1024,131240),(1024,138401),(1024,163976),(1024,172131),(1024,303271)]),([5,31,1168,1271,1631],[(1024,106657),(1024,106663),(1024,172129),(1024,303271)]),([5,31,1168,1271,1748],[(1024,163945),(1024,172129),(1024,303271)]),([5,31,1168,1274,1612],[(1024,99495),(1024,100647),(1024,132264),(1024,164967)]),([5,31,1168,1274,1756],[(1024,99495),(1024,100647),(1024,164967)]),([5,31,1168,1604,1800],[(1024,98473),(1024,163945),(1024,303271)]),([5,31,1168,1604,1944],[(1024,98472),(1024,98473),(1024,163945),(1024,303271)]),([5,31,1168,1612,1813],[(1024,99495),(1024,138339),(1024,164967),(1024,301155)])]
def t35 : BT := .nd (blockTree b38) [5,31,1168,1256,1604] (blockTree b39)
def t36 : BT := .nd t34 [5,31,871,1279,1604] t35
def t37 : BT := .nd t33 [5,31,776,1631,1944] t36
def b40 : List Row := [([5,31,1168,1631,1944],[(1024,98472),(1024,98473),(1024,295081),(1024,303271)]),([5,31,1168,1748,1944],[(1024,98473),(1024,163945),(1024,303271)]),([5,31,1168,1756,1944],[(1024,98473),(1024,100521),(1024,163976),(1024,303271)]),([5,31,1176,1248,1604],[(1024,98472),(1024,172327),(1024,295079),(1024,303271)]),([5,31,1176,1250,1604],[(1024,98472),(1024,172327),(1024,303271)]),([5,31,1176,1266,1604],[(1024,98472),(1024,165000),(1024,172327),(1024,303271)]),([5,31,1176,1266,1612],[(1024,165000),(1024,172327),(1024,303271)]),([5,31,1176,1266,1631],[(1024,172327),(1024,295051),(1024,303271)]),([5,31,1176,1266,1748],[(1024,132263),(1024,133415),(1024,165000),(1024,172327),(1024,303271)]),([5,31,1176,1266,1756],[(1024,132263),(1024,165000),(1024,172327),(1024,303271)]),([5,31,1176,1271,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,172327),(1024,303271)])]
def b41 : List Row := [([5,31,1176,1274,1604,1766],[(1024,98472),(1024,98599),(1024,303271)]),([5,31,1176,1274,1612],[(1024,132264),(1024,164971),(1024,172327),(1024,303271)]),([5,31,1176,1274,1631],[(1024,172327),(1024,295019),(1024,303271)]),([5,31,1176,1274,1748],[(1024,133415),(1024,165000),(1024,172327),(1024,303271)]),([5,31,1176,1274,1756],[(1024,99495),(1024,100647),(1024,164968),(1024,172327),(1024,303271)]),([5,31,1176,1279,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,172327),(1024,303271)]),([5,31,1176,1279,1612],[(1024,163947),(1024,172327),(1024,303271)]),([5,31,1176,1279,1631],[(1024,172327),(1024,303265),(1024,303271)]),([5,31,1176,1279,1748],[(1024,163976),(1024,172327),(1024,303271)]),([5,31,1176,1279,1756],[(1024,163944),(1024,172327),(1024,303271)])]
def t38 : BT := .nd (blockTree b40) [5,31,1176,1274,1604] (blockTree b41)
def b42 : List Row := [([5,31,1176,1604,1792],[(1024,105633),(1024,163944),(1024,297129),(1024,301225),(1024,303271)]),([5,31,1176,1604,1813],[(1024,164968),(1024,301225),(1024,303271)]),([5,31,1176,1604,1821],[(1024,105641),(1024,301225),(1024,303271)]),([5,31,1176,1604,1823],[(1024,105633),(1024,105641),(1024,301225),(1024,303271)]),([5,31,1176,1604,1936],[(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([5,31,1176,1604,1944],[(1024,98472),(1024,98473),(1024,163944),(1024,297129),(1024,301225),(1024,303271)]),([5,31,1176,1604,1949],[(1024,164968),(1024,301225),(1024,303271)]),([5,31,1176,1604,1951],[(1024,297064),(1024,301225),(1024,303271)]),([5,31,1176,1612,1821],[(1024,164971),(1024,301225),(1024,303271)]),([5,31,1176,1612,1936],[(1024,131240),(1024,163976),(1024,297067),(1024,301225),(1024,303271)]),([5,31,1176,1612,1944],[(1024,100521),(1024,131240),(1024,163947),(1024,301225),(1024,303271)])]
def b43 : List Row := [([5,31,1176,1631,1936],[(1024,295019),(1024,295081),(1024,301224),(1024,301225),(1024,303271)]),([5,31,1176,1631,1944],[(1024,98473),(1024,295081),(1024,301224),(1024,301225),(1024,303271)]),([5,31,1176,1748,1821],[(1024,165003),(1024,301225),(1024,303271)]),([5,31,1176,1748,1936],[(1024,163976),(1024,301225),(1024,303271)]),([5,31,1176,1748,1944],[(1024,98473),(1024,163976),(1024,301225),(1024,303271)]),([5,31,1176,1756,1821],[(1024,164971),(1024,301225),(1024,303271)]),([5,31,1176,1756,1936],[(1024,163976),(1024,301225),(1024,303271)]),([5,31,1176,1756,1944],[(1024,100521),(1024,163944),(1024,301225),(1024,303271)]),([5,31,1183,1604,1944],[(1024,98472),(1024,98473),(1024,301225),(1024,303271)]),([5,31,1266,1274,1748],[(1024,132195),(1024,132263),(1024,164999),(1024,170114)])]
def t39 : BT := .nd (blockTree b42) [5,31,1176,1631,1821] (blockTree b43)
def t40 : BT := .nd t38 [5,31,1176,1604,1766,1944] t39
def b44 : List Row := [([5,31,1266,1604,1944],[(1024,98472),(1024,98473),(1024,164969),(1024,303271)]),([5,31,1266,1612,1748],[(1024,131171),(1024,132195),(1024,133415),(1024,165000),(1024,172327)]),([5,31,1266,1748,1756],[(1024,98471),(1024,132195),(1024,133415),(1024,164999),(1024,301187),(1024,303203)]),([5,31,1266,1748,2039],[(1024,132263),(1024,133415),(1024,164999)]),([5,31,1271,1604,1748],[(1024,131239),(1024,131240),(1024,163945),(1024,172129),(1024,303235)]),([5,31,1271,1604,1936],[(1024,131177),(1024,131240),(1024,163976),(1024,303271)]),([5,31,1271,1604,1944],[(1024,98472),(1024,98473),(1024,131240),(1024,163945),(1024,303271)]),([5,31,1274,1604,1756],[(1024,98472),(1024,99495),(1024,99496),(1024,100647),(1024,164968),(1024,172327)]),([5,31,1274,1604,1944],[(1024,98472),(1024,99496),(1024,164968),(1024,301225),(1024,303271)]),([5,31,1274,1756],[(1024,99495),(1024,100647),(1024,104610),(1024,303271)]),([5,31,1279,1604,1756],[(1024,98471),(1024,98472),(1024,163944),(1024,172327),(1024,303203)])]
def b45 : List Row := [([5,31,1279,1612,1748],[(1024,98435),(1024,131171),(1024,163976)]),([5,95,226,1168,1176,1604],[(1024,98472),(1024,98603),(1024,303211)]),([5,95,226,1176,1604],[(1024,98472),(1024,99496),(1024,100651),(1024,171105),(1024,303211)]),([5,95,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105)]),([5,95,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,172129)]),([5,159,226,1176,1604],[(1024,98603),(1024,105641),(1024,303211),(1024,303271)]),([5,224,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,303211)]),([5,224,1176,1604,2016],[(1024,98472),(1024,297064),(1024,297067),(1024,301225),(1024,303211),(1024,303271)]),([5,226,234,1183,1604,1748],[(1024,98435),(1024,131170),(1024,131239)]),([5,226,255,1176,1631],[(1024,98472),(1024,105633),(1024,105634),(1024,295019),(1024,303265),(1024,303266)])]
def t41 : BT := .nd (blockTree b44) [5,31,1279,1604,1944] (blockTree b45)
def b46 : List Row := [([5,226,443,1176,2016],[(1024,98472),(1024,106664),(1024,164968),(1024,164971),(1024,171105),(1024,295019),(1024,301225),(1024,303271)]),([5,226,768,1176,1604,1759],[]),([5,226,768,1176,1606],[(1024,98472),(1024,105633),(1024,163944),(1024,303211)]),([5,226,768,1178,1604],[(1024,98466),(1024,99489),(1024,163938),(1024,303211)]),([5,226,768,1183,1604,1756],[(1024,98471),(1024,303203)]),([5,226,768,1604,1756,1759],[]),([5,226,770,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,296043),(1024,297122),(1024,303211)]),([5,226,864,1176,1604],[(1024,105641),(1024,108841),(1024,172136),(1024,303211)]),([5,226,871,1183,1604],[(1024,105641),(1024,108841),(1024,303211),(1024,303271)]),([5,226,871,1604,2016],[(1024,164968),(1024,164971),(1024,171105),(1024,301225),(1024,303211),(1024,303271)]),([5,226,1055,1176,1604],[(1024,98472),(1024,301225),(1024,303211)])]
def b47 : List Row := [([5,226,1168,1183,1612,1860],[(1024,131171)]),([5,226,1168,1608,2016],[(1024,98443),(1024,98471),(1024,106663),(1024,131240),(1024,165000),(1024,165003),(1024,301225)]),([5,226,1168,1612,2024],[(1024,100488),(1024,100491),(1024,104617),(1024,106635),(1024,106663),(1024,131179)]),([5,226,1168,1631,2024],[(1024,98443),(1024,106663)]),([5,226,1176,1183,1604],[(1024,105641),(1024,108841),(1024,172136),(1024,303211)]),([5,226,1176,1183,1604,1766],[(1024,98471),(1024,98599),(1024,172136),(1024,295079),(1024,303211)]),([5,226,1176,1183,1604,1860],[(1024,303203),(1024,303211)]),([5,226,1176,1600,2016],[(1024,98472),(1024,164968),(1024,164971),(1024,295019),(1024,301225),(1024,303211),(1024,303271)]),([5,226,1176,1604,1631,1944],[(1024,98472),(1024,99496),(1024,295019)]),([5,226,1176,1604,2016],[(1024,98472),(1024,164968),(1024,164971),(1024,301225),(1024,303211),(1024,303271)])]
def t42 : BT := .nd (blockTree b46) [5,226,1168,1183,1604,1774] (blockTree b47)
def t43 : BT := .nd t41 [5,226,443,1176,1183] t42
def t44 : BT := .nd t40 [5,31,1266,1604,1756] t43
def t45 : BT := .nd t37 [5,31,1168,1612,1944] t44
def b48 : List Row := [([5,226,1176,1604,2032],[(1024,98472),(1024,138409),(1024,303211),(1024,303243)]),([5,226,1176,1604,2040],[(1024,105641),(1024,106664),(1024,303211)]),([5,226,1176,1612,2016],[(1024,164971),(1024,297067),(1024,303271)]),([5,226,1176,1631,2016],[(1024,295019),(1024,303271)]),([5,226,1176,1748,2016],[(1024,164971),(1024,165000),(1024,165003),(1024,297099),(1024,303271)]),([5,226,1176,1756,2016],[(1024,164968),(1024,164971),(1024,297067),(1024,303271)]),([5,226,1183,1266,1604,1612],[(1024,98434),(1024,98471),(1024,131171)]),([5,226,1183,1274,1604],[(1024,98599),(1024,108841),(1024,303211)]),([5,226,1183,1604,1756],[(1024,98471),(1024,105641),(1024,172136),(1024,303203)]),([5,226,1183,1604,1944],[(1024,98473),(1024,106658),(1024,303203),(1024,303211)]),([5,226,1183,1612,1748],[(1024,98435),(1024,131171),(1024,138409)])]
def b49 : List Row := [([5,232,1168,1604,2016],[(1024,131176),(1024,131240),(1024,297096),(1024,297099),(1024,301153),(1024,303207),(1024,303243),(1024,303271)]),([5,234,768,1168,1606],[(1024,98440),(1024,131176),(1024,138337),(1024,303202)]),([5,234,768,1170,1604],[(1024,98434),(1024,131170),(1024,132193),(1024,303207)]),([5,234,770,1168,1604],[(1024,98440),(1024,131176),(1024,138337),(1024,296039),(1024,297058),(1024,303207)]),([5,234,1168,1183,1612],[(1024,99467),(1024,104610),(1024,105603),(1024,138339)]),([5,234,1168,1604,2024],[(1024,99464),(1024,99467),(1024,131176),(1024,301161),(1024,303207)]),([5,234,1168,1612,2016],[(1024,99495),(1024,164967)]),([5,234,1176,1604,2016],[(1024,164968),(1024,303271)]),([5,234,1183,1266,1604],[(1024,98434),(1024,131170),(1024,132193),(1024,303243)]),([5,255,768,1176,1631],[(1024,98472),(1024,105633)]),([5,255,776,1168,1631],[(1024,106657),(1024,131240),(1024,138401)])]
def t46 : BT := .nd (blockTree b48) [5,232,768,1168,1604] (blockTree b49)
def b50 : List Row := [([5,255,1168,1176,1631],[(1024,98603),(1024,105633),(1024,138401),(1024,163976),(1024,295051),(1024,303265)]),([5,255,1168,1604,2024],[(1024,98440),(1024,303207)]),([5,255,1168,1631,2039],[(1024,131240),(1024,138401),(1024,295051)]),([5,255,1176,1604,1631],[(1024,98472),(1024,105633),(1024,297129)]),([5,255,1176,1604,2016],[(1024,163944),(1024,303271)]),([5,255,1176,1631],[(1024,98472),(1024,98603),(1024,105633),(1024,303265)]),([5,416,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,172323),(1024,297129),(1024,303211)]),([5,416,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,172129)]),([5,424,768,1168,1604],[(1024,98440),(1024,105601),(1024,106787),(1024,131176),(1024,138337),(1024,297065),(1024,303243)]),([5,443,768,799,1176],[(1024,98472),(1024,105633),(1024,163944),(1024,170281),(1024,171105),(1024,303271)]),([5,443,768,1168,2024],[(1024,98440),(1024,131176)])]
def b51 : List Row := [([5,443,768,1176,2016],[(1024,98472),(1024,163944)]),([5,443,776,1168,1631],[(1024,98473),(1024,106657),(1024,131240),(1024,303267)]),([5,443,776,1168,2016],[(1024,131240),(1024,163945)]),([5,512,799,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105)]),([5,520,799,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([5,543,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,172323),(1024,297129),(1024,303271)]),([5,543,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,172129)]),([5,768,791,1168,1604],[(1024,131176),(1024,138337),(1024,303207)]),([5,768,799,871,1604],[(1024,105633),(1024,171105),(1024,303271)]),([5,768,799,1176,1604],[(1024,98472),(1024,105633),(1024,303271)])]
def t47 : BT := .nd (blockTree b50) [5,443,768,1176,1631] (blockTree b51)
def t48 : BT := .nd t46 [5,255,799,1176,1604] t47
def b52 : List Row := [([5,768,799,1176,1631],[(1024,98472),(1024,303265),(1024,303271)]),([5,768,799,1176,1748],[(1024,138401),(1024,303271)]),([5,768,799,1176,1756],[(1024,105633),(1024,303271)]),([5,768,799,1604,1756],[(1024,98471),(1024,98472),(1024,105633)]),([5,768,799,1604,1944],[(1024,98472),(1024,303271)]),([5,768,799,1612,1748],[(1024,98435),(1024,131171),(1024,138401)]),([5,768,871,1604,1631],[(1024,105633),(1024,171105)]),([5,768,871,1604,2016],[(1024,163944),(1024,303271)]),([5,768,879,1604,2024],[(1024,98440),(1024,303207)]),([5,768,1024,1176,1631],[(1024,98472),(1024,105633),(1024,295081)]),([5,768,1032,1168,1631],[(1024,98443),(1024,131179),(1024,138401),(1024,295081)])]
def b53 : List Row := [([5,768,1168,1176,1631,1766],[(1024,98472),(1024,98603),(1024,106658),(1024,303265)]),([5,768,1168,1256,1604],[(1024,98440),(1024,131176),(1024,303207)]),([5,768,1168,1600,2024],[(1024,98440),(1024,303207)]),([5,768,1168,1604,1623],[(1024,131176),(1024,138337),(1024,297065)]),([5,768,1168,1604,2024],[(1024,98440),(1024,303207)]),([5,768,1168,1604,2028],[(1024,98440),(1024,303203)]),([5,768,1168,1608,2016],[(1024,98471),(1024,163943)]),([5,768,1168,1612,2020],[(1024,98467),(1024,163939)]),([5,768,1168,1748,2024],[(1024,98440),(1024,303207)]),([5,768,1176,1183,1604,1766],[(1024,98471),(1024,106658)])]
def t49 : BT := .nd (blockTree b52) [5,768,1055,1176,1604] (blockTree b53)
def b54 : List Row := [([5,768,1176,1600,2016],[(1024,163944),(1024,303271)]),([5,768,1176,1604,1631],[(1024,98472),(1024,105633),(1024,297129)]),([5,768,1176,1604,1823],[(1024,98472),(1024,105633),(1024,303211)]),([5,768,1176,1604,1887],[(1024,98472),(1024,105633),(1024,303211)]),([5,768,1176,1604,2016],[(1024,163944),(1024,303271)]),([5,768,1176,1604,2020],[(1024,163944),(1024,303267)]),([5,768,1176,1612,2016],[(1024,163944),(1024,163947),(1024,303271)]),([5,768,1176,1631,1766],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,172139),(1024,303211),(1024,303265),(1024,303266)]),([5,768,1176,1631,1860],[(1024,98472),(1024,105633)]),([5,768,1176,1631,2016],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303265),(1024,303271)]),([5,768,1176,1748,2016],[(1024,163944),(1024,163976),(1024,303271)])]
def b55 : List Row := [([5,768,1604,1631,1756],[(1024,98472),(1024,105633)]),([5,768,1604,1631,1944],[(1024,98472),(1024,105633)]),([5,768,1604,1748,2024],[(1024,98440),(1024,131175),(1024,131176)]),([5,768,1604,1756,2016],[(1024,98471),(1024,98472),(1024,163944)]),([5,768,1604,1936,2024],[(1024,98440),(1024,131176)]),([5,768,1604,1944,2016],[(1024,98472),(1024,163944)]),([5,768,1612,1631,1748],[(1024,98435),(1024,131171),(1024,138401)]),([5,768,1612,1748,2016],[(1024,98435),(1024,131171),(1024,163976)]),([5,776,799,1168,1612],[(1024,106663),(1024,131240),(1024,138401)]),([5,776,799,1168,1631],[(1024,106657),(1024,106663),(1024,131240)])]
def t50 : BT := .nd (blockTree b54) [5,768,1176,1756,2016] (blockTree b55)
def t51 : BT := .nd t49 [5,768,1176,1248,1604] t50
def t52 : BT := .nd t48 [5,768,799,1176,1612] t51
def b56 : List Row := [([5,776,799,1604,1936],[(1024,131177),(1024,303271)]),([5,776,879,1604,1631],[(1024,106657),(1024,171137)]),([5,776,879,1604,2016],[(1024,163945),(1024,303271)]),([5,776,1024,1168,1631],[(1024,98473),(1024,106657),(1024,131240)]),([5,776,1055,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,303243)]),([5,776,1168,1600,2016],[(1024,163945),(1024,303271)]),([5,776,1168,1604,1631],[(1024,98473),(1024,106657),(1024,131240)]),([5,776,1168,1604,2016],[(1024,163945),(1024,303271)]),([5,776,1168,1604,2020],[(1024,163945),(1024,303267)]),([5,776,1168,1612,1631],[(1024,100521),(1024,106657),(1024,131240),(1024,138401)]),([5,776,1168,1612,2016],[(1024,163945),(1024,163976),(1024,303271)])]
def b57 : List Row := [([5,776,1168,1631,1860],[(1024,106657),(1024,131240),(1024,138401)]),([5,776,1168,1631,1868],[(1024,106657),(1024,131240),(1024,138401)]),([5,776,1168,1631,2016],[(1024,98473),(1024,106657),(1024,106663),(1024,131240),(1024,163945),(1024,303271)]),([5,776,1168,1748,2016],[(1024,163945),(1024,303271)]),([5,776,1176,1604,1631],[(1024,131240),(1024,138401),(1024,297129)]),([5,776,1176,1604,2016],[(1024,163944),(1024,163945),(1024,163976),(1024,303271)]),([5,776,1604,1631,1748],[(1024,106657),(1024,131240)]),([5,776,1604,1631,1936],[(1024,131177),(1024,131240),(1024,138401)]),([5,776,1604,1631,1944],[(1024,98472),(1024,106657),(1024,131240)]),([5,776,1604,1748,2016],[(1024,131239),(1024,131240),(1024,163945)])]
def t53 : BT := .nd (blockTree b56) [5,776,1168,1631,1766] (blockTree b57)
def b58 : List Row := [([5,776,1604,1944,2016],[(1024,131240),(1024,163944),(1024,163945)]),([5,799,994,1176,1604],[(1024,98472),(1024,296043),(1024,296103),(1024,301218)]),([5,799,1176,1183,1604],[(1024,105641),(1024,295079),(1024,303271)]),([5,799,1176,1279,1604],[(1024,98472),(1024,105633),(1024,303271)]),([5,799,1176,1604,1936],[(1024,98472),(1024,138401),(1024,297128),(1024,303271)]),([5,799,1176,1604,1944],[(1024,98472),(1024,105633),(1024,297128),(1024,303271)]),([5,799,1176,1604,2016],[(1024,98472),(1024,163944),(1024,297064),(1024,303271)]),([5,1168,1271,1604,1631],[(1024,106657),(1024,131240),(1024,172129)]),([5,1168,1271,1604,2016],[(1024,163945),(1024,303271)]),([5,1168,1279,1604,2024],[(1024,98440),(1024,303207)]),([5,1168,1604,1631,1944],[(1024,98472),(1024,98473),(1024,106657)])]
def b59 : List Row := [([5,1168,1604,1944,2016],[(1024,98473),(1024,163944),(1024,163945)]),([5,1176,1183,1604,1821],[(1024,105641),(1024,301225),(1024,303211)]),([5,1176,1266,1604,2016],[(1024,164968),(1024,165000),(1024,303271)]),([5,1176,1274,1604,2016],[(1024,164968),(1024,303271)]),([5,1176,1279,1604,1631],[(1024,98472),(1024,105633),(1024,172323),(1024,303211)]),([5,1176,1279,1604,2016],[(1024,163944),(1024,303271)]),([5,1176,1604,1631,1936],[(1024,138401),(1024,295081),(1024,297128),(1024,297129)]),([5,1176,1604,1631,1944],[(1024,98472),(1024,105633),(1024,295081),(1024,297128),(1024,297129)]),([5,1176,1604,1821,2016],[(1024,105641),(1024,163944),(1024,164968),(1024,164971),(1024,301225),(1024,303271)]),([5,1176,1604,1936,2016],[(1024,163944),(1024,163976),(1024,301225)])]
def t54 : BT := .nd (blockTree b58) [5,1168,1604,1936,2024] (blockTree b59)
def t55 : BT := .nd t53 [5,776,1604,1936,2016] t54
def b60 : List Row := [([6,0,31,226,1176,1604],[(1024,98472),(1024,301225),(1024,303211),(1024,303271)]),([6,0,31,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)]),([6,0,31,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303271)]),([6,2,31,226,1176,1604],[(1024,98472),(1024,295019),(1024,301225),(1024,303211),(1024,303271)]),([6,2,31,234,1168,1604],[(1024,131240),(1024,295015),(1024,301153),(1024,303207),(1024,303243),(1024,303271)]),([6,2,31,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)]),([6,2,31,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303271)]),([6,2,226,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,303211)]),([6,2,234,768,1168,1604],[(1024,98440),(1024,131176),(1024,138337),(1024,303207)]),([6,4,8,31,768,1748],[(1024,131239),(1024,163975),(1024,301225)]),([6,4,8,799,1168,1604],[(1024,131240),(1024,295079)])]
def b61 : List Row := [([6,4,31,226,1176,1604],[(1024,98472),(1024,295019),(1024,301225),(1024,303211),(1024,303271)]),([6,4,31,768,1168,1612],[(1024,98471),(1024,131240),(1024,163943),(1024,301225)]),([6,4,31,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)]),([6,4,31,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303271)]),([6,6,8,226,1168,1604],[(1024,131240),(1024,138401),(1024,295051)]),([6,8,15,226,879,1604],[(1024,138409),(1024,171145),(1024,303243)]),([6,8,15,226,1168,1604],[(1024,138409),(1024,139432),(1024,303243)]),([6,8,16,31,768,1748],[(1024,297129),(1024,301225),(1024,303271)]),([6,8,16,226,1183,1604],[(1024,170281),(1024,172327),(1024,301225),(1024,303271)]),([6,8,16,768,1168,1631],[(1024,295081),(1024,303265)])]
def t56 : BT := .nd (blockTree b60) [6,4,31,226,1168,1612] (blockTree b61)
def b62 : List Row := [([6,8,23,226,1168,1604],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,8,23,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303207),(1024,303271)]),([6,8,27,443,768,1168],[(1024,131240),(1024,163976),(1024,166185),(1024,171137),(1024,172323),(1024,297129),(1024,303267)]),([6,8,27,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,297129),(1024,303267)]),([6,8,31,64,1168,1766],[(1024,131240),(1024,132264),(1024,163976),(1024,171137),(1024,172168)]),([6,8,31,98,879,1604],[(1024,165000),(1024,301225),(1024,303271),(1024,305281)]),([6,8,31,98,1168,1604],[(1024,131371),(1024,165000),(1024,301225),(1024,303271)]),([6,8,31,111,768,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,170281),(1024,171137),(1024,303271)]),([6,8,31,111,1168,1604],[(1024,138401),(1024,163976),(1024,170281),(1024,172327),(1024,301225),(1024,302247),(1024,303271)]),([6,8,31,144,443,768],[(1024,131240),(1024,138401),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,297129),(1024,301225),(1024,303271)]),([6,8,31,144,768,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,301225),(1024,303271)])]
def b63 : List Row := [([6,8,31,224,1168,1604],[(1024,131240),(1024,295051),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,299,1168],[(1024,131371),(1024,133419),(1024,165003),(1024,170281),(1024,172327),(1024,301225),(1024,303271),(1024,305283)]),([6,8,31,226,416,1168],[(1024,131240),(1024,170281),(1024,171137),(1024,172327),(1024,295051),(1024,301225),(1024,303271)]),([6,8,31,226,435,1168],[(1024,131240),(1024,141609),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,226,443,879],[(1024,131240),(1024,171137),(1024,171145),(1024,301225),(1024,303271),(1024,305281),(1024,305283)]),([6,8,31,226,443,1168],[(1024,131240),(1024,141609),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,226,443,1176],[(1024,98472),(1024,131240),(1024,141609),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,226,447,1168],[(1024,131240),(1024,141609),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,226,576,1168],[(1024,131240),(1024,165003),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,226,580,879],[(1024,131240),(1024,165003),(1024,170281),(1024,171137),(1024,301225),(1024,303271)])]
def t57 : BT := .nd (blockTree b62) [6,8,31,192,768,1168,1604] (blockTree b63)
def t58 : BT := .nd t56 [6,8,16,768,1183,1604] t57
def t59 : BT := .nd t55 [5,1176,1604,1944,2016] t58
def t60 : BT := .nd t52 [5,776,799,1176,1604] t59
def t61 : BT := .nd t45 [5,226,1176,1604,2024] t60
def t62 : BT := .nd t30 [5,31,768,1748,1756,1766] t61
def b64 : List Row := [([6,8,31,226,871,1604],[(1024,171137),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,879,1604],[(1024,171137),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,879,1612],[(1024,171137),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,879,1631],[(1024,171137),(1024,295051),(1024,301225),(1024,303266),(1024,303271)]),([6,8,31,226,879,1748],[(1024,131240),(1024,165003),(1024,171137),(1024,301225),(1024,303271),(1024,305283)]),([6,8,31,226,1168,1232,1604],[(1024,131240),(1024,132264),(1024,133419),(1024,303243),(1024,303271)]),([6,8,31,226,1168,1467],[(1024,131240),(1024,165003),(1024,170281),(1024,301225)]),([6,8,31,226,1168,1600],[(1024,131240),(1024,295051),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,1168,1604],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,1168,1604,1680],[(1024,98603),(1024,132264),(1024,172168),(1024,303271)]),([6,8,31,226,1168,1604,1782],[(1024,98471),(1024,98472),(1024,98599),(1024,132264),(1024,295079),(1024,303271)])]
def b65 : List Row := [([6,8,31,226,1168,1606],[(1024,131240),(1024,295051),(1024,301225),(1024,303243),(1024,303266),(1024,303271)]),([6,8,31,226,1168,1612],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,1168,1620],[(1024,133288),(1024,165003),(1024,301225),(1024,303271)]),([6,8,31,226,1168,1631],[(1024,131240),(1024,295051),(1024,301225),(1024,303266),(1024,303271)]),([6,8,31,226,1168,1732],[(1024,131371),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,1168,1748],[(1024,133419),(1024,165003),(1024,301225),(1024,303271)]),([6,8,31,226,1168,1748,1766],[(1024,98471),(1024,98599),(1024,98603),(1024,131239),(1024,131243),(1024,303271)]),([6,8,31,226,1168,1748,1860],[(1024,98603),(1024,132264),(1024,303203),(1024,303271)]),([6,8,31,226,1168,1756],[(1024,133419),(1024,165003),(1024,301225),(1024,303271)]),([6,8,31,226,1168,1759],[(1024,131371),(1024,295051),(1024,301225),(1024,303266),(1024,303271)]),([6,8,31,226,1170,1604],[(1024,131240),(1024,132265),(1024,295051),(1024,303243),(1024,303271)])]
def t63 : BT := .nd (blockTree b64) [6,8,31,226,1168,1604,2004] (blockTree b65)
def b66 : List Row := [([6,8,31,226,1176,1604],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,1176,1612],[(1024,100520),(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,226,1176,1631],[(1024,98472),(1024,131240),(1024,295051),(1024,301225),(1024,303266),(1024,303271)]),([6,8,31,226,1176,1748],[(1024,133419),(1024,165003),(1024,301225),(1024,303271)]),([6,8,31,226,1176,1756],[(1024,100651),(1024,133419),(1024,165003),(1024,301225),(1024,303271)]),([6,8,31,226,1232,1604],[(1024,131239),(1024,131240),(1024,132264),(1024,133419),(1024,171137),(1024,303243)]),([6,8,31,226,1266,1604,1748],[(1024,98472),(1024,98603),(1024,131240),(1024,132264),(1024,303271)]),([6,8,31,226,1266,1748],[(1024,132263),(1024,132267),(1024,133419),(1024,165003),(1024,303271)]),([6,8,31,230,1168,1604],[(1024,131240),(1024,295051),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,234,443,1168],[(1024,131240),(1024,141609),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,234,879,1604],[(1024,171137),(1024,301225),(1024,303243),(1024,303271)])]
def b67 : List Row := [([6,8,31,234,1168,1612],[(1024,99495),(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,234,1168,1631],[(1024,131240),(1024,295051),(1024,301225),(1024,303266),(1024,303271)]),([6,8,31,234,1168,1748],[(1024,133419),(1024,165003),(1024,301225),(1024,303271)]),([6,8,31,234,1176,1604],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,8,31,242,1168,1604],[(1024,132264),(1024,165000),(1024,301225),(1024,303271)]),([6,8,31,255,443,1168],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,255,879,1604],[(1024,138401),(1024,163976),(1024,171137),(1024,301225),(1024,303271)]),([6,8,31,255,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,255,1168,1612],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,255,1168,1631],[(1024,131240),(1024,138401),(1024,138407),(1024,301225),(1024,303265),(1024,303271)])]
def t64 : BT := .nd (blockTree b66) [6,8,31,234,1168,1604] (blockTree b67)
def t65 : BT := .nd t63 [6,8,31,226,1172,1604] t64
def b68 : List Row := [([6,8,31,255,1176,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,299,768,1168],[(1024,138401),(1024,163976),(1024,170281),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,299,768,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303235)]),([6,8,31,416,768,1168],[(1024,131240),(1024,170281),(1024,171137),(1024,172327),(1024,295081),(1024,301225),(1024,303271)]),([6,8,31,435,768,1168],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,443,768,879],[(1024,131240),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,443,768,1168],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,443,768,1176],[(1024,98472),(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,443,768,1748],[(1024,131239),(1024,131240),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,443,768,1936],[(1024,131240),(1024,163976),(1024,170281)]),([6,8,31,443,776,1168],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)])]
def b69 : List Row := [([6,8,31,443,1168,1266],[(1024,132264),(1024,165000),(1024,170281),(1024,172327),(1024,303271)]),([6,8,31,443,1168,1279],[(1024,131240),(1024,163976),(1024,170281),(1024,172323),(1024,172327),(1024,303271)]),([6,8,31,443,1168,1821],[(1024,131240),(1024,138409),(1024,301225)]),([6,8,31,443,1168,1936],[(1024,131240),(1024,131241),(1024,163976),(1024,170281),(1024,297129),(1024,301225)]),([6,8,31,447,768,1168],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,512,1168,1860],[(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([6,8,31,512,1604,1936],[(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([6,8,31,576,768,1168],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,8,31,580,768,879],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327)]),([6,8,31,580,768,1168],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)])]
def t66 : BT := .nd (blockTree b68) [6,8,31,443,799,1168] (blockTree b69)
def b70 : List Row := [([6,8,31,768,879,1604],[(1024,138401),(1024,163976),(1024,171137),(1024,303271)]),([6,8,31,768,879,1612],[(1024,138401),(1024,163976),(1024,171137),(1024,303271)]),([6,8,31,768,879,1631],[(1024,171137),(1024,301225),(1024,303265),(1024,303271)]),([6,8,31,768,879,1748],[(1024,131240),(1024,163976),(1024,171137),(1024,301225),(1024,303271)]),([6,8,31,768,1168,1467],[(1024,131240),(1024,163976),(1024,166185),(1024,170281),(1024,301225)]),([6,8,31,768,1168,1600],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,768,1168,1606],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,768,1168,1612],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,768,1168,1620],[(1024,133288),(1024,163979),(1024,301225),(1024,303271)]),([6,8,31,768,1168,1631],[(1024,131240),(1024,301225),(1024,303265),(1024,303271)])]
def b71 : List Row := [([6,8,31,768,1168,1748],[(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,768,1168,1748,1766],[(1024,98471),(1024,106658),(1024,131239),(1024,303271)]),([6,8,31,768,1168,1756],[(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,768,1168,1759],[(1024,301225),(1024,303265),(1024,303271)]),([6,8,31,768,1172,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303235)]),([6,8,31,768,1176,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,768,1176,1612],[(1024,100520),(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,768,1176,1631],[(1024,98472),(1024,131240),(1024,301225),(1024,303265),(1024,303271)]),([6,8,31,768,1176,1748],[(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,768,1176,1756],[(1024,163976),(1024,301225),(1024,303271)])]
def t67 : BT := .nd (blockTree b70) [6,8,31,768,1168,1732] (blockTree b71)
def t68 : BT := .nd t66 [6,8,31,768,871,1604] t67
def t69 : BT := .nd t65 [6,8,31,255,1168,1748] t68
def b72 : List Row := [([6,8,31,768,1266,1748],[(1024,132263),(1024,133415),(1024,137377),(1024,137378),(1024,164999),(1024,170114)]),([6,8,31,768,1604,1680],[(1024,131240),(1024,163976),(1024,302249),(1024,305321)]),([6,8,31,768,1604,1748],[(1024,131239),(1024,131240),(1024,163976),(1024,301225)]),([6,8,31,768,1604,1756],[(1024,98472),(1024,131239),(1024,131240),(1024,163976),(1024,301225)]),([6,8,31,768,1604,1903],[(1024,163976),(1024,171137),(1024,303271)]),([6,8,31,768,1604,1936],[(1024,131240),(1024,163976),(1024,303271)]),([6,8,31,768,1604,1944],[(1024,98472),(1024,131240),(1024,163976),(1024,303271)]),([6,8,31,768,1604,2004],[(1024,131240),(1024,163976),(1024,303235)]),([6,8,31,768,1612,1748],[(1024,131171),(1024,131239),(1024,131240),(1024,163976),(1024,301225)]),([6,8,31,768,1612,1756],[(1024,131239),(1024,131240),(1024,163976),(1024,301225)]),([6,8,31,768,1612,1936],[(1024,131240),(1024,163976),(1024,303271)])]
def b73 : List Row := [([6,8,31,768,1748,1766],[(1024,131239),(1024,163975),(1024,170113),(1024,172163),(1024,301225)]),([6,8,31,768,1748,1860],[(1024,131239),(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([6,8,31,768,1748,1936],[(1024,133289),(1024,138401),(1024,163976),(1024,170281),(1024,302249),(1024,303271)]),([6,8,31,770,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,296103),(1024,301225),(1024,303271)]),([6,8,31,772,1168,1604],[(1024,131240),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,776,879,1604],[(1024,138401),(1024,163976),(1024,171137),(1024,303271)]),([6,8,31,776,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,776,1168,1612],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,776,1168,1631],[(1024,131240),(1024,301225),(1024,303265),(1024,303271)]),([6,8,31,776,1168,1748],[(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,776,1176,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)])]
def t70 : BT := .nd (blockTree b72) [6,8,31,768,1631,1936] (blockTree b73)
def b74 : List Row := [([6,8,31,776,1604,1936],[(1024,131240),(1024,163976),(1024,303271)]),([6,8,31,776,1604,1944],[(1024,131240),(1024,163976),(1024,303271)]),([6,8,31,781,1168,1604],[(1024,132264),(1024,165000),(1024,301225),(1024,303271)]),([6,8,31,784,1168,1604],[(1024,297129),(1024,301225),(1024,303271)]),([6,8,31,799,879,1604],[(1024,171137),(1024,295079),(1024,303271)]),([6,8,31,799,1168,1604],[(1024,131240),(1024,295079),(1024,301225),(1024,303271)]),([6,8,31,799,1168,1612],[(1024,131240),(1024,295079),(1024,301225),(1024,303271)]),([6,8,31,799,1168,1631],[(1024,131240),(1024,301225),(1024,303271)]),([6,8,31,799,1168,1748],[(1024,295079),(1024,301225),(1024,303271)]),([6,8,31,799,1176,1604],[(1024,131240),(1024,295079),(1024,301225),(1024,303271)]),([6,8,31,799,1604,1748],[(1024,131239),(1024,131240),(1024,301217),(1024,301225)])]
def b75 : List Row := [([6,8,31,879,1266,1604],[(1024,165000),(1024,171138),(1024,172327),(1024,303271)]),([6,8,31,879,1279,1604],[(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,303271)]),([6,8,31,879,1604,1821],[(1024,138409),(1024,301225),(1024,303271)]),([6,8,31,879,1604,1936],[(1024,131240),(1024,131241),(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([6,8,31,896,1168,1604],[(1024,297129),(1024,301225),(1024,302211),(1024,302247),(1024,303243),(1024,303271)]),([6,8,31,994,1604,1936],[(1024,131240),(1024,302219),(1024,302247)]),([6,8,31,1024,1604,1936],[(1024,131240),(1024,163976),(1024,302247)]),([6,8,31,1168,1248,1604],[(1024,131240),(1024,172327),(1024,295079),(1024,303271)]),([6,8,31,1168,1250,1604],[(1024,131240),(1024,172327),(1024,303271)]),([6,8,31,1168,1266,1604],[(1024,132264),(1024,165000),(1024,172327),(1024,303271)])]
def t71 : BT := .nd (blockTree b74) [6,8,31,799,1604,1936] (blockTree b75)
def t72 : BT := .nd t70 [6,8,31,776,1604,1748] t71
def b76 : List Row := [([6,8,31,1168,1266,1612],[(1024,132264),(1024,165000),(1024,172327),(1024,303271)]),([6,8,31,1168,1266,1631],[(1024,172327),(1024,295051),(1024,303271)]),([6,8,31,1168,1266,1748],[(1024,132263),(1024,133415),(1024,165000),(1024,172327),(1024,303271)]),([6,8,31,1168,1271,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,172327),(1024,303271)]),([6,8,31,1168,1274,1604],[(1024,132264),(1024,165000),(1024,172327),(1024,303271)]),([6,8,31,1168,1279,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,172327),(1024,303271)]),([6,8,31,1168,1279,1612],[(1024,131240),(1024,138401),(1024,163976),(1024,172327),(1024,303271)]),([6,8,31,1168,1279,1631],[(1024,172327),(1024,303265),(1024,303271)]),([6,8,31,1168,1279,1748],[(1024,163976),(1024,172327),(1024,303271)]),([6,8,31,1168,1604,1766,1936],[(1024,98471),(1024,98603),(1024,106658),(1024,131241),(1024,139426),(1024,301225)]),([6,8,31,1168,1604,1792],[(1024,138401),(1024,163976),(1024,297129),(1024,301225),(1024,303271)])]
def b77 : List Row := [([6,8,31,1168,1604,1821],[(1024,138409),(1024,301225),(1024,303271)]),([6,8,31,1168,1604,1823],[(1024,138401),(1024,138409),(1024,301225),(1024,303271)]),([6,8,31,1168,1604,1936],[(1024,131240),(1024,131241),(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([6,8,31,1168,1604,1944],[(1024,98473),(1024,131240),(1024,131241),(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([6,8,31,1168,1604,1949],[(1024,165000),(1024,301225),(1024,303271)]),([6,8,31,1168,1604,1951],[(1024,297096),(1024,301225),(1024,303271)]),([6,8,31,1168,1612,1821],[(1024,138409),(1024,301225),(1024,303271)]),([6,8,31,1168,1612,1936],[(1024,131240),(1024,131241),(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([6,8,31,1168,1631,1821],[(1024,295051),(1024,296105),(1024,301225),(1024,303271)]),([6,8,31,1168,1631,1936],[(1024,131241),(1024,295081),(1024,301224),(1024,301225),(1024,303271)])]
def t73 : BT := .nd (blockTree b76) [6,8,31,1168,1604,1813] (blockTree b77)
def b78 : List Row := [([6,8,31,1168,1748,1936],[(1024,133289),(1024,163976),(1024,301225),(1024,303271)]),([6,8,31,1176,1266,1604],[(1024,132264),(1024,165000),(1024,172327),(1024,303271)]),([6,8,31,1176,1274,1604],[(1024,132264),(1024,165000),(1024,172327),(1024,303271)]),([6,8,31,1176,1279,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,172327),(1024,303271)]),([6,8,31,1176,1604,1821],[(1024,138409),(1024,301225),(1024,303271)]),([6,8,31,1176,1604,1936],[(1024,131240),(1024,131241),(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([6,8,31,1176,1604,1944],[(1024,131240),(1024,131241),(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([6,8,31,1183,1604,1936],[(1024,131240),(1024,131241),(1024,301225),(1024,303271)]),([6,8,31,1266,1604,1748],[(1024,131240),(1024,132263),(1024,132264),(1024,133415),(1024,165000),(1024,172327)]),([6,8,31,1266,1604,1936],[(1024,131240),(1024,132264),(1024,165000),(1024,301225),(1024,303271)]),([6,8,31,1266,1748],[(1024,132263),(1024,133415),(1024,137378),(1024,303271)])]
def b79 : List Row := [([6,8,31,1279,1604,1936],[(1024,131240),(1024,163976),(1024,301225),(1024,303271)]),([6,8,95,226,1168,1604],[(1024,131240),(1024,132264),(1024,133419),(1024,171137),(1024,303243)]),([6,8,95,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([6,8,159,226,1168,1604],[(1024,131371),(1024,138409),(1024,303243),(1024,303271)]),([6,8,224,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,303243)]),([6,8,224,1168,1604,2016],[(1024,131240),(1024,297096),(1024,297099),(1024,301225),(1024,303243),(1024,303271)]),([6,8,226,255,1168,1631],[(1024,131240),(1024,138401),(1024,138402),(1024,295051),(1024,303265),(1024,303266)]),([6,8,226,443,1168,1183],[(1024,138409),(1024,141609),(1024,170281),(1024,303243)]),([6,8,226,443,1168,2016],[(1024,131240),(1024,139432),(1024,165000),(1024,165003),(1024,170281),(1024,171137),(1024,295051),(1024,301225),(1024,303271)]),([6,8,226,768,1168,1604,1759],[(1024,106658)])]
def t74 : BT := .nd (blockTree b78) [6,8,31,1279,1604,1748] (blockTree b79)
def t75 : BT := .nd t73 [6,8,31,1168,1748,1821] t74
def t76 : BT := .nd t72 [6,8,31,1168,1266,1604,1766] t75
def t77 : BT := .nd t69 [6,8,31,768,1232,1604] t76
def b80 : List Row := [([6,8,226,768,1170,1604],[(1024,131234),(1024,132257),(1024,163970),(1024,303243)]),([6,8,226,768,1183,1604,1748],[(1024,106658),(1024,131171),(1024,131239),(1024,303235)]),([6,8,226,768,1604,1748,1759],[(1024,106658),(1024,131171)]),([6,8,226,770,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,296075),(1024,297122),(1024,303243)]),([6,8,226,864,1168,1604],[(1024,138409),(1024,141609),(1024,172168),(1024,303243)]),([6,8,226,879,1183,1604],[(1024,138409),(1024,141609),(1024,172168),(1024,303243),(1024,303271)]),([6,8,226,879,1604,2016],[(1024,165000),(1024,165003),(1024,171137),(1024,301225),(1024,303243),(1024,303271)]),([6,8,226,1055,1168,1604],[(1024,131240),(1024,301225),(1024,303243)]),([6,8,226,1168,1183,1604],[(1024,138409),(1024,141609),(1024,172168),(1024,303243)]),([6,8,226,1168,1183,1604,1766],[(1024,98471),(1024,98599),(1024,131239),(1024,131367),(1024,172168),(1024,295079),(1024,303243)]),([6,8,226,1168,1183,1604,1860],[(1024,303203),(1024,303235),(1024,303243)])]
def b81 : List Row := [([6,8,226,1168,1600,2016],[(1024,131240),(1024,165000),(1024,165003),(1024,295051),(1024,301225),(1024,303243),(1024,303271)]),([6,8,226,1168,1604,1631,1936],[(1024,98603),(1024,106658),(1024,131240),(1024,132264),(1024,295051)]),([6,8,226,1168,1604,2016],[(1024,131240),(1024,165000),(1024,165003),(1024,301225),(1024,303243),(1024,303271)]),([6,8,226,1168,1604,2024],[(1024,131240),(1024,165000),(1024,165003),(1024,301225),(1024,303243),(1024,303271)]),([6,8,226,1168,1604,2032],[(1024,138409),(1024,139432),(1024,303243)]),([6,8,226,1168,1612,2016],[(1024,131240),(1024,165000),(1024,165003),(1024,301225),(1024,303243),(1024,303271)]),([6,8,226,1168,1631,2016],[(1024,295051),(1024,303271)]),([6,8,226,1168,1748,2016],[(1024,165000),(1024,165003),(1024,297099),(1024,303271)]),([6,8,226,1176,1183,1604],[(1024,138409),(1024,141609),(1024,172168),(1024,303211),(1024,303243)]),([6,8,226,1176,1604,2016],[(1024,131240),(1024,165000),(1024,165003),(1024,301225),(1024,303243),(1024,303271)]),([6,8,226,1183,1266,1604],[(1024,131367),(1024,141609),(1024,303243)])]
def t78 : BT := .nd (blockTree b80) [6,8,226,1168,1183,1612] (blockTree b81)
def b82 : List Row := [([6,8,226,1183,1604,1936],[(1024,131241),(1024,139426),(1024,303235),(1024,303243)]),([6,8,234,1168,1183,1604],[(1024,138409),(1024,141609),(1024,172168),(1024,303243)]),([6,8,234,1168,1604,2016],[(1024,131240),(1024,165000),(1024,165003),(1024,301225),(1024,303243),(1024,303271)]),([6,8,255,768,1168,1631],[(1024,131240),(1024,138401)]),([6,8,255,799,1168,1604],[(1024,131240),(1024,138401),(1024,303271)]),([6,8,255,1168,1604,1631],[(1024,131240),(1024,138401),(1024,297129)]),([6,8,255,1168,1604,2016],[(1024,163976),(1024,303271)]),([6,8,255,1168,1631],[(1024,131240),(1024,131371),(1024,138401),(1024,303265)]),([6,8,416,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172323),(1024,297129),(1024,303243)]),([6,8,443,768,799,1168],[(1024,131240),(1024,138401),(1024,163976),(1024,170281),(1024,171137),(1024,303271)]),([6,8,443,768,1168,1631],[(1024,131240),(1024,138401),(1024,297129),(1024,303267)])]
def b83 : List Row := [([6,8,512,799,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([6,8,543,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172323),(1024,297129),(1024,303271)]),([6,8,768,799,879,1604],[(1024,138401),(1024,171137),(1024,303271)]),([6,8,768,799,1168,1604],[(1024,131240),(1024,138401),(1024,303271)]),([6,8,768,799,1168,1612],[(1024,131240),(1024,138401),(1024,303271)]),([6,8,768,799,1168,1631],[(1024,131240),(1024,303265),(1024,303271)]),([6,8,768,799,1168,1748],[(1024,138401),(1024,303271)]),([6,8,768,799,1176,1604],[(1024,131240),(1024,138401),(1024,303271)]),([6,8,768,799,1604,1748],[(1024,131239),(1024,131240),(1024,138401)]),([6,8,768,799,1604,1936],[(1024,131240),(1024,303271)])]
def t79 : BT := .nd (blockTree b82) [6,8,443,768,1168,2016] (blockTree b83)
def t80 : BT := .nd t78 [6,8,226,1183,1604,1748] t79
def b84 : List Row := [([6,8,768,879,1604,2016],[(1024,163976),(1024,303271)]),([6,8,768,1024,1168,1631],[(1024,131240),(1024,138401),(1024,295081)]),([6,8,768,1055,1168,1604],[(1024,131240),(1024,138401),(1024,301225),(1024,303243)]),([6,8,768,1168,1183,1604,1766],[(1024,98471),(1024,106658),(1024,131239),(1024,139426)]),([6,8,768,1168,1248,1604],[(1024,131240),(1024,163976),(1024,303271)]),([6,8,768,1168,1600,2016],[(1024,163976),(1024,303271)]),([6,8,768,1168,1604,1631],[(1024,131240),(1024,138401),(1024,297129)]),([6,8,768,1168,1604,1823],[(1024,131240),(1024,138401),(1024,303243)]),([6,8,768,1168,1604,1887],[(1024,131240),(1024,138401),(1024,303243)]),([6,8,768,1168,1604,2016],[(1024,163976),(1024,303271)]),([6,8,768,1168,1604,2020],[(1024,163976),(1024,303267)])]
def b85 : List Row := [([6,8,768,1168,1612,1631],[(1024,131240),(1024,138401),(1024,297129)]),([6,8,768,1168,1612,2016],[(1024,163976),(1024,303271)]),([6,8,768,1168,1631,1766],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172171),(1024,303243),(1024,303265),(1024,303266)]),([6,8,768,1168,1631,1860],[(1024,131240),(1024,138401)]),([6,8,768,1168,1631,2016],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303265),(1024,303271)]),([6,8,768,1168,1748,2016],[(1024,163976),(1024,303271)]),([6,8,768,1176,1604,1631],[(1024,98472),(1024,105633),(1024,131240),(1024,138401),(1024,297129)]),([6,8,768,1176,1604,2016],[(1024,163944),(1024,163976),(1024,303271)]),([6,8,768,1604,1631,1748],[(1024,131240),(1024,138401)]),([6,8,768,1604,1631,1936],[(1024,131240),(1024,138401)])]
def t81 : BT := .nd (blockTree b84) [6,8,768,1168,1604,2024] (blockTree b85)
def b86 : List Row := [([6,8,768,1604,1936,2016],[(1024,131240),(1024,163976)]),([6,8,776,799,1168,1604],[(1024,131240),(1024,138401),(1024,303271)]),([6,8,776,1168,1604,1631],[(1024,106657),(1024,131240),(1024,138401),(1024,297129)]),([6,8,776,1168,1604,2016],[(1024,163945),(1024,163976),(1024,303271)]),([6,8,799,994,1168,1604],[(1024,131240),(1024,296075),(1024,296103),(1024,301218)]),([6,8,799,1168,1183,1604],[(1024,138409),(1024,295079),(1024,303271)]),([6,8,799,1168,1279,1604],[(1024,131240),(1024,138401),(1024,303271)]),([6,8,799,1168,1604,1936],[(1024,131240),(1024,138401),(1024,297128),(1024,303271)]),([6,8,799,1168,1604,2016],[(1024,131240),(1024,163976),(1024,297096),(1024,303271)]),([6,8,1168,1183,1604,1821],[(1024,138409),(1024,301225),(1024,303243)]),([6,8,1168,1266,1604,2016],[(1024,165000),(1024,303271)])]
def b87 : List Row := [([6,8,1168,1279,1604,2016],[(1024,163976),(1024,303271)]),([6,8,1168,1604,1631,1936],[(1024,131240),(1024,138401),(1024,295081),(1024,297128),(1024,297129)]),([6,8,1168,1604,1821,2016],[(1024,138409),(1024,163976),(1024,165000),(1024,165003),(1024,301225),(1024,303271)]),([6,8,1168,1604,1936,2016],[(1024,163976),(1024,163977),(1024,301225)]),([6,10,31,226,1168,1604],[(1024,99497),(1024,131240),(1024,295051),(1024,303243),(1024,303271)]),([6,10,226,768,1168,1604],[(1024,98466),(1024,99489),(1024,131240),(1024,163938),(1024,164961),(1024,303243)]),([6,12,31,226,1168,1604],[(1024,131240),(1024,295011),(1024,301225),(1024,303203)]),([6,12,31,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303203)]),([6,16,31,226,1176,1604],[(1024,98472),(1024,301225),(1024,303211),(1024,303271)]),([6,16,31,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)])]
def t82 : BT := .nd (blockTree b86) [6,8,1168,1279,1604,1631] (blockTree b87)
def t83 : BT := .nd t81 [6,8,768,1604,1748,2016] t82
def t84 : BT := .nd t80 [6,8,768,879,1604,1631] t83
def b88 : List Row := [([6,23,31,226,1168,1604],[(1024,131240),(1024,301225),(1024,303271)]),([6,23,31,768,1168,1604],[(1024,131240),(1024,301225),(1024,303207),(1024,303271)]),([6,23,226,768,1168,1604],[(1024,131176),(1024,131240),(1024,303207),(1024,303243),(1024,303271)]),([6,23,226,1168,1604,2039],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,23,768,1168,1604],[(1024,131176),(1024,301161),(1024,303207)]),([6,23,768,1168,1604,2039],[(1024,131176),(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303207),(1024,303271)]),([6,24,31,226,1168,1604],[(1024,170281),(1024,172327),(1024,301225),(1024,303271)]),([6,24,31,226,1176,1604],[(1024,170281),(1024,172327),(1024,301225),(1024,303271)]),([6,24,31,768,1168,1604],[(1024,297129),(1024,301225),(1024,303271)]),([6,24,31,768,1176,1604],[(1024,297129),(1024,301225),(1024,303271)]),([6,31,31,226,1176,1604],[(1024,98472),(1024,301225),(1024,303271)])]
def b89 : List Row := [([6,31,31,776,1168,1604],[(1024,98473),(1024,131240),(1024,303271)]),([6,31,64,226,1168,1176,1604],[(1024,98472),(1024,98603),(1024,303211),(1024,303271)]),([6,31,64,226,1176,1604],[(1024,98472),(1024,99496),(1024,100651),(1024,171105),(1024,303211),(1024,303271)]),([6,31,64,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,303271)]),([6,31,64,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,172129),(1024,303271)]),([6,31,72,226,1168,1604],[(1024,131240),(1024,132264),(1024,133419),(1024,171137),(1024,303243),(1024,303271)]),([6,31,72,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,303207),(1024,303271)]),([6,31,128,226,1176,1604],[(1024,98603),(1024,301225),(1024,303211),(1024,303271)]),([6,31,128,768,1176,1604],[(1024,297129),(1024,301225),(1024,303211),(1024,303271)]),([6,31,128,776,1168,1604],[(1024,98473),(1024,106657),(1024,163945),(1024,303243),(1024,303271)])]
def t85 : BT := .nd (blockTree b88) [6,31,31,768,1176,1604] (blockTree b89)
def b90 : List Row := [([6,31,136,768,1168,1604],[(1024,297129),(1024,301225),(1024,303243),(1024,303271)]),([6,31,226,226,1176,1604],[(1024,98472),(1024,303211),(1024,303271)]),([6,31,226,234,443,1168],[(1024,131240),(1024,141609),(1024,170281),(1024,171137),(1024,303271)]),([6,31,226,234,879,1604],[(1024,171137),(1024,303243),(1024,303271)]),([6,31,226,234,1168,1604],[(1024,131240),(1024,303243),(1024,303271)]),([6,31,226,234,1168,1604,1748],[(1024,98599),(1024,98603),(1024,303271)]),([6,31,226,234,1168,1612],[(1024,99495),(1024,131240),(1024,303243),(1024,303271)]),([6,31,226,234,1168,1631],[(1024,131240),(1024,295051),(1024,303266),(1024,303271)]),([6,31,226,234,1168,1748],[(1024,133419),(1024,165003),(1024,303271)]),([6,31,226,234,1176,1604],[(1024,98472),(1024,99496),(1024,131240),(1024,303243),(1024,303271)]),([6,31,226,255,1176,1604],[(1024,98472),(1024,303271)])]
def b91 : List Row := [([6,31,226,443,768,1176],[(1024,98472),(1024,99496),(1024,108841),(1024,170281),(1024,171105),(1024,301225),(1024,303271)]),([6,31,226,443,776,1168],[(1024,98473),(1024,106658),(1024,131240),(1024,132264),(1024,164969),(1024,170281),(1024,171137),(1024,303271)]),([6,31,226,443,1168,1176],[(1024,98472),(1024,98603),(1024,141609),(1024,170281),(1024,172327),(1024,301225),(1024,303271)]),([6,31,226,443,1168,1612],[(1024,98471),(1024,131240),(1024,171137),(1024,172168),(1024,172327),(1024,301225),(1024,303271)]),([6,31,226,443,1168,2039],[(1024,131240),(1024,141609),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,31,226,443,1176],[(1024,98472),(1024,98603),(1024,170281)]),([6,31,226,443,1176,1604],[(1024,98472),(1024,171105),(1024,172136),(1024,172327),(1024,301225),(1024,303271)]),([6,31,226,512,1168,1176,1604],[(1024,98472),(1024,98603),(1024,141474),(1024,172136),(1024,303271)]),([6,31,226,512,1176,1604],[(1024,98472),(1024,99496),(1024,108706),(1024,171105),(1024,172136),(1024,303271)]),([6,31,226,520,1168,1604],[(1024,131240),(1024,132264),(1024,141474),(1024,171137),(1024,172168),(1024,303271)])]
def t86 : BT := .nd (blockTree b90) [6,31,226,435,1168,1604] (blockTree b91)
def t87 : BT := .nd t85 [6,31,136,226,1168,1604] t86
def b92 : List Row := [([6,31,226,768,1168,1604,1756],[(1024,98471),(1024,98472),(1024,301225),(1024,303203)]),([6,31,226,768,1168,1612,1748],[(1024,98471),(1024,131171),(1024,132195),(1024,303203)]),([6,31,226,768,1176,1604],[(1024,98472),(1024,303211),(1024,303271)]),([6,31,226,768,1176,1604,1748],[(1024,98472),(1024,98603),(1024,138401),(1024,141474),(1024,303271)]),([6,31,226,768,1176,1604,1756],[(1024,98472),(1024,99496),(1024,105633),(1024,108706),(1024,301225),(1024,303271)]),([6,31,226,768,1176,1612],[(1024,100520),(1024,164971),(1024,303271)]),([6,31,226,768,1176,1631],[(1024,98472),(1024,303266),(1024,303271)]),([6,31,226,768,1176,1748],[(1024,98603),(1024,138402),(1024,141473),(1024,141474),(1024,165003),(1024,170281),(1024,303271)]),([6,31,226,768,1176,1756],[(1024,100651),(1024,105634),(1024,108705),(1024,108706),(1024,164971),(1024,170281),(1024,303271)]),([6,31,226,768,1604,1748,1756],[(1024,98472),(1024,305321)]),([6,31,226,768,1604,1756],[(1024,98471),(1024,98472),(1024,99496),(1024,171105),(1024,305321)])]
def b93 : List Row := [([6,31,226,768,1612,1748],[(1024,98435),(1024,131171),(1024,132264)]),([6,31,226,776,879,1604],[(1024,106658),(1024,164969),(1024,171137),(1024,303203),(1024,303243),(1024,303271)]),([6,31,226,776,1168,1604],[(1024,106658),(1024,131240),(1024,164969),(1024,303203),(1024,303243),(1024,303271)]),([6,31,226,776,1168,1612],[(1024,106635),(1024,106663),(1024,131240),(1024,303243),(1024,303271)]),([6,31,226,776,1168,1631],[(1024,106658),(1024,106663),(1024,131240),(1024,303266),(1024,303271)]),([6,31,226,776,1168,1748],[(1024,98473),(1024,106658),(1024,164969),(1024,170281),(1024,303203),(1024,303271)]),([6,31,226,776,1176,1604],[(1024,98472),(1024,131240),(1024,303243),(1024,303271)]),([6,31,226,776,1604,1748],[(1024,98473),(1024,106658),(1024,131239),(1024,131240),(1024,132264),(1024,164969),(1024,171137)]),([6,31,226,776,1604,1936],[(1024,131177),(1024,131240),(1024,132264),(1024,303271)]),([6,31,226,776,1604,1944],[(1024,98472),(1024,131240),(1024,132264),(1024,164969),(1024,303271)])]
def t88 : BT := .nd (blockTree b92) [6,31,226,768,1604,1944] (blockTree b93)
def b94 : List Row := [([6,31,226,871,1168,1604],[(1024,170281),(1024,301225),(1024,303243),(1024,303271),(1024,305249)]),([6,31,226,871,1176,1604],[(1024,98472),(1024,170281),(1024,172327),(1024,301225),(1024,303211),(1024,303271)]),([6,31,226,871,1604],[(1024,171105),(1024,303271)]),([6,31,226,879,1176,1604],[(1024,98472),(1024,170281),(1024,172327),(1024,301225),(1024,303243),(1024,303271)]),([6,31,226,879,1604,1612],[(1024,98471),(1024,131240),(1024,171137),(1024,171145),(1024,301225),(1024,303203),(1024,305281)]),([6,31,226,879,1604,2039],[(1024,171137),(1024,301225),(1024,303243),(1024,303271)]),([6,31,226,994,1176,1604],[(1024,98472),(1024,301225),(1024,303211),(1024,303271)]),([6,31,226,1002,1168,1604],[(1024,99497),(1024,106658),(1024,131240),(1024,164969),(1024,303203),(1024,303243),(1024,303271)]),([6,31,226,1024,1176,1604],[(1024,98472),(1024,301225),(1024,303271)]),([6,31,226,1032,1168,1604],[(1024,131240),(1024,301225),(1024,303271)]),([6,31,226,1168,1176,1604],[(1024,98603),(1024,170281),(1024,172327),(1024,301225),(1024,303243),(1024,303271)])]
def b95 : List Row := [([6,31,226,1168,1176,1604,1860],[(1024,98472),(1024,98603),(1024,303203),(1024,303271)]),([6,31,226,1168,1176,1612],[(1024,100651),(1024,170281),(1024,301225),(1024,303243),(1024,303271)]),([6,31,226,1168,1176,1631],[(1024,98603),(1024,170281),(1024,295051),(1024,301225),(1024,303266),(1024,303271)]),([6,31,226,1168,1176,1748],[(1024,98603),(1024,133419),(1024,165003),(1024,170281),(1024,301225),(1024,303271)]),([6,31,226,1168,1176,1756],[(1024,100651),(1024,165003),(1024,170281),(1024,301225),(1024,303271)]),([6,31,226,1168,1266,1604,1612],[(1024,98471),(1024,98472),(1024,131240),(1024,172327)]),([6,31,226,1168,1271,1604],[(1024,106658),(1024,131240),(1024,164969),(1024,172129),(1024,303243),(1024,303271)]),([6,31,226,1168,1274,1604],[(1024,98599),(1024,98603),(1024,170281),(1024,303243),(1024,303271)]),([6,31,226,1168,1604,1612],[(1024,98471),(1024,131240),(1024,171137),(1024,172168),(1024,172327),(1024,301225),(1024,303203)]),([6,31,226,1168,1604,1612,1936],[(1024,98471),(1024,131240),(1024,132264),(1024,139426),(1024,303203)])]
def t89 : BT := .nd (blockTree b94) [6,31,226,1168,1176,1604,1766] (blockTree b95)
def t90 : BT := .nd t88 [6,31,226,799,1176,1604] t89
def t91 : BT := .nd t87 [6,31,226,768,871,1604] t90
def t92 : BT := .nd t84 [6,16,31,776,1168,1604] t91
def t93 : BT := .nd t77 [6,8,226,768,1168,1606] t92
def b96 : List Row := [([6,31,226,1168,1604,1774],[(1024,131240),(1024,171137),(1024,303203)]),([6,31,226,1168,1604,1813],[(1024,131240),(1024,301153),(1024,301225),(1024,303243),(1024,303271)]),([6,31,226,1168,1604,1868],[(1024,98471),(1024,98473),(1024,131240),(1024,164969),(1024,303203)]),([6,31,226,1168,1604,1944],[(1024,98472),(1024,98473),(1024,99497),(1024,106658),(1024,164969),(1024,170281),(1024,303203),(1024,303243),(1024,303271)]),([6,31,226,1168,1604,2024],[(1024,131240),(1024,301225),(1024,303203),(1024,303271)]),([6,31,226,1168,1604,2039],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,31,226,1168,1612,1748],[(1024,98443),(1024,98471),(1024,131171),(1024,131240),(1024,133419),(1024,172327),(1024,301225),(1024,303203)]),([6,31,226,1168,1612,1766],[(1024,98471),(1024,131240),(1024,172131)]),([6,31,226,1168,1612,1860],[(1024,98471),(1024,131240),(1024,132264),(1024,171137)]),([6,31,226,1168,1612,2039],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,31,226,1168,1631,2039],[(1024,131240),(1024,295051),(1024,301225),(1024,303266),(1024,303271)])]
def b97 : List Row := [([6,31,226,1168,1748,2039],[(1024,133419),(1024,165003),(1024,301225),(1024,303271)]),([6,31,226,1176,1176,1604],[(1024,170281),(1024,172327),(1024,301225),(1024,303211),(1024,303271)]),([6,31,226,1176,1183,1604],[(1024,98603),(1024,170281),(1024,172327),(1024,301225),(1024,303211),(1024,303271)]),([6,31,226,1176,1266,1604],[(1024,98472),(1024,303243),(1024,303271)]),([6,31,226,1176,1274,1604],[(1024,98472),(1024,99496),(1024,170281),(1024,303211),(1024,303271)]),([6,31,226,1176,1279,1604],[(1024,98472),(1024,303211),(1024,303271)]),([6,31,226,1176,1604],[(1024,98472),(1024,172327),(1024,303271)]),([6,31,226,1176,1604,1604],[(1024,98472),(1024,171105),(1024,172136),(1024,172327),(1024,301225),(1024,303271)]),([6,31,226,1176,1604,1612],[(1024,98472),(1024,100520),(1024,100651),(1024,131240),(1024,171137),(1024,172168),(1024,172327),(1024,301225),(1024,303271)]),([6,31,226,1176,1604,1631],[(1024,98472),(1024,98603),(1024,100651),(1024,171105),(1024,172327),(1024,295019),(1024,301225),(1024,303271)]),([6,31,226,1176,1604,1748],[(1024,98472),(1024,98603),(1024,133419),(1024,172168),(1024,172327),(1024,301225),(1024,303271),(1024,305249)])]
def t94 : BT := .nd (blockTree b96) [6,31,226,1168,1748,1756] (blockTree b97)
def b98 : List Row := [([6,31,226,1176,1604,1766],[(1024,98472),(1024,171105),(1024,303271)]),([6,31,226,1176,1604,1821],[(1024,98472),(1024,301225),(1024,303211),(1024,303271)]),([6,31,226,1176,1604,1860],[(1024,98472),(1024,99496),(1024,171105),(1024,303271)]),([6,31,226,1176,1604,1936],[(1024,98472),(1024,98603),(1024,301225),(1024,303243),(1024,303271)]),([6,31,226,1176,1604,1944],[(1024,98472),(1024,105633),(1024,170281),(1024,301225),(1024,303211),(1024,303271)]),([6,31,226,1176,1604,2016],[(1024,98472),(1024,301225),(1024,303271)]),([6,31,226,1176,1604,2039],[(1024,98472),(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,31,226,1176,1612],[(1024,100520),(1024,100651),(1024,303271)]),([6,31,226,1176,1631],[(1024,98472),(1024,98603),(1024,303271)]),([6,31,226,1176,1748],[(1024,98603),(1024,133419),(1024,303271)]),([6,31,226,1176,1756],[(1024,100651),(1024,303271)])]
def b99 : List Row := [([6,31,234,768,1176,1604],[(1024,98472),(1024,99496),(1024,105634),(1024,164968),(1024,303243),(1024,303271)]),([6,31,234,776,1168,1604],[(1024,131240),(1024,303243),(1024,303271)]),([6,31,234,994,1168,1604],[(1024,131240),(1024,301153),(1024,303243),(1024,303271)]),([6,31,234,1168,1176,1604],[(1024,99627),(1024,170281),(1024,172327),(1024,301225),(1024,303243),(1024,303271)]),([6,31,234,1168,1266,1604],[(1024,98599),(1024,170281),(1024,303243),(1024,303271)]),([6,31,234,1168,1604,1612],[(1024,99495),(1024,131240),(1024,171137),(1024,172168),(1024,172327),(1024,301225),(1024,303271)]),([6,31,234,1168,1604,1766],[(1024,98599),(1024,131240),(1024,171137),(1024,301153),(1024,303202),(1024,303271)]),([6,31,234,1168,1604,1821],[(1024,99497),(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,31,234,1168,1604,2039],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([6,31,234,1168,1612],[(1024,99495),(1024,100647),(1024,131240),(1024,303271)])]
def t95 : BT := .nd (blockTree b98) [6,31,234,768,1168,1612] (blockTree b99)
def t96 : BT := .nd t94 [6,31,226,1176,1604,1756] t95
def b100 : List Row := [([6,31,255,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,303271)]),([6,31,255,776,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,303203),(1024,303271)]),([6,31,255,1168,1176,1604],[(1024,98603),(1024,138401),(1024,163976),(1024,170281),(1024,172327),(1024,301225),(1024,303271)]),([6,31,255,1168,1604,1612],[(1024,98471),(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303203)]),([6,31,255,1168,1604,2039],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,255,1176,1604],[(1024,98472),(1024,172327),(1024,303271)]),([6,31,435,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303203),(1024,303271)]),([6,31,443,768,776,1168],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,303271)]),([6,31,443,768,1168,1176],[(1024,98472),(1024,138401),(1024,163976),(1024,170281),(1024,172327),(1024,297129),(1024,301225),(1024,303271)]),([6,31,443,768,1168,1612],[(1024,98471),(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,31,443,768,1168,2039],[(1024,131240),(1024,163976),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)])]
def b101 : List Row := [([6,31,443,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([6,31,443,776,1168],[(1024,98473),(1024,131240),(1024,170281)]),([6,31,443,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,172129),(1024,303271)]),([6,31,512,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,303271)]),([6,31,512,776,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,172129),(1024,303271)]),([6,31,520,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,303271)]),([6,31,768,768,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,303271)]),([6,31,768,776,879,1604],[(1024,138401),(1024,163976),(1024,171137),(1024,303203),(1024,303271)]),([6,31,768,776,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,303203),(1024,303271)]),([6,31,768,776,1168,1612],[(1024,131240),(1024,138401),(1024,163976),(1024,303271)])]
def t97 : BT := .nd (blockTree b100) [6,31,443,768,1176] (blockTree b101)
def b102 : List Row := [([6,31,768,776,1168,1748],[(1024,98473),(1024,138401),(1024,163976),(1024,170281),(1024,303203),(1024,303271)]),([6,31,768,776,1176,1604],[(1024,98472),(1024,131240),(1024,138401),(1024,163976),(1024,303271)]),([6,31,768,776,1604,1748],[(1024,131239),(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([6,31,768,776,1604,1936],[(1024,131240),(1024,163976),(1024,303271)]),([6,31,768,776,1604,1944],[(1024,98472),(1024,131240),(1024,163976),(1024,303271)]),([6,31,768,799,1176,1604],[(1024,98472),(1024,303271)]),([6,31,768,871,1168,1604],[(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,871,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)]),([6,31,768,871,1604],[(1024,171105),(1024,303271)]),([6,31,768,879,1176,1604],[(1024,98472),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,879,1604,1612],[(1024,98471),(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,303203)])]
def b103 : List Row := [([6,31,768,994,1176,1604],[(1024,98472),(1024,301225),(1024,303211),(1024,303271)]),([6,31,768,1024,1176,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)]),([6,31,768,1032,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,1168,1176,1604],[(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,1168,1176,1604,1766],[(1024,98471),(1024,98472),(1024,98603),(1024,106658),(1024,303271)]),([6,31,768,1168,1176,1612],[(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,1168,1176,1631],[(1024,301225),(1024,303265),(1024,303271)]),([6,31,768,1168,1176,1748],[(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,1168,1176,1756],[(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,1168,1271,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,172129),(1024,303271)])]
def t98 : BT := .nd (blockTree b102) [6,31,768,879,1604,2039] (blockTree b103)
def t99 : BT := .nd t97 [6,31,768,776,1168,1631] t98
def t100 : BT := .nd t96 [6,31,234,1176,1604] t99
def b104 : List Row := [([6,31,768,1168,1604,1756],[(1024,98471),(1024,98472),(1024,138401),(1024,163976),(1024,172327),(1024,301225),(1024,303203)]),([6,31,768,1168,1604,1868],[(1024,98473),(1024,131240),(1024,138401),(1024,163976),(1024,303203)]),([6,31,768,1168,1604,1944],[(1024,98472),(1024,98473),(1024,138401),(1024,163976),(1024,170281),(1024,303203),(1024,303271)]),([6,31,768,1168,1604,2024],[(1024,98440),(1024,131240),(1024,163976),(1024,301225),(1024,303203),(1024,303207),(1024,303271)]),([6,31,768,1168,1604,2039],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,1168,1612,1748],[(1024,98435),(1024,98471),(1024,131171),(1024,131240),(1024,138401),(1024,163976),(1024,172327),(1024,301225),(1024,303203)]),([6,31,768,1168,1612,1766],[(1024,98471),(1024,131240),(1024,163943),(1024,172131)]),([6,31,768,1168,1612,1860],[(1024,98471),(1024,131240),(1024,138401),(1024,163976),(1024,171137)]),([6,31,768,1168,1612,2039],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,1168,1631,2039],[(1024,131240),(1024,301225),(1024,303265),(1024,303271)]),([6,31,768,1168,1748,1756],[(1024,98471),(1024,138401),(1024,163976),(1024,172327),(1024,301225),(1024,303203)])]
def b105 : List Row := [([6,31,768,1176,1176,1604],[(1024,105633),(1024,163944),(1024,301225),(1024,303271)]),([6,31,768,1176,1183,1604],[(1024,301225),(1024,303271)]),([6,31,768,1176,1266,1604],[(1024,98472),(1024,138402),(1024,165000),(1024,303271)]),([6,31,768,1176,1274,1604],[(1024,98472),(1024,99496),(1024,105634),(1024,164968),(1024,303271)]),([6,31,768,1176,1279,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,303271)]),([6,31,768,1176,1604],[(1024,98472),(1024,301225),(1024,303271)]),([6,31,768,1176,1604,1604],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]),([6,31,768,1176,1604,1612],[(1024,98472),(1024,100520),(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,31,768,1176,1604,1631],[(1024,98472),(1024,105633),(1024,171105),(1024,172327),(1024,297129),(1024,301225),(1024,303271)]),([6,31,768,1176,1604,1748],[(1024,98472),(1024,138401),(1024,163976),(1024,172327),(1024,301225),(1024,303271)])]
def t101 : BT := .nd (blockTree b104) [6,31,768,1168,1748,2039] (blockTree b105)
def b106 : List Row := [([6,31,768,1176,1604,1766],[(1024,98472),(1024,99496),(1024,163944),(1024,171105),(1024,303271)]),([6,31,768,1176,1604,1821],[(1024,98472),(1024,301225),(1024,303211),(1024,303271)]),([6,31,768,1176,1604,1860],[(1024,98472),(1024,105633),(1024,163944),(1024,171105),(1024,303271)]),([6,31,768,1176,1604,1936],[(1024,98472),(1024,98603),(1024,138401),(1024,163976),(1024,170281),(1024,301225),(1024,303271)]),([6,31,768,1176,1604,1944],[(1024,98472),(1024,105633),(1024,163944),(1024,170281),(1024,301225),(1024,303271)]),([6,31,768,1176,1604,2016],[(1024,98472),(1024,163944),(1024,301225),(1024,303271)]),([6,31,768,1176,1604,2039],[(1024,98472),(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,768,1176,1612],[(1024,100520),(1024,301225),(1024,303271)]),([6,31,768,1176,1631],[(1024,98472),(1024,301225),(1024,303271)]),([6,31,768,1176,1748],[(1024,138401),(1024,301225),(1024,303271)]),([6,31,768,1176,1756],[(1024,105633),(1024,301225),(1024,303271)])]
def b107 : List Row := [([6,31,768,1604,1612,1756],[(1024,98472),(1024,131240),(1024,163976),(1024,301225)]),([6,31,768,1604,1612,1936],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,303203)]),([6,31,768,1604,1748,1756],[(1024,98472),(1024,138401),(1024,163976),(1024,172327),(1024,301225)]),([6,31,768,1604,1748,2039],[(1024,131239),(1024,131240),(1024,163976),(1024,301225)]),([6,31,768,1604,1756],[(1024,98472),(1024,105633),(1024,301225)]),([6,31,768,1604,1936,1944],[(1024,98472),(1024,138401),(1024,163976),(1024,170281),(1024,303203),(1024,303271)]),([6,31,768,1604,1936,2039],[(1024,131240),(1024,163976),(1024,303271)]),([6,31,768,1604,1944],[(1024,98472),(1024,105633),(1024,303271)]),([6,31,768,1612,1748],[(1024,98435),(1024,131171),(1024,131240),(1024,301225)]),([6,31,776,776,1168,1604],[(1024,106657),(1024,131240),(1024,163945),(1024,303271)])]
def t102 : BT := .nd (blockTree b106) [6,31,768,1604,1612,1748] (blockTree b107)
def t103 : BT := .nd t101 [6,31,768,1176,1604,1756] t102
def b108 : List Row := [([6,31,776,879,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303271)]),([6,31,776,879,1604],[(1024,171137),(1024,303271)]),([6,31,776,994,1168,1604],[(1024,98473),(1024,131240),(1024,303243),(1024,303271)]),([6,31,776,1002,1168,1604],[(1024,99497),(1024,106658),(1024,131240),(1024,164969),(1024,303243),(1024,303271)]),([6,31,776,1024,1168,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,303271)]),([6,31,776,1168,1168,1604],[(1024,98473),(1024,106657),(1024,163945),(1024,303271)]),([6,31,776,1168,1176,1604],[(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,776,1168,1183,1604],[(1024,98473),(1024,303271)]),([6,31,776,1168,1266,1604],[(1024,106658),(1024,131240),(1024,132264),(1024,164969),(1024,303203),(1024,303271)]),([6,31,776,1168,1271,1604],[(1024,106657),(1024,131240),(1024,163945),(1024,172129),(1024,303271)]),([6,31,776,1168,1279,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,303203),(1024,303271)])]
def b109 : List Row := [([6,31,776,1168,1604,1604],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,172129),(1024,303271)]),([6,31,776,1168,1604,1612],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([6,31,776,1168,1604,1631],[(1024,98473),(1024,106657),(1024,131240),(1024,138401),(1024,171137),(1024,172129),(1024,303271)]),([6,31,776,1168,1604,1748],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,172129),(1024,303271)]),([6,31,776,1168,1604,1766],[(1024,106658),(1024,131240),(1024,132264),(1024,164969),(1024,171137),(1024,303271)]),([6,31,776,1168,1604,1821],[(1024,106658),(1024,131240),(1024,164969),(1024,301225),(1024,303203),(1024,303243),(1024,303271)]),([6,31,776,1168,1604,1860],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,303271)]),([6,31,776,1168,1604,1868],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,171137),(1024,303203),(1024,303271)]),([6,31,776,1168,1604,1936],[(1024,131240),(1024,138401),(1024,163976),(1024,170281),(1024,301225),(1024,303203),(1024,303271)]),([6,31,776,1168,1604,1944],[(1024,98473),(1024,106657),(1024,131240),(1024,163945),(1024,170281),(1024,301225),(1024,303271)])]
def t104 : BT := .nd (blockTree b108) [6,31,776,1168,1604] (blockTree b109)
def b110 : List Row := [([6,31,776,1168,1604,2039],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([6,31,776,1168,1612],[(1024,100521),(1024,131240),(1024,303271)]),([6,31,776,1168,1631],[(1024,98473),(1024,131240),(1024,303271)]),([6,31,776,1168,1748],[(1024,98473),(1024,106657),(1024,303271)]),([6,31,776,1176,1604],[(1024,131240),(1024,301225),(1024,303271)]),([6,31,776,1604,1748],[(1024,98473),(1024,106657),(1024,131240)]),([6,31,776,1604,1936],[(1024,131240),(1024,138401),(1024,303271)]),([6,31,776,1604,1944],[(1024,106657),(1024,131240),(1024,303271)]),([6,31,799,1168,1176,1604],[(1024,295079),(1024,301225),(1024,303271)]),([6,31,799,1168,1604,1612],[(1024,98471),(1024,131240),(1024,138409),(1024,171137),(1024,172327),(1024,301225),(1024,303203)]),([6,31,799,1168,1604,2039],[(1024,131240),(1024,295079),(1024,301225),(1024,303271)])]
def b111 : List Row := [([6,31,1168,1176,1266,1604],[(1024,165000),(1024,172327),(1024,303271)]),([6,31,1168,1176,1274,1604],[(1024,165000),(1024,172327),(1024,303271)]),([6,31,1168,1176,1279,1604],[(1024,138401),(1024,163976),(1024,172327),(1024,303271)]),([6,31,1168,1176,1604,1821],[(1024,138409),(1024,301225),(1024,303271)]),([6,31,1168,1176,1604,1936],[(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([6,31,1168,1176,1604,1944],[(1024,98473),(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([6,31,1168,1266,1274,1604],[(1024,98599),(1024,132264),(1024,165000),(1024,303271)]),([6,31,1168,1266,1604,1612],[(1024,98471),(1024,132264),(1024,165000),(1024,172327),(1024,303203)]),([6,31,1168,1266,1604,2039],[(1024,132264),(1024,165000),(1024,172327),(1024,303271)]),([6,31,1168,1271,1604],[(1024,131240),(1024,172129),(1024,303271)])]
def t105 : BT := .nd (blockTree b110) [6,31,799,1176,1604] (blockTree b111)
def t106 : BT := .nd t104 [6,31,776,1168,1604,2016] t105
def t107 : BT := .nd t103 [6,31,776,799,1168,1604] t106
def t108 : BT := .nd t100 [6,31,768,1168,1604,1612] t107
def b112 : List Row := [([6,31,1168,1279,1604,2039],[(1024,131240),(1024,138401),(1024,163976),(1024,172327),(1024,303271)]),([6,31,1168,1604,1612,1821],[(1024,98471),(1024,131240),(1024,138409),(1024,301225)]),([6,31,1168,1604,1612,1936],[(1024,131240),(1024,131241),(1024,138401),(1024,163976),(1024,172327),(1024,297129),(1024,301225),(1024,303203)]),([6,31,1168,1604,1821,2039],[(1024,138409),(1024,301225),(1024,303271)]),([6,31,1168,1604,1936,1944],[(1024,98473),(1024,138401),(1024,163976),(1024,170281),(1024,301225),(1024,302247),(1024,303203),(1024,303271)]),([6,31,1168,1604,1936,2039],[(1024,131240),(1024,131241),(1024,163976),(1024,297129),(1024,301225),(1024,303271)]),([6,31,1168,1604,1944],[(1024,98473),(1024,106657),(1024,301225),(1024,303271)]),([6,31,1176,1266,1604],[(1024,98472),(1024,172327),(1024,303271)]),([6,31,1176,1274,1604],[(1024,99496),(1024,172327),(1024,303271)]),([6,31,1176,1279,1604],[(1024,98472),(1024,172327),(1024,303271)]),([6,31,1176,1604,1821],[(1024,98472),(1024,301225),(1024,303271)])]
def b113 : List Row := [([6,31,1176,1604,1944],[(1024,105633),(1024,301225),(1024,303271)]),([6,226,234,1168,1183,1604],[(1024,98599),(1024,141609),(1024,303243)]),([6,226,234,1168,1604,2016],[(1024,131240),(1024,164969),(1024,165003),(1024,303243),(1024,303271)]),([6,226,768,799,1176,1604],[(1024,98472),(1024,303211),(1024,303271)]),([6,226,768,1168,1176,1604,1631],[(1024,98472),(1024,98603),(1024,106658),(1024,138402),(1024,297129),(1024,303266)]),([6,226,768,1168,1183,1604,1612],[(1024,98471),(1024,131171),(1024,139426),(1024,303203)]),([6,226,768,1168,1604,2024],[(1024,98440),(1024,98443),(1024,131240),(1024,303203),(1024,303207),(1024,303243),(1024,303271)]),([6,226,768,1176,1183,1604],[(1024,108841),(1024,172136),(1024,303211)]),([6,226,768,1176,1604,1631],[(1024,98472),(1024,105633),(1024,105634),(1024,171105),(1024,297129),(1024,303211),(1024,303266)]),([6,226,768,1176,1604,2016],[(1024,98472),(1024,163944),(1024,164968),(1024,164971),(1024,303211),(1024,303271)]),([6,226,776,1168,1183,1604],[(1024,106658),(1024,303203),(1024,303243)])]
def t109 : BT := .nd (blockTree b112) [6,31,1176,1604,1936] (blockTree b113)
def b114 : List Row := [([6,226,776,1168,1604,2016],[(1024,163945),(1024,164969),(1024,303271)]),([6,226,1168,1176,1183,1604],[(1024,138409),(1024,141609),(1024,172168),(1024,303211),(1024,303243),(1024,303271)]),([6,226,1168,1176,1604,2016],[(1024,98603),(1024,165000),(1024,165003),(1024,170281),(1024,172327),(1024,301225),(1024,303243),(1024,303271)]),([6,226,1168,1183,1604,1612],[(1024,98443),(1024,98471),(1024,138409),(1024,172168),(1024,303203)]),([6,226,1168,1183,1604,2039],[(1024,138409),(1024,141609),(1024,172168),(1024,303243)]),([6,226,1168,1604,1612,2016],[(1024,98471),(1024,131240),(1024,139432),(1024,165000),(1024,171137),(1024,172327),(1024,297065),(1024,301225)]),([6,226,1168,1604,2016,2024],[(1024,131240),(1024,164969),(1024,297065),(1024,301225),(1024,303271)]),([6,226,1168,1604,2016,2039],[(1024,131240),(1024,165000),(1024,165003),(1024,301225),(1024,303243),(1024,303271)]),([6,226,1176,1183,1604],[(1024,172136),(1024,303211),(1024,303271)]),([6,226,1176,1604,2016],[(1024,98472),(1024,172327),(1024,303271)]),([6,768,776,799,1168,1604],[(1024,131240),(1024,138401),(1024,303203),(1024,303271)])]
def b115 : List Row := [([6,768,776,1168,1604,2016],[(1024,163945),(1024,163976),(1024,303271)]),([6,768,799,1168,1176,1604],[(1024,138401),(1024,303271)]),([6,768,799,1168,1604,1612],[(1024,98471),(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,303203)]),([6,768,799,1168,1604,2039],[(1024,131240),(1024,138401),(1024,303271)]),([6,768,799,1176,1604],[(1024,98472),(1024,105633),(1024,303271)]),([6,768,1168,1176,1604,1631],[(1024,105633),(1024,138401),(1024,297129)]),([6,768,1168,1176,1604,2016],[(1024,163944),(1024,163976),(1024,303271)]),([6,768,1168,1604,1612,1631],[(1024,131240),(1024,138401),(1024,297129)]),([6,768,1168,1604,1612,2016],[(1024,98471),(1024,131240),(1024,163976),(1024,303203)]),([6,768,1168,1604,1631,2039],[(1024,131240),(1024,138401),(1024,297129)])]
def t110 : BT := .nd (blockTree b114) [6,768,776,1168,1604,1631] (blockTree b115)
def t111 : BT := .nd t109 [6,226,776,1168,1604,1631] t110
def b116 : List Row := [([6,768,1168,1604,2016,2039],[(1024,163976),(1024,303271)]),([6,768,1168,1604,2024],[(1024,98440),(1024,303207)]),([6,768,1176,1604,1631],[(1024,98472),(1024,105633),(1024,297129)]),([6,768,1176,1604,2016],[(1024,163944),(1024,303271)]),([6,776,1168,1604,1631],[(1024,98473),(1024,106657),(1024,131240),(1024,138401)]),([6,776,1168,1604,2016],[(1024,163945),(1024,163976),(1024,303271)]),([7,0,8,31,226,1168,1604],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([7,0,8,31,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([7,2,8,31,226,1168,1604],[(1024,131240),(1024,295051),(1024,301225),(1024,303243),(1024,303271)]),([7,2,8,31,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([7,2,8,226,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,303243)])]
def b117 : List Row := [([7,4,8,31,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([7,8,8,31,226,1168,1604],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([7,8,8,31,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([7,8,16,31,226,1168,1604],[(1024,170281),(1024,172327),(1024,301225),(1024,303271)]),([7,8,16,31,768,1168,1604],[(1024,297129),(1024,301225),(1024,303271)]),([7,8,31,31,226,1168,1604],[(1024,131240),(1024,301225),(1024,303271)]),([7,8,31,31,768,1168,1604],[(1024,131240),(1024,301225),(1024,303271)]),([7,8,31,64,226,1168,1604],[(1024,131240),(1024,132264),(1024,133419),(1024,171137),(1024,303243),(1024,303271)]),([7,8,31,64,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,303271)]),([7,8,31,128,226,1168,1604],[(1024,131371),(1024,301225),(1024,303243),(1024,303271)])]
def t112 : BT := .nd (blockTree b116) [7,4,8,31,226,1168,1604] (blockTree b117)
def b118 : List Row := [([7,8,31,226,226,1168,1604],[(1024,131240),(1024,303243),(1024,303271)]),([7,8,31,226,234,1168,1604],[(1024,131240),(1024,303243),(1024,303271)]),([7,8,31,226,255,1168,1604],[(1024,131240),(1024,303271)]),([7,8,31,226,443,768,1168],[(1024,131240),(1024,132264),(1024,141609),(1024,170281),(1024,171137),(1024,301225),(1024,303271)]),([7,8,31,226,443,1168],[(1024,131240),(1024,131371),(1024,170281)]),([7,8,31,226,443,1168,1604],[(1024,131240),(1024,171137),(1024,172168),(1024,172327),(1024,301225),(1024,303271)]),([7,8,31,226,512,1168,1604],[(1024,131240),(1024,132264),(1024,141474),(1024,171137),(1024,172168),(1024,303271)]),([7,8,31,226,768,879,1604],[(1024,171137),(1024,303243),(1024,303271)]),([7,8,31,226,768,1168,1604],[(1024,131240),(1024,303243),(1024,303271)]),([7,8,31,226,768,1168,1604,1748],[(1024,106658),(1024,131240),(1024,132264),(1024,138401),(1024,141474),(1024,301225),(1024,303271)]),([7,8,31,226,768,1168,1612],[(1024,131240),(1024,303243),(1024,303271)])]
def b119 : List Row := [([7,8,31,226,768,1168,1748],[(1024,133419),(1024,138402),(1024,141473),(1024,141474),(1024,165003),(1024,170281),(1024,303271)]),([7,8,31,226,768,1176,1604],[(1024,131240),(1024,303243),(1024,303271)]),([7,8,31,226,768,1604,1748],[(1024,131239),(1024,131240),(1024,132264),(1024,171137),(1024,305321)]),([7,8,31,226,768,1604,1936],[(1024,131240),(1024,132264),(1024,303243),(1024,303271)]),([7,8,31,226,776,1168,1604],[(1024,131240),(1024,303243),(1024,303271)]),([7,8,31,226,799,1168,1604],[(1024,131240),(1024,295079),(1024,303271)]),([7,8,31,226,879,1168,1604],[(1024,131240),(1024,170281),(1024,172327),(1024,301225),(1024,303243),(1024,303271)]),([7,8,31,226,879,1604],[(1024,171137),(1024,303271)]),([7,8,31,226,994,1168,1604],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([7,8,31,226,1024,1168,1604],[(1024,131240),(1024,301225),(1024,303271)])]
def t113 : BT := .nd (blockTree b118) [7,8,31,226,768,1168,1631] (blockTree b119)
def t114 : BT := .nd t112 [7,8,31,128,768,1168,1604] t113
def t115 : BT := .nd t111 [6,768,1168,1604,2016,2024] t114
def b120 : List Row := [([7,8,31,226,1168,1176,1604],[(1024,170281),(1024,172327),(1024,301225),(1024,303243),(1024,303271)]),([7,8,31,226,1168,1183,1604],[(1024,131371),(1024,170281),(1024,172327),(1024,301225),(1024,303243),(1024,303271)]),([7,8,31,226,1168,1266,1604],[(1024,131240),(1024,132264),(1024,170281),(1024,303243),(1024,303271)]),([7,8,31,226,1168,1279,1604],[(1024,131240),(1024,303243),(1024,303271)]),([7,8,31,226,1168,1604],[(1024,131240),(1024,172327),(1024,303271)]),([7,8,31,226,1168,1604,1604],[(1024,131240),(1024,171137),(1024,172168),(1024,172327),(1024,301225),(1024,303271)]),([7,8,31,226,1168,1604,1612],[(1024,131240),(1024,171137),(1024,172168),(1024,172327),(1024,301225),(1024,303271)]),([7,8,31,226,1168,1604,1631],[(1024,131240),(1024,131371),(1024,133419),(1024,171137),(1024,172327),(1024,295051),(1024,301225),(1024,303271)]),([7,8,31,226,1168,1604,1748],[(1024,131240),(1024,131371),(1024,133419),(1024,172168),(1024,172327),(1024,301225),(1024,303271)]),([7,8,31,226,1168,1604,1766],[(1024,131240),(1024,171137),(1024,303271)]),([7,8,31,226,1168,1604,1821],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)])]
def b121 : List Row := [([7,8,31,226,1168,1604,1936],[(1024,131240),(1024,138401),(1024,170281),(1024,301225),(1024,303243),(1024,303271)]),([7,8,31,226,1168,1604,2016],[(1024,131240),(1024,301225),(1024,303271)]),([7,8,31,226,1168,1604,2039],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([7,8,31,226,1168,1612],[(1024,131240),(1024,172327),(1024,303271)]),([7,8,31,226,1168,1631],[(1024,131240),(1024,131371),(1024,303271)]),([7,8,31,226,1168,1748],[(1024,133419),(1024,303271)]),([7,8,31,226,1176,1604],[(1024,131240),(1024,172327),(1024,303271)]),([7,8,31,234,768,1168,1604],[(1024,131240),(1024,303243),(1024,303271)]),([7,8,31,234,1168,1604],[(1024,131240),(1024,172327),(1024,303271)]),([7,8,31,255,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,303271)])]
def t116 : BT := .nd (blockTree b120) [7,8,31,226,1168,1604,1860] (blockTree b121)
def b122 : List Row := [([7,8,31,443,768,1168],[(1024,131240),(1024,170281),(1024,301225)]),([7,8,31,443,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([7,8,31,512,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,303271)]),([7,8,31,768,768,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,303271)]),([7,8,31,768,776,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,303271)]),([7,8,31,768,799,1168,1604],[(1024,131240),(1024,303271)]),([7,8,31,768,879,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([7,8,31,768,879,1604],[(1024,171137),(1024,303271)]),([7,8,31,768,994,1168,1604],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)]),([7,8,31,768,1024,1168,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1168,1604],[(1024,138401),(1024,163976),(1024,301225),(1024,303271)])]
def b123 : List Row := [([7,8,31,768,1168,1183,1604],[(1024,301225),(1024,303271)]),([7,8,31,768,1168,1266,1604],[(1024,131240),(1024,132264),(1024,138402),(1024,165000),(1024,303271)]),([7,8,31,768,1168,1279,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,303271)]),([7,8,31,768,1168,1604],[(1024,131240),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1604,1604],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1604,1612],[(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1604,1631],[(1024,131240),(1024,138401),(1024,171137),(1024,172327),(1024,297129),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1604,1748],[(1024,131240),(1024,138401),(1024,163976),(1024,172327),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1604,1766],[(1024,131240),(1024,132264),(1024,163976),(1024,171137),(1024,303271)]),([7,8,31,768,1168,1604,1821],[(1024,131240),(1024,301225),(1024,303243),(1024,303271)])]
def t117 : BT := .nd (blockTree b122) [7,8,31,768,1168,1176,1604] (blockTree b123)
def t118 : BT := .nd t116 [7,8,31,255,1168,1604] t117
def b124 : List Row := [([7,8,31,768,1168,1604,1936],[(1024,131240),(1024,138401),(1024,163976),(1024,170281),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1604,2016],[(1024,131240),(1024,163976),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1604,2039],[(1024,131240),(1024,138401),(1024,163976),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1612],[(1024,131240),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1631],[(1024,131240),(1024,301225),(1024,303271)]),([7,8,31,768,1168,1748],[(1024,138401),(1024,301225),(1024,303271)]),([7,8,31,768,1176,1604],[(1024,131240),(1024,301225),(1024,303271)]),([7,8,31,768,1604,1748],[(1024,131240),(1024,138401),(1024,301225)]),([7,8,31,768,1604,1936],[(1024,131240),(1024,138401),(1024,303271)]),([7,8,31,776,1168,1604],[(1024,131240),(1024,301225),(1024,303271)]),([7,8,31,799,1168,1604],[(1024,131240),(1024,301225),(1024,303271)])]
def b125 : List Row := [([7,8,31,1168,1279,1604],[(1024,131240),(1024,172327),(1024,303271)]),([7,8,31,1168,1604,1821],[(1024,131240),(1024,301225),(1024,303271)]),([7,8,31,1168,1604,1936],[(1024,138401),(1024,301225),(1024,303271)]),([7,8,226,768,799,1168,1604],[(1024,131240),(1024,303243),(1024,303271)]),([7,8,226,768,1168,1183,1604],[(1024,141609),(1024,172168),(1024,303243)]),([7,8,226,768,1168,1604,1631],[(1024,131240),(1024,138401),(1024,138402),(1024,171137),(1024,297129),(1024,303243),(1024,303266)]),([7,8,226,768,1168,1604,2016],[(1024,131240),(1024,163976),(1024,165000),(1024,165003),(1024,303243),(1024,303271)]),([7,8,226,1168,1183,1604],[(1024,172168),(1024,303243),(1024,303271)]),([7,8,226,1168,1604,2016],[(1024,131240),(1024,172327),(1024,303271)]),([7,8,768,799,1168,1604],[(1024,131240),(1024,138401),(1024,303271)])]
def t119 : BT := .nd (blockTree b124) [7,8,31,1168,1266,1604] (blockTree b125)
def b126 : List Row := [([7,8,768,1168,1604,2016],[(1024,163976),(1024,303271)]),([7,31,226,234,768,1168,1604],[(1024,131240),(1024,303243),(1024,303271)]),([7,31,226,234,1168,1604],[(1024,131240),(1024,303271)]),([7,31,226,768,776,1168,1604],[(1024,131240),(1024,303203),(1024,303243),(1024,303271)]),([7,31,226,768,1168,1176,1604],[(1024,138401),(1024,170281),(1024,303243),(1024,303271)]),([7,31,226,768,1168,1604,1612],[(1024,98471),(1024,131240),(1024,132264),(1024,171137),(1024,301225),(1024,303203)]),([7,31,226,768,1168,1604,2039],[(1024,131240),(1024,303243),(1024,303271)]),([7,31,226,768,1176,1604],[(1024,98472),(1024,303271)]),([7,31,226,776,1168,1604],[(1024,106658),(1024,131240),(1024,303271)]),([7,31,226,1168,1176,1604],[(1024,172327),(1024,303271)]),([7,31,226,1168,1604,1612],[(1024,131240),(1024,131371),(1024,172327)])]
def b127 : List Row := [([7,31,226,1176,1604],[]),([7,31,768,776,1168,1604],[(1024,131240),(1024,138401),(1024,303271)]),([7,31,768,1168,1176,1604],[(1024,138401),(1024,301225),(1024,303271)]),([7,31,768,1168,1604,1612],[(1024,131240),(1024,138401),(1024,301225)]),([7,31,768,1168,1604,2039],[(1024,131240),(1024,301225),(1024,303271)]),([7,31,768,1176,1604],[]),([7,31,776,1168,1604],[]),([8,8,31,226,768,1168,1604],[(1024,131240),(1024,303271)]),([8,8,31,226,1168,1604],[]),([8,8,31,768,1168,1604],[])]
def t120 : BT := .nd (blockTree b126) [7,31,226,1168,1604,2039] (blockTree b127)
def t121 : BT := .nd t119 [7,8,768,1168,1604,1631] t120
def t122 : BT := .nd t118 [7,8,31,768,1168,1604,1860] t121
def t123 : BT := .nd t115 [7,8,31,226,1168,1168,1604] t122
def t124 : BT := .nd t108 [6,31,1168,1279,1604,1612] t123
def t125 : BT := .nd t93 [6,31,226,1168,1604,1756] t124
def t126 : BT := .nd t62 [6,8,31,226,580,1168] t125
def T_cert : BT := t126
def mP := stepOK M_ Y_ PD_ PM_ G_ T_cert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb0 : Covered mP (blockTree b0) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb1 : Covered mP (blockTree b1) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb2 : Covered mP (blockTree b2) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb3 : Covered mP (blockTree b3) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb4 : Covered mP (blockTree b4) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb5 : Covered mP (blockTree b5) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb6 : Covered mP (blockTree b6) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb7 : Covered mP (blockTree b7) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb8 : Covered mP (blockTree b8) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb9 : Covered mP (blockTree b9) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb10 : Covered mP (blockTree b10) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb11 : Covered mP (blockTree b11) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb12 : Covered mP (blockTree b12) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb13 : Covered mP (blockTree b13) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb14 : Covered mP (blockTree b14) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb15 : Covered mP (blockTree b15) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb16 : Covered mP (blockTree b16) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb17 : Covered mP (blockTree b17) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb18 : Covered mP (blockTree b18) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb19 : Covered mP (blockTree b19) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb20 : Covered mP (blockTree b20) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb21 : Covered mP (blockTree b21) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb22 : Covered mP (blockTree b22) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb23 : Covered mP (blockTree b23) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb24 : Covered mP (blockTree b24) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb25 : Covered mP (blockTree b25) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb26 : Covered mP (blockTree b26) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb27 : Covered mP (blockTree b27) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb28 : Covered mP (blockTree b28) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb29 : Covered mP (blockTree b29) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb30 : Covered mP (blockTree b30) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb31 : Covered mP (blockTree b31) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb32 : Covered mP (blockTree b32) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb33 : Covered mP (blockTree b33) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb34 : Covered mP (blockTree b34) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb35 : Covered mP (blockTree b35) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb36 : Covered mP (blockTree b36) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb37 : Covered mP (blockTree b37) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb38 : Covered mP (blockTree b38) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb39 : Covered mP (blockTree b39) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb40 : Covered mP (blockTree b40) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb41 : Covered mP (blockTree b41) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb42 : Covered mP (blockTree b42) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb43 : Covered mP (blockTree b43) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb44 : Covered mP (blockTree b44) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb45 : Covered mP (blockTree b45) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb46 : Covered mP (blockTree b46) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb47 : Covered mP (blockTree b47) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb48 : Covered mP (blockTree b48) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb49 : Covered mP (blockTree b49) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb50 : Covered mP (blockTree b50) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb51 : Covered mP (blockTree b51) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb52 : Covered mP (blockTree b52) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb53 : Covered mP (blockTree b53) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb54 : Covered mP (blockTree b54) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb55 : Covered mP (blockTree b55) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb56 : Covered mP (blockTree b56) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb57 : Covered mP (blockTree b57) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb58 : Covered mP (blockTree b58) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb59 : Covered mP (blockTree b59) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb60 : Covered mP (blockTree b60) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb61 : Covered mP (blockTree b61) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb62 : Covered mP (blockTree b62) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb63 : Covered mP (blockTree b63) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb64 : Covered mP (blockTree b64) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb65 : Covered mP (blockTree b65) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb66 : Covered mP (blockTree b66) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb67 : Covered mP (blockTree b67) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb68 : Covered mP (blockTree b68) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb69 : Covered mP (blockTree b69) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb70 : Covered mP (blockTree b70) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb71 : Covered mP (blockTree b71) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb72 : Covered mP (blockTree b72) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb73 : Covered mP (blockTree b73) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb74 : Covered mP (blockTree b74) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb75 : Covered mP (blockTree b75) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb76 : Covered mP (blockTree b76) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb77 : Covered mP (blockTree b77) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb78 : Covered mP (blockTree b78) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb79 : Covered mP (blockTree b79) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb80 : Covered mP (blockTree b80) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb81 : Covered mP (blockTree b81) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb82 : Covered mP (blockTree b82) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb83 : Covered mP (blockTree b83) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb84 : Covered mP (blockTree b84) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb85 : Covered mP (blockTree b85) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb86 : Covered mP (blockTree b86) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb87 : Covered mP (blockTree b87) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb88 : Covered mP (blockTree b88) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb89 : Covered mP (blockTree b89) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb90 : Covered mP (blockTree b90) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb91 : Covered mP (blockTree b91) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb92 : Covered mP (blockTree b92) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb93 : Covered mP (blockTree b93) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb94 : Covered mP (blockTree b94) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb95 : Covered mP (blockTree b95) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb96 : Covered mP (blockTree b96) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb97 : Covered mP (blockTree b97) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb98 : Covered mP (blockTree b98) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb99 : Covered mP (blockTree b99) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb100 : Covered mP (blockTree b100) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb101 : Covered mP (blockTree b101) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb102 : Covered mP (blockTree b102) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb103 : Covered mP (blockTree b103) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb104 : Covered mP (blockTree b104) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb105 : Covered mP (blockTree b105) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb106 : Covered mP (blockTree b106) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb107 : Covered mP (blockTree b107) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb108 : Covered mP (blockTree b108) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb109 : Covered mP (blockTree b109) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb110 : Covered mP (blockTree b110) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb111 : Covered mP (blockTree b111) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb112 : Covered mP (blockTree b112) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb113 : Covered mP (blockTree b113) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb114 : Covered mP (blockTree b114) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb115 : Covered mP (blockTree b115) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb116 : Covered mP (blockTree b116) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb117 : Covered mP (blockTree b117) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb118 : Covered mP (blockTree b118) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb119 : Covered mP (blockTree b119) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb120 : Covered mP (blockTree b120) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb121 : Covered mP (blockTree b121) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb122 : Covered mP (blockTree b122) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb123 : Covered mP (blockTree b123) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb124 : Covered mP (blockTree b124) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb125 : Covered mP (blockTree b125) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb126 : Covered mP (blockTree b126) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb127 : Covered mP (blockTree b127) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct0 : Covered mP t0 := coveredNode cb0 cb1 (h := [(1024,131240),(1024,138401)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct1 : Covered mP t1 := coveredNode cb2 cb3 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct2 : Covered mP t2 := coveredNode ct0 ct1 (h := [(1024,98471),(1024,163943),(1024,301225)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct3 : Covered mP t3 := coveredNode cb4 cb5 (h := [(1024,98472),(1024,105633),(1024,163944),(1024,170273),(1024,171105),(1024,295079)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct4 : Covered mP t4 := coveredNode cb6 cb7 (h := [(1024,98472),(1024,295075)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct5 : Covered mP t5 := coveredNode ct3 ct4 (h := [(1024,98435),(1024,131171)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct6 : Covered mP t6 := coveredNode ct2 ct5 (h := [(1024,98466),(1024,99489),(1024,295011)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct7 : Covered mP t7 := coveredNode cb8 cb9 (h := [(1024,105641),(1024,171113),(1024,303211)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct8 : Covered mP t8 := coveredNode cb10 cb11 (h := [(1024,131234),(1024,132257),(1024,295043)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct9 : Covered mP t9 := coveredNode ct7 ct8 (h := [(1024,131240),(1024,138401),(1024,163976),(1024,302247)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct10 : Covered mP t10 := coveredNode cb12 cb13 (h := [(1024,131240),(1024,138401)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct11 : Covered mP t11 := coveredNode cb14 cb15 (h := [(1024,98440),(1024,131176),(1024,138337),(1024,301161),(1024,303207)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct12 : Covered mP t12 := coveredNode ct10 ct11 (h := [(1024,98472),(1024,138409),(1024,303211),(1024,303243)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct13 : Covered mP t13 := coveredNode ct9 ct12 (h := [(1024,131240),(1024,163976),(1024,171137),(1024,172321)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct14 : Covered mP t14 := coveredNode ct6 ct13 (h := [(1024,98443),(1024,106657)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct15 : Covered mP t15 := coveredNode cb16 cb17 (h := [(1024,98603),(1024,164968),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct16 : Covered mP t16 := coveredNode cb18 cb19 (h := [(1024,98472),(1024,164971),(1024,170281),(1024,171105),(1024,172327),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct17 : Covered mP t17 := coveredNode ct15 ct16 (h := [(1024,98472)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct18 : Covered mP t18 := coveredNode cb20 cb21 (h := [(1024,99496),(1024,303203),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct19 : Covered mP t19 := coveredNode cb22 cb23 (h := [(1024,99495),(1024,100647),(1024,104610),(1024,131240),(1024,164967),(1024,170082),(1024,171137),(1024,301155)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct20 : Covered mP t20 := coveredNode ct18 ct19 (h := [(1024,98603),(1024,295019),(1024,301225),(1024,303266),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct21 : Covered mP t21 := coveredNode ct17 ct20 (h := [(1024,131171),(1024,132195)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct22 : Covered mP t22 := coveredNode cb24 cb25 (h := [(1024,98603),(1024,163976),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct23 : Covered mP t23 := coveredNode cb26 cb27 (h := [(1024,98472),(1024,131240),(1024,163945),(1024,170281)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct24 : Covered mP t24 := coveredNode ct22 ct23 (h := [(1024,98472),(1024,100520),(1024,163947),(1024,170281),(1024,171107),(1024,172327),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct25 : Covered mP t25 := coveredNode cb28 cb29 (h := [(1024,105633),(1024,163944),(1024,171105),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct26 : Covered mP t26 := coveredNode cb30 cb31 (h := [(1024,98471),(1024,98472),(1024,104609),(1024,105633),(1024,163944),(1024,171105)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct27 : Covered mP t27 := coveredNode ct25 ct26 (h := [(1024,98472),(1024,105633),(1024,163944),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct28 : Covered mP t28 := coveredNode ct24 ct27 (h := [(1024,98473),(1024,131240),(1024,163945),(1024,170281),(1024,171137),(1024,172129),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct29 : Covered mP t29 := coveredNode ct21 ct28 (h := [(1024,99627),(1024,165003),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct30 : Covered mP t30 := coveredNode ct14 ct29 (h := [(1024,295081),(1024,303265)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct31 : Covered mP t31 := coveredNode cb32 cb33 (h := [(1024,106663),(1024,138401),(1024,163976),(1024,171137),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct32 : Covered mP t32 := coveredNode cb34 cb35 (h := [(1024,98472),(1024,106664),(1024,131239),(1024,131240),(1024,163976),(1024,301225)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct33 : Covered mP t33 := coveredNode ct31 ct32 (h := [(1024,100521),(1024,106663),(1024,163976),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct34 : Covered mP t34 := coveredNode cb36 cb37 (h := [(1024,171105),(1024,295079),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct35 : Covered mP t35 := coveredNode cb38 cb39 (h := [(1024,98599),(1024,131240),(1024,295015),(1024,303207),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct36 : Covered mP t36 := coveredNode ct34 ct35 (h := [(1024,105633),(1024,163944),(1024,171105),(1024,172327),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct37 : Covered mP t37 := coveredNode ct33 ct36 (h := [(1024,98472),(1024,131240),(1024,303265),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct38 : Covered mP t38 := coveredNode cb40 cb41 (h := [(1024,99496),(1024,164968),(1024,172327),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct39 : Covered mP t39 := coveredNode cb42 cb43 (h := [(1024,295019),(1024,296105),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct40 : Covered mP t40 := coveredNode ct38 ct39 (h := [(1024,98473),(1024,106658),(1024,301225)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct41 : Covered mP t41 := coveredNode cb44 cb45 (h := [(1024,98472),(1024,163944),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct42 : Covered mP t42 := coveredNode cb46 cb47 (h := [(1024,98434),(1024,98435),(1024,295011)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct43 : Covered mP t43 := coveredNode ct41 ct42 (h := [(1024,105641),(1024,108841),(1024,170281),(1024,303211)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct44 : Covered mP t44 := coveredNode ct40 ct43 (h := [(1024,98471),(1024,98472),(1024,165000),(1024,172327)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct45 : Covered mP t45 := coveredNode ct37 ct44 (h := [(1024,98473),(1024,100520),(1024,100521),(1024,163976),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct46 : Covered mP t46 := coveredNode cb48 cb49 (h := [(1024,98440),(1024,131176),(1024,138337),(1024,303207)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct47 : Covered mP t47 := coveredNode cb50 cb51 (h := [(1024,98472),(1024,105633),(1024,297129),(1024,303267)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct48 : Covered mP t48 := coveredNode ct46 ct47 (h := [(1024,98472),(1024,105633),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct49 : Covered mP t49 := coveredNode cb52 cb53 (h := [(1024,98472),(1024,105633),(1024,301225),(1024,303211)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct50 : Covered mP t50 := coveredNode cb54 cb55 (h := [(1024,163944),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct51 : Covered mP t51 := coveredNode ct49 ct50 (h := [(1024,98472),(1024,163944),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct52 : Covered mP t52 := coveredNode ct48 ct51 (h := [(1024,100520),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct53 : Covered mP t53 := coveredNode cb56 cb57 (h := [(1024,106657),(1024,106658),(1024,131240),(1024,172171)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct54 : Covered mP t54 := coveredNode cb58 cb59 (h := [(1024,98440),(1024,98441),(1024,301161)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct55 : Covered mP t55 := coveredNode ct53 ct54 (h := [(1024,131240),(1024,163945),(1024,163976)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct56 : Covered mP t56 := coveredNode cb60 cb61 (h := [(1024,98443),(1024,98471),(1024,131240),(1024,301225)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct57 : Covered mP t57 := coveredNode cb62 cb63 (h := [(1024,98473),(1024,131240),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct58 : Covered mP t58 := coveredNode ct56 ct57 (h := [(1024,297129),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct59 : Covered mP t59 := coveredNode ct55 ct58 (h := [(1024,163944),(1024,163945),(1024,301225)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct60 : Covered mP t60 := coveredNode ct52 ct59 (h := [(1024,98472),(1024,106664),(1024,138401),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct61 : Covered mP t61 := coveredNode ct45 ct60 (h := [(1024,105641),(1024,106664),(1024,303211)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct62 : Covered mP t62 := coveredNode ct30 ct61 (h := [(1024,98471),(1024,172131),(1024,301225)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct63 : Covered mP t63 := coveredNode cb64 cb65 (h := [(1024,98603),(1024,132264),(1024,303203),(1024,303235),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct64 : Covered mP t64 := coveredNode cb66 cb67 (h := [(1024,131240),(1024,301225),(1024,303243),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct65 : Covered mP t65 := coveredNode ct63 ct64 (h := [(1024,131240),(1024,295043),(1024,301225),(1024,303235)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct66 : Covered mP t66 := coveredNode cb68 cb69 (h := [(1024,131240),(1024,138409),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct67 : Covered mP t67 := coveredNode cb70 cb71 (h := [(1024,297129),(1024,301225),(1024,303240),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct68 : Covered mP t68 := coveredNode ct66 ct67 (h := [(1024,138401),(1024,163976),(1024,171137),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct69 : Covered mP t69 := coveredNode ct65 ct68 (h := [(1024,133419),(1024,163976),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct70 : Covered mP t70 := coveredNode cb72 cb73 (h := [(1024,131240),(1024,303265),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct71 : Covered mP t71 := coveredNode cb74 cb75 (h := [(1024,131240),(1024,297128),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct72 : Covered mP t72 := coveredNode ct70 ct71 (h := [(1024,131239),(1024,131240),(1024,163976),(1024,301225)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct73 : Covered mP t73 := coveredNode cb76 cb77 (h := [(1024,138409),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct74 : Covered mP t74 := coveredNode cb78 cb79 (h := [(1024,131239),(1024,131240),(1024,163976),(1024,172327),(1024,303235)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct75 : Covered mP t75 := coveredNode ct73 ct74 (h := [(1024,165003),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct76 : Covered mP t76 := coveredNode ct72 ct75 (h := [(1024,98471),(1024,98472),(1024,98599),(1024,131240),(1024,131367),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct77 : Covered mP t77 := coveredNode ct69 ct76 (h := [(1024,131239),(1024,131240),(1024,137377),(1024,138401),(1024,163976),(1024,171137)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct78 : Covered mP t78 := coveredNode cb80 cb81 (h := [(1024,138409),(1024,141609),(1024,172168),(1024,303243)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct79 : Covered mP t79 := coveredNode cb82 cb83 (h := [(1024,131240),(1024,163976)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct80 : Covered mP t80 := coveredNode ct78 ct79 (h := [(1024,131239),(1024,138409),(1024,172168),(1024,303235)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct81 : Covered mP t81 := coveredNode cb84 cb85 (h := [(1024,98440),(1024,163976),(1024,303207),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct82 : Covered mP t82 := coveredNode cb86 cb87 (h := [(1024,131240),(1024,138401),(1024,172323),(1024,303243)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct83 : Covered mP t83 := coveredNode ct81 ct82 (h := [(1024,131239),(1024,131240),(1024,163976)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct84 : Covered mP t84 := coveredNode ct80 ct83 (h := [(1024,138401),(1024,171137)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct85 : Covered mP t85 := coveredNode cb88 cb89 (h := [(1024,98472),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct86 : Covered mP t86 := coveredNode cb90 cb91 (h := [(1024,131240),(1024,171137),(1024,172168),(1024,172327),(1024,301225),(1024,303203),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct87 : Covered mP t87 := coveredNode ct85 ct86 (h := [(1024,131371),(1024,301225),(1024,303243),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct88 : Covered mP t88 := coveredNode cb92 cb93 (h := [(1024,98472),(1024,99496),(1024,303211),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct89 : Covered mP t89 := coveredNode cb94 cb95 (h := [(1024,98471),(1024,98472),(1024,98599),(1024,98603),(1024,295051),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct90 : Covered mP t90 := coveredNode ct88 ct89 (h := [(1024,98472),(1024,295079),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct91 : Covered mP t91 := coveredNode ct87 ct90 (h := [(1024,171105),(1024,303211),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct92 : Covered mP t92 := coveredNode ct84 ct91 (h := [(1024,98473),(1024,106657),(1024,163945),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct93 : Covered mP t93 := coveredNode ct77 ct92 (h := [(1024,131240),(1024,138401),(1024,163976),(1024,303243)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct94 : Covered mP t94 := coveredNode cb96 cb97 (h := [(1024,98471),(1024,133419),(1024,165003),(1024,172327),(1024,301225),(1024,303203),(1024,305283)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct95 : Covered mP t95 := coveredNode cb98 cb99 (h := [(1024,99467),(1024,99495),(1024,131240),(1024,164967)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct96 : Covered mP t96 := coveredNode ct94 ct95 (h := [(1024,98472),(1024,98603),(1024,100651),(1024,172136),(1024,172327),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct97 : Covered mP t97 := coveredNode cb100 cb101 (h := [(1024,98472),(1024,170281),(1024,301225)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct98 : Covered mP t98 := coveredNode cb102 cb103 (h := [(1024,138401),(1024,163976),(1024,171137),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct99 : Covered mP t99 := coveredNode ct97 ct98 (h := [(1024,131240),(1024,303265),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct100 : Covered mP t100 := coveredNode ct96 ct99 (h := [(1024,99496),(1024,172327),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct101 : Covered mP t101 := coveredNode cb104 cb105 (h := [(1024,163976),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct102 : Covered mP t102 := coveredNode cb106 cb107 (h := [(1024,98435),(1024,131171),(1024,131240),(1024,163976),(1024,301225)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct103 : Covered mP t103 := coveredNode ct101 ct102 (h := [(1024,98472),(1024,105633),(1024,163944),(1024,172327),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct104 : Covered mP t104 := coveredNode cb108 cb109 (h := [(1024,98473),(1024,131240),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct105 : Covered mP t105 := coveredNode cb110 cb111 (h := [(1024,98472),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct106 : Covered mP t106 := coveredNode ct104 ct105 (h := [(1024,98473),(1024,131240),(1024,163945),(1024,163976),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct107 : Covered mP t107 := coveredNode ct103 ct106 (h := [(1024,131240),(1024,303203),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct108 : Covered mP t108 := coveredNode ct100 ct107 (h := [(1024,98471),(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,172327),(1024,301225),(1024,303203)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct109 : Covered mP t109 := coveredNode cb112 cb113 (h := [(1024,98603),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct110 : Covered mP t110 := coveredNode cb114 cb115 (h := [(1024,106657),(1024,131240),(1024,138401)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct111 : Covered mP t111 := coveredNode ct109 ct110 (h := [(1024,106657),(1024,106658),(1024,131240),(1024,138401)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct112 : Covered mP t112 := coveredNode cb116 cb117 (h := [(1024,131240),(1024,295051),(1024,301225),(1024,303243),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct113 : Covered mP t113 := coveredNode cb118 cb119 (h := [(1024,131240),(1024,303266),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct114 : Covered mP t114 := coveredNode ct112 ct113 (h := [(1024,297129),(1024,301225),(1024,303243),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct115 : Covered mP t115 := coveredNode ct111 ct114 (h := [(1024,98440),(1024,131240),(1024,301225),(1024,303203),(1024,303207),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct116 : Covered mP t116 := coveredNode cb120 cb121 (h := [(1024,131240),(1024,132264),(1024,171137),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct117 : Covered mP t117 := coveredNode cb122 cb123 (h := [(1024,138401),(1024,163976),(1024,301225),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct118 : Covered mP t118 := coveredNode ct116 ct117 (h := [(1024,131240),(1024,172327),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct119 : Covered mP t119 := coveredNode cb124 cb125 (h := [(1024,132264),(1024,172327),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct120 : Covered mP t120 := coveredNode cb126 cb127 (h := [(1024,131240),(1024,172327),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct121 : Covered mP t121 := coveredNode ct119 ct120 (h := [(1024,131240),(1024,138401),(1024,297129)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct122 : Covered mP t122 := coveredNode ct118 ct121 (h := [(1024,131240),(1024,138401),(1024,163976),(1024,171137),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct123 : Covered mP t123 := coveredNode ct115 ct122 (h := [(1024,170281),(1024,172327),(1024,301225),(1024,303243),(1024,303271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct124 : Covered mP t124 := coveredNode ct108 ct123 (h := [(1024,98471),(1024,131240),(1024,138401),(1024,163976),(1024,172327),(1024,303203)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct125 : Covered mP t125 := coveredNode ct93 ct124 (h := [(1024,98471),(1024,98472),(1024,133419),(1024,172168),(1024,172327),(1024,301225),(1024,303203)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct126 : Covered mP t126 := coveredNode ct62 ct125 (h := [(1024,131240),(1024,165003),(1024,170281),(1024,171137),(1024,172327),(1024,301225),(1024,303271)]) (by decide +kernel)
theorem hT_cert : Covered mP T_cert := ct126
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ p ∈ PEqualNP.Outside.L_meta_23615.Short.samplePairs, C.eval (PEqualNP.Outside.L_meta_23615.Short.pairInput p.1 p.2) = (34224 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)) := by

  rintro ⟨C,hfan,hsize,hr⟩
  let f : BFn 6 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 6 × Fin 6) (hp : p ∈ samplePairs) : f (pt 6 (pairCode p)) = reference (pt 6 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 6 (pairCode (i,j)))) = _
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
  have nc : ∃ x y : Fin 6 → Bool, f x ≠ f y := by
    refine ⟨pt 6 (pairCode (0,1)),pt 6 (pairCode (0,4)),?_⟩
    rw [he (0,1) (by decide +kernel),he (0,4) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 8 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end PEqualNP.Outside.L_meta_23615.Short

theorem PEqualNP.Outside.L_meta_23615 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ p ∈ PEqualNP.Outside.L_meta_23615.Short.samplePairs, C.eval (PEqualNP.Outside.L_meta_23615.Short.pairInput p.1 p.2) = (34224 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)) := PEqualNP.Outside.L_meta_23615.Short.lower
