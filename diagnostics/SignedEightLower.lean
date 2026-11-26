import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23548.Lower

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



def pairCode (p : Fin 6 × Fin 6) : Nat := 2 ^ p.1.val ||| 2 ^ p.2.val
def reference (x : Fin 6 → Bool) : Bool :=
  (x 0 && (x 1 || x 2 || x 3 || x 4 || x 5)) || (x 3 && (x 1 || x 2)) || (x 1 && x 2)
def pairInput (i j : Fin 6) := List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)
theorem codeInputs : ∀ p : Fin 6 × Fin 6, List.ofFn (pt 6 (pairCode p)) = pairInput p.1 p.2 := by
  decide +kernel
theorem graphRow : ∀ i j : Fin 6, reference (pt 6 (pairCode (i,j))) =
    (33598 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel
def samplePairs : List (Fin 6 × Fin 6) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def M_ : ℕ := 2097151

def Y_ : ℕ := 4542

def XS_ : List ℕ := [63, 1986, 30852, 233736, 860688, 1721376]

def PD_ : List (ℕ × ℕ) := [(1, 6497), (2, 5585), (3, 5001), (4, 4261), (5, 4403), (6, 4600), (7, 4509), (8, 4527), (9, 438), (10, 442), (11, 444), (12, 447), (13, 190), (14, 62), (15, 62), (16, 30), (17, 14), (18, 6), (19, 2)]

def PM_ : List (ℕ × ℕ) := [(0, 4542), (6, 4542), (9, 4542), (10, 4542), (11, 4542), (13, 4542), (14, 4542), (15, 4542), (16, 4542), (17, 4542), (18, 4542), (19, 4542), (20, 4542)]

def G_ : List (List ℕ) := [[0,1,2,3,5,4,6,7,8,10,9,11,12,14,13,15,17,16,20,19,18],[0,1,3,2,4,5,6,8,7,9,10,15,12,16,17,11,13,14,18,19,20],[0,1,3,2,5,4,6,8,7,10,9,15,12,17,16,11,14,13,20,19,18],[0,2,1,3,4,5,11,7,12,13,14,6,8,9,10,15,16,17,18,19,20],[0,2,1,3,5,4,11,7,12,14,13,6,8,10,9,15,17,16,20,19,18],[0,2,3,1,4,5,11,12,7,13,14,15,8,16,17,6,9,10,18,19,20],[0,2,3,1,5,4,11,12,7,14,13,15,8,17,16,6,10,9,20,19,18],[0,3,1,2,4,5,15,8,12,16,17,6,7,9,10,11,13,14,18,19,20],[0,3,1,2,5,4,15,8,12,17,16,6,7,10,9,11,14,13,20,19,18],[0,3,2,1,4,5,15,12,8,16,17,11,7,13,14,6,9,10,18,19,20],[0,3,2,1,5,4,15,12,8,17,16,11,7,14,13,6,10,9,20,19,18]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,63,6082,260540] BT.lf) [2,63,6130,260492] BT.lf) [2,191,32710,233784] (BT.nd (BT.nd BT.lf [2,191,32758,233736] BT.lf) [2,1986,30908,233791] BT.lf)) [2,1986,30910,233791] (BT.nd (BT.nd (BT.nd BT.lf [2,1990,30911,233784] BT.lf) [2,2002,30892,233791] BT.lf) [2,2038,30911,233788] (BT.nd BT.lf [3,2,2047,30852,233784] BT.lf))) [3,16,1986,30892,233791] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,18,2047,30852,233768] BT.lf) [3,48,63,6082,260492] BT.lf) [3,48,191,32710,233736] (BT.nd (BT.nd BT.lf [3,48,1986,30860,233791] BT.lf) [3,50,2047,30852,233736] BT.lf)) [3,50,2047,30852,233786] (BT.nd (BT.nd (BT.nd BT.lf [3,54,1986,30911,233736] BT.lf) [3,62,1986,30852,233736] BT.lf) [3,63,128,32710,233784] (BT.nd BT.lf [3,63,128,32758,233736] BT.lf)))) [3,63,176,32710,233736] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,63,450,6276,2094904] BT.lf) [3,63,450,30852,233784] BT.lf) [3,63,498,30852,233736] (BT.nd (BT.nd BT.lf [3,63,962,30852,233784] BT.lf) [3,63,1010,30852,233736] BT.lf)) [3,63,1986,30852,233784] (BT.nd (BT.nd (BT.nd BT.lf [3,63,1986,30852,233786] BT.lf) [3,63,1986,30852,233790] BT.lf) [3,63,1986,30852,233912] (BT.nd BT.lf [3,63,1986,30852,758072] BT.lf))) [3,63,1986,30852,2068792] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,63,1986,30854,233784] BT.lf) [3,63,1986,30860,233784] BT.lf) [3,63,1986,30868,233768] (BT.nd BT.lf [3,63,1986,30868,233770] BT.lf)) [3,63,1986,30868,233772] (BT.nd (BT.nd (BT.nd BT.lf [3,63,1986,30868,233784] BT.lf) [3,63,1986,30868,233788] BT.lf) [3,63,1986,30868,758056] (BT.nd BT.lf [3,63,1986,30900,233784] BT.lf))))) [3,63,1986,30900,233788] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,63,1986,30900,233864] BT.lf) [3,63,1986,30900,758024] BT.lf) [3,63,1986,30902,233786] (BT.nd (BT.nd BT.lf [3,63,1986,30908,233791] BT.lf) [3,63,2002,30868,233768] BT.lf)) [3,63,2034,30900,233784] (BT.nd (BT.nd (BT.nd BT.lf [3,63,6082,260492,860720] BT.lf) [3,63,6082,260492,2057776] BT.lf) [3,63,6082,260492,2058226] (BT.nd BT.lf [3,63,6082,260492,2061872] BT.lf))) [3,63,6082,260492,2062322] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,63,6082,260492,2064052] BT.lf) [3,63,6082,260492,2097084] BT.lf) [3,63,6082,260508,1721376] (BT.nd BT.lf [3,63,6082,1047452,1834412] BT.lf)) [3,63,6086,260492,2057776] (BT.nd (BT.nd (BT.nd BT.lf [3,63,6098,260492,1721376] BT.lf) [3,63,32710,1029016,1824168] BT.lf) [3,191,1986,30852,233784] (BT.nd BT.lf [3,191,1986,30900,233736] BT.lf)))) [3,191,32710,233736,860720] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,191,32710,233736,2057776] BT.lf) [3,191,32710,233736,2057904] BT.lf) [3,191,32710,233736,2058226] (BT.nd (BT.nd BT.lf [3,191,32710,233736,2064374] BT.lf) [3,191,32710,233736,2094904] BT.lf)) [3,191,32710,233752,1721376] (BT.nd (BT.nd (BT.nd BT.lf [3,191,32710,233864,2057776] BT.lf) [3,191,32710,1028888,1824040] BT.lf) [3,191,32726,233736,1721376] (BT.nd BT.lf [3,191,233736,884694,1736678] BT.lf))) [3,447,30852,233736,2058226] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,447,30852,235466,2057776] BT.lf) [3,1716,1986,30911,233736] BT.lf) [3,1986,2038,30911,233736] (BT.nd BT.lf [3,1986,2047,30852,233786] BT.lf)) [3,1986,30852,233784,524351] (BT.nd (BT.nd (BT.nd BT.lf [3,1986,30908,233791] BT.lf) [3,1986,30908,233791,860688] BT.lf) [3,1986,30908,233791,1028888] (BT.nd BT.lf [3,1986,30908,233791,2057776] BT.lf)))))) [3,1986,30908,233791,2094904] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,1986,30911,233791,2097084] BT.lf) [4,0,63,1986,30852,233784] BT.lf) [4,2,48,2047,30852,233736] (BT.nd (BT.nd BT.lf [4,2,63,1986,30852,233784] BT.lf) [4,2,63,2034,30852,233736] BT.lf)) [4,15,48,1986,30852,233736] (BT.nd (BT.nd (BT.nd BT.lf [4,16,34,2047,30852,233736] BT.lf) [4,16,63,1986,30852,233768] BT.lf) [4,16,63,1986,30852,233770] (BT.nd BT.lf [4,16,63,1986,30852,233784] BT.lf))) [4,16,63,1986,30852,758056] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,16,63,1986,30868,233768] BT.lf) [4,16,63,1986,30884,233768] BT.lf) [4,16,63,6082,260492,1721376] (BT.nd BT.lf [4,16,191,32710,233736,1721376] BT.lf)) [4,18,63,1986,30852,233768] (BT.nd (BT.nd (BT.nd BT.lf [4,18,63,2018,30852,233736] BT.lf) [4,31,48,1986,30852,233736] BT.lf) [4,48,63,128,32710,233736] (BT.nd BT.lf [4,48,63,450,30852,233736] BT.lf)))) [4,48,63,962,30852,233736] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,48,63,1986,30852,233736] BT.lf) [4,48,63,1986,30852,233738] BT.lf) [4,48,63,1986,30852,233752] (BT.nd (BT.nd BT.lf [4,48,63,1986,30852,233784] BT.lf) [4,48,63,1986,30852,233864] BT.lf)) [4,48,63,1986,30852,758024] (BT.nd (BT.nd (BT.nd BT.lf [4,48,63,1986,30900,233784] BT.lf) [4,48,191,1986,30852,233736] BT.lf) [4,48,1986,30852,233736,524351] (BT.nd BT.lf [4,50,63,1986,30852,233736] BT.lf))) [4,50,63,1986,30852,233786] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,50,63,2002,30852,233736] BT.lf) [4,50,63,2034,30852,233736] BT.lf) [4,50,63,2047,30852,233736] (BT.nd BT.lf [4,50,1986,2047,30852,233736] BT.lf)) [4,50,2047,30852,233736] (BT.nd (BT.nd (BT.nd BT.lf [4,50,2047,30852,233736,860688] BT.lf) [4,50,2047,30852,233736,862162] BT.lf) [4,50,2047,30852,233736,2057776] (BT.nd BT.lf [4,50,2047,30852,233736,2058226] BT.lf))))) [4,54,63,1986,30852,233736] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,63,1986,30852,233784] BT.lf) [4,63,128,1986,30852,233784] BT.lf) [4,63,128,1986,30900,233736] (BT.nd (BT.nd BT.lf [4,63,128,32710,233736,860720] BT.lf) [4,63,128,32710,233736,2057776] BT.lf)) [4,63,128,32710,233736,2057904] (BT.nd (BT.nd (BT.nd BT.lf [4,63,128,32710,233736,2058226] BT.lf) [4,63,128,32710,233736,2064374] BT.lf) [4,63,128,32710,233736,2094904] (BT.nd BT.lf [4,63,128,32710,233752,1721376] BT.lf))) [4,63,128,32710,233864,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,128,32710,1028888,1824040] BT.lf) [4,63,128,32726,233736,1721376] BT.lf) [4,63,128,233736,884694,1736678] (BT.nd BT.lf [4,63,130,32710,233736,2057776] BT.lf)) [4,63,144,32710,233736,1721376] (BT.nd (BT.nd (BT.nd BT.lf [4,63,176,1986,30852,233736] BT.lf) [4,63,191,32710,233736,2057776] BT.lf) [4,63,384,30852,233736,2058226] (BT.nd BT.lf [4,63,384,30852,235466,2057776] BT.lf)))) [4,63,386,30852,233736,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,450,6276,233736,2057776] BT.lf) [4,63,450,30852,39375,2094904] BT.lf) [4,63,450,30852,233736,2057776] (BT.nd (BT.nd BT.lf [4,63,450,30852,233736,2058226] BT.lf) [4,63,450,30852,233736,2064052] BT.lf)) [4,63,512,1986,30852,233784] (BT.nd (BT.nd (BT.nd BT.lf [4,63,512,2034,30852,233736] BT.lf) [4,63,528,1986,30852,233768] BT.lf) [4,63,528,2018,30852,233736] (BT.nd BT.lf [4,63,528,2034,30852,233736] BT.lf))) [4,63,560,1986,30852,233736] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,962,14468,233736,2057776] BT.lf) [4,63,962,14468,860688,1824040] BT.lf) [4,63,962,30852,233736,860720] (BT.nd BT.lf [4,63,962,30852,233736,1721392] BT.lf)) [4,63,962,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [4,63,962,30852,233736,2058226] BT.lf) [4,63,962,30852,233736,2064052] BT.lf) [4,63,962,30852,233752,1721376] (BT.nd BT.lf [4,63,962,30852,233768,860688] BT.lf))))))) [4,63,962,30852,1028888,1824040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,978,30852,233736,1721376] BT.lf) [4,63,994,30852,233736,860688] BT.lf) [4,63,1536,1986,30852,233784] (BT.nd (BT.nd BT.lf [4,63,1536,2034,30852,233736] BT.lf) [4,63,1584,1986,30852,233736] BT.lf)) [4,63,1584,2034,30852,233736] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1716,1986,30852,233736] BT.lf) [4,63,1984,30852,233736,2058226] BT.lf) [4,63,1986,1986,30852,233784] (BT.nd BT.lf [4,63,1986,2002,30852,233768] BT.lf))) [4,63,1986,2034,30852,233736] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,2034,30852,233784] BT.lf) [4,63,1986,2038,30852,233736] BT.lf) [4,63,1986,2047,30852,233784] (BT.nd BT.lf [4,63,1986,6082,260492,2057776] BT.lf)) [4,63,1986,26160,30852,233736] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,26610,30852,233736] BT.lf) [4,63,1986,30852,32710,233784] BT.lf) [4,63,1986,30852,32758,233736] (BT.nd BT.lf [4,63,1986,30852,39360,2094904] BT.lf)))) [4,63,1986,30852,39375,233784] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,39375,2094904] BT.lf) [4,63,1986,30852,39423,2094904] BT.lf) [4,63,1986,30852,233736,336432] (BT.nd (BT.nd BT.lf [4,63,1986,30852,233736,524336] BT.lf) [4,63,1986,30852,233736,795184] BT.lf)) [4,63,1986,30852,233736,860720] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233736,860722] BT.lf) [4,63,1986,30852,233736,860726] BT.lf) [4,63,1986,30852,233736,860848] (BT.nd BT.lf [4,63,1986,30852,233736,861744] BT.lf))) [4,63,1986,30852,233736,861876] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233736,862194] BT.lf) [4,63,1986,30852,233736,862198] BT.lf) [4,63,1986,30852,233736,878128] (BT.nd BT.lf [4,63,1986,30852,233736,878578] BT.lf)) [4,63,1986,30852,233736,884726] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233736,1533488] BT.lf) [4,63,1986,30852,233736,1836592] BT.lf) [4,63,1986,30852,233736,1861168] (BT.nd BT.lf [4,63,1986,30852,233736,1861362] BT.lf))))) [4,63,1986,30852,233736,1861618] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233736,1910320] BT.lf) [4,63,1986,30852,233736,1926704] BT.lf) [4,63,1986,30852,233736,1926898] (BT.nd (BT.nd BT.lf [4,63,1986,30852,233736,1927154] BT.lf) [4,63,1986,30852,233736,2057776] BT.lf)) [4,63,1986,30852,233736,2057778] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233736,2057782] BT.lf) [4,63,1986,30852,233736,2057904] BT.lf) [4,63,1986,30852,233736,2057906] (BT.nd BT.lf [4,63,1986,30852,233736,2057970] BT.lf))) [4,63,1986,30852,233736,2058160] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233736,2058224] BT.lf) [4,63,1986,30852,233736,2058226] BT.lf) [4,63,1986,30852,233736,2058230] (BT.nd BT.lf [4,63,1986,30852,233736,2060016] BT.lf)) [4,63,1986,30852,233736,2062322] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233736,2064374] BT.lf) [4,63,1986,30852,233736,2097136] BT.lf) [4,63,1986,30852,233736,2097138] (BT.nd BT.lf [4,63,1986,30852,233736,2097150] BT.lf)))) [4,63,1986,30852,233738,860720] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233738,2057776] BT.lf) [4,63,1986,30852,233738,2057778] BT.lf) [4,63,1986,30852,233738,2058226] (BT.nd (BT.nd BT.lf [4,63,1986,30852,233738,2064052] BT.lf) [4,63,1986,30852,233738,2094904] BT.lf)) [4,63,1986,30852,233738,2094906] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233742,2057776] BT.lf) [4,63,1986,30852,233752,233768] BT.lf) [4,63,1986,30852,233752,233784] (BT.nd BT.lf [4,63,1986,30852,233752,524320] BT.lf))) [4,63,1986,30852,233752,860720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233752,1197088] BT.lf) [4,63,1986,30852,233752,1590304] BT.lf) [4,63,1986,30852,233752,1704992] (BT.nd BT.lf [4,63,1986,30852,233752,1721376] BT.lf)) [4,63,1986,30852,233752,1721378] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233752,1721384] BT.lf) [4,63,1986,30852,233752,1721392] BT.lf) [4,63,1986,30852,233752,1721400] (BT.nd BT.lf [4,63,1986,30852,233752,1721504] BT.lf)))))) [4,63,1986,30852,233752,1721632] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233752,1721888] BT.lf) [4,63,1986,30852,233752,1722338] BT.lf) [4,63,1986,30852,233752,1722354] (BT.nd (BT.nd BT.lf [4,63,1986,30852,233752,1736678] BT.lf) [4,63,1986,30852,233752,1786912] BT.lf)) [4,63,1986,30852,233752,1786928] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233752,1824040] BT.lf) [4,63,1986,30852,233752,1824056] BT.lf) [4,63,1986,30852,233752,1824746] (BT.nd BT.lf [4,63,1986,30852,233752,1824762] BT.lf))) [4,63,1986,30852,233752,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233752,2058226] BT.lf) [4,63,1986,30852,233752,2094904] BT.lf) [4,63,1986,30852,233752,2097120] (BT.nd BT.lf [4,63,1986,30852,233754,1721376] BT.lf)) [4,63,1986,30852,233754,1721394] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233754,1722338] BT.lf) [4,63,1986,30852,233754,1735844] BT.lf) [4,63,1986,30852,233754,1824040] (BT.nd BT.lf [4,63,1986,30852,233754,1824058] BT.lf)))) [4,63,1986,30852,233754,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233754,2058226] BT.lf) [4,63,1986,30852,233758,1721376] BT.lf) [4,63,1986,30852,233784] (BT.nd (BT.nd BT.lf [4,63,1986,30852,233784,233784] BT.lf) [4,63,1986,30852,233784,233791] BT.lf)) [4,63,1986,30852,233784,235466] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233784,235514] BT.lf) [4,63,1986,30852,233784,375775] BT.lf) [4,63,1986,30852,233784,524288] (BT.nd BT.lf [4,63,1986,30852,233784,860688] BT.lf))) [4,63,1986,30852,233784,860720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233784,860735] BT.lf) [4,63,1986,30852,233784,862162] BT.lf) [4,63,1986,30852,233784,1028888] (BT.nd BT.lf [4,63,1986,30852,233784,1028920] BT.lf)) [4,63,1986,30852,233784,1863367] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233784,1863415] BT.lf) [4,63,1986,30852,233784,2057776] BT.lf) [4,63,1986,30852,233784,2057791] (BT.nd BT.lf [4,63,1986,30852,233784,2058226] BT.lf))))) [4,63,1986,30852,233784,2066299] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233784,2094904] BT.lf) [4,63,1986,30852,233784,2097088] BT.lf) [4,63,1986,30852,233784,2097103] (BT.nd (BT.nd BT.lf [4,63,1986,30852,233786] BT.lf) [4,63,1986,30852,233786,860688] BT.lf)) [4,63,1986,30852,233786,862162] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233786,2057776] BT.lf) [4,63,1986,30852,233786,2058226] BT.lf) [4,63,1986,30852,233791,860728] (BT.nd BT.lf [4,63,1986,30852,233791,1028920] BT.lf))) [4,63,1986,30852,233791,2057784] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233791,2094904] BT.lf) [4,63,1986,30852,233791,2095098] BT.lf) [4,63,1986,30852,233864,860720] (BT.nd BT.lf [4,63,1986,30852,233864,2057776] BT.lf)) [4,63,1986,30852,233864,2057904] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,233864,2058226] BT.lf) [4,63,1986,30852,233864,2094904] BT.lf) [4,63,1986,30852,233864,2095032] (BT.nd BT.lf [4,63,1986,30852,233866,2057776] BT.lf)))) [4,63,1986,30852,233880,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,234264,1824040] BT.lf) [4,63,1986,30852,235983,2094904] BT.lf) [4,63,1986,30852,373528,1824040] (BT.nd (BT.nd BT.lf [4,63,1986,30852,375759,1824056] BT.lf) [4,63,1986,30852,375775,1824056] BT.lf)) [4,63,1986,30852,504600,1824040] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,758024,860720] BT.lf) [4,63,1986,30852,758024,2057776] BT.lf) [4,63,1986,30852,758024,2058226] (BT.nd BT.lf [4,63,1986,30852,758024,2094904] BT.lf))) [4,63,1986,30852,758040,1721376] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,758040,1721392] BT.lf) [4,63,1986,30852,758040,1722338] BT.lf) [4,63,1986,30852,758040,1824040] (BT.nd BT.lf [4,63,1986,30852,758040,1824056] BT.lf)) [4,63,1986,30852,758040,2057776] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,860688,1806632] BT.lf) [4,63,1986,30852,865040,1824040] BT.lf) [4,63,1986,30852,897816,1824040] (BT.nd BT.lf [4,63,1986,30852,900048,1824040] BT.lf)))))))) [4,63,1986,30852,1020696,1824040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,1028880,1824040] BT.lf) [4,63,1986,30852,1028888,1824040] BT.lf) [4,63,1986,30852,1028888,1824042] (BT.nd (BT.nd BT.lf [4,63,1986,30852,1028888,1824056] BT.lf) [4,63,1986,30852,1028888,1824168] BT.lf)) [4,63,1986,30852,1028890,1824042] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30852,1029016,1824168] BT.lf) [4,63,1986,30852,1863367] BT.lf) [4,63,1986,30854,233738,2057776] (BT.nd BT.lf [4,63,1986,30854,233752,1721376] BT.lf))) [4,63,1986,30854,1028888,1824040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30860,233752,1721376] BT.lf) [4,63,1986,30860,233791,2057776] BT.lf) [4,63,1986,30860,1028888,1824040] (BT.nd BT.lf [4,63,1986,30868,233752,1721376] BT.lf)) [4,63,1986,30868,233752,1721392] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30868,233752,1722338] BT.lf) [4,63,1986,30868,233752,1735844] BT.lf) [4,63,1986,30868,233752,1735860] (BT.nd BT.lf [4,63,1986,30868,233752,2057776] BT.lf)))) [4,63,1986,30868,233756,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30868,233768] BT.lf) [4,63,1986,30868,233768,860688] BT.lf) [4,63,1986,30868,233791,1824040] (BT.nd (BT.nd BT.lf [4,63,1986,30868,233864,1721376] BT.lf) [4,63,1986,30868,375775,1824040] BT.lf)) [4,63,1986,30868,758024,1721376] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30868,1028888,1824040] BT.lf) [4,63,1986,30870,233754,1721376] BT.lf) [4,63,1986,30876,233791,1721376] (BT.nd BT.lf [4,63,1986,30876,1028888,1824040] BT.lf))) [4,63,1986,30900,233784] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,30900,233784,860688] BT.lf) [4,63,1986,30900,233784,2057776] BT.lf) [4,63,1986,30900,1863415] (BT.nd BT.lf [4,63,1986,31108,235466,2057776] BT.lf)) [4,63,1986,31108,1028888,1824040] (BT.nd (BT.nd (BT.nd BT.lf [4,63,1986,39375,883348,1824040] BT.lf) [4,63,1986,39375,883348,2094904] BT.lf) [4,63,1986,39375,2064052,2094904] (BT.nd BT.lf [4,63,1986,260492,864784,1725472] BT.lf))))) [4,63,2002,30868,233752,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,63,6082,260492,860688,1721376] BT.lf) [4,63,6082,260492,860688,1722338] BT.lf) [4,63,6082,260492,860688,1725472] (BT.nd (BT.nd BT.lf [4,63,6082,260492,860688,1726434] BT.lf) [4,63,6082,260492,860688,1735844] BT.lf)) [4,63,6082,260492,860688,1834412] (BT.nd (BT.nd (BT.nd BT.lf [4,63,6082,260492,860688,2057776] BT.lf) [4,63,6082,260492,2057776] BT.lf) [4,63,6086,260492,860688,1721376] (BT.nd BT.lf [4,63,32710,235466,260492,2057776] BT.lf))) [4,128,191,32710,233736,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,191,1986,30852,233736,860720] BT.lf) [4,191,1986,30852,233736,2057776] BT.lf) [4,191,1986,30852,233736,2057904] (BT.nd BT.lf [4,191,1986,30852,233736,2058226] BT.lf)) [4,191,1986,30852,233736,2094904] (BT.nd (BT.nd (BT.nd BT.lf [4,191,1986,30852,233752,1721376] BT.lf) [4,191,1986,30852,233864,2057776] BT.lf) [4,191,1986,30852,1028888,1824040] (BT.nd BT.lf [4,191,1986,30868,233736,1721376] BT.lf)))) [4,191,1986,32710,233736,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,191,1986,233736,883348,1735844] BT.lf) [4,191,32710,233736,860688,1721376] BT.lf) [4,191,32710,233736,860688,1721504] (BT.nd (BT.nd BT.lf [4,191,32710,233736,860688,1722338] BT.lf) [4,191,32710,233736,860688,1736678] BT.lf)) [4,191,32710,233736,860688,1824040] (BT.nd (BT.nd (BT.nd BT.lf [4,191,32710,233736,860688,2057776] BT.lf) [4,191,32710,233736,2057776] BT.lf) [4,191,32710,233864,860688,1721376] (BT.nd BT.lf [4,447,1986,30852,233736,2057776] BT.lf))) [4,447,30852,233736,860688,1722338] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,447,30852,235466,860688,1721376] BT.lf) [4,1986,2047,30852,233791,2094904] BT.lf) [4,1986,30852,233784,2097088] (BT.nd BT.lf [4,1986,30911,233791,260492,2057776] BT.lf)) [4,1986,30911,233791,860688,1834412] (BT.nd (BT.nd (BT.nd BT.lf [4,1986,30911,233791,883348,1824040] BT.lf) [5,0,48,63,1986,30852,233736] BT.lf) [5,0,63,1986,30852,233736,860720] (BT.nd BT.lf [5,0,63,1986,30852,233736,2057776] BT.lf)))))) [5,0,63,1986,30852,233752,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2,48,63,1986,30852,233736] BT.lf) [5,2,63,1986,30852,233736,860720] BT.lf) [5,2,63,1986,30852,233736,2057776] (BT.nd (BT.nd BT.lf [5,2,63,1986,30852,233736,2057778] BT.lf) [5,2,63,1986,30852,233736,2058226] BT.lf)) [5,2,63,1986,30852,233736,2064052] (BT.nd (BT.nd (BT.nd BT.lf [5,2,63,1986,30852,233738,2057776] BT.lf) [5,2,63,1986,30852,233752,1721376] BT.lf) [5,2,63,1986,30852,1028888,1824040] (BT.nd BT.lf [5,2,63,2002,30852,233736,1721376] BT.lf))) [5,2,63,2047,30852,233736,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2,63,30852,233736,862162,1722338] BT.lf) [5,6,63,1986,30852,233736,2057776] BT.lf) [5,15,63,1986,30852,233736] (BT.nd BT.lf [5,15,63,1986,30852,233736,2057776] BT.lf)) [5,16,32,63,1986,30852,233736] (BT.nd (BT.nd (BT.nd BT.lf [5,16,32,63,1986,30852,233752] BT.lf) [5,16,34,63,1986,30852,233736] BT.lf) [5,16,47,1986,30852,233736,1721376] (BT.nd BT.lf [5,16,48,63,1986,30852,233736] BT.lf)))) [5,16,63,128,32710,233736,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16,63,962,30852,233736,1721376] BT.lf) [5,16,63,1056,1986,30852,233736] BT.lf) [5,16,63,1474,30852,233736,1721376] (BT.nd (BT.nd BT.lf [5,16,63,1986,2018,30852,233736] BT.lf) [5,16,63,1986,30852,233736,524320] BT.lf)) [5,16,63,1986,30852,233736,860720] (BT.nd (BT.nd (BT.nd BT.lf [5,16,63,1986,30852,233736,1197088] BT.lf) [5,16,63,1986,30852,233736,1590304] BT.lf) [5,16,63,1986,30852,233736,1721376] (BT.nd BT.lf [5,16,63,1986,30852,233736,1721378] BT.lf))) [5,16,63,1986,30852,233736,1721392] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16,63,1986,30852,233736,1721504] BT.lf) [5,16,63,1986,30852,233736,1721888] BT.lf) [5,16,63,1986,30852,233736,1722338] (BT.nd BT.lf [5,16,63,1986,30852,233736,1722354] BT.lf)) [5,16,63,1986,30852,233736,1736678] (BT.nd (BT.nd (BT.nd BT.lf [5,16,63,1986,30852,233736,2057776] BT.lf) [5,16,63,1986,30852,233736,2058226] BT.lf) [5,16,63,1986,30852,233736,2097120] (BT.nd BT.lf [5,16,63,1986,30852,233738,1721376] BT.lf))))) [5,16,63,1986,30852,233752,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16,63,1986,30852,233752,1721392] BT.lf) [5,16,63,1986,30852,233752,1722338] BT.lf) [5,16,63,1986,30852,233752,1824040] (BT.nd (BT.nd BT.lf [5,16,63,1986,30852,233752,1824056] BT.lf) [5,16,63,1986,30852,233752,2057776] BT.lf)) [5,16,63,1986,30852,233768] (BT.nd (BT.nd (BT.nd BT.lf [5,16,63,1986,30852,233768,860688] BT.lf) [5,16,63,1986,30852,233768,1721376] BT.lf) [5,16,63,1986,30852,233791,1824040] (BT.nd BT.lf [5,16,63,1986,30852,233864,1721376] BT.lf))) [5,16,63,1986,30852,375775,1824040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16,63,1986,30852,758024,1721376] BT.lf) [5,16,63,1986,30852,1028888,1824040] BT.lf) [5,16,63,1986,30868,233752,1721376] (BT.nd BT.lf [5,16,191,1986,30852,233736,1721376] BT.lf)) [5,18,63,1986,30852,233736,1721376] (BT.nd (BT.nd (BT.nd BT.lf [5,18,63,1986,30852,233736,1721394] BT.lf) [5,18,63,1986,30852,233736,1722338] BT.lf) [5,18,63,1986,30852,233736,1735844] (BT.nd BT.lf [5,18,63,1986,30852,233736,2057776] BT.lf)))) [5,18,63,1986,30852,233736,2058226] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,18,63,1986,30852,233754,1721376] BT.lf) [5,18,63,2002,30852,233736,1721376] BT.lf) [5,18,63,2047,30852,233736,1721376] (BT.nd (BT.nd BT.lf [5,18,63,30852,233736,862162,1722338] BT.lf) [5,22,63,1986,30852,233736,1721376] BT.lf)) [5,31,63,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [5,48,48,63,1986,30852,233736] BT.lf) [5,48,63,63,1986,30852,233736] BT.lf) [5,48,63,128,1986,30852,233736] (BT.nd BT.lf [5,48,63,512,1986,30852,233736] BT.lf))) [5,48,63,1536,1986,30852,233736] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,48,63,1986,1986,30852,233736] BT.lf) [5,48,63,1986,2034,30852,233736] BT.lf) [5,48,63,1986,2047,30852,233736] (BT.nd BT.lf [5,48,63,1986,30852,32710,233736] BT.lf)) [5,48,63,1986,30852,39375,233736] (BT.nd (BT.nd (BT.nd BT.lf [5,48,63,1986,30852,233736] BT.lf) [5,48,63,1986,30852,233736,375775] BT.lf) [5,48,63,1986,30852,233736,524288] (BT.nd BT.lf [5,48,63,1986,30852,233736,860688] BT.lf))))))) [5,48,63,1986,30852,233736,860720] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,48,63,1986,30852,233736,860735] BT.lf) [5,48,63,1986,30852,233736,862162] BT.lf) [5,48,63,1986,30852,233736,1863415] (BT.nd (BT.nd BT.lf [5,48,63,1986,30852,233736,2057776] BT.lf) [5,48,63,1986,30852,233736,2057791] BT.lf)) [5,48,63,1986,30852,233736,2058226] (BT.nd (BT.nd (BT.nd BT.lf [5,48,63,1986,30852,233736,2097088] BT.lf) [5,48,63,1986,30852,233736,2097103] BT.lf) [5,48,63,1986,30852,233784] (BT.nd BT.lf [5,48,63,1986,30852,233784,860688] BT.lf))) [5,48,63,1986,30852,233784,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,48,63,1986,30852,1863415] BT.lf) [5,48,1986,30852,233736,2097088] BT.lf) [5,50,63,1986,30852,233736] (BT.nd BT.lf [5,50,63,1986,30852,233736,860688] BT.lf)) [5,50,63,1986,30852,233736,862162] (BT.nd (BT.nd (BT.nd BT.lf [5,50,63,1986,30852,233736,2057776] BT.lf) [5,50,63,1986,30852,233736,2058226] BT.lf) [5,55,63,1986,30852,233736,2057776] (BT.nd BT.lf [5,63,63,1986,30852,233736,860720] BT.lf)))) [5,63,63,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,63,1986,30852,233736,2058226] BT.lf) [5,63,63,1986,30852,233752,1721376] BT.lf) [5,63,63,1986,30852,1028888,1824040] (BT.nd (BT.nd BT.lf [5,63,128,1986,30852,233736,860720] BT.lf) [5,63,128,1986,30852,233736,2057776] BT.lf)) [5,63,128,1986,30852,233736,2057904] (BT.nd (BT.nd (BT.nd BT.lf [5,63,128,1986,30852,233736,2058226] BT.lf) [5,63,128,1986,30852,233736,2094904] BT.lf) [5,63,128,1986,30852,233752,1721376] (BT.nd BT.lf [5,63,128,1986,30852,233864,2057776] BT.lf))) [5,63,128,1986,30852,1028888,1824040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,128,1986,30868,233736,1721376] BT.lf) [5,63,128,1986,32710,233736,2057776] BT.lf) [5,63,128,1986,233736,883348,1735844] (BT.nd BT.lf [5,63,128,32710,233736,860688,1721376] BT.lf)) [5,63,128,32710,233736,860688,1721504] (BT.nd (BT.nd (BT.nd BT.lf [5,63,128,32710,233736,860688,1722338] BT.lf) [5,63,128,32710,233736,860688,1736678] BT.lf) [5,63,128,32710,233736,860688,1824040] (BT.nd BT.lf [5,63,128,32710,233736,860688,2057776] BT.lf))))) [5,63,128,32710,233736,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,128,32710,233864,860688,1721376] BT.lf) [5,63,130,1986,30852,233736,2057776] BT.lf) [5,63,130,32710,233736,860688,1721376] (BT.nd (BT.nd BT.lf [5,63,144,1986,30852,233736,1721376] BT.lf) [5,63,191,1986,30852,233736,2057776] BT.lf)) [5,63,191,32710,233736,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [5,63,384,1986,30852,233736,2057776] BT.lf) [5,63,384,30852,233736,860688,1722338] BT.lf) [5,63,384,30852,235466,860688,1721376] (BT.nd BT.lf [5,63,386,30852,233736,860688,1721376] BT.lf))) [5,63,450,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,450,30852,39375,233736] BT.lf) [5,63,450,30852,39375,233736,2057776] BT.lf) [5,63,450,30852,233736,860688,1721376] (BT.nd BT.lf [5,63,450,30852,233736,860688,2057776] BT.lf)) [5,63,450,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [5,63,512,1986,30852,233736,860720] BT.lf) [5,63,512,1986,30852,233736,1721392] BT.lf) [5,63,512,1986,30852,233736,2057776] (BT.nd BT.lf [5,63,512,1986,30852,233736,2058226] BT.lf)))) [5,63,512,1986,30852,233736,2064052] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,512,1986,30852,233752,1721376] BT.lf) [5,63,512,1986,30852,233768,860688] BT.lf) [5,63,512,1986,30852,1028888,1824040] (BT.nd (BT.nd BT.lf [5,63,512,2002,30852,233736,1721376] BT.lf) [5,63,512,2018,30852,233736,860688] BT.lf)) [5,63,512,30852,233736,862162,1722338] (BT.nd (BT.nd (BT.nd BT.lf [5,63,514,1986,30852,233736,2057776] BT.lf) [5,63,528,1056,1986,30852,233736] BT.lf) [5,63,528,1986,30852,233736,1721376] (BT.nd BT.lf [5,63,528,1986,30852,233736,1721904] BT.lf))) [5,63,528,1986,30852,233736,1722338] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,528,1986,30852,233736,1735844] BT.lf) [5,63,528,1986,30852,233736,2057776] BT.lf) [5,63,528,2002,30852,233736,1721376] (BT.nd BT.lf [5,63,528,2047,30852,233736,1722338] BT.lf)) [5,63,544,1986,30852,233736,860688] (BT.nd (BT.nd (BT.nd BT.lf [5,63,575,1986,30852,233736,2057776] BT.lf) [5,63,640,1986,30852,233736,2057776] BT.lf) [5,63,640,1986,30852,233736,2064052] (BT.nd BT.lf [5,63,640,1986,233736,883348,1735844] BT.lf)))))) [5,63,660,1986,30852,233736,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,962,1986,30852,233736,2057776] BT.lf) [5,63,962,14468,233736,860688,1721376] BT.lf) [5,63,962,30852,233736,336400,1721376] (BT.nd (BT.nd BT.lf [5,63,962,30852,233736,375775,2057776] BT.lf) [5,63,962,30852,233736,860688,1721376] BT.lf)) [5,63,962,30852,233736,860688,1722338] (BT.nd (BT.nd (BT.nd BT.lf [5,63,962,30852,233736,860688,1735844] BT.lf) [5,63,962,30852,233736,860688,2057776] BT.lf) [5,63,962,30852,233736,861138,1721376] (BT.nd BT.lf [5,63,962,30852,233736,862162,1721376] BT.lf))) [5,63,962,30852,233736,883348,1721376] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,962,30852,233736,1721376,2057776] BT.lf) [5,63,962,30852,233736,2057776] BT.lf) [5,63,962,30852,375775,860688,1824040] (BT.nd BT.lf [5,63,1536,1986,30852,233736,2057776] BT.lf)) [5,63,1536,1986,30852,233736,2058226] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1536,1986,30852,233736,2064052] BT.lf) [5,63,1538,1986,30852,233736,2057776] BT.lf) [5,63,1584,1986,2047,30852,233736] (BT.nd BT.lf [5,63,1584,1986,30852,233736] BT.lf)))) [5,63,1584,1986,30852,233736,860688] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1584,1986,30852,233736,2057776] BT.lf) [5,63,1599,1986,30852,233736,2057776] BT.lf) [5,63,1664,1986,30852,233736,2057776] (BT.nd (BT.nd BT.lf [5,63,1664,1986,30852,233736,2064052] BT.lf) [5,63,1730,1986,30852,233736,2057776] BT.lf)) [5,63,1984,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1984,30852,233736,860688,1722338] BT.lf) [5,63,1986,1986,30852,233736,860720] BT.lf) [5,63,1986,1986,30852,233736,2057776] (BT.nd BT.lf [5,63,1986,1986,30852,233736,2058226] BT.lf))) [5,63,1986,1986,30852,233736,2064052] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,1986,30852,233752,1721376] BT.lf) [5,63,1986,1986,30852,1028888,1824040] BT.lf) [5,63,1986,1990,30852,233736,2057776] (BT.nd BT.lf [5,63,1986,2002,30852,233736,1721376] BT.lf)) [5,63,1986,2002,30852,233736,1721392] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,2002,30852,233736,1722338] BT.lf) [5,63,1986,2002,30852,233736,1722354] BT.lf) [5,63,1986,2002,30852,233736,1735844] (BT.nd BT.lf [5,63,1986,2002,30852,233736,2057776] BT.lf))))) [5,63,1986,2002,30852,233752,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,2006,30852,233736,1721376] BT.lf) [5,63,1986,2034,30852,233736] BT.lf) [5,63,1986,2034,30852,233736,860688] (BT.nd (BT.nd BT.lf [5,63,1986,2034,30852,233736,2057776] BT.lf) [5,63,1986,2047,30852,233736,860720] BT.lf)) [5,63,1986,2047,30852,233736,861744] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,2047,30852,233736,2057776] BT.lf) [5,63,1986,2047,30852,233736,2058226] BT.lf) [5,63,1986,2047,30852,233736,2064052] (BT.nd BT.lf [5,63,1986,2047,30852,233752,1721376] BT.lf))) [5,63,1986,2047,30852,1028888,1824040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,2247,30852,233736] BT.lf) [5,63,1986,2247,30852,233736,2057776] BT.lf) [5,63,1986,2247,30852,233736,2094904] (BT.nd BT.lf [5,63,1986,2247,30852,2057776] BT.lf)) [5,63,1986,6082,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,6082,260492,860688,1721376] BT.lf) [5,63,1986,8704,30852,233736,2057776] BT.lf) [5,63,1986,8720,30852,233736,1721376] (BT.nd BT.lf [5,63,1986,10178,30852,233736,2057776] BT.lf)))) [5,63,1986,10194,30852,233736,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,26112,30852,233736,2057776] BT.lf) [5,63,1986,26562,30852,233736,2057776] BT.lf) [5,63,1986,30852,32710,233736,860720] (BT.nd (BT.nd BT.lf [5,63,1986,30852,32710,233736,2057776] BT.lf) [5,63,1986,30852,32710,233736,2058226] BT.lf)) [5,63,1986,30852,32710,233736,2064374] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,32710,233736,2094904] BT.lf) [5,63,1986,30852,32710,233752,1721376] BT.lf) [5,63,1986,30852,32710,1028888,1824040] (BT.nd BT.lf [5,63,1986,30852,32726,233736,1721376] BT.lf))) [5,63,1986,30852,32767,233736,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,39360,233736,2057776] BT.lf) [5,63,1986,30852,39375,233736] BT.lf) [5,63,1986,30852,39375,233736,2057776] (BT.nd BT.lf [5,63,1986,30852,39375,233736,2058226] BT.lf)) [5,63,1986,30852,39375,860688,1824040] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,39375,860688,2094904] BT.lf) [5,63,1986,30852,39375,1028888,2057776] BT.lf) [5,63,1986,30852,39375,1863415] (BT.nd BT.lf [5,63,1986,30852,39375,2057776,2094904] BT.lf))))))))) [5,63,1986,30852,39375,2094904] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,39423,233736,2057776] BT.lf) [5,63,1986,30852,40911,233736] BT.lf) [5,63,1986,30852,40911,233736,2057776] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,262094,2057776] BT.lf) [5,63,1986,30852,233736,270864,1721376] BT.lf)) [5,63,1986,30852,233736,270864,1824040] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,273111,2057776] BT.lf) [5,63,1986,30852,233736,273111,2094904] BT.lf) [5,63,1986,30852,233736,336400,1721376] (BT.nd BT.lf [5,63,1986,30852,233736,336400,1722338] BT.lf))) [5,63,1986,30852,233736,336400,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,336850,1721376] BT.lf) [5,63,1986,30852,233736,337874,1721376] BT.lf) [5,63,1986,30852,233736,375744,2057776] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,375759] BT.lf) [5,63,1986,30852,233736,375759,1721392] BT.lf)) [5,63,1986,30852,233736,375775,860720] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,375775,1721392] BT.lf) [5,63,1986,30852,233736,375775,2057776] BT.lf) [5,63,1986,30852,233736,375775,2058226] (BT.nd BT.lf [5,63,1986,30852,233736,375807,2057776] BT.lf)))) [5,63,1986,30852,233736,376799,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,524288,860720] BT.lf) [5,63,1986,30852,233736,524288,2057776] BT.lf) [5,63,1986,30852,233736,524288,2058226] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,524304,1721376] BT.lf) [5,63,1986,30852,233736,524304,1721392] BT.lf)) [5,63,1986,30852,233736,524304,1722338] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,524304,2057776] BT.lf) [5,63,1986,30852,233736,524351,2057776] BT.lf) [5,63,1986,30852,233736,524800,2057776] (BT.nd BT.lf [5,63,1986,30852,233736,524800,2058226] BT.lf))) [5,63,1986,30852,233736,524816,1721376] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,524816,1722338] BT.lf) [5,63,1986,30852,233736,524834,860688] BT.lf) [5,63,1986,30852,233736,526274,2057776] (BT.nd BT.lf [5,63,1986,30852,233736,526290,1721376] BT.lf)) [5,63,1986,30852,233736,786960,1721376] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,795152,1590304] BT.lf) [5,63,1986,30852,233736,795152,1721376] BT.lf) [5,63,1986,30852,233736,795152,1722338] (BT.nd BT.lf [5,63,1986,30852,233736,795152,1824040] BT.lf))))) [5,63,1986,30852,233736,795152,1992240] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,795152,2057776] BT.lf) [5,63,1986,30852,233736,796370,1721376] BT.lf) [5,63,1986,30852,233736,796626,1721376] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860672,2057776] BT.lf) [5,63,1986,30852,233736,860688,860720] BT.lf)) [5,63,1986,30852,233736,860688,860722] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860688,861744] BT.lf) [5,63,1986,30852,233736,860688,862194] BT.lf) [5,63,1986,30852,233736,860688,1721376] (BT.nd BT.lf [5,63,1986,30852,233736,860688,1721378] BT.lf))) [5,63,1986,30852,233736,860688,1721382] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860688,1721392] BT.lf) [5,63,1986,30852,233736,860688,1721394] BT.lf) [5,63,1986,30852,233736,860688,1721504] (BT.nd BT.lf [5,63,1986,30852,233736,860688,1721506] BT.lf)) [5,63,1986,30852,233736,860688,1721760] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860688,1721826] BT.lf) [5,63,1986,30852,233736,860688,1721888] BT.lf) [5,63,1986,30852,233736,860688,1721890] (BT.nd BT.lf [5,63,1986,30852,233736,860688,1721904] BT.lf)))) [5,63,1986,30852,233736,860688,1722016] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860688,1722082] BT.lf) [5,63,1986,30852,233736,860688,1722336] BT.lf) [5,63,1986,30852,233736,860688,1722338] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860688,1722342] BT.lf) [5,63,1986,30852,233736,860688,1722354] BT.lf)) [5,63,1986,30852,233736,860688,1726434] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860688,1730080] BT.lf) [5,63,1986,30852,233736,860688,1730530] BT.lf) [5,63,1986,30852,233736,860688,1736678] (BT.nd BT.lf [5,63,1986,30852,233736,860688,1760736] BT.lf))) [5,63,1986,30852,233736,860688,1834990] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860688,1861168] BT.lf) [5,63,1986,30852,233736,860688,1926704] BT.lf) [5,63,1986,30852,233736,860688,1992240] (BT.nd BT.lf [5,63,1986,30852,233736,860688,1994464] BT.lf)) [5,63,1986,30852,233736,860688,2057760] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860688,2057776] BT.lf) [5,63,1986,30852,233736,860688,2057778] BT.lf) [5,63,1986,30852,233736,860688,2057904] (BT.nd BT.lf [5,63,1986,30852,233736,860688,2058226] BT.lf)))))) [5,63,1986,30852,233736,860688,2064374] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860688,2097120] BT.lf) [5,63,1986,30852,233736,860688,2097122] BT.lf) [5,63,1986,30852,233736,860688,2097136] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860690,1721378] BT.lf) [5,63,1986,30852,233736,860690,1722338] BT.lf)) [5,63,1986,30852,233736,860690,1735844] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860690,2057776] BT.lf) [5,63,1986,30852,233736,860690,2057778] BT.lf) [5,63,1986,30852,233736,860720] (BT.nd BT.lf [5,63,1986,30852,233736,860720,860720] BT.lf))) [5,63,1986,30852,233736,860720,860735] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860720,862162] BT.lf) [5,63,1986,30852,233736,860720,862194] BT.lf) [5,63,1986,30852,233736,860720,1721407] (BT.nd BT.lf [5,63,1986,30852,233736,860720,1722338] BT.lf)) [5,63,1986,30852,233736,860720,1863415] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860720,2057776] BT.lf) [5,63,1986,30852,233736,860720,2097088] BT.lf) [5,63,1986,30852,233736,860720,2097119] (BT.nd BT.lf [5,63,1986,30852,233736,860722] BT.lf)))) [5,63,1986,30852,233736,860722,1722338] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860735,2057776] BT.lf) [5,63,1986,30852,233736,860735,2058226] BT.lf) [5,63,1986,30852,233736,860816,1721504] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860816,1722338] BT.lf) [5,63,1986,30852,233736,860816,1824040] BT.lf)) [5,63,1986,30852,233736,860816,2057776] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,860816,2057904] BT.lf) [5,63,1986,30852,233736,861712,1722338] BT.lf) [5,63,1986,30852,233736,861712,1735844] (BT.nd BT.lf [5,63,1986,30852,233736,861712,2057776] BT.lf))) [5,63,1986,30852,233736,861744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,861840,1735844] BT.lf) [5,63,1986,30852,233736,862162,862194] BT.lf) [5,63,1986,30852,233736,862162,1722338] (BT.nd BT.lf [5,63,1986,30852,233736,862162,1735844] BT.lf)) [5,63,1986,30852,233736,862162,1736678] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,862162,1834412] BT.lf) [5,63,1986,30852,233736,862162,2057776] BT.lf) [5,63,1986,30852,233736,862162,2058226] (BT.nd BT.lf [5,63,1986,30852,233736,862162,2064052] BT.lf))))) [5,63,1986,30852,233736,862162,2064374] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,862162,2097120] BT.lf) [5,63,1986,30852,233736,862194] BT.lf) [5,63,1986,30852,233736,862207,2057776] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,862207,2058226] BT.lf) [5,63,1986,30852,233736,884694,1736678] BT.lf)) [5,63,1986,30852,233736,884694,2057776] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,884694,2058226] BT.lf) [5,63,1986,30852,233736,884694,2064374] BT.lf) [5,63,1986,30852,233736,900063,2057776] (BT.nd BT.lf [5,63,1986,30852,233736,1572863,2057776] BT.lf))) [5,63,1986,30852,233736,1836659,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,1861168] BT.lf) [5,63,1986,30852,233736,1861168,1863415] BT.lf) [5,63,1986,30852,233736,1861168,2057776] (BT.nd BT.lf [5,63,1986,30852,233736,1863360,2057776] BT.lf)) [5,63,1986,30852,233736,1863415,1926704] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,1863415,2057776] BT.lf) [5,63,1986,30852,233736,1863415,2058226] BT.lf) [5,63,1986,30852,233736,1863415,2094904] (BT.nd BT.lf [5,63,1986,30852,233736,1863423,2057776] BT.lf)))) [5,63,1986,30852,233736,1863671,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,1900543,2057776] BT.lf) [5,63,1986,30852,233736,1926704] BT.lf) [5,63,1986,30852,233736,1928951,2057776] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,1966079,2057776] BT.lf) [5,63,1986,30852,233736,2057728,2057776] BT.lf)) [5,63,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,2057776,2057776] BT.lf) [5,63,1986,30852,233736,2057776,2057778] BT.lf) [5,63,1986,30852,233736,2057776,2057791] (BT.nd BT.lf [5,63,1986,30852,233736,2057776,2057904] BT.lf))) [5,63,1986,30852,233736,2057776,2058226] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,2057776,2058239] BT.lf) [5,63,1986,30852,233736,2057776,2060023] BT.lf) [5,63,1986,30852,233736,2057776,2064374] (BT.nd BT.lf [5,63,1986,30852,233736,2057776,2093055] BT.lf)) [5,63,1986,30852,233736,2057776,2097088] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,2057776,2097090] BT.lf) [5,63,1986,30852,233736,2057776,2097103] BT.lf) [5,63,1986,30852,233736,2057776,2097104] (BT.nd BT.lf [5,63,1986,30852,233736,2057776,2097119] BT.lf))))))) [5,63,1986,30852,233736,2057776,2097136] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,2057776,2097143] BT.lf) [5,63,1986,30852,233736,2057776,2097151] BT.lf) [5,63,1986,30852,233736,2057778] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,2057791,2058226] BT.lf) [5,63,1986,30852,233736,2057904] BT.lf)) [5,63,1986,30852,233736,2058226] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,2058226,2058226] BT.lf) [5,63,1986,30852,233736,2058226,2058239] BT.lf) [5,63,1986,30852,233736,2058226,2064052] (BT.nd BT.lf [5,63,1986,30852,233736,2058226,2064374] BT.lf))) [5,63,1986,30852,233736,2058226,2097088] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,2064374] BT.lf) [5,63,1986,30852,233736,2097088,2097136] BT.lf) [5,63,1986,30852,233736,2097103] (BT.nd BT.lf [5,63,1986,30852,233736,2097104,2097120] BT.lf)) [5,63,1986,30852,233736,2097104,2097136] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233736,2097136] BT.lf) [5,63,1986,30852,233738,860688,1721376] BT.lf) [5,63,1986,30852,233738,860688,1721378] (BT.nd BT.lf [5,63,1986,30852,233738,860688,1722338] BT.lf)))) [5,63,1986,30852,233738,860688,1735844] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233738,860688,1824040] BT.lf) [5,63,1986,30852,233738,860688,1824042] BT.lf) [5,63,1986,30852,233738,860688,2057776] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233738,2057776] BT.lf) [5,63,1986,30852,233742,860688,1721376] BT.lf)) [5,63,1986,30852,233752,233752,1721376] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233752,233791,1721376] BT.lf) [5,63,1986,30852,233752,235466,1721376] BT.lf) [5,63,1986,30852,233752,235482,1721376] (BT.nd BT.lf [5,63,1986,30852,233752,375775] BT.lf))) [5,63,1986,30852,233752,375775,1721376] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233752,524288,1721376] BT.lf) [5,63,1986,30852,233752,860688,1721376] BT.lf) [5,63,1986,30852,233752,860688,1721392] (BT.nd BT.lf [5,63,1986,30852,233752,860688,1722338] BT.lf)) [5,63,1986,30852,233752,860688,1824040] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233752,860688,1824056] BT.lf) [5,63,1986,30852,233752,860688,2057776] BT.lf) [5,63,1986,30852,233752,860735,1721376] (BT.nd BT.lf [5,63,1986,30852,233752,862162,1721376] BT.lf))))) [5,63,1986,30852,233752,1028888,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233752,1236463,1721376] BT.lf) [5,63,1986,30852,233752,1721376] BT.lf) [5,63,1986,30852,233752,1721376,1721376] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233752,1721376,1721392] BT.lf) [5,63,1986,30852,233752,1721376,1721407] BT.lf)) [5,63,1986,30852,233752,1721376,1722338] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233752,1721376,1824040] BT.lf) [5,63,1986,30852,233752,1721376,1824056] BT.lf) [5,63,1986,30852,233752,1721376,1863399] (BT.nd BT.lf [5,63,1986,30852,233752,1721376,1863415] BT.lf))) [5,63,1986,30852,233752,1721376,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233752,1721376,2066299] BT.lf) [5,63,1986,30852,233752,1721376,2097088] BT.lf) [5,63,1986,30852,233752,1721376,2097135] (BT.nd BT.lf [5,63,1986,30852,233752,1721392] BT.lf)) [5,63,1986,30852,233752,1722338] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233752,1824040] BT.lf) [5,63,1986,30852,233752,1824056] BT.lf) [5,63,1986,30852,233752,2057776] (BT.nd BT.lf [5,63,1986,30852,233754,860688,1721376] BT.lf)))) [5,63,1986,30852,233754,862162,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233754,1721376] BT.lf) [5,63,1986,30852,233784] BT.lf) [5,63,1986,30852,233784,860688] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233784,860688,1721376] BT.lf) [5,63,1986,30852,233784,860688,2057776] BT.lf)) [5,63,1986,30852,233784,2057776] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233791,235466,2057776] BT.lf) [5,63,1986,30852,233791,860688,1721384] BT.lf) [5,63,1986,30852,233791,860688,1824040] (BT.nd BT.lf [5,63,1986,30852,233791,860688,1824746] BT.lf))) [5,63,1986,30852,233791,860688,2094904] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233791,862162,1824040] BT.lf) [5,63,1986,30852,233791,1028888,1824040] BT.lf) [5,63,1986,30852,233791,1028888,2057776] (BT.nd BT.lf [5,63,1986,30852,233791,1028888,2094904] BT.lf)) [5,63,1986,30852,233791,2057776,2094904] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233791,2094904] BT.lf) [5,63,1986,30852,233864,860688,1721376] BT.lf) [5,63,1986,30852,233864,860688,1721504] (BT.nd BT.lf [5,63,1986,30852,233864,860688,1722338] BT.lf)))))) [5,63,1986,30852,233864,860688,1824040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,233864,860688,1824168] BT.lf) [5,63,1986,30852,233864,860688,2057776] BT.lf) [5,63,1986,30852,233864,2057776] (BT.nd (BT.nd BT.lf [5,63,1986,30852,233866,860688,1721376] BT.lf) [5,63,1986,30852,234248,860688,1824040] BT.lf)) [5,63,1986,30852,235466,260492,2057776] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,235466,1028888,1824040] BT.lf) [5,63,1986,30852,273111,1028888] BT.lf) [5,63,1986,30852,273111,1028888,1824040] (BT.nd BT.lf [5,63,1986,30852,336400,375775,1824040] BT.lf))) [5,63,1986,30852,375744,860688,1824040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,375775,860688,1824040] BT.lf) [5,63,1986,30852,375775,862162,1824040] BT.lf) [5,63,1986,30852,375775,1028888,1824040] (BT.nd BT.lf [5,63,1986,30852,375775,1824040,2057776] BT.lf)) [5,63,1986,30852,375775,1824040,2094904] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,375807,860688,1824040] BT.lf) [5,63,1986,30852,506847,860688,1824040] BT.lf) [5,63,1986,30852,524288,758024,2057776] (BT.nd BT.lf [5,63,1986,30852,524288,1028888,1824040] BT.lf)))) [5,63,1986,30852,524304,758040,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,589824,1028888,1824040] BT.lf) [5,63,1986,30852,758024,860688,1721376] BT.lf) [5,63,1986,30852,758024,860688,1722338] (BT.nd (BT.nd BT.lf [5,63,1986,30852,758024,860688,1824040] BT.lf) [5,63,1986,30852,758024,860688,2057776] BT.lf)) [5,63,1986,30852,758024,1028888,1824040] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,758024,2057776] BT.lf) [5,63,1986,30852,758040,860688,1721376] BT.lf) [5,63,1986,30852,758040,1721376] (BT.nd BT.lf [5,63,1986,30852,758040,1721376,1721407] BT.lf))) [5,63,1986,30852,860688,900063,1824040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,860688,1028888,1824040] BT.lf) [5,63,1986,30852,860688,1028920] BT.lf) [5,63,1986,30852,860688,1028927,1824040] (BT.nd BT.lf [5,63,1986,30852,860688,1863383] BT.lf)) [5,63,1986,30852,860720,1028920] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,860720,1863415] BT.lf) [5,63,1986,30852,860735,1028888,1824040] BT.lf) [5,63,1986,30852,862162,1028888,1824040] (BT.nd BT.lf [5,63,1986,30852,1028888,1028888,1824040] BT.lf))))) [5,63,1986,30852,1028888,1028927,1824040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,1028888,1030106,1824040] BT.lf) [5,63,1986,30852,1028888,1824040] BT.lf) [5,63,1986,30852,1028888,1824040,1863415] (BT.nd (BT.nd BT.lf [5,63,1986,30852,1028888,1824040,2057776] BT.lf) [5,63,1986,30852,1028888,1824040,2066299] BT.lf)) [5,63,1986,30852,1028888,1824040,2094904] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,1028888,1824040,2097088] BT.lf) [5,63,1986,30852,1861168,1863415] BT.lf) [5,63,1986,30852,1863415,1926704] (BT.nd BT.lf [5,63,1986,30852,1863415,2057776] BT.lf))) [5,63,1986,30852,1863415,2058226] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30852,1863415,2094904] BT.lf) [5,63,1986,30852,1928951,2057776] BT.lf) [5,63,1986,30852,2057776,2060023] (BT.nd BT.lf [5,63,1986,30852,2057776,2094904] BT.lf)) [5,63,1986,30852,2057791,2094904] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30854,233738,860688,1721376] BT.lf) [5,63,1986,30860,233791,860688,1721376] BT.lf) [5,63,1986,30868,233752,860688,1721376] (BT.nd BT.lf [5,63,1986,30868,233752,1721376] BT.lf)))) [5,63,1986,30868,1721376,1824040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,30868,1721376,1863415] BT.lf) [5,63,1986,31108,235466,860688,1721376] BT.lf) [5,63,1986,375775,860688,1735844,1824040] (BT.nd (BT.nd BT.lf [5,63,1986,883348,1735844,1863415] BT.lf) [5,63,1986,883348,1824040,2057776] BT.lf)) [5,63,1986,883348,2057776,2094904] (BT.nd (BT.nd (BT.nd BT.lf [5,63,1986,1863415,2057776,2064052] BT.lf) [5,63,1986,1863415,2057776,2066299] BT.lf) [5,63,1986,2057776,2064052,2094904] (BT.nd BT.lf [5,63,6082,260492,860688,1721376] BT.lf))) [5,63,32710,235466,260492,860688,1721376] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,128,191,1986,30852,233736,2057776] BT.lf) [5,128,191,32710,233736,860688,1721376] BT.lf) [5,191,1986,30852,233736,860688,1721376] (BT.nd BT.lf [5,191,1986,30852,233736,860688,1721504] BT.lf)) [5,191,1986,30852,233736,860688,1722338] (BT.nd (BT.nd (BT.nd BT.lf [5,191,1986,30852,233736,860688,1824040] BT.lf) [5,191,1986,30852,233736,860688,2057776] BT.lf) [5,191,1986,30852,233736,2057776] (BT.nd BT.lf [5,191,1986,30852,233864,860688,1721376] BT.lf)))))))) [5,191,1986,32710,233736,860688,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,191,32710,233736,860688,1721376] BT.lf) [5,447,1986,30852,233736,860688,1721376] BT.lf) [5,1986,2047,30852,30911,233736,2057776] (BT.nd (BT.nd BT.lf [5,1986,2047,30852,233791,860688,1824040] BT.lf) [5,1986,30852,39375,233736,2097088] BT.lf)) [5,1986,30852,233736,860720,2097088] (BT.nd (BT.nd (BT.nd BT.lf [5,1986,30852,233736,2057776,2097088] BT.lf) [5,1986,30852,233736,2058226,2097088] BT.lf) [5,1986,30852,233736,2097088,2097136] (BT.nd BT.lf [5,1986,30852,233752,1721376,2097088] BT.lf))) [5,1986,30852,1028888,1824040,2097088] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1986,30852,1863415,2057776,2097088] BT.lf) [5,1986,30852,2057776,2094904,2097088] BT.lf) [5,1986,30911,233791,260492,860688,1721376] (BT.nd BT.lf [6,0,16,63,1986,30852,233736,1721376] BT.lf)) [6,0,63,1986,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,2,16,63,1986,30852,233736,1721376] BT.lf) [6,2,63,1986,30852,233736,860688,1721376] BT.lf) [6,2,63,1986,30852,233736,860688,1721378] (BT.nd BT.lf [6,2,63,1986,30852,233736,860688,1722338] BT.lf)))) [6,2,63,1986,30852,233736,860688,1735844] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2,63,1986,30852,233736,860688,2057776] BT.lf) [6,2,63,1986,30852,233736,2057776] BT.lf) [6,2,63,1986,30852,233738,860688,1721376] (BT.nd (BT.nd BT.lf [6,2,63,2047,30852,233736,860688,1721376] BT.lf) [6,6,63,1986,30852,233736,860688,1721376] BT.lf)) [6,16,16,63,1986,30852,233736,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,16,32,63,1986,30852,233736] BT.lf) [6,16,32,63,1986,30852,233736,860688] BT.lf) [6,16,63,63,1986,30852,233736,1721376] (BT.nd BT.lf [6,16,63,128,1986,30852,233736,1721376] BT.lf))) [6,16,63,512,1986,30852,233736,1721376] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,16,63,1024,1986,30852,233736,1721376] BT.lf) [6,16,63,1986,1986,30852,233736,1721376] BT.lf) [6,16,63,1986,2002,30852,233736,1721376] (BT.nd BT.lf [6,16,63,1986,2047,30852,233736,1721376] BT.lf)) [6,16,63,1986,30852,32710,233736,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,16,63,1986,30852,233736,375775] BT.lf) [6,16,63,1986,30852,233736,375775,1721376] BT.lf) [6,16,63,1986,30852,233736,524288,1721376] (BT.nd BT.lf [6,16,63,1986,30852,233736,860688,1721376] BT.lf))))) [6,16,63,1986,30852,233736,860688,1721392] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,16,63,1986,30852,233736,860688,1722338] BT.lf) [6,16,63,1986,30852,233736,860688,2057776] BT.lf) [6,16,63,1986,30852,233736,860735,1721376] (BT.nd (BT.nd BT.lf [6,16,63,1986,30852,233736,862162,1721376] BT.lf) [6,16,63,1986,30852,233736,1236463,1721376] BT.lf)) [6,16,63,1986,30852,233736,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,16,63,1986,30852,233736,1721376,1721376] BT.lf) [6,16,63,1986,30852,233736,1721376,1721392] BT.lf) [6,16,63,1986,30852,233736,1721376,1721407] (BT.nd BT.lf [6,16,63,1986,30852,233736,1721376,1722338] BT.lf))) [6,16,63,1986,30852,233736,1721376,1863415] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,16,63,1986,30852,233736,1721376,2057776] BT.lf) [6,16,63,1986,30852,233736,1721376,2097088] BT.lf) [6,16,63,1986,30852,233736,1721376,2097135] (BT.nd BT.lf [6,16,63,1986,30852,233736,1721392] BT.lf)) [6,16,63,1986,30852,233736,1722338] (BT.nd (BT.nd (BT.nd BT.lf [6,16,63,1986,30852,233736,2057776] BT.lf) [6,16,63,1986,30852,233752,860688,1721376] BT.lf) [6,16,63,1986,30852,233752,1721376] (BT.nd BT.lf [6,16,63,1986,30852,1721376,1824040] BT.lf)))) [6,16,63,1986,30852,1721376,1863415] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,16,1986,30852,233736,1721376,2097088] BT.lf) [6,18,63,1986,30852,233736,860688,1721376] BT.lf) [6,18,63,1986,30852,233736,862162,1721376] (BT.nd (BT.nd BT.lf [6,18,63,1986,30852,233736,1721376] BT.lf) [6,31,63,1986,30852,233736,860688] BT.lf)) [6,31,63,1986,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,48,63,1986,30852,233736] BT.lf) [6,48,63,1986,30852,233736,860688] BT.lf) [6,48,63,1986,30852,233736,860688,1721376] (BT.nd BT.lf [6,48,63,1986,30852,233736,860688,2057776] BT.lf))) [6,48,63,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,55,63,1986,30852,233736,860688,1721376] BT.lf) [6,63,63,1986,30852,233736,860688,1721376] BT.lf) [6,63,63,1986,30852,233736,860688,1722338] (BT.nd BT.lf [6,63,63,1986,30852,233736,860688,2057776] BT.lf)) [6,63,63,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [6,63,128,1986,30852,233736,860688,1721376] BT.lf) [6,63,128,1986,30852,233736,860688,1721504] BT.lf) [6,63,128,1986,30852,233736,860688,1722338] (BT.nd BT.lf [6,63,128,1986,30852,233736,860688,1824040] BT.lf)))))) [6,63,128,1986,30852,233736,860688,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,128,1986,30852,233736,2057776] BT.lf) [6,63,128,1986,30852,233864,860688,1721376] BT.lf) [6,63,128,1986,32710,233736,860688,1721376] (BT.nd (BT.nd BT.lf [6,63,128,32710,233736,860688,1721376] BT.lf) [6,63,130,1986,30852,233736,860688,1721376] BT.lf)) [6,63,191,1986,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,63,384,1986,30852,233736,860688,1721376] BT.lf) [6,63,512,1986,30852,233736,860688,1721376] BT.lf) [6,63,512,1986,30852,233736,860688,1721888] (BT.nd BT.lf [6,63,512,1986,30852,233736,860688,1722338] BT.lf))) [6,63,512,1986,30852,233736,860688,1735844] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,512,1986,30852,233736,860688,2057776] BT.lf) [6,63,512,1986,30852,233736,862162,1721376] BT.lf) [6,63,512,1986,30852,233736,883348,1721376] (BT.nd BT.lf [6,63,512,1986,30852,233736,1721376,2057776] BT.lf)) [6,63,512,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [6,63,514,1986,30852,233736,860688,1721376] BT.lf) [6,63,528,1986,2047,30852,233736,1721376] BT.lf) [6,63,528,1986,30852,233736,860688,1721376] (BT.nd BT.lf [6,63,528,1986,30852,233736,1721376] BT.lf)))) [6,63,575,1986,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,640,1986,30852,233736,860688,1721376] BT.lf) [6,63,640,1986,30852,233736,883348,1721376] BT.lf) [6,63,962,1986,30852,233736,860688,1721376] (BT.nd (BT.nd BT.lf [6,63,962,30852,233736,375775,860688] BT.lf) [6,63,962,30852,233736,375775,860688,1721376] BT.lf)) [6,63,962,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1536,1986,30852,233736,860688,1721376] BT.lf) [6,63,1536,1986,30852,233736,860688,2057776] BT.lf) [6,63,1536,1986,30852,233736,2057776] (BT.nd BT.lf [6,63,1730,1986,30852,233736,860688,1721376] BT.lf))) [6,63,1984,1986,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,1986,30852,233736,860688,1721376] BT.lf) [6,63,1986,1986,30852,233736,860688,1722338] BT.lf) [6,63,1986,1986,30852,233736,860688,1735844] (BT.nd BT.lf [6,63,1986,1986,30852,233736,860688,2057776] BT.lf)) [6,63,1986,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,1990,30852,233736,860688,1721376] BT.lf) [6,63,1986,2002,30852,233736,860688,1721376] BT.lf) [6,63,1986,2002,30852,233736,1721376] (BT.nd BT.lf [6,63,1986,2047,30852,233736,860688,1721376] BT.lf))))) [6,63,1986,2047,30852,233736,860688,1722338] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,2047,30852,233736,860688,1735844] BT.lf) [6,63,1986,2047,30852,233736,860688,2057776] BT.lf) [6,63,1986,2047,30852,233736,2057776] (BT.nd (BT.nd BT.lf [6,63,1986,6082,30852,233736,860688,1721376] BT.lf) [6,63,1986,8704,30852,233736,860688,1721376] BT.lf)) [6,63,1986,10178,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,32710,233736,860688,1721376] BT.lf) [6,63,1986,30852,32710,233736,860688,1722338] BT.lf) [6,63,1986,30852,32710,233736,860688,1736678] (BT.nd BT.lf [6,63,1986,30852,32710,233736,860688,1824040] BT.lf))) [6,63,1986,30852,32710,233736,860688,2057776] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,32710,233736,2057776] BT.lf) [6,63,1986,30852,32767,233736,860688,1721376] BT.lf) [6,63,1986,30852,39375,233736] (BT.nd BT.lf [6,63,1986,30852,39375,233736,860688] BT.lf)) [6,63,1986,30852,39375,233736,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,39375,233736,860688,2057776] BT.lf) [6,63,1986,30852,39375,233736,2057776] BT.lf) [6,63,1986,30852,233736,262094,860688,1721376] (BT.nd BT.lf [6,63,1986,30852,233736,273111,860688] BT.lf)))) [6,63,1986,30852,233736,273111,860688,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,273111,860688,1824040] BT.lf) [6,63,1986,30852,233736,336400,375775] BT.lf) [6,63,1986,30852,233736,336400,375775,1721376] (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,336400,860688,1721376] BT.lf) [6,63,1986,30852,233736,336400,1721376] BT.lf)) [6,63,1986,30852,233736,375744,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,375775,860688] BT.lf) [6,63,1986,30852,233736,375775,860688,1721376] BT.lf) [6,63,1986,30852,233736,375775,860688,1722338] (BT.nd BT.lf [6,63,1986,30852,233736,375775,860688,2057776] BT.lf))) [6,63,1986,30852,233736,375775,862162] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,375775,862162,1721376] BT.lf) [6,63,1986,30852,233736,375775,1236463] BT.lf) [6,63,1986,30852,233736,375775,1721376,2057776] (BT.nd BT.lf [6,63,1986,30852,233736,375775,2057776] BT.lf)) [6,63,1986,30852,233736,375807,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,376799,860688] BT.lf) [6,63,1986,30852,233736,376799,860688,1721376] BT.lf) [6,63,1986,30852,233736,524288,860688,1721376] (BT.nd BT.lf [6,63,1986,30852,233736,524288,860688,1722338] BT.lf))))))) [6,63,1986,30852,233736,524288,860688,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,524288,2057776] BT.lf) [6,63,1986,30852,233736,524304,860688,1721376] BT.lf) [6,63,1986,30852,233736,524304,1721376] (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,524304,1721376,1721407] BT.lf) [6,63,1986,30852,233736,524351,860688,1721376] BT.lf)) [6,63,1986,30852,233736,524800,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,524800,860688,1722338] BT.lf) [6,63,1986,30852,233736,526274,860688,1721376] BT.lf) [6,63,1986,30852,233736,795152,860688,1721376] (BT.nd BT.lf [6,63,1986,30852,233736,795152,1721376] BT.lf))) [6,63,1986,30852,233736,795152,1721376,1863415] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860672,860688,1721376] BT.lf) [6,63,1986,30852,233736,860688,860688,1721376] BT.lf) [6,63,1986,30852,233736,860688,860688,1722338] (BT.nd BT.lf [6,63,1986,30852,233736,860688,860688,2057776] BT.lf)) [6,63,1986,30852,233736,860688,860690,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,860720] BT.lf) [6,63,1986,30852,233736,860688,860720,1721376] BT.lf) [6,63,1986,30852,233736,860688,860735,1721376] (BT.nd BT.lf [6,63,1986,30852,233736,860688,860735,1722338] BT.lf)))) [6,63,1986,30852,233736,860688,860735,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,860816,1721376] BT.lf) [6,63,1986,30852,233736,860688,861712,1721376] BT.lf) [6,63,1986,30852,233736,860688,862162,1721376] (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,862162,1722338] BT.lf) [6,63,1986,30852,233736,860688,862162,1735844] BT.lf)) [6,63,1986,30852,233736,860688,862162,2057776] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,862162,2058226] BT.lf) [6,63,1986,30852,233736,860688,862207,1721376] BT.lf) [6,63,1986,30852,233736,860688,884694,1721376] (BT.nd BT.lf [6,63,1986,30852,233736,860688,900063] BT.lf))) [6,63,1986,30852,233736,860688,900063,1721376] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,1572863,1721376] BT.lf) [6,63,1986,30852,233736,860688,1721376] BT.lf) [6,63,1986,30852,233736,860688,1721376,1836659] (BT.nd BT.lf [6,63,1986,30852,233736,860688,1721376,1863360] BT.lf)) [6,63,1986,30852,233736,860688,1721376,1863415] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,1721376,1863423] BT.lf) [6,63,1986,30852,233736,860688,1721376,1863671] BT.lf) [6,63,1986,30852,233736,860688,1721376,1928951] (BT.nd BT.lf [6,63,1986,30852,233736,860688,1721376,1966079] BT.lf))))) [6,63,1986,30852,233736,860688,1721376,2057776] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,1721376,2057791] BT.lf) [6,63,1986,30852,233736,860688,1721376,2058226] BT.lf) [6,63,1986,30852,233736,860688,1721376,2093055] (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,1721376,2097088] BT.lf) [6,63,1986,30852,233736,860688,1721376,2097090] BT.lf)) [6,63,1986,30852,233736,860688,1721376,2097104] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,1721376,2097119] BT.lf) [6,63,1986,30852,233736,860688,1721376,2097143] BT.lf) [6,63,1986,30852,233736,860688,1721376,2097151] (BT.nd BT.lf [6,63,1986,30852,233736,860688,1721378] BT.lf))) [6,63,1986,30852,233736,860688,1721392] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,1721407,1722338] BT.lf) [6,63,1986,30852,233736,860688,1721407,2057776] BT.lf) [6,63,1986,30852,233736,860688,1721504] (BT.nd BT.lf [6,63,1986,30852,233736,860688,1721888] BT.lf)) [6,63,1986,30852,233736,860688,1722338] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,1722338,1722338] BT.lf) [6,63,1986,30852,233736,860688,1722338,1722367] BT.lf) [6,63,1986,30852,233736,860688,1722338,1735844] (BT.nd BT.lf [6,63,1986,30852,233736,860688,1722338,1736678] BT.lf)))) [6,63,1986,30852,233736,860688,1722338,1863415] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,1722338,2057776] BT.lf) [6,63,1986,30852,233736,860688,1722338,2058226] BT.lf) [6,63,1986,30852,233736,860688,1722338,2095165] (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,1722338,2097088] BT.lf) [6,63,1986,30852,233736,860688,1736678] BT.lf)) [6,63,1986,30852,233736,860688,1863415,2057776] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,2057776] BT.lf) [6,63,1986,30852,233736,860688,2057776,2057776] BT.lf) [6,63,1986,30852,233736,860688,2057776,2057791] (BT.nd BT.lf [6,63,1986,30852,233736,860688,2057776,2058226] BT.lf))) [6,63,1986,30852,233736,860688,2057776,2097088] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860688,2058226] BT.lf) [6,63,1986,30852,233736,860688,2097088,2097120] BT.lf) [6,63,1986,30852,233736,860688,2097119] (BT.nd BT.lf [6,63,1986,30852,233736,860688,2097120] BT.lf)) [6,63,1986,30852,233736,860720] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,860735,2057776] BT.lf) [6,63,1986,30852,233736,862162,1722338] BT.lf) [6,63,1986,30852,233736,862162,1735844] (BT.nd BT.lf [6,63,1986,30852,233736,862162,2057776] BT.lf)))))) [6,63,1986,30852,233736,862162,2058226] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,1863415,2057776] BT.lf) [6,63,1986,30852,233736,2057776] BT.lf) [6,63,1986,30852,233736,2057776,2057776] (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,2057776,2057791] BT.lf) [6,63,1986,30852,233736,2057776,2058226] BT.lf)) [6,63,1986,30852,233736,2057776,2097088] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233736,2058226] BT.lf) [6,63,1986,30852,233738,860688,1721376] BT.lf) [6,63,1986,30852,233752,860688,1721376] (BT.nd BT.lf [6,63,1986,30852,233752,1721376] BT.lf))) [6,63,1986,30852,233791,235466,860688,1721376] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,233791,860688,1028888,1721376] BT.lf) [6,63,1986,30852,233791,860688,1824040] BT.lf) [6,63,1986,30852,233864,860688,1721376] (BT.nd BT.lf [6,63,1986,30852,235466,260492,860688,1721376] BT.lf)) [6,63,1986,30852,273111,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,375775,860688,1028888] BT.lf) [6,63,1986,30852,375775,860688,1721376,1824040] BT.lf) [6,63,1986,30852,375775,860688,1824040] (BT.nd BT.lf [6,63,1986,30852,375775,860688,1863415] BT.lf)))) [6,63,1986,30852,524288,758024,860688,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,758024,860688,1721376] BT.lf) [6,63,1986,30852,795152,1721376,1863415] BT.lf) [6,63,1986,30852,860688,1028888,1721376] (BT.nd (BT.nd BT.lf [6,63,1986,30852,860688,1028888,1721376,1824040] BT.lf) [6,63,1986,30852,860688,1028888,1722338] BT.lf)) [6,63,1986,30852,860688,1028888,1824040] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,860688,1028888,2057776] BT.lf) [6,63,1986,30852,860688,1028888,2094904] BT.lf) [6,63,1986,30852,860688,1721376,1863415] (BT.nd BT.lf [6,63,1986,30852,860688,1721376,1928951] BT.lf))) [6,63,1986,30852,860688,1721376,2094904] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,860688,1721407,1824040] BT.lf) [6,63,1986,30852,860688,1722338,1863415] BT.lf) [6,63,1986,30852,860688,1824040,1863415] (BT.nd BT.lf [6,63,1986,30852,860688,1824040,2057776] BT.lf)) [6,63,1986,30852,860688,1863415,2057776] (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,30852,860688,2057776,2094904] BT.lf) [6,63,1986,30852,1028888,1824040] BT.lf) [6,63,1986,30852,1028888,2057776] (BT.nd BT.lf [6,63,1986,30852,1863415,2057776] BT.lf))))) [6,63,1986,30852,2057776,2094904] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,63,1986,860688,883348,1028888,1721376] BT.lf) [6,63,1986,860688,883348,1721376,1824040] BT.lf) [6,63,1986,860688,883348,1721376,1863415] (BT.nd (BT.nd BT.lf [6,63,1986,860688,1721376,1863415,2066299] BT.lf) [6,128,191,1986,30852,233736,860688,1721376] BT.lf)) [6,191,1986,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [6,1986,2047,30852,30911,233736,860688,1721376] BT.lf) [6,1986,30852,233736,375775,860688,2097088] BT.lf) [6,1986,30852,233736,860688,1721376,2097088] (BT.nd BT.lf [6,1986,30852,233736,860688,1722338,2097088] BT.lf))) [6,1986,30852,233736,860688,2057776,2097088] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1986,30852,233736,860688,2097088,2097120] BT.lf) [6,1986,30852,233736,2057776,2097088] BT.lf) [6,1986,30852,860688,1028888,1721376,2097088] (BT.nd BT.lf [6,1986,30852,860688,1721376,1863415,2097088] BT.lf)) [7,2,63,1986,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [7,16,63,1986,30852,233736,860688,1721376] BT.lf) [7,16,63,1986,30852,233736,1721376] BT.lf) [7,63,63,1986,30852,233736,860688,1721376] (BT.nd BT.lf [7,63,128,1986,30852,233736,860688,1721376] BT.lf)))) [7,63,512,1986,30852,233736,860688,1721376] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,63,1986,1986,30852,233736,860688,1721376] BT.lf) [7,63,1986,2047,30852,233736,860688,1721376] BT.lf) [7,63,1986,30852,32710,233736,860688,1721376] (BT.nd (BT.nd BT.lf [7,63,1986,30852,233736,375775,860688] BT.lf) [7,63,1986,30852,233736,375775,860688,1721376] BT.lf)) [7,63,1986,30852,233736,524288,860688,1721376] (BT.nd (BT.nd (BT.nd BT.lf [7,63,1986,30852,233736,860688,860688,1721376] BT.lf) [7,63,1986,30852,233736,860688,860735,1721376] BT.lf) [7,63,1986,30852,233736,860688,862162,1721376] (BT.nd BT.lf [7,63,1986,30852,233736,860688,1721376] BT.lf))) [7,63,1986,30852,233736,860688,1721376,1863415] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,63,1986,30852,233736,860688,1721376,2057776] BT.lf) [7,63,1986,30852,233736,860688,1721376,2097088] BT.lf) [7,63,1986,30852,233736,860688,1722338] (BT.nd BT.lf [7,63,1986,30852,233736,860688,2057776] BT.lf)) [7,63,1986,30852,233736,2057776] (BT.nd (BT.nd (BT.nd BT.lf [7,63,1986,30852,860688,1028888,1721376] BT.lf) [7,63,1986,30852,860688,1721376,1863415] BT.lf) [7,1986,30852,233736,860688,1721376,2097088] (BT.nd BT.lf [8,63,1986,30852,233736,860688,1721376] BT.lf))))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([2,63,6082,260540],[]),([2,63,6130,260492],[]),([2,191,32710,233784],[]),([2,191,32758,233736],[]),([2,1986,30908,233791],[]),([2,1986,30910,233791],[]),([2,1990,30911,233784],[]),([2,2002,30892,233791],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([2,2038,30911,233788],[]),([3,2,2047,30852,233784],[(72,3),(96,5)]),([3,16,1986,30892,233791],[]),([3,18,2047,30852,233768],[(72,10),(96,5)]),([3,48,63,6082,260492],[]),([3,48,191,32710,233736],[]),([3,48,1986,30860,233791],[(56,5)]),([3,50,2047,30852,233736],[(72,9),(96,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([3,50,2047,30852,233786],[(56,5),(72,3),(96,5)]),([3,54,1986,30911,233736],[(56,7),(96,1)]),([3,62,1986,30852,233736],[]),([3,63,128,32710,233784],[(104,7)]),([3,63,128,32758,233736],[(104,7)]),([3,63,176,32710,233736],[(104,7)]),([3,63,450,6276,2094904],[]),([3,63,450,30852,233784],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([3,63,498,30852,233736],[]),([3,63,962,30852,233784],[]),([3,63,1010,30852,233736],[]),([3,63,1986,30852,233784],[]),([3,63,1986,30852,233786],[(56,5)]),([3,63,1986,30852,233790],[(56,5),(72,1)]),([3,63,1986,30852,233912],[(80,7)]),([3,63,1986,30852,758072],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([3,63,1986,30852,2068792],[]),([3,63,1986,30854,233784],[(56,3)]),([3,63,1986,30860,233784],[]),([3,63,1986,30868,233768],[]),([3,63,1986,30868,233770],[(56,5)]),([3,63,1986,30868,233772],[]),([3,63,1986,30868,233784],[]),([3,63,1986,30868,233788],[(72,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([3,63,1986,30868,758056],[]),([3,63,1986,30900,233784],[]),([3,63,1986,30900,233788],[(72,1)]),([3,63,1986,30900,233864],[(80,7)]),([3,63,1986,30900,758024],[]),([3,63,1986,30902,233786],[(56,3)]),([3,63,1986,30908,233791],[]),([3,63,2002,30868,233768],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([3,63,2034,30900,233784],[]),([3,63,6082,260492,860720],[]),([3,63,6082,260492,2057776],[]),([3,63,6082,260492,2058226],[]),([3,63,6082,260492,2061872],[]),([3,63,6082,260492,2062322],[]),([3,63,6082,260492,2064052],[]),([3,63,6082,260492,2097084],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([3,63,6082,260508,1721376],[]),([3,63,6082,1047452,1834412],[]),([3,63,6086,260492,2057776],[]),([3,63,6098,260492,1721376],[]),([3,63,32710,1029016,1824168],[]),([3,191,1986,30852,233784],[]),([3,191,1986,30900,233736],[]),([3,191,32710,233736,860720],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([3,191,32710,233736,2057776],[]),([3,191,32710,233736,2057904],[]),([3,191,32710,233736,2058226],[]),([3,191,32710,233736,2064374],[]),([3,191,32710,233736,2094904],[]),([3,191,32710,233752,1721376],[]),([3,191,32710,233864,2057776],[]),([3,191,32710,1028888,1824040],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([3,191,32726,233736,1721376],[]),([3,191,233736,884694,1736678],[]),([3,447,30852,233736,2058226],[]),([3,447,30852,235466,2057776],[]),([3,1716,1986,30911,233736],[(56,7)]),([3,1986,2038,30911,233736],[(56,7)]),([3,1986,2047,30852,233786],[(56,5)]),([3,1986,30852,233784,524351],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([3,1986,30908,233791],[]),([3,1986,30908,233791,860688],[]),([3,1986,30908,233791,1028888],[]),([3,1986,30908,233791,2057776],[]),([3,1986,30908,233791,2094904],[]),([3,1986,30911,233791,2097084],[(116,1)]),([4,0,63,1986,30852,233784],[]),([4,2,48,2047,30852,233736],[(96,9),(104,1),(128,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([4,2,63,1986,30852,233784],[]),([4,2,63,2034,30852,233736],[(56,5),(72,5),(96,9),(128,5)]),([4,15,48,1986,30852,233736],[]),([4,16,34,2047,30852,233736],[(96,2),(104,9),(128,0),(136,5)]),([4,16,63,1986,30852,233768],[(72,3)]),([4,16,63,1986,30852,233770],[(72,3),(80,5)]),([4,16,63,1986,30852,233784],[(72,3)]),([4,16,63,1986,30852,758056],[(72,3)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([4,16,63,1986,30868,233768],[]),([4,16,63,1986,30884,233768],[(72,6),(96,2),(128,0)]),([4,16,63,6082,260492,1721376],[(128,0)]),([4,16,191,32710,233736,1721376],[(128,0)]),([4,18,63,1986,30852,233768],[(72,3),(96,2)]),([4,18,63,2018,30852,233736],[(72,5),(96,8),(128,4)]),([4,31,48,1986,30852,233736],[]),([4,48,63,128,32710,233736],[(144,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([4,48,63,450,30852,233736],[(96,1)]),([4,48,63,962,30852,233736],[(96,1)]),([4,48,63,1986,30852,233736],[(72,5),(96,1)]),([4,48,63,1986,30852,233738],[(72,5),(80,5),(96,1)]),([4,48,63,1986,30852,233752],[(72,5),(96,1)]),([4,48,63,1986,30852,233784],[(72,3)]),([4,48,63,1986,30852,233864],[(72,3),(112,7)]),([4,48,63,1986,30852,758024],[(72,3)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([4,48,63,1986,30900,233784],[]),([4,48,191,1986,30852,233736],[(72,3)]),([4,48,1986,30852,233736,524351],[(56,5),(72,1)]),([4,50,63,1986,30852,233736],[(72,5),(96,1)]),([4,50,63,1986,30852,233786],[(72,3)]),([4,50,63,2002,30852,233736],[(72,5),(96,7),(128,3)]),([4,50,63,2034,30852,233736],[(56,5),(72,5),(96,7),(128,3)]),([4,50,63,2047,30852,233736],[(96,9),(128,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([4,50,1986,2047,30852,233736],[(96,1)]),([4,50,2047,30852,233736],[(72,9),(73,3),(74,1),(96,5),(97,7)]),([4,50,2047,30852,233736,860688],[(72,9),(96,5)]),([4,50,2047,30852,233736,862162],[(72,9),(96,5)]),([4,50,2047,30852,233736,2057776],[(72,9),(96,5)]),([4,50,2047,30852,233736,2058226],[(72,9),(96,5)]),([4,54,63,1986,30852,233736],[(72,5),(80,3),(96,1)]),([4,63,63,1986,30852,233784],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,128,1986,30852,233784],[]),([4,63,128,1986,30900,233736],[(80,1),(104,1)]),([4,63,128,32710,233736,860720],[(104,7)]),([4,63,128,32710,233736,2057776],[(104,7)]),([4,63,128,32710,233736,2057904],[(104,7)]),([4,63,128,32710,233736,2058226],[(104,7)]),([4,63,128,32710,233736,2064374],[(104,7)]),([4,63,128,32710,233736,2094904],[(104,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,128,32710,233752,1721376],[(104,7)]),([4,63,128,32710,233864,2057776],[(80,7),(104,7),(136,7)]),([4,63,128,32710,1028888,1824040],[]),([4,63,128,32726,233736,1721376],[(104,7)]),([4,63,128,233736,884694,1736678],[(80,7)]),([4,63,130,32710,233736,2057776],[(104,7)]),([4,63,144,32710,233736,1721376],[(104,7)]),([4,63,176,1986,30852,233736],[(80,5),(104,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,191,32710,233736,2057776],[]),([4,63,384,30852,233736,2058226],[]),([4,63,384,30852,235466,2057776],[(80,3)]),([4,63,386,30852,233736,2057776],[]),([4,63,450,6276,233736,2057776],[]),([4,63,450,30852,39375,2094904],[]),([4,63,450,30852,233736,2057776],[]),([4,63,450,30852,233736,2058226],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,450,30852,233736,2064052],[]),([4,63,512,1986,30852,233784],[]),([4,63,512,2034,30852,233736],[(80,5)]),([4,63,528,1986,30852,233768],[(80,3)]),([4,63,528,2018,30852,233736],[(80,5)]),([4,63,528,2034,30852,233736],[(80,5)]),([4,63,560,1986,30852,233736],[(80,5)]),([4,63,962,14468,233736,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,962,14468,860688,1824040],[]),([4,63,962,30852,233736,860720],[]),([4,63,962,30852,233736,1721392],[]),([4,63,962,30852,233736,2057776],[]),([4,63,962,30852,233736,2058226],[]),([4,63,962,30852,233736,2064052],[]),([4,63,962,30852,233752,1721376],[]),([4,63,962,30852,233768,860688],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,962,30852,1028888,1824040],[]),([4,63,978,30852,233736,1721376],[]),([4,63,994,30852,233736,860688],[]),([4,63,1536,1986,30852,233784],[]),([4,63,1536,2034,30852,233736],[(80,5)]),([4,63,1584,1986,30852,233736],[(80,5)]),([4,63,1584,2034,30852,233736],[(80,5)]),([4,63,1716,1986,30852,233736],[(80,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1984,30852,233736,2058226],[]),([4,63,1986,1986,30852,233784],[]),([4,63,1986,2002,30852,233768],[(80,3)]),([4,63,1986,2034,30852,233736],[(80,5)]),([4,63,1986,2034,30852,233784],[(80,3)]),([4,63,1986,2038,30852,233736],[(80,5)]),([4,63,1986,2047,30852,233784],[]),([4,63,1986,6082,260492,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,26160,30852,233736],[]),([4,63,1986,26610,30852,233736],[]),([4,63,1986,30852,32710,233784],[]),([4,63,1986,30852,32758,233736],[]),([4,63,1986,30852,39360,2094904],[]),([4,63,1986,30852,39375,233784],[(116,3)]),([4,63,1986,30852,39375,2094904],[]),([4,63,1986,30852,39423,2094904],[(156,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233736,336432],[]),([4,63,1986,30852,233736,524336],[(136,5),(144,1)]),([4,63,1986,30852,233736,795184],[]),([4,63,1986,30852,233736,860720],[]),([4,63,1986,30852,233736,860722],[]),([4,63,1986,30852,233736,860726],[]),([4,63,1986,30852,233736,860848],[]),([4,63,1986,30852,233736,861744],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233736,861876],[]),([4,63,1986,30852,233736,862194],[]),([4,63,1986,30852,233736,862198],[]),([4,63,1986,30852,233736,878128],[]),([4,63,1986,30852,233736,878578],[]),([4,63,1986,30852,233736,884726],[]),([4,63,1986,30852,233736,1533488],[]),([4,63,1986,30852,233736,1836592],[(136,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233736,1861168],[]),([4,63,1986,30852,233736,1861362],[]),([4,63,1986,30852,233736,1861618],[]),([4,63,1986,30852,233736,1910320],[]),([4,63,1986,30852,233736,1926704],[]),([4,63,1986,30852,233736,1926898],[]),([4,63,1986,30852,233736,1927154],[]),([4,63,1986,30852,233736,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233736,2057778],[]),([4,63,1986,30852,233736,2057782],[]),([4,63,1986,30852,233736,2057904],[]),([4,63,1986,30852,233736,2057906],[]),([4,63,1986,30852,233736,2057970],[]),([4,63,1986,30852,233736,2058160],[]),([4,63,1986,30852,233736,2058224],[]),([4,63,1986,30852,233736,2058226],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233736,2058230],[]),([4,63,1986,30852,233736,2060016],[]),([4,63,1986,30852,233736,2062322],[]),([4,63,1986,30852,233736,2064374],[]),([4,63,1986,30852,233736,2097136],[]),([4,63,1986,30852,233736,2097138],[]),([4,63,1986,30852,233736,2097150],[]),([4,63,1986,30852,233738,860720],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233738,2057776],[]),([4,63,1986,30852,233738,2057778],[]),([4,63,1986,30852,233738,2058226],[]),([4,63,1986,30852,233738,2064052],[]),([4,63,1986,30852,233738,2094904],[]),([4,63,1986,30852,233738,2094906],[]),([4,63,1986,30852,233742,2057776],[]),([4,63,1986,30852,233752,233768],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233752,233784],[]),([4,63,1986,30852,233752,524320],[(136,5),(144,1)]),([4,63,1986,30852,233752,860720],[]),([4,63,1986,30852,233752,1197088],[]),([4,63,1986,30852,233752,1590304],[]),([4,63,1986,30852,233752,1704992],[]),([4,63,1986,30852,233752,1721376],[]),([4,63,1986,30852,233752,1721378],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233752,1721384],[]),([4,63,1986,30852,233752,1721392],[]),([4,63,1986,30852,233752,1721400],[]),([4,63,1986,30852,233752,1721504],[]),([4,63,1986,30852,233752,1721632],[]),([4,63,1986,30852,233752,1721888],[]),([4,63,1986,30852,233752,1722338],[]),([4,63,1986,30852,233752,1722354],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233752,1736678],[]),([4,63,1986,30852,233752,1786912],[]),([4,63,1986,30852,233752,1786928],[]),([4,63,1986,30852,233752,1824040],[]),([4,63,1986,30852,233752,1824056],[]),([4,63,1986,30852,233752,1824746],[]),([4,63,1986,30852,233752,1824762],[]),([4,63,1986,30852,233752,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233752,2058226],[]),([4,63,1986,30852,233752,2094904],[]),([4,63,1986,30852,233752,2097120],[]),([4,63,1986,30852,233754,1721376],[]),([4,63,1986,30852,233754,1721394],[]),([4,63,1986,30852,233754,1722338],[]),([4,63,1986,30852,233754,1735844],[]),([4,63,1986,30852,233754,1824040],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233754,1824058],[]),([4,63,1986,30852,233754,2057776],[]),([4,63,1986,30852,233754,2058226],[]),([4,63,1986,30852,233758,1721376],[]),([4,63,1986,30852,233784],[]),([4,63,1986,30852,233784,233784],[]),([4,63,1986,30852,233784,233791],[(100,7)]),([4,63,1986,30852,233784,235466],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233784,235514],[(108,1)]),([4,63,1986,30852,233784,375775],[(148,3)]),([4,63,1986,30852,233784,524288],[(136,5),(144,1)]),([4,63,1986,30852,233784,860688],[]),([4,63,1986,30852,233784,860720],[]),([4,63,1986,30852,233784,860735],[]),([4,63,1986,30852,233784,862162],[]),([4,63,1986,30852,233784,1028888],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233784,1028920],[]),([4,63,1986,30852,233784,1863367],[]),([4,63,1986,30852,233784,1863415],[]),([4,63,1986,30852,233784,2057776],[]),([4,63,1986,30852,233784,2057791],[]),([4,63,1986,30852,233784,2058226],[]),([4,63,1986,30852,233784,2066299],[]),([4,63,1986,30852,233784,2094904],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233784,2097088],[]),([4,63,1986,30852,233784,2097103],[]),([4,63,1986,30852,233786],[(56,5),(58,5)]),([4,63,1986,30852,233786,860688],[(56,5)]),([4,63,1986,30852,233786,862162],[(56,5)]),([4,63,1986,30852,233786,2057776],[(56,5)]),([4,63,1986,30852,233786,2058226],[(56,5)]),([4,63,1986,30852,233791,860728],[(132,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233791,1028920],[(132,7)]),([4,63,1986,30852,233791,2057784],[(132,7)]),([4,63,1986,30852,233791,2094904],[(132,7)]),([4,63,1986,30852,233791,2095098],[(56,3),(132,1)]),([4,63,1986,30852,233864,860720],[(80,7)]),([4,63,1986,30852,233864,2057776],[(80,7)]),([4,63,1986,30852,233864,2057904],[(80,7)]),([4,63,1986,30852,233864,2058226],[(80,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,233864,2094904],[(80,7)]),([4,63,1986,30852,233864,2095032],[(80,7)]),([4,63,1986,30852,233866,2057776],[(80,7)]),([4,63,1986,30852,233880,1721376],[(80,7)]),([4,63,1986,30852,234264,1824040],[]),([4,63,1986,30852,235983,2094904],[]),([4,63,1986,30852,373528,1824040],[]),([4,63,1986,30852,375759,1824056],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,375775,1824056],[]),([4,63,1986,30852,504600,1824040],[]),([4,63,1986,30852,758024,860720],[]),([4,63,1986,30852,758024,2057776],[]),([4,63,1986,30852,758024,2058226],[]),([4,63,1986,30852,758024,2094904],[]),([4,63,1986,30852,758040,1721376],[]),([4,63,1986,30852,758040,1721392],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,758040,1722338],[]),([4,63,1986,30852,758040,1824040],[]),([4,63,1986,30852,758040,1824056],[]),([4,63,1986,30852,758040,2057776],[]),([4,63,1986,30852,860688,1806632],[]),([4,63,1986,30852,865040,1824040],[]),([4,63,1986,30852,897816,1824040],[]),([4,63,1986,30852,900048,1824040],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,1020696,1824040],[]),([4,63,1986,30852,1028880,1824040],[]),([4,63,1986,30852,1028888,1824040],[]),([4,63,1986,30852,1028888,1824042],[]),([4,63,1986,30852,1028888,1824056],[]),([4,63,1986,30852,1028888,1824168],[]),([4,63,1986,30852,1028890,1824042],[]),([4,63,1986,30852,1029016,1824168],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30852,1863367],[]),([4,63,1986,30854,233738,2057776],[]),([4,63,1986,30854,233752,1721376],[]),([4,63,1986,30854,1028888,1824040],[]),([4,63,1986,30860,233752,1721376],[]),([4,63,1986,30860,233791,2057776],[]),([4,63,1986,30860,1028888,1824040],[]),([4,63,1986,30868,233752,1721376],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30868,233752,1721392],[]),([4,63,1986,30868,233752,1722338],[]),([4,63,1986,30868,233752,1735844],[]),([4,63,1986,30868,233752,1735860],[]),([4,63,1986,30868,233752,2057776],[]),([4,63,1986,30868,233756,1721376],[]),([4,63,1986,30868,233768],[]),([4,63,1986,30868,233768,860688],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30868,233791,1824040],[(132,8)]),([4,63,1986,30868,233864,1721376],[(80,7)]),([4,63,1986,30868,375775,1824040],[]),([4,63,1986,30868,758024,1721376],[]),([4,63,1986,30868,1028888,1824040],[]),([4,63,1986,30870,233754,1721376],[]),([4,63,1986,30876,233791,1721376],[(132,0)]),([4,63,1986,30876,1028888,1824040],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,30900,233784],[]),([4,63,1986,30900,233784,860688],[]),([4,63,1986,30900,233784,2057776],[]),([4,63,1986,30900,1863415],[(14,1)]),([4,63,1986,31108,235466,2057776],[(104,3),(136,3)]),([4,63,1986,31108,1028888,1824040],[]),([4,63,1986,39375,883348,1824040],[]),([4,63,1986,39375,883348,2094904],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,1986,39375,2064052,2094904],[]),([4,63,1986,260492,864784,1725472],[]),([4,63,2002,30868,233752,1721376],[]),([4,63,6082,260492,860688,1721376],[]),([4,63,6082,260492,860688,1722338],[]),([4,63,6082,260492,860688,1725472],[]),([4,63,6082,260492,860688,1726434],[(104,5)]),([4,63,6082,260492,860688,1735844],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,6082,260492,860688,1834412],[]),([4,63,6082,260492,860688,2057776],[]),([4,63,6082,260492,2057776],[]),([4,63,6086,260492,860688,1721376],[]),([4,63,32710,235466,260492,2057776],[(108,3),(116,7)]),([4,128,191,32710,233736,2057776],[]),([4,191,1986,30852,233736,860720],[]),([4,191,1986,30852,233736,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([4,191,1986,30852,233736,2057904],[]),([4,191,1986,30852,233736,2058226],[]),([4,191,1986,30852,233736,2094904],[]),([4,191,1986,30852,233752,1721376],[]),([4,191,1986,30852,233864,2057776],[]),([4,191,1986,30852,1028888,1824040],[]),([4,191,1986,30868,233736,1721376],[]),([4,191,1986,32710,233736,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([4,191,1986,233736,883348,1735844],[]),([4,191,32710,233736,860688,1721376],[]),([4,191,32710,233736,860688,1721504],[]),([4,191,32710,233736,860688,1722338],[]),([4,191,32710,233736,860688,1736678],[]),([4,191,32710,233736,860688,1824040],[]),([4,191,32710,233736,860688,2057776],[]),([4,191,32710,233736,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([4,191,32710,233864,860688,1721376],[]),([4,447,1986,30852,233736,2057776],[(80,1)]),([4,447,30852,233736,860688,1722338],[]),([4,447,30852,235466,860688,1721376],[]),([4,1986,2047,30852,233791,2094904],[(128,3),(140,1)]),([4,1986,30852,233784,2097088],[]),([4,1986,30911,233791,260492,2057776],[(84,5)]),([4,1986,30911,233791,860688,1834412],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([4,1986,30911,233791,883348,1824040],[]),([5,0,48,63,1986,30852,233736],[(104,5),(136,1)]),([5,0,63,1986,30852,233736,860720],[]),([5,0,63,1986,30852,233736,2057776],[]),([5,0,63,1986,30852,233752,1721376],[]),([5,2,48,63,1986,30852,233736],[(128,1),(136,1)]),([5,2,63,1986,30852,233736,860720],[(96,1)]),([5,2,63,1986,30852,233736,2057776],[(96,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([5,2,63,1986,30852,233736,2057778],[(96,1)]),([5,2,63,1986,30852,233736,2058226],[(96,1)]),([5,2,63,1986,30852,233736,2064052],[(56,3),(72,3),(96,1),(168,3)]),([5,2,63,1986,30852,233738,2057776],[]),([5,2,63,1986,30852,233752,1721376],[]),([5,2,63,1986,30852,1028888,1824040],[(128,0)]),([5,2,63,2002,30852,233736,1721376],[(56,5),(72,5),(96,9),(128,5),(168,5)]),([5,2,63,2047,30852,233736,2057776],[(96,9),(128,5),(168,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_54 : List (List ℕ × List (ℕ × ℕ)) := [([5,2,63,30852,233736,862162,1722338],[(56,5),(72,9),(96,5),(128,5),(168,5)]),([5,6,63,1986,30852,233736,2057776],[(72,5),(96,1)]),([5,15,63,1986,30852,233736],[]),([5,15,63,1986,30852,233736,2057776],[]),([5,16,32,63,1986,30852,233736],[(96,6),(104,5),(128,2),(136,1),(168,0)]),([5,16,32,63,1986,30852,233752],[(72,0),(96,4),(104,5),(128,0),(136,1),(168,0)]),([5,16,34,63,1986,30852,233736],[(96,0),(104,5),(128,2),(136,1),(168,0)]),([5,16,47,1986,30852,233736,1721376],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_54 : K_54.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_55 : List (List ℕ × List (ℕ × ℕ)) := [([5,16,48,63,1986,30852,233736],[(96,5),(104,5),(128,1),(136,1)]),([5,16,63,128,32710,233736,1721376],[(144,7),(168,0)]),([5,16,63,962,30852,233736,1721376],[(96,1)]),([5,16,63,1056,1986,30852,233736],[(72,0),(96,0),(112,5),(128,2),(168,0)]),([5,16,63,1474,30852,233736,1721376],[(72,0),(96,2),(128,0),(168,0)]),([5,16,63,1986,2018,30852,233736],[(72,5),(112,5),(128,2),(168,0)]),([5,16,63,1986,30852,233736,524320],[(72,5),(96,1),(184,5),(192,1)]),([5,16,63,1986,30852,233736,860720],[(72,5),(96,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_55 : K_55.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_56 : List (List ℕ × List (ℕ × ℕ)) := [([5,16,63,1986,30852,233736,1197088],[(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233736,1590304],[(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233736,1721376],[(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233736,1721378],[(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233736,1721392],[(56,0),(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233736,1721504],[(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233736,1721888],[(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233736,1722338],[(72,5),(96,1),(168,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_56 : K_56.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_57 : List (List ℕ × List (ℕ × ℕ)) := [([5,16,63,1986,30852,233736,1722354],[(56,0),(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233736,1736678],[(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233736,2057776],[(72,5),(96,1)]),([5,16,63,1986,30852,233736,2058226],[(72,5),(96,1)]),([5,16,63,1986,30852,233736,2097120],[(72,5),(96,1)]),([5,16,63,1986,30852,233738,1721376],[(72,5),(96,1),(168,0)]),([5,16,63,1986,30852,233752,1721376],[(72,3)]),([5,16,63,1986,30852,233752,1721392],[(72,3)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_57 : K_57.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_58 : List (List ℕ × List (ℕ × ℕ)) := [([5,16,63,1986,30852,233752,1722338],[(72,3)]),([5,16,63,1986,30852,233752,1824040],[(72,5),(96,1)]),([5,16,63,1986,30852,233752,1824056],[(72,5),(96,1)]),([5,16,63,1986,30852,233752,2057776],[(72,3)]),([5,16,63,1986,30852,233768],[(72,3),(74,3),(97,3),(129,0)]),([5,16,63,1986,30852,233768,860688],[(56,0),(72,3),(168,0)]),([5,16,63,1986,30852,233768,1721376],[(72,6),(96,2),(128,0),(168,0)]),([5,16,63,1986,30852,233791,1824040],[(72,3),(168,0),(180,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_58 : K_58.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_59 : List (List ℕ × List (ℕ × ℕ)) := [([5,16,63,1986,30852,233864,1721376],[(72,3),(112,7),(168,0)]),([5,16,63,1986,30852,375775,1824040],[(72,3)]),([5,16,63,1986,30852,758024,1721376],[(72,3),(168,0)]),([5,16,63,1986,30852,1028888,1824040],[(72,3)]),([5,16,63,1986,30868,233752,1721376],[]),([5,16,191,1986,30852,233736,1721376],[(72,3),(168,0)]),([5,18,63,1986,30852,233736,1721376],[(72,5),(96,1),(168,0)]),([5,18,63,1986,30852,233736,1721394],[(56,0),(72,5),(96,1),(168,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_59 : K_59.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_60 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,63,1986,30852,233736,1722338],[(72,5),(96,1),(168,0)]),([5,18,63,1986,30852,233736,1735844],[(72,5),(96,1),(168,4)]),([5,18,63,1986,30852,233736,2057776],[(72,5),(96,1)]),([5,18,63,1986,30852,233736,2058226],[(72,5),(96,1)]),([5,18,63,1986,30852,233754,1721376],[(72,3)]),([5,18,63,2002,30852,233736,1721376],[(56,5),(72,5),(96,7),(128,3),(168,5)]),([5,18,63,2047,30852,233736,1721376],[(96,9),(128,5),(168,6),(180,0)]),([5,18,63,30852,233736,862162,1722338],[(56,5),(72,9),(96,5),(128,5),(168,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_60 : K_60.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_61 : List (List ℕ × List (ℕ × ℕ)) := [([5,22,63,1986,30852,233736,1721376],[(72,5),(96,1),(168,0)]),([5,31,63,1986,30852,233736,2057776],[]),([5,48,48,63,1986,30852,233736],[(96,5),(128,1)]),([5,48,63,63,1986,30852,233736],[(96,5),(128,1)]),([5,48,63,128,1986,30852,233736],[(96,3)]),([5,48,63,512,1986,30852,233736],[(128,1)]),([5,48,63,1536,1986,30852,233736],[(128,1)]),([5,48,63,1986,1986,30852,233736],[(128,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_61 : K_61.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_62 : List (List ℕ × List (ℕ × ℕ)) := [([5,48,63,1986,2034,30852,233736],[(72,5),(76,5),(112,5),(128,1)]),([5,48,63,1986,2047,30852,233736],[(72,5),(128,1)]),([5,48,63,1986,30852,32710,233736],[(72,5),(96,1)]),([5,48,63,1986,30852,39375,233736],[(72,5),(96,1),(156,3),(204,7)]),([5,48,63,1986,30852,233736],[(72,5),(74,5),(96,1),(97,3),(98,1),(129,7)]),([5,48,63,1986,30852,233736,375775],[(72,5),(96,1),(196,3),(204,7)]),([5,48,63,1986,30852,233736,524288],[(72,5),(96,1),(184,5),(192,1)]),([5,48,63,1986,30852,233736,860688],[(72,5),(96,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_62 : K_62.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_63 : List (List ℕ × List (ℕ × ℕ)) := [([5,48,63,1986,30852,233736,860720],[(72,5),(96,1)]),([5,48,63,1986,30852,233736,860735],[(72,5),(96,1)]),([5,48,63,1986,30852,233736,862162],[(72,5),(96,1)]),([5,48,63,1986,30852,233736,1863415],[(72,5),(96,1)]),([5,48,63,1986,30852,233736,2057776],[(72,5),(96,1)]),([5,48,63,1986,30852,233736,2057791],[(72,5),(96,1)]),([5,48,63,1986,30852,233736,2058226],[(72,5),(96,1)]),([5,48,63,1986,30852,233736,2097088],[(72,5),(96,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_63 : K_63.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_64 : List (List ℕ × List (ℕ × ℕ)) := [([5,48,63,1986,30852,233736,2097103],[(72,5),(96,1)]),([5,48,63,1986,30852,233784],[(72,3),(74,3),(97,3)]),([5,48,63,1986,30852,233784,860688],[(72,3)]),([5,48,63,1986,30852,233784,2057776],[(72,3)]),([5,48,63,1986,30852,1863415],[(72,3)]),([5,48,1986,30852,233736,2097088],[(56,5),(72,1)]),([5,50,63,1986,30852,233736],[(72,5),(96,1),(97,3),(98,1),(129,7)]),([5,50,63,1986,30852,233736,860688],[(72,5),(96,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_64 : K_64.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_65 : List (List ℕ × List (ℕ × ℕ)) := [([5,50,63,1986,30852,233736,862162],[(72,5),(96,1)]),([5,50,63,1986,30852,233736,2057776],[(72,5),(96,1)]),([5,50,63,1986,30852,233736,2058226],[(72,5),(96,1)]),([5,55,63,1986,30852,233736,2057776],[]),([5,63,63,1986,30852,233736,860720],[]),([5,63,63,1986,30852,233736,2057776],[]),([5,63,63,1986,30852,233736,2058226],[(72,5)]),([5,63,63,1986,30852,233752,1721376],[(172,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_65 : K_65.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_66 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,63,1986,30852,1028888,1824040],[]),([5,63,128,1986,30852,233736,860720],[]),([5,63,128,1986,30852,233736,2057776],[]),([5,63,128,1986,30852,233736,2057904],[]),([5,63,128,1986,30852,233736,2058226],[]),([5,63,128,1986,30852,233736,2094904],[(80,7),(104,7),(176,7)]),([5,63,128,1986,30852,233752,1721376],[]),([5,63,128,1986,30852,233864,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_66 : K_66.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_67 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,128,1986,30852,1028888,1824040],[(136,0)]),([5,63,128,1986,30868,233736,1721376],[(80,1),(104,1),(176,1)]),([5,63,128,1986,32710,233736,2057776],[(136,1)]),([5,63,128,1986,233736,883348,1735844],[(80,1),(104,1),(136,1),(176,1)]),([5,63,128,32710,233736,860688,1721376],[(104,7)]),([5,63,128,32710,233736,860688,1721504],[(104,7),(136,7)]),([5,63,128,32710,233736,860688,1722338],[(104,7)]),([5,63,128,32710,233736,860688,1736678],[(104,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_67 : K_67.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_68 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,128,32710,233736,860688,1824040],[(104,7)]),([5,63,128,32710,233736,860688,2057776],[(104,7)]),([5,63,128,32710,233736,2057776],[(104,7),(105,7)]),([5,63,128,32710,233864,860688,1721376],[(80,7),(104,7),(136,8),(176,7)]),([5,63,130,1986,30852,233736,2057776],[(104,1)]),([5,63,130,32710,233736,860688,1721376],[(104,7)]),([5,63,144,1986,30852,233736,1721376],[(80,5),(104,1),(176,0)]),([5,63,191,1986,30852,233736,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_68 : K_68.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_69 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,191,32710,233736,860688,1721376],[(172,0)]),([5,63,384,1986,30852,233736,2057776],[(104,1),(112,1)]),([5,63,384,30852,233736,860688,1722338],[(136,5)]),([5,63,384,30852,235466,860688,1721376],[(80,3)]),([5,63,386,30852,233736,860688,1721376],[]),([5,63,450,1986,30852,233736,2057776],[]),([5,63,450,30852,39375,233736],[]),([5,63,450,30852,39375,233736,2057776],[(156,1),(176,5),(184,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_69 : K_69.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_70 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,450,30852,233736,860688,1721376],[]),([5,63,450,30852,233736,860688,2057776],[]),([5,63,450,30852,233736,2057776],[(154,1)]),([5,63,512,1986,30852,233736,860720],[]),([5,63,512,1986,30852,233736,1721392],[(80,0),(176,0)]),([5,63,512,1986,30852,233736,2057776],[]),([5,63,512,1986,30852,233736,2058226],[]),([5,63,512,1986,30852,233736,2064052],[(80,3),(176,3)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_70 : K_70.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_71 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,512,1986,30852,233752,1721376],[]),([5,63,512,1986,30852,233768,860688],[(80,0),(176,0)]),([5,63,512,1986,30852,1028888,1824040],[]),([5,63,512,2002,30852,233736,1721376],[(80,5),(176,5)]),([5,63,512,2018,30852,233736,860688],[(80,6),(176,6)]),([5,63,512,30852,233736,862162,1722338],[(136,5),(176,5)]),([5,63,514,1986,30852,233736,2057776],[]),([5,63,528,1056,1986,30852,233736],[(104,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_71 : K_71.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_72 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,528,1986,30852,233736,1721376],[(80,5),(176,0)]),([5,63,528,1986,30852,233736,1721904],[(80,5),(176,0)]),([5,63,528,1986,30852,233736,1722338],[(80,5),(176,0)]),([5,63,528,1986,30852,233736,1735844],[(80,5),(104,1),(176,4)]),([5,63,528,1986,30852,233736,2057776],[(80,5)]),([5,63,528,2002,30852,233736,1721376],[(80,5),(176,5)]),([5,63,528,2047,30852,233736,1722338],[(176,6)]),([5,63,544,1986,30852,233736,860688],[(80,6)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_72 : K_72.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_73 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,575,1986,30852,233736,2057776],[]),([5,63,640,1986,30852,233736,2057776],[]),([5,63,640,1986,30852,233736,2064052],[(80,3),(176,3)]),([5,63,640,1986,233736,883348,1735844],[(80,1),(136,1)]),([5,63,660,1986,30852,233736,1721376],[(80,5),(176,0)]),([5,63,962,1986,30852,233736,2057776],[]),([5,63,962,14468,233736,860688,1721376],[]),([5,63,962,30852,233736,336400,1721376],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_73 : K_73.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_74 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,962,30852,233736,375775,2057776],[(156,1)]),([5,63,962,30852,233736,860688,1721376],[]),([5,63,962,30852,233736,860688,1722338],[(136,5)]),([5,63,962,30852,233736,860688,1735844],[(144,1)]),([5,63,962,30852,233736,860688,2057776],[]),([5,63,962,30852,233736,861138,1721376],[(176,5)]),([5,63,962,30852,233736,862162,1721376],[(176,5)]),([5,63,962,30852,233736,883348,1721376],[(184,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_74 : K_74.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_75 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,962,30852,233736,1721376,2057776],[]),([5,63,962,30852,233736,2057776],[(154,1)]),([5,63,962,30852,375775,860688,1824040],[]),([5,63,1536,1986,30852,233736,2057776],[]),([5,63,1536,1986,30852,233736,2058226],[]),([5,63,1536,1986,30852,233736,2064052],[(80,3),(176,3)]),([5,63,1538,1986,30852,233736,2057776],[]),([5,63,1584,1986,2047,30852,233736],[(80,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_75 : K_75.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_76 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1584,1986,30852,233736],[(80,5),(105,3),(137,7)]),([5,63,1584,1986,30852,233736,860688],[(80,5)]),([5,63,1584,1986,30852,233736,2057776],[(80,5)]),([5,63,1599,1986,30852,233736,2057776],[]),([5,63,1664,1986,30852,233736,2057776],[]),([5,63,1664,1986,30852,233736,2064052],[(80,3),(176,3)]),([5,63,1730,1986,30852,233736,2057776],[]),([5,63,1984,1986,30852,233736,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_76 : K_76.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_77 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1984,30852,233736,860688,1722338],[(136,5)]),([5,63,1986,1986,30852,233736,860720],[]),([5,63,1986,1986,30852,233736,2057776],[]),([5,63,1986,1986,30852,233736,2058226],[]),([5,63,1986,1986,30852,233736,2064052],[(64,3),(68,3)]),([5,63,1986,1986,30852,233752,1721376],[]),([5,63,1986,1986,30852,1028888,1824040],[]),([5,63,1986,1990,30852,233736,2057776],[(80,5),(176,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_77 : K_77.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_78 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,2002,30852,233736,1721376],[(80,5),(176,5),(184,0)]),([5,63,1986,2002,30852,233736,1721392],[(80,5),(84,0),(176,5),(184,0)]),([5,63,1986,2002,30852,233736,1722338],[(80,5),(176,5),(184,0)]),([5,63,1986,2002,30852,233736,1722354],[(80,5),(84,0),(176,5),(184,0)]),([5,63,1986,2002,30852,233736,1735844],[(80,5),(176,5),(184,0)]),([5,63,1986,2002,30852,233736,2057776],[(80,5),(176,5)]),([5,63,1986,2002,30852,233752,1721376],[(80,3),(176,3)]),([5,63,1986,2006,30852,233736,1721376],[(80,5),(176,5),(184,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_78 : K_78.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_79 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,2034,30852,233736],[(6,5),(58,5),(80,5),(81,5),(105,5),(109,3),(137,9),(141,7),(145,1)]),([5,63,1986,2034,30852,233736,860688],[(80,5),(176,5)]),([5,63,1986,2034,30852,233736,2057776],[(80,5),(176,5)]),([5,63,1986,2047,30852,233736,860720],[(176,5)]),([5,63,1986,2047,30852,233736,861744],[(176,5)]),([5,63,1986,2047,30852,233736,2057776],[(176,5)]),([5,63,1986,2047,30852,233736,2058226],[(80,5),(176,5)]),([5,63,1986,2047,30852,233736,2064052],[(76,3),(84,3),(96,1),(176,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_79 : K_79.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_80 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,2047,30852,233752,1721376],[(176,5),(188,0)]),([5,63,1986,2047,30852,1028888,1824040],[]),([5,63,1986,2247,30852,233736],[(10,7)]),([5,63,1986,2247,30852,233736,2057776],[]),([5,63,1986,2247,30852,233736,2094904],[]),([5,63,1986,2247,30852,2057776],[]),([5,63,1986,6082,30852,233736,2057776],[(80,5),(176,5)]),([5,63,1986,6082,260492,860688,1721376],[(136,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_80 : K_80.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_81 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,8704,30852,233736,2057776],[]),([5,63,1986,8720,30852,233736,1721376],[(184,0)]),([5,63,1986,10178,30852,233736,2057776],[]),([5,63,1986,10194,30852,233736,1721376],[(176,5),(184,0)]),([5,63,1986,26112,30852,233736,2057776],[]),([5,63,1986,26562,30852,233736,2057776],[]),([5,63,1986,30852,32710,233736,860720],[]),([5,63,1986,30852,32710,233736,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_81 : K_81.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_82 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,32710,233736,2058226],[]),([5,63,1986,30852,32710,233736,2064374],[]),([5,63,1986,30852,32710,233736,2094904],[(108,7),(116,7),(156,7)]),([5,63,1986,30852,32710,233752,1721376],[]),([5,63,1986,30852,32710,1028888,1824040],[]),([5,63,1986,30852,32726,233736,1721376],[(192,0)]),([5,63,1986,30852,32767,233736,2057776],[(156,7)]),([5,63,1986,30852,39360,233736,2057776],[(176,5),(184,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_82 : K_82.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_83 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,39375,233736],[]),([5,63,1986,30852,39375,233736,2057776],[(116,3),(156,7),(176,5),(184,1)]),([5,63,1986,30852,39375,233736,2058226],[(104,5),(116,3),(156,7),(176,5)]),([5,63,1986,30852,39375,860688,1824040],[(136,3)]),([5,63,1986,30852,39375,860688,2094904],[(136,3)]),([5,63,1986,30852,39375,1028888,2057776],[(156,7),(176,5),(184,1)]),([5,63,1986,30852,39375,1863415],[]),([5,63,1986,30852,39375,2057776,2094904],[(136,3),(196,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_83 : K_83.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_84 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,39375,2094904],[(117,3),(157,7)]),([5,63,1986,30852,39423,233736,2057776],[(116,3),(156,7),(176,5),(184,1)]),([5,63,1986,30852,40911,233736],[(14,5)]),([5,63,1986,30852,40911,233736,2057776],[(116,3),(156,7),(176,5)]),([5,63,1986,30852,233736,262094,2057776],[]),([5,63,1986,30852,233736,270864,1721376],[(200,0)]),([5,63,1986,30852,233736,270864,1824040],[(200,7)]),([5,63,1986,30852,233736,273111,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_84 : K_84.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_85 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,273111,2094904],[]),([5,63,1986,30852,233736,336400,1721376],[]),([5,63,1986,30852,233736,336400,1722338],[(136,5)]),([5,63,1986,30852,233736,336400,2057776],[]),([5,63,1986,30852,233736,336850,1721376],[(176,5)]),([5,63,1986,30852,233736,337874,1721376],[(176,5)]),([5,63,1986,30852,233736,375744,2057776],[]),([5,63,1986,30852,233736,375759],[(18,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_85 : K_85.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_86 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,375759,1721392],[(148,3),(156,7),(176,5),(184,1)]),([5,63,1986,30852,233736,375775,860720],[(148,3),(156,7)]),([5,63,1986,30852,233736,375775,1721392],[(148,3),(156,7),(176,5),(184,1)]),([5,63,1986,30852,233736,375775,2057776],[(148,3),(156,7)]),([5,63,1986,30852,233736,375775,2058226],[(148,3),(156,7)]),([5,63,1986,30852,233736,375807,2057776],[(148,3),(156,7)]),([5,63,1986,30852,233736,376799,2057776],[(148,3),(156,7)]),([5,63,1986,30852,233736,524288,860720],[(136,5),(144,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_86 : K_86.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_87 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,524288,2057776],[(136,5),(144,1)]),([5,63,1986,30852,233736,524288,2058226],[(136,5),(144,1)]),([5,63,1986,30852,233736,524304,1721376],[(136,5),(144,1),(200,0)]),([5,63,1986,30852,233736,524304,1721392],[(136,5),(144,1),(200,0)]),([5,63,1986,30852,233736,524304,1722338],[(136,5),(144,1),(200,0)]),([5,63,1986,30852,233736,524304,2057776],[(136,5),(144,1)]),([5,63,1986,30852,233736,524351,2057776],[]),([5,63,1986,30852,233736,524800,2057776],[(136,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_87 : K_87.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_88 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,524800,2058226],[(136,5)]),([5,63,1986,30852,233736,524816,1721376],[(136,5),(200,0)]),([5,63,1986,30852,233736,524816,1722338],[(136,5),(200,0)]),([5,63,1986,30852,233736,524834,860688],[(136,6)]),([5,63,1986,30852,233736,526274,2057776],[(136,5),(176,5)]),([5,63,1986,30852,233736,526290,1721376],[(136,5),(176,5),(200,0)]),([5,63,1986,30852,233736,786960,1721376],[(136,6),(200,0)]),([5,63,1986,30852,233736,795152,1590304],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_88 : K_88.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_89 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,795152,1721376],[(200,0)]),([5,63,1986,30852,233736,795152,1722338],[(136,5),(200,0)]),([5,63,1986,30852,233736,795152,1824040],[(200,7)]),([5,63,1986,30852,233736,795152,1992240],[(200,0)]),([5,63,1986,30852,233736,795152,2057776],[]),([5,63,1986,30852,233736,796370,1721376],[(200,0)]),([5,63,1986,30852,233736,796626,1721376],[(176,5),(200,0)]),([5,63,1986,30852,233736,860672,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_89 : K_89.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_90 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,860688,860720],[]),([5,63,1986,30852,233736,860688,860722],[]),([5,63,1986,30852,233736,860688,861744],[]),([5,63,1986,30852,233736,860688,862194],[]),([5,63,1986,30852,233736,860688,1721376],[]),([5,63,1986,30852,233736,860688,1721378],[]),([5,63,1986,30852,233736,860688,1721382],[]),([5,63,1986,30852,233736,860688,1721392],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_90 : K_90.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_91 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,860688,1721394],[]),([5,63,1986,30852,233736,860688,1721504],[]),([5,63,1986,30852,233736,860688,1721506],[]),([5,63,1986,30852,233736,860688,1721760],[(136,6)]),([5,63,1986,30852,233736,860688,1721826],[(136,6)]),([5,63,1986,30852,233736,860688,1721888],[]),([5,63,1986,30852,233736,860688,1721890],[]),([5,63,1986,30852,233736,860688,1721904],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_91 : K_91.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_92 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,860688,1722016],[]),([5,63,1986,30852,233736,860688,1722082],[]),([5,63,1986,30852,233736,860688,1722336],[(136,6)]),([5,63,1986,30852,233736,860688,1722338],[(136,5)]),([5,63,1986,30852,233736,860688,1722342],[(136,5)]),([5,63,1986,30852,233736,860688,1722354],[(136,5)]),([5,63,1986,30852,233736,860688,1726434],[(136,5)]),([5,63,1986,30852,233736,860688,1730080],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_92 : K_92.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_93 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,860688,1730530],[]),([5,63,1986,30852,233736,860688,1736678],[]),([5,63,1986,30852,233736,860688,1760736],[(136,6),(144,2),(152,0)]),([5,63,1986,30852,233736,860688,1834990],[]),([5,63,1986,30852,233736,860688,1861168],[]),([5,63,1986,30852,233736,860688,1926704],[]),([5,63,1986,30852,233736,860688,1992240],[]),([5,63,1986,30852,233736,860688,1994464],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_93 : K_93.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_94 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,860688,2057760],[]),([5,63,1986,30852,233736,860688,2057776],[]),([5,63,1986,30852,233736,860688,2057778],[]),([5,63,1986,30852,233736,860688,2057904],[]),([5,63,1986,30852,233736,860688,2058226],[]),([5,63,1986,30852,233736,860688,2064374],[]),([5,63,1986,30852,233736,860688,2097120],[]),([5,63,1986,30852,233736,860688,2097122],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_94 : K_94.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_95 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,860688,2097136],[]),([5,63,1986,30852,233736,860690,1721378],[]),([5,63,1986,30852,233736,860690,1722338],[(136,5)]),([5,63,1986,30852,233736,860690,1735844],[(144,2),(200,3)]),([5,63,1986,30852,233736,860690,2057776],[]),([5,63,1986,30852,233736,860690,2057778],[]),([5,63,1986,30852,233736,860720],[(146,3),(154,7)]),([5,63,1986,30852,233736,860720,860720],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_95 : K_95.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_96 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,860720,860735],[]),([5,63,1986,30852,233736,860720,862162],[]),([5,63,1986,30852,233736,860720,862194],[]),([5,63,1986,30852,233736,860720,1721407],[]),([5,63,1986,30852,233736,860720,1722338],[(136,6)]),([5,63,1986,30852,233736,860720,1863415],[]),([5,63,1986,30852,233736,860720,2057776],[]),([5,63,1986,30852,233736,860720,2097088],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_96 : K_96.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_97 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,860720,2097119],[]),([5,63,1986,30852,233736,860722],[(58,5),(146,3),(154,7)]),([5,63,1986,30852,233736,860722,1722338],[(136,6)]),([5,63,1986,30852,233736,860735,2057776],[]),([5,63,1986,30852,233736,860735,2058226],[]),([5,63,1986,30852,233736,860816,1721504],[(80,7)]),([5,63,1986,30852,233736,860816,1722338],[(136,5)]),([5,63,1986,30852,233736,860816,1824040],[(152,0),(200,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_97 : K_97.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_98 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,860816,2057776],[]),([5,63,1986,30852,233736,860816,2057904],[]),([5,63,1986,30852,233736,861712,1722338],[(136,5)]),([5,63,1986,30852,233736,861712,1735844],[(200,3)]),([5,63,1986,30852,233736,861712,2057776],[]),([5,63,1986,30852,233736,861744],[(146,3),(154,7)]),([5,63,1986,30852,233736,861840,1735844],[(200,3)]),([5,63,1986,30852,233736,862162,862194],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_98 : K_98.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_99 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,862162,1722338],[(136,5),(176,5)]),([5,63,1986,30852,233736,862162,1735844],[]),([5,63,1986,30852,233736,862162,1736678],[]),([5,63,1986,30852,233736,862162,1834412],[]),([5,63,1986,30852,233736,862162,2057776],[]),([5,63,1986,30852,233736,862162,2058226],[]),([5,63,1986,30852,233736,862162,2064052],[(140,3)]),([5,63,1986,30852,233736,862162,2064374],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_99 : K_99.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_100 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,862162,2097120],[]),([5,63,1986,30852,233736,862194],[(58,5),(154,1)]),([5,63,1986,30852,233736,862207,2057776],[]),([5,63,1986,30852,233736,862207,2058226],[]),([5,63,1986,30852,233736,884694,1736678],[]),([5,63,1986,30852,233736,884694,2057776],[]),([5,63,1986,30852,233736,884694,2058226],[]),([5,63,1986,30852,233736,884694,2064374],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_100 : K_100.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_101 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,900063,2057776],[(148,3),(156,7)]),([5,63,1986,30852,233736,1572863,2057776],[]),([5,63,1986,30852,233736,1836659,2057776],[]),([5,63,1986,30852,233736,1861168],[(146,3),(154,7)]),([5,63,1986,30852,233736,1861168,1863415],[]),([5,63,1986,30852,233736,1861168,2057776],[]),([5,63,1986,30852,233736,1863360,2057776],[]),([5,63,1986,30852,233736,1863415,1926704],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_101 : K_101.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_102 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,1863415,2057776],[]),([5,63,1986,30852,233736,1863415,2058226],[]),([5,63,1986,30852,233736,1863415,2094904],[]),([5,63,1986,30852,233736,1863423,2057776],[]),([5,63,1986,30852,233736,1863671,2057776],[]),([5,63,1986,30852,233736,1900543,2057776],[(156,7)]),([5,63,1986,30852,233736,1926704],[(146,3),(154,7)]),([5,63,1986,30852,233736,1928951,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_102 : K_102.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_103 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,1966079,2057776],[(156,7)]),([5,63,1986,30852,233736,2057728,2057776],[]),([5,63,1986,30852,233736,2057776],[(146,3),(154,7)]),([5,63,1986,30852,233736,2057776,2057776],[]),([5,63,1986,30852,233736,2057776,2057778],[]),([5,63,1986,30852,233736,2057776,2057791],[]),([5,63,1986,30852,233736,2057776,2057904],[]),([5,63,1986,30852,233736,2057776,2058226],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_103 : K_103.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_104 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,2057776,2058239],[]),([5,63,1986,30852,233736,2057776,2060023],[]),([5,63,1986,30852,233736,2057776,2064374],[]),([5,63,1986,30852,233736,2057776,2093055],[]),([5,63,1986,30852,233736,2057776,2097088],[]),([5,63,1986,30852,233736,2057776,2097090],[]),([5,63,1986,30852,233736,2057776,2097103],[]),([5,63,1986,30852,233736,2057776,2097104],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_104 : K_104.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_105 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,2057776,2097119],[]),([5,63,1986,30852,233736,2057776,2097136],[]),([5,63,1986,30852,233736,2057776,2097143],[]),([5,63,1986,30852,233736,2057776,2097151],[]),([5,63,1986,30852,233736,2057778],[(58,5),(146,3),(154,7)]),([5,63,1986,30852,233736,2057791,2058226],[]),([5,63,1986,30852,233736,2057904],[(146,3),(154,7)]),([5,63,1986,30852,233736,2058226],[(58,5),(154,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_105 : K_105.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_106 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,2058226,2058226],[]),([5,63,1986,30852,233736,2058226,2058239],[]),([5,63,1986,30852,233736,2058226,2064052],[(140,3)]),([5,63,1986,30852,233736,2058226,2064374],[]),([5,63,1986,30852,233736,2058226,2097088],[]),([5,63,1986,30852,233736,2064374],[(58,5),(74,1)]),([5,63,1986,30852,233736,2097088,2097136],[]),([5,63,1986,30852,233736,2097103],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_106 : K_106.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_107 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233736,2097104,2097120],[]),([5,63,1986,30852,233736,2097104,2097136],[]),([5,63,1986,30852,233736,2097136],[(146,3),(154,7)]),([5,63,1986,30852,233738,860688,1721376],[]),([5,63,1986,30852,233738,860688,1721378],[]),([5,63,1986,30852,233738,860688,1722338],[(136,5)]),([5,63,1986,30852,233738,860688,1735844],[(144,1)]),([5,63,1986,30852,233738,860688,1824040],[(152,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_107 : K_107.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_108 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233738,860688,1824042],[]),([5,63,1986,30852,233738,860688,2057776],[]),([5,63,1986,30852,233738,2057776],[(58,5)]),([5,63,1986,30852,233742,860688,1721376],[]),([5,63,1986,30852,233752,233752,1721376],[]),([5,63,1986,30852,233752,233791,1721376],[(192,0),(204,8)]),([5,63,1986,30852,233752,235466,1721376],[]),([5,63,1986,30852,233752,235482,1721376],[(108,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_108 : K_108.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_109 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233752,375775],[]),([5,63,1986,30852,233752,375775,1721376],[(148,3),(156,7),(176,5),(184,1)]),([5,63,1986,30852,233752,524288,1721376],[(136,5),(144,1)]),([5,63,1986,30852,233752,860688,1721376],[]),([5,63,1986,30852,233752,860688,1721392],[]),([5,63,1986,30852,233752,860688,1722338],[(136,5)]),([5,63,1986,30852,233752,860688,1824040],[]),([5,63,1986,30852,233752,860688,1824056],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_109 : K_109.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_110 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233752,860688,2057776],[]),([5,63,1986,30852,233752,860735,1721376],[]),([5,63,1986,30852,233752,862162,1721376],[(176,5)]),([5,63,1986,30852,233752,1028888,1721376],[]),([5,63,1986,30852,233752,1236463,1721376],[(140,0),(148,4)]),([5,63,1986,30852,233752,1721376],[(134,0),(146,3)]),([5,63,1986,30852,233752,1721376,1721376],[]),([5,63,1986,30852,233752,1721376,1721392],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_110 : K_110.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_111 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233752,1721376,1721407],[]),([5,63,1986,30852,233752,1721376,1722338],[]),([5,63,1986,30852,233752,1721376,1824040],[]),([5,63,1986,30852,233752,1721376,1824056],[]),([5,63,1986,30852,233752,1721376,1863399],[]),([5,63,1986,30852,233752,1721376,1863415],[]),([5,63,1986,30852,233752,1721376,2057776],[]),([5,63,1986,30852,233752,1721376,2066299],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_111 : K_111.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_112 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233752,1721376,2097088],[]),([5,63,1986,30852,233752,1721376,2097135],[]),([5,63,1986,30852,233752,1721392],[(146,3)]),([5,63,1986,30852,233752,1722338],[(58,5),(134,0)]),([5,63,1986,30852,233752,1824040],[(134,8),(146,3)]),([5,63,1986,30852,233752,1824056],[(98,0),(134,7),(146,3)]),([5,63,1986,30852,233752,2057776],[(146,3)]),([5,63,1986,30852,233754,860688,1721376],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_112 : K_112.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_113 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233754,862162,1721376],[(176,5)]),([5,63,1986,30852,233754,1721376],[(58,5),(134,0)]),([5,63,1986,30852,233784],[(6,5),(7,3),(9,3),(10,1),(75,3),(79,3),(103,7),(111,1),(115,3),(119,5)]),([5,63,1986,30852,233784,860688],[(18,0),(146,3),(150,3),(158,7)]),([5,63,1986,30852,233784,860688,1721376],[]),([5,63,1986,30852,233784,860688,2057776],[]),([5,63,1986,30852,233784,2057776],[(146,3),(150,3),(158,7)]),([5,63,1986,30852,233791,235466,2057776],[(56,3),(108,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_113 : K_113.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_114 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233791,860688,1721384],[]),([5,63,1986,30852,233791,860688,1824040],[(196,0)]),([5,63,1986,30852,233791,860688,1824746],[(56,3),(196,0)]),([5,63,1986,30852,233791,860688,2094904],[(172,7)]),([5,63,1986,30852,233791,862162,1824040],[(56,3),(196,0)]),([5,63,1986,30852,233791,1028888,1824040],[(196,0)]),([5,63,1986,30852,233791,1028888,2057776],[]),([5,63,1986,30852,233791,1028888,2094904],[(172,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_114 : K_114.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_115 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233791,2057776,2094904],[(172,7)]),([5,63,1986,30852,233791,2094904],[(73,3),(132,7),(133,7),(134,7),(146,3)]),([5,63,1986,30852,233864,860688,1721376],[(80,7)]),([5,63,1986,30852,233864,860688,1721504],[(80,7)]),([5,63,1986,30852,233864,860688,1722338],[(80,7),(136,5)]),([5,63,1986,30852,233864,860688,1824040],[(80,7),(152,0)]),([5,63,1986,30852,233864,860688,1824168],[(80,7)]),([5,63,1986,30852,233864,860688,2057776],[(80,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_115 : K_115.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_116 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,233864,2057776],[(80,7),(81,5),(82,1),(146,3)]),([5,63,1986,30852,233866,860688,1721376],[(80,7)]),([5,63,1986,30852,234248,860688,1824040],[]),([5,63,1986,30852,235466,260492,2057776],[(116,3)]),([5,63,1986,30852,235466,1028888,1824040],[]),([5,63,1986,30852,273111,1028888],[]),([5,63,1986,30852,273111,1028888,1824040],[]),([5,63,1986,30852,336400,375775,1824040],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_116 : K_116.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_117 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,375744,860688,1824040],[]),([5,63,1986,30852,375775,860688,1824040],[]),([5,63,1986,30852,375775,862162,1824040],[]),([5,63,1986,30852,375775,1028888,1824040],[(116,3)]),([5,63,1986,30852,375775,1824040,2057776],[(156,7)]),([5,63,1986,30852,375775,1824040,2094904],[(156,7)]),([5,63,1986,30852,375807,860688,1824040],[(196,7)]),([5,63,1986,30852,506847,860688,1824040],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_117 : K_117.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_118 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,524288,758024,2057776],[]),([5,63,1986,30852,524288,1028888,1824040],[]),([5,63,1986,30852,524304,758040,1721376],[]),([5,63,1986,30852,589824,1028888,1824040],[]),([5,63,1986,30852,758024,860688,1721376],[]),([5,63,1986,30852,758024,860688,1722338],[]),([5,63,1986,30852,758024,860688,1824040],[]),([5,63,1986,30852,758024,860688,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_118 : K_118.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_119 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,758024,1028888,1824040],[]),([5,63,1986,30852,758024,2057776],[(146,3)]),([5,63,1986,30852,758040,860688,1721376],[]),([5,63,1986,30852,758040,1721376],[(134,0),(146,3)]),([5,63,1986,30852,758040,1721376,1721407],[]),([5,63,1986,30852,860688,900063,1824040],[]),([5,63,1986,30852,860688,1028888,1824040],[]),([5,63,1986,30852,860688,1028920],[(14,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_119 : K_119.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_120 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,860688,1028927,1824040],[(204,0)]),([5,63,1986,30852,860688,1863383],[(18,0)]),([5,63,1986,30852,860720,1028920],[(14,0)]),([5,63,1986,30852,860720,1863415],[]),([5,63,1986,30852,860735,1028888,1824040],[]),([5,63,1986,30852,862162,1028888,1824040],[]),([5,63,1986,30852,1028888,1028888,1824040],[]),([5,63,1986,30852,1028888,1028927,1824040],[(204,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_120 : K_120.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_121 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,1028888,1030106,1824040],[]),([5,63,1986,30852,1028888,1824040],[]),([5,63,1986,30852,1028888,1824040,1863415],[]),([5,63,1986,30852,1028888,1824040,2057776],[]),([5,63,1986,30852,1028888,1824040,2066299],[]),([5,63,1986,30852,1028888,1824040,2094904],[]),([5,63,1986,30852,1028888,1824040,2097088],[]),([5,63,1986,30852,1861168,1863415],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_121 : K_121.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_122 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30852,1863415,1926704],[]),([5,63,1986,30852,1863415,2057776],[]),([5,63,1986,30852,1863415,2058226],[]),([5,63,1986,30852,1863415,2094904],[(14,7)]),([5,63,1986,30852,1928951,2057776],[(14,8)]),([5,63,1986,30852,2057776,2060023],[(18,7)]),([5,63,1986,30852,2057776,2094904],[]),([5,63,1986,30852,2057791,2094904],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_122 : K_122.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_123 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,30854,233738,860688,1721376],[]),([5,63,1986,30860,233791,860688,1721376],[]),([5,63,1986,30868,233752,860688,1721376],[]),([5,63,1986,30868,233752,1721376],[(134,0),(154,1)]),([5,63,1986,30868,1721376,1824040],[]),([5,63,1986,30868,1721376,1863415],[(18,1)]),([5,63,1986,31108,235466,860688,1721376],[(104,3),(136,4),(176,3)]),([5,63,1986,375775,860688,1735844,1824040],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_123 : K_123.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_124 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,1986,883348,1735844,1863415],[(18,1)]),([5,63,1986,883348,1824040,2057776],[]),([5,63,1986,883348,2057776,2094904],[]),([5,63,1986,1863415,2057776,2064052],[]),([5,63,1986,1863415,2057776,2066299],[]),([5,63,1986,2057776,2064052,2094904],[(80,98538)]),([5,63,6082,260492,860688,1721376],[(106,0),(114,0),(134,0),(153,0)]),([5,63,32710,235466,260492,860688,1721376],[(108,3),(116,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_124 : K_124.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_125 : List (List ℕ × List (ℕ × ℕ)) := [([5,128,191,1986,30852,233736,2057776],[]),([5,128,191,32710,233736,860688,1721376],[(128,0)]),([5,191,1986,30852,233736,860688,1721376],[]),([5,191,1986,30852,233736,860688,1721504],[]),([5,191,1986,30852,233736,860688,1722338],[(136,3)]),([5,191,1986,30852,233736,860688,1824040],[]),([5,191,1986,30852,233736,860688,2057776],[]),([5,191,1986,30852,233736,2057776],[(81,3),(146,3)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_125 : K_125.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_126 : List (List ℕ × List (ℕ × ℕ)) := [([5,191,1986,30852,233864,860688,1721376],[]),([5,191,1986,32710,233736,860688,1721376],[(136,0)]),([5,191,32710,233736,860688,1721376],[(106,0),(114,0),(134,0),(153,0)]),([5,447,1986,30852,233736,860688,1721376],[(80,1),(136,0)]),([5,1986,2047,30852,30911,233736,2057776],[(72,7),(168,5),(184,1)]),([5,1986,2047,30852,233791,860688,1824040],[(128,3),(168,3)]),([5,1986,30852,39375,233736,2097088],[]),([5,1986,30852,233736,860720,2097088],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_126 : K_126.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_127 : List (List ℕ × List (ℕ × ℕ)) := [([5,1986,30852,233736,2057776,2097088],[]),([5,1986,30852,233736,2058226,2097088],[]),([5,1986,30852,233736,2097088,2097136],[]),([5,1986,30852,233752,1721376,2097088],[]),([5,1986,30852,1028888,1824040,2097088],[]),([5,1986,30852,1863415,2057776,2097088],[]),([5,1986,30852,2057776,2094904,2097088],[]),([5,1986,30911,233791,260492,860688,1721376],[(84,5),(152,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_127 : K_127.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_128 : List (List ℕ × List (ℕ × ℕ)) := [([6,0,16,63,1986,30852,233736,1721376],[(104,5),(136,1),(224,0)]),([6,0,63,1986,30852,233736,860688,1721376],[]),([6,2,16,63,1986,30852,233736,1721376],[(128,1),(136,1),(224,0)]),([6,2,63,1986,30852,233736,860688,1721376],[(96,1),(168,0)]),([6,2,63,1986,30852,233736,860688,1721378],[(96,1)]),([6,2,63,1986,30852,233736,860688,1722338],[(96,1)]),([6,2,63,1986,30852,233736,860688,1735844],[(56,3),(72,3),(96,1),(192,1),(216,3)]),([6,2,63,1986,30852,233736,860688,2057776],[(96,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_128 : K_128.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_129 : List (List ℕ × List (ℕ × ℕ)) := [([6,2,63,1986,30852,233736,2057776],[(2,5),(96,1),(97,3),(98,1),(129,7),(202,1)]),([6,2,63,1986,30852,233738,860688,1721376],[(168,0)]),([6,2,63,2047,30852,233736,860688,1721376],[(96,9),(128,5),(168,6),(216,5)]),([6,6,63,1986,30852,233736,860688,1721376],[(72,5),(96,1),(168,0)]),([6,16,16,63,1986,30852,233736,1721376],[(96,5),(128,1)]),([6,16,32,63,1986,30852,233736],[(57,0),(96,6),(97,0),(98,5),(104,5),(106,6),(128,2),(129,4),(130,1),(136,1),(137,3),(138,2),(168,0),(169,8),(177,7),(178,0)]),([6,16,32,63,1986,30852,233736,860688],[(72,0),(96,6),(104,5),(128,2),(136,1),(168,0),(216,0)]),([6,16,63,63,1986,30852,233736,1721376],[(96,5),(128,1),(216,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_129 : K_129.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_130 : List (List ℕ × List (ℕ × ℕ)) := [([6,16,63,128,1986,30852,233736,1721376],[(96,3),(216,0)]),([6,16,63,512,1986,30852,233736,1721376],[(128,1)]),([6,16,63,1024,1986,30852,233736,1721376],[(72,0),(96,0),(128,2),(168,0),(216,0)]),([6,16,63,1986,1986,30852,233736,1721376],[(128,1),(216,0)]),([6,16,63,1986,2002,30852,233736,1721376],[(72,5),(76,5),(112,5),(128,1),(232,5)]),([6,16,63,1986,2047,30852,233736,1721376],[(72,5),(128,1),(216,0),(232,5)]),([6,16,63,1986,30852,32710,233736,1721376],[(72,5),(96,1),(216,0)]),([6,16,63,1986,30852,233736,375775],[(72,5),(96,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_130 : K_130.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_131 : List (List ℕ × List (ℕ × ℕ)) := [([6,16,63,1986,30852,233736,375775,1721376],[(72,5),(96,1),(196,3),(204,7),(232,5),(240,1)]),([6,16,63,1986,30852,233736,524288,1721376],[(72,5),(96,1),(184,5),(192,1),(216,0)]),([6,16,63,1986,30852,233736,860688,1721376],[(72,5),(96,1)]),([6,16,63,1986,30852,233736,860688,1721392],[(72,5),(96,1)]),([6,16,63,1986,30852,233736,860688,1722338],[(72,5),(96,1),(184,5)]),([6,16,63,1986,30852,233736,860688,2057776],[(72,5),(96,1)]),([6,16,63,1986,30852,233736,860735,1721376],[(72,5),(96,1),(216,0)]),([6,16,63,1986,30852,233736,862162,1721376],[(56,0),(72,5),(96,1),(168,0),(216,0),(232,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_131 : K_131.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_132 : List (List ℕ × List (ℕ × ℕ)) := [([6,16,63,1986,30852,233736,1236463,1721376],[(72,5),(96,1),(196,3),(204,7),(216,0)]),([6,16,63,1986,30852,233736,1721376],[(72,5),(74,5),(96,1),(97,3),(98,1),(129,7),(168,0),(169,0),(194,3),(202,7)]),([6,16,63,1986,30852,233736,1721376,1721376],[(72,5),(96,1),(168,0)]),([6,16,63,1986,30852,233736,1721376,1721392],[(56,0),(72,5),(96,1),(168,0),(172,0),(216,0)]),([6,16,63,1986,30852,233736,1721376,1721407],[(72,5),(96,1),(168,0)]),([6,16,63,1986,30852,233736,1721376,1722338],[(72,5),(96,1),(168,0),(216,0)]),([6,16,63,1986,30852,233736,1721376,1863415],[(72,5),(96,1),(168,0)]),([6,16,63,1986,30852,233736,1721376,2057776],[(56,0),(72,5),(96,1),(168,0),(216,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_132 : K_132.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_133 : List (List ℕ × List (ℕ × ℕ)) := [([6,16,63,1986,30852,233736,1721376,2097088],[(72,5),(96,1),(168,0),(216,0)]),([6,16,63,1986,30852,233736,1721376,2097135],[(72,5),(96,1),(168,0)]),([6,16,63,1986,30852,233736,1721392],[(2,0),(56,0),(57,0),(72,5),(74,5),(77,0),(96,1),(97,3),(98,1),(101,0),(129,7),(133,0),(168,0),(169,0),(194,3),(202,7)]),([6,16,63,1986,30852,233736,1722338],[(72,5),(74,5),(82,5),(96,1),(97,3),(98,1),(129,7),(168,0),(169,0),(202,1)]),([6,16,63,1986,30852,233736,2057776],[(2,0),(72,5),(74,5),(96,1),(97,3),(98,1),(129,7),(194,3),(202,7)]),([6,16,63,1986,30852,233752,860688,1721376],[(72,3)]),([6,16,63,1986,30852,233752,1721376],[(72,3),(74,3),(97,3),(194,3)]),([6,16,63,1986,30852,1721376,1824040],[(72,3),(128,131339),(168,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_133 : K_133.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_134 : List (List ℕ × List (ℕ × ℕ)) := [([6,16,63,1986,30852,1721376,1863415],[(72,3),(128,0)]),([6,16,1986,30852,233736,1721376,2097088],[(56,5),(72,1),(128,0)]),([6,18,63,1986,30852,233736,860688,1721376],[(72,5),(96,1),(168,0)]),([6,18,63,1986,30852,233736,862162,1721376],[(56,0),(72,5),(96,1),(168,0),(216,0)]),([6,18,63,1986,30852,233736,1721376],[(72,5),(96,1),(97,3),(98,1),(129,7),(168,0),(169,0),(182,0),(202,1)]),([6,31,63,1986,30852,233736,860688],[]),([6,31,63,1986,30852,233736,860688,1721376],[(228,0)]),([6,48,63,1986,30852,233736],[(10,5),(11,5),(13,3),(14,1),(15,1),(17,7),(72,5),(74,5),(96,1),(97,3),(98,1),(99,3),(107,3),(111,3),(129,7),(131,7),(139,7),(143,7),(147,1),(151,1),(155,5),(159,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_134 : K_134.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_135 : List (List ℕ × List (ℕ × ℕ)) := [([6,48,63,1986,30852,233736,860688],[(22,0),(72,5),(74,5),(96,1),(97,3),(98,1),(129,7),(194,3),(198,3),(202,7),(206,7)]),([6,48,63,1986,30852,233736,860688,1721376],[(72,5),(96,1),(168,0),(220,0)]),([6,48,63,1986,30852,233736,860688,2057776],[(72,5),(96,1)]),([6,48,63,1986,30852,233736,2057776],[(72,5),(74,5),(96,1),(97,3),(98,1),(129,7),(194,3),(198,3),(202,7),(206,7)]),([6,55,63,1986,30852,233736,860688,1721376],[(220,0)]),([6,63,63,1986,30852,233736,860688,1721376],[(220,0)]),([6,63,63,1986,30852,233736,860688,1722338],[(72,5),(184,5),(220,0)]),([6,63,63,1986,30852,233736,860688,2057776],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_135 : K_135.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_136 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,63,1986,30852,233736,2057776],[(97,3),(101,3),(129,7),(133,7),(194,3),(202,7)]),([6,63,128,1986,30852,233736,860688,1721376],[(176,0)]),([6,63,128,1986,30852,233736,860688,1721504],[]),([6,63,128,1986,30852,233736,860688,1722338],[(184,3)]),([6,63,128,1986,30852,233736,860688,1824040],[(80,7),(104,7),(224,7)]),([6,63,128,1986,30852,233736,860688,2057776],[]),([6,63,128,1986,30852,233736,2057776],[(6,7),(105,3),(113,3),(137,7),(194,3)]),([6,63,128,1986,30852,233864,860688,1721376],[(176,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_136 : K_136.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_137 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,128,1986,32710,233736,860688,1721376],[(136,1),(184,0)]),([6,63,128,32710,233736,860688,1721376],[(104,7),(105,7),(138,0),(146,0),(154,0),(174,0),(201,0)]),([6,63,130,1986,30852,233736,860688,1721376],[(104,1),(176,0)]),([6,63,191,1986,30852,233736,860688,1721376],[(220,0),(228,0)]),([6,63,384,1986,30852,233736,860688,1721376],[(104,1),(112,1),(176,0),(184,0)]),([6,63,512,1986,30852,233736,860688,1721376],[]),([6,63,512,1986,30852,233736,860688,1721888],[]),([6,63,512,1986,30852,233736,860688,1722338],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_137 : K_137.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_138 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,512,1986,30852,233736,860688,1735844],[(80,3),(104,1),(176,3),(192,1),(224,3)]),([6,63,512,1986,30852,233736,860688,2057776],[]),([6,63,512,1986,30852,233736,862162,1721376],[(80,0),(176,0),(224,0)]),([6,63,512,1986,30852,233736,883348,1721376],[(80,4),(176,4),(224,0),(240,1)]),([6,63,512,1986,30852,233736,1721376,2057776],[(80,0),(176,0),(224,0)]),([6,63,512,1986,30852,233736,2057776],[(6,6),(56,131114),(104,131306),(105,3),(136,131338),(137,7),(202,1)]),([6,63,514,1986,30852,233736,860688,1721376],[(176,0)]),([6,63,528,1986,2047,30852,233736,1721376],[(80,5),(224,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_138 : K_138.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_139 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,528,1986,30852,233736,860688,1721376],[(80,5)]),([6,63,528,1986,30852,233736,1721376],[(80,5),(105,3),(137,7),(174,0),(176,0),(177,0),(202,1)]),([6,63,575,1986,30852,233736,860688,1721376],[(228,0)]),([6,63,640,1986,30852,233736,860688,1721376],[(176,0)]),([6,63,640,1986,30852,233736,883348,1721376],[(80,4),(176,4),(224,0)]),([6,63,962,1986,30852,233736,860688,1721376],[(176,0)]),([6,63,962,30852,233736,375775,860688],[]),([6,63,962,30852,233736,375775,860688,1721376],[(156,1),(224,5),(232,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_139 : K_139.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_140 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,962,30852,233736,860688,1721376],[(154,1),(174,0),(194,1)]),([6,63,1536,1986,30852,233736,860688,1721376],[(176,0)]),([6,63,1536,1986,30852,233736,860688,2057776],[]),([6,63,1536,1986,30852,233736,2057776],[(6,5),(56,131114),(104,131306),(105,3),(136,131338),(137,7),(202,1)]),([6,63,1730,1986,30852,233736,860688,1721376],[(176,0)]),([6,63,1984,1986,30852,233736,860688,1721376],[(176,0),(184,0)]),([6,63,1986,1986,30852,233736,860688,1721376],[(176,0)]),([6,63,1986,1986,30852,233736,860688,1722338],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_140 : K_140.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_141 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,1986,30852,233736,860688,1735844],[(64,3),(68,3),(192,1)]),([6,63,1986,1986,30852,233736,860688,2057776],[]),([6,63,1986,1986,30852,233736,2057776],[(6,5),(137,1),(141,1),(202,1)]),([6,63,1986,1990,30852,233736,860688,1721376],[(80,5),(176,6),(184,0),(224,5)]),([6,63,1986,2002,30852,233736,860688,1721376],[(80,5),(176,5),(184,0),(224,5)]),([6,63,1986,2002,30852,233736,1721376],[(6,5),(58,5),(80,5),(81,5),(105,5),(109,3),(137,9),(141,7),(145,1),(174,0),(176,5),(177,5),(181,0),(184,0),(185,0),(202,1)]),([6,63,1986,2047,30852,233736,860688,1721376],[(176,6),(224,5),(236,0)]),([6,63,1986,2047,30852,233736,860688,1722338],[(80,5),(176,5),(224,5),(236,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_141 : K_141.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_142 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,2047,30852,233736,860688,1735844],[(76,3),(84,3),(96,1),(176,6),(192,1),(224,5),(236,0)]),([6,63,1986,2047,30852,233736,860688,2057776],[(176,5),(224,5)]),([6,63,1986,2047,30852,233736,2057776],[(10,5),(105,5),(117,3),(129,1),(137,9),(145,1),(149,7),(176,5),(177,5),(202,1)]),([6,63,1986,6082,30852,233736,860688,1721376],[(80,5),(176,6),(184,0),(224,5)]),([6,63,1986,8704,30852,233736,860688,1721376],[]),([6,63,1986,10178,30852,233736,860688,1721376],[(184,0),(224,5)]),([6,63,1986,30852,32710,233736,860688,1721376],[(192,0)]),([6,63,1986,30852,32710,233736,860688,1722338],[(176,5),(192,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_142 : K_142.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_143 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,32710,233736,860688,1736678],[]),([6,63,1986,30852,32710,233736,860688,1824040],[(108,7),(116,7),(156,7),(192,8)]),([6,63,1986,30852,32710,233736,860688,2057776],[]),([6,63,1986,30852,32710,233736,2057776],[(14,7),(58,5),(74,1),(85,3),(118,3),(137,5),(145,1),(157,7),(186,3)]),([6,63,1986,30852,32767,233736,860688,1721376],[(156,7),(244,0)]),([6,63,1986,30852,39375,233736],[(6,5),(10,1),(114,3),(117,3),(153,7),(158,7)]),([6,63,1986,30852,39375,233736,860688],[(176,242849),(184,238753),(200,271521)]),([6,63,1986,30852,39375,233736,860688,1721376],[(116,3),(156,7),(176,6),(184,2),(200,0),(224,5),(232,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_143 : K_143.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_144 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,39375,233736,860688,2057776],[(116,3),(156,7),(176,5),(184,1),(224,5),(232,1)]),([6,63,1986,30852,39375,233736,2057776],[(114,3),(116,3),(117,3),(118,3),(153,7),(156,7),(157,7),(158,7),(176,5),(177,5),(184,1),(185,1),(186,3),(202,7)]),([6,63,1986,30852,233736,262094,860688,1721376],[(200,0)]),([6,63,1986,30852,233736,273111,860688],[(18,7)]),([6,63,1986,30852,233736,273111,860688,1721376],[]),([6,63,1986,30852,233736,273111,860688,1824040],[]),([6,63,1986,30852,233736,336400,375775],[]),([6,63,1986,30852,233736,336400,375775,1721376],[(188,3),(196,7),(224,5),(232,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_144 : K_144.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_145 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,336400,860688,1721376],[]),([6,63,1986,30852,233736,336400,1721376],[(146,3),(154,7),(174,0),(186,3),(194,7),(201,0)]),([6,63,1986,30852,233736,375744,860688,1721376],[(200,0),(224,5),(232,1)]),([6,63,1986,30852,233736,375775,860688],[]),([6,63,1986,30852,233736,375775,860688,1721376],[(148,3),(156,7),(224,5),(232,1)]),([6,63,1986,30852,233736,375775,860688,1722338],[(136,5),(148,3),(156,7),(176,5),(224,5)]),([6,63,1986,30852,233736,375775,860688,2057776],[(148,3),(156,7)]),([6,63,1986,30852,233736,375775,862162],[(18,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_145 : K_145.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_146 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,375775,862162,1721376],[(148,3),(156,7),(224,5),(232,1)]),([6,63,1986,30852,233736,375775,1236463],[]),([6,63,1986,30852,233736,375775,1721376,2057776],[(148,3),(156,7),(176,5),(184,1)]),([6,63,1986,30852,233736,375775,2057776],[(18,0),(146,3),(148,3),(149,3),(150,3),(154,7),(156,7),(157,7),(158,7),(186,3),(194,7)]),([6,63,1986,30852,233736,375807,860688,1721376],[(148,3),(156,7),(224,5),(232,1),(252,0)]),([6,63,1986,30852,233736,376799,860688],[(18,6)]),([6,63,1986,30852,233736,376799,860688,1721376],[(148,3),(156,7),(224,5)]),([6,63,1986,30852,233736,524288,860688,1721376],[(136,5),(144,1)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_146 : K_146.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_147 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,524288,860688,1722338],[(136,5),(144,1),(176,5)]),([6,63,1986,30852,233736,524288,860688,2057776],[(136,5),(144,1)]),([6,63,1986,30852,233736,524288,2057776],[(136,5),(137,5),(144,1),(145,1),(146,3),(154,7),(186,3),(194,7)]),([6,63,1986,30852,233736,524304,860688,1721376],[(136,5),(144,1)]),([6,63,1986,30852,233736,524304,1721376],[(136,5),(137,5),(144,1),(145,1),(146,3),(154,7),(174,0),(186,3),(194,7),(200,0),(201,0)]),([6,63,1986,30852,233736,524304,1721376,1721407],[(136,5),(144,1),(200,0)]),([6,63,1986,30852,233736,524351,860688,1721376],[(252,0)]),([6,63,1986,30852,233736,524800,860688,1721376],[(136,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_147 : K_147.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_148 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,524800,860688,1722338],[(136,5),(176,5)]),([6,63,1986,30852,233736,526274,860688,1721376],[(136,5),(176,6),(200,0),(224,5)]),([6,63,1986,30852,233736,795152,860688,1721376],[]),([6,63,1986,30852,233736,795152,1721376],[(146,3),(154,8),(174,0),(186,3),(200,0),(201,0)]),([6,63,1986,30852,233736,795152,1721376,1863415],[(200,0)]),([6,63,1986,30852,233736,860672,860688,1721376],[]),([6,63,1986,30852,233736,860688,860688,1721376],[]),([6,63,1986,30852,233736,860688,860688,1722338],[(136,5)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_148 : K_148.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_149 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,860688,860688,2057776],[]),([6,63,1986,30852,233736,860688,860690,1721376],[(200,0)]),([6,63,1986,30852,233736,860688,860720],[(18,0),(136,164078),(144,164074),(146,3),(150,3),(152,164106),(154,7),(158,7),(176,5),(184,1),(186,3),(194,7)]),([6,63,1986,30852,233736,860688,860720,1721376],[(200,0),(260,0)]),([6,63,1986,30852,233736,860688,860735,1721376],[(260,0)]),([6,63,1986,30852,233736,860688,860735,1722338],[(136,5),(176,5)]),([6,63,1986,30852,233736,860688,860735,2057776],[]),([6,63,1986,30852,233736,860688,860816,1721376],[(200,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_149 : K_149.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_150 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,860688,861712,1721376],[(200,0)]),([6,63,1986,30852,233736,860688,862162,1721376],[(200,0),(224,5)]),([6,63,1986,30852,233736,860688,862162,1722338],[(136,5),(176,5),(224,5)]),([6,63,1986,30852,233736,860688,862162,1735844],[(144,1),(180,3),(204,3)]),([6,63,1986,30852,233736,860688,862162,2057776],[]),([6,63,1986,30852,233736,860688,862162,2058226],[]),([6,63,1986,30852,233736,860688,862207,1721376],[(224,5),(260,0)]),([6,63,1986,30852,233736,860688,884694,1721376],[(200,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_150 : K_150.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_151 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,860688,900063],[(22,0)]),([6,63,1986,30852,233736,860688,900063,1721376],[(188,3),(196,7),(224,5),(232,1)]),([6,63,1986,30852,233736,860688,1572863,1721376],[(260,0)]),([6,63,1986,30852,233736,860688,1721376],[(138,0),(146,4),(154,8),(174,0),(186,3),(194,7),(201,0)]),([6,63,1986,30852,233736,860688,1721376,1836659],[(260,0)]),([6,63,1986,30852,233736,860688,1721376,1863360],[(248,0)]),([6,63,1986,30852,233736,860688,1721376,1863415],[(260,0)]),([6,63,1986,30852,233736,860688,1721376,1863423],[(260,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_151 : K_151.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_152 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,860688,1721376,1863671],[(260,0)]),([6,63,1986,30852,233736,860688,1721376,1928951],[(260,0)]),([6,63,1986,30852,233736,860688,1721376,1966079],[(244,7),(260,0)]),([6,63,1986,30852,233736,860688,1721376,2057776],[(248,0)]),([6,63,1986,30852,233736,860688,1721376,2057791],[]),([6,63,1986,30852,233736,860688,1721376,2058226],[(248,0)]),([6,63,1986,30852,233736,860688,1721376,2093055],[]),([6,63,1986,30852,233736,860688,1721376,2097088],[(248,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_152 : K_152.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_153 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,860688,1721376,2097090],[(248,0)]),([6,63,1986,30852,233736,860688,1721376,2097104],[(248,0)]),([6,63,1986,30852,233736,860688,1721376,2097119],[]),([6,63,1986,30852,233736,860688,1721376,2097143],[]),([6,63,1986,30852,233736,860688,1721376,2097151],[]),([6,63,1986,30852,233736,860688,1721378],[(58,5),(138,0),(146,0),(154,2),(174,0),(186,3),(194,7),(201,0)]),([6,63,1986,30852,233736,860688,1721392],[(18,0),(130,0),(138,0),(146,4),(150,3),(154,8),(158,7),(186,3),(194,7),(201,0)]),([6,63,1986,30852,233736,860688,1721407,1722338],[(136,6),(248,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_153 : K_153.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_154 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,860688,1721407,2057776],[(248,0)]),([6,63,1986,30852,233736,860688,1721504],[(138,0),(146,4),(154,0),(174,0),(186,3),(194,7),(201,0)]),([6,63,1986,30852,233736,860688,1721888],[(138,0),(146,0),(154,2),(174,0),(186,3),(194,7),(201,0)]),([6,63,1986,30852,233736,860688,1722338],[(58,5),(136,5),(137,5),(146,0),(154,2),(174,0),(194,1),(201,0)]),([6,63,1986,30852,233736,860688,1722338,1722338],[(136,6),(200,0)]),([6,63,1986,30852,233736,860688,1722338,1722367],[(136,6),(200,0)]),([6,63,1986,30852,233736,860688,1722338,1735844],[(136,6),(144,2),(180,3),(200,4),(248,0)]),([6,63,1986,30852,233736,860688,1722338,1736678],[(136,6),(200,0),(248,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_154 : K_154.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_155 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,860688,1722338,1863415],[(136,5),(260,0)]),([6,63,1986,30852,233736,860688,1722338,2057776],[(136,5),(248,0)]),([6,63,1986,30852,233736,860688,1722338,2058226],[(136,5),(248,0)]),([6,63,1986,30852,233736,860688,1722338,2095165],[(136,5),(200,5),(252,5),(260,6)]),([6,63,1986,30852,233736,860688,1722338,2097088],[(136,5),(248,0)]),([6,63,1986,30852,233736,860688,1736678],[(58,5),(74,1),(146,3),(154,7),(174,0),(201,0)]),([6,63,1986,30852,233736,860688,1863415,2057776],[]),([6,63,1986,30852,233736,860688,2057776],[(18,0),(136,164078),(144,164074),(146,3),(150,3),(152,164106),(154,7),(158,7),(186,3),(194,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_155 : K_155.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_156 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,860688,2057776,2057776],[]),([6,63,1986,30852,233736,860688,2057776,2057791],[]),([6,63,1986,30852,233736,860688,2057776,2058226],[]),([6,63,1986,30852,233736,860688,2057776,2097088],[]),([6,63,1986,30852,233736,860688,2058226],[(18,0),(58,5),(146,3),(150,3),(154,7),(158,7),(194,1)]),([6,63,1986,30852,233736,860688,2097088,2097120],[]),([6,63,1986,30852,233736,860688,2097119],[(22,0)]),([6,63,1986,30852,233736,860688,2097120],[(146,3),(154,7),(174,0),(186,3),(194,7),(201,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_156 : K_156.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_157 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,860720],[(6,5),(7,5),(9,3),(10,1),(11,1),(13,7),(18,0),(19,0),(75,3),(79,3),(99,7),(103,7),(107,1),(111,1),(115,5),(119,5),(137,5),(145,1),(146,3),(147,3),(151,3),(154,7),(155,7),(159,7)]),([6,63,1986,30852,233736,860735,2057776],[(18,0),(146,3),(150,3),(154,7),(158,7),(186,3),(194,7)]),([6,63,1986,30852,233736,862162,1722338],[(6,5),(58,5),(81,5),(85,3),(105,9),(109,7),(136,5),(137,5),(146,0),(154,2),(174,0),(176,5),(177,6),(194,1),(201,0)]),([6,63,1986,30852,233736,862162,1735844],[(58,6),(74,1),(146,4),(154,4),(174,4),(201,4)]),([6,63,1986,30852,233736,862162,2057776],[(18,6),(58,5),(136,164078),(150,3),(154,1),(158,7),(194,1)]),([6,63,1986,30852,233736,862162,2058226],[(18,6),(58,5),(150,3),(154,1),(158,7),(194,1)]),([6,63,1986,30852,233736,1863415,2057776],[(18,7),(146,3),(150,3),(186,3)]),([6,63,1986,30852,233736,2057776],[(6,5),(7,5),(9,3),(10,1),(11,1),(13,7),(75,3),(79,3),(99,7),(103,7),(107,1),(111,1),(115,5),(119,5),(137,5),(145,1),(146,3),(147,3),(151,3),(154,7),(155,7),(159,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_157 : K_157.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_158 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233736,2057776,2057776],[(136,5),(144,1),(146,3),(150,3),(154,7),(158,7)]),([6,63,1986,30852,233736,2057776,2057791],[(136,5),(144,1),(146,3),(154,7),(186,3),(190,3),(194,7),(198,7)]),([6,63,1986,30852,233736,2057776,2058226],[(22,5),(58,5),(150,3),(154,1),(158,7),(176,5),(190,3),(194,1),(198,7)]),([6,63,1986,30852,233736,2057776,2097088],[(146,3),(154,7),(186,3),(190,3),(194,7),(198,7)]),([6,63,1986,30852,233736,2058226],[(6,5),(7,5),(9,3),(10,1),(11,1),(13,7),(18,5),(19,5),(58,5),(75,3),(79,3),(99,7),(103,7),(107,1),(111,1),(115,5),(119,5),(151,3),(154,1),(155,1),(159,7)]),([6,63,1986,30852,233738,860688,1721376],[(58,5),(138,0),(146,0),(154,0),(174,0),(201,0)]),([6,63,1986,30852,233752,860688,1721376],[(146,3),(150,3),(158,7),(174,0),(186,3)]),([6,63,1986,30852,233752,1721376],[(6,5),(7,3),(9,3),(10,1),(14,0),(75,3),(79,3),(103,7),(111,1),(115,3),(119,5),(134,0),(135,0),(137,5),(143,0),(145,1),(146,3),(147,3),(151,4),(153,0),(159,8)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_158 : K_158.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_159 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,233791,235466,860688,1721376],[(56,3),(108,1),(200,0)]),([6,63,1986,30852,233791,860688,1028888,1721376],[(200,0)]),([6,63,1986,30852,233791,860688,1824040],[(73,3),(146,3),(158,7),(174,8),(186,3),(196,0),(197,0),(198,0),(201,0)]),([6,63,1986,30852,233864,860688,1721376],[(80,7),(81,5),(82,1),(138,0),(146,4),(154,0),(174,0),(186,3),(201,0)]),([6,63,1986,30852,235466,260492,860688,1721376],[(116,3)]),([6,63,1986,30852,273111,860688,1721376],[(200,131339)]),([6,63,1986,30852,375775,860688,1028888],[]),([6,63,1986,30852,375775,860688,1721376,1824040],[(176,3),(244,7)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_159 : K_159.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_160 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,375775,860688,1824040],[(117,3),(146,3),(197,7)]),([6,63,1986,30852,375775,860688,1863415],[]),([6,63,1986,30852,524288,758024,860688,1721376],[]),([6,63,1986,30852,758024,860688,1721376],[(138,0),(146,4),(154,0),(174,0),(186,3),(201,0)]),([6,63,1986,30852,795152,1721376,1863415],[(152,0)]),([6,63,1986,30852,860688,1028888,1721376],[(14,0),(192,164106)]),([6,63,1986,30852,860688,1028888,1721376,1824040],[(152,0)]),([6,63,1986,30852,860688,1028888,1722338],[(14,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_160 : K_160.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_161 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,860688,1028888,1824040],[(14,0),(114,3),(118,3)]),([6,63,1986,30852,860688,1028888,2057776],[(14,0),(104,164106),(112,164238),(152,164106),(192,164106)]),([6,63,1986,30852,860688,1028888,2094904],[(14,0)]),([6,63,1986,30852,860688,1721376,1863415],[]),([6,63,1986,30852,860688,1721376,1928951],[(22,8)]),([6,63,1986,30852,860688,1721376,2094904],[]),([6,63,1986,30852,860688,1721407,1824040],[]),([6,63,1986,30852,860688,1722338,1863415],[(104,3)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_161 : K_161.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_162 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,30852,860688,1824040,1863415],[(22,7)]),([6,63,1986,30852,860688,1824040,2057776],[(104,3),(192,131339)]),([6,63,1986,30852,860688,1863415,2057776],[(104,164078),(112,164074)]),([6,63,1986,30852,860688,2057776,2094904],[(104,3)]),([6,63,1986,30852,1028888,1824040],[(6,5),(7,3),(9,3),(10,1),(14,0),(15,0),(17,0),(75,3),(79,3),(103,7),(111,1),(115,3),(119,5),(131,0),(135,8),(139,0),(143,2),(147,4),(151,6)]),([6,63,1986,30852,1028888,2057776],[(0,164106),(2,164106),(4,164106),(6,164106),(8,164106),(10,164106),(12,164106),(14,164106),(16,164106),(18,271521),(137,5),(145,1)]),([6,63,1986,30852,1863415,2057776],[(6,3),(137,3),(146,3)]),([6,63,1986,30852,2057776,2094904],[(6,5),(10,1),(105,3)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_162 : K_162.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_163 : List (List ℕ × List (ℕ × ℕ)) := [([6,63,1986,860688,883348,1028888,1721376],[(10,0),(80,98538),(184,164238)]),([6,63,1986,860688,883348,1721376,1824040],[]),([6,63,1986,860688,883348,1721376,1863415],[(144,164074)]),([6,63,1986,860688,1721376,1863415,2066299],[]),([6,128,191,1986,30852,233736,860688,1721376],[(168,0)]),([6,191,1986,30852,233736,860688,1721376],[(81,3),(138,0),(146,4),(154,0),(174,0),(186,3),(201,0)]),([6,1986,2047,30852,30911,233736,860688,1721376],[(72,7),(168,6),(184,2),(216,5),(232,1)]),([6,1986,30852,233736,375775,860688,2097088],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_163 : K_163.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_164 : List (List ℕ × List (ℕ × ℕ)) := [([6,1986,30852,233736,860688,1721376,2097088],[]),([6,1986,30852,233736,860688,1722338,2097088],[(96,5)]),([6,1986,30852,233736,860688,2057776,2097088],[(96,164078),(104,164074),(112,164106)]),([6,1986,30852,233736,860688,2097088,2097120],[(152,163987)]),([6,1986,30852,233736,2057776,2097088],[(2,5),(6,1),(97,5),(105,1),(106,3),(114,7)]),([6,1986,30852,860688,1028888,1721376,2097088],[(144,164106)]),([6,1986,30852,860688,1721376,1863415,2097088],[]),([7,2,63,1986,30852,233736,860688,1721376],[(2,5),(96,1),(97,3),(98,1),(129,7),(168,0),(170,0),(186,0),(194,0),(202,2),(217,0),(230,0),(250,1),(257,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_164 : K_164.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_165 : List (List ℕ × List (ℕ × ℕ)) := [([7,16,63,1986,30852,233736,860688,1721376],[(2,0),(72,5),(74,5),(96,1),(97,3),(98,1),(129,7),(194,3),(198,3),(202,7),(206,7),(217,0),(242,3),(250,7)]),([7,16,63,1986,30852,233736,1721376],[(2,0),(10,5),(11,5),(13,3),(14,1),(15,1),(17,7),(72,5),(74,5),(96,1),(97,3),(98,1),(99,3),(107,3),(111,3),(129,7),(131,7),(139,7),(143,7),(147,1),(151,1),(155,5),(159,5),(168,0),(169,0),(183,0),(185,5),(193,1),(194,3),(195,3),(199,3),(202,7),(203,7),(207,7)]),([7,63,63,1986,30852,233736,860688,1721376],[(97,3),(101,3),(129,7),(133,7),(186,0),(194,4),(202,8),(217,0),(220,0),(221,0),(222,0),(242,3),(250,7),(257,0)]),([7,63,128,1986,30852,233736,860688,1721376],[(6,7),(105,3),(113,3),(137,7),(176,0),(178,0),(186,0),(194,4),(202,0),(222,0),(225,0),(242,3),(257,0)]),([7,63,512,1986,30852,233736,860688,1721376],[(6,6),(56,131114),(104,131306),(105,3),(136,131338),(137,7),(202,1),(222,0),(225,0),(250,1)]),([7,63,1986,1986,30852,233736,860688,1721376],[(6,5),(137,1),(141,1),(176,0),(178,0),(194,0),(202,2),(222,0),(225,0),(229,0),(250,1),(257,0)]),([7,63,1986,2047,30852,233736,860688,1721376],[(10,5),(105,5),(117,3),(129,1),(137,9),(145,1),(149,7),(176,6),(177,5),(178,0),(194,0),(202,2),(222,0),(224,5),(225,6),(233,0),(236,0),(237,0),(238,0),(250,1),(257,0)]),([7,63,1986,30852,32710,233736,860688,1721376],[(14,7),(58,5),(74,1),(85,3),(118,3),(137,5),(145,1),(157,7),(178,0),(186,4),(192,0),(194,0),(202,0),(222,0),(234,3),(241,0),(245,0),(257,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_165 : K_165.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_166 : List (List ℕ × List (ℕ × ℕ)) := [([7,63,1986,30852,233736,375775,860688],[(6,5),(10,1),(146,3),(149,3),(154,7),(157,7),(177,5),(185,1),(186,3),(194,7)]),([7,63,1986,30852,233736,375775,860688,1721376],[(18,0),(146,3),(148,3),(149,3),(150,3),(154,7),(156,7),(157,7),(158,7),(186,3),(194,7),(222,0),(224,5),(225,5),(232,1),(233,1),(234,3),(242,7)]),([7,63,1986,30852,233736,524288,860688,1721376],[(128,163988),(136,5),(137,5),(144,1),(145,1),(146,3),(154,7),(178,0),(186,4),(194,8),(222,0),(234,3),(242,7),(249,0),(257,0)]),([7,63,1986,30852,233736,860688,860688,1721376],[(18,0),(136,5),(144,1),(146,3),(150,3),(154,7),(158,7),(222,0),(234,3),(242,7)]),([7,63,1986,30852,233736,860688,860735,1721376],[(22,0),(136,6),(138,0),(144,2),(146,4),(152,0),(154,8),(186,3),(190,3),(194,7),(198,7),(222,0),(234,3),(242,7),(249,0),(260,0),(261,0),(262,0)]),([7,63,1986,30852,233736,860688,862162,1721376],[(18,0),(22,6),(58,5),(130,0),(138,0),(146,0),(150,3),(154,2),(158,7),(176,5),(190,3),(194,1),(198,7),(200,0),(201,0),(222,0),(224,5),(225,5),(242,1),(249,0),(253,0),(261,0)]),([7,63,1986,30852,233736,860688,1721376],[(6,5),(7,5),(9,3),(10,1),(11,1),(13,7),(18,0),(19,0),(21,0),(75,3),(79,3),(99,7),(103,7),(107,1),(111,1),(115,5),(119,5),(137,5),(138,0),(145,1),(146,4),(147,3),(151,3),(154,8),(155,7),(159,7),(171,0),(174,0),(175,0),(177,6),(179,0),(183,0),(185,2),(186,3),(187,4),(191,4),(193,0),(194,7),(195,8),(199,8),(201,0)]),([7,63,1986,30852,233736,860688,1721376,1863415],[(26,7),(138,0),(146,4),(152,0),(154,8),(174,0),(186,3),(194,7),(201,0),(234,3),(238,3),(258,0),(260,0),(261,0),(262,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_166 : K_166.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_167 : List (List ℕ × List (ℕ × ℕ)) := [([7,63,1986,30852,233736,860688,1721376,2057776],[(18,0),(130,0),(136,6),(138,0),(144,2),(146,4),(150,3),(152,0),(154,8),(158,7),(174,0),(176,5),(182,0),(184,1),(186,3),(190,4),(194,7),(198,8),(201,0),(205,0),(224,5),(232,1),(234,3),(238,3),(242,7),(246,7),(248,0),(249,0),(262,0)]),([7,63,1986,30852,233736,860688,1721376,2097088],[(138,0),(146,4),(154,8),(172,0),(174,0),(186,3),(194,7),(201,0),(234,3),(238,3),(242,7),(246,7),(248,0),(249,0),(258,0),(262,0)]),([7,63,1986,30852,233736,860688,1722338],[(6,5),(9,3),(10,1),(11,1),(13,7),(18,0),(19,0),(22,5),(23,5),(58,5),(75,3),(79,3),(99,7),(103,7),(107,1),(111,1),(115,5),(119,5),(136,5),(137,5),(145,1),(146,0),(147,3),(151,3),(154,2),(155,7),(159,7),(174,0),(175,0),(191,4),(194,1),(195,1),(199,8),(201,0)]),([7,63,1986,30852,233736,860688,2057776],[(6,5),(7,5),(9,3),(10,1),(11,1),(13,7),(18,0),(19,0),(75,3),(79,3),(99,7),(103,7),(107,1),(111,1),(115,5),(119,5),(136,5),(137,5),(144,1),(145,1),(146,3),(147,3),(150,3),(151,3),(154,7),(155,7),(158,7),(159,7),(177,5),(185,1),(186,3),(187,3),(191,3),(194,7),(195,7),(199,7)]),([7,63,1986,30852,233736,2057776],[(6,5),(7,5),(9,3),(10,1),(11,1),(13,7),(75,3),(79,3),(99,7),(103,7),(107,1),(111,1),(115,5),(119,5),(137,5),(145,1),(146,3),(147,3),(151,3),(154,7),(155,7),(159,7)]),([7,63,1986,30852,860688,1028888,1721376],[(6,5),(10,1),(14,0),(15,0),(18,0),(98,0),(105,3),(174,0),(177,4),(185,0),(186,3),(193,0)]),([7,63,1986,30852,860688,1721376,1863415],[(6,3),(14,0),(105,3),(106,0),(114,4),(134,0),(137,4),(145,0),(146,3),(153,0),(202,0),(205,0)]),([7,1986,30852,233736,860688,1721376,2097088],[(2,5),(6,1),(14,0),(97,5),(98,0),(105,1),(106,4),(114,8),(129,6),(137,2),(138,3),(145,0),(146,7),(153,0),(193,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_167 : K_167.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_168 : List (List ℕ × List (ℕ × ℕ)) := [([8,63,1986,30852,233736,860688,1721376],[(6,5),(7,5),(9,3),(10,1),(11,1),(13,7),(18,0),(19,0),(21,0),(75,3),(79,3),(99,7),(103,7),(107,1),(111,1),(115,5),(119,5),(137,5),(138,0),(145,1),(146,4),(147,3),(151,3),(154,8),(155,7),(159,7),(171,0),(174,0),(175,0),(177,6),(179,0),(183,0),(185,2),(186,3),(187,4),(191,4),(193,0),(194,7),(195,8),(199,8),(201,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_168 : K_168.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((((((((K_0 ++ K_1) ++ (K_2 ++ (K_3 ++ K_4))) ++ ((K_5 ++ K_6) ++ (K_7 ++ (K_8 ++ K_9)))) ++ (((K_10 ++ K_11) ++ (K_12 ++ (K_13 ++ K_14))) ++ ((K_15 ++ (K_16 ++ K_17)) ++ (K_18 ++ (K_19 ++ K_20))))) ++ ((((K_21 ++ K_22) ++ (K_23 ++ (K_24 ++ K_25))) ++ ((K_26 ++ K_27) ++ (K_28 ++ (K_29 ++ K_30)))) ++ (((K_31 ++ K_32) ++ (K_33 ++ (K_34 ++ K_35))) ++ ((K_36 ++ (K_37 ++ K_38)) ++ (K_39 ++ (K_40 ++ K_41)))))) ++ (((((K_42 ++ K_43) ++ (K_44 ++ (K_45 ++ K_46))) ++ ((K_47 ++ K_48) ++ (K_49 ++ (K_50 ++ K_51)))) ++ (((K_52 ++ K_53) ++ (K_54 ++ (K_55 ++ K_56))) ++ ((K_57 ++ (K_58 ++ K_59)) ++ (K_60 ++ (K_61 ++ K_62))))) ++ ((((K_63 ++ K_64) ++ (K_65 ++ (K_66 ++ K_67))) ++ ((K_68 ++ K_69) ++ (K_70 ++ (K_71 ++ K_72)))) ++ (((K_73 ++ K_74) ++ (K_75 ++ (K_76 ++ K_77))) ++ ((K_78 ++ (K_79 ++ K_80)) ++ (K_81 ++ (K_82 ++ K_83))))))) ++ ((((((K_84 ++ K_85) ++ (K_86 ++ (K_87 ++ K_88))) ++ ((K_89 ++ K_90) ++ (K_91 ++ (K_92 ++ K_93)))) ++ (((K_94 ++ K_95) ++ (K_96 ++ (K_97 ++ K_98))) ++ ((K_99 ++ (K_100 ++ K_101)) ++ (K_102 ++ (K_103 ++ K_104))))) ++ ((((K_105 ++ K_106) ++ (K_107 ++ (K_108 ++ K_109))) ++ ((K_110 ++ K_111) ++ (K_112 ++ (K_113 ++ K_114)))) ++ (((K_115 ++ K_116) ++ (K_117 ++ (K_118 ++ K_119))) ++ ((K_120 ++ (K_121 ++ K_122)) ++ (K_123 ++ (K_124 ++ K_125)))))) ++ (((((K_126 ++ K_127) ++ (K_128 ++ (K_129 ++ K_130))) ++ ((K_131 ++ K_132) ++ (K_133 ++ (K_134 ++ K_135)))) ++ (((K_136 ++ K_137) ++ (K_138 ++ (K_139 ++ K_140))) ++ ((K_141 ++ (K_142 ++ K_143)) ++ (K_144 ++ (K_145 ++ K_146))))) ++ ((((K_147 ++ K_148) ++ (K_149 ++ (K_150 ++ K_151))) ++ ((K_152 ++ (K_153 ++ K_154)) ++ (K_155 ++ (K_156 ++ K_157)))) ++ (((K_158 ++ K_159) ++ (K_160 ++ (K_161 ++ K_162))) ++ ((K_163 ++ (K_164 ++ K_165)) ++ (K_166 ++ (K_167 ++ K_168))))))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app (all_app (all_app c_0 c_1) (all_app c_2 (all_app c_3 c_4))) (all_app (all_app c_5 c_6) (all_app c_7 (all_app c_8 c_9)))) (all_app (all_app (all_app c_10 c_11) (all_app c_12 (all_app c_13 c_14))) (all_app (all_app c_15 (all_app c_16 c_17)) (all_app c_18 (all_app c_19 c_20))))) (all_app (all_app (all_app (all_app c_21 c_22) (all_app c_23 (all_app c_24 c_25))) (all_app (all_app c_26 c_27) (all_app c_28 (all_app c_29 c_30)))) (all_app (all_app (all_app c_31 c_32) (all_app c_33 (all_app c_34 c_35))) (all_app (all_app c_36 (all_app c_37 c_38)) (all_app c_39 (all_app c_40 c_41)))))) (all_app (all_app (all_app (all_app (all_app c_42 c_43) (all_app c_44 (all_app c_45 c_46))) (all_app (all_app c_47 c_48) (all_app c_49 (all_app c_50 c_51)))) (all_app (all_app (all_app c_52 c_53) (all_app c_54 (all_app c_55 c_56))) (all_app (all_app c_57 (all_app c_58 c_59)) (all_app c_60 (all_app c_61 c_62))))) (all_app (all_app (all_app (all_app c_63 c_64) (all_app c_65 (all_app c_66 c_67))) (all_app (all_app c_68 c_69) (all_app c_70 (all_app c_71 c_72)))) (all_app (all_app (all_app c_73 c_74) (all_app c_75 (all_app c_76 c_77))) (all_app (all_app c_78 (all_app c_79 c_80)) (all_app c_81 (all_app c_82 c_83))))))) (all_app (all_app (all_app (all_app (all_app (all_app c_84 c_85) (all_app c_86 (all_app c_87 c_88))) (all_app (all_app c_89 c_90) (all_app c_91 (all_app c_92 c_93)))) (all_app (all_app (all_app c_94 c_95) (all_app c_96 (all_app c_97 c_98))) (all_app (all_app c_99 (all_app c_100 c_101)) (all_app c_102 (all_app c_103 c_104))))) (all_app (all_app (all_app (all_app c_105 c_106) (all_app c_107 (all_app c_108 c_109))) (all_app (all_app c_110 c_111) (all_app c_112 (all_app c_113 c_114)))) (all_app (all_app (all_app c_115 c_116) (all_app c_117 (all_app c_118 c_119))) (all_app (all_app c_120 (all_app c_121 c_122)) (all_app c_123 (all_app c_124 c_125)))))) (all_app (all_app (all_app (all_app (all_app c_126 c_127) (all_app c_128 (all_app c_129 c_130))) (all_app (all_app c_131 c_132) (all_app c_133 (all_app c_134 c_135)))) (all_app (all_app (all_app c_136 c_137) (all_app c_138 (all_app c_139 c_140))) (all_app (all_app c_141 (all_app c_142 c_143)) (all_app c_144 (all_app c_145 c_146))))) (all_app (all_app (all_app (all_app c_147 c_148) (all_app c_149 (all_app c_150 c_151))) (all_app (all_app c_152 (all_app c_153 c_154)) (all_app c_155 (all_app c_156 c_157)))) (all_app (all_app (all_app c_158 c_159) (all_app c_160 (all_app c_161 c_162))) (all_app (all_app c_163 (all_app c_164 c_165)) (all_app c_166 (all_app c_167 c_168))))))))


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33598 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by

  rintro ⟨C,hfan,hsize,hr⟩
  let f : BFn 6 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 6 × Fin 6) : f (pt 6 (pairCode p)) = reference (pt 6 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 6 (pairCode (i,j)))) = _
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
  have nc : ∃ x y : Fin 6 → Bool, f x ≠ f y := by
    refine ⟨pt 6 (pairCode (0,0)),pt 6 (pairCode (0,4)),?_⟩
    rw [he (0,0),he (0,4)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 8 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end PEqualNP.Outside.L_meta_23548.Lower

theorem PEqualNP.Outside.L_meta_23548 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33598 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := PEqualNP.Outside.L_meta_23548.Lower.lower
