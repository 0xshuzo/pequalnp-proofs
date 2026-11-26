import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19053_Negation

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


def code (k : ℕ) : ℕ := 2 ^ (k / 4) + 2 ^ (4 + k % 4)

def ohPts : List ℕ := List.ofFn fun k : Fin 16 => code k.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ofFn_code : ∀ k : Fin 16, List.ofFn (pt 8 (code k.val)) =
    PEqualNP.Represents.oneEach (Fin.mk (k.val / 4) (by have := k.isLt; omega) : Fin 4)
      (Fin.mk (k.val % 4) (by have := k.isLt; omega) : Fin 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ohPts_length : ohPts.length = 16 := by simp [ohPts]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rep_val (M : ℕ) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) C)
    (k : ℕ) (hk : k < 16) : C.eval (List.ofFn (pt 8 (code k))) = M.testBit k := by
  have h := ofFn_code ⟨k, hk⟩
  simp only at h
  rw [h, hrep]
  show M.testBit (4 * (k / 4) + k % 4) = M.testBit k
  rw [Nat.div_add_mod]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem enc_rep (M : ℕ) (hM : M < 2 ^ 16) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) C) :
    encL (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) ohPts = M := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [encL_testBit]
  by_cases hj : j < 16
  · rw [List.getD_eq_getElem _ _ (by simp [ohPts_length, hj])]
    simp only [ohPts, List.getElem_map, List.getElem_ofFn]
    exact rep_val M C hrep j hj
  · rw [List.getD_eq_default _ _ (by simp [ohPts_length]; omega)]
    symm
    apply Nat.testBit_eq_false_of_lt
    calc M < 2 ^ 16 := hM
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signed_rep_lb (M s one zer : ℕ) (PD PM : List (ℕ × ℕ)) (XS : List ℕ)
    (G : List (List ℕ)) (T : BT)
    (hM : M < 2 ^ 16) (h1 : M.testBit one = true) (h0 : M.testBit zer = false)
    (h1' : one < 16) (h0' : zer < 16)
    (hxs : (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map
      (fun a => encL a ohPts) = XS)
    (hp : prsOK 65535 M PD PM = true) (hG : symOK 65535 M G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK 65535 M PD PM G T x h = true)
    (hi : XS.sublists.all (rootOK 65535 M PD PM G T s) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) C := by
  rintro ⟨C, hfan, hsize, hrep⟩
  have hnc : ∃ a b : Fin 8 → Bool, (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) a ≠
      (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) b := by
    refine ⟨pt 8 (code one), pt 8 (code zer), ?_⟩
    simp only [rep_val M C hrep one h1', rep_val M C hrep zer h0', h1, h0]
    decide
  have hl := lb_cert (fun x : Fin 8 → Bool => C.eval (List.ofFn x)) ohPts 65535 M XS PD PM G T s
    (s + 1) rfl (by rw [ohPts_length]; decide) (enc_rep M hM C hrep) hxs hnc hp hG hT hi s
    ⟨C, hfan, hsize, fun _ => rfl⟩
  omega



def M_ : ℕ := 65535

def Y_ : ℕ := 4702

def XS_ : List ℕ := [15,240,3840,61440,4369,8738,17476,34952]

def PD_ : List (ℕ × ℕ) := [(1,7025),(2,5833),(3,4117),(4,891),(5,716),(6,535),(7,122),(8,76),(9,87),(10,26),(11,28),(12,15),(13,6),(14,2)]

def PM_ : List (ℕ × ℕ) := [(0,4702),(5,4702),(7,4702),(8,4702),(10,4702),(11,4702),(13,4702),(14,4702),(15,4702)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,15,4624,17476,43770] BT.lf) [3,240,526,4369,62532] BT.lf) [3,240,4895,17476,64170] (BT.nd BT.lf [3,240,4895,17476,65262] BT.lf)) [3,240,4895,43690,62532] (BT.nd (BT.nd BT.lf [3,240,4895,61166,62532] BT.lf) [3,240,7967,17476,62190] (BT.nd BT.lf [3,783,4433] BT.lf))) [3,847,4369] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,3840,4383,8946,21580] BT.lf) [3,3840,4383,13050,17476] BT.lf) [3,4383,4610,17476,35064] (BT.nd BT.lf [3,4383,8946,17988,63624] BT.lf)) [3,4383,8946,20292,64716] (BT.nd (BT.nd BT.lf [3,4383,8946,20292,65262] BT.lf) [3,4383,17988,43770,61440] (BT.nd BT.lf [3,4895,8946,17476,63624] BT.lf)))) [3,4895,17476,35064,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,4895,17476,43770,61440] BT.lf) [3,7967,8946,17476,61678] BT.lf) [4,14,240,512,4369,62532] (BT.nd BT.lf [4,14,240,7953,17476,61986] BT.lf)) [4,14,4369,8946,20292,61440] (BT.nd (BT.nd BT.lf [4,14,7953,8946,17476,61440] BT.lf) [4,15,240,4881,17476,64170] (BT.nd BT.lf [4,15,240,4881,17476,65262] BT.lf))) [4,15,240,4881,43690,62532] (BT.nd (BT.nd (BT.nd BT.lf [4,15,240,4881,61166,62532] BT.lf) [4,15,240,7953,17476,61994] (BT.nd BT.lf [4,15,240,7953,17476,62190] BT.lf)) [4,15,240,7953,17484,61986] (BT.nd (BT.nd BT.lf [4,15,248,7953,17476,61986] BT.lf) [4,15,768,4433] (BT.nd BT.lf [4,15,832,4369] BT.lf))))) [4,15,4112,8946,20292,34952] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,15,4369,8946,17988,63624] BT.lf) [4,15,4369,8946,20292,39048] BT.lf) [4,15,4369,8946,20292,61448] (BT.nd BT.lf [4,15,4369,8946,20292,63624] BT.lf)) [4,15,4369,8946,20292,63736] (BT.nd (BT.nd BT.lf [4,15,4369,8946,20292,64170] BT.lf) [4,15,4369,8946,20292,64250] (BT.nd BT.lf [4,15,4369,8946,20292,64716] BT.lf))) [4,15,4369,8946,20292,65262] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,15,4369,8946,20300,61440] BT.lf) [4,15,4369,8954,20292,61440] BT.lf) [4,15,4369,13042,20292,34952] (BT.nd BT.lf [4,15,4369,17988,43770,61440] BT.lf)) [4,15,4369,20292,43770,62194] (BT.nd (BT.nd BT.lf [4,15,4383,8946,20292,63624] BT.lf) [4,15,4624,8946,17476,34952] (BT.nd BT.lf [4,15,4881,8946,17476,63624] BT.lf)))) [4,15,4881,17476,35064,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,15,4881,17476,43770,61440] BT.lf) [4,15,7953,8946,17476,61448] BT.lf) [4,15,7953,8946,17476,61678] (BT.nd BT.lf [4,15,7953,8946,17484,61440] BT.lf)) [4,15,7953,8954,17476,61440] (BT.nd (BT.nd BT.lf [4,15,7953,13042,17476,34952] BT.lf) [4,15,7953,17476,35064,62194] (BT.nd BT.lf [4,15,7953,17476,43770,62194] BT.lf))) [4,15,8738,53132] (BT.nd (BT.nd (BT.nd BT.lf [4,15,8802,53196] BT.lf) [4,15,25126,36744] (BT.nd BT.lf [4,64,783,4369] BT.lf)) [4,79,768,4369] (BT.nd (BT.nd BT.lf [4,79,8738,53196] BT.lf) [4,240,512,4383,17476,64170] (BT.nd BT.lf [4,240,512,4383,17476,65262] BT.lf)))))) [4,240,512,4383,43690,62532] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,240,512,4383,61166,62532] BT.lf) [4,240,514,4383,17476,63624] BT.lf) [4,240,514,4383,34952,62532] (BT.nd BT.lf [4,240,526,4369,17476,61440] BT.lf)) [4,240,527,4369,17476,64170] (BT.nd (BT.nd BT.lf [4,240,527,4369,17476,65262] BT.lf) [4,240,527,4369,43690,62532] (BT.nd BT.lf [4,240,527,4369,61166,62532] BT.lf))) [4,240,3840,4383,8738,21580] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,240,3840,4383,8738,62540] BT.lf) [4,240,3840,4383,8746,62532] BT.lf) [4,240,3840,4383,12842,17476] (BT.nd BT.lf [4,240,3840,4383,17476,61994] BT.lf)) [4,240,3840,4383,17484,61986] (BT.nd (BT.nd BT.lf [4,240,4369,4895,62532] BT.lf) [4,240,4383,4610,17476,34952] (BT.nd BT.lf [4,240,4383,8738,17988,63624] BT.lf)))) [4,240,4383,8738,20292,64716] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,240,4383,8738,20292,65262] BT.lf) [4,240,4383,8738,35464,62532] BT.lf) [4,240,4383,17988,43690,61440] (BT.nd BT.lf [4,240,4895,8738,17476,63624] BT.lf)) [4,240,4895,8738,34952,62532] (BT.nd (BT.nd BT.lf [4,240,4895,17476,34952,61986] BT.lf) [4,240,4895,17476,43690,61440] (BT.nd BT.lf [4,240,4895,17476,61166,61440] BT.lf))) [4,240,7967,8738,17476,61678] (BT.nd (BT.nd (BT.nd BT.lf [4,240,7967,17476,57582,61986] BT.lf) [4,240,7967,17476,58094,61440] (BT.nd BT.lf [4,248,3840,4383,8738,62532] BT.lf)) [4,248,3840,4383,17476,61986] (BT.nd (BT.nd BT.lf [4,512,4383,8946,17476,63624] BT.lf) [4,512,4383,17476,35064,61986] (BT.nd BT.lf [4,512,4383,17476,43770,61440] BT.lf))))) [4,514,4383,17476,35064,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,527,3840,4433] BT.lf) [4,527,4369,8946,17476,63624] BT.lf) [4,527,4369,17476,35064,61986] (BT.nd BT.lf [4,527,4369,17476,43770,61440] BT.lf)) [4,591,3840,4369] (BT.nd (BT.nd BT.lf [4,591,4369,20292] BT.lf) [4,3840,4104,4383,8946,17476] (BT.nd BT.lf [4,3840,4344,4383,8738,17476] BT.lf))) [4,3840,4383,8738,17476,39160] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,3840,4383,8738,21572,35064] BT.lf) [4,3840,4383,8946,17476,39048] BT.lf) [4,3840,4383,8946,17476,61448] (BT.nd BT.lf [4,3840,4383,8946,17476,63624] BT.lf)) [4,3840,4383,8946,17476,63736] (BT.nd (BT.nd BT.lf [4,3840,4383,8946,17476,64170] BT.lf) [4,3840,4383,8946,17476,64250] (BT.nd BT.lf [4,3840,4383,8946,17476,64716] BT.lf)))) [4,3840,4383,8946,17476,65262] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,3840,4383,8946,17484,61440] BT.lf) [4,3840,4383,8946,21572,34952] BT.lf) [4,3840,4383,8946,35064,62532] (BT.nd BT.lf [4,3840,4383,8946,52428,62532] BT.lf)) [4,3840,4383,8954,17476,61440] (BT.nd (BT.nd BT.lf [4,3840,4383,12834,17476,35064] BT.lf) [4,3840,4383,13042,17476,34952] (BT.nd BT.lf [4,3840,4383,17476,35064,61986] BT.lf))) [4,3840,4383,17476,35064,62194] (BT.nd (BT.nd (BT.nd BT.lf [4,3840,4383,17476,43770,61986] BT.lf) [4,3840,4383,17476,43770,62194] (BT.nd BT.lf [4,3855,4383,8946,17476,63624] BT.lf)) [4,3855,4383,17476,35064,61986] (BT.nd (BT.nd BT.lf [4,3855,4433,8751] BT.lf) [4,3855,8017,8738] (BT.nd BT.lf [4,3919,4369,8815] BT.lf))))))) [4,3919,7953,8738] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,4369,8959,20303] BT.lf) [4,4383,7953,8946,17476,63624] BT.lf) [4,4383,7953,17476,35064,61986] (BT.nd BT.lf [4,4383,7967,8946,17476,63624] BT.lf)) [4,4383,7967,17476,35064,61986] (BT.nd (BT.nd BT.lf [4,4383,8738,17988,35064,61440] BT.lf) [4,4383,8738,20292,35064,62532] (BT.nd BT.lf [4,4383,8946,17476,20292,63624] BT.lf))) [4,4383,8946,17988,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,4383,8946,20292,34952,62532] BT.lf) [4,4383,8946,20292,52428,61440] BT.lf) [4,4383,8946,20292,61166,61440] (BT.nd BT.lf [4,4433,8751,61680] BT.lf)) [4,4593,8751,36751] (BT.nd (BT.nd BT.lf [4,4895,8738,17476,35064,61440] BT.lf) [4,4895,8946,17476,34952,61440] (BT.nd BT.lf [4,7953,8738,61616] BT.lf)))) [4,7967,8946,17476,57582,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,8017,8738,61680] BT.lf) [5,8,15,240,7953,17476,61986] BT.lf) [5,8,15,4369,8946,20292,61440] (BT.nd BT.lf [5,8,15,7953,8946,17476,61440] BT.lf)) [5,8,240,3840,4383,8738,62532] (BT.nd (BT.nd BT.lf [5,8,240,3840,4383,17476,61986] BT.lf) [5,8,3840,4383,8946,17476,61440] (BT.nd BT.lf [5,14,240,512,4369,17476,61440] BT.lf))) [5,14,240,3840,4369,8738,62532] (BT.nd (BT.nd (BT.nd BT.lf [5,14,240,3840,4369,17476,61986] BT.lf) [5,14,240,4369,8738,20292,61440] (BT.nd BT.lf [5,14,240,7953,8738,17476,61440] BT.lf)) [5,14,3840,4369,8946,17476,61440] (BT.nd (BT.nd BT.lf [5,15,64,768,4369] BT.lf) [5,15,64,8738,53196] (BT.nd BT.lf [5,15,240,512,4369,17476,64170] BT.lf))))) [5,15,240,512,4369,17476,65262] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,512,4369,43690,62532] BT.lf) [5,15,240,512,4369,61166,62532] BT.lf) [5,15,240,514,4369,17476,63624] (BT.nd BT.lf [5,15,240,514,4369,34952,62532] BT.lf)) [5,15,240,3840,4369,8738,62540] (BT.nd (BT.nd BT.lf [5,15,240,3840,4369,8746,62532] BT.lf) [5,15,240,3840,4369,17476,61994] (BT.nd BT.lf [5,15,240,3840,4369,17484,61986] BT.lf))) [5,15,240,3848,4369,8738,62532] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,3848,4369,17476,61986] BT.lf) [5,15,240,4112,8738,17476,36744] BT.lf) [5,15,240,4112,8738,20292,34952] (BT.nd BT.lf [5,15,240,4369,4881,62532] BT.lf)) [5,15,240,4369,8738,17988,63624] (BT.nd (BT.nd BT.lf [5,15,240,4369,8738,20292,39048] BT.lf) [5,15,240,4369,8738,20292,61448] (BT.nd BT.lf [5,15,240,4369,8738,20292,63624] BT.lf)))) [5,15,240,4369,8738,20292,63736] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,4369,8738,20292,64170] BT.lf) [5,15,240,4369,8738,20292,64716] BT.lf) [5,15,240,4369,8738,20292,65262] (BT.nd BT.lf [5,15,240,4369,8738,20300,61440] BT.lf)) [5,15,240,4369,8738,21572,36744] (BT.nd (BT.nd BT.lf [5,15,240,4369,8738,35464,62532] BT.lf) [5,15,240,4369,8738,36744,62532] (BT.nd BT.lf [5,15,240,4369,8738,53196,62532] BT.lf))) [5,15,240,4369,8746,20292,61440] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,4369,8946,20292,63624] BT.lf) [5,15,240,4369,12834,17476,36744] (BT.nd BT.lf [5,15,240,4369,12834,20292,34952] BT.lf)) [5,15,240,4369,17988,43690,61440] (BT.nd (BT.nd BT.lf [5,15,240,4369,20292,36744,61986] BT.lf) [5,15,240,4369,20292,43690,61986] (BT.nd BT.lf [5,15,240,4369,64580] BT.lf)))))) [5,15,240,4383,8738,20292,63624] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,4383,8738,36744,62532] BT.lf) [5,15,240,4881,8738,17476,63624] BT.lf) [5,15,240,4881,8738,34952,62532] (BT.nd BT.lf [5,15,240,4881,17476,34952,61986] BT.lf)) [5,15,240,4881,17476,43690,61440] (BT.nd (BT.nd BT.lf [5,15,240,4881,17476,61166,61440] BT.lf) [5,15,240,6417,62532] (BT.nd BT.lf [5,15,240,7953,8738,17476,61448] BT.lf))) [5,15,240,7953,8738,17476,61678] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,7953,8738,17484,61440] BT.lf) [5,15,240,7953,8738,62532,63624] BT.lf) [5,15,240,7953,8746,17476,61440] (BT.nd BT.lf [5,15,240,7953,12834,17476,34952] BT.lf)) [5,15,240,7953,17476,34952,61986] (BT.nd (BT.nd BT.lf [5,15,240,7953,17476,34952,62194] BT.lf) [5,15,240,7953,17476,35064,61986] (BT.nd BT.lf [5,15,240,7953,17476,36744,61986] BT.lf)))) [5,15,240,7953,17476,43690,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,7953,17476,52428,61986] BT.lf) [5,15,240,7953,17476,57582,61986] BT.lf) [5,15,240,7953,17476,58094,61440] (BT.nd BT.lf [5,15,240,7953,17476,61166,61986] BT.lf)) [5,15,240,7953,17476,61986,63624] (BT.nd (BT.nd BT.lf [5,15,240,7953,17476,61986,64170] BT.lf) [5,15,240,7953,20292,34952,61986] (BT.nd BT.lf [5,15,240,7953,34952,61986,62532] BT.lf))) [5,15,240,7967,17476,34952,61986] (BT.nd (BT.nd (BT.nd BT.lf [5,15,248,3840,4369,8738,62532] BT.lf) [5,15,248,3840,4369,17476,61986] (BT.nd BT.lf [5,15,248,4369,8738,20292,61440] BT.lf)) [5,15,248,7953,8738,17476,61440] (BT.nd (BT.nd BT.lf [5,15,512,3840,4433] BT.lf) [5,15,512,4369,8946,17476,63624] (BT.nd BT.lf [5,15,512,4369,17476,35064,61986] BT.lf))))) [5,15,512,4369,17476,43770,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,514,4369,17476,35064,61440] BT.lf) [5,15,576,3840,4369] BT.lf) [5,15,576,4369,20292] (BT.nd BT.lf [5,15,752,4369,20292] BT.lf)) [5,15,2288,4369,62532] (BT.nd (BT.nd BT.lf [5,15,3840,4112,8738,17476,35064] BT.lf) [5,15,3840,4112,8946,17476,34952] (BT.nd BT.lf [5,15,3840,4369,8738,17476,39160] BT.lf))) [5,15,3840,4369,8738,21572,35064] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,3840,4369,8946,17476,39048] BT.lf) [5,15,3840,4369,8946,17476,61448] BT.lf) [5,15,3840,4369,8946,17476,63624] (BT.nd BT.lf [5,15,3840,4369,8946,17476,63736] BT.lf)) [5,15,3840,4369,8946,17476,64170] (BT.nd (BT.nd BT.lf [5,15,3840,4369,8946,17476,64250] BT.lf) [5,15,3840,4369,8946,17476,64716] (BT.nd BT.lf [5,15,3840,4369,8946,17476,65262] BT.lf)))) [5,15,3840,4369,8946,17484,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,3840,4369,8946,20292,63624] BT.lf) [5,15,3840,4369,8946,21572,34952] BT.lf) [5,15,3840,4369,8946,35064,62532] (BT.nd BT.lf [5,15,3840,4369,8946,52428,62532] BT.lf)) [5,15,3840,4369,8954,17476,61440] (BT.nd (BT.nd BT.lf [5,15,3840,4369,12834,17476,35064] BT.lf) [5,15,3840,4369,13042,17476,34952] (BT.nd BT.lf [5,15,3840,4369,17476,35064,61986] BT.lf))) [5,15,3840,4369,17476,35064,62194] (BT.nd (BT.nd (BT.nd BT.lf [5,15,3840,4369,17476,43770,61986] BT.lf) [5,15,3840,4369,17476,43770,62194] (BT.nd BT.lf [5,15,3840,4369,62114] BT.lf)) [5,15,3840,4383,8946,17476,63624] (BT.nd (BT.nd BT.lf [5,15,3840,4383,17476,35064,61986] BT.lf) [5,15,3840,4433,8738] (BT.nd BT.lf [5,15,3840,4433,8751] BT.lf)))))))) [5,15,3840,4433,8802] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,3840,4433,8946] BT.lf) [5,15,3840,4433,13107] BT.lf) [5,15,3840,4433,13171] (BT.nd BT.lf [5,15,3840,4433,52428] BT.lf)) [5,15,3840,4433,56797] (BT.nd (BT.nd BT.lf [5,15,3840,4433,61986] BT.lf) [5,15,3840,4465,8738] (BT.nd BT.lf [5,15,3840,4593,8866] BT.lf))) [5,15,3840,5457,8738] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,3840,5457,34952] BT.lf) [5,15,3840,8017,8738] BT.lf) [5,15,3840,8738,13171] (BT.nd BT.lf [5,15,3840,8738,51340] BT.lf)) [5,15,3840,8738,52364] (BT.nd (BT.nd BT.lf [5,15,3840,8738,61070] BT.lf) [5,15,3840,8738,61102] (BT.nd BT.lf [5,15,3840,8802,13107] BT.lf)))) [5,15,3840,8802,52428] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,3840,13299,21845] BT.lf) [5,15,3840,13299,43690] BT.lf) [5,15,3840,21845,39417] (BT.nd BT.lf [5,15,3840,25126,34952] BT.lf)) [5,15,3840,39417,43690] (BT.nd (BT.nd BT.lf [5,15,3848,4369,8946,17476,61440] BT.lf) [5,15,3855,4369,8946,17476,63624] (BT.nd BT.lf [5,15,3855,4369,17476,35064,61986] BT.lf))) [5,15,3855,4433,8738] (BT.nd (BT.nd (BT.nd BT.lf [5,15,3904,4369,8802] BT.lf) [5,15,3904,4369,8946] (BT.nd BT.lf [5,15,3904,7953,8738] BT.lf)) [5,15,3968,4369,61986] (BT.nd (BT.nd BT.lf [5,15,3968,4593,8738] BT.lf) [5,15,4096,4369,8946,20292,34952] (BT.nd BT.lf [5,15,4096,7953,8946,17476,34952] BT.lf))))) [5,15,4336,4369,8738,17476,36744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,4336,4369,8738,20292,34952] BT.lf) [5,15,4336,7953,8738,17476,34952] BT.lf) [5,15,4369,7953,8946,17476,63624] (BT.nd BT.lf [5,15,4369,7953,17476,35064,61986] BT.lf)) [5,15,4369,8738,8946,20292,63624] (BT.nd (BT.nd BT.lf [5,15,4369,8738,17988,35064,61440] BT.lf) [5,15,4369,8738,20292,35064,61680] (BT.nd BT.lf [5,15,4369,8738,20292,35064,62532] BT.lf))) [5,15,4369,8738,53128] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,4369,8802,20292] BT.lf) [5,15,4369,8946,17476,20292,63624] BT.lf) [5,15,4369,8946,17476,36744,61986] (BT.nd BT.lf [5,15,4369,8946,17988,34952,61440] BT.lf)) [5,15,4369,8946,20292] (BT.nd (BT.nd BT.lf [5,15,4369,8946,20292,34952,61440] BT.lf) [5,15,4369,8946,20292,34952,61680] (BT.nd BT.lf [5,15,4369,8946,20292,34952,61986] BT.lf)))) [5,15,4369,8946,20292,34952,62194] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,4369,8946,20292,34952,62532] BT.lf) [5,15,4369,8946,20292,34952,63624] BT.lf) [5,15,4369,8946,20292,35064,61440] (BT.nd BT.lf [5,15,4369,8946,20292,36744,61440] BT.lf)) [5,15,4369,8946,20292,43690,61440] (BT.nd (BT.nd BT.lf [5,15,4369,8946,20292,43770,61440] BT.lf) [5,15,4369,8946,20292,52428,61440] (BT.nd BT.lf [5,15,4369,8946,20292,53196,61440] BT.lf))) [5,15,4369,8946,20292,61166,61440] (BT.nd (BT.nd (BT.nd BT.lf [5,15,4369,8946,20292,61440,63624] BT.lf) [5,15,4369,8946,20292,63624] (BT.nd BT.lf [5,15,4369,8946,20303] BT.lf)) [5,15,4369,8946,45243] (BT.nd (BT.nd BT.lf [5,15,4369,8959,20292] BT.lf) [5,15,4369,13299,20292] (BT.nd BT.lf [5,15,4369,20292,56589] BT.lf)))))) [5,15,4369,25122,36744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,4369,63736,64170] BT.lf) [5,15,4369,64716,65416] BT.lf) [5,15,4383,8946,20292,34952,61440] (BT.nd BT.lf [5,15,4433,8738,36744] BT.lf)) [5,15,4433,8738,61680] (BT.nd (BT.nd BT.lf [5,15,4433,8738,61695] BT.lf) [5,15,4593,8738,28791] (BT.nd BT.lf [5,15,4593,8738,36744] BT.lf))) [5,15,4593,8738,36751] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,4593,8751,36744] BT.lf) [5,15,4593,36744,56797] BT.lf) [5,15,4881,8738,17476,35064,61440] (BT.nd BT.lf [5,15,4881,8946,17476,34952,61440] BT.lf)) [5,15,7953,8738,17476,35064,61680] (BT.nd (BT.nd BT.lf [5,15,7953,8946,17476,34952,61440] BT.lf) [5,15,7953,8946,17476,34952,61680] (BT.nd BT.lf [5,15,7953,8946,17476,34952,61986] BT.lf)))) [5,15,7953,8946,17476,34952,62194] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,7953,8946,17476,35064,61440] BT.lf) [5,15,7953,8946,17476,36744,61440] BT.lf) [5,15,7953,8946,17476,43690,61440] (BT.nd BT.lf [5,15,7953,8946,17476,43770,61440] BT.lf)) [5,15,7953,8946,17476,52428,61440] (BT.nd (BT.nd BT.lf [5,15,7953,8946,17476,57582,61440] BT.lf) [5,15,7953,8946,17476,61166,61440] (BT.nd BT.lf [5,15,7953,8946,17476,61440,63624] BT.lf))) [5,15,7953,8946,20292] (BT.nd (BT.nd (BT.nd BT.lf [5,15,7953,8946,20292,34952,61440] BT.lf) [5,15,7953,20292,61986] (BT.nd BT.lf [5,15,7953,36744,61986] BT.lf)) [5,15,7967,8946,17476,34952,61440] (BT.nd (BT.nd BT.lf [5,15,8177,8738,36744] BT.lf) [5,15,8738,13299,36744] (BT.nd BT.lf [5,15,8738,16388,36744] BT.lf))))) [5,15,8738,17412,36744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,8738,17476,53128] BT.lf) [5,15,8738,20228,34952] BT.lf) [5,15,8738,34952,45307] (BT.nd BT.lf [5,15,8738,36744,39417] BT.lf)) [5,15,8738,36744,40953] (BT.nd (BT.nd BT.lf [5,15,8738,36744,48123] BT.lf) [5,15,8738,36744,60942] (BT.nd BT.lf [5,15,8738,53196,65416] BT.lf))) [5,15,8802,17476,36744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,8802,20292,34952] BT.lf) [5,15,8946,20292,21845] BT.lf) [5,15,8946,20292,24405] (BT.nd BT.lf [5,15,8946,20292,43690] BT.lf)) [5,15,8946,20292,61166] (BT.nd (BT.nd BT.lf [5,15,17476,25122,36744] BT.lf) [5,15,20292,21845,35064] (BT.nd BT.lf [5,15,20292,35064,43690] BT.lf)))) [5,15,26214,36744,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,36744,39321,61986] BT.lf) [5,64,527,3840,4369] BT.lf) [5,64,3855,4369,8751] (BT.nd BT.lf [5,64,3855,7953,8738] BT.lf)) [5,64,4369,8751,61680] (BT.nd (BT.nd BT.lf [5,64,7953,8738,61680] BT.lf) [5,79,512,3840,4369] (BT.nd BT.lf [5,79,3840,4369,8738] BT.lf))) [5,79,3840,4369,8751] (BT.nd (BT.nd (BT.nd BT.lf [5,79,3840,4369,8802] BT.lf) [5,79,3840,4369,8815] (BT.nd BT.lf [5,79,3840,4369,8946] BT.lf)) [5,79,3840,4369,13107] (BT.nd (BT.nd BT.lf [5,79,3840,4369,52428] BT.lf) [5,79,3840,4369,56797] (BT.nd BT.lf [5,79,3840,4369,61986] BT.lf))))))) [5,79,3840,7953,8738] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,79,3840,8738,13107] BT.lf) [5,79,3840,8738,52428] BT.lf) [5,79,3840,8738,61166] (BT.nd BT.lf [5,79,3855,4369,8738] BT.lf)) [5,79,3904,4369,8738] (BT.nd (BT.nd BT.lf [5,79,3919,4369,8738] BT.lf) [5,79,4369,8738,20292] (BT.nd BT.lf [5,79,4369,8738,36744] BT.lf))) [5,79,4369,8738,61680] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,79,4369,8738,61695] BT.lf) [5,79,8738,17476,36744] BT.lf) [5,79,8738,20292,34952] (BT.nd BT.lf [5,112,4369,8751,61440] BT.lf)) [5,143,3840,4593,8738] (BT.nd (BT.nd BT.lf [5,176,7953,8738,61440] BT.lf) [5,240,512,4369,4383,62532] (BT.nd BT.lf [5,240,512,4383,8738,17476,63624] BT.lf)))) [5,240,512,4383,8738,34952,62532] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,512,4383,17476,34952,61986] BT.lf) [5,240,512,4383,17476,43690,61440] BT.lf) [5,240,512,4383,17476,61166,61440] (BT.nd BT.lf [5,240,514,4383,17476,34952,61440] BT.lf)) [5,240,527,4369,8738,17476,63624] (BT.nd (BT.nd BT.lf [5,240,527,4369,8738,34952,62532] BT.lf) [5,240,527,4369,17476,34952,61986] (BT.nd BT.lf [5,240,527,4369,17476,43690,61440] BT.lf))) [5,240,527,4369,17476,61166,61440] (BT.nd (BT.nd (BT.nd BT.lf [5,240,527,4369,20292] BT.lf) [5,240,527,4369,62532] (BT.nd BT.lf [5,240,783,4369,17476] BT.lf)) [5,240,3840,4104,4383,8738,17476] (BT.nd (BT.nd BT.lf [5,240,3840,4383,8738,17476,39048] BT.lf) [5,240,3840,4383,8738,17476,61448] (BT.nd BT.lf [5,240,3840,4383,8738,17476,63624] BT.lf))))) [5,240,3840,4383,8738,17476,63736] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,3840,4383,8738,17476,64170] BT.lf) [5,240,3840,4383,8738,17476,64716] BT.lf) [5,240,3840,4383,8738,17476,65262] (BT.nd BT.lf [5,240,3840,4383,8738,17484,61440] BT.lf)) [5,240,3840,4383,8738,21572,34952] (BT.nd (BT.nd BT.lf [5,240,3840,4383,8738,34952,62532] BT.lf) [5,240,3840,4383,8738,35064,62532] (BT.nd BT.lf [5,240,3840,4383,8738,43690,62532] BT.lf))) [5,240,3840,4383,8738,52428,62532] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,3840,4383,8738,61166,62532] BT.lf) [5,240,3840,4383,8738,62532,63624] BT.lf) [5,240,3840,4383,8738,62532,64716] (BT.nd BT.lf [5,240,3840,4383,8746,17476,61440] BT.lf)) [5,240,3840,4383,8946,17476,63624] (BT.nd (BT.nd BT.lf [5,240,3840,4383,8946,34952,62532] BT.lf) [5,240,3840,4383,12834,17476,34952] (BT.nd BT.lf [5,240,3840,4383,17476,34952,61986] BT.lf)))) [5,240,3840,4383,17476,34952,62194] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,3840,4383,17476,35064,61986] BT.lf) [5,240,3840,4383,17476,43690,61986] BT.lf) [5,240,3840,4383,17476,52428,61986] (BT.nd BT.lf [5,240,3840,4383,17476,61166,61986] BT.lf)) [5,240,3840,4383,17476,61986,63624] (BT.nd (BT.nd BT.lf [5,240,3840,4383,17476,61986,64170] BT.lf) [5,240,3840,4383,34952,61986,62532] (BT.nd BT.lf [5,240,3855,4383,8738,17476,63624] BT.lf))) [5,240,3855,4383,8738,34952,62532] (BT.nd (BT.nd (BT.nd BT.lf [5,240,3855,4383,17476,34952,61986] BT.lf) [5,240,4369,4895,17476,61440] (BT.nd BT.lf [5,240,4369,8751,20303] BT.lf)) [5,240,4369,8751,36751] (BT.nd (BT.nd BT.lf [5,240,4369,8751,61504] BT.lf) [5,240,4369,8751,61568] (BT.nd BT.lf [5,240,4369,8879,61440] BT.lf)))))) [5,240,4369,17476,64512] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,4383,7953,8738,17476,63624] BT.lf) [5,240,4383,7953,8738,34952,62532] BT.lf) [5,240,4383,7953,8738,62532] (BT.nd BT.lf [5,240,4383,7953,17476,34952,61986] BT.lf)) [5,240,4383,7967,8738,17476,63624] (BT.nd (BT.nd BT.lf [5,240,4383,7967,8738,34952,62532] BT.lf) [5,240,4383,7967,17476,34952,61986] (BT.nd BT.lf [5,240,4383,8738,17476,20292,63624] BT.lf))) [5,240,4383,8738,17476,35464,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,4383,8738,17476,36744,63624] BT.lf) [5,240,4383,8738,17988,34952,61440] BT.lf) [5,240,4383,8738,20292,34952,62532] (BT.nd BT.lf [5,240,4383,8738,20292,52428,61440] BT.lf)) [5,240,4383,8738,20292,61166,61440] (BT.nd (BT.nd BT.lf [5,240,4383,8738,34952,36744,62532] BT.lf) [5,240,4433,8751,61440] (BT.nd BT.lf [5,240,4895,8738,17476,34952,61440] BT.lf)))) [5,240,7441,17476,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,240,7953,7967,17476,61986] BT.lf) [5,240,7953,8738,61504] BT.lf) [5,240,7953,8738,61568] (BT.nd BT.lf [5,240,7953,8866,61440] BT.lf)) [5,240,7953,17476,61952] (BT.nd (BT.nd BT.lf [5,240,7953,61986,62532] BT.lf) [5,240,7953,61986,63624] (BT.nd BT.lf [5,240,7967,8738,17476,57582,61440] BT.lf))) [5,240,8017,8738,61440] (BT.nd (BT.nd (BT.nd BT.lf [5,240,17476,58094,61440] BT.lf) [5,248,3840,4383,8738,17476,61440] (BT.nd BT.lf [5,255,4369,8738,20303] BT.lf)) [5,255,4369,8738,62543] (BT.nd (BT.nd BT.lf [5,255,4369,17487,63624] BT.lf) [5,255,4369,34952,62543] (BT.nd BT.lf [5,255,8738,17652,36744] BT.lf))))) [5,255,8738,20468,34952] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,512,4383,8738,17476,35064,61440] BT.lf) [5,512,4383,8946,17476,34952,61440] BT.lf) [5,527,4369,8738,17476,35064,61440] (BT.nd BT.lf [5,527,4369,8946,17476,34952,61440] BT.lf)) [5,752,7953,17476,61440] (BT.nd (BT.nd BT.lf [5,1103,3840,4369,8738] BT.lf) [5,1103,3840,4369,34952] (BT.nd BT.lf [5,1792,4369,17487,61440] BT.lf))) [5,3840,3855,4433,8738] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,3919,4369,8738] BT.lf) [5,3840,4096,4383,8738,17476,35064] BT.lf) [5,3840,4096,4383,8946,17476,34952] (BT.nd BT.lf [5,3840,4336,4383,8738,17476,34952] BT.lf)) [5,3840,4369,4383,8946,17476,63624] (BT.nd (BT.nd BT.lf [5,3840,4369,4383,17476,35064,61986] BT.lf) [5,3840,4369,8738,61616] (BT.nd BT.lf [5,3840,4369,8738,64432] BT.lf)))) [5,3840,4369,8738,65456] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4369,8959,17487] BT.lf) [5,3840,4369,17487,35071] BT.lf) [5,3840,4369,17487,61952] (BT.nd BT.lf [5,3840,4369,17487,63488] BT.lf)) [5,3840,4369,19535,61440] (BT.nd (BT.nd BT.lf [5,3840,4369,34952,64432] BT.lf) [5,3840,4383,8738,8946,17476,63624] (BT.nd BT.lf [5,3840,4383,8738,17476,35064,61440] BT.lf))) [5,3840,4383,8738,17476,35064,61680] (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4383,8738,17476,35064,61986] BT.lf) [5,3840,4383,8738,17476,35064,62532] (BT.nd BT.lf [5,3840,4383,8738,17476,35064,63624] BT.lf)) [5,3840,4383,8738,17476,35064,63736] (BT.nd (BT.nd BT.lf [5,3840,4383,8738,17476,43770,61440] BT.lf) [5,3840,4383,8946,17476,34952,61440] (BT.nd BT.lf [5,3840,4383,8946,17476,34952,61680] BT.lf))))))))) [5,3840,4383,8946,17476,34952,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4383,8946,17476,34952,62194] BT.lf) [5,3840,4383,8946,17476,34952,62532] BT.lf) [5,3840,4383,8946,17476,34952,63624] (BT.nd BT.lf [5,3840,4383,8946,17476,35064,61440] BT.lf)) [5,3840,4383,8946,17476,43690,61440] (BT.nd (BT.nd BT.lf [5,3840,4383,8946,17476,43770,61440] BT.lf) [5,3840,4383,8946,17476,52428,61440] (BT.nd BT.lf [5,3840,4383,8946,17476,61166,61440] BT.lf))) [5,3840,4383,8946,17476,61440,63624] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4383,8946,17476,63624] BT.lf) [5,3840,4383,17476,34952,35064,61986] BT.lf) [5,3840,4383,17476,35064,61440,61986] (BT.nd BT.lf [5,3840,4383,17476,35064,61986] BT.lf)) [5,3840,4433,8738,61680] (BT.nd (BT.nd BT.lf [5,3840,4433,8738,65520] BT.lf) [5,3840,4593,8751,34959] (BT.nd BT.lf [5,3840,6417,17487,61440] BT.lf)))) [5,3840,8738,17487,20753] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,17487,20753,34952] BT.lf) [5,3855,3904,4369,8738] BT.lf) [5,3855,4369,8751,63624] (BT.nd BT.lf [5,3855,4369,8959,17476] BT.lf)) [5,3855,4369,17476,61999] (BT.nd (BT.nd BT.lf [5,3855,4369,34952,61999] BT.lf) [5,3855,4383,8738,17476,35064,61440] (BT.nd BT.lf [5,3855,4383,8946,17476,34952,61440] BT.lf))) [5,3855,4593,8751,34952] (BT.nd (BT.nd (BT.nd BT.lf [5,3855,7953,8738,63624] BT.lf) [5,3855,7953,8946,17476] (BT.nd BT.lf [5,3855,7953,17476,61986] BT.lf)) [5,3855,7953,34952,61986] (BT.nd (BT.nd BT.lf [5,3855,8177,8738,34952] BT.lf) [5,3904,4369,8738,61680] (BT.nd BT.lf [5,4369,4383,8946,20292,61440] BT.lf))))) [5,4369,8738,17487,20224] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,4369,8738,20303,65280] BT.lf) [5,4369,8738,62543,65280] BT.lf) [5,4369,8751,35064,63624] (BT.nd BT.lf [5,4369,8751,36751,61440] BT.lf)) [5,4369,8751,61440,65423] (BT.nd (BT.nd BT.lf [5,4369,8751,61680,63624] BT.lf) [5,4369,8946,20292,65520] (BT.nd BT.lf [5,4369,8959,17476,61680] BT.lf))) [5,4369,17476,61680,61999] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,4369,17487,20224,34952] BT.lf) [5,4369,17487,35071,61440] BT.lf) [5,4369,17487,36744,63624] (BT.nd BT.lf [5,4369,17487,61440,63743] BT.lf)) [5,4369,17487,63624,65280] (BT.nd (BT.nd BT.lf [5,4369,34952,61680,61999] BT.lf) [5,4369,34952,62543,65280] (BT.nd BT.lf [5,4383,7953,8738,17476,35064,61440] BT.lf)))) [5,4383,7953,8946,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,4383,7967,8738,17476,35064,61440] BT.lf) [5,4383,7967,8946,17476,34952,61440] BT.lf) [5,4383,8738,17476,20292,35064,61440] (BT.nd BT.lf [5,4383,8738,17476,35064,36744,61440] BT.lf)) [5,4383,8946,17476,20292,34952,61440] (BT.nd (BT.nd BT.lf [5,4593,8738,36744,65520] BT.lf) [5,4593,8751,34952,61680] (BT.nd BT.lf [5,4593,8751,36744,61440] BT.lf))) [5,7953,7967,8946,17476,61440] (BT.nd (BT.nd (BT.nd BT.lf [5,7953,8738,20303,61440] BT.lf) [5,7953,8738,61440,65359] (BT.nd BT.lf [5,7953,8738,61680,63624] BT.lf)) [5,7953,8946,17476,61680] (BT.nd (BT.nd BT.lf [5,7953,8946,17487,61440] BT.lf) [5,7953,17476,61680,61986] (BT.nd BT.lf [5,7953,34952,61680,61986] BT.lf)))))) [5,8177,8738,34952,61680] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,8738,17652,36744,65280] BT.lf) [5,8738,20468,34952,65280] BT.lf) [5,8738,20468,36744,61440] (BT.nd BT.lf [5,17487,26214,36744,61440] BT.lf)) [5,17487,36744,39321,61440] (BT.nd (BT.nd BT.lf [6,8,15,240,3840,4369,8738,62532] BT.lf) [6,8,15,240,3840,4369,17476,61986] (BT.nd BT.lf [6,8,15,240,4369,8738,20292,61440] BT.lf))) [6,8,15,240,7953,8738,17476,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,8,15,3840,4369,8946,17476,61440] BT.lf) [6,8,240,3840,4383,8738,17476,61440] BT.lf) [6,14,240,3840,4369,8738,17476,61440] (BT.nd BT.lf [6,15,64,512,3840,4369] BT.lf)) [6,15,64,3840,4369,8738] (BT.nd (BT.nd BT.lf [6,15,64,3840,4369,8751] BT.lf) [6,15,64,3840,4369,8802] (BT.nd BT.lf [6,15,64,3840,4369,8946] BT.lf)))) [6,15,64,3840,4369,13107] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,64,3840,4369,52428] BT.lf) [6,15,64,3840,4369,56797] BT.lf) [6,15,64,3840,4369,61986] (BT.nd BT.lf [6,15,64,3840,4433,8738] BT.lf)) [6,15,64,3840,7953,8738] (BT.nd (BT.nd BT.lf [6,15,64,3840,8738,13107] BT.lf) [6,15,64,3840,8738,52428] (BT.nd BT.lf [6,15,64,3840,8738,61166] BT.lf))) [6,15,64,3855,4369,8738] (BT.nd (BT.nd (BT.nd BT.lf [6,15,64,3904,4369,8738] BT.lf) [6,15,64,4369,8738,20292] (BT.nd BT.lf [6,15,64,4369,8738,36744] BT.lf)) [6,15,64,4369,8738,61680] (BT.nd (BT.nd BT.lf [6,15,64,4369,8738,61695] BT.lf) [6,15,64,8738,17476,36744] (BT.nd BT.lf [6,15,64,8738,20292,34952] BT.lf))))) [6,15,68,3840,4369,8738] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,79,3840,4369,8738] BT.lf) [6,15,80,3840,4369,8738] BT.lf) [6,15,96,3840,4369,8738] (BT.nd BT.lf [6,15,112,3840,4369,8738] BT.lf)) [6,15,112,4369,8738,61440] (BT.nd (BT.nd BT.lf [6,15,128,3840,4369,61986] BT.lf) [6,15,128,3840,4593,8738] (BT.nd BT.lf [6,15,240,512,4369,8738,17476,63624] BT.lf))) [6,15,240,512,4369,8738,34952,62532] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,512,4369,17476,34952,61986] BT.lf) [6,15,240,512,4369,17476,43690,61440] BT.lf) [6,15,240,512,4369,17476,61166,61440] (BT.nd BT.lf [6,15,240,512,4369,20292] BT.lf)) [6,15,240,512,4369,62532] (BT.nd (BT.nd BT.lf [6,15,240,514,4369,17476,34952,61440] BT.lf) [6,15,240,768,4369,17476] (BT.nd BT.lf [6,15,240,1792,4369,17476] BT.lf)))) [6,15,240,1911,4369,8738] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,1911,4369,17476] BT.lf) [6,15,240,2048,4369,62532] BT.lf) [6,15,240,3003,4369,8738] (BT.nd BT.lf [6,15,240,3003,4369,34952] BT.lf)) [6,15,240,3840,4112,8738,17476,34952] (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,8738,17476,39048] BT.lf) [6,15,240,3840,4369,8738,17476,61448] (BT.nd BT.lf [6,15,240,3840,4369,8738,17476,63624] BT.lf))) [6,15,240,3840,4369,8738,17476,63736] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,8738,17476,64170] BT.lf) [6,15,240,3840,4369,8738,17476,64716] (BT.nd BT.lf [6,15,240,3840,4369,8738,17476,65262] BT.lf)) [6,15,240,3840,4369,8738,17484,61440] (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,8738,20292,63624] BT.lf) [6,15,240,3840,4369,8738,21572,34952] (BT.nd BT.lf [6,15,240,3840,4369,8738,34952,62532] BT.lf))))))) [6,15,240,3840,4369,8738,35064,62532] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,8738,36744,62532] BT.lf) [6,15,240,3840,4369,8738,43690,62532] BT.lf) [6,15,240,3840,4369,8738,52428,62532] (BT.nd BT.lf [6,15,240,3840,4369,8738,61166,62532] BT.lf)) [6,15,240,3840,4369,8738,62532,63624] (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,8738,62532,64716] BT.lf) [6,15,240,3840,4369,8746,17476,61440] (BT.nd BT.lf [6,15,240,3840,4369,8866] BT.lf))) [6,15,240,3840,4369,8946,17476,63624] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,8946,34952,62532] BT.lf) [6,15,240,3840,4369,12834,17476,34952] BT.lf) [6,15,240,3840,4369,17476,34952,61986] (BT.nd BT.lf [6,15,240,3840,4369,17476,34952,62194] BT.lf)) [6,15,240,3840,4369,17476,35064,61986] (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,17476,36744,61986] BT.lf) [6,15,240,3840,4369,17476,43690,61986] (BT.nd BT.lf [6,15,240,3840,4369,17476,52428,61986] BT.lf)))) [6,15,240,3840,4369,17476,61166,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,17476,61986,63624] BT.lf) [6,15,240,3840,4369,17476,61986,64170] BT.lf) [6,15,240,3840,4369,19524] (BT.nd BT.lf [6,15,240,3840,4369,20292,34952,61986] BT.lf)) [6,15,240,3840,4369,34952,61986,62532] (BT.nd (BT.nd BT.lf [6,15,240,3840,4383,8738,17476,63624] BT.lf) [6,15,240,3840,4383,8738,34952,62532] (BT.nd BT.lf [6,15,240,3840,4383,17476,34952,61986] BT.lf))) [6,15,240,3840,4433,8738] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,3840,6417,17476] BT.lf) [6,15,240,3840,7953,17476,34952,61986] (BT.nd BT.lf [6,15,240,3840,13107,21845] BT.lf)) [6,15,240,3840,13107,26214] (BT.nd (BT.nd BT.lf [6,15,240,3840,13107,39321] BT.lf) [6,15,240,3840,13107,43690] (BT.nd BT.lf [6,15,240,3840,21845,26214] BT.lf))))) [6,15,240,3840,21845,39321] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,3840,21845,52428] BT.lf) [6,15,240,3840,26214,43690] BT.lf) [6,15,240,3840,26214,52428] (BT.nd BT.lf [6,15,240,3840,39321,43690] BT.lf)) [6,15,240,3840,39321,52428] (BT.nd (BT.nd BT.lf [6,15,240,3840,43690,52428] BT.lf) [6,15,240,3848,4369,8738,17476,61440] (BT.nd BT.lf [6,15,240,3855,4369,8738,17476,63624] BT.lf))) [6,15,240,3855,4369,8738,34952,62532] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,3855,4369,17476,34952,61986] BT.lf) [6,15,240,3904,4369,8738] BT.lf) [6,15,240,3968,4369,8738] (BT.nd BT.lf [6,15,240,4096,4369,8738,17476,36744] BT.lf)) [6,15,240,4096,4369,8738,20292,34952] (BT.nd (BT.nd BT.lf [6,15,240,4096,7953,8738,17476,34952] BT.lf) [6,15,240,4369,4881,17476,61440] (BT.nd BT.lf [6,15,240,4369,7953,8738,17476,63624] BT.lf)))) [6,15,240,4369,7953,8738,34952,62532] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,7953,8738,62532] BT.lf) [6,15,240,4369,7953,17476,34952,61986] BT.lf) [6,15,240,4369,7953,17476,61986] (BT.nd BT.lf [6,15,240,4369,8738,17476,20292,63624] BT.lf)) [6,15,240,4369,8738,17476,35464,61440] (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,17476,36744,61440] BT.lf) [6,15,240,4369,8738,17476,36744,61680] (BT.nd BT.lf [6,15,240,4369,8738,17476,36744,61986] BT.lf))) [6,15,240,4369,8738,17476,36744,62532] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,17476,36744,63624] BT.lf) [6,15,240,4369,8738,17476,53196,61440] (BT.nd BT.lf [6,15,240,4369,8738,17988,34952,61440] BT.lf)) [6,15,240,4369,8738,20292] (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,20292,34952,61440] BT.lf) [6,15,240,4369,8738,20292,34952,61680] (BT.nd BT.lf [6,15,240,4369,8738,20292,34952,61986] BT.lf)))))) [6,15,240,4369,8738,20292,34952,62532] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,20292,34952,63624] BT.lf) [6,15,240,4369,8738,20292,35064,61440] BT.lf) [6,15,240,4369,8738,20292,36744,61440] (BT.nd BT.lf [6,15,240,4369,8738,20292,43690,61440] BT.lf)) [6,15,240,4369,8738,20292,52428,61440] (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,20292,53196,61440] BT.lf) [6,15,240,4369,8738,20292,61166,61440] (BT.nd BT.lf [6,15,240,4369,8738,20292,61440,63624] BT.lf))) [6,15,240,4369,8738,20292,63624] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,20303] BT.lf) [6,15,240,4369,8738,28791] BT.lf) [6,15,240,4369,8738,34952,36744,62532] (BT.nd BT.lf [6,15,240,4369,8738,36744] BT.lf)) [6,15,240,4369,8738,36744,61440,62532] (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,36744,62532] BT.lf) [6,15,240,4369,8738,36751] (BT.nd BT.lf [6,15,240,4369,8738,45243] BT.lf)))) [6,15,240,4369,8738,61504] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,61568] BT.lf) [6,15,240,4369,8738,62532] BT.lf) [6,15,240,4369,8738,62543] (BT.nd BT.lf [6,15,240,4369,8738,63624] BT.lf)) [6,15,240,4369,8738,63631] (BT.nd (BT.nd BT.lf [6,15,240,4369,8751,20292] BT.lf) [6,15,240,4369,8751,36744] (BT.nd BT.lf [6,15,240,4369,8751,62532] BT.lf))) [6,15,240,4369,8751,63624] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,8866,61440] BT.lf) [6,15,240,4369,8946,20292] (BT.nd BT.lf [6,15,240,4369,8946,20292,34952,61440] BT.lf)) [6,15,240,4369,8946,62532] (BT.nd (BT.nd BT.lf [6,15,240,4369,13107,20292] BT.lf) [6,15,240,4369,13107,36744] (BT.nd BT.lf [6,15,240,4369,13107,62532] BT.lf))))) [6,15,240,4369,13107,63624] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,17476,63488] BT.lf) [6,15,240,4369,17476,63624] BT.lf) [6,15,240,4369,17476,63631] (BT.nd BT.lf [6,15,240,4369,17476,63736] BT.lf)) [6,15,240,4369,17476,63743] (BT.nd (BT.nd BT.lf [6,15,240,4369,17476,64716] BT.lf) [6,15,240,4369,17487,63624] (BT.nd BT.lf [6,15,240,4369,19524,61440] BT.lf))) [6,15,240,4369,20292,52428] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,20292,56797] BT.lf) [6,15,240,4369,21845,63624] BT.lf) [6,15,240,4369,26214,62532] (BT.nd BT.lf [6,15,240,4369,30583,62532] BT.lf)) [6,15,240,4369,34952,62532] (BT.nd (BT.nd BT.lf [6,15,240,4369,34952,62543] BT.lf) [6,15,240,4369,34952,64716] (BT.nd BT.lf [6,15,240,4369,34959,62532] BT.lf)))) [6,15,240,4369,35064,62532] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,36744,52428] BT.lf) [6,15,240,4369,36744,56797] BT.lf) [6,15,240,4369,39321,62532] (BT.nd BT.lf [6,15,240,4369,43690,63624] BT.lf)) [6,15,240,4369,48059,63624] (BT.nd (BT.nd BT.lf [6,15,240,4369,52428,62532] BT.lf) [6,15,240,4369,52428,63624] (BT.nd BT.lf [6,15,240,4369,56797,62532] BT.lf))) [6,15,240,4369,56797,63624] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,61986,62532] BT.lf) [6,15,240,4369,61986,63624] (BT.nd BT.lf [6,15,240,4369,62532,63078] BT.lf)) [6,15,240,4369,62532,63624] (BT.nd (BT.nd BT.lf [6,15,240,4369,62532,64716] BT.lf) [6,15,240,4369,63624,64170] (BT.nd BT.lf [6,15,240,4369,63624,64716] BT.lf)))))))) [6,15,240,4383,8738,17476,36744,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4383,8738,20292,34952,61440] BT.lf) [6,15,240,4433,8738,61440] BT.lf) [6,15,240,4593,8738,36744] (BT.nd BT.lf [6,15,240,4593,8738,63624] BT.lf)) [6,15,240,4881,8738,17476,34952,61440] (BT.nd (BT.nd BT.lf [6,15,240,6417,17476,61440] BT.lf) [6,15,240,7953,8738,17476,34952,61440] (BT.nd BT.lf [6,15,240,7953,8738,17476,34952,61680] BT.lf))) [6,15,240,7953,8738,17476,34952,61986] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,7953,8738,17476,35064,61440] BT.lf) [6,15,240,7953,8738,17476,36744,61440] BT.lf) [6,15,240,7953,8738,17476,43690,61440] (BT.nd BT.lf [6,15,240,7953,8738,17476,52428,61440] BT.lf)) [6,15,240,7953,8738,17476,57582,61440] (BT.nd (BT.nd BT.lf [6,15,240,7953,8738,17476,61166,61440] BT.lf) [6,15,240,7953,8738,17476,61440,63624] (BT.nd BT.lf [6,15,240,7953,8738,20292] BT.lf)))) [6,15,240,7953,8738,20292,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,7953,8738,34952,61440,62532] BT.lf) [6,15,240,7953,8738,36744] BT.lf) [6,15,240,7953,8946,17476,34952,61440] (BT.nd BT.lf [6,15,240,7953,17476,34952,61440,61986] BT.lf)) [6,15,240,7953,17476,34952,61986] (BT.nd (BT.nd BT.lf [6,15,240,7953,17476,61986] BT.lf) [6,15,240,7953,34952,61986] (BT.nd BT.lf [6,15,240,7967,8738,17476,34952,61440] BT.lf))) [6,15,240,8738,13107,20292] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,8738,13107,36744] BT.lf) [6,15,240,8738,13107,62532] (BT.nd BT.lf [6,15,240,8738,13107,63624] BT.lf)) [6,15,240,8738,17476,28791] (BT.nd (BT.nd BT.lf [6,15,240,8738,17476,36744] BT.lf) [6,15,240,8738,17476,53196] (BT.nd BT.lf [6,15,240,8738,17652,36744] BT.lf))))) [6,15,240,8738,20292,21845] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,8738,20292,24405] BT.lf) [6,15,240,8738,20292,30583] BT.lf) [6,15,240,8738,20292,34952] (BT.nd BT.lf [6,15,240,8738,20292,36744] BT.lf)) [6,15,240,8738,20292,43690] (BT.nd (BT.nd BT.lf [6,15,240,8738,20292,52428] BT.lf) [6,15,240,8738,20292,53196] (BT.nd BT.lf [6,15,240,8738,20292,61166] BT.lf))) [6,15,240,8738,20468,34952] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,8738,26214,36744] BT.lf) [6,15,240,8738,34952,45243] BT.lf) [6,15,240,8738,34952,53196] (BT.nd BT.lf [6,15,240,8738,36744,39321] BT.lf)) [6,15,240,8738,36744,40857] (BT.nd (BT.nd BT.lf [6,15,240,8738,36744,48059] BT.lf) [6,15,240,8738,36744,52428] (BT.nd BT.lf [6,15,240,8738,36744,53196] BT.lf)))) [6,15,240,8738,36744,61166] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,8738,52428,62532] BT.lf) [6,15,240,8738,52428,63624] BT.lf) [6,15,240,8738,61166,62532] (BT.nd BT.lf [6,15,240,8738,61166,63624] BT.lf)) [6,15,240,12066,17476,34952,61713] (BT.nd (BT.nd BT.lf [6,15,240,13107,21845,61440] BT.lf) [6,15,240,13107,26214,61440] (BT.nd BT.lf [6,15,240,13107,39321,61440] BT.lf))) [6,15,240,13107,43690,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,17476,21845,63624] BT.lf) [6,15,240,17476,26214,36744] (BT.nd BT.lf [6,15,240,17476,36744,39321] BT.lf)) [6,15,240,17476,36744,56797] (BT.nd (BT.nd BT.lf [6,15,240,17476,43690,63624] BT.lf) [6,15,240,17476,61166,63624] (BT.nd BT.lf [6,15,240,20292,21845,34952] BT.lf)))))) [6,15,240,20292,34952,43690] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,20292,34952,56797] BT.lf) [6,15,240,21845,26214,61440] BT.lf) [6,15,240,21845,39321,61440] (BT.nd BT.lf [6,15,240,21845,52428,61440] BT.lf)) [6,15,240,26214,34952,62532] (BT.nd (BT.nd BT.lf [6,15,240,26214,43690,61440] BT.lf) [6,15,240,26214,52428,61440] (BT.nd BT.lf [6,15,240,34952,39321,62532] BT.lf))) [6,15,240,34952,61166,62532] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,39321,43690,61440] BT.lf) [6,15,240,39321,52428,61440] BT.lf) [6,15,240,43690,52428,61440] (BT.nd BT.lf [6,15,248,3840,4369,8738,17476,61440] BT.lf)) [6,15,255,4369,8738,20292] (BT.nd (BT.nd BT.lf [6,15,255,4369,8738,36744] BT.lf) [6,15,255,4369,8738,62532] (BT.nd BT.lf [6,15,255,4369,8738,63624] BT.lf)))) [6,15,255,4369,17476,63624] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,255,4369,34952,62532] BT.lf) [6,15,255,8738,17476,36744] BT.lf) [6,15,255,8738,20292,34952] (BT.nd BT.lf [6,15,512,4369,8738,17476,35064,61440] BT.lf)) [6,15,512,4369,8946,17476,34952,61440] (BT.nd (BT.nd BT.lf [6,15,752,3840,4369,17476] BT.lf) [6,15,1088,3840,4369,8738] (BT.nd BT.lf [6,15,1088,3840,4369,34952] BT.lf))) [6,15,1092,3840,4369,8738] (BT.nd (BT.nd (BT.nd BT.lf [6,15,1092,3840,4369,34952] BT.lf) [6,15,1792,4369,17476,61440] (BT.nd BT.lf [6,15,1911,3840,4369,8738] BT.lf)) [6,15,1911,3840,4369,17476] (BT.nd (BT.nd BT.lf [6,15,2288,3840,4369,17476] BT.lf) [6,15,2288,4369,17476,61440] (BT.nd BT.lf [6,15,3549,3840,4369,17476] BT.lf))))) [6,15,3549,3840,4369,34952] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,3904,4369,8738] BT.lf) [6,15,3840,4096,4369,8738,17476,35064] BT.lf) [6,15,3840,4096,4369,8946,17476,34952] (BT.nd BT.lf [6,15,3840,4336,4369,8738,17476,34952] BT.lf)) [6,15,3840,4369,4433,8738] (BT.nd (BT.nd BT.lf [6,15,3840,4369,8738,8802] BT.lf) [6,15,3840,4369,8738,8946,17476,63624] (BT.nd BT.lf [6,15,3840,4369,8738,17476,35064,61440] BT.lf))) [6,15,3840,4369,8738,17476,35064,61680] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,8738,17476,35064,61986] BT.lf) [6,15,3840,4369,8738,17476,35064,62532] BT.lf) [6,15,3840,4369,8738,17476,35064,63624] (BT.nd BT.lf [6,15,3840,4369,8738,17476,35064,63736] BT.lf)) [6,15,3840,4369,8738,17476,43770,61440] (BT.nd (BT.nd BT.lf [6,15,3840,4369,8738,17652,63624] BT.lf) [6,15,3840,4369,8738,51336] (BT.nd BT.lf [6,15,3840,4369,8738,61568] BT.lf)))) [6,15,3840,4369,8738,63624] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,8738,63631] BT.lf) [6,15,3840,4369,8738,63897] BT.lf) [6,15,3840,4369,8738,64170] (BT.nd BT.lf [6,15,3840,4369,8738,64443] BT.lf)) [6,15,3840,4369,8738,65416] (BT.nd (BT.nd BT.lf [6,15,3840,4369,8738,65423] BT.lf) [6,15,3840,4369,8738,65471] (BT.nd BT.lf [6,15,3840,4369,8751,63624] BT.lf))) [6,15,3840,4369,8802,17476] (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,8866,61440] BT.lf) [6,15,3840,4369,8946,17476] (BT.nd BT.lf [6,15,3840,4369,8946,17476,34952,61440] BT.lf)) [6,15,3840,4369,8946,17476,34952,61680] (BT.nd (BT.nd BT.lf [6,15,3840,4369,8946,17476,34952,61986] BT.lf) [6,15,3840,4369,8946,17476,34952,62194] (BT.nd BT.lf [6,15,3840,4369,8946,17476,34952,62532] BT.lf))))))) [6,15,3840,4369,8946,17476,34952,63624] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,8946,17476,35064,61440] BT.lf) [6,15,3840,4369,8946,17476,36744,61440] BT.lf) [6,15,3840,4369,8946,17476,43690,61440] (BT.nd BT.lf [6,15,3840,4369,8946,17476,43770,61440] BT.lf)) [6,15,3840,4369,8946,17476,52428,61440] (BT.nd (BT.nd BT.lf [6,15,3840,4369,8946,17476,61166,61440] BT.lf) [6,15,3840,4369,8946,17476,61440,63624] (BT.nd BT.lf [6,15,3840,4369,8946,17476,63624] BT.lf))) [6,15,3840,4369,8946,17487] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,8946,20292] BT.lf) [6,15,3840,4369,8946,20292,34952,61440] BT.lf) [6,15,3840,4369,8946,21845] (BT.nd BT.lf [6,15,3840,4369,8946,43690] BT.lf)) [6,15,3840,4369,8946,48059] (BT.nd (BT.nd BT.lf [6,15,3840,4369,8959,17476] BT.lf) [6,15,3840,4369,13107,63624] (BT.nd BT.lf [6,15,3840,4369,13299,17476] BT.lf)))) [6,15,3840,4369,17476,25122] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,17476,30471] BT.lf) [6,15,3840,4369,17476,34952,35064,61986] BT.lf) [6,15,3840,4369,17476,35016] (BT.nd BT.lf [6,15,3840,4369,17476,35064] BT.lf)) [6,15,3840,4369,17476,35064,61440,61986] (BT.nd (BT.nd BT.lf [6,15,3840,4369,17476,35064,61986] BT.lf) [6,15,3840,4369,17476,35071] (BT.nd BT.lf [6,15,3840,4369,17476,39417] BT.lf))) [6,15,3840,4369,17476,51336] (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,17476,56589] BT.lf) [6,15,3840,4369,17476,61952] (BT.nd BT.lf [6,15,3840,4369,17476,61986] BT.lf)) [6,15,3840,4369,17476,61999] (BT.nd (BT.nd BT.lf [6,15,3840,4369,17476,62259] BT.lf) [6,15,3840,4369,17476,63488] (BT.nd BT.lf [6,15,3840,4369,17476,63624] BT.lf))))) [6,15,3840,4369,17476,63631] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,17476,63897] BT.lf) [6,15,3840,4369,17487,35064] BT.lf) [6,15,3840,4369,17487,61986] (BT.nd BT.lf [6,15,3840,4369,17487,63624] BT.lf)) [6,15,3840,4369,19524,61440] (BT.nd (BT.nd BT.lf [6,15,3840,4369,20292,61986] BT.lf) [6,15,3840,4369,21845,35064] (BT.nd BT.lf [6,15,3840,4369,21845,61986] BT.lf))) [6,15,3840,4369,21845,63624] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,25122,34952] BT.lf) [6,15,3840,4369,26214,61986] BT.lf) [6,15,3840,4369,30583,61986] (BT.nd BT.lf [6,15,3840,4369,34952,61986] BT.lf)) [6,15,3840,4369,34952,61999] (BT.nd (BT.nd BT.lf [6,15,3840,4369,34952,62259] BT.lf) [6,15,3840,4369,34952,64170] (BT.nd BT.lf [6,15,3840,4369,34952,64443] BT.lf)))) [6,15,3840,4369,34959,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,35064,43690] BT.lf) [6,15,3840,4369,35064,48059] BT.lf) [6,15,3840,4369,36744,61986] (BT.nd BT.lf [6,15,3840,4369,39321,61986] BT.lf)) [6,15,3840,4369,43690,61986] (BT.nd (BT.nd BT.lf [6,15,3840,4369,43690,63624] BT.lf) [6,15,3840,4369,48059,61986] (BT.nd BT.lf [6,15,3840,4369,48059,63624] BT.lf))) [6,15,3840,4369,52428,63624] (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,56797,63624] BT.lf) [6,15,3840,4369,61986,62532] (BT.nd BT.lf [6,15,3840,4369,61986,63078] BT.lf)) [6,15,3840,4369,61986,63624] (BT.nd (BT.nd BT.lf [6,15,3840,4369,61986,64170] BT.lf) [6,15,3840,4369,62532,63624] (BT.nd BT.lf [6,15,3840,4369,63624,64170] BT.lf)))))) [6,15,3840,4369,63624,64716] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4383,8738,17476,35064,61440] BT.lf) [6,15,3840,4383,8946,17476,34952,61440] BT.lf) [6,15,3840,4433,8738] (BT.nd BT.lf [6,15,3840,4433,8738,17476] BT.lf)) [6,15,3840,4433,8738,34952] (BT.nd (BT.nd BT.lf [6,15,3840,4433,8738,61440] BT.lf) [6,15,3840,4433,17476,34952] (BT.nd BT.lf [6,15,3840,4593,8738,17476,61713] BT.lf))) [6,15,3840,4593,8738,21845] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4593,8738,30583] BT.lf) [6,15,3840,4593,8738,34952] BT.lf) [6,15,3840,4593,8738,34959] (BT.nd BT.lf [6,15,3840,4593,8738,36744] BT.lf)) [6,15,3840,4593,8738,43690] (BT.nd (BT.nd BT.lf [6,15,3840,4593,8751,34952] BT.lf) [6,15,3840,4593,21845,34952] (BT.nd BT.lf [6,15,3840,4593,34952,43690] BT.lf)))) [6,15,3840,4593,34952,56797] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,6417,17476,61440] BT.lf) [6,15,3840,7953,8738,63624] BT.lf) [6,15,3840,7953,8946,17476] (BT.nd BT.lf [6,15,3840,7953,8946,17476,34952,61440] BT.lf)) [6,15,3840,7953,17476,61986] (BT.nd (BT.nd BT.lf [6,15,3840,7953,34952,61986] BT.lf) [6,15,3840,8177,8738,34952] (BT.nd BT.lf [6,15,3840,8738,13107,63624] BT.lf))) [6,15,3840,8738,13299,34952] (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,8738,16388,34952] BT.lf) [6,15,3840,8738,17412,34952] (BT.nd BT.lf [6,15,3840,8738,17476,20753] BT.lf)) [6,15,3840,8738,17476,35016] (BT.nd (BT.nd BT.lf [6,15,3840,8738,17476,51336] BT.lf) [6,15,3840,8738,34952,39417] (BT.nd BT.lf [6,15,3840,8738,34952,48123] BT.lf))))) [6,15,3840,8738,34952,60942] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,8738,52428,63624] BT.lf) [6,15,3840,8738,61166,63624] BT.lf) [6,15,3840,8802,17476,34952] (BT.nd BT.lf [6,15,3840,8946,17476,21845] BT.lf)) [6,15,3840,8946,17476,43690] (BT.nd (BT.nd BT.lf [6,15,3840,8946,17476,61166] BT.lf) [6,15,3840,13107,21845,61440] (BT.nd BT.lf [6,15,3840,13107,26214,61440] BT.lf))) [6,15,3840,13107,39321,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,13107,43690,61440] BT.lf) [6,15,3840,17476,20753,34952] (BT.nd BT.lf [6,15,3840,17476,21845,35064] BT.lf)) [6,15,3840,17476,21845,61986] (BT.nd (BT.nd BT.lf [6,15,3840,17476,21845,63624] BT.lf) [6,15,3840,17476,25122,34952] (BT.nd BT.lf [6,15,3840,17476,35064,43690] BT.lf)))) [6,15,3840,17476,35064,61166] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,17476,43690,61986] BT.lf) [6,15,3840,17476,43690,63624] BT.lf) [6,15,3840,17476,61166,61986] (BT.nd BT.lf [6,15,3840,17476,61166,63624] BT.lf)) [6,15,3840,21845,26214,61440] (BT.nd (BT.nd BT.lf [6,15,3840,21845,39321,61440] BT.lf) [6,15,3840,21845,52428,61440] (BT.nd BT.lf [6,15,3840,26214,34952,61986] BT.lf))) [6,15,3840,26214,43690,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,26214,52428,61440] BT.lf) [6,15,3840,34952,39321,61986] (BT.nd BT.lf [6,15,3840,34952,61166,61986] BT.lf)) [6,15,3840,39321,43690,61440] (BT.nd (BT.nd BT.lf [6,15,3840,39321,52428,61440] BT.lf) [6,15,3840,43690,52428,61440] (BT.nd BT.lf [6,15,3855,4369,8738,17476,35064,61440] BT.lf)))))))))) [6,15,3855,4369,8738,63624] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3855,4369,8946,17476] BT.lf) [6,15,3855,4369,8946,17476,34952,61440] BT.lf) [6,15,3855,4369,17476,35064] (BT.nd BT.lf [6,15,3855,4369,17476,61986] BT.lf)) [6,15,3855,4369,17476,63624] (BT.nd (BT.nd BT.lf [6,15,3855,4369,34952,61986] BT.lf) [6,15,3855,4593,8738,34952] (BT.nd BT.lf [6,15,3968,4369,8738,61440] BT.lf))) [6,15,4080,4369,8738,36744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,4080,4369,17476,35064] BT.lf) [6,15,4080,8738,17476,36744] BT.lf) [6,15,4095,4369,8738,36744] (BT.nd BT.lf [6,15,4095,4369,17476,35064] BT.lf)) [6,15,4095,8738,17476,36744] (BT.nd (BT.nd BT.lf [6,15,4369,4593,8738,20292] BT.lf) [6,15,4369,4593,8738,36744] (BT.nd BT.lf [6,15,4369,7953,8738,17476,35064,61440] BT.lf)))) [6,15,4369,7953,8946,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,7953,8946,17476,61440] BT.lf) [6,15,4369,8738,8946,17476,36744,61440] BT.lf) [6,15,4369,8738,8946,20292] (BT.nd BT.lf [6,15,4369,8738,8946,20292,34952,61440] BT.lf)) [6,15,4369,8738,8946,36744] (BT.nd (BT.nd BT.lf [6,15,4369,8738,16384,36744] BT.lf) [6,15,4369,8738,17476,20224] (BT.nd BT.lf [6,15,4369,8738,17476,20292,35064,61440] BT.lf))) [6,15,4369,8738,17476,35064,36744,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,8738,20224,34952] BT.lf) [6,15,4369,8738,20292,65280] (BT.nd BT.lf [6,15,4369,8738,20292,65295] BT.lf)) [6,15,4369,8738,28791,61440] (BT.nd (BT.nd BT.lf [6,15,4369,8738,35064,36744] BT.lf) [6,15,4369,8738,35064,63624] (BT.nd BT.lf [6,15,4369,8738,36744,36856] BT.lf))))) [6,15,4369,8738,36744,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,8738,36744,61455] BT.lf) [6,15,4369,8738,36744,61713] BT.lf) [6,15,4369,8738,36744,61986] (BT.nd BT.lf [6,15,4369,8738,36744,63624] BT.lf)) [6,15,4369,8738,36744,65280] (BT.nd (BT.nd BT.lf [6,15,4369,8738,36744,65295] BT.lf) [6,15,4369,8738,36744,65416] (BT.nd BT.lf [6,15,4369,8738,36751,61440] BT.lf))) [6,15,4369,8738,61440,65416] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,8738,61440,65423] BT.lf) [6,15,4369,8738,61680,63624] BT.lf) [6,15,4369,8738,61695,63624] (BT.nd BT.lf [6,15,4369,8738,62532,65280] BT.lf)) [6,15,4369,8738,62532,65295] (BT.nd (BT.nd BT.lf [6,15,4369,8738,63624,63736] BT.lf) [6,15,4369,8738,63624,65280] (BT.nd BT.lf [6,15,4369,8738,63624,65295] BT.lf)))) [6,15,4369,8738,63624,65416] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,8751,36744,61440] BT.lf) [6,15,4369,8946,17476,20292] BT.lf) [6,15,4369,8946,17476,20292,34952,61440] (BT.nd BT.lf [6,15,4369,8946,17476,61680] BT.lf)) [6,15,4369,8946,17476,61695] (BT.nd (BT.nd BT.lf [6,15,4369,8946,20292] BT.lf) [6,15,4369,8946,20292,34952] (BT.nd BT.lf [6,15,4369,8946,20292,34952,61440] BT.lf))) [6,15,4369,8946,20292,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,12066,17652,34952,61440] BT.lf) [6,15,4369,13107,36744,61440] (BT.nd BT.lf [6,15,4369,17476,20224,34952] BT.lf)) [6,15,4369,17476,20292,35064] (BT.nd (BT.nd BT.lf [6,15,4369,17476,30471,61440] BT.lf) [6,15,4369,17476,35064,36744] (BT.nd BT.lf [6,15,4369,17476,35064,36856] BT.lf)))))) [6,15,4369,17476,35064,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,17476,35064,61455] BT.lf) [6,15,4369,17476,35064,61680] BT.lf) [6,15,4369,17476,35064,61695] (BT.nd BT.lf [6,15,4369,17476,35064,62532] BT.lf)) [6,15,4369,17476,35064,63624] (BT.nd (BT.nd BT.lf [6,15,4369,17476,35064,63736] BT.lf) [6,15,4369,17476,35071,61440] (BT.nd BT.lf [6,15,4369,17476,36744,63624] BT.lf))) [6,15,4369,17476,61440,63736] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,17476,61440,63743] BT.lf) [6,15,4369,17476,61680,61986] BT.lf) [6,15,4369,17476,61680,63624] (BT.nd BT.lf [6,15,4369,17476,61695,61986] BT.lf)) [6,15,4369,17476,61695,63624] (BT.nd (BT.nd BT.lf [6,15,4369,17476,63624,63736] BT.lf) [6,15,4369,17476,63624,65280] (BT.nd BT.lf [6,15,4369,17476,63624,65295] BT.lf)))) [6,15,4369,17476,63624,65416] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,17487,35064,61440] BT.lf) [6,15,4369,21845,35064,61440] BT.lf) [6,15,4369,34952,35064,62532] (BT.nd BT.lf [6,15,4369,34952,36744,61986] BT.lf)) [6,15,4369,34952,61680,61986] (BT.nd (BT.nd BT.lf [6,15,4369,34952,61695,61986] BT.lf) [6,15,4369,34952,62532,65280] (BT.nd BT.lf [6,15,4369,34952,62532,65295] BT.lf))) [6,15,4369,35064,43690,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,35064,48059,61440] BT.lf) [6,15,4369,35064,61440,62532] (BT.nd BT.lf [6,15,4369,36744,52428,61440] BT.lf)) [6,15,4369,36744,56797,61440] (BT.nd (BT.nd BT.lf [6,15,4369,36744,61440,61986] BT.lf) [6,15,4593,8738,17476,36744] (BT.nd BT.lf [6,15,4593,8738,34952,36744] BT.lf))))) [6,15,4593,8738,34952,61680] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,4593,8738,34952,61695] BT.lf) [6,15,4593,8738,36744] BT.lf) [6,15,4593,8738,36744,61440] (BT.nd BT.lf [6,15,4593,12066,17476,34952,61440] BT.lf)) [6,15,7953,8738,8946,17476,34952,61440] (BT.nd (BT.nd BT.lf [6,15,7953,8738,20292,61440] BT.lf) [6,15,7953,8738,36744,61440] (BT.nd BT.lf [6,15,7953,8946,17476,34952,61440] BT.lf))) [6,15,7953,8946,17476,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,8738,8946,17476,36744] BT.lf) [6,15,8738,8946,20292,34952] BT.lf) [6,15,8738,13107,36744,61440] (BT.nd BT.lf [6,15,8738,16384,17476,36744] BT.lf)) [6,15,8738,17476,20224,34952] (BT.nd (BT.nd BT.lf [6,15,8738,17476,28791,61440] BT.lf) [6,15,8738,17476,35064,36744] (BT.nd BT.lf [6,15,8738,17476,35064,63624] BT.lf)))) [6,15,8738,17476,36744,36856] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,8738,17476,36744,61440] BT.lf) [6,15,8738,17476,36744,61455] BT.lf) [6,15,8738,17476,36744,61713] (BT.nd BT.lf [6,15,8738,17476,36744,61986] BT.lf)) [6,15,8738,17476,36744,63624] (BT.nd (BT.nd BT.lf [6,15,8738,17476,36744,65280] BT.lf) [6,15,8738,17476,36744,65295] (BT.nd BT.lf [6,15,8738,17476,36744,65416] BT.lf))) [6,15,8738,17652,36744,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,15,8738,20292,34952,35064] BT.lf) [6,15,8738,20292,34952,65280] (BT.nd BT.lf [6,15,8738,20292,34952,65295] BT.lf)) [6,15,8738,20292,36744,61440] (BT.nd (BT.nd BT.lf [6,15,8738,26214,36744,61440] BT.lf) [6,15,8738,36744,39321,61440] (BT.nd BT.lf [6,15,8738,36744,40857,61440] BT.lf))))))) [6,15,8738,36744,48059,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,8738,36744,52428,61440] BT.lf) [6,15,8738,36744,53196,61440] BT.lf) [6,15,8738,36744,61166,61440] (BT.nd BT.lf [6,15,17476,21845,35064,61440] BT.lf)) [6,15,17476,26214,36744,61440] (BT.nd (BT.nd BT.lf [6,15,17476,35064,43690,61440] BT.lf) [6,15,17476,35064,61166,61440] (BT.nd BT.lf [6,15,17476,36744,39321,61440] BT.lf))) [6,15,17476,36744,56797,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,64,79,3840,4369,8738] BT.lf) [6,64,240,4369,8751,61440] BT.lf) [6,64,240,7953,8738,61440] (BT.nd BT.lf [6,64,3840,3855,4369,8738] BT.lf)) [6,64,3840,4369,8738,61680] (BT.nd (BT.nd BT.lf [6,64,3840,4369,8738,65520] BT.lf) [6,79,240,3840,4369,8738] (BT.nd BT.lf [6,79,240,4369,8738,61440] BT.lf)))) [6,79,3840,4369,8738] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,79,3840,4369,8738,17476] BT.lf) [6,79,3840,4369,8738,34952] BT.lf) [6,79,3840,4369,8738,61440] (BT.nd BT.lf [6,79,3840,4369,17476,34952] BT.lf)) [6,79,3840,8738,17476,34952] (BT.nd (BT.nd BT.lf [6,128,240,4369,8751,61440] BT.lf) [6,128,240,7953,8738,61440] (BT.nd BT.lf [6,143,240,3840,4369,8738] BT.lf))) [6,143,240,4369,8738,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,176,3840,4369,8738,61440] BT.lf) [6,240,255,4369,8738,20292] (BT.nd BT.lf [6,240,255,4369,8738,36744] BT.lf)) [6,240,255,4369,8738,62532] (BT.nd (BT.nd BT.lf [6,240,255,4369,8738,63624] BT.lf) [6,240,255,4369,17476,63624] (BT.nd BT.lf [6,240,255,4369,34952,62532] BT.lf))))) [6,240,255,8738,17476,36744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,255,8738,20292,34952] BT.lf) [6,240,512,4369,4383,17476,61440] BT.lf) [6,240,512,4383,8738,17476,34952,61440] (BT.nd BT.lf [6,240,512,7953,17476,61440] BT.lf)) [6,240,527,3840,4369,17476] (BT.nd (BT.nd BT.lf [6,240,527,4369,8738,17476,34952,61440] BT.lf) [6,240,527,4369,17476,61440] (BT.nd BT.lf [6,240,2063,3840,4369,17476] BT.lf))) [6,240,3072,4369,17476,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,3328,4369,17476,61440] BT.lf) [6,240,3840,4096,4383,8738,17476,34952] BT.lf) [6,240,3840,4369,4383,8738,17476,63624] (BT.nd BT.lf [6,240,3840,4369,4383,8738,34952,62532] BT.lf)) [6,240,3840,4369,4383,8738,62532] (BT.nd (BT.nd BT.lf [6,240,3840,4369,4383,17476,34952,61986] BT.lf) [6,240,3840,4369,4383,17476,61986] (BT.nd BT.lf [6,240,3840,4369,8738,61504] BT.lf)))) [6,240,3840,4369,8738,61568] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,3840,4369,8751,17487] BT.lf) [6,240,3840,4369,8751,34959] BT.lf) [6,240,3840,4369,8866,61440] (BT.nd BT.lf [6,240,3840,4369,17476,61952] BT.lf)) [6,240,3840,4369,17476,63488] (BT.nd (BT.nd BT.lf [6,240,3840,4369,17487,34959] BT.lf) [6,240,3840,4369,19524,61440] (BT.nd BT.lf [6,240,3840,4369,61986,62532] BT.lf))) [6,240,3840,4369,61986,63624] (BT.nd (BT.nd (BT.nd BT.lf [6,240,3840,4369,62532,63624] BT.lf) [6,240,3840,4383,8738,17476,34952,61440] (BT.nd BT.lf [6,240,3840,4383,8738,17476,34952,61680] BT.lf)) [6,240,3840,4383,8738,17476,34952,61986] (BT.nd (BT.nd BT.lf [6,240,3840,4383,8738,17476,34952,62532] BT.lf) [6,240,3840,4383,8738,17476,34952,63624] (BT.nd BT.lf [6,240,3840,4383,8738,17476,35064,61440] BT.lf)))))) [6,240,3840,4383,8738,17476,43690,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,3840,4383,8738,17476,52428,61440] BT.lf) [6,240,3840,4383,8738,17476,61166,61440] BT.lf) [6,240,3840,4383,8738,17476,61440,63624] (BT.nd BT.lf [6,240,3840,4383,8738,17476,63624] BT.lf)) [6,240,3840,4383,8738,34952,61440,62532] (BT.nd (BT.nd BT.lf [6,240,3840,4383,8738,34952,62532] BT.lf) [6,240,3840,4383,8946,17476,34952,61440] (BT.nd BT.lf [6,240,3840,4383,17476,34952,61440,61986] BT.lf))) [6,240,3840,4383,17476,34952,61986] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,3840,4433,8738,61440] BT.lf) [6,240,3840,6417,17476,61440] BT.lf) [6,240,3840,8738,17476,34959,61713] (BT.nd BT.lf [6,240,3840,8738,17487,34952,61713] BT.lf)) [6,240,3840,8751,17476,34952,61713] (BT.nd (BT.nd BT.lf [6,240,3840,13107,21845,61440] BT.lf) [6,240,3840,13107,26214,61440] (BT.nd BT.lf [6,240,3840,13107,39321,61440] BT.lf)))) [6,240,3840,13107,43690,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,3840,21845,26214,61440] BT.lf) [6,240,3840,21845,39321,61440] BT.lf) [6,240,3840,21845,52428,61440] (BT.nd BT.lf [6,240,3840,26214,43690,61440] BT.lf)) [6,240,3840,26214,52428,61440] (BT.nd (BT.nd BT.lf [6,240,3840,39321,43690,61440] BT.lf) [6,240,3840,39321,52428,61440] (BT.nd BT.lf [6,240,3840,43690,52428,61440] BT.lf))) [6,240,3841,4369,8738,17476,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,240,3855,4369,8751,17476] BT.lf) [6,240,3855,4369,8751,34952] (BT.nd BT.lf [6,240,3855,4383,8738,17476,34952,61440] BT.lf)) [6,240,3855,7953,8738,17476] (BT.nd (BT.nd BT.lf [6,240,3855,7953,8738,34952] BT.lf) [6,240,3904,4369,8738,61440] (BT.nd BT.lf [6,240,3968,4369,8738,61440] BT.lf))))) [6,240,4095,4369,8751,17476] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,4095,4369,8751,34952] BT.lf) [6,240,4095,7953,8738,17476] BT.lf) [6,240,4095,7953,8738,34952] (BT.nd BT.lf [6,240,4369,4383,8738,20292,61440] BT.lf)) [6,240,4369,4383,8738,62532] (BT.nd (BT.nd BT.lf [6,240,4369,4383,8738,63624] BT.lf) [6,240,4369,4383,17476,63624] (BT.nd BT.lf [6,240,4369,4383,34952,62532] BT.lf))) [6,240,4369,8738,8751,62532] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,4369,8738,8751,63624] BT.lf) [6,240,4369,8738,20292,65280] BT.lf) [6,240,4369,8738,20292,65520] (BT.nd BT.lf [6,240,4369,8738,36744,65280] BT.lf)) [6,240,4369,8738,36744,65520] (BT.nd (BT.nd BT.lf [6,240,4369,8738,62532,65280] BT.lf) [6,240,4369,8738,62532,65520] (BT.nd BT.lf [6,240,4369,8738,63624,65280] BT.lf)))) [6,240,4369,8738,63624,65520] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,4369,8751,17476,36744,61440] BT.lf) [6,240,4369,8751,17476,61440] BT.lf) [6,240,4369,8751,17476,61680] (BT.nd BT.lf [6,240,4369,8751,17476,62532] BT.lf)) [6,240,4369,8751,17487,61440] (BT.nd (BT.nd BT.lf [6,240,4369,8751,20292,61440] BT.lf) [6,240,4369,8751,21845,61440] (BT.nd BT.lf [6,240,4369,8751,26214,61440] BT.lf))) [6,240,4369,8751,26223,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,240,4369,8751,30583,61440] BT.lf) [6,240,4369,8751,34952,61440] (BT.nd BT.lf [6,240,4369,8751,34952,61680] BT.lf)) [6,240,4369,8751,34952,63624] (BT.nd (BT.nd BT.lf [6,240,4369,8751,34959,61440] BT.lf) [6,240,4369,8751,36744,61440] (BT.nd BT.lf [6,240,4369,8751,39321,61440] BT.lf)))))))) [6,240,4369,8751,43690,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,4369,8751,43695,61440] BT.lf) [6,240,4369,8751,48059,61440] BT.lf) [6,240,4369,8751,61440,62532] (BT.nd BT.lf [6,240,4369,8751,61440,63624] BT.lf)) [6,240,4369,8959,17476,61440] (BT.nd (BT.nd BT.lf [6,240,4369,13119,17476,61440] BT.lf) [6,240,4369,13119,34952,61440] (BT.nd BT.lf [6,240,4369,17476,56784,61440] BT.lf))) [6,240,4369,17476,61440,61999] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,4369,17476,61440,62207] BT.lf) [6,240,4369,17476,63624,65280] BT.lf) [6,240,4369,17476,63624,65520] (BT.nd BT.lf [6,240,4369,17487,34959,61440] BT.lf)) [6,240,4369,34952,56784,61440] (BT.nd (BT.nd BT.lf [6,240,4369,34952,61440,61999] BT.lf) [6,240,4369,34952,62532,65280] (BT.nd BT.lf [6,240,4369,34952,62532,65520] BT.lf)))) [6,240,4383,7953,8738,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,4383,7953,8738,17476,61440] BT.lf) [6,240,4383,7967,8738,17476,34952,61440] BT.lf) [6,240,4383,8738,17476,20292,34952,61440] (BT.nd BT.lf [6,240,4383,8738,17476,34952,36744,61440] BT.lf)) [6,240,4383,8738,17476,63624] (BT.nd (BT.nd BT.lf [6,240,4383,8738,34952,62532] BT.lf) [6,240,4593,8751,34952,61440] (BT.nd BT.lf [6,240,7953,7967,8738,17476,61440] BT.lf))) [6,240,7953,8738,17476,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,240,7953,8738,17476,61680] BT.lf) [6,240,7953,8738,17487,61440] (BT.nd BT.lf [6,240,7953,8738,20292,61440] BT.lf)) [6,240,7953,8738,21845,61440] (BT.nd (BT.nd BT.lf [6,240,7953,8738,24405,61440] BT.lf) [6,240,7953,8738,26214,61440] (BT.nd BT.lf [6,240,7953,8738,30583,61440] BT.lf))))) [6,240,7953,8738,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,7953,8738,34952,61680] BT.lf) [6,240,7953,8738,34959,61440] BT.lf) [6,240,7953,8738,36744,61440] (BT.nd BT.lf [6,240,7953,8738,39321,61440] BT.lf)) [6,240,7953,8738,40857,61440] (BT.nd (BT.nd BT.lf [6,240,7953,8738,43690,61440] BT.lf) [6,240,7953,8738,48059,61440] (BT.nd BT.lf [6,240,7953,8738,61440,62532] BT.lf))) [6,240,7953,8738,61440,63624] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,7953,8946,17476,61440] BT.lf) [6,240,7953,17476,26214,61440] BT.lf) [6,240,7953,17476,39321,61440] (BT.nd BT.lf [6,240,7953,17476,56797,61440] BT.lf)) [6,240,7953,17476,61440,61986] (BT.nd (BT.nd BT.lf [6,240,7953,21845,34952,61440] BT.lf) [6,240,7953,34952,43690,61440] (BT.nd BT.lf [6,240,7953,34952,56797,61440] BT.lf)))) [6,240,7953,34952,61440,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,240,8177,8738,34952,61440] BT.lf) [6,240,8738,16179,17476,61440] BT.lf) [6,240,8738,16179,34952,61440] (BT.nd BT.lf [6,240,8738,17476,36744,65280] BT.lf)) [6,240,8738,17476,36744,65520] (BT.nd (BT.nd BT.lf [6,240,8738,17476,57582,61440] BT.lf) [6,240,8738,20292,34952,65280] (BT.nd BT.lf [6,240,8738,20292,34952,65520] BT.lf))) [6,240,8738,20292,36744,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,240,8738,34952,57582,61440] BT.lf) [6,240,8751,17476,21845,61440] (BT.nd BT.lf [6,240,8751,17476,43690,61440] BT.lf)) [6,240,8751,17476,61166,61440] (BT.nd (BT.nd BT.lf [6,240,8751,26214,34952,61440] BT.lf) [6,240,8751,34952,39321,61440] (BT.nd BT.lf [6,240,8751,34952,61166,61440] BT.lf)))))) [6,255,3840,4369,8738,17487] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,255,3840,4369,17487,34952] BT.lf) [6,255,3840,8738,17652,34952] BT.lf) [6,255,3855,4369,8738,17476] (BT.nd BT.lf [6,255,3855,4369,8738,34952] BT.lf)) [6,255,3855,4369,17476,34952] (BT.nd (BT.nd BT.lf [6,255,3855,8738,17476,34952] BT.lf) [6,255,4080,4369,8738,17476] (BT.nd BT.lf [6,255,4080,4369,8738,34952] BT.lf))) [6,255,4080,4369,17476,34952] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,255,4080,8738,17476,34952] BT.lf) [6,255,4369,8738,17476,61455] BT.lf) [6,255,4369,8738,17476,61680] (BT.nd BT.lf [6,255,4369,8738,17487,61440] BT.lf)) [6,255,4369,8738,34952,61455] (BT.nd (BT.nd BT.lf [6,255,4369,8738,34952,61680] BT.lf) [6,255,4369,17476,34952,61455] (BT.nd BT.lf [6,255,4369,17476,34952,61680] BT.lf)))) [6,255,4369,17487,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,255,8738,17476,34952,61455] BT.lf) [6,255,8738,17476,34952,61680] BT.lf) [6,255,8738,17652,34952,61440] (BT.nd BT.lf [6,512,3840,4369,17487,61440] BT.lf)) [6,527,3840,4369,17476,61440] (BT.nd (BT.nd BT.lf [6,752,3840,4369,17476,61440] BT.lf) [6,2048,3840,4369,17487,61440] (BT.nd BT.lf [6,2063,3840,4369,17476,61440] BT.lf))) [6,2288,3840,4369,17476,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,3840,3855,4369,8738,63624] BT.lf) [6,3840,3855,4369,8946,17476] (BT.nd BT.lf [6,3840,3855,4369,17476,35064] BT.lf)) [6,3840,3855,4369,17476,61986] (BT.nd (BT.nd BT.lf [6,3840,3855,4369,17476,63624] BT.lf) [6,3840,3855,4369,34952,61986] (BT.nd BT.lf [6,3840,3855,4593,8738,34952] BT.lf))))) [6,3840,4095,4369,8738,17487] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4095,4369,17487,34952] BT.lf) [6,3840,4095,8738,17652,34952] BT.lf) [6,3840,4369,4383,8738,17476,35064,61440] (BT.nd BT.lf [6,3840,4369,4383,8946,17476,34952,61440] BT.lf)) [6,3840,4369,4383,8946,17476,61440] (BT.nd (BT.nd BT.lf [6,3840,4369,8738,16384,17487] BT.lf) [6,3840,4369,8738,17487,61440] (BT.nd BT.lf [6,3840,4369,8738,17487,61713] BT.lf))) [6,3840,4369,8738,17487,61986] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,8738,17487,65280] BT.lf) [6,3840,4369,8738,20303,61440] BT.lf) [6,3840,4369,8738,48048,61440] (BT.nd BT.lf [6,3840,4369,8738,61440,62543] BT.lf)) [6,3840,4369,8738,61440,65359] (BT.nd (BT.nd BT.lf [6,3840,4369,8738,61680,63624] BT.lf) [6,3840,4369,8738,63624,65520] (BT.nd BT.lf [6,3840,4369,8751,17487,61440] BT.lf)))) [6,3840,4369,8751,34959,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,8946,17476,61680] BT.lf) [6,3840,4369,8946,17476,65520] BT.lf) [6,3840,4369,8946,17487,61440] (BT.nd BT.lf [6,3840,4369,13107,17487,61440] BT.lf)) [6,3840,4369,16384,17487,34952] (BT.nd (BT.nd BT.lf [6,3840,4369,17476,17487,61986] BT.lf) [6,3840,4369,17476,17487,63624] (BT.nd BT.lf [6,3840,4369,17476,35064,61680] BT.lf))) [6,3840,4369,17476,35064,65520] (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,17476,61680,61986] BT.lf) [6,3840,4369,17476,61680,63624] (BT.nd BT.lf [6,3840,4369,17476,61986,65520] BT.lf)) [6,3840,4369,17476,63624,65520] (BT.nd (BT.nd BT.lf [6,3840,4369,17487,26214,61440] BT.lf) [6,3840,4369,17487,26223,61440] (BT.nd BT.lf [6,3840,4369,17487,30583,61440] BT.lf))))))) [6,3840,4369,17487,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,17487,34952,61713] BT.lf) [6,3840,4369,17487,34952,63624] BT.lf) [6,3840,4369,17487,34952,65280] (BT.nd BT.lf [6,3840,4369,17487,34959,61440] BT.lf)) [6,3840,4369,17487,35064,61440] (BT.nd (BT.nd BT.lf [6,3840,4369,17487,39321,61440] BT.lf) [6,3840,4369,17487,52428,61440] (BT.nd BT.lf [6,3840,4369,17487,52431,61440] BT.lf))) [6,3840,4369,17487,56797,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,17487,61440,61986] BT.lf) [6,3840,4369,17487,61440,63624] BT.lf) [6,3840,4369,34952,48048,61440] (BT.nd BT.lf [6,3840,4369,34952,61440,62543] BT.lf)) [6,3840,4369,34952,61680,61986] (BT.nd (BT.nd BT.lf [6,3840,4369,34952,61986,65520] BT.lf) [6,3840,4383,8738,8946,17476,34952,61440] (BT.nd BT.lf [6,3840,4383,8738,17476,34952,35064,61440] BT.lf)))) [6,3840,4383,8738,17476,35064,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4383,8946,17476,34952,61440] BT.lf) [6,3840,4593,8738,17476,34959,61440] BT.lf) [6,3840,4593,8738,34952,61680] (BT.nd BT.lf [6,3840,4593,8738,34952,65520] BT.lf)) [6,3840,4593,8738,34959,61440] (BT.nd (BT.nd BT.lf [6,3840,4593,8751,17476,34952,61440] BT.lf) [6,3840,4593,8751,34952,61440] (BT.nd BT.lf [6,3840,7953,8738,17487,61440] BT.lf))) [6,3840,8738,13107,17487,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,3840,8738,17487,34952,61713] BT.lf) [6,3840,8738,17487,52428,61440] (BT.nd BT.lf [6,3840,8738,17487,61166,61440] BT.lf)) [6,3840,8738,17652,21845,61440] (BT.nd (BT.nd BT.lf [6,3840,8738,17652,30583,61440] BT.lf) [6,3840,8738,17652,34952,61440] (BT.nd BT.lf [6,3840,8738,17652,34952,65280] BT.lf))))) [6,3840,8738,17652,36744,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,8738,17652,43690,61440] BT.lf) [6,3840,8738,20468,34952,61440] BT.lf) [6,3840,8738,34952,47883,61440] (BT.nd BT.lf [6,3840,17487,26214,34952,61440] BT.lf)) [6,3840,17487,34952,39321,61440] (BT.nd (BT.nd BT.lf [6,3840,17487,34952,61166,61440] BT.lf) [6,3840,17652,21845,34952,61440] (BT.nd BT.lf [6,3840,17652,34952,43690,61440] BT.lf))) [6,3840,17652,34952,56797,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3855,4080,4369,8738,17476] BT.lf) [6,3855,4080,4369,8738,34952] BT.lf) [6,3855,4080,4369,17476,34952] (BT.nd BT.lf [6,3855,4080,8738,17476,34952] BT.lf)) [6,3855,4369,8738,17476,61455] (BT.nd (BT.nd BT.lf [6,3855,4369,8738,17476,65280] BT.lf) [6,3855,4369,8738,34952,61455] (BT.nd BT.lf [6,3855,4369,8738,34952,65280] BT.lf)))) [6,3855,4369,8751,17476,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3855,4369,8751,34952,61440] BT.lf) [6,3855,4369,17476,34952,61455] BT.lf) [6,3855,4369,17476,34952,65280] (BT.nd BT.lf [6,3855,7953,8738,17476,61440] BT.lf)) [6,3855,7953,8738,34952,61440] (BT.nd (BT.nd BT.lf [6,3855,8738,17476,34952,61455] BT.lf) [6,3855,8738,17476,34952,65280] (BT.nd BT.lf [6,4080,4369,8738,17476,61680] BT.lf))) [6,4080,4369,8738,17476,65280] (BT.nd (BT.nd (BT.nd BT.lf [6,4080,4369,8738,34952,61680] BT.lf) [6,4080,4369,8738,34952,65280] (BT.nd BT.lf [6,4080,4369,8738,36744,61440] BT.lf)) [6,4080,4369,17476,34952,61680] (BT.nd (BT.nd BT.lf [6,4080,4369,17476,34952,65280] BT.lf) [6,4080,4369,17476,35064,61440] (BT.nd BT.lf [6,4080,8738,17476,34952,61680] BT.lf)))))) [6,4080,8738,17476,34952,65280] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,4080,8738,17476,36744,61440] BT.lf) [6,4369,4383,17476,35064,61440] BT.lf) [6,4369,8738,17476,61455,61680] (BT.nd BT.lf [6,4369,8738,17476,61455,65280] BT.lf)) [6,4369,8738,17476,61680,65280] (BT.nd (BT.nd BT.lf [6,4369,8738,17487,61440,61695] BT.lf) [6,4369,8738,17487,61440,65280] (BT.nd BT.lf [6,4369,8738,34952,61455,61680] BT.lf))) [6,4369,8738,34952,61455,65280] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,4369,8738,34952,61680,65280] BT.lf) [6,4369,8738,36744,61440,61455] BT.lf) [6,4369,8738,36744,61440,65520] (BT.nd BT.lf [6,4369,8751,17476,61440,61680] BT.lf)) [6,4369,8751,17476,61440,65295] (BT.nd (BT.nd BT.lf [6,4369,8751,34952,35064,61440] BT.lf) [6,4369,8751,34952,61440,61680] (BT.nd BT.lf [6,4369,8751,34952,61440,65295] BT.lf)))) [6,4369,12066,17652,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,4369,17476,34952,61455,61680] BT.lf) [6,4369,17476,34952,61455,65280] BT.lf) [6,4369,17476,34952,61680,65280] (BT.nd BT.lf [6,4369,17476,35064,61440,61455] BT.lf)) [6,4369,17476,35064,61440,65520] (BT.nd (BT.nd BT.lf [6,4369,17487,34952,36744,61440] BT.lf) [6,4369,17487,34952,61440,61695] (BT.nd BT.lf [6,4369,17487,34952,61440,65280] BT.lf))) [6,4383,8738,17476,35064,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,7953,8738,17476,17652,61440] BT.lf) [6,7953,8738,17476,61440,61680] (BT.nd BT.lf [6,7953,8738,17476,61440,65295] BT.lf)) [6,7953,8738,34952,61440,61680] (BT.nd (BT.nd BT.lf [6,7953,8738,34952,61440,65295] BT.lf) [6,8738,12066,17652,34952,61440] (BT.nd BT.lf [6,8738,17476,17487,36744,61440] BT.lf))))) [6,8738,17476,34952,61455,61680] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,8738,17476,34952,61455,65280] BT.lf) [6,8738,17476,34952,61680,65280] BT.lf) [6,8738,17476,36744,61440,61455] (BT.nd BT.lf [6,8738,17476,36744,61440,65520] BT.lf)) [6,8738,17652,34952,61440,61695] (BT.nd (BT.nd BT.lf [6,8738,17652,34952,61440,65280] BT.lf) [7,1,240,3840,4369,8738,17476,61440] (BT.nd BT.lf [7,8,15,240,3840,4369,8738,17476,61440] BT.lf))) [7,15,64,240,3840,4369,8738] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,64,240,4369,8738,61440] BT.lf) [7,15,64,3840,4369,8738] BT.lf) [7,15,64,3840,4369,8738,17476] (BT.nd BT.lf [7,15,64,3840,4369,8738,34952] BT.lf)) [7,15,64,3840,4369,8738,61440] (BT.nd (BT.nd BT.lf [7,15,64,3840,4369,17476,34952] BT.lf) [7,15,64,3840,8738,17476,34952] (BT.nd BT.lf [7,15,128,240,3840,4369,8738] BT.lf)))) [7,15,128,240,4369,8738,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,128,3840,4369,8738,61440] BT.lf) [7,15,240,512,3840,4369,17476] BT.lf) [7,15,240,512,4369,8738,17476,34952,61440] (BT.nd BT.lf [7,15,240,512,4369,17476,61440] BT.lf)) [7,15,240,2048,3840,4369,17476] (BT.nd (BT.nd BT.lf [7,15,240,2048,4369,17476,61440] BT.lf) [7,15,240,3840,4096,4369,8738,17476,34952] (BT.nd BT.lf [7,15,240,3840,4369,8738,17476] BT.lf))) [7,15,240,3840,4369,8738,17476,34952,61440] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,8738,17476,34952,61680] BT.lf) [7,15,240,3840,4369,8738,17476,34952,61986] (BT.nd BT.lf [7,15,240,3840,4369,8738,17476,34952,62532] BT.lf)) [7,15,240,3840,4369,8738,17476,34952,63624] (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,8738,17476,35064,61440] BT.lf) [7,15,240,3840,4369,8738,17476,36744,61440] (BT.nd BT.lf [7,15,240,3840,4369,8738,17476,43690,61440] BT.lf))))))))) [7,15,240,3840,4369,8738,17476,52428,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,8738,17476,61166,61440] BT.lf) [7,15,240,3840,4369,8738,17476,61440,63624] BT.lf) [7,15,240,3840,4369,8738,17476,61713] (BT.nd BT.lf [7,15,240,3840,4369,8738,17476,63624] BT.lf)) [7,15,240,3840,4369,8738,17487] (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,8738,20292] BT.lf) [7,15,240,3840,4369,8738,20292,34952,61440] (BT.nd BT.lf [7,15,240,3840,4369,8738,21845] BT.lf))) [7,15,240,3840,4369,8738,26214] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,8738,30583] BT.lf) [7,15,240,3840,4369,8738,34952] BT.lf) [7,15,240,3840,4369,8738,34952,61440,62532] (BT.nd BT.lf [7,15,240,3840,4369,8738,34952,62532] BT.lf)) [7,15,240,3840,4369,8738,34959] (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,8738,36744] BT.lf) [7,15,240,3840,4369,8738,39321] (BT.nd BT.lf [7,15,240,3840,4369,8738,43690] BT.lf)))) [7,15,240,3840,4369,8738,48059] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,8738,62532] BT.lf) [7,15,240,3840,4369,8738,63624] BT.lf) [7,15,240,3840,4369,8751,17476] (BT.nd BT.lf [7,15,240,3840,4369,8751,34952] BT.lf)) [7,15,240,3840,4369,8946,17476] (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,8946,17476,34952,61440] BT.lf) [7,15,240,3840,4369,13107,17476] (BT.nd BT.lf [7,15,240,3840,4369,13107,34952] BT.lf))) [7,15,240,3840,4369,17476,26214] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,17476,30583] BT.lf) [7,15,240,3840,4369,17476,34952] (BT.nd BT.lf [7,15,240,3840,4369,17476,34952,61440,61986] BT.lf)) [7,15,240,3840,4369,17476,34952,61986] (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,17476,34959] BT.lf) [7,15,240,3840,4369,17476,35064] (BT.nd BT.lf [7,15,240,3840,4369,17476,39321] BT.lf))))) [7,15,240,3840,4369,17476,52428] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,17476,56797] BT.lf) [7,15,240,3840,4369,17476,61986] BT.lf) [7,15,240,3840,4369,17476,63624] (BT.nd BT.lf [7,15,240,3840,4369,17487,34952] BT.lf)) [7,15,240,3840,4369,21845,34952] (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,34952,43690] BT.lf) [7,15,240,3840,4369,34952,48059] (BT.nd BT.lf [7,15,240,3840,4369,34952,52428] BT.lf))) [7,15,240,3840,4369,34952,56797] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,34952,61986] BT.lf) [7,15,240,3840,4369,34952,62532] BT.lf) [7,15,240,3840,4383,8738,17476,34952,61440] (BT.nd BT.lf [7,15,240,3840,4593,8738,34952] BT.lf)) [7,15,240,3840,7953,8738,17476] (BT.nd (BT.nd BT.lf [7,15,240,3840,7953,8738,17476,34952,61440] BT.lf) [7,15,240,3840,7953,8738,34952] (BT.nd BT.lf [7,15,240,3840,8738,13107,17476] BT.lf)))) [7,15,240,3840,8738,13107,34952] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,8738,17476,21845] BT.lf) [7,15,240,3840,8738,17476,30583] BT.lf) [7,15,240,3840,8738,17476,34952] (BT.nd BT.lf [7,15,240,3840,8738,17476,34952,61713] BT.lf)) [7,15,240,3840,8738,17476,36744] (BT.nd (BT.nd BT.lf [7,15,240,3840,8738,17476,43690] BT.lf) [7,15,240,3840,8738,17476,52428] (BT.nd BT.lf [7,15,240,3840,8738,17476,61166] BT.lf))) [7,15,240,3840,8738,17652,34952] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,8738,20292,34952] BT.lf) [7,15,240,3840,8738,26214,34952] (BT.nd BT.lf [7,15,240,3840,8738,34952,39321] BT.lf)) [7,15,240,3840,8738,34952,48059] (BT.nd (BT.nd BT.lf [7,15,240,3840,8738,34952,52428] BT.lf) [7,15,240,3840,8738,34952,61166] (BT.nd BT.lf [7,15,240,3840,17476,21845,34952] BT.lf)))))) [7,15,240,3840,17476,26214,34952] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,17476,34952,39321] BT.lf) [7,15,240,3840,17476,34952,43690] BT.lf) [7,15,240,3840,17476,34952,56797] (BT.nd BT.lf [7,15,240,3840,17476,34952,61166] BT.lf)) [7,15,240,3855,4369,8738,17476] (BT.nd (BT.nd BT.lf [7,15,240,3855,4369,8738,17476,34952,61440] BT.lf) [7,15,240,3855,4369,8738,34952] (BT.nd BT.lf [7,15,240,3855,4369,17476,34952] BT.lf))) [7,15,240,3855,8738,17476,34952] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4080,4369,8738,17476] BT.lf) [7,15,240,4080,4369,8738,34952] BT.lf) [7,15,240,4080,4369,17476,34952] (BT.nd BT.lf [7,15,240,4080,8738,17476,34952] BT.lf)) [7,15,240,4095,4369,8738,17476] (BT.nd (BT.nd BT.lf [7,15,240,4095,4369,8738,34952] BT.lf) [7,15,240,4095,4369,17476,34952] (BT.nd BT.lf [7,15,240,4095,8738,17476,34952] BT.lf)))) [7,15,240,4369,7953,8738,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4369,7953,8738,17476,61440] BT.lf) [7,15,240,4369,8738,17476,20292] BT.lf) [7,15,240,4369,8738,17476,20292,34952,61440] (BT.nd BT.lf [7,15,240,4369,8738,17476,34952,36744,61440] BT.lf)) [7,15,240,4369,8738,17476,36744] (BT.nd (BT.nd BT.lf [7,15,240,4369,8738,17476,36744,61440] BT.lf) [7,15,240,4369,8738,17476,61440] (BT.nd BT.lf [7,15,240,4369,8738,17476,61455] BT.lf))) [7,15,240,4369,8738,17476,61680] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4369,8738,17476,61695] BT.lf) [7,15,240,4369,8738,17476,62532] (BT.nd BT.lf [7,15,240,4369,8738,17476,63624] BT.lf)) [7,15,240,4369,8738,17487,61440] (BT.nd (BT.nd BT.lf [7,15,240,4369,8738,20292] BT.lf) [7,15,240,4369,8738,20292,34952] (BT.nd BT.lf [7,15,240,4369,8738,20292,34952,61440] BT.lf))))) [7,15,240,4369,8738,20292,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4369,8738,21845,61440] BT.lf) [7,15,240,4369,8738,26214,61440] BT.lf) [7,15,240,4369,8738,30583,61440] (BT.nd BT.lf [7,15,240,4369,8738,34952,36744] BT.lf)) [7,15,240,4369,8738,34952,61440] (BT.nd (BT.nd BT.lf [7,15,240,4369,8738,34952,61455] BT.lf) [7,15,240,4369,8738,34952,61680] (BT.nd BT.lf [7,15,240,4369,8738,34952,61695] BT.lf))) [7,15,240,4369,8738,34952,62532] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4369,8738,34952,63624] BT.lf) [7,15,240,4369,8738,34959,61440] BT.lf) [7,15,240,4369,8738,36744] (BT.nd BT.lf [7,15,240,4369,8738,36744,61440] BT.lf)) [7,15,240,4369,8738,39321,61440] (BT.nd (BT.nd BT.lf [7,15,240,4369,8738,43690,61440] BT.lf) [7,15,240,4369,8738,48059,61440] (BT.nd BT.lf [7,15,240,4369,8738,61440,62532] BT.lf)))) [7,15,240,4369,8738,61440,63624] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4369,8738,62532] BT.lf) [7,15,240,4369,8738,63624] BT.lf) [7,15,240,4369,8751,17476,61440] (BT.nd BT.lf [7,15,240,4369,8751,34952,61440] BT.lf)) [7,15,240,4369,8946,17476,61440] (BT.nd (BT.nd BT.lf [7,15,240,4369,12066,17476,34952,61440] BT.lf) [7,15,240,4369,13107,17476,61440] (BT.nd BT.lf [7,15,240,4369,13107,34952,61440] BT.lf))) [7,15,240,4369,17476,20292,34952] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4369,17476,26214,61440] BT.lf) [7,15,240,4369,17476,30583,61440] (BT.nd BT.lf [7,15,240,4369,17476,34952,36744] BT.lf)) [7,15,240,4369,17476,34952,61440] (BT.nd (BT.nd BT.lf [7,15,240,4369,17476,34952,61455] BT.lf) [7,15,240,4369,17476,34952,61680] (BT.nd BT.lf [7,15,240,4369,17476,34952,61695] BT.lf))))))) [7,15,240,4369,17476,34952,62532] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4369,17476,34952,63624] BT.lf) [7,15,240,4369,17476,34959,61440] BT.lf) [7,15,240,4369,17476,35064,61440] (BT.nd BT.lf [7,15,240,4369,17476,39321,61440] BT.lf)) [7,15,240,4369,17476,52428,61440] (BT.nd (BT.nd BT.lf [7,15,240,4369,17476,56797,61440] BT.lf) [7,15,240,4369,17476,61440,61986] (BT.nd BT.lf [7,15,240,4369,17476,61440,63624] BT.lf))) [7,15,240,4369,17476,63624] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4369,17487,34952,61440] BT.lf) [7,15,240,4369,21845,34952,61440] BT.lf) [7,15,240,4369,34952,43690,61440] (BT.nd BT.lf [7,15,240,4369,34952,48059,61440] BT.lf)) [7,15,240,4369,34952,52428,61440] (BT.nd (BT.nd BT.lf [7,15,240,4369,34952,56797,61440] BT.lf) [7,15,240,4369,34952,61440,61986] (BT.nd BT.lf [7,15,240,4369,34952,61440,62532] BT.lf)))) [7,15,240,4369,34952,62532] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,4593,8738,34952,61440] BT.lf) [7,15,240,7953,8738,17476,34952,61440] BT.lf) [7,15,240,7953,8738,17476,61440] (BT.nd BT.lf [7,15,240,7953,8738,34952,61440] BT.lf)) [7,15,240,8738,13107,17476,61440] (BT.nd (BT.nd BT.lf [7,15,240,8738,13107,34952,61440] BT.lf) [7,15,240,8738,17476,20292,34952] (BT.nd BT.lf [7,15,240,8738,17476,21845,61440] BT.lf))) [7,15,240,8738,17476,30583,61440] (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,8738,17476,34952,36744] BT.lf) [7,15,240,8738,17476,34952,61440] (BT.nd BT.lf [7,15,240,8738,17476,34952,61455] BT.lf)) [7,15,240,8738,17476,34952,61680] (BT.nd (BT.nd BT.lf [7,15,240,8738,17476,34952,61695] BT.lf) [7,15,240,8738,17476,34952,62532] (BT.nd BT.lf [7,15,240,8738,17476,34952,63624] BT.lf))))) [7,15,240,8738,17476,36744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,8738,17476,36744,61440] BT.lf) [7,15,240,8738,17476,43690,61440] BT.lf) [7,15,240,8738,17476,52428,61440] (BT.nd BT.lf [7,15,240,8738,17476,61166,61440] BT.lf)) [7,15,240,8738,17652,34952,61440] (BT.nd (BT.nd BT.lf [7,15,240,8738,20292,34952] BT.lf) [7,15,240,8738,20292,34952,61440] (BT.nd BT.lf [7,15,240,8738,26214,34952,61440] BT.lf))) [7,15,240,8738,34952,39321,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,8738,34952,48059,61440] BT.lf) [7,15,240,8738,34952,52428,61440] BT.lf) [7,15,240,8738,34952,61166,61440] (BT.nd BT.lf [7,15,240,17476,21845,34952,61440] BT.lf)) [7,15,240,17476,26214,34952,61440] (BT.nd (BT.nd BT.lf [7,15,240,17476,34952,39321,61440] BT.lf) [7,15,240,17476,34952,43690,61440] (BT.nd BT.lf [7,15,240,17476,34952,56797,61440] BT.lf)))) [7,15,240,17476,34952,61166,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,255,3840,4369,8738,17476] BT.lf) [7,15,255,3840,4369,8738,34952] BT.lf) [7,15,255,3840,4369,17476,34952] (BT.nd BT.lf [7,15,255,3840,8738,17476,34952] BT.lf)) [7,15,255,4369,8738,17476,61440] (BT.nd (BT.nd BT.lf [7,15,255,4369,8738,34952,61440] BT.lf) [7,15,255,4369,17476,34952,61440] (BT.nd BT.lf [7,15,255,8738,17476,34952,61440] BT.lf))) [7,15,512,3840,4369,17476,61440] (BT.nd (BT.nd (BT.nd BT.lf [7,15,2048,3840,4369,17476,61440] BT.lf) [7,15,3840,4080,4369,8738,17476] (BT.nd BT.lf [7,15,3840,4080,4369,8738,34952] BT.lf)) [7,15,3840,4080,4369,17476,34952] (BT.nd (BT.nd BT.lf [7,15,3840,4080,8738,17476,34952] BT.lf) [7,15,3840,4095,4369,8738,17476] (BT.nd BT.lf [7,15,3840,4095,4369,8738,34952] BT.lf)))))) [7,15,3840,4095,4369,17476,34952] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4095,8738,17476,34952] BT.lf) [7,15,3840,4369,4593,8738,17476] BT.lf) [7,15,3840,4369,4593,8738,17476,61440] (BT.nd BT.lf [7,15,3840,4369,4593,8738,34952] BT.lf)) [7,15,3840,4369,4593,17476,34952] (BT.nd (BT.nd BT.lf [7,15,3840,4369,8738,8946,17476] BT.lf) [7,15,3840,4369,8738,8946,17476,34952,61440] (BT.nd BT.lf [7,15,3840,4369,8738,8946,34952] BT.lf))) [7,15,3840,4369,8738,16384,17476] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,8738,16384,34952] BT.lf) [7,15,3840,4369,8738,17476,34952,35064,61440] BT.lf) [7,15,3840,4369,8738,17476,35064] (BT.nd BT.lf [7,15,3840,4369,8738,17476,35064,61440] BT.lf)) [7,15,3840,4369,8738,17476,61440] (BT.nd (BT.nd BT.lf [7,15,3840,4369,8738,17476,61455] BT.lf) [7,15,3840,4369,8738,17476,61713] (BT.nd BT.lf [7,15,3840,4369,8738,17476,61986] BT.lf)))) [7,15,3840,4369,8738,17476,63624] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,8738,17476,65280] BT.lf) [7,15,3840,4369,8738,17476,65295] BT.lf) [7,15,3840,4369,8738,17487,61440] (BT.nd BT.lf [7,15,3840,4369,8738,17652,34952,61440] BT.lf)) [7,15,3840,4369,8738,20292,61440] (BT.nd (BT.nd BT.lf [7,15,3840,4369,8738,21845,61440] BT.lf) [7,15,3840,4369,8738,26214,61440] (BT.nd BT.lf [7,15,3840,4369,8738,30583,61440] BT.lf))) [7,15,3840,4369,8738,34952,35064] (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,8738,34952,61440] BT.lf) [7,15,3840,4369,8738,34952,61455] (BT.nd BT.lf [7,15,3840,4369,8738,34952,61713] BT.lf)) [7,15,3840,4369,8738,34952,61986] (BT.nd (BT.nd BT.lf [7,15,3840,4369,8738,34952,63624] BT.lf) [7,15,3840,4369,8738,34952,65280] (BT.nd BT.lf [7,15,3840,4369,8738,34952,65295] BT.lf))))) [7,15,3840,4369,8738,34959,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,8738,36744,61440] BT.lf) [7,15,3840,4369,8738,39321,61440] BT.lf) [7,15,3840,4369,8738,43690,61440] (BT.nd BT.lf [7,15,3840,4369,8738,48059,61440] BT.lf)) [7,15,3840,4369,8738,61440,62532] (BT.nd (BT.nd BT.lf [7,15,3840,4369,8738,61440,63624] BT.lf) [7,15,3840,4369,8738,63624] (BT.nd BT.lf [7,15,3840,4369,8751,17476,61440] BT.lf))) [7,15,3840,4369,8751,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,8946,17476] BT.lf) [7,15,3840,4369,8946,17476,34952] BT.lf) [7,15,3840,4369,8946,17476,34952,61440] (BT.nd BT.lf [7,15,3840,4369,8946,17476,61440] BT.lf)) [7,15,3840,4369,13107,17476,61440] (BT.nd (BT.nd BT.lf [7,15,3840,4369,13107,34952,61440] BT.lf) [7,15,3840,4369,16384,17476,34952] (BT.nd BT.lf [7,15,3840,4369,17476,26214,61440] BT.lf)))) [7,15,3840,4369,17476,30583,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,17476,34952,35064] BT.lf) [7,15,3840,4369,17476,34952,61440] BT.lf) [7,15,3840,4369,17476,34952,61455] (BT.nd BT.lf [7,15,3840,4369,17476,34952,61713] BT.lf)) [7,15,3840,4369,17476,34952,61986] (BT.nd (BT.nd BT.lf [7,15,3840,4369,17476,34952,63624] BT.lf) [7,15,3840,4369,17476,34952,65280] (BT.nd BT.lf [7,15,3840,4369,17476,34952,65295] BT.lf))) [7,15,3840,4369,17476,34959,61440] (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,17476,35064] BT.lf) [7,15,3840,4369,17476,35064,61440] (BT.nd BT.lf [7,15,3840,4369,17476,39321,61440] BT.lf)) [7,15,3840,4369,17476,52428,61440] (BT.nd (BT.nd BT.lf [7,15,3840,4369,17476,56797,61440] BT.lf) [7,15,3840,4369,17476,61440,61986] (BT.nd BT.lf [7,15,3840,4369,17476,61440,63624] BT.lf)))))))) [7,15,3840,4369,17476,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,17476,63624] BT.lf) [7,15,3840,4369,17487,34952,61440] BT.lf) [7,15,3840,4369,21845,34952,61440] (BT.nd BT.lf [7,15,3840,4369,34952,43690,61440] BT.lf)) [7,15,3840,4369,34952,48059,61440] (BT.nd (BT.nd BT.lf [7,15,3840,4369,34952,52428,61440] BT.lf) [7,15,3840,4369,34952,56797,61440] (BT.nd BT.lf [7,15,3840,4369,34952,61440,61986] BT.lf))) [7,15,3840,4369,34952,61440,62532] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,34952,61986] BT.lf) [7,15,3840,4593,8738,17476,34952] BT.lf) [7,15,3840,4593,8738,17476,34952,61440] (BT.nd BT.lf [7,15,3840,4593,8738,34952] BT.lf)) [7,15,3840,4593,8738,34952,61440] (BT.nd (BT.nd BT.lf [7,15,3840,7953,8738,17476,61440] BT.lf) [7,15,3840,7953,8738,34952,61440] (BT.nd BT.lf [7,15,3840,8738,8946,17476,34952] BT.lf)))) [7,15,3840,8738,13107,17476,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,8738,13107,34952,61440] BT.lf) [7,15,3840,8738,16384,17476,34952] BT.lf) [7,15,3840,8738,17476,21845,61440] (BT.nd BT.lf [7,15,3840,8738,17476,30583,61440] BT.lf)) [7,15,3840,8738,17476,34952,35064] (BT.nd (BT.nd BT.lf [7,15,3840,8738,17476,34952,61440] BT.lf) [7,15,3840,8738,17476,34952,61455] (BT.nd BT.lf [7,15,3840,8738,17476,34952,61713] BT.lf))) [7,15,3840,8738,17476,34952,61986] (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,8738,17476,34952,63624] BT.lf) [7,15,3840,8738,17476,34952,65280] (BT.nd BT.lf [7,15,3840,8738,17476,34952,65295] BT.lf)) [7,15,3840,8738,17476,36744,61440] (BT.nd (BT.nd BT.lf [7,15,3840,8738,17476,43690,61440] BT.lf) [7,15,3840,8738,17476,52428,61440] (BT.nd BT.lf [7,15,3840,8738,17476,61166,61440] BT.lf))))) [7,15,3840,8738,17652,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,8738,20292,34952,61440] BT.lf) [7,15,3840,8738,26214,34952,61440] BT.lf) [7,15,3840,8738,34952,39321,61440] (BT.nd BT.lf [7,15,3840,8738,34952,48059,61440] BT.lf)) [7,15,3840,8738,34952,52428,61440] (BT.nd (BT.nd BT.lf [7,15,3840,8738,34952,61166,61440] BT.lf) [7,15,3840,17476,21845,34952,61440] (BT.nd BT.lf [7,15,3840,17476,26214,34952,61440] BT.lf))) [7,15,3840,17476,34952,39321,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,17476,34952,43690,61440] BT.lf) [7,15,3840,17476,34952,56797,61440] BT.lf) [7,15,3840,17476,34952,61166,61440] (BT.nd BT.lf [7,15,3855,4369,8738,17476,61440] BT.lf)) [7,15,3855,4369,8738,34952,61440] (BT.nd (BT.nd BT.lf [7,15,3855,4369,17476,34952,61440] BT.lf) [7,15,3855,8738,17476,34952,61440] (BT.nd BT.lf [7,15,4369,8738,17476,35064,61440] BT.lf)))) [7,15,4369,8738,17476,36744,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,4369,8738,17476,61440,61680] BT.lf) [7,15,4369,8738,17476,61440,61695] BT.lf) [7,15,4369,8738,17476,61440,65280] (BT.nd BT.lf [7,15,4369,8738,17476,61440,65295] BT.lf)) [7,15,4369,8738,34952,35064,61440] (BT.nd (BT.nd BT.lf [7,15,4369,8738,34952,36744,61440] BT.lf) [7,15,4369,8738,34952,61440,61680] (BT.nd BT.lf [7,15,4369,8738,34952,61440,61695] BT.lf))) [7,15,4369,8738,34952,61440,65280] (BT.nd (BT.nd (BT.nd BT.lf [7,15,4369,8738,34952,61440,65295] BT.lf) [7,15,4369,8738,36744,61440] (BT.nd BT.lf [7,15,4369,17476,34952,35064,61440] BT.lf)) [7,15,4369,17476,34952,36744,61440] (BT.nd (BT.nd BT.lf [7,15,4369,17476,34952,61440,61680] BT.lf) [7,15,4369,17476,34952,61440,61695] (BT.nd BT.lf [7,15,4369,17476,34952,61440,65280] BT.lf)))))) [7,15,4369,17476,34952,61440,65295] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,4369,17476,35064,61440] BT.lf) [7,15,8738,17476,34952,35064,61440] BT.lf) [7,15,8738,17476,34952,36744,61440] (BT.nd BT.lf [7,15,8738,17476,34952,61440,61680] BT.lf)) [7,15,8738,17476,34952,61440,61695] (BT.nd (BT.nd BT.lf [7,15,8738,17476,34952,61440,65280] BT.lf) [7,15,8738,17476,34952,61440,65295] (BT.nd BT.lf [7,15,8738,17476,36744,61440] BT.lf))) [7,64,240,3840,4369,8738,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,128,240,3840,4369,8738,61440] BT.lf) [7,240,255,3840,4369,8738,17476] BT.lf) [7,240,255,3840,4369,8738,34952] (BT.nd BT.lf [7,240,255,3840,4369,17476,34952] BT.lf)) [7,240,255,3840,8738,17476,34952] (BT.nd (BT.nd BT.lf [7,240,255,4369,8738,17476,61440] BT.lf) [7,240,255,4369,8738,34952,61440] (BT.nd BT.lf [7,240,255,4369,17476,34952,61440] BT.lf)))) [7,240,255,8738,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,512,3840,4369,17476,61440] BT.lf) [7,240,2048,3840,4369,17476,61440] BT.lf) [7,240,3840,3855,4369,8738,17476] (BT.nd BT.lf [7,240,3840,3855,4369,8738,34952] BT.lf)) [7,240,3840,3855,4369,17476,34952] (BT.nd (BT.nd BT.lf [7,240,3840,3855,8738,17476,34952] BT.lf) [7,240,3840,4095,4369,8738,17476] (BT.nd BT.lf [7,240,3840,4095,4369,8738,34952] BT.lf))) [7,240,3840,4095,4369,17476,34952] (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,4095,8738,17476,34952] BT.lf) [7,240,3840,4369,4383,8738,17476,34952,61440] (BT.nd BT.lf [7,240,3840,4369,4383,8738,17476,61440] BT.lf)) [7,240,3840,4369,8738,17476,34959,61440] (BT.nd (BT.nd BT.lf [7,240,3840,4369,8738,17476,61440] BT.lf) [7,240,3840,4369,8738,17476,61680] (BT.nd BT.lf [7,240,3840,4369,8738,17476,65280] BT.lf))))) [7,240,3840,4369,8738,17476,65520] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,4369,8738,17487,34952,61440] BT.lf) [7,240,3840,4369,8738,17487,61440] BT.lf) [7,240,3840,4369,8738,20292,61440] (BT.nd BT.lf [7,240,3840,4369,8738,21845,61440] BT.lf)) [7,240,3840,4369,8738,26214,61440] (BT.nd (BT.nd BT.lf [7,240,3840,4369,8738,30583,61440] BT.lf) [7,240,3840,4369,8738,34952,61440] (BT.nd BT.lf [7,240,3840,4369,8738,34952,61680] BT.lf))) [7,240,3840,4369,8738,34952,65280] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,4369,8738,34952,65520] BT.lf) [7,240,3840,4369,8738,34959,61440] BT.lf) [7,240,3840,4369,8738,36744,61440] (BT.nd BT.lf [7,240,3840,4369,8738,39321,61440] BT.lf)) [7,240,3840,4369,8738,43690,61440] (BT.nd (BT.nd BT.lf [7,240,3840,4369,8738,48059,61440] BT.lf) [7,240,3840,4369,8738,61440,62532] (BT.nd BT.lf [7,240,3840,4369,8738,61440,63624] BT.lf)))) [7,240,3840,4369,8751,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,4369,8751,17476,61440] BT.lf) [7,240,3840,4369,8751,34952,61440] BT.lf) [7,240,3840,4369,8946,17476,61440] (BT.nd BT.lf [7,240,3840,4369,13107,17476,61440] BT.lf)) [7,240,3840,4369,13107,34952,61440] (BT.nd (BT.nd BT.lf [7,240,3840,4369,17476,26214,61440] BT.lf) [7,240,3840,4369,17476,30583,61440] (BT.nd BT.lf [7,240,3840,4369,17476,34952,61440] BT.lf))) [7,240,3840,4369,17476,34952,61680] (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,4369,17476,34952,65280] BT.lf) [7,240,3840,4369,17476,34952,65520] (BT.nd BT.lf [7,240,3840,4369,17476,34959,61440] BT.lf)) [7,240,3840,4369,17476,35064,61440] (BT.nd (BT.nd BT.lf [7,240,3840,4369,17476,39321,61440] BT.lf) [7,240,3840,4369,17476,52428,61440] (BT.nd BT.lf [7,240,3840,4369,17476,56797,61440] BT.lf))))))) [7,240,3840,4369,17476,61440,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,4369,17476,61440,63624] BT.lf) [7,240,3840,4369,17487,34952,61440] BT.lf) [7,240,3840,4369,21845,34952,61440] (BT.nd BT.lf [7,240,3840,4369,34952,43690,61440] BT.lf)) [7,240,3840,4369,34952,48059,61440] (BT.nd (BT.nd BT.lf [7,240,3840,4369,34952,52428,61440] BT.lf) [7,240,3840,4369,34952,56797,61440] (BT.nd BT.lf [7,240,3840,4369,34952,61440,61986] BT.lf))) [7,240,3840,4369,34952,61440,62532] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,4383,8738,17476,34952,61440] BT.lf) [7,240,3840,4593,8738,34952,61440] BT.lf) [7,240,3840,7953,8738,17476,61440] (BT.nd BT.lf [7,240,3840,7953,8738,34952,61440] BT.lf)) [7,240,3840,8738,13107,17476,61440] (BT.nd (BT.nd BT.lf [7,240,3840,8738,13107,34952,61440] BT.lf) [7,240,3840,8738,17476,21845,61440] (BT.nd BT.lf [7,240,3840,8738,17476,30583,61440] BT.lf)))) [7,240,3840,8738,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,8738,17476,34952,61680] BT.lf) [7,240,3840,8738,17476,34952,65280] BT.lf) [7,240,3840,8738,17476,34952,65520] (BT.nd BT.lf [7,240,3840,8738,17476,36744,61440] BT.lf)) [7,240,3840,8738,17476,43690,61440] (BT.nd (BT.nd BT.lf [7,240,3840,8738,17476,52428,61440] BT.lf) [7,240,3840,8738,17476,61166,61440] (BT.nd BT.lf [7,240,3840,8738,17652,34952,61440] BT.lf))) [7,240,3840,8738,20292,34952,61440] (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,8738,26214,34952,61440] BT.lf) [7,240,3840,8738,34952,39321,61440] (BT.nd BT.lf [7,240,3840,8738,34952,48059,61440] BT.lf)) [7,240,3840,8738,34952,52428,61440] (BT.nd (BT.nd BT.lf [7,240,3840,8738,34952,61166,61440] BT.lf) [7,240,3840,17476,21845,34952,61440] (BT.nd BT.lf [7,240,3840,17476,26214,34952,61440] BT.lf))))) [7,240,3840,17476,34952,39321,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,3840,17476,34952,43690,61440] BT.lf) [7,240,3840,17476,34952,56797,61440] BT.lf) [7,240,3840,17476,34952,61166,61440] (BT.nd BT.lf [7,240,4080,4369,8738,17476,61440] BT.lf)) [7,240,4080,4369,8738,34952,61440] (BT.nd (BT.nd BT.lf [7,240,4080,4369,17476,34952,61440] BT.lf) [7,240,4080,8738,17476,34952,61440] (BT.nd BT.lf [7,240,4369,4383,8738,17476,61440] BT.lf))) [7,240,4369,4383,8738,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,4369,4383,17476,34952,61440] BT.lf) [7,240,4369,7953,8738,17476,61440] BT.lf) [7,240,4369,7953,8738,34952,61440] (BT.nd BT.lf [7,240,4369,7953,17476,34952,61440] BT.lf)) [7,240,4369,8738,8751,17476,61440] (BT.nd (BT.nd BT.lf [7,240,4369,8738,8751,34952,61440] BT.lf) [7,240,4369,8738,12066,17476,61440] (BT.nd BT.lf [7,240,4369,8738,12066,34952,61440] BT.lf)))) [7,240,4369,8738,17476,61440,61455] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,4369,8738,17476,61440,61695] BT.lf) [7,240,4369,8738,17476,61440,65280] BT.lf) [7,240,4369,8738,17476,61440,65520] (BT.nd BT.lf [7,240,4369,8738,34952,61440,61455] BT.lf)) [7,240,4369,8738,34952,61440,61695] (BT.nd (BT.nd BT.lf [7,240,4369,8738,34952,61440,65280] BT.lf) [7,240,4369,8738,34952,61440,65520] (BT.nd BT.lf [7,240,4369,8751,17476,34952,61440] BT.lf))) [7,240,4369,8751,17476,61440] (BT.nd (BT.nd (BT.nd BT.lf [7,240,4369,8751,34952,61440] BT.lf) [7,240,4369,12066,17476,34952,61440] (BT.nd BT.lf [7,240,4369,17476,34952,61440,61455] BT.lf)) [7,240,4369,17476,34952,61440,61695] (BT.nd (BT.nd BT.lf [7,240,4369,17476,34952,61440,65280] BT.lf) [7,240,4369,17476,34952,61440,65520] (BT.nd BT.lf [7,240,4383,8738,17476,34952,61440] BT.lf)))))) [7,240,7953,8738,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,240,7953,8738,17476,61440] BT.lf) [7,240,7953,8738,34952,61440] BT.lf) [7,240,8738,8751,17476,34952,61440] (BT.nd BT.lf [7,240,8738,12066,17476,34952,61440] BT.lf)) [7,240,8738,17476,34952,61440,61455] (BT.nd (BT.nd BT.lf [7,240,8738,17476,34952,61440,61695] BT.lf) [7,240,8738,17476,34952,61440,65280] (BT.nd BT.lf [7,240,8738,17476,34952,61440,65520] BT.lf))) [7,3840,3855,4369,8738,17476,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,3840,3855,4369,8738,34952,61440] BT.lf) [7,3840,3855,4369,17476,34952,61440] BT.lf) [7,3840,3855,8738,17476,34952,61440] (BT.nd BT.lf [7,3840,4080,4369,8738,17476,61440] BT.lf)) [7,3840,4080,4369,8738,34952,61440] (BT.nd (BT.nd BT.lf [7,3840,4080,4369,17476,34952,61440] BT.lf) [7,3840,4080,8738,17476,34952,61440] (BT.nd BT.lf [7,3840,4369,8738,17476,17487,61440] BT.lf)))) [7,3840,4369,8738,17476,17652,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,3840,4369,8738,17476,61440,61455] BT.lf) [7,3840,4369,8738,17476,61440,61680] BT.lf) [7,3840,4369,8738,17476,61440,65295] (BT.nd BT.lf [7,3840,4369,8738,17476,61440,65520] BT.lf)) [7,3840,4369,8738,17487,34952,61440] (BT.nd (BT.nd BT.lf [7,3840,4369,8738,17487,61440] BT.lf) [7,3840,4369,8738,17652,34952,61440] (BT.nd BT.lf [7,3840,4369,8738,34952,61440,61455] BT.lf))) [7,3840,4369,8738,34952,61440,61680] (BT.nd (BT.nd (BT.nd BT.lf [7,3840,4369,8738,34952,61440,65295] BT.lf) [7,3840,4369,8738,34952,61440,65520] (BT.nd BT.lf [7,3840,4369,17476,17487,34952,61440] BT.lf)) [7,3840,4369,17476,17652,34952,61440] (BT.nd (BT.nd BT.lf [7,3840,4369,17476,34952,61440,61455] BT.lf) [7,3840,4369,17476,34952,61440,61680] (BT.nd BT.lf [7,3840,4369,17476,34952,61440,65295] BT.lf))))) [7,3840,4369,17476,34952,61440,65520] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,3840,4369,17487,34952,61440] BT.lf) [7,3840,8738,17476,17487,34952,61440] BT.lf) [7,3840,8738,17476,17652,34952,61440] (BT.nd BT.lf [7,3840,8738,17476,34952,61440,61455] BT.lf)) [7,3840,8738,17476,34952,61440,61680] (BT.nd (BT.nd BT.lf [7,3840,8738,17476,34952,61440,65295] BT.lf) [7,3840,8738,17476,34952,61440,65520] (BT.nd BT.lf [7,3840,8738,17652,34952,61440] BT.lf))) [8,15,240,3840,4369,8738,17476] (BT.nd (BT.nd (BT.nd BT.lf [8,15,240,3840,4369,8738,17476,34952] BT.lf) [8,15,240,3840,4369,8738,17476,34952,61440] (BT.nd BT.lf [8,15,240,3840,4369,8738,17476,61440] BT.lf)) [8,15,240,3840,4369,8738,34952] (BT.nd (BT.nd BT.lf [8,15,240,3840,4369,8738,34952,61440] BT.lf) [8,15,240,3840,4369,17476,34952] (BT.nd BT.lf [8,15,240,3840,4369,17476,34952,61440] BT.lf)))) [8,15,240,3840,8738,17476,34952] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [8,15,240,3840,8738,17476,34952,61440] BT.lf) [8,15,240,4369,8738,17476,34952,61440] BT.lf) [8,15,240,4369,8738,17476,61440] (BT.nd BT.lf [8,15,240,4369,8738,34952,61440] BT.lf)) [8,15,240,4369,17476,34952,61440] (BT.nd (BT.nd BT.lf [8,15,240,8738,17476,34952,61440] BT.lf) [8,15,3840,4369,8738,17476,34952,61440] (BT.nd BT.lf [8,15,3840,4369,8738,17476,61440] BT.lf))) [8,15,3840,4369,8738,34952,61440] (BT.nd (BT.nd (BT.nd BT.lf [8,15,3840,4369,17476,34952,61440] BT.lf) [8,15,3840,8738,17476,34952,61440] (BT.nd BT.lf [8,240,3840,4369,8738,17476,34952,61440] BT.lf)) [8,240,3840,4369,8738,17476,61440] (BT.nd (BT.nd BT.lf [8,240,3840,4369,8738,34952,61440] BT.lf) [8,240,3840,4369,17476,34952,61440] (BT.nd BT.lf [8,240,3840,8738,17476,34952,61440] BT.lf)))))))))))

def hintValues : Array Nat := #[131110,393262,136225,300169,38017,139558,401710,202027,305350,98440,32902,138337,407617,65935,138305,401454,138273,308617,65672,303302,393518,136289,305286,139302,145473,131118,393254,38025,65679,136257,308361,401608,139566,300107,204078,303238,43206,306383,300075,32904,202121,98438,136491,401708,393295,401702,76070,43302,131366,203822,398401,300425,308424,204169,211244,300161,300168,308360,400449,302278,295110,202024,407585,203913,401473,33167,139310,65929,300078,98376,202030,303311,38187,65928,305359,46465,401544,202025,306255,401606,201865,138315,393516,201771,406593,300232,393416,398369,401487,65836,75983,98379,98448,207148,305281,65670,138542,145441,393260,136267,393264,308616,46209,300097,46473,401707,98704,98696,32911,201774,70785,131112,43142,400481,406561,403535,46216,70689,72801,202017,295046,308289,98441,38273,404591,408673,139462,139329,65673,403521,46280,38088,403534,37953,400417,404545,75912,393327,306305,40065,306209,139464,138534,136488,303183,141377,144417,46217,32838,401455,308321,204161,306310,136489,408873,146529,401615,98511,393263,72833,131176,80001,308609,138286,302214,40134,393259,305230,306223,43308,75976,203851,33160,41094,294991,108673,306569,65932,32910,204070,139564,65926,98504,80172,305358,201857,305222,300129,401446,32975,109697,206886,401486,105601,401518,98606,65838,393326,103553,306561,98697,401520,203905,136235,202113,38281,108678,205100,294990,47404,44239,43215,295119,201768,131119,131179,43137,47233,400494,112008,98347,108577,306241,138441,108742,306379,211241,103723,138319,205094,300171,105670,400686,75873,300424,98377,72841,139336,306222,40235,109953,47302,403502,401488,393296,401456,404526,38190,44326,300076,112940,46379,407590,211019,103624,393359,407849,113862,308427,113963,305264,201840,305550,306574,306374,204075,211041,393423,207142,105771,308353,310337,309448,306377,44161,294958,295022,303151,305199,136240,75910,136481,103470,111654,38024,108591,112683,43105,306313,136392,300238,400521,393352,309313,303216,203841,305352,393256,305231,306382,303310,113798,145608,203919,98383,145606,201871,300417,204936,393510,401614,210313,305356,211240,401704,136492,131374,211238,403662,210315,144680,302222,398640,138433,72911,211016,44334,308268,47489,201776,303150,305198,305200,306254,305262,303214,201838,393294,32966,76161,38091,79241,44230,201835,103561,112009,44331,98350,98604,65582,65835,138313,401519,295024,203814,305190,305192,305254,108838,131371,303233,74022,300105,73871,38027,108840,98598,72843,108609,65643,98507,98380,400681,303174,398433,398633,131372,210977,211009,305294,306318,303246,401551,401552,408641,48513,109766,76076,46380,108844,408651,76174,408609,407593,408617,406603,404592,38287,65574]

def tagGroups : Array (List Nat) := #[[2],[6],[10],[14],[18],[129],[137],[169],[73],[177],[105],[97],[145],[82],[153],[154],[22],[113],[106],[114],[18,153],[98],[185],[81],[146],[57],[130],[141],[74],[22,193,201],[138],[193],[202],[201],[110,114],[101],[109],[58],[194],[18,145],[18,145,153],[110],[137,177],[149],[22,193],[14,113],[150,154],[133],[117],[97,129],[186],[129,169],[105,137],[189],[170],[181],[118],[150],[178],[113,154],[145,185],[22,201],[86],[137,153],[113,145,154],[78],[157],[18,137],[14,145],[22,177,193,201],[97,169],[128],[101,129],[77],[133,169],[22,169,193,201],[155],[85],[80],[136],[142],[130,142],[115],[170,182],[143],[102],[144],[14,154],[98,110],[130,158],[98,114],[137,146],[113,145],[96],[145,154],[18,129,153],[82,145],[177,201],[137,153,202],[147],[153,202],[0,4,8,12,14,57,58,82],[102,114],[105,114],[98,118],[158],[73,129],[97,113,154],[134,138,150,158],[130,150],[168],[22,177],[197],[1,3,5,7,9,11,13,15,59,63,75,79,83,87,99,103,107,111,115,119,135,159],[113,154,194],[177,186],[113,145,154,194],[0,4,8],[78,82],[72],[0,4,8,12,14,57,58,82,113],[98,110,114],[62],[58,85],[104],[0,4,6,8,12,16,57,58,73,74,81,82,105,130,154],[141,153],[106,157],[180],[0,2,4,8,10,12,14,16,57,58,98,113,114,130,138,154],[18,150],[83],[18,129],[142,154],[18,137,153],[134],[176],[22,185,201],[137,153,193,202],[153,193,202],[134,138,150,158,205],[113,185],[22,185],[198],[0,4,8,12,57,58,98],[110,118],[0,4,8,12,57,58,106,114],[0,4,8,10,12,74,81,82,98],[0,4,8,10,12,74,98],[0,4,6,8,10,12,74,98],[82,113],[0,4,8,12,14,98,106,113,118],[14,105],[156],[84],[196],[106,153],[81,141],[0,2,4,8,10,12,14,16,57,58,82,130,138],[0,4,8,12,16,18,57,58,98,114,130,138,146,153,158],[0,4,8,12,16,18,57,58,98,114,130,146,153],[145,153],[18,113],[102,106],[248],[140],[173],[1,3,5,7,9,11,13,15,59,63,75,79,83,87,99,103,107,111,115,119,135,151],[1,3,5,7,9,11,13,15,59,63,75,79,83,87,99,103,107,111,115,119,135,151,159],[174],[1,3,5,7,9,11,13,15,17,19,59,63,75,79,83,87,99,103,107,111,115,119,131,135,139,143,147,151,155,159,175,183,207],[195],[1,3,5,7,9,11,13,15,17,19,59,63,75,79,83,87,99,103,107,111,115,119,131,135,139,143,147,151,155,159,175,183,199,207],[0,4,8,57,58],[0,2,4,8,10,12,57,58,73,98],[0,4,8,12,81,82,114],[0,4,8,12,106,114],[0,4,6,8,10,12,73,78,82,98],[81,105],[137,145],[105,145],[150,158],[18,149],[0,2,4,8,10,12,14,16,57,58,82,98,113,114,130,138],[116],[112],[0,2,4,8,10,12,14,16,57,58,73,98,113,114,130],[0,2,4,8,10,12,14,16,57,58,98,113,114,130],[18,153,158],[85,105],[117,149],[0,4,8,12,16,18,57,58,98,114,130,138,146,153],[0,4,8,12,16,57,58,98,113,114,130,146],[134,142,150,158],[0,4,8,12,16,57,58,105,106,113,114,138,146,154],[14,145,158],[97,113,145,154],[56],[105,158],[74,117],[0,2,4,6,8,10,12,14,16,74,81,82,98,130,146,154],[134,142,146,158],[192],[22,177,201],[105,185],[177,185,201],[184],[256],[148],[138,150,154],[141,153,193,202],[141,153,202],[150,153,193,202],[142,201],[17,19,131,139,147],[182],[206],[114,177,186],[113,145,154,198],[142,146],[1,3,5,7,9,11,17,19,59,63,75,79,83,87,103,131,135,139,143,147,151,159],[22,145],[22,145,193],[22,185,193,201],[203],[21,23,171,179,187,191,203],[0,4],[0,4,6,8,58,82,85],[0,4,8,10],[0,4,8,10,81],[0,2,4,6,8,57,62],[0,4,6,8,10,12,57,58,73,74,82,85,106,114,117],[109,113],[0,2,4,8,12,14,57,58,82,98,101],[0,4,8,12,14,57,58,98,109,110,114,117],[0,4,8,12,14,57,58,82,114,117],[0,4,8,12,14,57,58,98,110,113],[0,4,6,8,12,14,57,58,82,85,105,113],[0,4,8,12,57,58,106,109,114,117],[0,4,8,10,12,57,58,106,114,117],[0,2,4,8,12,14,58,61,97,113],[0,4,6,8,12,74,81,82,98],[0,2,4,6,8,10,12,74,81,82,98],[0,4,6,8,10,12,74,81,82,98,101],[14,109],[0,4,8,12,74,98],[0,4,6,8,12,114],[0,4,6,8,10,12,98,114],[0,4,6,8,10,12,58,98],[0,4,6,8,10,12,74,81,86,98],[0,4,6,8,10,12,74,81,82],[0,4,8,12,106],[0,4,8,12,14,98,110,113],[0,2,4,8,12,14,58,61,74,97,113],[0,2,4,6,8,10,12,57,58,73,78,81,82,98],[0,2,4,6,8,10,12,58,78,81,82,98,101],[0,2,4,6,8,10,12,106],[0,4,8,12,14,98,106,113],[81,114],[0,2,4,6,8,10,12,73,117],[74,86],[0,2,4,6,8,10,12],[0,4,6,8,12,16,18,57,58,73,74,81,82,106,114,137,138,153],[130,150,154],[130,138],[0,4,6,8,12,16,57,58,73,74,81,82,105,106,117],[0,4,6,8,12,16,57,58,73,74,81,82,105,117],[0,4,6,8,12,16,57,58,73,74,81,82,109,138],[0,4,6,8,12,14,16,57,58,73,74,81,82,109],[0,4,6,8,12,14,16,57,58,73,74,81,82,105],[81,137],[0,4,6,8,12,14,16,57,58,98,105,113,114,130],[0,4,8,10,12,14,16,57,58,98,113,114,130,133],[0,2,4,8,10,12,14,16,57,58,73,98,101,114,130],[0,2,4,8,10,12,14,16,57,58,73,98,114,117,130],[0,2,4,8,10,12,14,16,57,58,98,114,117,130],[0,2,4,8,10,12,14,16,57,58,114,117,130],[73,97],[18,114,137],[0,2,4,8,10,12,14,16,57,58,113,114,130],[0,2,4,8,10,12,14,16,57,58,130,138],[0,2,4,8,10,12,14,16,57,58,106,130,138],[0,2,4,8,10,12,14,16,57,58,106,130,138,154],[0,2,4,8,10,12,14,16,57,58,130,138,154],[0,4,8,10,12,14,16,58,61,98,113,114,130],[0,4,8,12,16,18,57,58,73,74,106,130,138,150,153],[142,153],[0,4,8,10,12,16,18,57,58,98,114,130,138,146,153],[137,154],[98,114,157],[0,4,6,8,10,12,14,16,57,58,98,113,114,130,146],[0,4,8,12,16,18,57,58,98,114,117,130,146,153],[1,3,5,7,13,15,59,63,87,99,103,107,111,119],[9,11,75,79,115],[130,142,150,158],[0,4,8,12,14,16,18,57,58,82,113,130,138,145,153,154],[0,4,8,12,14,16,18,57,58,82,113,130,134,138,142,150,153,154,158],[200],[86,145],[0,4,8,12,16,18,57,58,130,138,146,158],[0,4,8,12,16,18,57,58,130,138,146],[0,4,8,12,16,18,57,58,130,138,150],[0,4,8,10,12,16,18,57,58,130,138,150,158],[0,4,8,10,12,16,18,57,58,130,138,146,158],[114,157],[78,86,113,149],[105,137,153],[0,4,8,12,16,18,74,81,82,98,130,138,146,153],[18,141],[1,3,5,7,9,11,59,63,75,79,83,87,103],[0,2,4,8,10,12,14,16,18,105,130,142,145,146],[0,4,6,8,10,12,14,16,74,81,82,98,130,133,146,154],[0,4,6,8,10,12,14,16,74,81,82,98,113,114,130,154,157],[18,114,145],[115,119],[86,113],[0,4,6,8,10,12,14,16,57,58,81,82,98,105,110,113,114,130,138],[98,106],[0,4,6,8,10,12,14,16,57,58,81,82,97,102,106,113,114,130,138],[0,4,6,8,10,12,14,16,57,58,81,97,113,114,130],[0,4,6,8,10,12,14,16,57,58,81,97,109,113,114,130,138],[0,4,6,8,10,12,14,16,57,58,74,81,130,138],[0,4,6,8,10,12,14,16,57,58,81,130,138],[0,4,6,8,10,12,14,16,57,58,98,130,138],[0,4,6,8,10,12,14,16,57,58,98,109,130,138],[0,4,6,8,10,12,14,16,57,58,74,130,138],[0,4,6,8,10,12,14,16,57,58,109,130,138],[97,145,154],[134,138],[0,4,6,8,10,12,14,16,58,74,82,85,105,106,114],[138,150],[106,118],[18,129,145],[102,153],[14,113,145],[110,113,145,154],[138,158],[18,98],[129,138],[18,98,145],[0,2,4,8,12,14,16,18,98,110,113,130,138,145],[18,105],[198,202],[1,3,5,7,9,11,17,19,59,63,75,79,83,87,111,119,131,135,139,143,147,151,159],[170,182,190,198,206],[244],[188],[228],[129,173],[78,86,113,149,189],[141,193,202],[137,193],[22,154,177],[153,193],[129,137,153,193,202],[117,149,185,189],[232],[236],[252],[0,2,4,8,10,12,14,16,18,20,57,58,98,106,113,114,130,142,145,146,153,154,170,178,202],[177,193,201],[260],[0,2,4,8,10,12,14,16,18,20,57,58,82,98,113,114,130,137,142,145,146,153,154,170,178,202],[102,118,157,193,197],[155,159],[174,182,190,194,206],[134,142,150,154],[17,19,131,139,147,151],[61,77,97,133,173],[109,177],[102,118,157],[61,133,169,173],[77,97],[1,3,5,7,9,11,13,15,59,63,75,79,83,87,99,103,107,111,115,119,151,159],[22,185,193],[149,150,153,193,202],[114,177],[108],[130,201],[129,169,186],[0,4,8,12,16,18,20,22,57,58,98,114,130,134,138,142,146,150,153,158,170,178,186,193,201,202,205],[1,3,5,7,9,11,17,19,59,63,75,79,83,87,103,119,131,135,139,143,147,151,159],[13,15,99,107,111,155],[145,154,194],[119],[105,177],[105,137,177],[17,19,131,139,143,147],[182,186],[17,19,131,139,143,155],[185,193,201],[145,194],[18,114,202],[113,145,185],[97,113,145,154,194],[22,189,193],[13,15,99,107,155],[111],[22,169,201],[100],[134,201],[62,81,109,141,181],[106,193],[18,145,153,185],[139],[151],[61,77,173,217,221],[78,86,189,233,237],[1,3,5,7,9,11,13,15,21,23,59,63,75,79,83,87,99,103,107,111,115,119,135,159,171,175,179,183,187,191,195,199,207],[17,19,131,139,143,147,151,203],[61,77,133,173,217,221],[78,86,149,189,233,237],[26],[237],[245],[187],[1,3,5,7,9,11,17,19,21,23,59,63,75,79,83,87,103,119,131,135,139,143,147,151,159,171,175,179,183,187,191,199,203,207],[13,15,99,107,111,155,195],[199],[0,2,4,8,57,58,74],[0,4,8,10,74,81,86],[0,4,6,8,58],[0,2,4,6,8],[58,81],[0,4,6,8,12,57,58,73,74,81,82,106],[0,4,6,8,12,57,58,81,82,106,109],[0,4,6,8,10,12,57,58,73,74,82,106,114,117],[0,4,6,8,12,14,57,58,82,98,106,109,113,118],[0,4,6,8,12,57,58,98],[0,4,6,8,10,12,57,58,98,114],[0,4,8,12,14,57,58,98,109,110,114],[0,4,8,12,14,57,58,98,110],[0,4,8,10,12,57,58,106,114],[0,4,8,12,57,58,106,109],[0,4,8,12,57,58,106],[0,4,8,12,57,58,85,118],[0,4,8,12,57,58,85],[0,4,8,12,57,58],[0,4,8,10,12,57,58],[0,4,8,12,14,57,58,113],[0,4,6,8,10,12,57,58,82,98,114],[0,2,4,8,10,12,74,98,101],[0,4,8,10,12,74,77,98],[105,117],[0,4,8,10,12,74,82,85,98],[117,118],[0,4,8,12,14,74,98],[0,2,4,6,8,10,12,57,74,98,106],[0,2,4,8,12,74,98,101],[0,2,4,8,12,57,74,77,98],[0,4,8,12,74,81,86,98],[0,4,8,12,82,85,98],[0,4,8,10,12,78,81,82],[0,4,8,10,12,81,82,114,117],[0,4,8,10,12,106,114],[0,4,8,10,12,106,114,117],[0,4,8,10,12,106,109,114],[0,4,6,8,10,12,74,106,114],[0,4,8,12,14,98,106],[0,4,8,12,114],[0,4,6,8,12,114,117],[0,4,6,8,10,12,114],[0,4,6,8,12,62,81],[0,4,8,12,98],[0,4,8,10,12,74,86],[0,4,6,8,10,12,98],[14,110],[0,2,4,8,10,12,57,58,73,74,82,98,114,117],[0,2,4,8,12,14,57,58,74,97,98],[0,2,4,8,12,14,57,58,74,97,98,113],[0,2,4,6,8,10,12,57,58,73,74,98,101],[0,2,4,6,8,10,12,57,58,73,74,81,86,98,101],[0,2,4,8,12,14,57,58,82,98],[0,2,4,8,12,14,58,97,113],[0,4,8,12,14,58,82,113],[0,2,4,8,12,57,58,106],[101,113],[0,2,4,6,8,12,14,57,58,106],[0,2,4,8,12,14,57,58,101,102,106,113],[0,2,4,8,10,12,74],[0,2,4,8,12,82],[0,4,6,8,10,12,82],[74,113],[0,4,6,8,10,12,58],[0,4,6,8,10,12,73,81,82,98],[0,4,6,8,10,12,81],[74,86,113],[0,4,6,8,10,12,58,81],[0,4,6,8,10,12,58,81,98],[0,4,6,8,10,12,106],[0,4,6,8,12,14,58,106],[0,4,6,8,10,12,57,62,85,98],[0,2,4,8,10,12,57,73,74,81,82],[0,4,8,12],[0,4,8,12,14,57,82,113],[0,2,4,6,8,10,12,58,78,81,82,98],[0,4,8,10,12,58,82,98],[0,4,8,12,14,106,113],[0,2,4,6,8,10,12,73,78,81,82,117],[0,4,8,12,58,98],[0,4,6,8,12,74,98,106],[62,105],[0,4,8,12,14,102,106,113],[0,4,8,12,14,82,113],[0,4,8,12,14,82,98,106],[0,4,8,10,12,14,82,98,105,118],[0,2,4,6,8,10,12,81,82,106],[0,2,4,6,8,10,12,74,81,82,106],[0,4,8,12,14,98,110],[0,4,8,10,12,14],[0,2,4,6,8,10,12,74,82],[0,2,4,6,8,10,12,74,82,114],[0,2,4,6,8,10,12,57,58,73,78,81,82],[0,4,6,8,12,57,58],[0,4,6,8,12,14,57,58,98,106,109,118],[0,2,4,6,8,10,12,57,58],[0,2,4,6,8,10,12,58,73],[0,2,4,6,8,10,12,81,114,117],[0,2,4,6,8,12,14,98,106,118],[0,2,4,6,8,10,12,58,73,74,86,114,117],[0,2,4,6,8,10,12,57,58,98],[0,2,4,6,8,10,12,106,114],[0,2,4,6,8,10,12,98],[0,2,4,6,8,10,12,74,81,86,114,117],[0,2,4,6,8,10,12,82,117],[0,2,4,6,8,10,12,57,58,85,98],[0,2,4,6,8,10,12,57,58,81,109],[0,2,4,6,8,10,12,73,78,82,114,117],[0,4,8,10,12,14,98,105],[73,82],[0,4,6,8,12,14,57,62,98,105,106,113,118],[0,2,4,6,8,10,12,57,62,81,114,117],[0,2,4,6,8,12,14,57,98,106,118],[10,105],[0,2,4,6,8,10,12,74,86,117],[62,81],[0,2,4,6,8,10,12,58,85],[14,82],[0,2,4,6,8,10,12,58,85,106],[0,2,4,6,8,10,12,62,78,81,82,117],[0,2,4,6,8,10,12,73,74],[0,4,8,12,14,102,110],[0,4,6,8,12,14,102,106],[10,114],[0,4,6,8,10,12,14,16,57,58,73,74,81,82,97,98,105,106,114,117,138,146,154,157],[0,2,4,6,8,12,16,18,57,58,73,74,81,82,106,114,130,133,137,138],[0,4,6,8,12,16,18,57,58,73,74,81,82,106,114,138,141,153],[0,4,6,8,12,16,18,57,58,73,74,81,82,106,114,138,141],[0,4,6,8,12,16,18,57,58,73,74,81,82,106,130,137,138,149,150,154,157],[0,4,6,8,12,16,18,57,58,73,74,81,82,106,130,138,141,150,153],[0,4,6,8,12,16,18,57,58,73,74,81,82,106,114,138,141,154,157],[0,4,6,8,12,16,18,57,58,73,74,81,82,106,114,137,138],[0,4,6,8,12,16,18,57,58,62,73,74,81,82,85,106,109,114,137,138,141,153],[0,4,6,8,10,12,16,18,57,58,73,74,81,82,106,114,117,137,138,145,153],[0,4,6,8,12,16,57,58,73,74,81,82,105,106,138,146,149,154,157],[0,4,6,8,12,16,57,58,73,74,81,82,105,106,138,141,146,154],[0,4,6,8,12,14,16,57,58,73,74,81,82,105,106,138,141,146,154,157],[0,2,4,6,8,12,16,18,57,58,74,77,81,82,106,129,137,138,153],[0,4,6,8,12,16,18,57,58,73,74,82,85,106,114,137,138,153],[0,4,6,8,12,14,16,57,58,81,82,98,105,106,113,114,130,138,141],[0,4,6,8,12,14,16,57,58,81,82,98,105,106,113,114,130,138],[0,2,4,6,8,10,12,14,16,57,58,81,82,98,105,106,113,114,130,138,141],[0,4,6,8,10,12,14,16,57,58,81,82,98,105,106,113,114,130,133,138,141],[0,4,6,8,12,16,57,58,81,82,106,109,113,114,138,154],[0,4,6,8,12,16,57,58,81,82,106,109,138,146,154],[0,4,6,8,12,16,18,57,73,74,81,82,106,114,137,138,153],[0,2,4,6,8,12,16,18,57,58,61,73,74,77,81,82,114,129,133,137,153],[97,101,105],[0,4,6,8,12,16,57,58,73,74,81,82,105,106,130,154],[0,4,6,8,10,12,14,16,57,58,73,74,81,82,105,106,130,138,154],[0,4,6,8,12,16,57,58,73,74,81,82,106,109,130,138],[0,4,6,8,10,12,16,57,58,73,74,81,82,113,114,130,146,149],[0,2,4,6,8,10,12,16,18,57,58,73,74,81,82,114,130,145,146],[0,4,6,8,12,16,18,57,58,73,74,81,82,130,141,142,146,153],[0,2,4,8,12,16,57,58,74,85,97,130,154],[129,150,153],[0,2,4,8,12,16,57,58,74,82,85,97,130,154],[150,153],[0,2,4,8,10,12,14,16,57,58,73,74,81,82,97,113,114,130,146],[0,2,4,8,12,16,18,57,58,129,150,153],[0,2,4,8,12,16,18,57,58,74,130,138,150,153],[97,145],[0,4,6,8,12,16,18,57,58,62,73,74,81,82,85,114,137,141,153],[0,4,6,8,12,14,16,57,58,73,74,81,82,109,138],[0,4,6,8,12,14,16,57,58,73,74,81,82,105,138],[0,4,6,8,12,16,18,57,58,73,74,85,114,137,153],[0,4,6,8,12,16,57,58,73,74,105,130,154],[0,2,4,6,8,12,14,16,57,58,98,105,113,114,130,133],[0,4,6,8,12,16,57,58,98,113,114,130,149],[0,4,6,8,12,16,57,58,98,113,114,130],[0,2,4,6,8,12,16,57,58,73,98,113,114,130,133],[137,149],[0,2,4,6,8,12,14,16,57,58,73,98,101,105,114,130],[129,145],[0,2,4,6,8,12,16,57,58,73,98,101,114,130],[0,4,6,8,12,14,16,57,58,62,81,85,98,105,106,109,114,130],[0,2,4,8,10,12,14,16,57,58,73,81,98,106,109,114,130],[0,4,6,8,12,14,16,57,58,98,114,117,130],[0,4,6,8,12,16,57,58,98,114,117,130],[0,4,8,10,12,14,16,57,58,98,113,114,130,133,138,154],[0,2,4,6,8,10,12,14,16,57,58,98,113,114,130,138,141,154],[0,4,6,8,10,12,14,16,57,58,98,113,114,130,133,138,141,154],[0,2,4,8,10,12,14,16,57,58,98,113,114,130,138,154,157],[0,2,4,8,10,12,14,16,57,58,73,98,101,114,130,138,154],[0,4,6,8,12,16,18,57,58,98,130,146],[0,4,6,8,12,16,18,57,58,98,130,141,146,149],[0,2,4,8,10,12,14,16,57,58,82,98,114,117,130,138],[0,2,4,8,10,12,14,16,57,58,73,98,106,113,114,130,153],[0,2,4,8,10,12,14,16,57,58,73,98,106,109,114,117,130,153,158],[0,2,4,8,10,12,14,16,57,58,73,98,105,106,113,114,130,154],[0,4,8,10,12,14,16,57,58,98,105,106,113,114,130,133,154],[0,2,4,8,10,12,14,16,57,58,73,98,105,110,113,114,130,154,157],[0,2,4,8,10,12,14,16,57,58,73,98,101,105,106,114,130,154],[0,2,4,6,8,10,12,14,16,57,58,73,81,98,106,109,114,130],[0,4,6,8,12,14,16,57,58,81,98,130,146],[0,4,6,8,12,14,16,57,58,81,98,130,146,149],[0,2,4,8,10,12,14,16,57,58,73,98,106,114,117,130],[0,2,4,8,10,12,14,16,57,58,98,114,117,130,138],[0,2,4,8,10,12,14,16,57,58,73,98,114,130,146],[0,2,4,8,10,12,16,18,57,58,73,98,130,146,153],[14,97],[0,2,4,8,10,12,16,18,57,58,73,98,114,130,138,146,154,157],[0,2,4,8,10,12,16,18,57,58,73,98,130,138,146,153],[0,2,4,8,12,14,16,18,57,58,98,130,133,138,154,157],[0,2,4,8,10,12,14,16,57,58,73,98,105,106,114,130,146,154,157],[0,2,4,8,10,12,14,16,57,58,73,98,105,110,114,130,146,154,157],[0,2,4,8,10,12,14,16,57,58,98,106,113,114,130,138],[0,4,6,8,12,16,57,58,62,81,82,85,98,105,109,113,130],[0,2,4,8,10,12,14,16,57,58,82,85,98,105,113,130],[0,4,6,8,12,14,16,57,58,98,105,113,130,154],[106,118,157],[141,145],[0,4,6,8,12,16,18,57,58,81,98,130,137],[0,2,4,6,8,12,14,16,18,57,58,113,137],[0,2,4,6,8,10,12,14,16,57,58,85,98,105,110,113,114,130,154],[0,4,6,8,12,16,57,58,81,114,117,130],[0,4,6,8,12,16,57,58,114,117,130],[0,4,6,8,12,16,57,58,81,106,109,113,114,154,157],[0,4,6,8,12,16,57,58,81,106,109,113,114,154],[0,4,6,8,12,14,16,57,58,81,109,113,114,154,157],[0,4,6,8,12,16,57,58,81,106,109,114],[0,4,6,8,10,12,16,57,58,81,106,109,146,154],[117,145],[0,4,6,8,10,12,16,57,58,81,106,109,146,154,157],[0,4,6,8,12,16,57,58,81,106,109,146,149,154,157],[0,4,6,8,12,16,57,58,81,106,109,146,154],[0,4,6,8,12,16,57,58,81,106,109,114,146,154],[0,4,6,8,10,12,16,57,58,81,106,109,146,149,154],[0,4,6,8,12,14,16,57,58,81,109,146,154],[0,4,6,8,12,14,16,57,58,81,109,114,146,154,157],[0,4,6,8,10,12,14,16,57,58,81,109,146,149,154],[0,4,8,12,16,57,58,106,109,146],[0,4,6,8,12,16,57,58,74,81,106,109,114,117],[0,4,6,8,12,14,16,57,58,81,105,113,114,138,154,157],[0,4,6,8,12,14,16,57,58,81,98,105,110,113,114,138,154,157],[0,4,6,8,12,14,16,57,58,81,105,138,146,154],[0,4,6,8,12,14,16,57,58,81,105,138,146,154,157],[0,4,6,8,12,14,16,57,58,81,105,138,146,149,154],[0,4,6,8,12,14,16,57,58,81,98,105,138,146,154],[0,4,6,8,12,14,16,57,58,81,98,105,114,138,146,154,157],[0,4,6,8,10,12,14,16,57,58,81,98,105,138,146,149,154],[73,101],[0,2,4,8,10,12,14,16,57,58,74,101,114,117,130],[0,2,4,8,10,12,14,16,57,58,74,114,117,130],[0,2,4,8,10,12,14,16,57,58,82,114,117,130,138,146],[0,4,6,8,12,16,57,58,74,85,109,114,117,146],[0,4,6,8,12,14,16,57,58,74,85,105,146],[0,4,6,8,10,12,14,16,57,58,82,85,105,113,114,146,149],[0,2,4,8,10,12,14,16,57,58,82,113,114,130,138,146],[0,2,4,8,10,12,14,16,57,58,74,114,117,130,138,146],[0,4,6,8,12,16,18,57,58,82,85,130,137,138,150,153],[0,4,6,8,12,14,16,57,58,82,85,98,105,106,118,154,157],[113,137],[0,4,6,8,10,12,14,16,57,58,82,85,105,113,114,154,157],[0,2,4,8,10,12,14,16,57,58,105,113,114,130,154],[0,2,4,8,10,12,14,16,57,58,81,114,117,130,146],[0,2,4,8,10,12,14,16,57,58,74,81,82,101,114,117,130,146],[0,4,6,8,12,14,16,58,61,98,105,113,114,130],[0,4,6,8,12,16,58,61,98,113,114,130],[0,4,8,10,12,14,16,58,61,97,98,113,114,130,138,154],[0,4,8,10,12,14,16,58,61,98,105,106,113,114,130,154],[0,4,6,8,12,16,58,61,81,97,109,113,114,137,154],[0,4,6,8,12,16,58,61,81,97,109,137,146,154],[0,4,6,8,12,16,18,57,58,73,74,114,130,142,146,153],[0,4,6,8,12,16,18,57,58,73,74,81,106,114,138,153],[0,4,6,8,12,16,18,57,73,74,81,106,114,138,153],[0,4,6,8,12,16,58,73,74,81,86,105,130,137,154],[0,4,6,8,12,16,58,73,74,86,105,130,154],[0,4,8,12,16,57,58,73,74,82,105,130,154],[0,4,8,12,16,18,73,74,114,142,146,153],[0,4,8,12,16,18,73,74,114,130,142,146,153],[0,4,6,8,10,12,16,18,57,58,73,74,82,85,106,114,137,153],[142,150,154],[0,4,8,10,12,14,16,18,58,78,98,113,114,117,130,145,146,153,154],[57,82,106,142],[86,149],[0,4,8,12,14,16,18,57,58,82,98,106,113,130,145,154,157],[114,146],[0,4,8,12,16,18,57,58,98,114,130,133,138,146,153],[0,4,8,12,16,18,57,58,82,98,114,130,138,146,149,153],[0,4,8,12,14,16,18,57,58,82,98,113,130,138,154,157],[0,4,8,12,14,16,18,57,58,82,113,133,138,146,149,154,157],[0,4,8,12,16,18,57,58,98,114,130,138,141,146],[0,4,8,12,16,18,57,58,98,114,130,133,138,141,146],[0,4,8,12,14,16,18,57,58,82,113,130,133,138,141,146,149,154,157],[0,2,4,8,12,16,18,57,58,98,101,114,130,138,146,153],[0,4,8,12,14,16,18,57,58,82,113,138,145],[0,4,8,12,14,16,18,57,58,82,138,145],[0,2,4,8,12,14,16,18,57,58,82,97,130,133,138,158],[0,4,6,8,12,14,16,18,57,58,82,85,105,137,138,141,145],[62,81,109],[0,4,8,12,14,16,18,57,58,82,98,113,130,138,146,149,158],[0,4,8,12,14,16,18,57,58,82,98,113,130,138,145,158],[0,4,8,12,14,16,18,57,58,82,138,141,146,149],[0,4,8,12,14,16,18,57,58,82,98,101,114,130,138,145,158],[0,4,8,12,16,18,57,58,98,114,117,130,138,146,153],[0,4,8,12,14,16,18,57,58,98,109,114,117,130,138,145,158],[0,4,8,12,14,16,57,58,98,113,114,130,146],[0,4,8,12,16,57,58,98,113,114,130,133,146],[0,4,8,12,16,57,58,98,113,114,130,146,149],[0,4,8,12,14,16,18,57,58,82,106,113],[98,153],[0,4,6,8,10,12,14,16,57,58,98,113,114,130,133,146],[0,4,6,8,10,12,14,16,57,58,98,113,114,130,146,149],[0,4,8,12,16,18,57,58,98,114,130,133,146,153],[0,4,8,12,16,18,57,58,82,98,114,130,146,149,153],[0,2,4,8,12,16,57,58,73,98,101,114,130,146],[0,2,4,6,8,10,12,14,16,57,58,73,98,101,114,130,146],[0,2,4,8,12,16,18,57,58,98,101,114,130,146,153],[0,4,6,8,10,12,14,16,57,58,81,98,106,109,114,130,146,158],[0,4,8,12,16,57,58,82,98,114,117,130,146],[0,4,6,8,10,12,14,16,57,58,82,98,114,117,130,146],[0,4,6,8,10,12,14,16,57,58,82,98,106,113,114,130,146,153,158],[0,4,6,8,10,12,14,16,57,58,98,106,109,114,117,130,146,153,158],[0,4,6,8,10,12,14,16,57,58,98,105,106,113,114,130,146,154],[0,4,6,8,10,12,14,16,57,58,98,105,106,113,114,130,133,146,154],[0,4,6,8,10,12,14,16,57,58,98,105,106,113,114,130,146,149,154],[0,4,6,8,10,12,14,16,57,58,98,105,110,113,114,130,146,154,157],[0,4,6,8,10,12,14,16,57,58,98,105,110,113,114,130,146,149,154,157],[0,2,4,6,8,10,12,14,16,57,58,73,98,101,105,106,114,130,146,154],[0,4,8,12,14,16,57,58,98,105,114,130,146],[0,4,8,12,14,16,57,58,98,105,114,130,146,149],[0,4,6,8,10,12,14,16,57,58,81,98,106,109,114,130,146],[18,141,153],[0,4,6,8,10,12,14,16,57,58,82,98,106,114,117,130,146,154],[0,4,6,8,10,12,14,16,57,58,82,98,113,114,130,146],[0,4,6,8,10,12,14,16,57,58,98,114,117,130,146],[0,4,8,12,16,18,57,58,98,114,117,130,138,146,153,158],[0,4,6,8,10,12,16,18,57,58,98,114,130,146],[0,4,6,8,10,12,16,18,57,58,82,98,114,130,138,146,154,157],[0,4,6,8,10,12,16,18,57,58,98,114,130,138,146,153],[0,4,8,12,14,16,18,57,58,82,98,110,130,138,154,157],[0,4,6,8,10,12,16,18,57,58,98,114,130,146,153],[0,4,6,8,10,12,14,16,57,58,98,110,114,130,146,154,157],[0,4,6,8,10,12,14,16,57,58,98,106,114,130,146,154,157],[0,4,8,12,14,16,18,57,58,82,113,134,138,153,154],[0,4,8,12,14,16,18,57,58,98,110,130,142,145,153,154],[0,4,8,12,14,16,18,57,58,82,98,110,113,130,138,149],[114,150],[0,4,8,12,16,18,57,58,98,130,138,141,149,150,154,157],[0,4,8,12,16,18,57,58,98,130,138,150,153],[0,2,4,8,12,16,18,57,58,73,98,130,133,138,150,153],[0,4,6,8,12,16,18,57,58,81,98,130,137,138,141,150],[62,85,105],[109,113,145,154],[0,4,8,12,14,16,18,57,58,82,98,110,113,130,138,145,150,154,157],[0,2,4,8,12,16,18,57,58,98,101,130,138,150,153],[0,4,8,12,16,18,57,58,98,130,142,146,153],[117,145,154],[0,4,8,12,14,16,57,58,98,105,110,113,114,130,154,157],[0,4,8,12,14,16,57,58,98,105,106,113,118,130,154,157],[0,4,6,8,12,16,18,57,58,82,85,98,130,138,146,153],[0,4,6,8,12,14,16,18,57,58,82,85,105,137,138,145],[0,4,6,8,10,12,14,16,57,58,82,85,98,105,106,113,114,130],[0,4,6,8,10,12,14,16,57,58,82,85,98,105,106,113,114,130,154],[0,4,8,12,16,18,57,58,82,85,98,130,138,150,153],[0,4,8,12,16,18,57,58,106,114,117,130,138,146],[0,4,8,12,16,18,57,58,106,114,117,130,138,146,153,158],[0,4,8,10,12,16,57,58,106,113,138,146],[0,4,8,12,16,57,58,105,106,113,114,138,146],[0,4,8,12,14,16,57,58,102,106,113,114,138,146],[0,4,8,12,14,16,57,58,105,106,138,146,154,157],[18,114],[0,4,8,12,14,16,57,58,105,106,113,114,138,146,149,154,157],[0,4,8,10,12,14,16,57,58,98,105,106,113,114,138,146,154],[0,4,8,12,16,18,57,58,106,114,130,138,146],[113,158],[0,4,8,10,12,16,18,57,58,106,114,117,130,138,146],[0,4,8,12,16,57,58,105,106,138,146,154],[0,4,8,10,12,16,57,58,105,106,138,154,157],[0,4,8,10,12,16,57,58,105,106,114,138,154],[0,4,8,10,12,14,16,57,58,105,106,138,154,157],[0,4,8,12,16,18,57,58,73,74,130,142,146,153],[0,4,8,12,16,57,58,82,114,117,130],[0,4,6,8,10,12,14,16,57,58,82,114,117,130],[0,4,8,12,16,18,57,58,73,82,114,117,130],[0,4,8,10,12,16,57,58,73,78,82,113,138,146,154],[0,4,8,12,14,16,57,58,81,82,98,105,146],[0,4,8,10,12,14,16,57,58,74,81,98,105,146,149],[0,4,6,8,10,12,14,16,57,58,82,113,114,130],[0,4,8,12,16,18,57,58,73,82,114,130],[0,4,6,8,10,12,14,16,57,58,74,114,117,130],[18,158],[0,4,8,10,12,16,18,57,58,73,74,114,117,130,158],[0,4,6,8,10,12,14,16,57,58,105,106,113,114,130,154],[0,4,8,10,12,16,18,57,58,130,138,150],[0,4,6,8,10,12,14,16,57,58,81,82,114,117,130,146,154],[0,4,6,8,10,12,14,16,57,58,74,81,82,114,117,130,146,158],[0,4,8,10,12,16,18,57,58,130,138,146],[0,2,4,8,12,16,18,58,61,73,98,114,130,138,146,153],[0,2,4,8,12,14,16,18,58,61,97,145],[130,138,158],[0,2,4,8,12,16,58,61,73,98,113,114,130,146],[0,2,4,6,8,10,12,14,16,58,61,73,98,113,114,130,146],[0,2,4,8,12,16,18,58,61,73,98,114,130,146,153],[0,2,4,6,8,10,12,14,16,58,61,73,98,105,106,113,114,130,146,154],[0,2,4,8,12,16,18,58,61,73,98,130,138,150,153],[0,4,8,12,16,18,57,58,82,98,114,130,138,146,153],[0,4,6,8,12,16,57,58,81,98,105,110,113,114,130,137],[0,4,8,12,16,57,58,98,105,110,113,114,130],[0,4,6,8,12,16,57,58,81,106,109,113,114],[0,4,6,8,12,16,58,61,81,98,105,110,113,114,130,137],[0,2,4,8,12,16,58,61,98,105,110,113,114,130],[0,4,6,8,12,16,58,61,81,109,113,114,137],[0,4,8,10,12,14,16,58,74,82,85,98,105,106,113,130],[0,4,6,8,10,12,16,58,74,82,85,98,105,106,130],[62,81,109,141],[80,180],[0,4,8,10,12,14,16,74,81,82,98,114,117,130],[137,145,157],[0,4,8,12,14,16,74,81,82,98,114,117,130],[0,4,6,8,12,14,16,74,81,82,97,98,105,106,113,114,130,154],[0,4,8,10,12,14,16,74,81,82,98,106,113,114,130],[0,4,6,8,12,16,18,62,74,81,82,98,130,138,146,153],[0,4,8,10,12,16,18,74,81,82,98,130,146],[0,4,8,10,12,16,18,74,81,82,98,130,133,146],[0,4,8,12,16,18,74,81,82,98,130,138,146,153,158],[0,4,8,12,14,16,74,81,82,98,130],[0,2,4,6,8,10,12,14,16,74,81,82,98,130],[0,4,8,12,16,18,74,81,82,98,130,138,146,149,154,157],[0,4,8,12,16,18,74,81,82,98,130,133,138,146,153],[0,4,6,8,12,16,18,58,74,81,82,98,130,138,141,146],[0,4,8,10,12,16,18,74,81,82,98,130,138,146,149],[0,4,8,12,16,18,74,81,82,98,130],[0,4,8,12,16,18,74,81,82,98,130,133],[0,4,8,12,16,18,74,81,82,98,130,154,157],[0,2,4,8,12,16,18,74,81,82,98,101,129,130,138,146,153],[0,4,6,8,10,12,14,16,74,81,82,97,98,113,130,154,157],[0,2,4,6,8,10,12,14,16,74,81,82,97,98,113,130,133,154,157],[0,2,4,6,8,10,12,16,18,74,81,82,98,130,138,146,153,158],[0,4,6,8,10,12,16,18,74,81,82,98,101,130,138,146,153,158],[0,4,6,8,10,12,14,16,74,81,82,98,113,130],[0,2,4,6,8,10,12,14,16,74,81,82,98,113,130,133],[0,2,4,6,8,10,12,14,16,74,81,82,98,106,114,130,154,157],[0,4,6,8,10,12,14,16,74,81,82,98,113,130,154],[0,2,4,6,8,10,12,14,16,74,81,82,98,113,130,133,154],[0,4,6,8,10,12,14,16,74,81,82,98,113,130,154,157],[0,2,4,8,12,16,18,57,74,77,82,98,129,130,138,146,153],[0,4,8,10,12,14,16,74,98,106,118,130,154,157],[102,110,114],[0,2,4,6,8,10,12,14,16,74,98,105,106,118,130,154,157],[0,4,6,8,10,12,14,16,74,98,105,106,118,130,133,154,157],[13,15,99,111,115,119],[107],[0,4,6,8,10,12,16,18,74,98,130,134,138,142,145,146,150,153,158],[58,105],[204],[0,4,8,12,16,18,74,82,85,98,130,138,146,153],[0,4,8,12,16,18,74,98,130,138,146,153,158],[0,4,8,12,16,74,81,82,98,114,117,130,138],[0,2,4,6,8,10,12,14,16,74,81,82,98,130,146],[0,4,8,12,14,16,74,81,82,98,130,146,154],[18,106],[0,4,8,12,14,16,74,81,82,98,130,146,149,154,157],[0,2,4,6,8,10,12,14,16,74,81,82,98,130,146,149,154],[0,2,4,6,8,10,12,14,16,74,81,82,98,130,146,154,157],[0,4,6,8,10,12,14,16,73,74,81,82,98,101,130,146,154],[0,4,8,12,16,18,74,81,82,98,130,138,153],[0,2,4,6,8,10,12,14,16,74,81,82,97,98,106,113,118,130,154,157],[0,4,6,8,10,12,14,16,74,81,82,97,98,106,113,118,130,133,154,157],[0,2,4,6,8,10,12,14,16,57,74,81,82,97,98,130,138],[0,2,4,6,8,10,12,16,18,74,81,82,98,130,138,153],[0,4,6,8,10,12,14,16,74,81,82,98,101,130,138],[0,4,6,8,10,12,16,18,74,81,82,98,101,130,138,153],[0,2,4,6,8,10,12,14,16,74,81,82,98,106,118,130,154,157],[0,2,4,6,8,10,12,14,16,74,81,82,98,113,114,130,133,154,157],[0,2,4,6,8,10,12,14,16,57,74,77,82,97,98,130,146,154],[0,2,4,6,8,10,12,14,16,74,82,85,98,105,130,154],[0,2,4,6,8,10,12,14,16,57,74,81,82,98,114,117,130,146,149],[0,4,6,8,10,12,14,16,74,81,82,98,114,117,130,138,146],[0,2,4,6,8,10,12,14,16,57,74,81,82,97,98,117,130,138,146],[0,4,6,8,10,12,14,16,74,81,82,98,101,117,130,138,146],[0,4,6,8,10,12,14,16,74,81,82,98,113,114,130,146,149],[0,2,4,6,8,10,12,14,16,74,81,82,98,113,114,130,133,146,149],[0,2,4,6,8,10,12,14,16,74,81,98,105,106,130,146],[0,2,4,6,8,10,12,14,16,74,98,106,109,130,146],[0,2,4,6,8,10,12,14,16,57,74,97,98,106,118,130,138,154,157],[0,4,8,10,12,16,18,74,98,106,130,138,146,153,158],[0,4,8,10,12,16,18,74,81,98,106,109,130,138,146,153,158],[0,4,6,8,10,12,14,16,74,81,97,98,106,118,130,138,154,157],[0,4,6,8,12,14,16,74,98,102,106,110,113,114,118,130,154,157],[58,109,137],[0,4,8,12,14,16,74,98,110,114,130,154,157],[102,106,118],[113,153],[0,2,4,6,8,10,12,14,16,74,98,105,110,113,114,130,154,157],[0,4,6,8,10,12,14,16,74,98,105,110,113,114,130,133,154,157],[13,15,99,107,111],[0,4,8,12,14,16,18,74,98,110,130,138,145,150],[0,4,8,10,12,16,18,74,81,98,114,130,138,145,146,153,158],[86,117],[0,4,8,12,14,16,18,74,98,130,138,145,153,154],[105,146],[0,4,8,10,12,16,58,74,82,85,105,106,114,117,154],[0,4,6,8,10,12,16,58,74,82,85,105,117,138,154],[137,145,153],[0,4,8,12,16,18,82,85,98,130,138,146,153],[0,4,8,10,12,14,16,73,74,81,82,102,105,106,114,117,146],[0,4,8,10,12,16,73,78,81,82,97,98,113,138,146,154],[0,4,8,12,16,18,81,82,117,130,138,150,158],[0,4,8,12,14,16,81,82,130,146],[0,2,4,6,8,10,12,14,16,81,82,113,130,146],[0,4,8,12,16,18,81,82,98,138,154,157],[0,4,8,12,16,18,81,82,130,138,150],[0,4,8,12,16,18,81,82,130,133,138,149,150],[0,4,8,10,12,16,18,58,74,81,82,98,138,149],[0,4,8,12,16,18,81,82,130,138,141,150],[0,4,8,12,16,18,81,82,138],[0,4,8,12,16,18,73,81,82,114,130,138,150],[0,4,8,12,16,18,81,82,114,130,133,138,149,150],[0,4,8,12,16,18,73,81,82,114,154,157],[0,2,4,8,12,16,18,57,82,106,130,138,150],[0,4,8,12,14,16,18,98,106,113,138,145,154,157],[0,4,8,12,16,18,73,106,114,130,138,150],[0,4,8,12,16,18,106,114,130,133,138,149,150],[0,4,8,12,16,18,82,106,130,138,150],[0,4,8,12,16,18,58,82,85,130,138,150],[0,4,8,10,12,16,18,106,114,130,138,146],[0,4,8,10,12,16,18,106,114,117,130,138,146],[14,82,154],[0,4,8,10,12,16,18,106,109,114,130,138,146],[0,4,8,10,12,16,18,74,106,114,130,138,146],[0,4,8,10,12,16,18,74,82,106,114,117,130,138,145,146],[0,4,6,8,10,12,16,18,74,106,109,114,130,138,146],[0,2,4,6,8,10,12,14,16,82,85,98,105,130,138,154],[0,4,8,12,16,18,58,82,85,130,142,150],[0,2,4,6,8,10,12,14,16,74,81,105,106,130,138,146],[0,2,4,6,8,10,12,14,16,58,74,106,109,130,138,146],[0,4,8,10,12,16,18,57,58,106,130,142,146],[0,4,6,8,10,12,16,18,57,81,106,109,130,142,146,158],[0,2,4,8,12,16,18,57,58,61,73,74,77,81,82,98,101,114,129,130,133,153],[0,2,4,8,10,12,14,16,58,61,73,74,97,98,106,130,138],[114,153],[0,2,4,8,10,12,14,16,58,61,73,74,97,98,106,113,118,130,138],[0,2,4,6,8,12,16,18,57,58,73,74,82,85,98,106,129,130,137,153],[97,105],[0,2,4,6,8,10,12,14,16,57,58,73,74,81,82,97,98,105,110,113,114,130,133,138],[0,2,4,6,8,10,12,14,16,57,58,73,74,82,97,98,110,113,114,130,133,138,141],[0,4,6,8,12,16,18,58,62,73,74,81,82,85,114,137,141,153],[0,2,4,8,10,12,14,16,58,98,106,113,114,130,138],[0,4,8,12,14,16,18,57,58,82,113,134,138,145,153,154],[0,4,8,12,14,16,18,57,58,98,110,113,130,142,145,153,154],[0,2,4,8,10,12,14,16,58,61,73,74,82,97,98,130,138],[0,2,4,8,10,12,14,16,58,61,73,74,82,97,98,113,130,138],[0,4,8,12,16,73,74,81,82,105,130,154],[0,4,8,10,12,14,16,82,98,113,114,130,138],[0,4,8,12,14,16,58,61,113,114],[98,106,157],[0,4,8,12,16,58,61,113,114],[0,4,6,8,10,12,14,16,58,61,81,113,114],[0,4,6,8,10,12,14,16,58,61,113,114],[0,4,6,8,10,12,14,16,58,61,97,113,114,130,138,154],[0,4,6,8,10,12,14,16,58,61,81,98,106,113,114,154],[0,4,8,12,16,58,61,97,98,113,114,154],[0,4,8,12,16,58,61,97,98,146,154],[0,4,6,8,10,12,14,16,57,58,82,85,97,102,105,106,114,130,138],[0,2,4,8,10,12,16,18,57,58,73,74,82,114,117,133,134,138,145,146,153],[0,2,4,6,8,12,14,16,18,57,58,102,106,113,129,130,138,150,153,154],[0,2,4,8,12,16,57,58,73,74,97,138,154],[133,153],[0,4,6,8,10,12,14,16,57,58,81,82,105,113,114,138],[98,110,153],[0,4,6,8,10,12,14,16,57,58,74,81,82,105,113,114,138],[0,2,4,8,12,14,16,18,57,58,82,97,133,138],[0,2,4,8,12,16,57,58,73,82,114,138,146],[0,4,6,8,10,12,14,16,57,58,74,81,82,105,113,114,130,138],[0,2,4,8,12,16,57,58,73,101,114,130,146],[0,4,6,8,10,12,14,16,57,58,81,82,105,114,138,146],[0,4,6,8,10,12,16,18,57,58,74,81,138,146],[0,4,6,8,10,12,16,18,57,58,81,130,146],[0,2,4,8,12,14,16,18,57,58,97,133,134,138,145],[0,2,4,8,12,16,18,57,58,73,114,129,134,138,146],[0,2,4,8,12,14,16,18,57,58,97,113,133],[0,2,4,8,12,16,18,57,58,73,129,134,138,146,153],[0,4,8,10,12,14,16,81,82,98,105,110,113,114,130,138],[0,4,6,8,10,12,14,16,57,74,81,82,105,113,114,130,138],[0,4,8,12,14,16,18,58,61,110,134,142,145],[0,4,8,12,16,18,58,61,114,134,142,146],[0,4,8,12,14,16,18,58,61,110,113,142],[0,4,8,12,16,18,58,61,134,142,146,153],[0,4,6,8,10,12,14,16,58,74,82,85,105,106,114,130,154],[0,4,6,8,10,12,14,16,58,74,82,85,97,98,105,106,114,154],[0,4,6,8,10,12,14,16,74,81,82,98,106,114,117],[0,4,6,8,10,12,14,16,58,74,81,82,98,114,117],[0,4,6,8,10,12,14,16,74,81,82,97,105,117,130],[0,2,4,6,8,10,12,14,16,74,81,82,105,117,130,133,157],[0,4,6,8,10,12,14,16,58,81,82,105,130],[0,2,4,6,8,10,12,14,16,58,81,82,97,105,130,133,157],[0,4,6,8,10,12,16,18,81,82,130,138],[74,149],[0,4,6,8,10,12,16,18,81,82,130,133,138,149,157],[0,4,6,8,10,12,16,18,81,82,130],[0,4,6,8,10,12,16,18,81,82,130,133,149,157],[0,4,6,8,10,12,14,16,74,102,105,106,114,130,154],[0,2,4,6,8,10,12,14,16,74,102,105,106,114,130,133,154,157],[0,4,6,8,10,12,14,16,74,105,106,130,154,157],[0,4,6,8,10,12,14,16,74,82,106,130,154],[0,4,8,10,12,14,16,18,105,130],[82,117,145],[0,4,6,8,10,12,14,16,58,74,102,106,109,114,130],[0,4,6,8,10,12,14,16,102,105,106,114,130],[0,4,6,8,10,12,14,16,82,102,106,114,117,130],[0,4,6,8,10,12,14,16,58,101,102,106,109,114,130,153,158],[0,4,6,8,10,12,14,16,58,97,102,105,106,114,130,154],[0,2,4,6,8,10,12,14,16,58,97,102,105,106,114,130,133,154,157],[0,4,6,8,10,12,14,16,58,97,98,105,106,118,130,154,157],[0,4,6,8,10,12,14,16,58,82,97,106,130,154],[0,2,4,8,12,14,16,18,129,130,138,145],[0,4,6,8,10,12,14,16,102,106,109,114,130],[0,4,6,8,10,12,14,16,58,74,102,105,106,114,130],[0,4,6,8,10,12,14,16,58,74,82,102,106,114,117,130],[0,4,6,8,10,12,14,16,74,102,106,109,114,130,153,158],[0,4,8,10,12,14,16,18,98,113,118,154,157],[74,82],[97,106],[0,4,8,12,14,16,18,82,98,113,154,157],[0,4,6,8,10,12,14,16,74,77,97,102,105,106,118,130,154],[0,4,6,8,10,12,14,16,74,82,85,102,105,106,114,130,145,150,154],[0,4,6,8,10,12,14,16,82,85,97,102,105,106,114,130,154],[18,145,150,153],[0,4,6,8,10,12,14,16,78,81,82,98,117,130,146],[0,4,6,8,10,12,16,18,78,81,82,98,130,138,154,157],[0,4,6,8,10,12,16,18,73,78,81,82,98,130,133,138,141,149,154,157],[0,4,6,8,10,12,16,18,73,81,82,98,114,130,157],[0,4,6,8,10,12,16,18,81,82,98,114,130,133,149,157],[0,4,6,8,10,12,14,16,82,97,98,106,130,146,154],[0,4,6,8,10,12,14,16,58,73,78,81,82,117,130,146],[0,4,6,8,10,12,14,16,73,78,81,82,97,98,113,138,154,157],[0,4,6,8,10,12,16,18,74,81,82,114,130,138,149],[0,4,6,8,10,12,16,18,73,74,81,82,114,130,133,138,149,157],[0,4,6,8,10,12,14,16,74,113,114,130,154],[129,145,153],[0,4,6,8,10,12,14,16,58,74,97,98,110,113,114,130,154],[0,2,4,6,8,10,12,14,16,58,61,73,97,102,105,110,114,130,154],[18,129,145,153],[116,144],[0,4,6,8,10,12,14,16,74,81,86,97,102,106,113,114,130],[0,2,4,6,8,10,12,14,16,74,81,86,102,106,113,114,130,133,157],[0,2,4,6,8,10,12,14,16,61,73,74,81,97,130,146],[0,4,6,8,10,12,14,16,74,81,86,97,102,106,114,117,130],[0,4,6,8,10,12,14,16,58,74,81,86,102,106,113,114,130],[0,4,6,8,10,12,14,16,58,74,81,86,102,106,109,114,117,130],[0,4,6,8,10,12,14,16,81,102,106,114,117,130],[0,4,6,8,10,12,14,16,58,81,102,106,114,117,130,153],[0,4,6,8,10,12,14,16,58,81,102,106,113,114,130],[0,2,4,6,8,10,12,14,16,58,81,97,102,106,113,114,130,133,157],[0,4,6,8,10,12,14,16,58,73,81,130,146],[0,4,6,8,10,12,14,16,58,81,102,106,114,130],[0,4,6,8,10,12,14,16,81,102,106,113,114,130],[0,4,6,8,10,12,14,16,81,102,106,109,114,130],[0,4,6,8,10,12,14,16,58,74,81,86,102,106,114,117,130],[0,4,6,8,10,12,14,16,74,81,86,101,102,106,114,117,130,153],[0,4,6,8,10,12,16,18,74,81,98,154,157],[0,4,6,8,10,12,16,18,58,81,98,114,154,157],[0,2,4,6,8,10,12,14,16,57,74,77,86,97,102,106,113,118,130],[0,4,6,8,10,12,14,16,73,98,110,114,117,130],[0,4,6,8,10,12,14,16,73,98,110,113,114,130],[0,4,6,8,10,12,14,16,73,78,82,98,109,110,114,117,130],[0,4,8,10,12,14,16,18,98,113,154,157],[73,97,106],[0,4,6,8,10,12,14,16,58,98,110,113,114,130],[0,4,6,8,10,12,14,16,58,74,86,114,117,130],[0,4,6,8,10,12,14,16,58,78,82,109,114,117,130],[0,4,6,8,10,12,14,16,78,82,97,98,106,113,146,154,157],[0,4,6,8,10,12,14,16,58,61,81,86,97,102,110,113,114,130],[0,4,6,8,10,12,14,16,82,85,97,102,105,106,114,130],[0,4,6,8,10,12,14,16,74,82,85,102,105,106,114,130],[0,4,6,8,10,12,14,16,73,74,81,82,113,114,130],[0,2,4,6,8,10,12,14,16,74,81,82,97,113,114,130,133],[0,4,6,8,10,12,14,16,58,73,78,81,82,105,106,117,130],[0,4,6,8,10,12,14,16,73,74,105,106,113,114,130],[0,2,4,6,8,10,12,14,16,74,97,105,106,113,114,130,133],[0,4,6,8,10,12,14,16,73,74,82,106,130],[0,4,6,8,10,12,14,16,78,81,82,98,106,117,130],[0,4,6,8,10,12,14,16,58,74,114,117,130,146],[0,4,6,8,10,12,14,16,58,74,113,114,130,146],[0,4,6,8,10,12,14,16,58,78,82,114,117,130,146],[109,137],[0,4,6,8,10,12,14,16,74,97,113,114,130,154],[0,4,6,8,10,12,14,16,73,98,114,117,130,146],[0,4,6,8,10,12,14,16,73,78,82,98,114,117,130,146],[0,2,4,8,12,14,16,57,58,73,82,97,98,110,113,114,138],[133,134],[0,2,4,8,12,16,18,57,58,73,129,130,142,146],[101,145,154],[0,4,8,12,16,57,58,105,106,138,146],[0,2,4,8,12,14,16,18,73,97,113,134,145],[0,2,4,8,12,16,18,73,114,134,138,146,153],[0,2,4,8,12,16,18,73,114,130,142,146,153],[0,2,4,8,12,16,73,105,113,114,146,154],[0,4,8,12,14,16,18,113,134,145],[0,4,8,12,16,18,114,134,142,146,153],[0,4,8,12,16,18,114,130,142,146,153],[0,4,8,12,16,105,106,113,114,146,154],[0,4,6,8,10,12,14,16,74,81,82,102,105,106,113,114,154],[0,2,4,6,8,10,12,14,16,57,73,74,81,82,102,105,106,113,114,154,157],[0,4,6,8,10,12,14,16,74,81,82,102,113,130,154],[0,4,6,8,10,12,14,16,81,82,102,105,106,113,114],[0,2,4,6,8,10,12,14,16,57,73,81,82,102,105,106,113,114,157],[0,4,6,8,10,12,14,16,81,82,98,105,106,113,114,146],[0,2,4,6,8,10,12,14,16,57,81,82,98,105,106,113,114,146],[0,4,6,8,10,12,14,16,97,98,105,106,114,130,146,154],[0,4,6,8,10,12,14,16,81,82,105,106,113,114,146,149],[0,2,4,6,8,10,12,14,16,57,81,82,105,106,113,114,146],[0,2,4,6,8,10,12,14,16,105,106,130,146,154],[0,2,4,6,8,12,16,18,58,61,73,74,82,98,106,129,130,137,138,146,153,158],[0,4,6,8,12,14,16,18,58,82,98,106,113,130,137,138,153,158],[97,129,146],[0,4,8,10,12,14,16,81,82,97,102,106,113,114,130,138],[0,2,4,8,12,16,18,58,61,73,74,98,129,130,138,146,153,158],[0,4,8,12,16,18,98,114,130,138,146,153,158],[0,4,6,8,10,12,14,16,58,81,97,109,113,114,130,138],[0,2,4,8,12,16,18,58,61,73,114,130,138,146,153],[0,2,4,8,12,14,16,18,58,61,74,97,130,145],[0,2,4,8,12,16,58,61,73,113,114,146],[0,2,4,6,8,10,12,14,16,58,61,73,113,114,146],[0,2,4,8,12,16,18,58,61,73,114,146,153],[0,2,4,6,8,10,12,14,16,58,61,73,98,106,113,114,146,154],[0,2,4,8,12,16,18,58,61,73,130,138,150,153],[0,4,6,8,12,14,16,58,61,74,81,102,105,110,113,114,130],[141,142],[0,4,6,8,12,16,18,58,61,81,134,137,142,146],[109,110,145,154],[0,2,4,8,12,16,58,61,73,98,130,146],[0,4,8,10,12,14,16,58,78,81,82,98,106,113,114,130,154,157],[0,4,8,10,12,16,18,58,78,81,82,98,130,138,145,146,153,158],[0,4,6,8,10,12,16,18,58,78,81,82,98,130,138,141,145,146],[0,4,8,10,12,16,18,58,81,82,98,130,138,146,149],[0,4,8,10,12,16,18,58,78,81,82,98,130,133,138,146,149,153,158],[0,2,4,8,10,12,16,18,57,58,73,78,81,82,98,101,129,130,138,145,146,153,158],[0,4,8,10,12,16,18,58,78,81,82,98,130,138,145,146,153],[0,2,4,6,8,10,12,14,16,58,78,81,82,113,130,154,157],[0,2,4,6,8,10,12,14,16,57,58,73,78,81,82,97,98,113,130,133,154,157],[0,2,4,6,8,10,12,16,18,57,58,73,81,82,98,130,138,146,158],[0,2,4,6,8,10,12,14,16,58,81,82,97,98,106,113,114,130,133,157],[0,4,8,10,12,14,16,18,58,98,130,145,146,153,158],[0,4,8,12,16,18,58,98,106,130,138,146,153],[0,2,4,6,8,10,12,14,16,57,58,73,98,105,106,118,130,157],[0,2,4,6,8,10,12,14,16,58,97,98,105,106,118,130,133,157],[0,4,8,10,12,14,16,18,58,98,130,145,146],[78,82,113],[0,4,8,10,12,16,18,78,82,85,98,113,130,138,145,146,153,158],[0,4,8,10,12,16,18,74,82,114,117,134,138,145,146],[81,137,154],[0,2,4,6,8,10,12,14,16,74,81,82,98,114,117,138],[0,4,8,10,12,16,18,74,82,98,114,117,138,149],[0,2,4,6,8,10,12,14,16,57,81,82,130],[0,2,4,6,8,10,12,14,16,73,81,82,97,130,133,149,157],[0,2,4,6,8,10,12,14,16,57,81,82,97,138],[18,98,114,129],[0,2,4,6,8,10,12,16,18,57,81,82,98,114,138],[0,2,4,6,8,10,12,14,16,58,74,81,82,106,113,130,133,146,149],[0,2,4,6,8,10,12,14,16,81,82,97,106,113,130,133,146,149,157],[0,4,8,12,14,16,18,58,102,106,130,138,145,150,153,158],[0,4,8,12,14,16,18,58,114,117,130,138,145,150,153,158],[0,4,8,12,14,16,18,101,102,106,109,114,130,138,145,150,153,158],[0,4,8,12,14,16,18,102,106,130,138,145,150,153,154],[0,4,6,8,12,14,16,18,58,102,105,106,130,138,141,153,154],[81,97,114],[0,4,8,12,14,16,18,98,106,118,138,154,157],[0,4,8,12,14,16,18,102,106,130,133,138,150,157],[0,4,8,12,14,16,18,82,130,138,145,150,153,154],[0,2,4,8,12,14,16,18,130,138,145,153,154],[57,77],[0,4,8,12,14,16,18,58,102,106,109,130,138,145,150,153,154],[0,4,8,12,14,16,18,74,102,106,130,138,145,150,153,158],[0,4,8,10,12,14,16,18,74,114,117,130,145,150,153,158],[82,129,138],[0,4,8,12,14,16,18,58,74,102,106,109,130,138,145,150,153,158],[0,4,8,12,14,16,18,58,74,98,106,113,118,134,138,154,157],[0,4,8,12,14,16,18,98,106,113,118,134,138,154,157],[0,4,8,10,12,16,18,73,78,81,82,117,130,138,145,146,153],[0,2,4,6,8,10,12,14,16,73,78,81,82,113,154,157],[0,2,4,6,8,10,12,14,16,57,74,81,82,97,117,138,146],[18,98,129,145],[0,2,4,6,8,10,12,14,16,58,73,74,81,82,106,113,114,130,133,149],[0,2,4,6,8,10,12,14,16,57,58,73,98,105,110,113,114,130,157],[0,2,4,6,8,10,12,14,16,58,97,98,105,110,113,114,130,133,157],[146,158],[61],[73,105,114],[0,2,4,8,10,12,16,18,58,61,73,78,81,86,98,129,130,138,145,146,153,158],[0,4,8,12,16,18,74,82,85,98,130,138,146,153,158],[0,4,6,8,12,14,16,18,58,74,98,105,106,130,138],[97,114],[0,4,8,10,12,16,18,74,98,106,130,138,150,158],[0,4,6,8,10,12,16,18,74,98,106,109,130,137,138,150,158],[0,2,4,6,8,10,12,14,16,57,62,74,81,98,105,106,130],[0,2,4,6,8,10,12,14,16,57,74,98,106,109,130],[0,2,4,6,8,10,12,14,16,57,74,98,105,106,130],[0,2,4,6,8,10,12,14,16,73,74,97,98,105,106,130,133],[0,2,4,6,8,10,12,14,16,57,73,74,98,101,106,130],[0,2,4,6,8,10,12,14,16,57,62,74,81,98,106,109,130],[0,4,6,8,10,12,14,16,74,77,97,98,105,106,130],[0,2,4,6,8,10,12,14,16,57,74,81,82,98,130],[0,4,8,12,16,18,98,114,130,142,150],[0,4,8,10,12,16,18,73,74,114,117,130,142,146],[0,4,6,8,10,12,16,18,73,78,82,114,117,130,142,145,146,158],[14,137],[0,2,4,6,8,10,12,14,16,58,102,106,113,114,130],[0,2,4,6,8,10,12,14,16,58,78,82,114,117,130],[0,2,4,6,8,10,12,14,16,58,74,101,114,117,130],[0,4,8,12,14,16,18,113,145],[0,4,8,12,16,18,81,114,130,142,146,153],[0,4,8,12,16,18,81,114,134,142,146,153],[0,4,8,12,16,81,106,113,114,146,154],[0,4,6,8,10,12,14,16,78,81,82,98,105,106,113,114,138,146,153],[0,4,8,10,12,14,16,18,81,105,146,153],[82,149],[97,138],[0,4,6,8,10,12,14,16,81,82,98,105,106,113,114,138,146],[0,4,8,12,14,16,18,82,98,106,113,138,153],[81,105,114,146],[0,4,8,10,12,14,16,18,98,105,130,145,146,153,158],[0,4,8,12,14,16,18,82,98,106,130,138,145,153,154],[105,114,146],[0,4,6,8,10,12,14,16,81,82,102,105,106,113,114,138],[0,4,8,12,14,16,18,82,102,106,113,138,157],[81,105,114],[0,4,8,10,12,14,16,18,81,130,145,146,153,158],[97,129,138],[0,4,8,12,14,16,18,98,106,113,130,138,145,153,154],[81,114,146],[0,4,6,8,10,12,14,16,81,82,105,106,113,114,138],[0,4,8,12,16,18,73,81,82,106,114,138],[0,2,4,6,8,10,12,14,16,78,81,82,102,105,106,113,114,157],[0,2,4,6,8,10,12,14,16,78,81,82,97,102,105,106,113,114],[0,2,4,6,8,10,12,14,16,58,78,81,82,102,105,106,113,114,157],[0,2,4,6,8,10,12,14,16,58,78,81,82,102,105,106,113,114],[0,4,6,8,10,12,14,16,58,78,81,82,102,105,130],[0,2,4,6,8,10,12,14,16,78,81,82,102,105,106,113,114],[0,2,4,6,8,10,12,14,16,73,78,81,82,102,105,106,113,114,157],[0,2,4,6,8,10,12,14,16,57,78,81,82,102,130],[0,2,4,6,8,10,12,14,16,74,81,82,105,106,113,114],[0,2,4,6,8,10,12,14,16,73,74,81,82,105,106,113,114],[0,4,6,8,10,12,14,16,73,74,81,82,113,130],[0,2,4,6,8,10,12,14,16,58,61,73,74,82,97,146,154],[0,2,4,6,8,10,12,14,16,57,58,73,74,81,82,105,113,149],[18,98,106,137],[0,2,4,6,8,10,12,14,16,57,58,73,74,81,82,105,113,114],[0,2,4,6,8,10,12,16,18,57,58,73,74,81,82,114,117,130,138,141,145],[0,2,4,6,8,10,12,14,16,57,58,98,105,106,118,133,154,157],[18,113,137],[0,2,4,6,8,10,12,14,16,57,58,105,113,114,154,157],[0,2,4,6,8,10,12,14,16,57,58,73,74,81,82,101,113,149],[18,98,106],[0,2,4,6,8,10,12,14,16,57,58,73,74,81,82,101,105,113],[0,2,4,6,8,10,12,16,18,57,58,73,74,81,82,117,130,138,145],[0,2,4,6,8,10,12,14,16,57,58,73,154,157],[18,133],[0,2,4,6,8,10,12,14,16,57,58,73,98,105,106,113,114,149,154,157],[0,2,4,6,8,10,12,14,16,73,74,82,98,105,106,113,118,149,154,157],[58,137],[0,2,4,6,8,10,12,14,16,73,74,82,105,113,114,154,157],[18,141,145],[0,2,4,6,8,10,12,14,16,73,74,97,114,117,146,154],[0,2,4,6,8,10,12,14,16,73,74,82,98,106,113,114,146,149,154,157],[0,2,4,6,8,10,12,14,16,73,74,82,105,113,114,146,154,157],[0,2,4,6,8,10,12,14,16,58,61,73,97,98],[0,2,4,6,8,10,12,14,16,57,58,73,74,81,82,113],[0,2,4,6,8,10,12,14,16,57,58,73,74,81,82,105,106,113,149],[0,2,4,6,8,10,12,16,18,57,58,73,74,81,82,106,130,149],[0,2,4,6,8,10,12,16,18,57,58,130,154,157],[0,2,4,6,8,10,12,16,18,57,58,106,114,141,149,154,157],[0,4,8,10,12,16,18,114,117,130,142,146,153],[14,74,145],[0,2,4,6,8,10,12,14,16,73,74,82,98,110,113,114,146,154,157],[18,105,145],[0,2,4,6,8,10,12,14,16,73,74,82,105,106,113,114,146,149,154,157],[0,2,4,6,8,10,12,14,16,62,81,82,105,146,154],[18,137,145,153],[57,129],[0,2,4,6,8,10,12,14,16,57,62,81,82,105,114,117],[0,2,4,6,8,10,12,14,16,57,62,74,81,82,98,105,106,113,118,146,149,154,157],[0,2,4,6,8,10,12,14,16,57,62,74,81,82,105,113,146,154,157],[0,2,4,6,8,10,12,14,16,57,74,81,82,98,106,113,114,149,154,157],[0,2,4,6,8,10,12,14,16,57,74,81,82,105,113,154,157],[18,133,145],[0,2,4,6,8,10,12,14,16,58,61,73,97,98,106],[0,4,8,12,16,18,57,58,82,85,130,142,150],[0,2,4,6,8,10,12,14,16,57,58,73,74,81,82,109],[0,2,4,6,8,10,12,14,16,57,58,73,74,81,82,106,109],[0,2,4,6,8,10,12,16,18,57,58,73,74,81,82,106,130],[0,2,4,6,8,10,12,14,16,57,58,81,138,141,154,157],[0,2,4,6,8,10,12,14,16,57,58,81,98,110,114,138,154,157],[0,2,4,6,8,10,12,16,18,73,74,130,141,149,154,157],[0,2,4,6,8,10,12,16,18,73,74,106,114,154,157],[0,4,6,8,10,12,16,20,22,57,58,73,74,78,82,85,86,97,98,105,106,113,114,117,138,154,177,178,185,189,201],[0,2,4,6,8,12,14,16,18,20,57,58,73,74,82,85,105,106,130,137,138,146,153,154,170,178,186],[13,15,99,103,107,155],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,106,114,137,138,153,174,178,181,186,193,201,202],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,106,114,137,138,153,170,177,178,186,193,201,202],[174,182,190,198,206],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,106,114,137,138,153,170,174,177,178,182,186,190,198,201,202,206],[105,185,194],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,106,130,138,141,150,153,170,177,178,190,193,201,202],[105,145,185],[0,4,6,8,12,16,20,57,58,73,74,81,82,105,106,138,141,145,146,153,154,178,186,194,202],[0,4,6,8,10,12,16,20,57,58,73,74,82,85,97,98,105,106,113,114,137,138,145,170,178,202],[0,2,4,6,8,12,14,16,18,20,57,58,73,74,82,85,105,106,114,130,137,138,153,154,170,178,186],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,106,130,138,154,170,177,178,186,194,201],[0,4,6,8,10,12,14,16,20,22,57,58,73,74,81,82,97,98,105,106,114,117,146,154,157,170,181,182,185,186,193,194,201],[0,2,4,6,8,10,12,16,18,20,22,57,58,73,74,81,82,114,130,142,145,146,153,170,177,178,185,186,198,201,202],[0,4,6,8,10,12,16,20,57,58,73,74,81,82,97,98,105,106,114,117,137,145,146,170,186,202],[181,185,201],[0,2,4,8,10,12,14,16,18,20,57,58,73,74,81,82,113,114,130,145,146,153,154,170,178,186,202],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,114,137,153,181,186,193],[0,2,4,6,8,12,16,18,20,22,57,58,73,74,81,82,114,129,137,153,170,173,181,182,186],[0,4,6,8,10,12,16,18,20,22,57,58,73,74,81,82,114,117,137,145,153,181,185,186,189,193],[150,154,205],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,106,114,130,137,138,150,153,170,181,182,186,194,197],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,114,130,154,170,181,182,186,194,202,205],[137,153,193],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,130,154,170,181,182,186,189,194,197,202,205],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,130,154,170,177,182,186,194,201],[0,2,4,6,8,12,16,20,22,57,58,73,74,81,82,97,105,130,154,170,173,177,182,186,194,201],[0,4,6,8,10,12,16,20,22,57,58,73,74,81,82,105,113,130,154,170,177,182,185,186,189,194],[78,86,117,145],[137,149,153,193,202],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,114,130,154,170,177,182,186,194,197,201],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,106,114,130,137,138,150,153,170,177,182,186,193,202,205],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,114,137,153,177,186,189,194,197,202,205],[0,2,4,6,8,10,12,16,18,20,22,57,58,73,74,81,82,114,137,149,153,181,186],[78,86,117,145,189],[0,2,4,6,8,10,12,16,20,22,57,58,62,73,74,81,82,85,105,109,117,130,154,170,177,181,182,186,194,201],[129,137,145,153,202],[0,2,4,6,8,12,16,18,20,22,57,58,73,74,81,82,114,130,133,137,169,170,181,182,186,193],[0,2,4,6,8,12,16,20,22,57,58,73,74,81,82,97,105,130,133,154,170,177,182,186,194,201],[137,193,202],[0,4,6,8,12,16,18,20,22,57,58,62,73,74,81,82,85,114,137,138,141,177,181,186,193],[170,182,206],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,130,137,138,149,150,154,157,170,181,182,186,193],[185,194],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,130,154,157,170,177,182,186,194,201],[137,149,193,202],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,114,130,154,170,178,181,190,194,202,205],[141,153,193],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,130,154,170,178,181,189,190,194,197,202,205],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,130,154,170,177,178,190,194,201],[0,2,4,6,8,12,16,20,22,57,58,73,74,81,82,97,105,130,154,170,173,177,178,190,194,201],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,130,154,170,177,178,181,190,194],[62,85,109,137],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,114,130,154,170,177,178,190,194,197,201],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,130,141,142,146,153,170,178,181,190,193,202,205],[145,154,185],[0,4,6,8,12,16,18,20,22,57,58,73,74,81,82,114,141,146,153,181,194,197,202,205],[190],[0,2,4,6,8,10,12,16,18,20,22,57,58,73,74,81,82,114,141,145,146,153,177,189],[62,85,109,137,181],[190,194],[0,2,4,6,8,10,12,16,20,22,57,58,62,73,74,81,82,85,105,109,117,130,154,170,177,178,181,190,194,201],[78,86,113,149,185],[129,137,141,145,153,202],[0,2,4,6,8,12,16,20,22,57,58,73,74,81,82,97,105,130,133,154,170,177,178,190,194,201],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,130,154,157,170,177,178,190,194,201],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,105,130,137,138,145,150,153,154,170,194,202,205],[177,193],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,105,130,137,138,145,150,153,154,170,194,197,202,205],[177,189],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,105,130,137,142,145,146,153,154,170,194,202,205],[181,193],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,105,130,137,142,145,146,153,154,170,194,197,202,205],[0,2,4,6,8,10,12,14,16,18,20,57,58,62,73,74,81,82,85,97,105,109,113,130,137,141,142,145,146,153,154,170,194,202],[0,2,4,6,8,10,12,14,16,18,20,57,58,73,74,78,81,82,86,97,105,113,117,130,137,138,145,149,150,153,154,170,194,202],[22,181,201],[0,4,6,8,12,16,20,22,57,58,62,73,74,81,82,85,105,106,109,130,170,177,181,182,186,198,201],[0,4,6,8,10,12,16,18,20,22,57,58,73,74,81,82,114,117,137,145,153,181,185,186,193],[0,4,6,8,10,12,16,20,22,57,58,73,74,81,82,105,114,117,130,170,177,182,185,186,194,201],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,146,149,154,157,181,186,194,201],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,105,138,146,154,157,170,177,182,186,194,201],[0,4,6,8,12,14,16,20,57,58,73,74,81,82,105,138,141,145,146,153,186,194,202,205],[118,193],[0,4,6,8,12,16,20,57,58,73,74,81,82,105,138,141,145,146,153,154,186,189,194,197,202,205],[0,4,6,8,12,16,20,57,58,73,74,81,82,105,138,141,145,146,153,154,186,194,202],[0,4,6,8,10,12,16,20,57,58,73,74,78,81,82,86,105,113,117,138,141,145,146,149,153,154,186,189,194,202],[0,4,6,8,12,14,16,20,57,58,73,74,81,82,105,138,141,145,146,153,154,186,194,197,202],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,105,141,145,146,153,154,186,194,202,205],[0,4,6,8,12,14,16,18,20,57,58,73,74,81,82,105,141,145,146,153,154,186,194,197,202,205],[0,4,6,8,12,16,20,57,58,73,74,81,82,105,138,141,145,146,154,186,194],[0,4,6,8,10,12,16,20,57,58,73,74,78,81,82,86,105,113,117,138,141,145,146,149,154,186,189,194,202],[0,4,6,8,12,16,20,57,58,73,74,81,82,98,105,138,141,146,154,157,186,194,202],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,105,137,145,146,178,186,194,202,205],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,105,137,145,146,153,154,178,186,194,197,202,205],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,105,130,137,142,145,146,153,154,178,186,194,202,205],[0,4,6,8,12,14,16,18,20,57,58,73,74,81,82,105,130,137,142,145,146,153,154,178,186,194,197,202,205],[0,4,6,8,12,16,20,22,57,58,73,74,81,82,106,109,113,114,154,157,170,177,178,190,194,201],[0,4,6,8,12,16,20,57,58,73,74,81,82,98,109,113,141,154,157,186,194,202],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,98,109,113,137,145,146,194,202,205],[0,4,6,8,12,16,18,20,57,58,73,74,81,82,106,109,113,114,130,137,138,145,150,154,194,202,205],[153,177,193],[0,4,6,8,12,14,16,18,20,57,58,73,74,81,82,106,109,113,114,137,145,146,153,154,194,197,202,205],[0,4,6,8,12,14,16,18,20,57,58,73,74,81,82,98,109,113,130,137,138,145,150,153,154,194,197,202,205],[0,2,4,6,8,12,16,18,20,22,57,58,74,77,81,82,129,137,153,181,193],[170,182,186],[0,2,4,6,8,12,16,20,22,57,58,74,77,81,82,97,105,130,154,170,177,182,186,194,201],[0,2,4,6,8,12,16,20,22,57,58,74,77,81,82,97,105,130,154,170,177,178,190,194,201],[0,2,4,6,8,12,16,20,57,58,74,77,81,82,97,105,138,141,145,153,154,194,202],[0,4,8,12,16,18,20,22,57,58,73,74,82,85,153,193],[170,182,190],[0,4,8,12,16,20,22,57,58,73,74,82,85,130,154,170,182,190,194,201],[0,4,8,12,16,20,22,57,58,73,74,82,85,130,154,170,178,190,194,201],[0,4,8,12,16,20,57,58,73,74,82,85,138,145,146,153,154,194,202],[0,2,4,8,12,16,18,20,22,57,58,74,77,82,85,129,150,153,190,193],[0,2,4,8,12,16,20,22,57,58,74,77,82,85,97,130,154,170,182,190,194,201],[129,153,193,202],[0,2,4,8,12,16,20,22,57,58,74,77,82,85,97,130,154,170,178,190,194,201],[0,2,4,8,12,16,20,57,58,74,77,82,85,97,138,145,153,154,194,202],[76,128],[112,236],[184,192],[0,4,6,8,12,14,16,18,20,57,58,98,106,113,114,130,142,146,153,154,170,178,202,205],[141,181],[145,185,201],[0,4,6,8,10,12,14,16,18,20,57,58,98,106,113,114,130,142,145,146,153,154,170,178,202],[141,177],[0,4,8,10,12,14,16,18,20,57,58,98,106,113,114,130,142,145,146,153,154,170,173,178,202],[0,2,4,6,8,10,12,14,16,18,20,57,58,98,106,113,114,130,142,145,146,153,154,170,178,181,202,205],[0,4,6,8,10,12,14,16,18,20,57,58,98,106,113,114,130,142,145,146,153,154,170,173,178,181,202,205],[22,189],[0,2,4,8,10,12,14,16,18,20,57,58,98,106,113,114,130,142,145,146,153,154,170,178,202,205],[102,110,118,157,197],[0,2,4,8,10,12,14,16,18,20,57,58,73,97,98,106,113,114,130,133,142,146,153,154,170,178,202],[17,19,131,139,151,155],[0,4,6,8,10,12,14,16,20,22,57,58,78,82,98,113,114,130,138,170,177,182,186,193,194,201],[74,145],[174,178,190,198,206],[0,2,4,6,8,12,14,16,18,20,22,57,58,97,105,113,145,170,177,178,190,193,194],[174,182,186,198,206],[0,2,4,8,10,12,14,16,18,20,57,58,82,98,106,113,114,130,142,146,149,153,154,170,178],[0,2,4,8,10,12,14,16,18,20,57,58,98,113,114,130,142,145,146,154,157,170,178],[0,2,4,8,10,12,14,16,18,20,57,58,82,98,113,114,130,141,142,146,149,154,157,170,178,201,206],[0,4,6,8,12,16,18,20,57,58,82,98,113,114,130,137,142,146,154,170,178,202,205],[153,201],[0,4,8,10,12,14,16,18,20,57,58,82,98,113,114,130,137,142,145,146,153,154,170,173,178,202],[0,2,4,6,8,10,12,14,16,18,20,57,58,82,98,113,114,130,137,142,145,146,153,154,170,178,181,202,205],[0,4,6,8,10,12,14,16,18,20,57,58,82,98,113,114,130,137,142,145,146,153,154,170,173,178,181,202,205],[74,189],[0,2,4,8,10,12,14,16,18,20,57,58,82,98,113,114,130,137,142,145,146,153,154,170,178,202,205],[0,2,4,8,10,12,14,16,18,20,57,58,73,82,97,98,113,114,130,133,137,142,146,153,154,170,178,202],[0,2,4,6,8,12,16,18,20,22,57,58,73,81,98,114,130,146,170,177,178,186,193,198],[62,137,141,181],[97,109,113,145,154],[0,2,4,8,10,12,14,16,18,20,57,58,98,113,114,130,142,146,149,153,154,170,178],[0,2,4,8,10,12,14,16,18,20,57,58,82,98,106,113,114,130,142,145,146,154,157,170,178],[0,2,4,8,10,12,14,16,18,20,57,58,98,106,113,114,130,142,146,149,154,157,170,178,201,206],[0,2,4,8,12,14,16,18,20,22,57,58,97,113,129,130,138,153,158,201,202,205],[0,2,4,8,12,16,18,20,22,57,58,73,98,114,129,130,138,150,153,170,186,193,201,202,205],[97,113,154,194],[17,19,131,139,155,159],[0,2,4,8,10,12,14,16,18,20,57,58,73,98,101,106,114,129,130,142,145,146,153,154,170,178,202],[0,2,4,8,10,12,14,16,18,20,57,58,73,82,98,101,114,129,130,137,142,145,146,153,154,170,178,202],[0,2,4,6,8,10,12,14,16,18,20,57,58,81,98,106,109,114,130,137,142,145,146,153,158,170,178,202],[0,2,4,8,10,12,14,16,18,20,57,58,98,106,114,117,130,142,145,146,153,154,170,178,193,198,202],[0,2,4,8,10,12,14,16,18,20,57,58,98,114,117,130,137,142,145,146,153,154,170,178,202],[22,193,198,201],[0,4,6,8,12,14,16,20,22,57,58,98,114,130,138,154,157,170,177,178,186,193,194,201,206],[109,141],[0,2,4,8,10,12,14,16,18,20,57,58,98,113,114,130,138,145,146,154,157,170,178,194],[0,2,4,8,10,12,14,16,18,20,57,58,98,113,114,130,138,141,146,149,154,157,170,178,194,201,206],[0,4,6,8,12,16,18,20,57,58,98,113,114,130,137,138,146,154,170,178,194,202,205],[0,2,4,8,10,12,14,16,18,20,57,58,98,113,114,130,137,138,145,146,153,154,170,178,194,202],[0,4,8,10,12,14,16,18,20,57,58,98,113,114,130,137,138,145,146,153,154,170,173,178,194,202],[0,2,4,6,8,10,12,14,16,18,20,57,58,98,113,114,130,137,138,145,146,153,154,170,178,181,194,202],[0,4,6,8,10,12,14,16,18,20,57,58,98,113,114,130,137,138,145,146,153,154,170,173,178,181,194,202],[0,2,4,8,10,12,14,16,18,20,57,58,98,113,114,130,137,138,145,146,153,154,170,178,194,197,202],[0,2,4,8,10,12,14,16,18,20,57,58,98,113,114,130,137,138,145,146,153,154,170,178,194,202,205],[0,2,4,8,10,12,14,16,18,20,57,58,73,97,98,113,114,130,133,137,138,146,153,154,170,178,194,202],[0,2,4,6,8,10,12,14,16,18,20,57,58,62,81,85,98,105,109,113,114,130,137,138,141,146,154,170,178,181,194,202],[0,2,4,8,10,12,14,16,18,20,57,58,98,113,114,130,138,146,149,153,154,170,178,194],[0,2,4,8,10,12,14,16,18,20,57,58,98,110,113,114,130,138,145,146,154,157,170,178,194,202],[0,2,4,8,10,12,14,16,18,20,57,58,98,110,113,114,130,138,146,149,154,157,170,178,194],[0,2,4,8,12,14,16,18,20,22,57,58,113,129,130,138,153,154,169,202,205],[0,2,4,8,12,16,18,20,22,57,58,73,98,114,129,130,138,150,153,170,178,186,193,201,202,205],[1,3,5,7,9,11,13,15,59,63,75,79,83,87,99,103,107,111,115,119,135,143,159],[0,2,4,8,10,12,14,16,18,20,57,58,73,98,101,114,129,130,137,138,145,146,153,154,170,178,194,202],[0,2,4,8,10,12,14,16,18,20,57,58,82,98,114,117,130,137,138,145,146,153,154,170,178,202],[0,2,4,8,10,12,14,16,18,20,57,58,82,98,105,106,113,114,130,145,146,154,157,170,178,194],[0,2,4,8,10,12,14,16,18,20,57,58,98,105,106,113,114,130,146,149,154,157,170,178,194],[22,193,201,206],[0,2,4,8,10,12,14,16,18,20,57,58,98,105,110,113,114,130,145,146,154,157,170,178,194,202],[0,2,4,8,10,12,14,16,18,20,57,58,82,98,105,110,113,114,130,146,149,154,157,170,178,194],[0,2,4,8,10,12,14,16,18,20,57,58,73,98,105,110,113,114,129,130,137,138,146,153,154,170,186,194,202,205],[22,169,193],[0,2,4,8,10,12,14,16,18,20,57,58,73,98,105,106,113,114,129,130,134,137,138,142,146,150,153,154,158,170,186,194,202,205],[17,19,131,139,155],[0,2,4,6,8,10,12,14,16,18,20,57,58,82,85,98,105,113,130,137,142,145,150,153,154,170,178,202],[132,172],[0,2,4,6,8,12,14,16,18,20,22,57,58,105,145,170,177,178,190,193,194,201,202],[85,137],[0,2,4,6,8,12,16,18,20,22,57,58,98,130,137,142,146,153,170,177,178,190,193,201,202],[0,2,4,8,10,12,14,16,18,20,57,58,114,117,130,142,145,146,153,154,170,178,202],[22,198,201],[0,2,4,8,10,12,14,16,18,20,57,58,106,114,117,130,137,142,145,146,153,154,170,178,198,202],[0,4,6,8,12,14,16,20,57,58,81,98,102,106,109,110,113,114,118,130,138,141,153,154,157,186,194,197,202],[0,2,4,8,10,12,14,16,18,20,57,58,74,82,106,113,114,145,146,154,157,170,178,194],[0,2,4,8,10,12,14,16,18,20,57,58,106,113,114,141,146,149,154,157,170,178,194],[22,206],[0,4,6,8,12,16,18,20,57,58,106,113,114,137,146,154,170,178,194,202,205],[153,193,201],[0,2,4,8,10,12,14,16,18,20,57,58,106,113,114,137,145,146,153,154,170,178,194,202],[0,4,8,10,12,14,16,18,20,57,58,106,113,114,137,145,146,153,154,170,173,178,194,197,202],[0,2,4,6,8,10,12,14,16,18,20,57,58,106,113,114,137,145,146,153,154,170,178,181,194,202],[0,4,6,8,10,12,14,16,18,20,57,58,106,113,114,137,145,146,153,154,170,173,178,181,194,197,202,205],[0,2,4,8,10,12,14,16,18,20,57,58,106,113,114,137,145,146,153,154,170,178,194,197,202],[0,2,4,8,10,12,14,16,18,20,57,58,106,113,114,137,145,146,153,154,170,178,194,202,205],[135],[0,2,4,6,8,12,16,20,22,57,58,62,73,81,85,105,106,109,113,114,146,154,170,174,177,178,181,182,186,190,194,198,206],[0,2,4,8,10,12,14,16,18,20,57,58,74,82,106,113,114,146,149,153,154,170,178,194],[0,2,4,8,10,12,14,16,18,20,57,58,98,110,113,114,145,146,154,157,170,178,194,202],[0,2,4,8,10,12,14,16,18,20,57,58,74,82,98,110,113,114,146,149,154,157,170,178,194],[0,2,4,6,8,10,12,14,16,18,20,57,58,81,106,109,114,137,145,146,153,170,178,194,202],[17,19,131,135,139,147],[0,2,4,6,8,12,16,20,22,57,58,73,81,106,109,114,146,154,170,174,177,178,182,186,190,194,198,206],[101,169],[0,2,4,8,10,12,14,16,18,20,57,58,74,106,114,117,137,145,146,153,154,170,178,202],[0,2,4,8,10,12,14,16,18,20,57,58,74,105,113,114,138,145,146,154,157,170,178,194],[0,2,4,8,10,12,14,16,18,20,57,58,105,113,114,138,146,149,154,157,170,178,194,206],[0,2,4,8,10,12,14,16,18,20,57,58,98,105,110,113,114,138,145,146,154,157,170,178,194,202],[0,2,4,8,10,12,14,16,18,20,57,58,74,98,105,110,113,114,138,146,149,154,157,170,178,194],[0,2,4,8,10,12,14,16,18,20,57,58,82,114,117,130,137,138,145,146,153,154,170,178,186,202],[0,2,4,8,10,12,14,16,18,20,57,58,74,114,117,137,145,146,153,154,170,178,186,202],[0,2,4,8,10,12,14,16,18,20,57,58,74,105,113,114,145,146,154,157,170,178,186,194],[0,2,4,8,10,12,14,16,18,20,57,58,82,98,105,106,113,114,145,146,154,157,170,178,186,194],[0,2,4,8,10,12,14,16,18,20,57,58,82,105,113,114,146,149,154,157,170,178,186,194],[0,2,4,8,10,12,14,16,18,20,57,58,74,98,105,106,113,114,146,149,154,157,170,178,186,194],[0,4,6,8,12,16,18,20,22,58,61,73,74,81,82,105,114,137,153,181,182,186,193],[0,4,6,8,12,16,20,22,58,61,73,74,81,82,105,130,154,170,177,182,186,194,201],[0,4,6,8,12,16,20,22,58,61,73,74,81,82,105,130,154,170,177,178,190,194,201],[0,4,6,8,12,16,20,58,61,73,74,81,82,105,129,141,145,146,153,154,177,186,194,202],[0,4,8,10,12,14,16,18,20,58,61,98,106,113,114,129,130,142,145,146,153,154,170,178,202],[0,4,8,10,12,14,16,18,20,58,61,98,113,114,130,137,142,145,146,153,154,170,178,202],[0,4,8,10,12,14,16,18,20,58,61,97,98,113,114,130,137,138,145,146,153,154,170,178,194,202],[0,4,8,10,12,14,16,18,20,58,61,97,113,114,137,145,146,153,154,170,178,194,202],[0,4,6,8,10,12,16,18,20,22,57,58,73,74,82,85,106,114,130,137,138,146,153,170,177,178,185,186,201,206],[105,129,169,194],[0,4,6,8,12,16,20,22,57,58,73,74,82,85,105,106,130,138,154,170,177,178,186,194,201,206],[0,4,8,10,12,16,18,20,22,57,58,73,74,82,85,106,145,153,178,189,193],[170,190],[0,4,8,10,12,16,20,22,57,58,73,74,82,85,113,130,145,154,170,178,185,190,194,201],[0,4,8,10,12,16,20,22,57,58,73,74,82,85,113,130,154,170,182,185,190,194,201],[0,4,8,10,12,16,20,57,58,73,74,82,85,113,138,146,149,153,154,178,194,202],[185,201],[0,4,8,10,12,16,18,20,22,57,58,74,77,82,85,106,113,145,150,153,178,189,190,193],[0,4,8,10,12,16,20,22,57,58,74,77,82,85,113,130,145,154,170,178,185,190,194,201],[0,4,8,10,12,16,20,22,57,58,74,77,82,85,113,130,154,170,182,185,190,194,201],[0,4,8,10,12,16,20,57,58,74,77,82,85,113,129,138,149,153,154,178,185,194,202],[0,4,8,10,12,14,16,18,20,22,58,114,117,130,145,146,154,170,177,185,186,198],[57,82,142,178],[98,197],[152],[0,4,8,10,12,14,16,20,22,57,58,74,82,98,106,114,117,130,146,170,178,185,186,193,198,201],[145,177,202],[0,4,8,10,12,14,16,20,22,57,58,74,82,98,106,114,117,130,146,170,182,185,186,193,194,201],[137,145,177,202],[0,4,8,12,14,16,18,20,22,57,58,82,98,106,113,130,138,154,157,178,185,193,194,205],[102,110,118,153,197],[170,206],[0,4,8,12,14,16,18,20,22,57,58,82,98,106,113,130,145,154,157,170,178,185,193,194,201,206],[0,4,8,12,14,16,18,20,22,57,58,82,113,130,138,145,153,154,178,185,202,205],[137,146,186],[0,4,8,10,12,16,18,20,22,57,58,98,114,130,138,145,146,153,170,178,186,193,201,202],[137,154,177,194],[0,4,8,10,12,14,16,18,20,22,58,74,137,177,193],[57,82,138],[102,106,118,157,197],[130,205],[170,186,206],[128,204],[0,4,8,12,14,16,18,20,22,57,58,82,113,138,145,170,178,193,194,201,206],[0,4,8,12,14,16,18,20,22,57,58,82,113,138,145,170,173,178,194,206],[98,193],[0,4,8,10,12,14,16,18,20,22,58,74,98,113,114,130,145,146,186,189,193,194,201],[57,82,110,129,138],[0,4,8,12,14,16,18,20,22,57,58,82,98,110,113,138,145,153,154,170,178,193,194,197,201,206],[102,106,118,157],[114,186],[0,4,8,10,12,14,16,18,20,22,58,177,193,194,201],[57,82,129,138],[102,118,153,157,197],[134,150,154,158,205],[186,206],[0,4,8,12,14,16,18,20,22,57,58,82,113,138,145,170,178,181,194,201,206],[110,114,197],[0,4,8,12,14,16,18,20,22,57,58,82,113,138,145,170,173,178,181,194,206],[0,2,4,8,12,14,16,18,20,22,57,58,82,97,113,129,130,133,138,169,170,178,193,194,201,206],[61,173],[76],[204,252],[240],[0,4,6,8,12,14,16,18,20,22,57,58,82,105,113,138,141,145,170,177,178,193,194,201,206],[110,114,157],[0,4,8,12,14,16,18,20,22,57,58,82,98,110,113,130,138,146,149,170,178,193,194,201,206],[0,4,8,12,16,18,20,22,57,58,82,98,114,130,138,146,154,157,170,178,186,193,201,206],[113,145,194],[0,4,8,12,16,18,20,22,57,58,98,114,130,138,141,146,149,154,157,170,178,186,193,201,206],[113,194],[0,4,8,12,16,18,20,22,57,58,98,114,130,138,146,153,170,178,186,202,205],[113,145,154,185,194],[0,4,8,12,16,18,20,22,57,58,98,114,130,138,146,153,170,178,186,193,201,202],[0,4,8,12,16,18,20,22,57,58,98,114,130,138,146,153,170,173,178,186,193,201,202],[0,4,8,10,12,16,18,20,22,57,58,74,82,98,114,130,138,145,146,153,170,178,186,189,193,201,202],[113,137,154,194],[0,4,8,12,14,16,18,20,22,57,58,82,98,113,130,138,145,153,154,170,178,194,197,201,202],[110,193],[114,137,186],[0,4,8,12,16,18,20,22,57,58,98,114,130,138,146,153,170,178,181,186,201,202],[0,4,8,12,16,18,20,22,57,58,98,114,130,138,146,153,170,173,178,181,186,201,202],[0,2,4,8,12,16,18,20,22,57,58,73,98,114,130,133,138,146,153,169,170,178,186,193,201,202],[0,4,6,8,12,16,18,20,22,57,58,81,98,114,130,138,141,146,170,177,178,186,193,201,202],[62,181],[109,113,145,154,194],[0,4,8,12,16,18,20,22,57,58,82,98,114,130,138,146,149,153,170,178,186,193,201,202],[0,4,8,12,14,16,18,20,22,57,58,82,98,110,113,130,138,145,154,157,170,178,193,194,201,202],[0,4,8,12,14,16,18,20,22,57,58,82,113,133,138,146,149,154,157,170,178,193,194,201,202],[0,4,8,12,14,16,18,20,22,57,58,82,113,130,138,153,154,178,202,205],[0,2,4,8,12,14,16,18,20,22,57,58,82,98,101,129,130,138,145,169,170,178,193,194,201,206],[0,2,4,8,12,16,18,20,22,57,58,98,101,114,130,138,146,153,169,170,178,186,193,201,202],[1,3,5,7,13,15,17,19,59,63,87,99,103,107,111,131,135,139,143,151,155,159],[9,11,75,79,115,147],[0,4,8,10,12,14,16,18,20,22,58,74,137,174,177,193,194,201,202],[57,82,138,178],[0,2,4,6,8,12,14,16,18,20,22,57,58,82,109,129,137,138,145,170,174,178,182,190,193,194,198,201,202,206],[0,4,8,12,14,16,18,20,22,57,58,98,110,114,117,130,138,145,170,178,193,194,201,206],[146,177,186],[0,4,8,12,16,18,20,22,57,58,98,114,117,130,138,146,153,170,178,186,193,201,202],[0,4,8,12,14,16,20,22,57,58,97,98,106,114,130,146,154,157,170,182,186,193,194,201],[113,145,185,202],[0,4,8,12,16,18,20,22,57,58,82,98,114,130,142,146,154,157,170,178,186,193,198,201,206],[0,4,8,12,16,18,20,22,57,58,98,114,130,141,142,146,149,154,157,170,178,186,193,198,201,206],[0,4,8,12,16,18,20,22,57,58,98,114,130,142,146,153,170,178,186,201,202,205],[0,4,8,12,16,18,20,22,57,58,98,114,130,142,146,153,170,178,186,193,198,201,202],[0,4,8,12,16,18,20,22,57,58,98,114,130,142,146,153,170,173,178,186,193,198,201,202],[0,4,8,10,12,16,18,20,22,57,58,74,82,98,114,130,142,145,146,153,170,178,186,189,193,198,201,202],[113,137,154],[0,4,8,10,12,14,16,18,20,22,58,137,153,154,201,202],[57,97],[0,4,8,12,16,18,20,22,57,58,98,114,130,134,138,142,146,150,153,158,170,178,186,193,198,201,202,205],[0,4,8,12,16,18,20,22,57,58,98,114,130,142,146,153,170,178,181,186,202,205],[0,4,8,12,16,18,20,22,57,58,98,114,130,142,146,153,170,173,178,181,186,202,205],[0,2,4,8,12,16,18,20,22,57,58,73,98,114,130,133,142,146,153,169,170,178,186,193,198,201,202],[0,2,4,6,8,12,16,18,20,22,57,58,98,114,130,142,146,170,178,186,193,198,201,202],[62,109,141,177,181],[0,4,8,12,16,18,20,22,57,58,82,98,114,130,142,146,149,153,170,178,186,193,198,201,202],[0,4,8,12,14,16,18,20,22,57,58,98,106,113,130,142,145,154,157,170,178,193,198,201,206],[0,4,8,12,14,16,18,20,22,57,58,82,106,113,146,149,154,157,170,178,193,198,201,206],[0,4,8,12,14,16,18,20,22,57,58,82,106,113,130,138,153,158,201,202,205],[0,4,8,12,16,18,20,22,57,58,98,114,130,134,138,142,146,150,153,158,170,182,186,193,201,202,205],[17,19,131,139,143,155,159],[0,2,4,8,12,16,18,20,22,57,58,98,101,114,130,142,146,153,169,170,178,186,193,198,201,202],[61,133,173],[0,4,8,12,16,18,20,22,57,58,98,114,117,130,142,146,153,170,178,186,193,198,201,202],[0,4,8,12,14,16,20,22,57,58,98,105,110,113,114,130,146,154,157,170,178,186,193,194,201],[145,202],[0,4,8,12,14,16,20,22,57,58,98,105,110,113,114,130,146,149,154,157,170,178,186,193,194,201],[0,4,8,12,14,16,20,22,57,58,98,105,106,113,114,130,146,154,157,170,178,186,193,194,201,206],[0,4,8,12,14,16,20,22,57,58,98,105,106,113,114,130,146,149,154,157,170,178,186,193,194,201,206],[0,4,6,8,10,12,14,16,18,20,57,58,98,105,106,113,114,129,130,134,138,142,146,150,153,154,158,170,186,194,202,205],[0,4,6,8,10,12,14,16,18,20,57,58,98,105,110,113,114,129,130,138,146,153,154,170,186,194,202,205],[0,4,8,10,12,14,16,18,20,22,58,137,177,193,194,201,202],[74,149,185],[178,190],[13,15,99,107,111,119,155],[0,2,4,6,8,12,16,18,20,22,57,58,77,85,98,129,130,137,138,150,153,170,174,178,182,186,190,193,198,201,202,206],[105,113,145,154,194],[0,4,6,8,12,14,16,18,20,22,57,58,82,85,105,113,137,138,145,170,177,178,193,194,201,206],[0,4,6,8,12,16,18,20,22,57,58,82,85,98,130,137,138,146,153,170,177,178,186,193,201,202],[0,4,8,10,12,14,16,20,57,58,74,82,98,106,114,117,137,138,145,146,154,157,178,186,202],[0,4,8,12,16,18,20,22,57,58,106,114,117,138,146,153,170,178,186,201,206],[0,4,8,12,16,18,20,22,57,58,106,114,117,130,138,146,153,170,178,186,201,202],[0,4,8,12,14,16,18,20,57,58,97,98,105,106,113,114,129,134,138,145,146,154,157,178,186,194,202],[0,4,8,10,12,16,20,22,57,58,97,106,113,138,146,154,157,170,178,185,186,198,206],[0,4,8,12,16,20,22,57,58,97,106,113,114,138,141,146,149,154,157,170,178,186,198,206],[0,4,8,12,16,18,20,22,57,58,106,114,130,138,146,153,178,186,193,202,205],[170,198],[0,4,8,12,16,20,22,57,58,97,106,113,114,138,146,154,170,178,186,198],[0,4,8,12,16,20,22,57,58,106,113,114,138,146,154,170,173,178,186,197,198],[0,4,8,10,12,14,16,18,20,22,58,74,98,130,137,145,146,153,154],[57,82,97],[106,197],[205],[0,4,8,10,12,16,20,22,57,58,97,106,113,114,138,146,154,170,178,186,189,198],[145,153,202],[0,4,8,12,16,18,20,22,57,58,106,114,138,146,153,178,186,202,205],[0,4,8,12,16,20,22,57,58,97,105,106,113,114,138,146,154,170,178,181,186,198],[0,4,8,12,16,20,22,57,58,105,106,113,114,138,146,154,170,173,178,181,186,197,198],[0,4,6,8,12,16,20,22,57,58,62,81,85,97,105,106,109,113,114,138,141,146,154,170,177,178,181,186,198],[0,4,8,10,12,16,20,22,57,58,97,106,113,114,138,146,149,154,170,178,185,186,198],[0,4,8,12,14,16,20,22,57,58,97,106,113,114,138,146,154,157,170,178,186,193,198,206],[0,4,8,10,12,14,16,20,22,57,58,97,106,113,114,138,146,149,154,157,170,178,185,186,193,198,206],[0,2,4,6,8,12,16,20,22,57,58,73,81,106,114,138,146,170,178,186,198],[61,101,133,169,173],[0,4,6,8,12,16,20,22,57,58,81,97,106,109,114,138,146,154,170,177,178,186,198],[0,4,8,12,16,20,22,57,58,74,106,114,117,138,146,154,170,178,186,198],[0,4,8,12,14,16,20,22,57,58,105,106,138,146,154,157,170,178,186,194],[0,4,8,12,14,16,20,22,57,58,105,106,113,114,138,146,149,154,157,170,178,186,194],[18,133,202],[0,4,8,12,14,16,20,22,57,58,98,105,106,113,114,138,146,154,157,170,178,186,193,194],[145,206],[0,4,8,10,12,14,16,20,22,57,58,98,105,106,113,114,138,146,149,154,157,170,178,186,193,194],[18,185,206],[0,4,8,12,16,18,20,22,57,58,73,82,114,117,130,142,146,153,170,178,190,198,201,202],[0,4,8,12,16,20,22,57,58,73,74,114,117,138,146,154,170,178,190,198],[0,4,8,12,14,16,20,22,57,58,73,74,105,106,146,154,157,170,178,190,194],[0,4,8,12,14,16,20,22,57,58,73,82,98,105,110,114,146,154,157,170,178,190,193,194],[113,145,202],[0,4,8,10,12,14,16,20,22,57,58,73,82,105,106,113,114,146,149,154,157,170,178,190,194,206],[0,4,8,10,12,14,16,20,22,57,58,73,74,98,105,110,113,114,146,149,154,157,170,178,190,193,194,206],[18,185],[0,2,4,8,12,14,16,18,20,22,58,61,97,113,145,169,170,178,193,194,201,206],[0,2,4,8,12,16,18,20,22,58,61,73,98,114,130,138,146,153,169,170,178,186,193,201,202],[0,2,4,8,12,16,18,20,22,58,61,73,98,114,130,142,146,153,169,170,178,186,193,198,201,202],[0,2,4,8,12,16,20,22,58,61,73,113,114,146,154,169,170,178,186,198],[0,2,4,6,8,10,12,14,16,18,20,58,74,78,81,82,86,98,105,106,113,114,117,130,141,145,149,157,170,194,202],[22,185,189,193,201],[0,4,6,8,10,12,14,16,20,22,74,81,82,98,102,105,106,110,113,114,118,130,157,170,177,178,185,186,193,197,198,201],[85,109,137,141,181],[153,169],[0,2,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,138,145,146,153,158,170,197,202,205],[0,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,138,145,146,153,158,170,173,197,202,205],[0,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,145,153,154,170,202,205],[0,2,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,145,153,154,170,173,202,205],[0,2,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,130,137,154,157,170,194,202],[0,4,8,12,14,16,20,22,74,81,82,98,102,106,110,114,118,130,154,157,170,178,186,193,194,197,201],[0,2,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,138,146,153,154,170,194,197,202,205],[0,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,138,146,153,154,170,173,194,197,202,205],[0,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,145,153,154,170,194,202,205],[0,2,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,145,153,154,170,173,194,202,205],[0,2,4,6,8,10,12,14,16,18,20,74,81,82,98,102,105,106,110,113,114,118,130,153,154,157,170,186,194,197,202],[0,4,8,12,14,16,20,22,74,81,82,98,106,114,130,154,157,170,178,190,193,194,201],[0,2,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,138,150,153,154,170,194,202,205],[0,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,138,150,153,154,170,173,194,202,205],[0,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,145,146,153,154,170,194,197,202,205],[0,2,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,113,114,129,130,145,146,153,154,170,173,194,197,202,205],[0,2,4,6,8,10,12,14,16,18,20,81,82,98,105,106,113,114,130,145,154,157,170,186,194,202],[0,4,8,12,14,16,20,22,81,82,106,114,130,154,157,170,178,190,193,194,201],[110,118,197],[113,145,153],[0,2,4,6,8,10,12,14,16,18,20,81,82,105,106,113,114,129,130,138,150,154,170,194,202,205],[0,4,6,8,10,12,14,16,18,20,81,82,105,106,113,114,129,130,138,150,154,170,173,189,194,197,202,205],[0,4,6,8,10,12,14,16,18,20,81,82,105,106,113,114,129,130,146,154,170,194,202,205],[0,2,4,6,8,10,12,14,16,18,20,81,82,105,106,113,114,129,130,146,154,170,173,189,194,202,205],[103],[0,2,4,8,10,12,14,16,18,20,58,61,73,74,81,82,97,98,113,114,129,130,138,145,150,153,154,170,178,186],[0,2,4,8,10,12,14,16,18,20,58,61,73,74,81,82,97,98,106,113,114,129,130,145,153,154,170,178,186],[0,4,8,12,16,18,20,22,58,61,73,74,81,82,114,153,182,186,193],[0,4,8,12,16,20,22,58,61,73,74,81,82,154,174,182,186,194,201],[0,4,8,12,16,20,22,58,61,73,74,81,82,154,170,178,190,194,201],[0,4,8,12,16,20,58,61,73,74,81,82,129,130,145,146,153,154,186,194,202],[0,4,6,8,10,12,14,16,18,20,58,61,98,106,113,114,129,134,142,145,146,153,154,170,178,202],[0,4,6,8,10,12,14,16,18,20,58,61,74,113,114,134,142,145,146,153,154,170,178,202],[0,4,6,8,10,12,14,16,18,20,58,61,97,113,114,130,138,145,146,153,154,170,178,194,202],[0,4,6,8,10,12,14,16,18,20,58,61,97,98,113,114,145,146,153,154,170,178,194,202],[0,4,6,8,10,12,14,16,18,20,57,58,73,74,82,85,105,106,113,114,129,134,137,138,146,153,154,170,178,186],[22,177,185,201],[0,4,6,8,10,12,14,16,18,20,57,58,73,74,82,85,105,106,113,129,137,138,149,153,154,170,178,186],[0,2,4,6,8,12,16,18,20,22,57,58,73,74,82,85,106,129,137,153,173,178,193],[174,186],[0,2,4,6,8,12,16,20,22,57,58,73,74,82,85,97,105,154,169,174,178,186,194,201],[0,2,4,6,8,12,16,20,22,57,58,73,74,82,85,97,105,154,169,170,182,190,194,201],[133,153,193,202],[0,2,4,6,8,12,16,20,57,58,73,74,82,85,97,105,130,133,138,153,154,178,194,202],[169,201],[0,4,6,8,12,16,18,20,22,57,58,74,77,82,85,106,137,150,153,178,190,193],[0,4,6,8,12,16,20,22,57,58,74,77,82,85,105,154,174,178,190,194,201],[0,4,6,8,12,16,20,22,57,58,74,77,82,85,105,154,170,182,190,194,201],[0,4,6,8,12,16,20,57,58,74,77,82,85,105,129,130,138,153,154,178,194,202],[116,152],[0,4,6,8,10,12,14,16,18,20,57,58,81,82,98,105,110,113,114,129,134,138,145,146,153,154,170,178],[0,2,4,6,8,10,12,14,16,18,20,57,58,81,82,98,105,110,113,114,134,138,145,146,153,154,170,173,178,205],[0,4,6,8,10,12,14,16,18,20,57,58,82,98,110,113,114,129,134,137,138,145,146,153,154,170,178,181],[0,2,4,6,8,10,12,14,16,18,20,57,58,82,98,110,113,114,134,137,138,145,146,153,154,170,173,178,181,205],[172],[0,2,4,6,8,12,14,16,18,20,22,57,58,82,97,105,113,138,169,170,178,193,194],[61,129,133,173],[0,4,6,8,10,12,14,16,18,20,57,58,81,82,98,105,110,113,114,129,134,138,141,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,82,98,105,110,113,114,134,138,146,149,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,82,105,113,114,134,138,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,82,105,113,114,134,138,146,149,154,157,170,178,201],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,82,105,113,114,134,138,145,146,153,154,170,178],[0,2,4,6,8,10,12,14,16,18,20,57,58,74,81,82,105,113,114,129,134,138,145,146,153,154,170,173,178,205],[0,4,6,8,10,12,14,16,18,20,57,58,74,82,113,114,134,137,138,145,146,153,154,170,178,181],[0,2,4,6,8,10,12,14,16,18,20,57,58,74,82,113,114,129,134,137,138,145,146,153,154,170,173,178,181,205],[0,2,4,6,8,12,16,18,20,22,57,58,73,114,138,153,169,170,178,186,193],[105,113,154],[194,206],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,82,105,113,114,134,138,141,145,146,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,82,105,113,114,134,138,146,149,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,82,98,105,110,113,114,134,138,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,82,98,105,110,113,114,133,134,138,146,149,154,157,170,178,201],[0,4,6,8,12,14,16,18,20,22,57,58,82,105,113,130,137,138,153,178,202,205],[81,129,146,169],[0,4,6,8,12,16,18,20,22,57,58,81,114,130,137,138,153,178,193,202,205],[105,113,154,194],[140,180],[0,2,4,6,8,12,14,16,18,20,22,57,58,82,85,105,129,134,137,138,145,169,170,178,201,202],[110,114,193],[0,2,4,6,8,12,16,18,20,22,57,58,134,138,146,153,169,170,178,186,193,201],[105,145,154],[0,2,4,6,8,10,12,14,16,18,20,57,58,73,81,82,98,101,105,110,114,129,134,138,145,146,153,158,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,98,105,110,114,117,129,134,138,145,146,153,154,170,178,193],[0,4,6,8,10,12,14,16,18,20,57,58,81,105,114,117,134,138,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,82,97,113,114,130,142,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,97,113,114,130,142,146,149,154,157,170,178,201],[0,4,6,8,10,12,14,16,18,20,57,58,81,97,113,114,130,142,145,146,153,154,170,178],[0,2,4,6,8,10,12,14,16,18,20,57,58,81,113,114,129,130,142,145,146,153,154,170,173,178],[0,4,6,8,10,12,14,16,18,20,57,58,97,105,113,114,130,137,142,145,146,153,154,170,178,181,205],[0,2,4,6,8,10,12,14,16,18,20,57,58,105,113,114,129,130,137,142,145,146,153,154,170,173,178,181,197,205],[0,2,4,6,8,12,16,18,20,22,57,58,73,114,130,153,169,170,178,186,193],[0,2,4,6,8,10,12,14,16,18,20,57,58,73,81,97,113,114,130,133,142,146,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,82,97,113,114,130,142,146,149,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,97,102,106,113,114,130,141,142,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,82,97,102,106,113,114,130,141,142,146,149,154,157,170,178],[0,4,6,8,12,14,16,18,20,22,57,58,82,106,113,130,137,138,153,177,202,205],[81,97,129,146],[0,4,6,8,12,16,18,20,22,57,58,81,114,130,137,138,153,170,193,202,205],[0,2,4,6,8,12,16,18,20,22,57,58,130,142,146,153,169,170,178,186,193,201],[61,97,101,133,173],[81,109],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,82,114,117,130,142,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,82,98,110,113,114,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,98,110,113,114,133,146,149,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,102,106,113,114,141,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,82,102,106,113,114,141,146,149,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,102,106,113,114,129,130,137,138,146,153,186,194,202,205],[22,177,193],[0,4,6,8,10,12,14,16,18,20,57,58,81,98,110,113,114,129,130,137,138,146,153,186,194,202,205],[0,2,4,6,8,10,12,14,16,18,20,57,58,74,77,81,82,97,105,113,129,134,138,145,150,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,62,81,82,85,98,105,109,110,113,118,129,134,137,138,141,145,146,153,154,170,178,181],[0,4,6,8,10,12,14,16,18,20,57,58,62,74,81,82,85,105,109,113,134,137,138,141,145,146,153,154,170,178,181],[0,4,6,8,10,12,14,16,18,20,57,58,81,105,106,114,117,129,134,138,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,98,105,106,114,117,134,138,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,86,97,98,106,113,114,138,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,97,98,106,113,114,138,146,149,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,97,98,106,113,114,138,145,146,153,154,170,178],[0,2,4,6,8,10,12,14,16,18,20,57,58,81,98,106,113,114,129,138,145,146,153,154,170,173,178],[0,4,6,8,10,12,14,16,18,20,57,58,97,98,105,106,113,114,137,138,145,146,153,154,170,178,181],[0,2,4,6,8,10,12,14,16,18,20,57,58,98,105,106,113,114,129,137,138,145,146,153,154,170,173,178,181],[0,4,6,8,10,12,14,16,18,20,57,58,81,97,98,105,106,113,114,138,141,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,86,97,98,106,113,114,138,146,149,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,97,102,106,113,114,138,141,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,74,81,86,97,102,106,113,114,138,141,146,149,154,157,170,178],[0,2,4,6,8,10,12,14,16,18,20,57,58,61,73,77,81,97,98,101,106,114,129,133,138,145,146,153,170,173,178],[22,169],[0,4,6,8,10,12,14,16,18,20,57,58,81,97,98,106,109,114,137,138,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,98,106,114,117,138,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,106,113,114,130,138,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,106,113,114,130,133,138,146,149,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,102,106,113,114,130,138,141,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,81,102,106,113,114,130,138,141,146,149,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,73,74,82,114,117,130,142,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,73,114,117,138,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,73,106,113,114,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,73,74,82,98,110,113,114,145,146,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,73,74,82,106,113,114,141,146,149,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,57,58,73,98,110,113,114,141,146,149,154,157,170,178],[0,4,6,8,10,12,14,16,18,20,58,61,81,98,105,110,113,114,134,142,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,58,61,74,81,82,105,110,113,114,129,134,142,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,58,61,81,110,113,114,129,130,142,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,58,61,81,98,106,113,114,129,145,146,153,154,170,178],[0,4,6,8,10,12,14,16,18,20,58,74,82,85,98,105,106,114,134,137,138,146,153,154,170,202],[169,177,193,201],[0,4,6,8,10,12,14,16,18,20,58,74,82,85,105,106,114,129,134,137,138,146,153,154,170,202],[0,4,6,8,10,12,14,16,18,20,58,74,82,85,105,106,114,129,130,137,138,146,153,154,170,194,202],[0,4,6,8,10,12,14,16,18,20,58,62,74,81,82,85,98,105,106,109,113,118,129,134,137,138,141,146,153,154,170],[169,193,201],[0,4,6,8,10,12,14,16,18,20,58,62,74,81,82,85,105,106,109,113,134,137,138,141,146,153,154,170],[0,4,6,8,10,12,14,16,18,20,58,74,82,85,97,105,106,130,137,138,150,153,154,170],[0,4,6,8,10,12,14,16,18,20,74,78,81,82,86,98,113,114,117,134,137,138,145,146,149,154,170,202],[0,4,6,8,10,12,14,16,18,20,58,74,78,81,82,86,98,113,114,117,129,134,137,138,145,146,149,154,170,202],[0,4,6,8,10,12,14,16,18,20,74,81,82,98,105,106,114,117,129,134,137,138,145,146,154,170],[0,4,6,8,10,12,14,16,18,20,58,74,81,82,98,105,106,114,117,134,137,138,145,146,154,170],[0,4,6,8,10,12,14,16,20,22,74,81,82,102,105,106,113,114,130,170,178,185,186,193,202,205],[0,4,6,8,10,12,14,16,20,22,74,81,82,97,102,105,106,113,114,130,170,173,178,181,185,186,197,202,205],[0,4,6,8,10,12,14,16,20,22,74,81,82,97,102,105,106,113,114,130,154,170,189,193,202,205],[0,4,6,8,10,12,14,16,20,22,74,81,82,102,105,106,113,114,130,154,170,173,189,197,202,205],[0,4,6,8,10,12,14,16,20,22,58,81,82,97,102,105,106,113,114,130,170,178,181,186,193,202,205],[0,4,6,8,10,12,14,16,20,22,58,81,82,102,105,106,113,114,130,170,173,178,181,186,197,202,205],[0,4,6,8,10,12,14,16,20,22,58,81,82,102,105,106,113,114,130,154,170,193,202,205],[0,4,6,8,10,12,14,16,20,22,58,81,82,97,102,105,106,113,114,130,154,170,173,189,197,202,205],[0,4,6,8,10,12,14,16,18,20,58,74,85,98,102,105,106,110,114,118,129,130,134,137,138,142,146,150,153,154,157,158,170,194,197,202,205],[82,185],[17,19,131,143,147,151,155],[17,19,131,139,143,151,155],[0,4,6,8,10,12,14,16,18,20,58,74,82,85,97,98,105,106,118,130,137,138,150,153,154,170],[169,177],[0,4,6,8,10,12,14,16,20,22,81,82,97,98,105,106,113,114,130,170,178,193,202,205],[0,4,6,8,10,12,14,16,20,22,73,81,82,98,105,106,113,114,130,170,173,178,193,202,205],[0,4,6,8,10,12,14,16,20,22,73,81,82,98,105,106,113,114,130,146,154,170,197,202,205],[0,4,6,8,10,12,14,16,20,22,81,82,97,98,105,106,113,114,130,146,154,170,173,189,197,202,205],[0,4,6,8,10,12,14,16,18,20,58,74,86,98,110,113,114,129,130,142,145,146,153,154,170,194,202],[81,177],[169,185,193,201],[0,4,6,8,10,12,14,16,18,20,58,74,81,86,97,98,102,106,110,113,114,118,130,134,138,142,145,146,150,153,154,157,158,170,197,205],[17,19,131,143,147,155],[0,4,6,8,10,12,14,16,18,20,58,74,82,85,98,105,106,129,137,138,153,154,170,194,202],[0,4,6,8,10,12,14,16,18,20,58,74,82,85,97,98,105,106,114,137,138,146,153,154,170],[0,4,6,8,10,12,14,16,20,22,74,81,82,97,105,106,113,114,130,170,178,189,202,205],[0,4,6,8,10,12,14,16,20,22,73,74,81,82,105,106,113,114,130,170,173,178,189,197,202,205],[0,4,6,8,10,12,14,16,20,22,73,74,81,82,105,106,113,114,130,146,154,170,202,205],[0,4,6,8,10,12,14,16,20,22,74,81,82,97,105,106,113,114,130,146,154,170,173,202,205],[0,2,4,8,12,14,16,18,20,22,58,61,74,97,113,130,145,169,170,178,193,194,201,206],[73,137,177,186],[0,2,4,8,12,16,18,20,22,58,61,73,114,130,138,146,153,169,170,178,186,193,201,202],[0,2,4,8,12,16,18,20,22,58,61,73,114,134,142,146,153,169,170,178,186,193,198,201,202],[0,2,4,8,12,16,20,22,58,61,73,98,105,113,114,130,146,154,169,170,178,186,198],[0,4,8,10,12,14,16,18,20,58,61,74,102,110,113,114,130,137,142,145,146,153,154,170,178],[0,4,8,10,12,14,16,18,20,58,61,74,82,110,113,114,129,130,142,145,146,153,154,170,178],[0,4,8,10,12,14,16,18,20,58,61,105,110,113,114,129,134,142,145,146,153,154,170,178],[0,4,8,10,12,14,16,18,20,58,61,98,105,106,113,114,129,130,145,146,153,154,170,178],[0,4,8,10,12,14,16,20,22,58,78,81,82,98,102,106,110,113,114,118,130,154,157,170,178,185,186,193,197,198,201,206],[0,2,4,6,8,10,12,14,16,18,20,57,58,73,78,81,82,98,105,106,113,114,130,145,154,157,170],[0,4,6,8,10,12,14,16,18,20,58,78,81,82,98,105,106,113,114,145,153,170,194,202,205],[22,130,185,193],[0,2,4,6,8,10,12,14,16,18,20,57,58,73,78,81,82,98,105,106,113,114,129,130,138,145,146,153,158,170,194,197,202,205],[0,2,4,6,8,10,12,14,16,18,20,57,58,73,78,81,82,98,105,106,113,114,129,130,145,153,170,173,194,202,205],[0,2,4,6,8,10,12,14,16,18,20,58,78,81,82,98,105,106,113,114,129,130,138,145,146,153,158,170,173,194,197,202,205],[0,4,6,8,10,12,16,18,20,22,58,74,78,81,82,86,98,130,134,138,142,145,146,149,150,158,170,177,178,185,186,189,193,198,201,202,205],[129,154,169],[13,15,99,115,155],[107,111],[0,2,4,6,8,10,12,14,16,18,20,57,58,62,73,74,81,82,85,98,105,109,117,130,137,138,141,145,146,158,170],[0,4,6,8,10,12,14,16,18,20,58,81,82,97,98,105,106,113,114,153,170,202,205],[22,130,181,193],[0,2,4,6,8,10,12,14,16,18,20,57,58,73,81,82,98,105,106,113,114,129,130,138,146,153,154,170,197,202,205],[0,2,4,6,8,10,12,14,16,18,20,57,58,73,81,82,98,105,106,113,114,129,130,145,153,170,173,202,205],[22,181,193],[0,2,4,6,8,10,12,14,16,18,20,58,81,82,97,98,105,106,113,114,129,130,138,145,146,153,154,170,173,197,202,205],[0,4,8,10,12,16,18,20,22,74,78,82,86,98,114,117,134,138,145,146,149,170,178,185,189,190,193,198,201,202],[81,113,137,154],[0,2,4,6,8,10,12,14,16,18,20,57,74,81,82,98,114,117,134,137,138,145,146,154,170],[0,4,6,8,10,12,14,16,18,20,81,82,97,102,105,106,113,114,153,170,186,202,205],[22,130,193],[0,2,4,6,8,10,12,14,16,18,20,57,81,82,102,105,106,113,114,129,130,138,150,153,154,170,186,202,205],[0,2,4,6,8,10,12,14,16,18,20,57,81,82,102,105,106,113,114,129,130,145,153,170,173,186,197,202,205],[0,2,4,6,8,10,12,14,16,18,20,81,82,97,102,105,106,113,114,129,130,138,145,150,153,154,170,173,186,189,197,202,205],[1,3,5,7,13,15,17,19,59,63,79,99,103,107,111,119,131,135,139,143,151,155,159],[9,11,75,115,147],[87],[0,4,8,10,12,16,20,22,74,81,82,98,114,117,130,138,146,170,178,185,190,198],[145,193,202],[0,2,4,6,8,10,12,14,16,18,20,57,74,78,81,82,86,98,113,114,117,130,137,138,145,146,149,170,189],[0,4,6,8,10,12,14,16,18,20,74,81,82,97,98,105,106,113,114,170,186,189,202,205],[22,130],[0,2,4,6,8,10,12,14,16,18,20,57,74,81,82,98,105,106,113,114,129,130,138,150,154,170,186,202,205],[0,2,4,6,8,10,12,14,16,18,20,57,74,81,82,98,105,106,113,114,129,130,170,173,186,189,202,205],[0,2,4,6,8,10,12,14,16,18,20,74,81,82,97,98,105,106,113,114,129,130,138,150,154,170,173,186,202,205],[1,3,5,7,9,11,17,19,21,23,59,63,75,79,83,87,119,131,135,139,143,147,151,159,171,175,179,183,187,191,199,203,207],[13,15,99,103,107,155,195],[0,4,6,8,12,14,16,18,20,22,24,26,57,58,74,82,98,106,130,138,170,178,185,218,222,225,226,233,249,250,257,258],[73,114,146,186,234],[81,181],[118,157,197,241,245],[134,158,201,205,253],[174,198,202,206,261],[182,190,194],[230],[238,242,246,254,262],[116,300],[132],[172,220],[188,236],[308],[316],[324],[0,2,4,6,8,10,12,16,18,20,22,24,26,57,58,62,73,74,81,82,85,114,117,129,137,141,145,149,153,169,177,181,185,186,193,218,222,225,226,229,230,234,238,246,249,250,254,257,258,262],[0,2,4,6,8,10,12,16,20,22,24,26,57,58,62,73,74,81,82,85,97,101,105,109,113,117,130,154,169,170,177,181,182,185,186,194,201,218,222,225,226,229,230,234,238,242,246,249,254,257,258,262],[129,137,141,145,149,153,193,202,250],[0,2,4,6,8,10,12,16,20,22,24,26,57,58,62,73,74,81,82,85,97,101,105,109,113,117,130,154,169,170,177,178,181,185,190,194,201,218,222,225,226,229,230,234,238,242,246,249,254,257,258,262],[129,137,141,145,153,193,202,250],[1,3,5,7,9,11,13,15,17,19,59,63,75,79,83,87,99,103,107,111,115,119,131,135,139,143,147,151,155,159,191,199,207],[21,23,171,175,179,187,195],[183],[0,2,4,6,8,10,12,16,20,24,26,57,58,62,73,74,81,82,85,97,105,109,113,117,129,137,138,141,145,146,153,154,186,194,202,218,222,225,226,229,230,234,238,242,246,250,254,262],[169,177,185,201,258],[0,2,4,8,10,12,14,16,18,20,22,24,57,58,74,78,82,86,98,102,106,110,113,114,117,118,130,134,138,142,145,146,149,150,153,154,157,158,170,174,177,178,182,185,186,189,190,193,194,197,198,201,202,205,206,218,226,250,253,258,261],[217],[225,233,241,249,257],[21,23,171,179,191,195,199,203],[21,23,171,179,187,191,199,203],[21,23,171,179,187,191,195],[0,4,8,10,12,14,16,18,20,22,24,26,58,74,98,130,170,174,177,193,194,201,202,218,225,233,234,241,242,249,254,257,258],[57,82,106,129,138,178,217],[86,117,149,185,189,237],[102,118,153,157,197,245],[134,150,154,158,205,253],[182,186,190,198,206,261],[226],[1,3,5,7,13,15,17,19,21,23,59,63,87,99,103,107,111,119,131,135,139,143,151,155,159,171,175,179,183,191,195,199,203,207],[9,11,75,79,115,147,187],[1,3,5,7,9,11,13,15,21,23,59,63,75,79,83,87,99,103,107,111,115,119,143,151,159,171,175,179,183,187,191,195,199,207],[17,19,131,135,139,147,203],[0,4,6,8,10,12,14,16,18,20,22,24,57,58,74,78,81,82,86,98,102,105,106,110,113,114,117,118,129,130,134,138,142,145,146,149,150,153,154,157,158,170,174,178,182,185,186,189,190,193,194,197,198,201,202,205,206,218,226,253,261],[217,233,241,249,257],[225],[21,23,171,179,191,195,203],[21,23,171,179,187,195],[191]]

def readHints (xs : List Nat) : List (Nat × Nat) :=
  xs.flatMap fun z =>
    let value := (hintValues[z % 512]?).getD 0
    ((tagGroups[z / 512]?).getD []).map fun t => (t,value)

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,15,4624,17476,43770],readHints []),([3,240,526,4369,62532],readHints []),([3,240,4895,17476,64170],readHints []),([3,240,4895,17476,65262],readHints []),([3,240,4895,43690,62532],readHints []),([3,240,4895,61166,62532],readHints []),([3,240,7967,17476,62190],readHints []),([3,783,4433],readHints [115714,0,522])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([3,847,4369],readHints [115714,0,522]),([3,3840,4383,8946,21580],readHints []),([3,3840,4383,13050,17476],readHints []),([3,4383,4610,17476,35064],readHints []),([3,4383,8946,17988,63624],readHints []),([3,4383,8946,20292,64716],readHints []),([3,4383,8946,20292,65262],readHints []),([3,4383,17988,43770,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([3,4895,8946,17476,63624],readHints []),([3,4895,17476,35064,61986],readHints []),([3,4895,17476,43770,61440],readHints []),([3,7967,8946,17476,61678],readHints []),([4,14,240,512,4369,62532],readHints []),([4,14,240,7953,17476,61986],readHints []),([4,14,4369,8946,20292,61440],readHints []),([4,14,7953,8946,17476,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,240,4881,17476,64170],readHints []),([4,15,240,4881,17476,65262],readHints []),([4,15,240,4881,43690,62532],readHints []),([4,15,240,4881,61166,62532],readHints []),([4,15,240,7953,17476,61994],readHints []),([4,15,240,7953,17476,62190],readHints []),([4,15,240,7953,17484,61986],readHints []),([4,15,248,7953,17476,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,768,4433],readHints [88578,0,517,1034]),([4,15,832,4369],readHints [88578,0,638,1034]),([4,15,4112,8946,20292,34952],readHints []),([4,15,4369,8946,17988,63624],readHints []),([4,15,4369,8946,20292,39048],readHints []),([4,15,4369,8946,20292,61448],readHints []),([4,15,4369,8946,20292,63624],readHints []),([4,15,4369,8946,20292,63736],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,4369,8946,20292,64170],readHints []),([4,15,4369,8946,20292,64250],readHints []),([4,15,4369,8946,20292,64716],readHints []),([4,15,4369,8946,20292,65262],readHints []),([4,15,4369,8946,20300,61440],readHints []),([4,15,4369,8954,20292,61440],readHints []),([4,15,4369,13042,20292,34952],readHints []),([4,15,4369,17988,43770,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,4369,20292,43770,62194],readHints []),([4,15,4383,8946,20292,63624],readHints []),([4,15,4624,8946,17476,34952],readHints []),([4,15,4881,8946,17476,63624],readHints []),([4,15,4881,17476,35064,61986],readHints []),([4,15,4881,17476,43770,61440],readHints []),([4,15,7953,8946,17476,61448],readHints []),([4,15,7953,8946,17476,61678],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,7953,8946,17484,61440],readHints []),([4,15,7953,8954,17476,61440],readHints []),([4,15,7953,13042,17476,34952],readHints []),([4,15,7953,17476,35064,62194],readHints []),([4,15,7953,17476,43770,62194],readHints []),([4,15,8738,53132],readHints [59922,0,514,1038]),([4,15,8802,53196],readHints [59922,0,514,1038]),([4,15,25126,36744],readHints [59913,0,514,1035])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([4,64,783,4369],readHints [214530,512,1034,4100]),([4,79,768,4369],readHints [88578,0,517,1034]),([4,79,8738,53196],readHints [59922,0,514,1038]),([4,240,512,4383,17476,64170],readHints []),([4,240,512,4383,17476,65262],readHints []),([4,240,512,4383,43690,62532],readHints []),([4,240,512,4383,61166,62532],readHints []),([4,240,514,4383,17476,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([4,240,514,4383,34952,62532],readHints []),([4,240,526,4369,17476,61440],readHints []),([4,240,527,4369,17476,64170],readHints []),([4,240,527,4369,17476,65262],readHints []),([4,240,527,4369,43690,62532],readHints []),([4,240,527,4369,61166,62532],readHints []),([4,240,3840,4383,8738,21580],readHints []),([4,240,3840,4383,8738,62540],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([4,240,3840,4383,8746,62532],readHints []),([4,240,3840,4383,12842,17476],readHints []),([4,240,3840,4383,17476,61994],readHints []),([4,240,3840,4383,17484,61986],readHints []),([4,240,4369,4895,62532],readHints []),([4,240,4383,4610,17476,34952],readHints []),([4,240,4383,8738,17988,63624],readHints []),([4,240,4383,8738,20292,64716],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([4,240,4383,8738,20292,65262],readHints []),([4,240,4383,8738,35464,62532],readHints []),([4,240,4383,17988,43690,61440],readHints []),([4,240,4895,8738,17476,63624],readHints []),([4,240,4895,8738,34952,62532],readHints []),([4,240,4895,17476,34952,61986],readHints []),([4,240,4895,17476,43690,61440],readHints []),([4,240,4895,17476,61166,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([4,240,7967,8738,17476,61678],readHints []),([4,240,7967,17476,57582,61986],readHints []),([4,240,7967,17476,58094,61440],readHints []),([4,248,3840,4383,8738,62532],readHints []),([4,248,3840,4383,17476,61986],readHints []),([4,512,4383,8946,17476,63624],readHints []),([4,512,4383,17476,35064,61986],readHints []),([4,512,4383,17476,43770,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([4,514,4383,17476,35064,61440],readHints []),([4,527,3840,4433],readHints [116226,0,1034]),([4,527,4369,8946,17476,63624],readHints []),([4,527,4369,17476,35064,61986],readHints []),([4,527,4369,17476,43770,61440],readHints []),([4,591,3840,4369],readHints [116226,0,1034]),([4,591,4369,20292],readHints [215042,0,522]),([4,3840,4104,4383,8946,17476],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([4,3840,4344,4383,8738,17476],readHints []),([4,3840,4383,8738,17476,39160],readHints []),([4,3840,4383,8738,21572,35064],readHints []),([4,3840,4383,8946,17476,39048],readHints []),([4,3840,4383,8946,17476,61448],readHints []),([4,3840,4383,8946,17476,63624],readHints []),([4,3840,4383,8946,17476,63736],readHints []),([4,3840,4383,8946,17476,64170],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([4,3840,4383,8946,17476,64250],readHints []),([4,3840,4383,8946,17476,64716],readHints []),([4,3840,4383,8946,17476,65262],readHints []),([4,3840,4383,8946,17484,61440],readHints []),([4,3840,4383,8946,21572,34952],readHints []),([4,3840,4383,8946,35064,62532],readHints []),([4,3840,4383,8946,52428,62532],readHints []),([4,3840,4383,8954,17476,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([4,3840,4383,12834,17476,35064],readHints []),([4,3840,4383,13042,17476,34952],readHints []),([4,3840,4383,17476,35064,61986],readHints []),([4,3840,4383,17476,35064,62194],readHints []),([4,3840,4383,17476,43770,61986],readHints []),([4,3840,4383,17476,43770,62194],readHints []),([4,3855,4383,8946,17476,63624],readHints []),([4,3855,4383,17476,35064,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([4,3855,4433,8751],readHints [116752,23,551,60418]),([4,3855,8017,8738],readHints [117262,0,530,33309,31746]),([4,3919,4369,8815],readHints [116752,23,551,60418]),([4,3919,7953,8738],readHints [117262,0,530,33309,31746]),([4,4369,8959,20303],readHints [215556,10,1024,39426]),([4,4383,7953,8946,17476,63624],readHints []),([4,4383,7953,17476,35064,61986],readHints []),([4,4383,7967,8946,17476,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([4,4383,7967,17476,35064,61986],readHints []),([4,4383,8738,17988,35064,61440],readHints []),([4,4383,8738,20292,35064,62532],readHints []),([4,4383,8946,17476,20292,63624],readHints []),([4,4383,8946,17988,34952,61440],readHints []),([4,4383,8946,20292,34952,62532],readHints []),([4,4383,8946,20292,52428,61440],readHints []),([4,4383,8946,20292,61166,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([4,4433,8751,61680],readHints [216087,1040,216576]),([4,4593,8751,36751],readHints [60020,108,715,1187]),([4,4895,8738,17476,35064,61440],readHints []),([4,4895,8946,17476,34952,61440],readHints []),([4,7953,8738,61616],readHints [117760,1038,11805]),([4,7967,8946,17476,57582,61440],readHints []),([4,8017,8738,61680],readHints [117760,1038,11805]),([5,8,15,240,7953,17476,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,8,15,4369,8946,20292,61440],readHints []),([5,8,15,7953,8946,17476,61440],readHints []),([5,8,240,3840,4383,8738,62532],readHints []),([5,8,240,3840,4383,17476,61986],readHints []),([5,8,3840,4383,8946,17476,61440],readHints []),([5,14,240,512,4369,17476,61440],readHints []),([5,14,240,3840,4369,8738,62532],readHints []),([5,14,240,3840,4369,17476,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,14,240,4369,8738,20292,61440],readHints []),([5,14,240,7953,8738,17476,61440],readHints []),([5,14,3840,4369,8946,17476,61440],readHints []),([5,15,64,768,4369],readHints [217090,0,1029,1546,5123]),([5,15,64,8738,53196],readHints [217618,0,1026,1550]),([5,15,240,512,4369,17476,64170],readHints []),([5,15,240,512,4369,17476,65262],readHints []),([5,15,240,512,4369,43690,62532],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,512,4369,61166,62532],readHints []),([5,15,240,514,4369,17476,63624],readHints []),([5,15,240,514,4369,34952,62532],readHints []),([5,15,240,3840,4369,8738,62540],readHints []),([5,15,240,3840,4369,8746,62532],readHints []),([5,15,240,3840,4369,17476,61994],readHints []),([5,15,240,3840,4369,17484,61986],readHints []),([5,15,240,3848,4369,8738,62532],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,3848,4369,17476,61986],readHints []),([5,15,240,4112,8738,17476,36744],readHints []),([5,15,240,4112,8738,20292,34952],readHints []),([5,15,240,4369,4881,62532],readHints [61068]),([5,15,240,4369,8738,17988,63624],readHints []),([5,15,240,4369,8738,20292,39048],readHints []),([5,15,240,4369,8738,20292,61448],readHints []),([5,15,240,4369,8738,20292,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,4369,8738,20292,63736],readHints []),([5,15,240,4369,8738,20292,64170],readHints []),([5,15,240,4369,8738,20292,64716],readHints []),([5,15,240,4369,8738,20292,65262],readHints []),([5,15,240,4369,8738,20300,61440],readHints []),([5,15,240,4369,8738,21572,36744],readHints []),([5,15,240,4369,8738,35464,62532],readHints []),([5,15,240,4369,8738,36744,62532],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,4369,8738,53196,62532],readHints []),([5,15,240,4369,8746,20292,61440],readHints []),([5,15,240,4369,8946,20292,63624],readHints []),([5,15,240,4369,12834,17476,36744],readHints []),([5,15,240,4369,12834,20292,34952],readHints []),([5,15,240,4369,17988,43690,61440],readHints []),([5,15,240,4369,20292,36744,61986],readHints []),([5,15,240,4369,20292,43690,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,4369,64580],readHints [89095,515,1538,18003]),([5,15,240,4383,8738,20292,63624],readHints []),([5,15,240,4383,8738,36744,62532],readHints []),([5,15,240,4881,8738,17476,63624],readHints []),([5,15,240,4881,8738,34952,62532],readHints []),([5,15,240,4881,17476,34952,61986],readHints []),([5,15,240,4881,17476,43690,61440],readHints []),([5,15,240,4881,17476,61166,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,6417,62532],readHints [89095,515,1538,18003]),([5,15,240,7953,8738,17476,61448],readHints []),([5,15,240,7953,8738,17476,61678],readHints []),([5,15,240,7953,8738,17484,61440],readHints []),([5,15,240,7953,8738,62532,63624],readHints []),([5,15,240,7953,8746,17476,61440],readHints []),([5,15,240,7953,12834,17476,34952],readHints []),([5,15,240,7953,17476,34952,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,7953,17476,34952,62194],readHints []),([5,15,240,7953,17476,35064,61986],readHints []),([5,15,240,7953,17476,36744,61986],readHints []),([5,15,240,7953,17476,43690,61986],readHints []),([5,15,240,7953,17476,52428,61986],readHints []),([5,15,240,7953,17476,57582,61986],readHints []),([5,15,240,7953,17476,58094,61440],readHints []),([5,15,240,7953,17476,61166,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,7953,17476,61986,63624],readHints []),([5,15,240,7953,17476,61986,64170],readHints []),([5,15,240,7953,20292,34952,61986],readHints []),([5,15,240,7953,34952,61986,62532],readHints []),([5,15,240,7967,17476,34952,61986],readHints []),([5,15,248,3840,4369,8738,62532],readHints []),([5,15,248,3840,4369,17476,61986],readHints []),([5,15,248,4369,8738,20292,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,248,7953,8738,17476,61440],readHints []),([5,15,512,3840,4433],readHints [118274,0,1546,5124]),([5,15,512,4369,8946,17476,63624],readHints []),([5,15,512,4369,17476,35064,61986],readHints []),([5,15,512,4369,17476,43770,61440],readHints []),([5,15,514,4369,17476,35064,61440],readHints []),([5,15,576,3840,4369],readHints [218114,0,1546,5124]),([5,15,576,4369,20292],readHints [218626,0,1034,11780])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,752,4369,20292],readHints [219176,1,1034,1615,11856,118786]),([5,15,2288,4369,62532],readHints [89095,515,1538,18003]),([5,15,3840,4112,8738,17476,35064],readHints []),([5,15,3840,4112,8946,17476,34952],readHints []),([5,15,3840,4369,8738,17476,39160],readHints []),([5,15,3840,4369,8738,21572,35064],readHints []),([5,15,3840,4369,8946,17476,39048],readHints []),([5,15,3840,4369,8946,17476,61448],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,3840,4369,8946,17476,63624],readHints []),([5,15,3840,4369,8946,17476,63736],readHints []),([5,15,3840,4369,8946,17476,64170],readHints []),([5,15,3840,4369,8946,17476,64250],readHints []),([5,15,3840,4369,8946,17476,64716],readHints []),([5,15,3840,4369,8946,17476,65262],readHints []),([5,15,3840,4369,8946,17484,61440],readHints []),([5,15,3840,4369,8946,20292,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,3840,4369,8946,21572,34952],readHints []),([5,15,3840,4369,8946,35064,62532],readHints []),([5,15,3840,4369,8946,52428,62532],readHints []),([5,15,3840,4369,8954,17476,61440],readHints []),([5,15,3840,4369,12834,17476,35064],readHints []),([5,15,3840,4369,13042,17476,34952],readHints []),([5,15,3840,4369,17476,35064,61986],readHints []),([5,15,3840,4369,17476,35064,62194],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,3840,4369,17476,43770,61986],readHints []),([5,15,3840,4369,17476,43770,62194],readHints []),([5,15,3840,4369,62114],readHints [219656,0,1586,6675]),([5,15,3840,4383,8946,17476,63624],readHints []),([5,15,3840,4383,17476,35064,61986],readHints []),([5,15,3840,4433,8738],readHints [61454,0,517,1042,10768,17410]),([5,15,3840,4433,8751],readHints [119312,517,1063,4190,17410]),([5,15,3840,4433,8802],readHints [51726,0,517,1042,10768,17410])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,3840,4433,8946],readHints [51741,26,557,1119,61954]),([5,15,3840,4433,13107],readHints [220162,0,517,1034]),([5,15,3840,4433,13171],readHints [119810,0,517,1034]),([5,15,3840,4433,52428],readHints [220674,0,517,1034,5123,9742]),([5,15,3840,4433,56797],readHints [120334,0,517,1042,10768,20994]),([5,15,3840,4433,61986],readHints [51726,0,517,1042,10768,17410]),([5,15,3840,4465,8738],readHints [73750,25,544,1042,1578,6691,8718]),([5,15,3840,4593,8866],readHints [73750,25,544,1052,1578,6691,8728])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,3840,5457,8738],readHints [61454,0,517,1042,10768,17410]),([5,15,3840,5457,34952],readHints [120834,0,517,1034,5123,9739]),([5,15,3840,8017,8738],readHints [121358,0,1042,10768,74242]),([5,15,3840,8738,13171],readHints [121870,0,517,1026,1554]),([5,15,3840,8738,51340],readHints [74770,0,517,1026,1550,5123,8714]),([5,15,3840,8738,52364],readHints [74770,0,517,1026,1550,5123,8714]),([5,15,3840,8738,61070],readHints [221202,25,544,1558,14375]),([5,15,3840,8738,61102],readHints [122386,0,517,1550,14375,31754])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,3840,8802,13107],readHints [221710,0,517,1026,1554]),([5,15,3840,8802,52428],readHints [222226,0,517,1026,1550,5123]),([5,15,3840,13299,21845],readHints [222722,0,517,1052,1546]),([5,15,3840,13299,43690],readHints [223242,0,517,1052,1538,28696]),([5,15,3840,21845,39417],readHints [223768,25,544,1065,1564]),([5,15,3840,25126,34952],readHints [74761,0,517,1026,1547,5123,8714]),([5,15,3840,39417,43690],readHints [224297,25,544,1560]),([5,15,3848,4369,8946,17476,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,3855,4369,8946,17476,63624],readHints []),([5,15,3855,4369,17476,35064,61986],readHints []),([5,15,3855,4433,8738],readHints [122894,517,1042,4151,10768,21021,9730]),([5,15,3904,4369,8802],readHints [61454,0,638,1042,10768,17410]),([5,15,3904,4369,8946],readHints [51741,26,591,1119,61954]),([5,15,3904,7953,8738],readHints [224782,0,653,1042,10768,5183,74242]),([5,15,3968,4369,61986],readHints [225339,0,1586]),([5,15,3968,4593,8738],readHints [73750,25,608,1052,1578,6820,8728])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,4096,4369,8946,20292,34952],readHints []),([5,15,4096,7953,8946,17476,34952],readHints []),([5,15,4336,4369,8738,17476,36744],readHints []),([5,15,4336,4369,8738,20292,34952],readHints []),([5,15,4336,7953,8738,17476,34952],readHints []),([5,15,4369,7953,8946,17476,63624],readHints []),([5,15,4369,7953,17476,35064,61986],readHints []),([5,15,4369,8738,8946,20292,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,4369,8738,17988,35064,61440],readHints []),([5,15,4369,8738,20292,35064,61680],readHints []),([5,15,4369,8738,20292,35064,62532],readHints []),([5,15,4369,8738,53128],readHints [123395,0,1085,1541,62520,5129]),([5,15,4369,8802,20292],readHints [75344,0,521,1662,5131,24578]),([5,15,4369,8946,17476,20292,63624],readHints []),([5,15,4369,8946,17476,36744,61986],readHints []),([5,15,4369,8946,17988,34952,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,4369,8946,20292],readHints [75816,26,553,1615,6736,5141,24578]),([5,15,4369,8946,20292,34952,61440],readHints []),([5,15,4369,8946,20292,34952,61680],readHints []),([5,15,4369,8946,20292,34952,61986],readHints []),([5,15,4369,8946,20292,34952,62194],readHints []),([5,15,4369,8946,20292,34952,62532],readHints []),([5,15,4369,8946,20292,34952,63624],readHints []),([5,15,4369,8946,20292,35064,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,4369,8946,20292,36744,61440],readHints []),([5,15,4369,8946,20292,43690,61440],readHints []),([5,15,4369,8946,20292,43770,61440],readHints []),([5,15,4369,8946,20292,52428,61440],readHints []),([5,15,4369,8946,20292,53196,61440],readHints []),([5,15,4369,8946,20292,61166,61440],readHints []),([5,15,4369,8946,20292,61440,63624],readHints []),([5,15,4369,8946,20292,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,4369,8946,20303],readHints [225832,607,1615,13004,4301,6736,24605]),([5,15,4369,8946,45243],readHints [75855,26,553,1576,6782,18453,8706]),([5,15,4369,8959,20292],readHints [226344,0,522,1615,6736,5636,226818]),([5,15,4369,13299,20292],readHints [227408,0,522,1662,227842]),([5,15,4369,20292,56589],readHints [228392,26,553,1103,11797,9296,28674]),([5,15,4369,25122,36744],readHints [123395,0,1085,1541,62520,5129]),([5,15,4369,63736,64170],readHints [228872,1541]),([5,15,4369,64716,65416],readHints [76291,0,1597])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,4383,8946,20292,34952,61440],readHints []),([5,15,4433,8738,36744],readHints [75267,0,540,1541,5144,24578]),([5,15,4433,8738,61680],readHints [123909,1550,12848,4119,5632,8733]),([5,15,4433,8738,61695],readHints [124421,0,124942,8706]),([5,15,4593,8738,28791],readHints [125536,25,540,1066,1593,11918,18596]),([5,15,4593,8738,36744],readHints [125497,25,540,1066,1632,11832,5144]),([5,15,4593,8738,36751],readHints [229433,540,1066,1632,13070,4212,11832]),([5,15,4593,8751,36744],readHints [229945,620,1066,1632,5838,5217])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,4593,36744,56797],readHints [75818,25,540,1593,11919,18488]),([5,15,4881,8738,17476,35064,61440],readHints []),([5,15,4881,8946,17476,34952,61440],readHints []),([5,15,7953,8738,17476,35064,61680],readHints []),([5,15,7953,8946,17476,34952,61440],readHints []),([5,15,7953,8946,17476,34952,61680],readHints []),([5,15,7953,8946,17476,34952,61986],readHints []),([5,15,7953,8946,17476,34952,62194],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,7953,8946,17476,35064,61440],readHints []),([5,15,7953,8946,17476,36744,61440],readHints []),([5,15,7953,8946,17476,43690,61440],readHints []),([5,15,7953,8946,17476,43770,61440],readHints []),([5,15,7953,8946,17476,52428,61440],readHints []),([5,15,7953,8946,17476,57582,61440],readHints []),([5,15,7953,8946,17476,61166,61440],readHints []),([5,15,7953,8946,17476,61440,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,7953,8946,20292],readHints [75816,26,553,1615,5141,24578]),([5,15,7953,8946,20292,34952,61440],readHints []),([5,15,7953,20292,61986],readHints [76359,0,23103,4240,28752]),([5,15,7953,36744,61986],readHints [76307,0,1807,8807]),([5,15,7967,8946,17476,34952,61440],readHints []),([5,15,8177,8738,36744],readHints [230456,25,540,1167,1678,5144,21156]),([5,15,8738,13299,36744],readHints [230968,0,514,1052,1678,8728,28817]),([5,15,8738,16388,36744],readHints [89609,0,514,1048,1547,8732])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,8738,17412,36744],readHints [89609,0,514,1048,1547,8732]),([5,15,8738,17476,53128],readHints [231433,0,514,1547,4187,8714]),([5,15,8738,20228,34952],readHints [90121,0,514,1151,1547,5130,8832]),([5,15,8738,34952,45307],readHints [232063,0,514,1545]),([5,15,8738,36744,39417],readHints [232472,25,554,1545,19041]),([5,15,8738,36744,40953],readHints [232984,25,655,1545,19041,18578]),([5,15,8738,36744,48123],readHints [233496,0,514,1545,24721]),([5,15,8738,36744,60942],readHints [234012,25,1593,19052])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,8738,53196,65416],readHints [234569,0,514,1082,28682]),([5,15,8802,17476,36744],readHints [235017,0,514,1048,1547,8732]),([5,15,8802,20292,34952],readHints [90121,0,514,1151,1547,5130,8832]),([5,15,8946,20292,21845],readHints [125973,26,1088,1577,62978]),([5,15,8946,20292,24405],readHints [235541,26,1088,1577,62978,6723,18519]),([5,15,8946,20292,43690],readHints [125993,26,1088,1557,62986]),([5,15,8946,20292,61166],readHints [236073,26,1576,62986,14431,18524]),([5,15,17476,25122,36744],readHints [236553,0,1026,1547,12891,5392])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,20292,21845,35064],readHints [237263,1,576,1034,1809,5187,20994]),([5,15,20292,35064,43690],readHints [237578,1,576,1743,11843]),([5,15,26214,36744,61986],readHints [238088,0,238601]),([5,15,36744,39321,61986],readHints [126472,0,1586]),([5,64,527,3840,4369],readHints [239106,512,1546,5636]),([5,64,3855,4369,8751],readHints [239632,535,1063,4123,17410]),([5,64,3855,7953,8738],readHints [240142,512,1042,4100,21021,28674]),([5,64,4369,8751,61680],readHints [240663,1552,76800])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([5,64,7953,8738,61680],readHints [241152,1550,8733]),([5,79,512,3840,4369],readHints [118274,0,1546,5124]),([5,79,3840,4369,8738],readHints [61454,0,517,1042,10768,17410]),([5,79,3840,4369,8751],readHints [241680,517,1063,4190,17410]),([5,79,3840,4369,8802],readHints [61454,0,517,1042,10768,17410]),([5,79,3840,4369,8815],readHints [119312,517,1063,4190,17410]),([5,79,3840,4369,8946],readHints [51741,26,557,1119,61954]),([5,79,3840,4369,13107],readHints [119810,0,517,1034])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([5,79,3840,4369,52428],readHints [120834,0,517,1034,5123,9742]),([5,79,3840,4369,56797],readHints [120334,0,517,1042,10768,20994]),([5,79,3840,4369,61986],readHints [51726,0,517,1042,10768,17410]),([5,79,3840,7953,8738],readHints [121358,0,1042,10768,74242]),([5,79,3840,8738,13107],readHints [121870,0,517,1026,1554]),([5,79,3840,8738,52428],readHints [74770,0,517,1026,1550,5123,8714]),([5,79,3840,8738,61166],readHints [122386,0,517,1550,14375,31754]),([5,79,3855,4369,8738],readHints [242190,517,1042,4151,10768,21021,9730])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([5,79,3904,4369,8738],readHints [242702,0,517,1042,10768,17410]),([5,79,3919,4369,8738],readHints [122894,517,1042,4151,10768,21021,9730]),([5,79,4369,8738,20292],readHints [75267,0,521,1541,5131,24578]),([5,79,4369,8738,36744],readHints [75267,0,540,1541,5144,24578]),([5,79,4369,8738,61680],readHints [123909,1550,12848,4119,8733]),([5,79,4369,8738,61695],readHints [124421,0,124942,8706]),([5,79,8738,17476,36744],readHints [89609,0,514,1048,1547,8732]),([5,79,8738,20292,34952],readHints [90121,0,514,1151,1547,5130,8832])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_54 : List (List ℕ × List (ℕ × ℕ)) := [([5,112,4369,8751,61440],readHints [126991,27,23205,6657,5655]),([5,143,3840,4593,8738],readHints [73750,25,544,1052,1578,6691,8728]),([5,176,7953,8738,61440],readHints [127489,4,23054,5632]),([5,240,512,4369,4383,62532],readHints [40076]),([5,240,512,4383,8738,17476,63624],readHints []),([5,240,512,4383,8738,34952,62532],readHints []),([5,240,512,4383,17476,34952,61986],readHints []),([5,240,512,4383,17476,43690,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_54 : K_54.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_55 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,512,4383,17476,61166,61440],readHints []),([5,240,514,4383,17476,34952,61440],readHints []),([5,240,527,4369,8738,17476,63624],readHints []),([5,240,527,4369,8738,34952,62532],readHints []),([5,240,527,4369,17476,34952,61986],readHints []),([5,240,527,4369,17476,43690,61440],readHints []),([5,240,527,4369,17476,61166,61440],readHints []),([5,240,527,4369,20292],readHints [243240,513,1034,1615,4176,243714])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_55 : K_55.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_56 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,527,4369,62532],readHints [244226,1034]),([5,240,783,4369,17476],readHints [244738,610,1034,4370,9857]),([5,240,3840,4104,4383,8738,17476],readHints []),([5,240,3840,4383,8738,17476,39048],readHints []),([5,240,3840,4383,8738,17476,61448],readHints []),([5,240,3840,4383,8738,17476,63624],readHints []),([5,240,3840,4383,8738,17476,63736],readHints []),([5,240,3840,4383,8738,17476,64170],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_56 : K_56.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_57 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,3840,4383,8738,17476,64716],readHints []),([5,240,3840,4383,8738,17476,65262],readHints []),([5,240,3840,4383,8738,17484,61440],readHints []),([5,240,3840,4383,8738,21572,34952],readHints []),([5,240,3840,4383,8738,34952,62532],readHints []),([5,240,3840,4383,8738,35064,62532],readHints []),([5,240,3840,4383,8738,43690,62532],readHints []),([5,240,3840,4383,8738,52428,62532],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_57 : K_57.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_58 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,3840,4383,8738,61166,62532],readHints []),([5,240,3840,4383,8738,62532,63624],readHints []),([5,240,3840,4383,8738,62532,64716],readHints []),([5,240,3840,4383,8746,17476,61440],readHints []),([5,240,3840,4383,8946,17476,63624],readHints []),([5,240,3840,4383,8946,34952,62532],readHints []),([5,240,3840,4383,12834,17476,34952],readHints []),([5,240,3840,4383,17476,34952,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_58 : K_58.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_59 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,3840,4383,17476,34952,62194],readHints []),([5,240,3840,4383,17476,35064,61986],readHints []),([5,240,3840,4383,17476,43690,61986],readHints []),([5,240,3840,4383,17476,52428,61986],readHints []),([5,240,3840,4383,17476,61166,61986],readHints []),([5,240,3840,4383,17476,61986,63624],readHints []),([5,240,3840,4383,17476,61986,64170],readHints []),([5,240,3840,4383,34952,61986,62532],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_59 : K_59.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_60 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,3855,4383,8738,17476,63624],readHints []),([5,240,3855,4383,8738,34952,62532],readHints []),([5,240,3855,4383,17476,34952,61986],readHints []),([5,240,4369,4895,17476,61440],readHints []),([5,240,4369,8751,20303],readHints [245352,551,1551,12947,4301,6731,17947,24616]),([5,240,4369,8751,36751],readHints [245890,577,1107,1585,12947,19060,4227,5659]),([5,240,4369,8751,61504],readHints [246321,27,1552,246893]),([5,240,4369,8751,61568],readHints [247311,27,23076,6657,5655])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_60 : K_60.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_61 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,4369,8879,61440],readHints [126991,27,23076,6657,5655]),([5,240,4369,17476,64512],readHints [247906,4,23042,33446,5632]),([5,240,4383,7953,8738,17476,63624],readHints []),([5,240,4383,7953,8738,34952,62532],readHints []),([5,240,4383,7953,8738,62532],readHints []),([5,240,4383,7953,17476,34952,61986],readHints []),([5,240,4383,7967,8738,17476,63624],readHints []),([5,240,4383,7967,8738,34952,62532],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_61 : K_61.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_62 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,4383,7967,17476,34952,61986],readHints []),([5,240,4383,8738,17476,20292,63624],readHints []),([5,240,4383,8738,17476,35464,61440],readHints []),([5,240,4383,8738,17476,36744,63624],readHints []),([5,240,4383,8738,17988,34952,61440],readHints []),([5,240,4383,8738,20292,34952,62532],readHints []),([5,240,4383,8738,20292,52428,61440],readHints []),([5,240,4383,8738,20292,61166,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_62 : K_62.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_63 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,4383,8738,34952,36744,62532],readHints []),([5,240,4433,8751,61440],readHints [76303,27,1552,76801,5655]),([5,240,4895,8738,17476,34952,61440],readHints []),([5,240,7441,17476,61440],readHints [90625,4,1538,5632,8836]),([5,240,7953,7967,17476,61986],readHints []),([5,240,7953,8738,61504],readHints [248369,4,1550,248941]),([5,240,7953,8738,61568],readHints [249345,4,23100,5632]),([5,240,7953,8866,61440],readHints [249857,4,23100,5632])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_63 : K_63.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_64 : List (List ℕ × List (ℕ × ℕ)) := [([5,240,7953,17476,61952],readHints [90899,4,1538,5632,8871]),([5,240,7953,61986,62532],readHints [250417,4,1744,14445,5632]),([5,240,7953,61986,63624],readHints [251156,4,1108]),([5,240,7967,8738,17476,57582,61440],readHints []),([5,240,8017,8738,61440],readHints [127489,4,23054,5632]),([5,240,17476,58094,61440],readHints [251393,4,1546,5632,5252]),([5,248,3840,4383,8738,17476,61440],readHints []),([5,255,4369,8738,20303],readHints [251908,530,1536,17923,24686])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_64 : K_64.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_65 : List (List ℕ × List (ℕ × ℕ)) := [([5,255,4369,8738,62543],readHints [128004,68,1550,8776]),([5,255,4369,17487,63624],readHints [126507,38,1540]),([5,255,4369,34952,62543],readHints [128004,38,23042]),([5,255,8738,17652,36744],readHints [252485,1,629,1157,1654]),([5,255,8738,20468,34952],readHints [128581,68,629,1157,1654,5268]),([5,512,4383,8738,17476,35064,61440],readHints []),([5,512,4383,8946,17476,34952,61440],readHints []),([5,527,4369,8738,17476,35064,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_65 : K_65.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_66 : List (List ℕ × List (ℕ × ℕ)) := [([5,527,4369,8946,17476,34952,61440],readHints []),([5,752,7953,17476,61440],readHints [90625,4,1538,5632,8836]),([5,1103,3840,4369,8738],readHints [252942,0,558,1042,10768,17410]),([5,1103,3840,4369,34952],readHints [129026,0,559,1034,5158,9739]),([5,1792,4369,17487,61440],readHints [77316,47,522,1024,5670]),([5,3840,3855,4433,8738],readHints [129550,512,1042,4100,52226,21021]),([5,3840,3919,4369,8738],readHints [129550,512,1042,4100,52226,21021]),([5,3840,4096,4383,8738,17476,35064],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_66 : K_66.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_67 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4096,4383,8946,17476,34952],readHints []),([5,3840,4336,4383,8738,17476,34952],readHints []),([5,3840,4369,4383,8946,17476,63624],readHints []),([5,3840,4369,4383,17476,35064,61986],readHints []),([5,3840,4369,8738,61616],readHints [130048,1550,5637,8733]),([5,3840,4369,8738,64432],readHints [253440,1550,24687]),([5,3840,4369,8738,65456],readHints [130560,1550,24687]),([5,3840,4369,8959,17487],readHints [253956,45,522,1536,5683,28674])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_67 : K_67.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_68 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4369,17487,35071],readHints [128721,6,522,1024,1704,4265,5649]),([5,3840,4369,17487,61952],readHints [131240,23044,19221,14614]),([5,3840,4369,17487,63488],readHints [254468,47,522,1024,5670]),([5,3840,4369,19535,61440],readHints [77316,47,522,1024,5670]),([5,3840,4369,34952,64432],readHints [254976,1538]),([5,3840,4383,8738,8946,17476,63624],readHints []),([5,3840,4383,8738,17476,35064,61440],readHints []),([5,3840,4383,8738,17476,35064,61680],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_68 : K_68.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_69 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4383,8738,17476,35064,61986],readHints []),([5,3840,4383,8738,17476,35064,62532],readHints []),([5,3840,4383,8738,17476,35064,63624],readHints []),([5,3840,4383,8738,17476,35064,63736],readHints []),([5,3840,4383,8738,17476,43770,61440],readHints []),([5,3840,4383,8946,17476,34952,61440],readHints []),([5,3840,4383,8946,17476,34952,61680],readHints []),([5,3840,4383,8946,17476,34952,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_69 : K_69.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_70 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4383,8946,17476,34952,62194],readHints []),([5,3840,4383,8946,17476,34952,62532],readHints []),([5,3840,4383,8946,17476,34952,63624],readHints []),([5,3840,4383,8946,17476,35064,61440],readHints []),([5,3840,4383,8946,17476,43690,61440],readHints []),([5,3840,4383,8946,17476,43770,61440],readHints []),([5,3840,4383,8946,17476,52428,61440],readHints []),([5,3840,4383,8946,17476,61166,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_70 : K_70.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_71 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4383,8946,17476,61440,63624],readHints []),([5,3840,4383,8946,17476,63624],readHints []),([5,3840,4383,17476,34952,35064,61986],readHints []),([5,3840,4383,17476,35064,61440,61986],readHints []),([5,3840,4383,17476,35064,61986],readHints []),([5,3840,4433,8738,61680],readHints [130048,1550,5637,8733]),([5,3840,4433,8738,65520],readHints [130560,1550,24687]),([5,3840,4593,8751,34959],readHints [255604,32,620,1303,1699,5662])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_71 : K_71.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_72 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,6417,17487,61440],readHints [77316,47,522,1024,5670]),([5,3840,8738,17487,20753],readHints [256014,46,1024,1554,256514,11792]),([5,3840,17487,20753,34952],readHints [257026,47,512,1034,5670,9739]),([5,3855,3904,4369,8738],readHints [257550,0,682,1042,91307,43549,17410]),([5,3855,4369,8751,63624],readHints [258084,23,684,1107,9862]),([5,3855,4369,8959,17476],readHints [258562,0,522,5636,9228]),([5,3855,4369,17476,61999],readHints [259282,1552,14547,8740]),([5,3855,4369,34952,61999],readHints [259620,23127,18605])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_72 : K_72.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_73 : List (List ℕ × List (ℕ × ℕ)) := [([5,3855,4383,8738,17476,35064,61440],readHints []),([5,3855,4383,8946,17476,34952,61440],readHints []),([5,3855,4593,8751,34952],readHints [260208,66,620,1227,5779,52833]),([5,3855,7953,8738,63624],readHints [131644,0,585,1143,132154]),([5,3855,7953,8946,17476],readHints [260707,26,792,53277,9228]),([5,3855,7953,17476,61986],readHints [261332,1617,4270,8712]),([5,3855,7953,34952,61986],readHints [261692,23090]),([5,3855,8177,8738,34952],readHints [129144,25,540,1305,132120,31890])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_73 : K_73.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_74 : List (List ℕ × List (ℕ × ℕ)) := [([5,3904,4369,8738,61680],readHints [262144,1550,8733]),([5,4369,4383,8946,20292,61440],readHints []),([5,4369,8738,17487,20224],readHints [262689,18,1024,1582,11814,5646,118788]),([5,4369,8738,20303,65280],readHints [263172,18,1024,39534]),([5,4369,8738,62543,65280],readHints [263748,1540,11814,18598]),([5,4369,8751,35064,63624],readHints [264474,1819]),([5,4369,8751,36751,61440],readHints [131611,65,725,1047,18948,5285,9832]),([5,4369,8751,61440,65423],readHints [264731,1551,18948,18204])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_74 : K_74.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_75 : List (List ℕ × List (ℕ × ℕ)) := [([5,4369,8751,61680,63624],readHints [265239,1060,18944]),([5,4369,8946,20292,65520],readHints [132634,1576,62976,18532]),([5,4369,8959,17476,61680],readHints [265728,1538]),([5,4369,17476,61680,61999],readHints [266450,1559,39635,5156]),([5,4369,17487,20224,34952],readHints [77350,10,512,1071,5634]),([5,4369,17487,35071,61440],readHints [266758,23087,5124]),([5,4369,17487,36744,63624],readHints [267549,1822]),([5,4369,17487,61440,63743],readHints [267823,1540])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_75 : K_75.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_76 : List (List ℕ × List (ℕ × ℕ)) := [([5,4369,17487,63624,65280],readHints [268326,1579]),([5,4369,34952,61680,61999],readHints [268836,77847,18093]),([5,4369,34952,62543,65280],readHints [269350,1540]),([5,4383,7953,8738,17476,35064,61440],readHints []),([5,4383,7953,8946,17476,34952,61440],readHints []),([5,4383,7967,8738,17476,35064,61440],readHints []),([5,4383,7967,8946,17476,34952,61440],readHints []),([5,4383,8738,17476,20292,35064,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_76 : K_76.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_77 : List (List ℕ × List (ℕ × ℕ)) := [([5,4383,8738,17476,35064,36744,61440],readHints []),([5,4383,8946,17476,20292,34952,61440],readHints []),([5,4593,8738,36744,65520],readHints [132633,1593,12800,18646]),([5,4593,8751,34952,61680],readHints [269890,1648]),([5,4593,8751,36744,61440],readHints [270511,65,727,270910,33496,21209,8922,9947]),([5,7953,7967,8946,17476,61440],readHints [63532]),([5,7953,8738,20303,61440],readHints [271364,18,1024,39534]),([5,7953,8738,61440,65359],readHints [271876,1537,18542])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_77 : K_77.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_78 : List (List ℕ × List (ℕ × ℕ)) := [([5,7953,8738,61680,63624],readHints [272384,272956]),([5,7953,8946,17476,61680],readHints [273434,1635]),([5,7953,8946,17487,61440],readHints [131160,77853,274069,133164,8705]),([5,7953,17476,61680,61986],readHints [274644,274944,5128]),([5,7953,34952,61680,61986],readHints [275516,77824]),([5,8177,8738,34952,61680],readHints [275993,1656,12800]),([5,8738,17652,36744,65280],readHints [133633,1605]),([5,8738,20468,34952,65280],readHints [276548,1605])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_78 : K_78.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_79 : List (List ℕ × List (ℕ × ℕ)) := [([5,8738,20468,36744,61440],readHints [133633,1605]),([5,17487,26214,36744,61440],readHints [277212,0,733,1311,5636,9829]),([5,17487,36744,39321,61440],readHints [277725,0,278236,5636]),([6,8,15,240,3840,4369,8738,62532],readHints []),([6,8,15,240,3840,4369,17476,61986],readHints []),([6,8,15,240,4369,8738,20292,61440],readHints []),([6,8,15,240,7953,8738,17476,61440],readHints []),([6,8,15,3840,4369,8946,17476,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_79 : K_79.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_80 : List (List ℕ × List (ℕ × ℕ)) := [([6,8,240,3840,4383,8738,17476,61440],readHints []),([6,14,240,3840,4369,8738,17476,61440],readHints []),([6,15,64,512,3840,4369],readHints [278530,0,2058,91652]),([6,15,64,3840,4369,8738],readHints [134158,0,1029,1554,5123,13328,23554]),([6,15,64,3840,4369,8751],readHints [279056,1029,1575,5726,5123,23554]),([6,15,64,3840,4369,8802],readHints [279566,0,1029,1554,5123,13328,23554]),([6,15,64,3840,4369,8946],readHints [280093,26,1069,1631,5171,134658]),([6,15,64,3840,4369,13107],readHints [280578,0,1029,1546,5123])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_80 : K_80.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_81 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,64,3840,4369,52428],readHints [281090,0,1029,1546,92163,7694]),([6,15,64,3840,4369,56797],readHints [281614,0,1029,1554,5123,13328,29186]),([6,15,64,3840,4369,61986],readHints [282126,0,1029,1554,5123,13328,23554]),([6,15,64,3840,4433,8738],readHints [282638,0,1029,1554,5123,13328,23554]),([6,15,64,3840,7953,8738],readHints [283150,0,1554,5124,13328,92674]),([6,15,64,3840,8738,13107],readHints [283662,0,1029,1538,2066,3082]),([6,15,64,3840,8738,52428],readHints [284178,0,1029,1538,2062,6147,7178]),([6,15,64,3840,8738,61166],readHints [284690,0,1029,2062,10791,28682])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_81 : K_81.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_82 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,64,3855,4369,8738],readHints [285198,1029,1554,5687,5123,13328,29213,7682]),([6,15,64,3904,4369,8738],readHints [285710,0,1029,1554,5123,13328,23554]),([6,15,64,4369,8738,20292],readHints [286211,0,1033,2053,6155,33794]),([6,15,64,4369,8738,36744],readHints [286723,0,1052,2053,91672,33794]),([6,15,64,4369,8738,61680],readHints [287237,2062,4144,5655,2560,7197]),([6,15,64,4369,8738,61695],readHints [287749,0,93198,7170]),([6,15,64,8738,17476,36744],readHints [288265,0,1026,1560,2059,32284]),([6,15,64,8738,20292,34952],readHints [288777,0,1026,1663,2059,32384,6154])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_82 : K_82.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_83 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,68,3840,4369,8738],readHints [289291,0,1029,1545,18958,5123,13328,23554]),([6,15,79,3840,4369,8738],readHints [289806,1029,1554,290307,135184,23554]),([6,15,80,3840,4369,8738],readHints [134202,26,1069,1609,5123,13446,23639]),([6,15,96,3840,4369,8738],readHints [290824,25,1056,1554,2055,9747,32270]),([6,15,112,3840,4369,8738],readHints [64008,1,1030,1609,2055,9238,9747,32314]),([6,15,112,4369,8738,61440],readHints [93702,515,10299,4116,5647,2561,3077]),([6,15,128,3840,4369,61986],readHints [291336,0,34354,9747]),([6,15,128,3840,4593,8738],readHints [291862,25,1056,1564,2090,9763,32280])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_83 : K_83.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_84 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,512,4369,8738,17476,63624],readHints []),([6,15,240,512,4369,8738,34952,62532],readHints []),([6,15,240,512,4369,17476,34952,61986],readHints []),([6,15,240,512,4369,17476,43690,61440],readHints []),([6,15,240,512,4369,17476,61166,61440],readHints []),([6,15,240,512,4369,20292],readHints [292392,1,1546,2127,5200,64514]),([6,15,240,512,4369,62532],readHints [292866,1546]),([6,15,240,514,4369,17476,34952,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_84 : K_84.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_85 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,768,4369,17476],readHints [293378,98,1067,1546,5408,6320,7809]),([6,15,240,1792,4369,17476],readHints [64007,98,1067,1546,2056,64514,6320]),([6,15,240,1911,4369,8738],readHints [293896,515,1055,1713,2055,9238,294535]),([6,15,240,1911,4369,17476],readHints [294919,515,1067,1546,2056,6320,295426]),([6,15,240,2048,4369,62532],readHints [295943,515,19970,24147]),([6,15,240,3003,4369,8738],readHints [296459,515,1058,1545,14350,5684,13328,15381,7682]),([6,15,240,3003,4369,34952],readHints [296962,515,1031,1546,297480,3077,7691]),([6,15,240,3840,4112,8738,17476,34952],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_85 : K_85.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_86 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,3840,4369,8738,17476,39048],readHints []),([6,15,240,3840,4369,8738,17476,61448],readHints []),([6,15,240,3840,4369,8738,17476,63624],readHints []),([6,15,240,3840,4369,8738,17476,63736],readHints []),([6,15,240,3840,4369,8738,17476,64170],readHints []),([6,15,240,3840,4369,8738,17476,64716],readHints []),([6,15,240,3840,4369,8738,17476,65262],readHints []),([6,15,240,3840,4369,8738,17484,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_86 : K_86.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_87 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,3840,4369,8738,20292,63624],readHints []),([6,15,240,3840,4369,8738,21572,34952],readHints []),([6,15,240,3840,4369,8738,34952,62532],readHints []),([6,15,240,3840,4369,8738,35064,62532],readHints []),([6,15,240,3840,4369,8738,36744,62532],readHints []),([6,15,240,3840,4369,8738,43690,62532],readHints []),([6,15,240,3840,4369,8738,52428,62532],readHints []),([6,15,240,3840,4369,8738,61166,62532],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_87 : K_87.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_88 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,3840,4369,8738,62532,63624],readHints []),([6,15,240,3840,4369,8738,62532,64716],readHints []),([6,15,240,3840,4369,8746,17476,61440],readHints []),([6,15,240,3840,4369,8866],readHints [64008,1,1030,1549,2055,9238,9747,32268]),([6,15,240,3840,4369,8946,17476,63624],readHints []),([6,15,240,3840,4369,8946,34952,62532],readHints []),([6,15,240,3840,4369,12834,17476,34952],readHints []),([6,15,240,3840,4369,17476,34952,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_88 : K_88.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_89 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,3840,4369,17476,34952,62194],readHints []),([6,15,240,3840,4369,17476,35064,61986],readHints []),([6,15,240,3840,4369,17476,36744,61986],readHints []),([6,15,240,3840,4369,17476,43690,61986],readHints []),([6,15,240,3840,4369,17476,52428,61986],readHints []),([6,15,240,3840,4369,17476,61166,61986],readHints []),([6,15,240,3840,4369,17476,61986,63624],readHints []),([6,15,240,3840,4369,17476,61986,64170],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_89 : K_89.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_90 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,3840,4369,19524],readHints [64007,1,1030,1546,2056,64514,6161]),([6,15,240,3840,4369,20292,34952,61986],readHints []),([6,15,240,3840,4369,34952,61986,62532],readHints []),([6,15,240,3840,4383,8738,17476,63624],readHints []),([6,15,240,3840,4383,8738,34952,62532],readHints []),([6,15,240,3840,4383,17476,34952,61986],readHints []),([6,15,240,3840,4433,8738],readHints [297998,1,1030,1554,5150,18490,13328,15389,23554]),([6,15,240,3840,6417,17476],readHints [64007,1,1030,1546,2056,64514,6161])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_90 : K_90.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_91 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,3840,7953,17476,34952,61986],readHints []),([6,15,240,3840,13107,21845],readHints [135682,1,1030,1625,2058,13911]),([6,15,240,3840,13107,26214],readHints [136202,1,1030,1545,2050,14002]),([6,15,240,3840,13107,39321],readHints [136194,1,1030,1545,2058,3361]),([6,15,240,3840,13107,43690],readHints [135690,1,1030,1625,2050,3294]),([6,15,240,3840,21845,26214],readHints [136717,1,1030,1545,2060,13852]),([6,15,240,3840,21845,39321],readHints [136716,1,1030,1545,2061,3083]),([6,15,240,3840,21845,52428],readHints [298585,1,1030,2050,13852,6161])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_91 : K_91.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_92 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,3840,26214,43690],readHints [137225,1,1030,34317,9257]),([6,15,240,3840,26214,52428],readHints [137225,1,1030,2058,13916,6161]),([6,15,240,3840,39321,43690],readHints [137737,1,1030,34316,9257]),([6,15,240,3840,39321,52428],readHints [137737,1,1030,2050,13916,6161]),([6,15,240,3840,43690,52428],readHints [299097,1,1030,2058,13852,6161]),([6,15,240,3848,4369,8738,17476,61440],readHints []),([6,15,240,3855,4369,8738,17476,63624],readHints []),([6,15,240,3855,4369,8738,34952,62532],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_92 : K_92.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_93 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,3855,4369,17476,34952,61986],readHints []),([6,15,240,3904,4369,8738],readHints [299534,1,1055,1554,5343,13328,15389,23554]),([6,15,240,3968,4369,8738],readHints [300040,1,1058,1549,2055,138299,9238,9747,7180]),([6,15,240,4096,4369,8738,17476,36744],readHints []),([6,15,240,4096,4369,8738,20292,34952],readHints []),([6,15,240,4096,7953,8738,17476,34952],readHints []),([6,15,240,4369,4881,17476,61440],readHints [61068,44109]),([6,15,240,4369,7953,8738,17476,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_93 : K_93.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_94 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,7953,8738,34952,62532],readHints []),([6,15,240,4369,7953,8738,62532],readHints [94242,78338]),([6,15,240,4369,7953,17476,34952,61986],readHints []),([6,15,240,4369,7953,17476,61986],readHints [61078,78919,94731,44153,79362]),([6,15,240,4369,8738,17476,20292,63624],readHints []),([6,15,240,4369,8738,17476,35464,61440],readHints []),([6,15,240,4369,8738,17476,36744,61440],readHints []),([6,15,240,4369,8738,17476,36744,61680],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_94 : K_94.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_95 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,8738,17476,36744,61986],readHints []),([6,15,240,4369,8738,17476,36744,62532],readHints []),([6,15,240,4369,8738,17476,36744,63624],readHints []),([6,15,240,4369,8738,17476,53196,61440],readHints []),([6,15,240,4369,8738,17988,34952,61440],readHints []),([6,15,240,4369,8738,20292],readHints [138805,1,1033,2079,11839,65064,13827,6155]),([6,15,240,4369,8738,20292,34952,61440],readHints []),([6,15,240,4369,8738,20292,34952,61680],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_95 : K_95.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_96 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,8738,20292,34952,61986],readHints []),([6,15,240,4369,8738,20292,34952,62532],readHints []),([6,15,240,4369,8738,20292,34952,63624],readHints []),([6,15,240,4369,8738,20292,35064,61440],readHints []),([6,15,240,4369,8738,20292,36744,61440],readHints []),([6,15,240,4369,8738,20292,43690,61440],readHints []),([6,15,240,4369,8738,20292,52428,61440],readHints []),([6,15,240,4369,8738,20292,53196,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_96 : K_96.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_97 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,8738,20292,61166,61440],readHints []),([6,15,240,4369,8738,20292,61440,63624],readHints []),([6,15,240,4369,8738,20292,63624],readHints []),([6,15,240,4369,8738,20303],readHints [300597,1042,2079,4247,11839,5736,65064,13827]),([6,15,240,4369,8738,28791],readHints [301090,1,1037,1543,2100,11808,6752,5299,13830]),([6,15,240,4369,8738,34952,36744,62532],readHints []),([6,15,240,4369,8738,36744],readHints [301620,1,1037,1543,2082,11806,6713,5205,3075,6156]),([6,15,240,4369,8738,36744,61440,62532],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_97 : K_97.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_98 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,8738,36744,62532],readHints [40088,78338,65539]),([6,15,240,4369,8738,36751],readHints [302132,1037,1543,2082,11806,6713,5762,5205,3075]),([6,15,240,4369,8738,45243],readHints [138783,1,1033,2101,11917,9295,302603,7170]),([6,15,240,4369,8738,61504],readHints [95266,515,2062,5681,79942,2561]),([6,15,240,4369,8738,61568],readHints [95775,515,10248,4182,6732,5647,2561,3077]),([6,15,240,4369,8738,62532],readHints [95266,515,2059,5681,9286,7175]),([6,15,240,4369,8738,62543],readHints [139298,1,515,2062,9286,7175]),([6,15,240,4369,8738,63624],readHints [95775,515,10248,4182,6732,5647,3077])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_98 : K_98.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_99 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,8738,63631],readHints [139295,1,515,10248,6732,3077,22051]),([6,15,240,4369,8751,20292],readHints [303157,1063,2079,11839,65064,303632,13827]),([6,15,240,4369,8751,36744],readHints [304180,1089,1543,2082,11806,6713,5205,2784,3075,6206]),([6,15,240,4369,8751,62532],readHints [139810,515,2064,9286,24113,7175]),([6,15,240,4369,8751,63624],readHints [139807,515,10248,6732,24079,3077]),([6,15,240,4369,8866,61440],readHints [93702,515,10248,4116,5647,2561,3077]),([6,15,240,4369,8946,20292],readHints [304680,1,1065,2127,91669,13875,33794]),([6,15,240,4369,8946,20292,34952,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_99 : K_99.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_100 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,8946,62532],readHints [305222,802,2069,5741,7175]),([6,15,240,4369,13107,20292],readHints [305717,1,1034,2079,91199,9256,13827,33794]),([6,15,240,4369,13107,36744],readHints [306228,1,1034,1543,2082,11806,26627]),([6,15,240,4369,13107,62532],readHints [140322,515,2050,5681,9286,7175]),([6,15,240,4369,13107,63624],readHints [140831,515,10248,4182,5633,3077]),([6,15,240,4369,17476,63488],readHints [66091,515,10247,4178,36962,3077]),([6,15,240,4369,17476,63624],readHints [66091,515,10247,4178,3077]),([6,15,240,4369,17476,63631],readHints [306731,98,515,10247,3077])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_100 : K_100.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_101 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,17476,63736],readHints [307243,2055,4178,11956,18437]),([6,15,240,4369,17476,63743],readHints [307755,98,2055,11956,18437]),([6,15,240,4369,17476,64716],readHints [308267,515,2050,4178,21097,24162]),([6,15,240,4369,17487,63624],readHints [308779,515,10247,3077]),([6,15,240,4369,19524,61440],readHints [66054,515,10247,4116,36865,3077]),([6,15,240,4369,20292,52428],readHints [309301,1,1034,1567,80447,18435,15400,6146,53777]),([6,15,240,4369,20292,56797],readHints [309813,1,1033,1567,11839,18435,8715,15400,53762]),([6,15,240,4369,21845,63624],readHints [310315,515,10247,4178,3077])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_101 : K_101.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_102 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,26214,62532],readHints [310791,515,2059]),([6,15,240,4369,30583,62532],readHints [311303,515,2050]),([6,15,240,4369,34952,62532],readHints [311815,515,10242]),([6,15,240,4369,34952,62543],readHints [312327,166,515,10242]),([6,15,240,4369,34952,64716],readHints [312839,515,2050,24147]),([6,15,240,4369,34959,62532],readHints [313351,515,10242]),([6,15,240,4369,35064,62532],readHints [313863,10242,13929]),([6,15,240,4369,36744,52428],readHints [314375,1,1034,2100,5181,13827,6146])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_102 : K_102.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_103 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,36744,56797],readHints [314887,1,1037,2100,6698,5181,8781,13909]),([6,15,240,4369,39321,62532],readHints [315399,515,10251]),([6,15,240,4369,43690,63624],readHints [93739,515,10248,4178,3077]),([6,15,240,4369,48059,63624],readHints [315947,515,96264,4178,3077]),([6,15,240,4369,52428,62532],readHints [95266,515,10242,17969,9286]),([6,15,240,4369,52428,63624],readHints [95775,515,10247,4182,17921,3077]),([6,15,240,4369,56797,62532],readHints [140322,515,10251,17969,9286]),([6,15,240,4369,56797,63624],readHints [140831,515,10247,4182,6732,17935,3077])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_103 : K_103.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_104 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,61986,62532],readHints [316450,515,2059,5681,9286,7175]),([6,15,240,4369,61986,63624],readHints [316936,515,317524,6678,9759,3077]),([6,15,240,4369,62532,63078],readHints [317959,515,1547]),([6,15,240,4369,62532,63624],readHints [318471,515,44546,9771,3077]),([6,15,240,4369,62532,64716],readHints [318978,515,1034,4144,21097,9771,12299]),([6,15,240,4369,63624,64170],readHints [319496,515,2183,6678]),([6,15,240,4369,63624,64716],readHints [320007,515,2050,24147]),([6,15,240,4383,8738,17476,36744,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_104 : K_104.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_105 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4383,8738,20292,34952,61440],readHints []),([6,15,240,4433,8738,61440],readHints [320518,515,10254,4116,5647,2561,3077]),([6,15,240,4593,8738,36744],readHints [321081,1,1037,1578,2144,3094,13854,6156]),([6,15,240,4593,8738,63624],readHints [321612,803,10262,4388,5647]),([6,15,240,4881,8738,17476,34952,61440],readHints []),([6,15,240,6417,17476,61440],readHints [66054,515,10247,4116,36865,3077]),([6,15,240,7953,8738,17476,34952,61440],readHints []),([6,15,240,7953,8738,17476,34952,61680],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_105 : K_105.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_106 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,7953,8738,17476,34952,61986],readHints []),([6,15,240,7953,8738,17476,35064,61440],readHints []),([6,15,240,7953,8738,17476,36744,61440],readHints []),([6,15,240,7953,8738,17476,43690,61440],readHints []),([6,15,240,7953,8738,17476,52428,61440],readHints []),([6,15,240,7953,8738,17476,57582,61440],readHints []),([6,15,240,7953,8738,17476,61166,61440],readHints []),([6,15,240,7953,8738,17476,61440,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_106 : K_106.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_107 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,7953,8738,20292],readHints [322101,1,1033,2079,11839,322600,323083]),([6,15,240,7953,8738,20292,34952,61440],readHints []),([6,15,240,7953,8738,34952,61440,62532],readHints []),([6,15,240,7953,8738,36744],readHints [323603,1,1037,1613,6691,92172,8756,7801]),([6,15,240,7953,8946,17476,34952,61440],readHints []),([6,15,240,7953,17476,34952,61440,61986],readHints []),([6,15,240,7953,17476,34952,61986],readHints []),([6,15,240,7953,17476,61986],readHints [324107,1033,96839,5776,45070,10021,13328,24238,15381,29186,7176,7687])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_107 : K_107.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_108 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,7953,34952,61986],readHints [324627,10361,4156,6691,5926,24272,3175]),([6,15,240,7967,8738,17476,34952,61440],readHints []),([6,15,240,8738,13107,20292],readHints [325173,1,1026,1545,2079,5183,13827,7179]),([6,15,240,8738,13107,36744],readHints [325684,1,1026,1549,2082,11861,26627,9273,7180]),([6,15,240,8738,13107,62532],readHints [141346,515,2059,141873]),([6,15,240,8738,13107,63624],readHints [141343,515,2183,4111,5633,9292,3077]),([6,15,240,8738,17476,28791],readHints [326155,1,1026,1548,2057,13937]),([6,15,240,8738,17476,36744],readHints [326665,1,1026,1548,2059,3128,7181])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_108 : K_108.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_109 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,8738,17476,53196],readHints [327177,1,1026,2059,45074,13946]),([6,15,240,8738,17652,36744],readHints [327689,1,1026,1548,2059,32269]),([6,15,240,8738,20292,21845],readHints [328203,1,1600,2057,14352,6677,328706,13937]),([6,15,240,8738,20292,24405],readHints [329227,1,1600,2057,14352,6677,9795,97282,13937]),([6,15,240,8738,20292,30583],readHints [329739,1,1026,1600,2057,13937]),([6,15,240,8738,20292,34952],readHints [330249,1,1026,1600,2059,32323,6154]),([6,15,240,8738,20292,36744],readHints [330761,1,1026,1548,2059,32269]),([6,15,240,8738,20292,43690],readHints [331273,1,1600,2059,14375,6697,24586,3139])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_109 : K_109.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_110 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,8738,20292,52428],readHints [331785,1,1026,2101,10770,13916,6154]),([6,15,240,8738,20292,53196],readHints [332297,1,1026,2059,45074,13916]),([6,15,240,8738,20292,61166],readHints [332809,1,2101,14375,6697,10770,24586,13916]),([6,15,240,8738,20468,34952],readHints [333321,1,515,1026,1600,2059,3077,6154,7235]),([6,15,240,8738,26214,36744],readHints [333833,1,1031,1548,2059,3128,7181]),([6,15,240,8738,34952,45243],readHints [334400,1,1026,34313]),([6,15,240,8738,34952,53196],readHints [334915,1,1026,2112,13952]),([6,15,240,8738,36744,39321],readHints [335372,1,1031,34313,14398,6152])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_110 : K_110.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_111 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,8738,36744,40857],readHints [335884,1,1101,142345,14398]),([6,15,240,8738,36744,48059],readHints [336396,1,1026,34313,33921]),([6,15,240,8738,36744,52428],readHints [336909,1,1026,2100,13852,6154]),([6,15,240,8738,36744,53196],readHints [337421,1,1026,2060,21059,13852]),([6,15,240,8738,36744,61166],readHints [337933,1,2100,14401,13852]),([6,15,240,8738,52428,62532],readHints [142882,515,2057,338481]),([6,15,240,8738,52428,63624],readHints [142879,515,2225,4111,17921,9292,3077]),([6,15,240,8738,61166,62532],readHints [338978,515,2057,4145,6726,6151])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_111 : K_111.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_112 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,8738,61166,63624],readHints [339487,515,2225,4111,18006,9292,3077,6152]),([6,15,240,12066,17476,34952,61713],readHints []),([6,15,240,13107,21845,61440],readHints [80902,515,66562,54273,3077]),([6,15,240,13107,26214,61440],readHints [143366,515,66570,54273,3077]),([6,15,240,13107,39321,61440],readHints [143366,515,66562,54273,3077]),([6,15,240,13107,43690,61440],readHints [80902,515,66570,54273,3077]),([6,15,240,17476,21845,63624],readHints [340011,515,2050,3077]),([6,15,240,17476,26214,36744],readHints [340489,1,1032,1538,2059,3128])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_112 : K_112.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_113 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,17476,36744,39321],readHints [340994,1,1032,142345,6151]),([6,15,240,17476,36744,56797],readHints [341506,1,2057,13911]),([6,15,240,17476,43690,63624],readHints [342059,515,2058,3077]),([6,15,240,17476,61166,63624],readHints [342571,515,2058,18002,3077,6151]),([6,15,240,20292,21845,34952],readHints [343042,1,1088,1546,18519,6211,7691]),([6,15,240,20292,34952,43690],readHints [343562,1,1088,2050,344131]),([6,15,240,20292,34952,56797],readHints [344578,1,2057,13911]),([6,15,240,21845,26214,61440],readHints [143878,515,2061,2561,3077])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_113 : K_113.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_114 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,21845,39321,61440],readHints [143878,515,2060,2561,3077]),([6,15,240,21845,52428,61440],readHints [144390,515,2137,36865,3077]),([6,15,240,26214,34952,62532],readHints [345095,515,2057]),([6,15,240,26214,43690,61440],readHints [80902,515,2057,2561,3077]),([6,15,240,26214,52428,61440],readHints [144902,515,2057,36865,3077]),([6,15,240,34952,39321,62532],readHints [345607,515,2050]),([6,15,240,34952,61166,62532],readHints [346119,515,19978]),([6,15,240,39321,43690,61440],readHints [80902,515,2057,2561,3077])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_114 : K_114.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_115 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,39321,52428,61440],readHints [144902,515,2057,36865,3077]),([6,15,240,43690,52428,61440],readHints [144390,515,2137,36865,3077]),([6,15,248,3840,4369,8738,17476,61440],readHints []),([6,15,255,4369,8738,20292],readHints [346677,0,1033,2079,11839,65064,2564,13827,6155]),([6,15,255,4369,8738,36744],readHints [347188,0,1037,1543,2082,11806,5205,3075,6156]),([6,15,255,4369,8738,62532],readHints [145442,0,515,2059,9286,2564,7175]),([6,15,255,4369,8738,63624],readHints [145439,0,515,10248,3077]),([6,15,255,4369,17476,63624],readHints [347691,0,515,10247,3077])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_115 : K_115.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_116 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,255,4369,34952,62532],readHints [348167,0,515,10242,2564]),([6,15,255,8738,17476,36744],readHints [348681,0,1026,1548,2059,7181]),([6,15,255,8738,20292,34952],readHints [349193,0,1026,1600,2059,6154,7235]),([6,15,512,4369,8738,17476,35064,61440],readHints []),([6,15,512,4369,8946,17476,34952,61440],readHints []),([6,15,752,3840,4369,17476],readHints [349698,1,1069,1546,5273,6195,7692]),([6,15,1088,3840,4369,8738],readHints [350222,0,1029,1554,5123,13328,3080,23554]),([6,15,1088,3840,4369,34952],readHints [145922,0,520,1029,1546,26631,6147,7691])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_116 : K_116.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_117 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,1092,3840,4369,8738],readHints [350731,0,1029,1545,18958,5123,13328,3080,23554]),([6,15,1092,3840,4369,34952],readHints [145922,0,520,1029,1546,26631,6147,7691]),([6,15,1792,4369,17476,61440],readHints [81415,0,517,1034,1544,25092,8706,3075]),([6,15,1911,3840,4369,8738],readHints [351240,0,1029,1609,2055,9747,146490]),([6,15,1911,3840,4369,17476],readHints [351751,0,1029,1546,2056,2564,146434]),([6,15,2288,3840,4369,17476],readHints [352263,1,549,1030,1546,2056,6161,7170]),([6,15,2288,4369,17476,61440],readHints [66054,515,10247,4116,36865,3077]),([6,15,3549,3840,4369,17476],readHints [352779,0,549,1029,1545,18960,5174,2564,13326,7692])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_117 : K_117.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_118 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3549,3840,4369,34952],readHints [353330,0,520,1029,1717,19031,26631,6147,7691]),([6,15,3840,3904,4369,8738],readHints [353806,0,1554,5183,8708,13328,354306,6152]),([6,15,3840,4096,4369,8738,17476,35064],readHints []),([6,15,3840,4096,4369,8946,17476,34952],readHints []),([6,15,3840,4336,4369,8738,17476,34952],readHints []),([6,15,3840,4369,4433,8738],readHints [354819,0,517,355332,14631,355854]),([6,15,3840,4369,8738,8802],readHints [356366,0,517,1042,356867,15368]),([6,15,3840,4369,8738,8946,17476,63624],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_118 : K_118.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_119 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,8738,17476,35064,61440],readHints []),([6,15,3840,4369,8738,17476,35064,61680],readHints []),([6,15,3840,4369,8738,17476,35064,61986],readHints []),([6,15,3840,4369,8738,17476,35064,62532],readHints []),([6,15,3840,4369,8738,17476,35064,63624],readHints []),([6,15,3840,4369,8738,17476,35064,63736],readHints []),([6,15,3840,4369,8738,17476,43770,61440],readHints []),([6,15,3840,4369,8738,17652,63624],readHints [61110,63642])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_119 : K_119.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_120 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,8738,51336],readHints [146952,0,517,1543,33315,6675,8714,147459,6153]),([6,15,3840,4369,8738,61568],readHints [97800,0,517,1097,1543,6675,30266,2564,3075]),([6,15,3840,4369,8738,63624],readHints [97800,0,517,1097,1543,6675,30266,3075]),([6,15,3840,4369,8738,63631],readHints [357384,1,517,1097,1543,6675,30266,3075,22051]),([6,15,3840,4369,8738,63897],readHints [357896,0,517,1033,1543,30219]),([6,15,3840,4369,8738,64170],readHints [358458,0,517,1097,21042,9731,12299]),([6,15,3840,4369,8738,64443],readHints [358923,0,517,1033,10768,17410,13326]),([6,15,3840,4369,8738,65416],readHints [359432,0,518,1097,1543,6675,30266])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_120 : K_120.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_121 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,8738,65423],readHints [359944,1,518,1097,1543,6675,30266,22038]),([6,15,3840,4369,8738,65471],readHints [360462,0,517,1042,10768,17410]),([6,15,3840,4369,8751,63624],readHints [360968,517,1196,1543,4190,6675,3075,7814]),([6,15,3840,4369,8802,17476],readHints [361483,0,517,1033,10768,9730,45582,3075,12312]),([6,15,3840,4369,8866,61440],readHints [97800,0,517,1037,1543,6675,30220,2564,3075]),([6,15,3840,4369,8946,17476],readHints [362005,26,557,1065,46082,45597,3123,12300]),([6,15,3840,4369,8946,17476,34952,61440],readHints []),([6,15,3840,4369,8946,17476,34952,61680],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_121 : K_121.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_122 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,8946,17476,34952,61986],readHints []),([6,15,3840,4369,8946,17476,34952,62194],readHints []),([6,15,3840,4369,8946,17476,34952,62532],readHints []),([6,15,3840,4369,8946,17476,34952,63624],readHints []),([6,15,3840,4369,8946,17476,35064,61440],readHints []),([6,15,3840,4369,8946,17476,36744,61440],readHints []),([6,15,3840,4369,8946,17476,43690,61440],readHints []),([6,15,3840,4369,8946,17476,43770,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_122 : K_122.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_123 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,8946,17476,52428,61440],readHints []),([6,15,3840,4369,8946,17476,61166,61440],readHints []),([6,15,3840,4369,8946,17476,61440,63624],readHints []),([6,15,3840,4369,8946,17476,63624],readHints []),([6,15,3840,4369,8946,17487],readHints [362525,557,1119,4300,46082,3123,12300]),([6,15,3840,4369,8946,20292],readHints [363029,26,1065,363560,147970,45597,12300]),([6,15,3840,4369,8946,20292,34952,61440],readHints []),([6,15,3840,4369,8946,21845],readHints [364044,26,557,1037,9731])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_123 : K_123.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_124 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,8946,43690],readHints [364556,26,557,1037,9731,12309]),([6,15,3840,4369,8946,48059],readHints [365077,26,557,1065,46082,45597]),([6,15,3840,4369,8959,17476],readHints [365570,0,557,1034,2564,3123,12300]),([6,15,3840,4369,13107,63624],readHints [366088,0,517,1034,1543,3075,7682]),([6,15,3840,4369,13299,17476],readHints [366594,0,517,1034,46595]),([6,15,3840,4369,17476,25122],readHints [367141,0,517,1033,2102,6727,5710,9290,6155,7176]),([6,15,3840,4369,17476,30471],readHints [98341,1,518,1034,1544,2102,5345,13831]),([6,15,3840,4369,17476,34952,35064,61986],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_124 : K_124.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_125 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,17476,35016],readHints [98358,0,517,1034,1832,2085,5213,3075,6146]),([6,15,3840,4369,17476,35064],readHints [98358,1,518,1034,1544,2085,5213,3089]),([6,15,3840,4369,17476,35064,61440,61986],readHints []),([6,15,3840,4369,17476,35064,61986],readHints [78350]),([6,15,3840,4369,17476,35071],readHints [367670,0,518,1034,1544,2085,5815,5213,3089]),([6,15,3840,4369,17476,39417],readHints [368182,25,544,1065,1544,2085,6882,5213]),([6,15,3840,4369,17476,51336],readHints [81927,0,517,1034,1544,5636,47106,3075]),([6,15,3840,4369,17476,56589],readHints [368661,26,557,1065,369181,5171,9740,13314,12443])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_125 : K_125.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_126 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,17476,61952],readHints [148517,0,2050,6727,5710,9290,2564,7352]),([6,15,3840,4369,17476,61986],readHints [148517,0,2059,6727,5710,9290,7176]),([6,15,3840,4369,17476,61999],readHints [369701,26,2064,6727,9290,7176]),([6,15,3840,4369,17476,62259],readHints [370213,0,2050,5710,9290,7176]),([6,15,3840,4369,17476,63488],readHints [81927,0,517,1034,1544,25092,8706,3075]),([6,15,3840,4369,17476,63624],readHints [81927,0,517,1034,1544,5636,8706,3075]),([6,15,3840,4369,17476,63631],readHints [370695,297,517,1034,1544,8706,3075]),([6,15,3840,4369,17476,63897],readHints [371207,0,517,1033,1544,5636,8715])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_126 : K_126.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_127 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,17487,35064],readHints [371766,518,1034,1544,2085,5213,2787,3089]),([6,15,3840,4369,17487,61986],readHints [372261,2062,6727,9290,24142,7176]),([6,15,3840,4369,17487,63624],readHints [372743,517,1034,1544,4281,24068,3075]),([6,15,3840,4369,19524,61440],readHints [81415,0,517,1034,1544,25092,8706,3075]),([6,15,3840,4369,20292,61986],readHints [373322,0,2059,76871,5930,7176]),([6,15,3840,4369,21845,35064],readHints [373814,1,518,1037,1544,2085,3089,6156]),([6,15,3840,4369,21845,61986],readHints [374309,0,2060,9290,7176]),([6,15,3840,4369,21845,63624],readHints [148999,0,517,1037,1544,6733,3075])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_127 : K_127.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_128 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,25122,34952],readHints [146952,0,517,1543,33315,6675,8714,147459,6153]),([6,15,3840,4369,26214,61986],readHints [374792,0,2059]),([6,15,3840,4369,30583,61986],readHints [375304,0,2098,6675]),([6,15,3840,4369,34952,61986],readHints [375816,0,10290,6675]),([6,15,3840,4369,34952,61999],readHints [376328,26,10327,6675,22051]),([6,15,3840,4369,34952,62259],readHints [376840,0,10242]),([6,15,3840,4369,34952,64170],readHints [377352,0,2098,6675]),([6,15,3840,4369,34952,64443],readHints [377864,0,2050,24250])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_128 : K_128.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_129 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,34959,61986],readHints [378376,10290,6675]),([6,15,3840,4369,35064,43690],readHints [378888,1,518,1037,2102,6675,8726,6156]),([6,15,3840,4369,35064,48059],readHints [379400,1,518,1034,2102,13917]),([6,15,3840,4369,36744,61986],readHints [379912,0,380466,76819]),([6,15,3840,4369,39321,61986],readHints [380936,0,10251]),([6,15,3840,4369,43690,61986],readHints [381477,0,2060,9290,7218]),([6,15,3840,4369,43690,63624],readHints [81928,0,517,1037,1543,6675,8716,3075]),([6,15,3840,4369,48059,61986],readHints [381989,0,10251,6727,17998,9290])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_129 : K_129.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_130 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,48059,63624],readHints [149000,0,517,1034,1543,18106,3075]),([6,15,3840,4369,52428,63624],readHints [81415,0,517,1034,1544,8706,3075]),([6,15,3840,4369,56797,63624],readHints [382471,0,517,1097,1544,6733,3075]),([6,15,3840,4369,61986,62532],readHints [383275,0,1547,6956,2564,15544,7688]),([6,15,3840,4369,61986,63078],readHints [383496,0,1547]),([6,15,3840,4369,61986,63624],readHints [384008,0,1620,6675,3075,7730]),([6,15,3840,4369,61986,64170],readHints [384562,0,517,1205,9731,12299]),([6,15,3840,4369,62532,63624],readHints [385031,0,1538,5636,3075])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_130 : K_130.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_131 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,63624,64170],readHints [385544,0,2106,6675,5123]),([6,15,3840,4369,63624,64716],readHints [386055,0,2050,5123]),([6,15,3840,4383,8738,17476,35064,61440],readHints []),([6,15,3840,4383,8946,17476,34952,61440],readHints []),([6,15,3840,4433,8738],readHints [149518,150019,67076]),([6,15,3840,4433,8738,17476],readHints [386571,0,517,1033,10768,17410,150542,3075,12312]),([6,15,3840,4433,8738,34952],readHints [151064,0,517,1052,10849,17410,98830,3075,12299]),([6,15,3840,4433,8738,61440],readHints [151566,0,517,1042,10768,17410,2564,46595])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_131 : K_131.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_132 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4433,17476,34952],readHints [387074,0,517,1034,26627,9752,12299]),([6,15,3840,4593,8738,17476,61713],readHints [47779,36580,40671,152088]),([6,15,3840,4593,8738,21845],readHints [387608,25,544,1052,388126,7210,7702]),([6,15,3840,4593,8738,30583],readHints [388630,25,544,1052,1578,6691,8728]),([6,15,3840,4593,8738,34952],readHints [389142,25,544,1052,1578,6691,32792,3102]),([6,15,3840,4593,8738,34959],readHints [389654,544,1052,1578,6691,5748,30232,3102]),([6,15,3840,4593,8738,36744],readHints [390166,25,1052,1578,390713,6691,391192]),([6,15,3840,4593,8738,43690],readHints [391704,25,544,1052,9758])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_132 : K_132.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_133 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4593,8751,34952],readHints [392214,544,1132,1578,4190,6691,2861,3102,48225]),([6,15,3840,4593,21845,34952],readHints [392746,25,544,1052,1558,6809,393240,3102]),([6,15,3840,4593,34952,43690],readHints [393750,25,544,1052,2090,6691,6168]),([6,15,3840,4593,34952,56797],readHints [394282,25,544,1052,2070,6809,22040]),([6,15,3840,6417,17476,61440],readHints [81415,0,517,1034,1544,25092,8706,3075]),([6,15,3840,7953,8738,63624],readHints [394771,0,1097,1613,5223,30266]),([6,15,3840,7953,8946,17476],readHints [395285,26,1065,10754,45597,12300]),([6,15,3840,7953,8946,17476,34952,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_133 : K_133.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_134 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,7953,17476,61986],readHints [395847,0,34315,5776,7176]),([6,15,3840,7953,34952,61986],readHints [396307,0,10290,3175]),([6,15,3840,8177,8738,34952],readHints [396835,25,517,1052,1689,32792,28818,3075]),([6,15,3840,8738,13107,63624],readHints [397370,0,517,1026,1609,3075,7691]),([6,15,3840,8738,13299,34952],readHints [397848,0,517,1026,1564,18577,3075,6154]),([6,15,3840,8738,16388,34952],readHints [99337,0,517,1026,1560,2059,3075,6154,7196]),([6,15,3840,8738,17412,34952],readHints [99337,0,517,1026,1560,2059,3075,6154,7196]),([6,15,3840,8738,17476,20753],readHints [398347,0,517,1838,2057,14352,152578,5860,10766,10031])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_134 : K_134.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_135 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,8738,17476,35016],readHints [398857,0,517,1026,1560,2059,3075,6154]),([6,15,3840,8738,17476,51336],readHints [399369,0,517,1026,2059,5936,3075,82442]),([6,15,3840,8738,34952,39417],readHints [399896,25,544,1066,400393,14433,8726]),([6,15,3840,8738,34952,48123],readHints [400920,0,517,1026,2057,13969]),([6,15,3840,8738,34952,60942],readHints [401436,25,544,10262,14444]),([6,15,3840,8738,52428,63624],readHints [401993,0,517,1026,1594,402442,3075]),([6,15,3840,8738,61166,63624],readHints [403017,0,517,99848,14508,3075]),([6,15,3840,8802,17476,34952],readHints [403465,0,517,1026,1560,2059,3075,6154,7196])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_135 : K_135.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_136 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,8946,17476,21845],readHints [403989,26,557,1548,2089,14338,9741]),([6,15,3840,8946,17476,43690],readHints [404521,26,557,1548,2069,14346,7181]),([6,15,3840,8946,17476,61166],readHints [405033,26,557,2069,14346,53343,22108]),([6,15,3840,13107,21845,61440],readHints [153090,0,517,1113,1546,2564,3075]),([6,15,3840,13107,26214,61440],readHints [153098,0,517,1033,1538,2564,3075]),([6,15,3840,13107,39321,61440],readHints [153602,0,517,1033,1546,2564,3075,7691]),([6,15,3840,13107,43690,61440],readHints [153610,0,517,1113,1538,2564,3075,7902]),([6,15,3840,17476,20753,34952],readHints [405506,0,517,1329,1546,3075,6450,7691])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_136 : K_136.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_137 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,17476,21845,35064],readHints [406070,1,518,1036,1546,2085,11869,3089,6157]),([6,15,3840,17476,21845,61986],readHints [406565,0,2059,4174,9287]),([6,15,3840,17476,21845,63624],readHints [407042,0,517,1036,1546,3075]),([6,15,3840,17476,25122,34952],readHints [407561,0,517,1538,2059,3075,82442]),([6,15,3840,17476,35064,43690],readHints [408074,1,518,1036,2102,47117]),([6,15,3840,17476,35064,61166],readHints [408586,1,518,2102,33970]),([6,15,3840,17476,43690,61986],readHints [409125,0,2057,4174,9287]),([6,15,3840,17476,43690,63624],readHints [409610,0,517,1036,1538,8717,3075])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_137 : K_137.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_138 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,17476,61166,61986],readHints [410149,0,410633,4174,6730,9287,6152]),([6,15,3840,17476,61166,63624],readHints [411146,0,517,34823,3075]),([6,15,3840,21845,26214,61440],readHints [154125,0,517,1033,1548,2564,3075,53771]),([6,15,3840,21845,39321,61440],readHints [154124,0,517,1033,1549,2564,3075,7691]),([6,15,3840,21845,52428,61440],readHints [154713,0,517,1538,2564,3075]),([6,15,3840,26214,34952,61986],readHints [411656,0,66569,6675]),([6,15,3840,26214,43690,61440],readHints [412169,0,517,44557,2564,3075]),([6,15,3840,26214,52428,61440],readHints [154633,0,517,1546,2564,3075])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_138 : K_138.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_139 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,34952,39321,61986],readHints [412680,0,2098,9235]),([6,15,3840,34952,61166,61986],readHints [413192,0,20149,9235]),([6,15,3840,39321,43690,61440],readHints [413705,0,517,44556,2564,3075]),([6,15,3840,39321,52428,61440],readHints [155145,0,517,1538,2564,3075]),([6,15,3840,43690,52428,61440],readHints [155225,0,517,1546,2564,3075]),([6,15,3855,4369,8738,17476,35064,61440],readHints []),([6,15,3855,4369,8738,63624],readHints [414216,517,1097,1543,54842,3075]),([6,15,3855,4369,8946,17476],readHints [414741,557,1065,4403,46082,415261,3123,12300])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_139 : K_139.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_140 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3855,4369,8946,17476,34952,61440],readHints []),([6,15,3855,4369,17476,35064],readHints [415798,518,1034,1544,2085,5213,3089]),([6,15,3855,4369,17476,61986],readHints [416293,67595,9290,7176]),([6,15,3855,4369,17476,63624],readHints [416775,517,1034,1544,8706,3075]),([6,15,3855,4369,34952,61986],readHints [417288,48690]),([6,15,3855,4593,8738,34952],readHints [417814,544,1052,1578,100376,3102]),([6,15,3968,4369,8738,61440],readHints [418363,0,517,1037,1597,30220,2564,3075]),([6,15,4080,4369,8738,36744],readHints [418819,1,1037,1597,2053,6712,41019,6156])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_140 : K_140.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_141 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4080,4369,17476,35064],readHints [419333,1,518,1034,1544,2051,3089,40967]),([6,15,4080,8738,17476,36744],readHints [419849,1,1026,1548,2059,3128,7181]),([6,15,4095,4369,8738,36744],readHints [420355,0,1037,1597,2053,41019,6156]),([6,15,4095,4369,17476,35064],readHints [420869,518,1034,1544,2051,4144,3089,40967]),([6,15,4095,8738,17476,36744],readHints [421385,0,1026,1548,2059,5723,7181]),([6,15,4369,4593,8738,20292],readHints [421951,25,820,2189,155728,22027]),([6,15,4369,4593,8738,36744],readHints [422430,25,1543,2080,422969,47107,3080]),([6,15,4369,7953,8738,17476,35064,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_141 : K_141.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_142 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,7953,8946,17476,34952,61440],readHints []),([6,15,4369,7953,8946,17476,61440],readHints [101051,423445,36440,40551,44044]),([6,15,4369,8738,8946,17476,36744,61440],readHints []),([6,15,4369,8738,8946,20292],readHints [423989,26,521,2079,156200,9279,424459]),([6,15,4369,8738,8946,20292,34952,61440],readHints []),([6,15,4369,8738,8946,36744],readHints [425045,26,525,1085,2227,5176,79875,3084]),([6,15,4369,8738,16384,36744],readHints [425475,0,1085,2053,62520,3081,7227]),([6,15,4369,8738,17476,20224],readHints [425987,0,521,2053,5665,156683,2564,22018])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_142 : K_142.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_143 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,8738,17476,20292,35064,61440],readHints []),([6,15,4369,8738,17476,35064,36744,61440],readHints []),([6,15,4369,8738,20224,34952],readHints [426499,0,1031,1541,5636,5139,3081,48136]),([6,15,4369,8738,20292,65280],readHints [427061,0,521,1567,25092,101387,97320,15423]),([6,15,4369,8738,20292,65295],readHints [427573,1,521,1567,101387,97320,15423]),([6,15,4369,8738,28791,61440],readHints [428037,0,525,1085,1539,18611,2564,6203]),([6,15,4369,8738,35064,36744],readHints [428596,1,525,1031,2082,26636,9246,9813,7171]),([6,15,4369,8738,35064,63624],readHints [429087,10245,12886,4111,5196,6152])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_143 : K_143.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_144 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,8738,36744,36856],readHints [429571,1,525,1085,1541,26636]),([6,15,4369,8738,36744,61440],readHints [157187,0,525,1085,1541,5132,2564,6203,7697]),([6,15,4369,8738,36744,61455],readHints [430083,1,525,1085,1541,5132,13880,6203,7697]),([6,15,4369,8738,36744,61713],readHints [430595,0,1085,1541,92219,7710]),([6,15,4369,8738,36744,61986],readHints [431107,0,525,1541,5132,24626,7731]),([6,15,4369,8738,36744,63624],readHints [157187,0,525,1031,1541,5132,6152,7697]),([6,15,4369,8738,36744,65280],readHints [431668,0,525,1031,1570,5132,2564,15390,12373,7697]),([6,15,4369,8738,36744,65295],readHints [432180,1,525,1031,1570,5132,15390,13881,12373,7697])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_144 : K_144.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_145 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,8738,36744,65416],readHints [432657,0,525,1085,1542,5132,15390,12339]),([6,15,4369,8738,36751,61440],readHints [433155,525,1085,1541,12855,4123,6203,7697]),([6,15,4369,8738,61440,65416],readHints [433667,0,2054]),([6,15,4369,8738,61440,65423],readHints [434179,2054,12855,4123,13880]),([6,15,4369,8738,61680,63624],readHints [434693,34824,12848,4119,5632]),([6,15,4369,8738,61695,63624],readHints [435205,0,34824,18661]),([6,15,4369,8738,62532,65280],readHints [435715,0,2082,5665,2564,22086]),([6,15,4369,8738,62532,65295],readHints [436227,2082,12855,4123,22086])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_145 : K_145.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_146 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,8738,63624,63736],readHints [436741,82952,12848,4119]),([6,15,4369,8738,63624,65280],readHints [437251,0,2079,2564]),([6,15,4369,8738,63624,65295],readHints [437763,2079,12855,4123,14054]),([6,15,4369,8738,63624,65416],readHints [438275,0,2054]),([6,15,4369,8751,36744,61440],readHints [438787,577,1085,1541,5863,5182,6203,7697]),([6,15,4369,8946,17476,20292],readHints [439347,26,553,2093,6659,439848,156693,22018]),([6,15,4369,8946,17476,20292,34952,61440],readHints []),([6,15,4369,8946,17476,61680],readHints [440365,2069,13109,4284,6661,2586])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_146 : K_146.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_147 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,8946,17476,61695],readHints [440877,26,157717,6661]),([6,15,4369,8946,20292],readHints [158248,441365,441979]),([6,15,4369,8946,20292,34952],readHints [442408,26,1615,442947,6736,39530,24578,3081,7803]),([6,15,4369,8946,20292,34952,61440],readHints [443432]),([6,15,4369,8946,20292,61440],readHints [158741,553,101890,6736,53277,9228,2561,55336,7478,7991]),([6,15,4369,12066,17652,34952,61440],readHints [152218]),([6,15,4369,13107,36744,61440],readHints [443907,0,522,1085,1541,2564,6203,7697]),([6,15,4369,17476,20224,34952],readHints [444419,0,522,1032,1541,4129,138242,49159,5636])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_147 : K_147.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_148 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,17476,20292,35064],readHints [445021,1,522,1336,1542,2273,7185,53763]),([6,15,4369,17476,30471,61440],readHints [445446,96259,12820,2561,6151]),([6,15,4369,17476,35064,36744],readHints [445969,1,522,1032,446777]),([6,15,4369,17476,35064,36856],readHints [446993,1,522,1032,2053]),([6,15,4369,17476,35064,61440],readHints [102406,10245,12820,2561,6151]),([6,15,4369,17476,35064,61455],readHints [159238,1,10245,6151]),([6,15,4369,17476,35064,61680],readHints [102406,2102,12820,9248,2561]),([6,15,4369,17476,35064,61695],readHints [159238,1,2102,9248])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_148 : K_148.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_149 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,17476,35064,62532],readHints [447494,2053,12820,24681]),([6,15,4369,17476,35064,63624],readHints [102406,10245,12820,6151]),([6,15,4369,17476,35064,63736],readHints [448006,2055,12820,9248,28677]),([6,15,4369,17476,35071,61440],readHints [448518,0,10245,2564,6151]),([6,15,4369,17476,36744,63624],readHints [449027,0,522,1032,1541,4129,6151]),([6,15,4369,17476,61440,63736],readHints [449541,2055,12848]),([6,15,4369,17476,61440,63743],readHints [450053,0,2055,4142]),([6,15,4369,17476,61680,61986],readHints [450597,2053,24650,2583,6152])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_149 : K_149.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_150 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,17476,61680,63624],readHints [451077,34823,12848,5632]),([6,15,4369,17476,61695,61986],readHints [451621,0,2053,4174,18503,24650,6152]),([6,15,4369,17476,61695,63624],readHints [452101,0,34823,4142]),([6,15,4369,17476,63624,63736],readHints [452613,82951,12848]),([6,15,4369,17476,63624,65280],readHints [159747,0,2091,4129,2564]),([6,15,4369,17476,63624,65295],readHints [453123,2091,12855]),([6,15,4369,17476,63624,65416],readHints [159747,0,2362,4129]),([6,15,4369,17487,35064,61440],readHints [453638,48645,6151])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_150 : K_150.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_151 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,21845,35064,61440],readHints [454150,10245,12820,2561,6151]),([6,15,4369,34952,35064,62532],readHints [454663,2053]),([6,15,4369,34952,36744,61986],readHints [455176,0,2051,5139,22075]),([6,15,4369,34952,61680,61986],readHints [455688,160261,2583]),([6,15,4369,34952,61695,61986],readHints [456200,0,160261,18451]),([6,15,4369,34952,62532,65280],readHints [456707,0,2055,5665,2564]),([6,15,4369,34952,62532,65295],readHints [457219,2055,12855]),([6,15,4369,35064,43690,61440],readHints [457734,10248,12820,2561,6149])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_151 : K_151.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_152 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4369,35064,48059,61440],readHints [458246,96264,12820,2561,6149]),([6,15,4369,35064,61440,62532],readHints [458759,82949]),([6,15,4369,36744,52428,61440],readHints [459325,0,522,34819,5122,2564]),([6,15,4369,36744,56797,61440],readHints [459837,0,525,34819,2564]),([6,15,4369,36744,61440,61986],readHints [460347,0,82947]),([6,15,4593,8738,17476,36744],readHints [460857,25,1339,2144,461321,11832,7190]),([6,15,4593,8738,34952,36744],readHints [461854,25,540,1066,2080,11779,462393,26648,462870]),([6,15,4593,8738,34952,61680],readHints [463392,2070,13116,4162,11781,2585])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_152 : K_152.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_153 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,4593,8738,34952,61695],readHints [463904,25,2070,11781,13859]),([6,15,4593,8738,36744],readHints [158265,464406,160792]),([6,15,4593,8738,36744,61440],readHints [464918,215,525,1066,54447,11832,52748,102969,7400,7781]),([6,15,4593,12066,17476,34952,61440],readHints [103741]),([6,15,7953,8738,8946,17476,34952,61440],readHints []),([6,15,7953,8738,20292,61440],readHints [465471,0,521,1677,466000,25092]),([6,15,7953,8738,36744,61440],readHints [466451,0,525,1101,11779,466956,9831,2564]),([6,15,7953,8946,17476,34952,61440],readHints [47704])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_153 : K_153.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_154 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,7953,8946,17476,61440],readHints [158741,553,14338,37420,161436,5720,53277,9228,2561,7486,7999]),([6,15,8738,8946,17476,36744],readHints [467465,26,655,1548,2059,6200,7181]),([6,15,8738,8946,20292,34952],readHints [467977,26,1600,2059,468547]),([6,15,8738,13107,36744,61440],readHints [468995,0,514,1037,1541,8716,2564,7697]),([6,15,8738,16384,17476,36744],readHints [469513,0,514,2059,5723,82442]),([6,15,8738,17476,20224,34952],readHints [470025,0,514,1541,2059,3082,82435]),([6,15,8738,17476,28791,61440],readHints [470539,0,514,1036,1545,4329,2564]),([6,15,8738,17476,35064,36744],readHints [471097,1,514,1036,2144,53257,79928,47117])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_154 : K_154.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_155 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,8738,17476,35064,63624],readHints [471628,2053,12815,10761]),([6,15,8738,17476,36744,36856],readHints [472120,1,514,1036,1678,47117,55817]),([6,15,8738,17476,36744,61440],readHints [472585,0,514,1036,1547,4187,8717,2564,7781]),([6,15,8738,17476,36744,61455],readHints [473097,1,514,1036,1547,8717,7787]),([6,15,8738,17476,36744,61713],readHints [473603,0,832,1541,4129,9025,13434,23561]),([6,15,8738,17476,36744,61986],readHints [474121,0,834,1036,1547,19133,4187,8717,7914]),([6,15,8738,17476,36744,63624],readHints [474627,0,514,1036,1541,4129,10909,8717,13434,29193,7781]),([6,15,8738,17476,36744,65280],readHints [475145,0,514,1036,1547,8717,2564,7781])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_155 : K_155.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_156 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,8738,17476,36744,65295],readHints [475657,1,514,1036,1547,8717,7787]),([6,15,8738,17476,36744,65416],readHints [476261,0,514,1036,1768,10909,8717,13419,15594,29193]),([6,15,8738,17652,36744,61440],readHints [476681,514,1036,1547,4165,36865,8717,7697]),([6,15,8738,20292,34952,35064],readHints [477251,1,514,1088,5130,55817]),([6,15,8738,20292,34952,65280],readHints [477705,0,514,1088,1547,5130,30275,2564]),([6,15,8738,20292,34952,65295],readHints [478217,1,514,1088,1547,5130,8771,7787]),([6,15,8738,20292,36744,61440],readHints [478729,0,514,1036,1547,4331,30221,2564]),([6,15,8738,26214,36744,61440],readHints [479241,0,519,1036,1547,8717,2564,3080,7781])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_156 : K_156.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_157 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,8738,36744,39321,61440],readHints [479756,0,519,44553,19006,26632,2564]),([6,15,8738,36744,40857,61440],readHints [480268,0,573,480777,19006,2564,3131]),([6,15,8738,36744,48059,61440],readHints [481292,0,514,44553,18011,2564]),([6,15,8738,36744,52428,61440],readHints [481805,0,514,99843,5130,2564]),([6,15,8738,36744,53196,61440],readHints [482317,0,514,1548,2564,53770]),([6,15,8738,36744,61166,61440],readHints [482829,0,99843,19009,2564,3131]),([6,15,17476,21845,35064,61440],readHints [483334,10245,2561]),([6,15,17476,26214,36744,61440],readHints [483849,0,520,1026,1547,12891,2564,3079,7781])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_157 : K_157.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_158 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,17476,35064,43690,61440],readHints [484358,2058,2561,6149]),([6,15,17476,35064,61166,61440],readHints [484870,2058,17940,2561,3079,6149]),([6,15,17476,36744,39321,61440],readHints [485378,0,520,44553,26631,2564]),([6,15,17476,36744,56797,61440],readHints [485890,0,1545,2564]),([6,64,79,3840,4369,8738],readHints [486414,512,1029,1554,5635,15376,23554]),([6,64,240,4369,8751,61440],readHints [486927,539,67600,487425,3095]),([6,64,240,7953,8738,61440],readHints [487937,516,48654,3072]),([6,64,3840,3855,4369,8738],readHints [488462,1024,1554,488964,68098,29213])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_158 : K_158.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_159 : List (List ℕ × List (ℕ × ℕ)) := [([6,64,3840,4369,8738,61680],readHints [489472,2062,3077,7197]),([6,64,3840,4369,8738,65520],readHints [489984,2062,33903]),([6,79,240,3840,4369,8738],readHints [490510,1,1030,1554,5443,18490,13328,15389,23554]),([6,79,240,4369,8738,61440],readHints [491014,515,10254,4116,5647,2561,3077]),([6,79,3840,4369,8738],readHints [149518,150019,67076]),([6,79,3840,4369,8738,17476],readHints [491531,0,517,1033,10768,17410,150542,3075,12312]),([6,79,3840,4369,8738,34952],readHints [151064,0,517,1052,10849,17410,98830,3075,12299]),([6,79,3840,4369,8738,61440],readHints [151566,0,517,1042,10768,17410,2564,46595])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_159 : K_159.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_160 : List (List ℕ × List (ℕ × ℕ)) := [([6,79,3840,4369,17476,34952],readHints [492034,0,517,1034,26627,9752,12299]),([6,79,3840,8738,17476,34952],readHints [99337,0,517,1026,1560,2059,3075,6154,7196]),([6,128,240,4369,8751,61440],readHints [492559,539,48676,9729,3095]),([6,128,240,7953,8738,61440],readHints [493057,516,48700,3072]),([6,143,240,3840,4369,8738],readHints [493576,49,836,1030,1549,2055,9238,9747,3397,7180]),([6,143,240,4369,8738,61440],readHints [494086,171,748,10248,4116,5647,2730,3309]),([6,176,3840,4369,8738,61440],readHints [161793,4,10254,2560,3078]),([6,240,255,4369,8738,20292],readHints [494645,4,513,1033,2079,495144,2560,6155])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_160 : K_160.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_161 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,255,4369,8738,36744],readHints [495668,4,513,1037,1543,2082,14393,6156]),([6,240,255,4369,8738,62532],readHints [496162,4,2059,162374,5169,2560,7175]),([6,240,255,4369,8738,63624],readHints [496671,4,10248,14412,11862,5135]),([6,240,255,4369,17476,63624],readHints [497195,4,10247,11858]),([6,240,255,4369,34952,62532],readHints [497671,4,10242,2560]),([6,240,255,8738,17476,36744],readHints [498185,4,513,1026,1548,2059,7181]),([6,240,255,8738,20292,34952],readHints [498697,4,513,1026,1600,2059,6154,7235]),([6,240,512,4369,4383,17476,61440],readHints [40076])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_161 : K_161.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_162 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,512,4383,8738,17476,34952,61440],readHints []),([6,240,512,7953,17476,61440],readHints [499201,4,34306,2560,7300]),([6,240,527,3840,4369,17476],readHints [499714,513,1546,5734,7692]),([6,240,527,4369,8738,17476,34952,61440],readHints []),([6,240,527,4369,17476,61440],readHints [500226,1034,9740,3073]),([6,240,2063,3840,4369,17476],readHints [500743,750,1350,1546,2056,501250,6471]),([6,240,3072,4369,17476,61440],readHints [162817,4,68610,2560]),([6,240,3328,4369,17476,61440],readHints [162817,4,68610,2560])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_162 : K_162.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_163 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,3840,4096,4383,8738,17476,34952],readHints []),([6,240,3840,4369,4383,8738,17476,63624],readHints []),([6,240,3840,4369,4383,8738,34952,62532],readHints []),([6,240,3840,4369,4383,8738,62532],readHints []),([6,240,3840,4369,4383,17476,34952,61986],readHints []),([6,240,3840,4369,4383,17476,61986],readHints [40086]),([6,240,3840,4369,8738,61504],readHints [501809,4,2062,502381,3078]),([6,240,3840,4369,8738,61568],readHints [502785,4,10248,2560,3078])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_163 : K_163.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_164 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,3840,4369,8751,17487],readHints [503312,518,1063,4126,10754,9803,3089,12616]),([6,240,3840,4369,8751,34959],readHints [503938,518,1089,1865,2097,14452,25219,3089]),([6,240,3840,4369,8866,61440],readHints [504321,4,10248,2560,3078]),([6,240,3840,4369,17476,61952],readHints [163566,4,2050,6986,83787,2560,7335]),([6,240,3840,4369,17476,63488],readHints [163329,4,10247,18530,2560,3115]),([6,240,3840,4369,17487,34959],readHints [505041,518,1034,1868,2216,5289,2799,3089]),([6,240,3840,4369,19524,61440],readHints [163841,4,10247,2560,3078]),([6,240,3840,4369,61986,62532],readHints [505393,4,2381,10861,2560])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_164 : K_164.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_165 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,3840,4369,61986,63624],readHints [506190,4,77908,6991,9729]),([6,240,3840,4369,62532,63624],readHints [506704,4,1538,5632,10065]),([6,240,3840,4383,8738,17476,34952,61440],readHints []),([6,240,3840,4383,8738,17476,34952,61680],readHints []),([6,240,3840,4383,8738,17476,34952,61986],readHints []),([6,240,3840,4383,8738,17476,34952,62532],readHints []),([6,240,3840,4383,8738,17476,34952,63624],readHints []),([6,240,3840,4383,8738,17476,35064,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_165 : K_165.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_166 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,3840,4383,8738,17476,43690,61440],readHints []),([6,240,3840,4383,8738,17476,52428,61440],readHints []),([6,240,3840,4383,8738,17476,61166,61440],readHints []),([6,240,3840,4383,8738,17476,61440,63624],readHints []),([6,240,3840,4383,8738,17476,63624],readHints [36534]),([6,240,3840,4383,8738,34952,61440,62532],readHints []),([6,240,3840,4383,8738,34952,62532],readHints []),([6,240,3840,4383,8946,17476,34952,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_166 : K_166.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_167 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,3840,4383,17476,34952,61440,61986],readHints []),([6,240,3840,4383,17476,34952,61986],readHints [47954]),([6,240,3840,4433,8738,61440],readHints [161793,4,10254,2560,3078]),([6,240,3840,6417,17476,61440],readHints [163841,4,10247,2560,3078]),([6,240,3840,8738,17476,34959,61713],readHints []),([6,240,3840,8738,17487,34952,61713],readHints []),([6,240,3840,8751,17476,34952,61713],readHints [63827,40688]),([6,240,3840,13107,21845,61440],readHints [164353,4,2050,2560,3078])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_167 : K_167.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_168 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,3840,13107,26214,61440],readHints [164865,4,2058,2560,3078]),([6,240,3840,13107,39321,61440],readHints [164865,4,2050,2560,3078]),([6,240,3840,13107,43690,61440],readHints [164353,4,2058,2560,3078]),([6,240,3840,21845,26214,61440],readHints [165377,4,2061,2560,3078]),([6,240,3840,21845,39321,61440],readHints [165377,4,2060,2560,3078]),([6,240,3840,21845,52428,61440],readHints [165889,4,2137,2560,3078]),([6,240,3840,26214,43690,61440],readHints [166401,4,2057,2560,3078]),([6,240,3840,26214,52428,61440],readHints [166913,4,2057,2560,3078])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_168 : K_168.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_169 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,3840,39321,43690,61440],readHints [166401,4,2057,2560,3078]),([6,240,3840,39321,52428,61440],readHints [166913,4,2057,2560,3078]),([6,240,3840,43690,52428,61440],readHints [165889,4,2137,2560,3078]),([6,240,3841,4369,8738,17476,61440],readHints [39937]),([6,240,3855,4369,8751,17476],readHints [506896,527,1063,4243,61954,3176,12300,7716]),([6,240,3855,4369,8751,34952],readHints [507428,527,1089,1619,14448,167486,3176]),([6,240,3855,4383,8738,17476,34952,61440],readHints []),([6,240,3855,7953,8738,17476],readHints [507985,513,1160,4198,45155,28674,167950,12300,7175,7688])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_169 : K_169.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_170 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,3855,7953,8738,34952],readHints [508476,513,1037,1655,14456,54796]),([6,240,3904,4369,8738,61440],readHints [508929,4,682,10254,2560,3243]),([6,240,3968,4369,8738,61440],readHints [509441,4,10248,2560,3078]),([6,240,4095,4369,8751,17476],readHints [509968,27,527,1063,46082,3176,12300,7716]),([6,240,4095,4369,8751,34952],readHints [510500,27,527,1089,1619,14448,21106,2583,3176,48190]),([6,240,4095,7953,8738,17476],readHints [511057,4,513,1160,10851,28674,2560,69134,12300,7175,7688]),([6,240,4095,7953,8738,34952],readHints [511548,4,513,1037,1655,14456,21076,30220]),([6,240,4369,4383,8738,20292,61440],readHints [94721])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_170 : K_170.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_171 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,4369,4383,8738,62532],readHints [168482,55,2100,10822,8753,3120,7175]),([6,240,4369,4383,8738,63624],readHints [168534,55,68616,8705,2608]),([6,240,4369,4383,17476,63624],readHints [512082,55,68615,2608]),([6,240,4369,4383,34952,62532],readHints [512519,55,2056,32304]),([6,240,4369,8738,8751,62532],readHints [513073,27,2059,22032]),([6,240,4369,8738,8751,63624],readHints [513551,27,2183,9217,2583,22047]),([6,240,4369,8738,20292,65280],readHints [514049,4,2101,2560,22116]),([6,240,4369,8738,20292,65520],readHints [514561,2101,12825,4122,17920,22116])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_171 : K_171.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_172 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,4369,8738,36744,65280],readHints [515073,4,2100,2560]),([6,240,4369,8738,36744,65520],readHints [515585,2100,12825,4122,22174]),([6,240,4369,8738,62532,65280],readHints [516130,4,1547,516678,25088,8711,12337]),([6,240,4369,8738,62532,65520],readHints [517154,3,1547,14406,8711,12337]),([6,240,4369,8738,63624,65280],readHints [517663,4,23048,19020,2560,15446,12303]),([6,240,4369,8738,63624,65520],readHints [518175,3,23048,19020,5637,15446,12303]),([6,240,4369,8751,17476,36744,61440],readHints [101054,69872]),([6,240,4369,8751,17476,61440],readHints [518671,27,10256,49153,2583])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_172 : K_172.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_173 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,4369,8751,17476,61680],readHints [519183,2064,12866,4284,49153,17943]),([6,240,4369,8751,17476,62532],readHints [519695,27,2064,6657,53297]),([6,240,4369,8751,17487,61440],readHints [520198,3,20496,52239,2565]),([6,240,4369,8751,20292,61440],readHints [520720,340,551,12863,14338,521217,83471,9764,2751,169013,7360,8021]),([6,240,4369,8751,21845,61440],readHints [521743,27,2060,49153,2583,7360]),([6,240,4369,8751,26214,61440],readHints [522255,27,20516,6657,2583]),([6,240,4369,8751,26223,61440],readHints [522767,27,20516,2583]),([6,240,4369,8751,30583,61440],readHints [523279,27,20004,6657,2583])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_173 : K_173.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_174 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,4369,8751,34952,61440],readHints [523791,27,20516,6657,2583]),([6,240,4369,8751,34952,61680],readHints [524303,2084,12866,4284,6657]),([6,240,4369,8751,34952,63624],readHints [524815,27,2084,6657,2583]),([6,240,4369,8751,34959,61440],readHints [525318,3,20822,52239,2565]),([6,240,4369,8751,36744,61440],readHints [526048,577,1367,12975,19150,37569,6657,5976,83471,52798,29425,7362,8025]),([6,240,4369,8751,39321,61440],readHints [526351,27,20004,6657,2583,7362]),([6,240,4369,8751,43690,61440],readHints [526863,27,10252,49153,2583]),([6,240,4369,8751,43695,61440],readHints [527375,27,20542,2583])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_174 : K_174.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_175 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,4369,8751,48059,61440],readHints [527887,27,2064,49153,2583]),([6,240,4369,8751,61440,62532],readHints [528400,27,551,528898,529431,69135,15552,12324]),([6,240,4369,8751,61440,63624],readHints [529956,27,577,1107,19056,25111,169503,69135,15554,12350]),([6,240,4369,8959,17476,61440],readHints [530447,4,10242,49153,2560]),([6,240,4369,13119,17476,61440],readHints [530945,4,10242,2560]),([6,240,4369,13119,34952,61440],readHints [531457,4,532004,2560]),([6,240,4369,17476,56784,61440],readHints [532495,27,20496,9217,2583]),([6,240,4369,17476,61440,61999],readHints [532993,27,23056,5655,6180])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_175 : K_175.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_176 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,4369,17476,61440,62207],readHints [533505,4,23042,5632]),([6,240,4369,17476,63624,65280],readHints [534059,4,23047,2560,15442]),([6,240,4369,17476,63624,65520],readHints [534571,3,23047,5637,15442]),([6,240,4369,17487,34959,61440],readHints [535046,3,10409,2565,6490]),([6,240,4369,34952,56784,61440],readHints [535567,27,20563,9217,2583]),([6,240,4369,34952,61440,61999],readHints [536100,27,19969,19056,13997]),([6,240,4369,34952,62532,65280],readHints [536583,4,23042,25088]),([6,240,4369,34952,62532,65520],readHints [537095,3,23042])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_176 : K_176.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_177 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,4383,7953,8738,17476,34952,61440],readHints []),([6,240,4383,7953,8738,17476,61440],readHints [47803,40492,103574]),([6,240,4383,7967,8738,17476,34952,61440],readHints []),([6,240,4383,8738,17476,20292,34952,61440],readHints []),([6,240,4383,8738,17476,34952,36744,61440],readHints []),([6,240,4383,8738,17476,63624],readHints [537795,55,2198,18953,12123,32092,45238,538160]),([6,240,4383,8738,34952,62532],readHints [538820,55,2169,12125,32094,6151,7216]),([6,240,4593,8751,34952,61440],readHints [539151,539760])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_177 : K_177.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_178 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,7953,7967,8738,17476,61440],readHints [78849,540204]),([6,240,7953,8738,17476,61440],readHints [540673,4,20049,2560,7283]),([6,240,7953,8738,17476,61680],readHints [541185,2129,12825,4122,17920,6243]),([6,240,7953,8738,17487,61440],readHints [541784,169998,161429,170497,9260,9743]),([6,240,7953,8738,20292,61440],readHints [542209,4,20319,2560,7256]),([6,240,7953,8738,21845,61440],readHints [542721,4,19980,2560,7212]),([6,240,7953,8738,24405,61440],readHints [543233,4,19980,2560,7212]),([6,240,7953,8738,26214,61440],readHints [543745,4,19976,2560,7410])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_178 : K_178.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_179 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,7953,8738,30583,61440],readHints [544257,4,20028,2560]),([6,240,7953,8738,34952,61440],readHints [544769,4,20028,2560,7292]),([6,240,7953,8738,34952,61680],readHints [545281,2108,12825,4122]),([6,240,7953,8738,34959,61440],readHints [546035,236,19987,170497,9460,8949,9743,2797]),([6,240,7953,8738,36744,61440],readHints [546305,4,19987,2560,7520]),([6,240,7953,8738,39321,61440],readHints [546817,4,19976,2560,7305]),([6,240,7953,8738,40857,61440],readHints [547329,4,20028,2560,7305]),([6,240,7953,8738,43690,61440],readHints [547841,4,19980,2560,7414])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_179 : K_179.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_180 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,7953,8738,48059,61440],readHints [548353,4,20049,2560]),([6,240,7953,8738,61440,62532],readHints [548979,4,23121,31876,25088,9777,69121,15404,6151,12530]),([6,240,7953,8738,61440,63624],readHints [549500,4,171068,5632,69121,15497,12534]),([6,240,7953,8946,17476,61440],readHints [549889,170083,7283]),([6,240,7953,17476,26214,61440],readHints [550401,4,20487,2560]),([6,240,7953,17476,39321,61440],readHints [550913,4,19975,2560,7365]),([6,240,7953,17476,56797,61440],readHints [551425,4,2129,2560,6259,7212]),([6,240,7953,17476,61440,61986],readHints [552017,4,648,552448,33294,6668,9902,13411,40962,6152,12295])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_180 : K_180.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_181 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,7953,21845,34952,61440],readHints [552961,4,20599,2560]),([6,240,7953,34952,43690,61440],readHints [553473,4,20540,2560]),([6,240,7953,34952,56797,61440],readHints [553985,4,10359,2560,6268]),([6,240,7953,34952,61440,61986],readHints [554556,4,20052,19064,10081]),([6,240,8177,8738,34952,61440],readHints [555009,55,20088,2608,7292]),([6,240,8738,16179,17476,61440],readHints [555521,4,2129,2560,7283]),([6,240,8738,16179,34952,61440],readHints [556033,4,2060,2560,7292]),([6,240,8738,17476,36744,65280],readHints [556545,4,2057,2560])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_181 : K_181.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_182 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,8738,17476,36744,65520],readHints [557057,2057,12826,37376]),([6,240,8738,17476,57582,61440],readHints [557569,4,34440,2560,6259]),([6,240,8738,20292,34952,65280],readHints [558081,4,2057,2560]),([6,240,8738,20292,34952,65520],readHints [558593,2057,12826,37376]),([6,240,8738,20292,36744,61440],readHints [559105,4,2283,2560]),([6,240,8738,34952,57582,61440],readHints [559617,4,2061,2560,3132,6268]),([6,240,8751,17476,21845,61440],readHints [560143,27,2064,2583,3073]),([6,240,8751,17476,43690,61440],readHints [560655,27,2087,2583,3073])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_182 : K_182.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_183 : List (List ℕ × List (ℕ × ℕ)) := [([6,240,8751,17476,61166,61440],readHints [561167,27,20007,561665,2583]),([6,240,8751,26214,34952,61440],readHints [562191,27,2057,2583,3108]),([6,240,8751,34952,39321,61440],readHints [562703,27,2110,2583,3108]),([6,240,8751,34952,61166,61440],readHints [563215,27,20033,18433,2583,3108]),([6,255,3840,4369,8738,17487],readHints [563716,518,1042,2048,564238,3089,7240]),([6,255,3840,4369,17487,34952],readHints [564740,518,1034,1536,565250,26641]),([6,255,3840,8738,17652,34952],readHints [565829,1,518,1141,1669,2166,3089,6292]),([6,255,3855,4369,8738,17476],readHints [566283,512,1033,46082,21013,3076,15374,12300,7175,7688])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_183 : K_183.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_184 : List (List ℕ × List (ℕ × ℕ)) := [([6,255,3855,4369,8738,34952],readHints [566792,512,1037,1543,100364]),([6,255,3855,4369,17476,34952],readHints [567303,512,1034,1544,5124,32770]),([6,255,3855,8738,17476,34952],readHints [567817,512,1026,1548,2059,6154,7181]),([6,255,4080,4369,8738,17476],readHints [568331,68,516,1033,46082,21008,3072,40974,12300,7175,7688]),([6,255,4080,4369,8738,34952],readHints [568840,68,516,1037,1543,6691,21106,32780]),([6,255,4080,4369,17476,34952],readHints [569351,68,516,1034,1544,5120,171522]),([6,255,4080,8738,17476,34952],readHints [569865,68,516,1026,1548,2059,6154,7181]),([6,255,4369,8738,17476,61455],readHints [570372,68,2059,6391,7182])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_184 : K_184.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_185 : List (List ℕ × List (ℕ × ℕ)) := [([6,255,4369,8738,17476,61680],readHints [570880,2059,6165]),([6,255,4369,8738,17487,61440],readHints [571398,33,20484,2606]),([6,255,4369,8738,34952,61455],readHints [571908,68,20488,14071]),([6,255,4369,8738,34952,61680],readHints [572416,2056]),([6,255,4369,17476,34952,61455],readHints [572932,68,20487]),([6,255,4369,17476,34952,61680],readHints [573440,10247]),([6,255,4369,17487,34952,61440],readHints [573958,38,20484,2607]),([6,255,8738,17476,34952,61455],readHints [574468,68,2057])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_185 : K_185.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_186 : List (List ℕ × List (ℕ × ℕ)) := [([6,255,8738,17476,34952,61680],readHints [574976,2057]),([6,255,8738,17652,34952,61440],readHints [575494,2117,12815,2561]),([6,512,3840,4369,17487,61440],readHints [576004,1034,1536,5634]),([6,527,3840,4369,17476,61440],readHints [576514,0,1034,577028,9740]),([6,752,3840,4369,17476,61440],readHints [577537,4,760,10242,2560,3321]),([6,2048,3840,4369,17487,61440],readHints [578052,559,1034,1536,5634,3110]),([6,2063,3840,4369,17476,61440],readHints [578567,0,760,1034,1544,25092,8706,3321]),([6,2288,3840,4369,17476,61440],readHints [579073,4,10247,2560,3078])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_186 : K_186.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_187 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,3855,4369,8738,63624],readHints [579592,512,1097,1543,14355,54842]),([6,3840,3855,4369,8946,17476],readHints [580117,538,1065,4219,9730,172061,12300]),([6,3840,3855,4369,17476,35064],readHints [580662,513,1034,1544,2085]),([6,3840,3855,4369,17476,61986],readHints [581157,67595,14407,162378,5198,7176]),([6,3840,3855,4369,17476,63624],readHints [581639,512,1034,1544,5124,8706]),([6,3840,3855,4369,34952,61986],readHints [582152,48690,14355]),([6,3840,3855,4593,8738,34952],readHints [582678,537,1052,1578,14371,100376]),([6,3840,4095,4369,8738,17487],readHints [583172,46,1042,2048,583694,7240])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_187 : K_187.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_188 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4095,4369,17487,34952],readHints [584196,47,1034,1536,584706,2598]),([6,3840,4095,8738,17652,34952],readHints [585285,513,1141,1669,2166,6292]),([6,3840,4369,4383,8738,17476,35064,61440],readHints []),([6,3840,4369,4383,8946,17476,34952,61440],readHints []),([6,3840,4369,4383,8946,17476,61440],readHints [101051,44076]),([6,3840,4369,8738,16384,17487],readHints [585732,46,530,2048,5665,5134,6216]),([6,3840,4369,8738,17487,61440],readHints [586244,46,530,1536,8776,2593]),([6,3840,4369,8738,17487,61713],readHints [586756,46,1536,101409,8776])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_188 : K_188.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_189 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,8738,17487,61986],readHints [587268,46,530,1536,101966,53919]),([6,3840,4369,8738,17487,65280],readHints [587780,6,530,1536,5649,8776]),([6,3840,4369,8738,20303,61440],readHints [588292,530,1536,24686]),([6,3840,4369,8738,48048,61440],readHints [588800,46,530,1540,24687,2593,7694]),([6,3840,4369,8738,61440,62543],readHints [589316,172545,5665,6216]),([6,3840,4369,8738,61440,65359],readHints [589828,2049,22126]),([6,3840,4369,8738,61680,63624],readHints [590336,34824,5637]),([6,3840,4369,8738,63624,65520],readHints [590848,2056,22176])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_189 : K_189.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_190 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,8751,17487,61440],readHints [591376,5,551,60420,9354,8776,173059]),([6,3840,4369,8751,34959,61440],readHints [592003,5,577,1237,1890,6660,25091,48293]),([6,3840,4369,8946,17476,61680],readHints [592410,2069,6656,2605]),([6,3840,4369,8946,17476,65520],readHints [592922,2069,6656,22116]),([6,3840,4369,8946,17487,61440],readHints [593437,46,607,12888,593924,169516,2593,172155,7169]),([6,3840,4369,13107,17487,61440],readHints [594436,46,522,1536,2593]),([6,3840,4369,16384,17487,34952],readHints [594948,47,522,1536,54310,595458]),([6,3840,4369,17476,17487,61986],readHints [596046,93188,19088])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_190 : K_190.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_191 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,17476,17487,63624],readHints [596484,46,522,1536,11778,2593]),([6,3840,4369,17476,35064,61680],readHints [596993,2102,9241,2566]),([6,3840,4369,17476,35064,65520],readHints [597505,2102,9241]),([6,3840,4369,17476,61680,61986],readHints [598053,598528,19015,101962,6152]),([6,3840,4369,17476,61680,63624],readHints [599040,34823,5637]),([6,3840,4369,17476,61986,65520],readHints [599552,2085,33903]),([6,3840,4369,17476,63624,65520],readHints [600064,2055]),([6,3840,4369,17487,26214,61440],readHints [600580,47,521,1024,5131,9800,2598])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_191 : K_191.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_192 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,17487,26223,61440],readHints [601160,47,551,1379,6794,83460,2598]),([6,3840,4369,17487,30583,61440],readHints [601604,47,522,1024,2598]),([6,3840,4369,17487,34952,61440],readHints [602116,47,522,1024,25126,52738]),([6,3840,4369,17487,34952,61713],readHints [602628,47,1024,603174,29256]),([6,3840,4369,17487,34952,63624],readHints [603652,47,522,1024,25126,5122,56058]),([6,3840,4369,17487,34952,65280],readHints [604164,6,522,1024,141841,52738,7930]),([6,3840,4369,17487,34959,61440],readHints [604911,5,522,1380,25091,43524,9355,9730]),([6,3840,4369,17487,35064,61440],readHints [605411,522,1381,605845,6814,5990,52228,9414,2566,29435])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_192 : K_192.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_193 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,17487,39321,61440],readHints [606212,47,521,1024,9867,2598]),([6,3840,4369,17487,52428,61440],readHints [606724,46,522,1024,52738,2593]),([6,3840,4369,17487,52431,61440],readHints [607234,47,522,607782,43524,9355]),([6,3840,4369,17487,56797,61440],readHints [608260,46,530,1024,9867,2593]),([6,3840,4369,17487,61440,61986],readHints [608772,46,530,1024,5665,12360]),([6,3840,4369,17487,61440,63624],readHints [609284,47,522,1024,25126,12290]),([6,3840,4369,34952,48048,61440],readHints [609792,47,522,1540,2598,7682]),([6,3840,4369,34952,61440,62543],readHints [610308,173569,5670])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_193 : K_193.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_194 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,34952,61680,61986],readHints [610824,611328,18963]),([6,3840,4369,34952,61986,65520],readHints [611840,2056,33952]),([6,3840,4383,8738,8946,17476,34952,61440],readHints []),([6,3840,4383,8738,17476,34952,35064,61440],readHints []),([6,3840,4383,8738,17476,35064,61440],readHints []),([6,3840,4383,8946,17476,34952,61440],readHints []),([6,3840,4593,8738,17476,34959,61440],readHints []),([6,3840,4593,8738,34952,61680],readHints [612377,2070,11776,2592])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_194 : K_194.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_195 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4593,8738,34952,65520],readHints [612889,2070,11776,22230]),([6,3840,4593,8738,34959,61440],readHints [174102,525,1066,18979,4108,11780,9980,2566,613478,7169]),([6,3840,4593,8751,17476,34952,61440],readHints [36542]),([6,3840,4593,8751,34952,61440],readHints [174174,577,1383,19304,614104,614462,5822,2566,29401,7386,7899]),([6,3840,7953,8738,17487,61440],readHints [614916,530,1536,5646,8776]),([6,3840,8738,13107,17487,61440],readHints [615428,46,514,1042,1536,2593]),([6,3840,8738,17487,34952,61713],readHints [615940,46,1024,11848,616481,13826,29219,7689,33806]),([6,3840,8738,17487,52428,61440],readHints [616978,46,514,34820,5130,2593])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_195 : K_195.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_196 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,8738,17487,61166,61440],readHints [617490,46,34820,62474,11815,2593]),([6,3840,8738,17652,21845,61440],readHints [617985,34422,2566]),([6,3840,8738,17652,30583,61440],readHints [618497,2166,2566]),([6,3840,8738,17652,34952,61440],readHints [619009,2117,2566]),([6,3840,8738,17652,34952,65280],readHints [619521,2117]),([6,3840,8738,17652,36744,61440],readHints [620033,67653]),([6,3840,8738,17652,43690,61440],readHints [620545,34373,2566]),([6,3840,8738,20468,34952,61440],readHints [621057,361,2117,2922])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_196 : K_196.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_197 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,8738,34952,47883,61440],readHints [621569,2181,2566]),([6,3840,17487,26214,34952,61440],readHints [622089,47,512,1026,1547,25126,30218,3076]),([6,3840,17487,34952,39321,61440],readHints [622594,47,512,44553,2598,3076]),([6,3840,17487,34952,61166,61440],readHints [623114,47,623620,2598]),([6,3840,17652,21845,34952,61440],readHints [624129,10357,2566]),([6,3840,17652,34952,43690,61440],readHints [624641,20116,2566]),([6,3840,17652,34952,56797,61440],readHints [625153,2165,2566]),([6,3855,4080,4369,8738,17476],readHints [625675,66,602,1033,91389,43541,21008,9730,41486,12300,7175,7688])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_197 : K_197.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_198 : List (List ℕ × List (ℕ × ℕ)) := [([6,3855,4080,4369,8738,34952],readHints [626184,66,602,1037,1543,6691,5373,21106,32780]),([6,3855,4080,4369,17476,34952],readHints [626695,66,602,1034,1544,171522]),([6,3855,4080,8738,17476,34952],readHints [627209,66,602,1026,1548,2059,6154,7181]),([6,3855,4369,8738,17476,61455],readHints [627802,66,2059,6160]),([6,3855,4369,8738,17476,65280],readHints [628235,0,521,33301,628738,629252,10766,9228,8711,9736]),([6,3855,4369,8738,34952,61455],readHints [629850,66,20488,14187]),([6,3855,4369,8738,34952,65280],readHints [630280,0,525,1031,630796]),([6,3855,4369,8751,17476,61440],readHints [631312,23,551,60418,9228,9764,173083])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_198 : K_198.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_199 : List (List ℕ × List (ℕ × ℕ)) := [([6,3855,4369,8751,34952,61440],readHints [631844,23,577,1107,25115,632382]),([6,3855,4369,17476,34952,61455],readHints [632922,66,20487]),([6,3855,4369,17476,34952,65280],readHints [633351,0,522,1032,4100,633858]),([6,3855,7953,8738,17476,61440],readHints [634449,0,648,33379,31746,634884,10766,9228,8711,9736]),([6,3855,7953,8738,34952,61440],readHints [635452,0,525,1143,635916,2564]),([6,3855,8738,17476,34952,61455],readHints [636506,66,93193]),([6,3855,8738,17476,34952,65280],readHints [636937,0,514,1036,1547,5130,8717]),([6,4080,4369,8738,17476,61680],readHints [637506,2059,12825,4119,6165])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_199 : K_199.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_200 : List (List ℕ × List (ℕ × ℕ)) := [([6,4080,4369,8738,17476,65280],readHints [638020,10251,22116]),([6,4080,4369,8738,34952,61680],readHints [638530,2056,12825,4119]),([6,4080,4369,8738,34952,65280],readHints [639044,10248]),([6,4080,4369,8738,36744,61440],readHints [639489,4,10243,2560,6203]),([6,4080,4369,17476,34952,61680],readHints [640066,10247,12825]),([6,4080,4369,17476,34952,65280],readHints [640580,2055]),([6,4080,4369,17476,35064,61440],readHints [641025,10245,2566,6151]),([6,4080,8738,17476,34952,61680],readHints [641602,2057,12823])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_200 : K_200.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_201 : List (List ℕ × List (ℕ × ℕ)) := [([6,4080,8738,17476,34952,65280],readHints [642116,2057]),([6,4080,8738,17476,36744,61440],readHints [642561,4,2057,2560]),([6,4369,4383,17476,35064,61440],readHints [643092,48688,3073,6151]),([6,4369,8738,17476,61455,61680],readHints [643650,644186]),([6,4369,8738,17476,61455,65280],readHints [644676,19972,13924]),([6,4369,8738,17476,61680,65280],readHints [645120,1547,5141]),([6,4369,8738,17487,61440,61695],readHints [645678,646148,11823,22021]),([6,4369,8738,17487,61440,65280],readHints [646689,157702,11814,6148])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_201 : K_201.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_202 : List (List ℕ × List (ℕ × ℕ)) := [([6,4369,8738,34952,61455,61680],readHints [647234,647770,5128]),([6,4369,8738,34952,61455,65280],readHints [648260,19972]),([6,4369,8738,34952,61680,65280],readHints [648704,1544]),([6,4369,8738,36744,61440,61455],readHints [649220,649729,26683,47107]),([6,4369,8738,36744,61440,65520],readHints [650240,2051,13984]),([6,4369,8751,17476,61440,61680],readHints [650775,2064,651264]),([6,4369,8751,17476,61440,65295],readHints [651803,652303,18948]),([6,4369,8751,34952,35064,61440],readHints [652815,10263,18945,3108,6398])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_202 : K_202.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_203 : List (List ℕ × List (ℕ × ℕ)) := [([6,4369,8751,34952,61440,61680],readHints [653335,174628,18944]),([6,4369,8751,34952,61440,65295],readHints [653851,19983,18948,24428]),([6,4369,12066,17652,34952,61440],readHints [654337,20480,2815,3087]),([6,4369,17476,34952,61455,61680],readHints [654914,173658,5127]),([6,4369,17476,34952,61455,65280],readHints [655428,2052]),([6,4369,17476,34952,61680,65280],readHints [655872,23047]),([6,4369,17476,35064,61440,61455],readHints [656385,171013,26631]),([6,4369,17476,35064,61440,65520],readHints [656902,23045,5127,13332])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_203 : K_203.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_204 : List (List ℕ × List (ℕ × ℕ)) := [([6,4369,17487,34952,36744,61440],readHints [657446,10,512,658285,4098,3076,7697]),([6,4369,17487,34952,61440,61695],readHints [658479,658948]),([6,4369,17487,34952,61440,65280],readHints [659494,2054]),([6,4383,8738,17476,35064,61440],readHints [659988,660846,660993]),([6,7953,8738,17476,17652,61440],readHints [661505,68608,6511]),([6,7953,8738,17476,61440,61680],readHints [662016,2129,3171]),([6,7953,8738,17476,61440,65295],readHints [662532,19969,14022]),([6,7953,8738,34952,61440,61680],readHints [663040,174652])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_204 : K_204.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_205 : List (List ℕ × List (ℕ × ℕ)) := [([6,7953,8738,34952,61440,65295],readHints [663556,664065]),([6,8738,12066,17652,34952,61440],readHints [664577,67653,3087]),([6,8738,17476,17487,36744,61440],readHints [665179,2,880,1024,1769,3441,6148,7781]),([6,8738,17476,34952,61455,61680],readHints [665666,172634]),([6,8738,17476,34952,61455,65280],readHints [666180,2052]),([6,8738,17476,34952,61680,65280],readHints [666624,1545]),([6,8738,17476,36744,61440,61455],readHints [667140,2049]),([6,8738,17476,36744,61440,65520],readHints [667648,2057])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_205 : K_205.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_206 : List (List ℕ × List (ℕ × ℕ)) := [([6,8738,17652,34952,61440,61695],readHints [668161,1605]),([6,8738,17652,34952,61440,65280],readHints [668678,1605,13327]),([7,1,240,3840,4369,8738,17476,61440],readHints [47617,94735,36368,56334]),([7,8,15,240,3840,4369,8738,17476,61440],readHints []),([7,15,64,240,3840,4369,8738],readHints [669198,1,1542,2066,3089,6174,22074,27664,25629,175106]),([7,15,64,240,4369,8738,61440],readHints [669702,1027,103950,5652,2575,3585,11269]),([7,15,64,3840,4369,8738],readHints [175630,670211,41988]),([7,15,64,3840,4369,8738,17476],readHints [670731,0,1029,1545,104451,13328,23554,176142,19480])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_206 : K_206.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_207 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,64,3840,4369,8738,34952],readHints [671256,0,1029,1564,104451,13409,23554,671758,19467]),([7,15,64,3840,4369,8738,61440],readHints [672270,0,1029,1554,672771,13328,23554,3588]),([7,15,64,3840,4369,17476,34952],readHints [673282,0,1029,1546,673795,7704,19467]),([7,15,64,3840,8738,17476,34952],readHints [674313,0,1029,1538,2072,8203,49692,11267,15882]),([7,15,128,240,3840,4369,8738],readHints [674824,1,1542,2061,8199,12310,7699,104972]),([7,15,128,240,4369,8738,61440],readHints [675334,1027,103944,5652,2575,3585,11269]),([7,15,128,3840,4369,8738,61440],readHints [675848,0,1029,1549,2055,9747,50188,3588,11267]),([7,15,240,512,3840,4369,17476],readHints [676354,1,2058,3174,6219,16396])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_207 : K_207.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_208 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,512,4369,8738,17476,34952,61440],readHints []),([7,15,240,512,4369,17476,61440],readHints [676866,1546,7692,3585]),([7,15,240,2048,3840,4369,17476],readHints [677383,1,1542,2058,8200,677890,15889]),([7,15,240,2048,4369,17476,61440],readHints [678406,515,70151,5652,37889,4613]),([7,15,240,3840,4096,4369,8738,17476,34952],readHints []),([7,15,240,3840,4369,8738,17476],readHints [678923,1,1030,1545,5150,13328,15381,23554,42510,11281,19468,16903,16392]),([7,15,240,3840,4369,8738,17476,34952,61440],readHints []),([7,15,240,3840,4369,8738,17476,34952,61680],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_208 : K_208.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_209 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,4369,8738,17476,34952,61986],readHints []),([7,15,240,3840,4369,8738,17476,34952,62532],readHints []),([7,15,240,3840,4369,8738,17476,34952,63624],readHints []),([7,15,240,3840,4369,8738,17476,35064,61440],readHints []),([7,15,240,3840,4369,8738,17476,36744,61440],readHints []),([7,15,240,3840,4369,8738,17476,43690,61440],readHints []),([7,15,240,3840,4369,8738,17476,52428,61440],readHints []),([7,15,240,3840,4369,8738,17476,61166,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_209 : K_209.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_210 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,4369,8738,17476,61440,63624],readHints []),([7,15,240,3840,4369,8738,17476,61713],readHints [36551,40499,56471,65539,105525,176651,83970,105996]),([7,15,240,3840,4369,8738,17476,63624],readHints [84614,44186,106498,65594,177183]),([7,15,240,3840,4369,8738,17487],readHints [679438,1030,1554,5783,5150,13328,15389,23554,11281,19468,16903,16392]),([7,15,240,3840,4369,8738,20292],readHints [679947,1,1545,156213,5222,13328,15381,680450,42510,19468,16392]),([7,15,240,3840,4369,8738,20292,34952,61440],readHints []),([7,15,240,3840,4369,8738,21845],readHints [680972,1,1030,1549,5150,7697,16903,16392]),([7,15,240,3840,4369,8738,26214],readHints [681480,1,1030,1545,2055,681995])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_210 : K_210.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_211 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,4369,8738,30583],readHints [682504,1,1030,1549,2055,9238,9747,32268]),([7,15,240,3840,4369,8738,34952],readHints [683016,1,1030,1549,2055,9238,9747,70668,11281]),([7,15,240,3840,4369,8738,34952,61440,62532],readHints []),([7,15,240,3840,4369,8738,34952,62532],readHints [63649,44288,106498,177186,177688]),([7,15,240,3840,4369,8738,34959],readHints [683528,1030,1549,2055,9238,9747,2690,50188,11281]),([7,15,240,3840,4369,8738,36744],readHints [684040,1,1549,2055,684596,9238,9747,685068]),([7,15,240,3840,4369,8738,39321],readHints [685576,1,1030,1545,2055,50187]),([7,15,240,3840,4369,8738,43690],readHints [686092,1,1030,1549,5150,7697,19467])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_211 : K_211.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_212 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,4369,8738,48059],readHints [686603,1,1030,1545,5150,13328,15381,23554,42510]),([7,15,240,3840,4369,8738,62532],readHints [687115,1545,687650,5281,178225,13328,15381,23554,42510,11270,19468,16903,16392]),([7,15,240,3840,4369,8738,63624],readHints [688136,1549,2055,178719,5718,9238,9747,688652,13882,84993,11270]),([7,15,240,3840,4369,8751,17476],readHints [689168,1030,1575,5831,5150,107010,11281,19468,16903,16392]),([7,15,240,3840,4369,8751,34952],readHints [689672,1030,1601,2055,9238,9747,690238,3841,11281]),([7,15,240,3840,4369,8946,17476],readHints [690709,1,1030,1577,104465,18557,134658,691229,19468,16903]),([7,15,240,3840,4369,8946,17476,34952,61440],readHints []),([7,15,240,3840,4369,13107,17476],readHints [691714,1,1030,1546,5150,692241,16903,16392])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_212 : K_212.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_213 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,4369,13107,34952],readHints [692744,1,1030,1546,2055,693250,11281]),([7,15,240,3840,4369,17476,26214],readHints [693767,1,1030,1545,2056,694283,6161]),([7,15,240,3840,4369,17476,30583],readHints [694791,1,1030,1546,2056,64514,6161]),([7,15,240,3840,4369,17476,34952],readHints [695303,1,1030,1546,2056,107522,30737]),([7,15,240,3840,4369,17476,34952,61440,61986],readHints []),([7,15,240,3840,4369,17476,34952,61986],readHints [40706,84530,65573]),([7,15,240,3840,4369,17476,34959],readHints [695815,1030,1546,2056,2743,108034,30737]),([7,15,240,3840,4369,17476,35064],readHints [696327,1,1030,1546,2056,696886,108034,30737])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_213 : K_213.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_214 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,4369,17476,39321],readHints [697351,1,1030,1545,2056,108043,6161]),([7,15,240,3840,4369,17476,52428],readHints [697858,1,1030,1546,5150,698385,19467]),([7,15,240,3840,4369,17476,56797],readHints [698891,1,1030,1545,5150,41486,6161,7692,27664,29717,699394]),([7,15,240,3840,4369,17476,61986],readHints [699915,1545,700453,5150,178254,41486,7692,27664,29717,700930,16904,16391]),([7,15,240,3840,4369,17476,63624],readHints [701447,1546,2056,701995,5714,702466,84993,27142]),([7,15,240,3840,4369,17487,34952],readHints [702983,1030,1546,2056,179202,30737,3843]),([7,15,240,3840,4369,21845,34952],readHints [703495,1,1030,1549,2056,9258,9805,179212,11281]),([7,15,240,3840,4369,34952,43690],readHints [704008,1,1030,1549,8199,9238,9747,704524])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_214 : K_214.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_215 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,4369,34952,48059],readHints [705032,1,1030,1546,8199,705538]),([7,15,240,3840,4369,34952,52428],readHints [706055,1,1030,1546,8200,706562,11281]),([7,15,240,3840,4369,34952,56797],readHints [707079,1,1030,1549,8200,9258,9805,28172]),([7,15,240,3840,4369,34952,61986],readHints [707592,31316,9238,9747,2820,85159,4658,28344,27215]),([7,15,240,3840,4369,34952,62532],readHints [708103,708610,2821,85101,11369,27206]),([7,15,240,3840,4383,8738,17476,34952,61440],readHints []),([7,15,240,3840,4593,8738,34952],readHints [709142,1,1030,1549,2090,9763,70668,13848,11281]),([7,15,240,3840,7953,8738,17476],readHints [709643,1,1545,5222,13328,15381,92674,42510,19468,16903,16392])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_215 : K_215.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_216 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,7953,8738,17476,34952,61440],readHints []),([7,15,240,3840,7953,8738,34952],readHints [710163,1,1549,2125,9251,70668,6265]),([7,15,240,3840,8738,13107,17476],readHints [710667,1,1030,1538,2057,179722,42510,11281,16396]),([7,15,240,3840,8738,13107,34952],readHints [711180,1,1030,1538,2061,179722,22145,11281,16395]),([7,15,240,3840,8738,17476,21845],readHints [711691,1,1030,2060,8201,10768,9237,712194,7693,28273]),([7,15,240,3840,8738,17476,30583],readHints [712715,1,1030,1538,2060,8201,28273]),([7,15,240,3840,8738,17476,34952],readHints [713225,1,1030,1538,2060,8203,49677,11281,15882]),([7,15,240,3840,8738,17476,34952,61713],readHints [44294,105735])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_216 : K_216.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_217 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,8738,17476,36744],readHints [713737,1,1538,2060,8203,104973]),([7,15,240,3840,8738,17476,43690],readHints [714249,1,1030,2060,8203,10791,9257,28682,49677]),([7,15,240,3840,8738,17476,52428],readHints [714761,1,1030,1538,8203,41490,28252,11281,15882]),([7,15,240,3840,8738,17476,61166],readHints [715273,1,1030,8203,10791,9257,28682,41490,28252]),([7,15,240,3840,8738,17652,34952],readHints [715785,1,1030,1538,2060,8203,49677,11281,15882]),([7,15,240,3840,8738,20292,34952],readHints [716297,1,1538,2060,8203,104973,15882]),([7,15,240,3840,8738,26214,34952],readHints [716809,1,1030,1543,2060,8203,49677,11281,15880]),([7,15,240,3840,8738,34952,39321],readHints [717324,1,1030,1543,180233,10814,180744])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_217 : K_217.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_218 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,8738,34952,48059],readHints [717836,1,1030,1538,56841,27265]),([7,15,240,3840,8738,34952,52428],readHints [718349,1,1030,1538,8204,28188,11281,15882]),([7,15,240,3840,8738,34952,61166],readHints [718861,1,1030,8200,10817,28188]),([7,15,240,3840,17476,21845,34952],readHints [719362,1,1030,1548,2058,13911,11281,15885,16395]),([7,15,240,3840,17476,26214,34952],readHints [719881,1,1030,1544,2050,8203,49674,11281,15879]),([7,15,240,3840,17476,34952,39321],readHints [720386,1,1030,1544,180233,180743]),([7,15,240,3840,17476,34952,43690],readHints [720906,1,1030,1548,8194,721421]),([7,15,240,3840,17476,34952,56797],readHints [721922,1,1030,8201,28247])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_218 : K_218.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_219 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,17476,34952,61166],readHints [722442,1,1030,8199,28338]),([7,15,240,3855,4369,8738,17476],readHints [722955,1030,1545,5794,5150,13328,168981,7682,723470,11281,19468,16903,16392]),([7,15,240,3855,4369,8738,17476,34952,61440],readHints []),([7,15,240,3855,4369,8738,34952],readHints [723976,1030,1549,2055,9238,181260,11281]),([7,15,240,3855,4369,17476,34952],readHints [724487,1030,1546,2056,107522,30737]),([7,15,240,3855,8738,17476,34952],readHints [725001,1030,1538,2060,8203,49677,11281,15882]),([7,15,240,4080,4369,8738,17476],readHints [725515,1,515,1030,1545,55824,15381,7682,726030,11281,19468,16903,16392]),([7,15,240,4080,4369,8738,34952],readHints [726536,1,515,1030,1549,2055,9238,9763,29298,71180,4613,11281])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_219 : K_219.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_220 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4080,4369,17476,34952],readHints [727047,1,515,1030,1546,2056,30737,108546,4613]),([7,15,240,4080,8738,17476,34952],readHints [727561,1,515,1030,1538,2060,8203,4613,11281,15882,16909]),([7,15,240,4095,4369,8738,17476],readHints [728075,515,1030,1545,5794,13328,15381,7682,42510,11281,19468,16903,16392]),([7,15,240,4095,4369,8738,34952],readHints [728584,515,1030,1549,2055,9238,729100,29268,4613,11281]),([7,15,240,4095,4369,17476,34952],readHints [729607,515,1030,1546,2056,30737,108546,4613]),([7,15,240,4095,8738,17476,34952],readHints [730121,515,1030,1538,2060,8203,4613,11281,15882,16909]),([7,15,240,4369,7953,8738,17476,34952,61440],readHints []),([7,15,240,4369,7953,8738,17476,61440],readHints [730639,79004,731147,94214,78338,56408,731660])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_220 : K_220.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_221 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,8738,17476,20292],readHints [732177,1,1033,8198,11806,5171,55349,732675,733195,57346]),([7,15,240,4369,8738,17476,20292,34952,61440],readHints []),([7,15,240,4369,8738,17476,34952,36744,61440],readHints []),([7,15,240,4369,8738,17476,36744],readHints [733713,1,8198,133320,60473,11806,5171,181769,71732,734211,57346,16971]),([7,15,240,4369,8738,17476,36744,61440],readHints [40088,79218,40712,84483,79362,182535,182793,183348]),([7,15,240,4369,8738,17476,61440],readHints [183814,515,14859,4116,5647,3585,4613]),([7,15,240,4369,8738,17476,61455],readHints [734726,1,515,8203,4613,15888,16910]),([7,15,240,4369,8738,17476,61680],readHints [735238,8203,4116,11808,5647,5165,13829,3585,15893])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_221 : K_221.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_222 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,8738,17476,61695],readHints [735750,1,736267,11808,5165,13829,15874]),([7,15,240,4369,8738,17476,62532],readHints [736774,515,14859,4116,5647,55330]),([7,15,240,4369,8738,17476,63624],readHints [183814,515,8209,4116,14531,6732,5647,737323,71711,184325,27145]),([7,15,240,4369,8738,17487,61440],readHints [737798,515,38414,4613]),([7,15,240,4369,8738,20292],readHints [57909,738315,43025,50763]),([7,15,240,4369,8738,20292,34952],readHints [738833,1,2054,739395,11806,31850,5171,65064,181769,13827,739893,16459]),([7,15,240,4369,8738,20292,34952,61440],readHints [47807,182534,182793,184885]),([7,15,240,4369,8738,20292,61440],readHints [740363,1033,11839,10768,9237,155650,13326,37889,13827,109062,12300,7688,740917,16401])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_222 : K_222.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_223 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,8738,21845,61440],readHints [741382,515,14860,4116,5647,3585,4613]),([7,15,240,4369,8738,26214,61440],readHints [741894,515,14856,4116,5647,3585,4613]),([7,15,240,4369,8738,30583,61440],readHints [742406,515,22536,4116,5647,3585,4613]),([7,15,240,4369,8738,34952,36744],readHints [742929,1,1037,1543,8198,11806,5171,55348,30732,743432,4611]),([7,15,240,4369,8738,34952,61440],readHints [185350,515,14856,4116,5647,3585,4613]),([7,15,240,4369,8738,34952,61455],readHints [743942,1,515,14856,4613,27171]),([7,15,240,4369,8738,34952,61680],readHints [744454,8200,4116,11808,5647,5165,3585]),([7,15,240,4369,8738,34952,61695],readHints [744966,1,8200,11808,5165,27155])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_223 : K_223.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_224 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,8738,34952,62532],readHints [185350,515,8209,4116,745668,5647,185863,9286,21097,71714,16901]),([7,15,240,4369,8738,34952,63624],readHints [745990,515,14856,4116,5647,55327,4613]),([7,15,240,4369,8738,34959,61440],readHints [746502,515,38408,4613]),([7,15,240,4369,8738,36744],readHints [85556,109576,43025,186380]),([7,15,240,4369,8738,36744,61440],readHints [747016,1037,1543,747523,6678,96853,748044,37889,109062,186932,16401]),([7,15,240,4369,8738,39321,61440],readHints [748550,515,14856,4116,5647,3585,4613]),([7,15,240,4369,8738,43690,61440],readHints [749062,515,14860,4116,5647,3585,4613]),([7,15,240,4369,8738,48059,61440],readHints [749574,515,22539,4116,5647,3585,4613])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_224 : K_224.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_225 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,8738,61440,62532],readHints [750091,515,1033,4144,10768,9237,9730,187426,46597,27662,110086,25612,15879,19464]),([7,15,240,4369,8738,61440,63624],readHints [750600,515,1037,1543,6678,751116,102943,21509,110086]),([7,15,240,4369,8738,62532],readHints [85538,751627,43014,50693]),([7,15,240,4369,8738,63624],readHints [57887,187912,43014,39047]),([7,15,240,4369,8751,17476,61440],readHints [752134,515,38416,188431,4613]),([7,15,240,4369,8751,34952,61440],readHints [752646,515,38408,188431,4613]),([7,15,240,4369,8946,17476,61440],readHints [753158,35349,4116,5647,3585]),([7,15,240,4369,12066,17476,34952,61440],readHints [69897,79366,84224,106138])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_225 : K_225.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_226 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,13107,17476,61440],readHints [753670,515,31234,4116,35841,4613]),([7,15,240,4369,13107,34952,61440],readHints [754182,515,754696,4116,35841,4613]),([7,15,240,4369,17476,20292,34952],readHints [755217,1,1034,2054,11806,9256,755715,72194]),([7,15,240,4369,17476,26214,61440],readHints [756230,515,14855,4116,3585,4613]),([7,15,240,4369,17476,30583,61440],readHints [756742,515,22535,4116,3585,4613]),([7,15,240,4369,17476,34952,36744],readHints [757265,1,1034,1544,8198,11806,188931,6146,7175]),([7,15,240,4369,17476,34952,61440],readHints [757766,515,14855,4116,3585,4613]),([7,15,240,4369,17476,34952,61455],readHints [758278,1,515,14855,4613])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_226 : K_226.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_227 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,17476,34952,61680],readHints [758790,31239,4116,11808,18437,3585]),([7,15,240,4369,17476,34952,61695],readHints [759302,1,31239,11808,18437]),([7,15,240,4369,17476,34952,62532],readHints [759814,515,14850,4116,189447,9286,21097]),([7,15,240,4369,17476,34952,63624],readHints [760326,515,14855,4116,98859,4613]),([7,15,240,4369,17476,34959,61440],readHints [760838,515,38407,4613]),([7,15,240,4369,17476,35064,61440],readHints [761350,35335,4116,3585]),([7,15,240,4369,17476,39321,61440],readHints [761862,515,14855,4116,3585,4613]),([7,15,240,4369,17476,52428,61440],readHints [762374,515,14850,4116,37889,4613])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_227 : K_227.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_228 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,17476,56797,61440],readHints [762886,515,14859,4116,24079,3585,4613]),([7,15,240,4369,17476,61440,61986],readHints [763403,515,1033,4144,45070,9740,46597,27664,29717,25606,15880,19463]),([7,15,240,4369,17476,61440,63624],readHints [763911,515,1034,1544,58370,102955,21509]),([7,15,240,4369,17476,63624],readHints [764459,187911,38914]),([7,15,240,4369,17487,34952,61440],readHints [764934,515,38407,4613]),([7,15,240,4369,21845,34952,61440],readHints [765446,515,14855,4116,3585,4613]),([7,15,240,4369,34952,43690,61440],readHints [765958,515,14856,4116,3585,4613]),([7,15,240,4369,34952,48059,61440],readHints [766470,515,766984,4116,3585,4613])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_228 : K_228.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_229 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,34952,52428,61440],readHints [767494,515,14855,4116,37889,4613]),([7,15,240,4369,34952,56797,61440],readHints [768006,515,14855,4116,24079,3585,4613]),([7,15,240,4369,34952,61440,61986],readHints [768520,515,769108,6678]),([7,15,240,4369,34952,61440,62532],readHints [769543,515,14850]),([7,15,240,4369,34952,62532],readHints [86023,770050,43113,50693]),([7,15,240,4593,8738,34952,61440],readHints [770566,35350,4116,5647,3585]),([7,15,240,7953,8738,17476,34952,61440],readHints [36440,771073,56521]),([7,15,240,7953,8738,17476,61440],readHints [771595,1033,189953,190479,772252,10768,17964,9237,8710,28674,2648,41486,12300,7175,7688])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_229 : K_229.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_230 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,7953,8738,34952,61440],readHints [772627,1037,1613,189953,4156,190479,6691,39580,17964,5223,8710,2761,48140,19577]),([7,15,240,8738,13107,17476,61440],readHints [773126,515,773643,4111,35841,4613]),([7,15,240,8738,13107,34952,61440],readHints [774150,515,31244,4111,35841,4613]),([7,15,240,8738,17476,20292,34952],readHints [774665,1,1026,2054,8203,184337,11274]),([7,15,240,8738,17476,21845,61440],readHints [775174,515,72715,4111,3585,4613]),([7,15,240,8738,17476,30583,61440],readHints [775686,515,776203,4111,3585,4613]),([7,15,240,8738,17476,34952,36744],readHints [776721,1,1026,1548,8198,11827,188931,41672,167993,6154,92681,777229]),([7,15,240,8738,17476,34952,61440],readHints [777734,515,8201,4111,3585,4613])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_230 : K_230.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_231 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,8738,17476,34952,61455],readHints [778246,1,515,8201,4613]),([7,15,240,8738,17476,34952,61680],readHints [778758,8201,4111,11821,18437,3585]),([7,15,240,8738,17476,34952,61695],readHints [779270,1,8201,11821,18437]),([7,15,240,8738,17476,34952,62532],readHints [779782,515,8201,4111,10948]),([7,15,240,8738,17476,34952,63624],readHints [780294,515,8205,4111,13507,15436,4613]),([7,15,240,8738,17476,36744],readHints [190985,109581,780857,43208,38922]),([7,15,240,8738,17476,36744,61440],readHints [781321,1026,1548,2059,5723,37889,3128,13946,7181,16401]),([7,15,240,8738,17476,43690,61440],readHints [781830,515,72713,4111,3585,4613])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_231 : K_231.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_232 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,8738,17476,52428,61440],readHints [782342,515,22537,4111,37889,4613]),([7,15,240,8738,17476,61166,61440],readHints [782854,515,191497,4111,24084,3585,4613]),([7,15,240,8738,17652,34952,61440],readHints [783366,56841,4111,3585]),([7,15,240,8738,20292,34952],readHints [190985,783939,43114,38922]),([7,15,240,8738,20292,34952,61440],readHints [784393,1026,1548,2059,784897,2931,50189,6154]),([7,15,240,8738,26214,34952,61440],readHints [785414,515,8201,4111,3585,4613,11272]),([7,15,240,8738,34952,39321,61440],readHints [785926,515,8204,4111,3585,4613,11272]),([7,15,240,8738,34952,48059,61440],readHints [786438,515,8204,4111,3585,4613])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_232 : K_232.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_233 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,8738,34952,52428,61440],readHints [786950,515,22541,4111,37889,4613]),([7,15,240,8738,34952,61166,61440],readHints [787462,515,22541,4111,24084,3585,4613,11272]),([7,15,240,17476,21845,34952,61440],readHints [787974,515,31234,3585,4613]),([7,15,240,17476,26214,34952,61440],readHints [788486,515,8201,3585,4613,11271]),([7,15,240,17476,34952,39321,61440],readHints [788998,515,8194,3585,4613,11271]),([7,15,240,17476,34952,43690,61440],readHints [789510,515,22538,3585,4613]),([7,15,240,17476,34952,56797,61440],readHints [790022,515,8194,24079,3585,4613]),([7,15,240,17476,34952,61166,61440],readHints [790534,515,22538,24084,3585,4613,11271])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_233 : K_233.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_234 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,255,3840,4369,8738,17476],readHints [791051,0,1030,1545,13328,107010,3588,27662,11281,19468,16903,16392]),([7,15,255,3840,4369,8738,34952],readHints [791560,0,1030,1549,2055,9747,70668,11281]),([7,15,255,3840,4369,17476,34952],readHints [792071,0,1030,1546,2056,2564,107522,30737]),([7,15,255,3840,8738,17476,34952],readHints [792585,0,1030,1538,2060,8203,11281,15882,16909]),([7,15,255,4369,8738,17476,61440],readHints [793094,0,515,14859,3588,4613]),([7,15,255,4369,8738,34952,61440],readHints [793606,0,515,14856,3588,4613]),([7,15,255,4369,17476,34952,61440],readHints [794118,0,515,14855,3588,4613]),([7,15,255,8738,17476,34952,61440],readHints [794630,0,515,8201,3588,4613])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_234 : K_234.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_235 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,512,3840,4369,17476,61440],readHints [795138,0,1546,795652,7692]),([7,15,2048,3840,4369,17476,61440],readHints [796167,0,1029,1546,2056,26116,32258,11267]),([7,15,3840,4080,4369,8738,17476],readHints [796683,1,517,1545,8707,55824,68098,797198,19468,16903,16392]),([7,15,3840,4080,4369,8738,34952],readHints [797704,1,517,1549,2055,9235,9763,29298,71180,4611]),([7,15,3840,4080,4369,17476,34952],readHints [798215,1,517,1546,2056,192002,4611]),([7,15,3840,4080,8738,17476,34952],readHints [798729,1,517,1538,2060,8203,4611,799245,15882]),([7,15,3840,4095,4369,8738,17476],readHints [799755,0,517,1545,13328,68098,3588,27662,19468,16903,16392]),([7,15,3840,4095,4369,8738,34952],readHints [800264,0,517,1549,2055,9235,29268,71180,4611])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_235 : K_235.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_236 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4095,4369,17476,34952],readHints [800775,0,517,1546,2056,2564,192002,4611]),([7,15,3840,4095,8738,17476,34952],readHints [801289,0,517,1538,2060,8203,4611,15882,16909]),([7,15,3840,4369,4593,8738,17476],readHints [801822,25,544,802406,14602,802827,79875,16903,16392]),([7,15,3840,4369,4593,8738,17476,61440],readHints [94219,36490,803330,56522,69695,105484,79374,83998,106145]),([7,15,3840,4369,4593,8738,34952],readHints [803848,25,544,2055,178710,804382,7171]),([7,15,3840,4369,4593,17476,34952],readHints [804871,25,544,2056,805406,33794]),([7,15,3840,4369,8738,8946,17476],readHints [805899,26,557,1033,806421,192563,12291,806926,25612]),([7,15,3840,4369,8738,8946,17476,34952,61440],readHints [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_236 : K_236.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_237 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,8738,8946,34952],readHints [807436,26,557,1037,192563,15368,12291,25611]),([7,15,3840,4369,8738,16384,17476],readHints [807947,0,517,1033,10768,17410,26116,808451,27662,15879,19464]),([7,15,3840,4369,8738,16384,34952],readHints [808968,0,517,1543,33315,6675,8714,2564,809475,11273]),([7,15,3840,4369,8738,17476,34952,35064,61440],readHints []),([7,15,3840,4369,8738,17476,35064],readHints [810001,1,518,810571,10768,811062,17410,8714,811534,6157,12300,7175,7688,812043,29699,27243,19507]),([7,15,3840,4369,8738,17476,35064,61440],readHints [63753,193026,812558,176694]),([7,15,3840,4369,8738,17476,61440],readHints [813067,0,517,1033,10768,17410,26116,13326,12300,7175,7688,58883]),([7,15,3840,4369,8738,17476,61455],readHints [813579,1,517,1033,814096,17410,193550,12300,7175,7688,4611,25755])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_237 : K_237.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_238 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,8738,17476,61713],readHints [814595,0,517,815108,7175,7688,27803,29726,110603]),([7,15,3840,4369,8738,17476,61986],readHints [815627,0,517,1033,816165,816643,2564,13326,12300]),([7,15,3840,4369,8738,17476,63624],readHints [817155,0,517,817668,14493,10886,818183,9588,17410,8714,41530,818696,6157,12300,27761,29713,819211,27145]),([7,15,3840,4369,8738,17476,65280],readHints [819723,0,518,1033,10768,820226,26116,13326,3089,12300,7175,7688,25630]),([7,15,3840,4369,8738,17476,65295],readHints [820747,1,518,1033,10768,17410,193550,3089,12300,7175,7688,25755,57365]),([7,15,3840,4369,8738,17487,61440],readHints [821262,517,1042,821764,4298,37409,10768,18079,17410,12300,7175,7688,58883]),([7,15,3840,4369,8738,17652,34952,61440],readHints [61195,822645,69896,822792,823554]),([7,15,3840,4369,8738,20292,61440],readHints [823819,0,1033,11839,10768,824322,194052,13326,12300,7688])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_238 : K_238.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_239 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,8738,21845,61440],readHints [824844,0,517,1037,111107,7175,7688,3588]),([7,15,3840,4369,8738,26214,61440],readHints [825352,0,517,1033,1543,825867,3588,4611]),([7,15,3840,4369,8738,30583,61440],readHints [826376,0,517,1037,1543,6675,826892,3588,4611]),([7,15,3840,4369,8738,34952,35064],readHints [827400,1,518,1037,1543,6675,827916,21521]),([7,15,3840,4369,8738,34952,61440],readHints [828424,0,517,1037,1543,6675,59404,21507,3588]),([7,15,3840,4369,8738,34952,61455],readHints [828936,1,517,1037,1543,6675,59404,21507,27171]),([7,15,3840,4369,8738,34952,61713],readHints [829448,0,517,1543,829955]),([7,15,3840,4369,8738,34952,61986],readHints [830476,0,517,1037,189448,9290,831026,831491,12299])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_239 : K_239.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_240 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,8738,34952,63624],readHints [194568,0,517,1037,1543,6675,59404,21507]),([7,15,3840,4369,8738,34952,65280],readHints [832008,0,518,1037,1543,6675,59404,3089,3588]),([7,15,3840,4369,8738,34952,65295],readHints [832520,1,518,1037,1543,6675,59404,3089,27158]),([7,15,3840,4369,8738,34959,61440],readHints [833032,517,1037,1543,6675,5763,58380,21507]),([7,15,3840,4369,8738,36744,61440],readHints [833544,0,1037,1543,834051,6675,96853,834572,3131,3588]),([7,15,3840,4369,8738,39321,61440],readHints [835080,0,517,1033,1543,58379,3588,4611]),([7,15,3840,4369,8738,43690,61440],readHints [835596,0,517,1037,111107,12299,3588]),([7,15,3840,4369,8738,48059,61440],readHints [836107,0,517,1033,10768,17410,13326,3588,58883])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_240 : K_240.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_241 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,8738,61440,62532],readHints [836619,0,517,1033,10768,17410,26116,46595,27662,25612,15879,19464]),([7,15,3840,4369,8738,61440,63624],readHints [194568,0,517,1037,1543,6675,58380,2564,21507]),([7,15,3840,4369,8738,63624],readHints [195080,195642,41987]),([7,15,3840,4369,8751,17476,61440],readHints [837136,517,1063,4234,17410,12300,7175,7688,58883]),([7,15,3840,4369,8751,34952,61440],readHints [837640,517,1089,1543,4190,6675,2791,21507,196158]),([7,15,3840,4369,8946,17476],readHints [838165,838707,67195,196733]),([7,15,3840,4369,8946,17476,34952],readHints [839219,26,557,839803,147970,9223,24682,45597,6157,12300,176149,11273,25611]),([7,15,3840,4369,8946,17476,34952,61440],readHints [36381,184853])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_241 : K_241.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_242 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,8946,17476,61440],readHints [840213,1065,61954,17964,45597,12300,7175,3585,4614,25651]),([7,15,3840,4369,13107,17476,61440],readHints [840706,0,517,1034,26116,841219,7175,7688]),([7,15,3840,4369,13107,34952,61440],readHints [841736,0,517,1034,1543,21507,196098,3588]),([7,15,3840,4369,16384,17476,34952],readHints [842247,0,517,1034,2056,197123,842754,2564]),([7,15,3840,4369,17476,26214,61440],readHints [843271,0,517,1033,1544,35844,47115,4611]),([7,15,3840,4369,17476,30583,61440],readHints [843783,0,517,1034,1544,35844,8706,4611]),([7,15,3840,4369,17476,34952,35064],readHints [844295,1,518,1034,1544,197649,111618,55350]),([7,15,3840,4369,17476,34952,61440],readHints [844807,0,517,1034,1544,35844,32770,21507])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_242 : K_242.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_243 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,17476,34952,61455],readHints [845319,1,517,1034,1544,32770,21507]),([7,15,3840,4369,17476,34952,61713],readHints [845831,0,517,1544,5636,846339]),([7,15,3840,4369,17476,34952,61986],readHints [846851,0,517,847364,14525,6727,45106,185864,9290,8717,9740,13686,71717,112139,6153,27735,30071,25602,27146,73223]),([7,15,3840,4369,17476,34952,63624],readHints [847879,0,517,1034,1544,5636,32770,21507]),([7,15,3840,4369,17476,34952,65280],readHints [848391,0,518,1034,1544,35844,26641,111618]),([7,15,3840,4369,17476,34952,65295],readHints [848903,1,518,1034,1544,26641,111618]),([7,15,3840,4369,17476,34959,61440],readHints [849415,517,1034,1544,54786,21507]),([7,15,3840,4369,17476,35064],readHints [85558,198151,186370])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_243 : K_243.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_244 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,17476,35064,61440],readHints [849927,1034,1544,850438,4472,11956,39692,54786,5213,37889,3077,186934]),([7,15,3840,4369,17476,39321,61440],readHints [850951,0,517,1033,1544,35844,30219,4611]),([7,15,3840,4369,17476,52428,61440],readHints [851458,0,517,1034,35844,111107,12299]),([7,15,3840,4369,17476,56797,61440],readHints [851979,0,517,1033,35844,10766,9740,13328,40962,58883]),([7,15,3840,4369,17476,61440,61986],readHints [852491,0,517,1033,25092,10766,9740,187429,46595,27664,198658,15880,19463]),([7,15,3840,4369,17476,61440,63624],readHints [852999,0,517,1034,1544,25092,58370,21507]),([7,15,3840,4369,17476,61986],readHints [85541,853515,50691]),([7,15,3840,4369,17476,63624],readHints [195079,195586,41987])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_244 : K_244.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_245 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,17487,34952,61440],readHints [854023,517,1034,1544,854532,4281,37448,167426,2829,21507]),([7,15,3840,4369,21845,34952,61440],readHints [855047,0,517,1037,1544,6733,21507,48140,3588]),([7,15,3840,4369,34952,43690,61440],readHints [855560,0,517,1037,2055,6675,856076,3588,4611]),([7,15,3840,4369,34952,48059,61440],readHints [856584,0,517,1034,2055,24250,3588,4611,16386]),([7,15,3840,4369,34952,52428,61440],readHints [857095,0,517,1034,2056,6146,3588,4611]),([7,15,3840,4369,34952,56797,61440],readHints [857607,0,517,1037,2056,6733,3588,4611]),([7,15,3840,4369,34952,61440,61986],readHints [858120,0,22612,6675,3075,16946]),([7,15,3840,4369,34952,61440,62532],readHints [858631,0,22530,3075,3588])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_245 : K_245.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_246 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,4369,34952,61986],readHints [86024,199218,50691]),([7,15,3840,4593,8738,17476,34952],readHints [859166,25,544,12902,859657,6691,11129,9442,8714,28818,13690,71702,112152,7175,7688,27914,860312]),([7,15,3840,4593,8738,17476,34952,61440],readHints [69784,84129,183318]),([7,15,3840,4593,8738,34952],readHints [112662,860696,42014]),([7,15,3840,4593,8738,34952,61440],readHints [861206,1037,1578,6691,5884,861708,3585,4614]),([7,15,3840,7953,8738,17476,61440],readHints [862219,0,1033,10768,74242,194052,13326,12300,7175,7688]),([7,15,3840,7953,8738,34952,61440],readHints [862739,0,1037,1613,5223,59404,3588]),([7,15,3840,8738,8946,17476,34952],readHints [863241,26,557,2060,8203,4659,199693])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_246 : K_246.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_247 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,8738,13107,17476,61440],readHints [863755,0,517,1026,1545,26116,13326,200202,7692,4611]),([7,15,3840,8738,13107,34952,61440],readHints [864268,0,517,1026,1549,21507,200202,7691,3588]),([7,15,3840,8738,16384,17476,34952],readHints [864777,0,517,1026,8203,4611,199690]),([7,15,3840,8738,17476,21845,61440],readHints [865291,0,517,1548,2057,14352,152578,9741,3588,4611]),([7,15,3840,8738,17476,30583,61440],readHints [865803,0,517,1026,1548,2057,3588,4611]),([7,15,3840,8738,17476,34952,35064],readHints [866317,1,518,1026,1548,197649,32778,866825]),([7,15,3840,8738,17476,34952,61440],readHints [867337,0,517,1026,1548,2059,21507,6154,51213,3588]),([7,15,3840,8738,17476,34952,61455],readHints [867849,1,517,1026,1548,2059,21507,6154,7181,16491])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_247 : K_247.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_248 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,8738,17476,34952,61713],readHints [868355,0,517,868868,869755,8711,9736,15740,27740,30077,25610,27138,175113,869899]),([7,15,3840,8738,17476,34952,61986],readHints [870409,0,517,1548,2059,14525,6727,3075,870925]),([7,15,3840,8738,17476,34952,63624],readHints [871437,0,517,1026,1548,5636,32778,13469,21507,27755,73225]),([7,15,3840,8738,17476,34952,65280],readHints [871945,0,518,1026,1548,2059,3089,6154,51213,3588]),([7,15,3840,8738,17476,34952,65295],readHints [872457,1,518,1026,1548,2059,3089,6154,7181,16491]),([7,15,3840,8738,17476,36744,61440],readHints [872969,0,1026,1548,2059,50189,3588]),([7,15,3840,8738,17476,43690,61440],readHints [873481,0,517,1548,2059,14375,31754,51213,3588,4611]),([7,15,3840,8738,17476,52428,61440],readHints [873993,0,517,1026,2059,10770,6154,3588,4611])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_248 : K_248.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_249 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,8738,17476,61166,61440],readHints [874505,0,517,2059,14375,31754,10770,3588,4611]),([7,15,3840,8738,17652,34952,61440],readHints [875017,1026,1548,2059,875521,37420,25157,18814,50189,6154,4614]),([7,15,3840,8738,20292,34952,61440],readHints [876041,0,1026,1548,2059,50189,6154,3588]),([7,15,3840,8738,26214,34952,61440],readHints [876553,0,517,1031,1548,2059,21507,30728,51213,3588]),([7,15,3840,8738,34952,39321,61440],readHints [877068,0,517,1031,200713,14398,201224,3588,4611]),([7,15,3840,8738,34952,48059,61440],readHints [877580,0,517,1026,878089,3588,4611]),([7,15,3840,8738,34952,52428,61440],readHints [878605,0,517,1026,2060,879114,3588,4611]),([7,15,3840,8738,34952,61166,61440],readHints [879629,0,517,880136,14401,3588,4611])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_249 : K_249.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_250 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3840,17476,21845,34952,61440],readHints [880642,0,517,1036,1546,21507,6157,7691,3588]),([7,15,3840,17476,26214,34952,61440],readHints [881161,0,517,1032,1538,2059,21507,30727,51210,3588]),([7,15,3840,17476,34952,39321,61440],readHints [881666,0,517,1032,200713,201223,3588,4611]),([7,15,3840,17476,34952,43690,61440],readHints [882186,0,517,1036,2050,882701,3588,4611]),([7,15,3840,17476,34952,56797,61440],readHints [883202,0,517,2057,3588,4611]),([7,15,3840,17476,34952,61166,61440],readHints [883722,0,517,884231,3588,4611]),([7,15,3855,4369,8738,17476,61440],readHints [884747,517,1033,4151,10768,21013,9730,135182,12300,7175,7688,58883]),([7,15,3855,4369,8738,34952,61440],readHints [885256,517,1037,1543,201740,21507])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_250 : K_250.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_251 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,3855,4369,17476,34952,61440],readHints [885767,517,1034,1544,32770,21507]),([7,15,3855,8738,17476,34952,61440],readHints [886281,517,1026,1548,2059,21507,6154,51213]),([7,15,4369,8738,17476,35064,61440],readHints [886790,887301,12820,4111,3585,4991]),([7,15,4369,8738,17476,36744,61440],readHints [887811,0,2053,19066,62520,888329,5665,22018,888836,16401]),([7,15,4369,8738,17476,61440,61680],readHints [889349,8203,12848,4119,3584,11285]),([7,15,4369,8738,17476,61440,61695],readHints [889861,0,8203,5678,28428,11266]),([7,15,4369,8738,17476,61440,65280],readHints [890371,0,202246,5665,3588]),([7,15,4369,8738,17476,61440,65295],readHints [890883,202246,12855,4123])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_251 : K_251.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_252 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,4369,8738,34952,35064,61440],readHints [891398,14853,12820,4111,3585,11272]),([7,15,4369,8738,34952,36744,61440],readHints [891907,0,525,1031,2053,26636,72200,7227,3588,16401]),([7,15,4369,8738,34952,61440,61680],readHints [892421,113160,12848,4119,3584]),([7,15,4369,8738,34952,61440,61695],readHints [892933,0,113160,28389]),([7,15,4369,8738,34952,61440,65280],readHints [893443,0,22534,3588]),([7,15,4369,8738,34952,61440,65295],readHints [893955,22534,12855,4123,28390]),([7,15,4369,8738,36744,61440],readHints [112643,202811,203349,160780]),([7,15,4369,17476,34952,35064,61440],readHints [894470,14853,12820,3585,11271])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_252 : K_252.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_253 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,4369,17476,34952,36744,61440],readHints [894979,0,522,1032,2053,4129,5122,72199,3588,16401]),([7,15,4369,17476,34952,61440,61680],readHints [895493,113671,12848,3584]),([7,15,4369,17476,34952,61440,61695],readHints [896005,0,113671,4142]),([7,15,4369,17476,34952,61440,65280],readHints [896515,0,8198,4129,3588]),([7,15,4369,17476,34952,61440,65295],readHints [897027,8198,12855]),([7,15,4369,17476,35064,61440],readHints [86022,198149,38919]),([7,15,8738,17476,34952,35064,61440],readHints [897542,14853,12815,3585]),([7,15,8738,17476,34952,36744,61440],readHints [898051,0,514,1036,2053,4129,10874,43576,5130,898569,899085,3588,16401])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_253 : K_253.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_254 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,8738,17476,34952,61440,61680],readHints [899589,8201,12823,3584]),([7,15,8738,17476,34952,61440,61695],readHints [900101,0,8201,4142]),([7,15,8738,17476,34952,61440,65280],readHints [900611,0,8198,4129,3588]),([7,15,8738,17476,34952,61440,65295],readHints [901123,8198,12827]),([7,15,8738,17476,36744,61440],readHints [175625,202765,901688,41994]),([7,64,240,3840,4369,8738,61440],readHints [902145,516,203790,4608,11270]),([7,128,240,3840,4369,8738,61440],readHints [902657,516,203784,4608,11270]),([7,240,255,3840,4369,8738,17476],readHints [903179,4,513,1030,1545,13333,107010,3584,86542,11281,19468,16903,16392])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_254 : K_254.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_255 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,255,3840,4369,8738,34952],readHints [903688,4,513,1030,1549,2055,10774,9747,71180,11281]),([7,240,255,3840,4369,17476,34952],readHints [904199,4,513,1030,1546,2056,2560,30737,71170]),([7,240,255,3840,8738,17476,34952],readHints [904713,4,513,1030,1538,2060,8203,11281,15882,16909]),([7,240,255,4369,8738,17476,61440],readHints [905222,4,14859,11796,5135,3584,4609]),([7,240,255,4369,8738,34952,61440],readHints [905734,4,14856,11796,5135,3584,4609]),([7,240,255,4369,17476,34952,61440],readHints [906246,4,14855,11796,3584,4609]),([7,240,255,8738,17476,34952,61440],readHints [906758,4,8201,11791,3584,4609]),([7,240,512,3840,4369,17476,61440],readHints [907265,4,907778,3584])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_255 : K_255.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_256 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,2048,3840,4369,17476,61440],readHints [908289,4,103943,3584,11270]),([7,240,3840,3855,4369,8738,17476],readHints [908811,1025,1545,5734,5195,55829,68098,909326,19468,16903,16392]),([7,240,3840,3855,4369,8738,34952],readHints [909832,1025,1549,2055,10774,9235,181260]),([7,240,3840,3855,4369,17476,34952],readHints [910343,1025,1546,2056,910850]),([7,240,3840,3855,8738,17476,34952],readHints [911369,1025,1538,2060,8203,911885,15882]),([7,240,3840,4095,4369,8738,17476],readHints [912395,4,1025,1545,5195,13333,68098,3584,86542,19468,16903,16392]),([7,240,3840,4095,4369,8738,34952],readHints [912904,4,1025,1549,2055,10774,9235,70668,29268]),([7,240,3840,4095,4369,17476,34952],readHints [913415,4,1025,1546,2056,2560,108546])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_256 : K_256.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_257 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,4095,8738,17476,34952],readHints [913929,4,1025,1538,2060,8203,15882,16909]),([7,240,3840,4369,4383,8738,17476,34952,61440],readHints []),([7,240,3840,4369,4383,8738,17476,61440],readHints [914433,103468]),([7,240,3840,4369,8738,17476,34959,61440],readHints [40137]),([7,240,3840,4369,8738,17476,61440],readHints [914945,4,14859,3584,4614]),([7,240,3840,4369,8738,17476,61680],readHints [915457,8203,4121,5658,24064,4614,15893]),([7,240,3840,4369,8738,17476,65280],readHints [915969,4,31243,3584,57444]),([7,240,3840,4369,8738,17476,65520],readHints [916481,8203,4121,5658,24064,57444])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_257 : K_257.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_258 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,4369,8738,17487,34952,61440],readHints [40024,47645,204481,56334,916996]),([7,240,3840,4369,8738,17487,61440],readHints [917518,1042,918020,4298,37760,80472,10781,18079,17410,204801,12332,7175,7688,4614,25751,110667]),([7,240,3840,4369,8738,20292,61440],readHints [918529,4,35339,3584]),([7,240,3840,4369,8738,21845,61440],readHints [919041,4,22540,3584,4614,16940]),([7,240,3840,4369,8738,26214,61440],readHints [919553,4,14856,3584,4614]),([7,240,3840,4369,8738,30583,61440],readHints [920065,4,22536,3584,4614]),([7,240,3840,4369,8738,34952,61440],readHints [920577,4,14856,3584,4614]),([7,240,3840,4369,8738,34952,61680],readHints [921089,8200,4121,5658,4614])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_258 : K_258.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_259 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,4369,8738,34952,65280],readHints [921601,4,31240,3584]),([7,240,3840,4369,8738,34952,65520],readHints [922113,8200,4121,5658,57502]),([7,240,3840,4369,8738,34959,61440],readHints [922632,1037,1543,14358,80627,6675,5763,923148,24068,204801,12532,4614,923778]),([7,240,3840,4369,8738,36744,61440],readHints [924161,4,35336,3584]),([7,240,3840,4369,8738,39321,61440],readHints [924673,4,22536,3584,4614,17033]),([7,240,3840,4369,8738,43690,61440],readHints [925185,4,14860,3584,4614]),([7,240,3840,4369,8738,48059,61440],readHints [925697,4,22539,3584,4614]),([7,240,3840,4369,8738,61440,62532],readHints [926219,4,1033,926720,10773,17410,7729,86529,25644,15879,19464])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_259 : K_259.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_260 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,4369,8738,61440,63624],readHints [927240,4,1037,1543,14358,6675,927756,2560,12374,86529,25737]),([7,240,3840,4369,8751,17476,34952,61440],readHints [40639,928271]),([7,240,3840,4369,8751,17476,61440],readHints [928784,1063,205327,4234,10754,18059,929281,12300,7175,7688,4614,25799,73601]),([7,240,3840,4369,8751,34952,61440],readHints [929800,1089,1543,205327,4190,14358,6675,39460,18113,930366,9729,2814,3458,4614,73457,16641]),([7,240,3840,4369,8946,17476,61440],readHints [930817,38421,4614]),([7,240,3840,4369,13107,17476,61440],readHints [931329,4,31234,3584,4614]),([7,240,3840,4369,13107,34952,61440],readHints [931841,4,14856,3584,4614]),([7,240,3840,4369,17476,26214,61440],readHints [932353,4,14855,3584,4614])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_260 : K_260.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_261 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,4369,17476,30583,61440],readHints [932865,4,22535,3584,4614]),([7,240,3840,4369,17476,34952,61440],readHints [933377,4,14855,3584,4614]),([7,240,3840,4369,17476,34952,61680],readHints [933889,31239,4121,17920,4614]),([7,240,3840,4369,17476,34952,65280],readHints [934401,4,8199,3584]),([7,240,3840,4369,17476,34952,65520],readHints [934913,8199,4121,17920]),([7,240,3840,4369,17476,34959,61440],readHints [935431,1034,1544,80629,54786,5507,24068,109057,12388,4614,19639,110980]),([7,240,3840,4369,17476,35064,61440],readHints [935937,38407,4614]),([7,240,3840,4369,17476,39321,61440],readHints [936449,4,22535,3584,4614,17093])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_261 : K_261.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_262 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,4369,17476,52428,61440],readHints [936961,4,14850,3584,4614]),([7,240,3840,4369,17476,56797,61440],readHints [937473,4,22539,3584,4614,16940]),([7,240,3840,4369,17476,61440,61986],readHints [937995,4,1033,938496,43534,9740,7758,27669,198657,15880,19463]),([7,240,3840,4369,17476,61440,63624],readHints [939015,4,1034,1544,25088,58370,12370,110081,25797]),([7,240,3840,4369,17487,34952,61440],readHints [939527,1034,1544,940036,4281,37448,940693,9886,2829,3461,48130,4614,73467,16643]),([7,240,3840,4369,21845,34952,61440],readHints [941057,4,14855,3584,4614]),([7,240,3840,4369,34952,43690,61440],readHints [941569,4,14856,3584,4614]),([7,240,3840,4369,34952,48059,61440],readHints [942081,4,14856,3584,4614])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_262 : K_262.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_263 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,4369,34952,52428,61440],readHints [942593,4,14855,3584,4614]),([7,240,3840,4369,34952,56797,61440],readHints [943105,4,14855,3584,4614]),([7,240,3840,4369,34952,61440,61986],readHints [943624,4,944212,14358,6675,7940]),([7,240,3840,4369,34952,61440,62532],readHints [944647,4,22530,7941,3584]),([7,240,3840,4383,8738,17476,34952,61440],readHints [36619]),([7,240,3840,4593,8738,34952,61440],readHints [945153,38422,4614]),([7,240,3840,7953,8738,17476,61440],readHints [945665,4,35339,3584]),([7,240,3840,7953,8738,34952,61440],readHints [946177,4,35347,3584])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_263 : K_263.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_264 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,8738,13107,17476,61440],readHints [946689,4,31243,3584,4614]),([7,240,3840,8738,13107,34952,61440],readHints [947201,4,31244,3584,4614]),([7,240,3840,8738,17476,21845,61440],readHints [947713,4,72715,3584,4614]),([7,240,3840,8738,17476,30583,61440],readHints [948225,4,8203,3584,4614]),([7,240,3840,8738,17476,34952,61440],readHints [948737,4,8201,3584,4614]),([7,240,3840,8738,17476,34952,61680],readHints [949249,8201,4122,17920,4614]),([7,240,3840,8738,17476,34952,65280],readHints [949761,4,8201,3584]),([7,240,3840,8738,17476,34952,65520],readHints [950273,8201,4122,17920])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_264 : K_264.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_265 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,8738,17476,36744,61440],readHints [950785,4,56841,3584]),([7,240,3840,8738,17476,43690,61440],readHints [951297,4,72713,3584,4614]),([7,240,3840,8738,17476,52428,61440],readHints [951809,4,22537,3584,4614]),([7,240,3840,8738,17476,61166,61440],readHints [952321,4,191497,3584,4614]),([7,240,3840,8738,17652,34952,61440],readHints [952833,953353,4614]),([7,240,3840,8738,20292,34952,61440],readHints [953857,4,56841,3584]),([7,240,3840,8738,26214,34952,61440],readHints [954369,4,8201,3584,4614,11272]),([7,240,3840,8738,34952,39321,61440],readHints [954881,4,8204,3584,4614,11272])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_265 : K_265.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_266 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,8738,34952,48059,61440],readHints [955393,4,8204,3584,4614]),([7,240,3840,8738,34952,52428,61440],readHints [955905,4,22541,3584,4614]),([7,240,3840,8738,34952,61166,61440],readHints [956417,4,22541,3584,4614,11272]),([7,240,3840,17476,21845,34952,61440],readHints [956929,4,31234,3584,4614]),([7,240,3840,17476,26214,34952,61440],readHints [957441,4,8201,3584,4614,11271]),([7,240,3840,17476,34952,39321,61440],readHints [957953,4,8194,3584,4614,11271]),([7,240,3840,17476,34952,43690,61440],readHints [958465,4,22538,3584,4614]),([7,240,3840,17476,34952,56797,61440],readHints [958977,4,8194,3584,4614])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_266 : K_266.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_267 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,3840,17476,34952,61166,61440],readHints [959489,4,22538,3584,4614,11271]),([7,240,4080,4369,8738,17476,61440],readHints [960001,3,14859,3589,4614]),([7,240,4080,4369,8738,34952,61440],readHints [960513,3,14856,3589,4614]),([7,240,4080,4369,17476,34952,61440],readHints [961025,3,14855,3589,4614]),([7,240,4080,8738,17476,34952,61440],readHints [961537,3,8201,3589,4614]),([7,240,4369,4383,8738,17476,61440],readHints [962068,55,8354,72193,962608]),([7,240,4369,4383,8738,34952,61440],readHints [963092,55,35336,72193,3632]),([7,240,4369,4383,17476,34952,61440],readHints [963604,55,35335,3632,11265])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_267 : K_267.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_268 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,4369,7953,8738,17476,61440],readHints [964097,4,8267,964608,4998,28241,11284]),([7,240,4369,7953,8738,34952,61440],readHints [965121,4,35336,3584,28220,11284]),([7,240,4369,7953,17476,34952,61440],readHints [965633,4,35335,3584,11284]),([7,240,4369,8738,8751,17476,61440],readHints [966159,27,70155,205825,3607,27152]),([7,240,4369,8738,8751,34952,61440],readHints [966671,27,70156,205825,3607,27172]),([7,240,4369,8738,12066,17476,61440],readHints [967169,4,70155,3584,15887]),([7,240,4369,8738,12066,34952,61440],readHints [967681,4,70156,3584,15887]),([7,240,4369,8738,17476,61440,61455],readHints [968193,3,20491,26117])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_268 : K_268.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_269 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,4369,8738,17476,61440,61695],readHints [968705,4,20491,2560]),([7,240,4369,8738,17476,61440,65280],readHints [969222,4,20491,26112,29716,25615]),([7,240,4369,8738,17476,61440,65520],readHints [969734,3,20491,2565,29716,25615]),([7,240,4369,8738,34952,61440,61455],readHints [970241,3,206344,26117]),([7,240,4369,8738,34952,61440,61695],readHints [970753,4,20488,2560]),([7,240,4369,8738,34952,61440,65280],readHints [971270,4,20488,26112,29716,25615]),([7,240,4369,8738,34952,61440,65520],readHints [971782,3,20488,2565,29716,25615]),([7,240,4369,8751,17476,34952,61440],readHints [972303,27,8296,972801,3607,4999,15934,17288])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_269 : K_269.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_270 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,4369,8751,17476,61440],readHints [57871,973328,206871]),([7,240,4369,8751,34952,61440],readHints [57871,973860,50750]),([7,240,4369,12066,17476,34952,61440],readHints [974337,4,8267,974848,11279,16265,17290]),([7,240,4369,17476,34952,61440,61455],readHints [975361,3,206343,26117]),([7,240,4369,17476,34952,61440,61695],readHints [975873,4,20487,2560]),([7,240,4369,17476,34952,61440,65280],readHints [976390,4,20487,26112,29716]),([7,240,4369,17476,34952,61440,65520],readHints [976902,3,20487,2565,29716]),([7,240,4383,8738,17476,34952,61440],readHints [977428,55,8354,977921,978480])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_270 : K_270.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_271 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,7953,8738,17476,34952,61440],readHints [978945,4,8267,3584,4628,11659,15987,17292]),([7,240,7953,8738,17476,61440],readHints [57857,979537,206848,207404]),([7,240,7953,8738,34952,61440],readHints [57857,199228,50700,207404]),([7,240,8738,8751,17476,34952,61440],readHints [979983,27,56841,3607,11265]),([7,240,8738,12066,17476,34952,61440],readHints [980481,4,56841,3584,11279]),([7,240,8738,17476,34952,61440,61455],readHints [980993,3,2057,26117]),([7,240,8738,17476,34952,61440,61695],readHints [981505,4,2057,2560]),([7,240,8738,17476,34952,61440,65280],readHints [982022,4,2057,26112,29711])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_271 : K_271.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_272 : List (List ℕ × List (ℕ × ℕ)) := [([7,240,8738,17476,34952,61440,65520],readHints [982534,3,2057,2565,29711]),([7,3840,3855,4369,8738,17476,61440],readHints [983051,512,1033,983556,52226,21013,15374,12300,7175,7688]),([7,3840,3855,4369,8738,34952,61440],readHints [984072,512,1037,1543,14355,201740,4612]),([7,3840,3855,4369,17476,34952,61440],readHints [984583,512,1034,1544,197124,32770]),([7,3840,3855,8738,17476,34952,61440],readHints [985097,512,1026,1548,2059,6154,51213,4612]),([7,3840,4080,4369,8738,17476,61440],readHints [985601,5,516,14859,3587,4608]),([7,3840,4080,4369,8738,34952,61440],readHints [986113,5,516,14856,3587,4608]),([7,3840,4080,4369,17476,34952,61440],readHints [986625,5,516,14855,3587,4608])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_272 : K_272.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_273 : List (List ℕ × List (ℕ × ℕ)) := [([7,3840,4080,8738,17476,34952,61440],readHints [987137,5,516,8201,3587,4608]),([7,3840,4369,8738,17476,17487,61440],readHints [987652,46,521,2048,5131,6160,7182,3617]),([7,3840,4369,8738,17476,17652,61440],readHints [988161,114176,3590]),([7,3840,4369,8738,17476,61440,61455],readHints [988676,5,989185,26115]),([7,3840,4369,8738,17476,61440,61680],readHints [989696,8203,3589,11285]),([7,3840,4369,8738,17476,61440,65295],readHints [990212,22529,27334]),([7,3840,4369,8738,17476,61440,65520],readHints [990720,8203,27247]),([7,3840,4369,8738,17487,34952,61440],readHints [991236,46,1536,18829,8776,24686,991777,3081])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_273 : K_273.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_274 : List (List ℕ × List (ℕ × ℕ)) := [([7,3840,4369,8738,17487,61440],readHints [112644,992270,992801,196767]),([7,3840,4369,8738,17652,34952,61440],readHints [993281,114176,3590,4863,28229]),([7,3840,4369,8738,34952,61440,61455],readHints [993796,5,994305,26115,30728]),([7,3840,4369,8738,34952,61440,61680],readHints [994816,113160,3589]),([7,3840,4369,8738,34952,61440,65295],readHints [995332,995841]),([7,3840,4369,8738,34952,61440,65520],readHints [996352,8200,27296]),([7,3840,4369,17476,17487,34952,61440],readHints [996868,46,522,1536,997378,26145]),([7,3840,4369,17476,17652,34952,61440],readHints [997889,114176,3590])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_274 : K_274.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_275 : List (List ℕ × List (ℕ × ℕ)) := [([7,3840,4369,17476,34952,61440,61455],readHints [998404,5,998913,26115,30727]),([7,3840,4369,17476,34952,61440,61680],readHints [999424,113671,3589]),([7,3840,4369,17476,34952,61440,65295],readHints [999940,8193]),([7,3840,4369,17476,34952,61440,65520],readHints [1000448,8199]),([7,3840,4369,17487,34952,61440],readHints [1000964,1001474,67110,1002056]),([7,3840,8738,17476,17487,34952,61440],readHints [1002505,46,514,1536,2059,26145,3082,1003012]),([7,3840,8738,17476,17652,34952,61440],readHints [1003521,72713,3590,15872]),([7,3840,8738,17476,34952,61440,61455],readHints [1004036,5,1004545,26115])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_275 : K_275.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_276 : List (List ℕ × List (ℕ × ℕ)) := [([7,3840,8738,17476,34952,61440,61680],readHints [1005056,8201,3589]),([7,3840,8738,17476,34952,61440,65295],readHints [1005572,8193]),([7,3840,8738,17476,34952,61440,65520],readHints [1006080,8201]),([7,3840,8738,17652,34952,61440],readHints [86017,109637,43052,39310]),([8,15,240,3840,4369,8738,17476],readHints [1006603,1007121,203389,42059]),([8,15,240,3840,4369,8738,17476,34952],readHints [1007633,1,1030,1008203,1008643,43555,5150,21098,1009161,1009671,3123,41074,23554,7178,1010184,1010700,15885,1011325,1011723]),([8,15,240,3840,4369,8738,17476,34952,61440],readHints [204323,193130,1012233,1012780,84594,106498,1013249,65548,1013766,177789,1014279,1014792,1015307]),([8,15,240,3840,4369,8738,17476,61440],readHints [1015819,1545,207873,208390,18557,13328,24108,15381,23554,42510,19468,16903,16392])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_276 : K_276.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_277 : List (List ℕ × List (ℕ × ℕ)) := [([8,15,240,3840,4369,8738,34952],readHints [208904,209420,38929]),([8,15,240,3840,4369,8738,34952,61440],readHints [1016328,1549,2055,207873,208390,9238,9747,1016844,24108]),([8,15,240,3840,4369,17476,34952],readHints [208903,209410,38929]),([8,15,240,3840,4369,17476,34952,61440],readHints [1017351,1546,2056,209921,210438,1017858]),([8,15,240,3840,8738,17476,34952],readHints [1018377,1018893,1019498,114698]),([8,15,240,3840,8738,17476,34952,61440],readHints [1019913,1538,2060,8203,209921,210438,17964,1020429,28266,15882]),([8,15,240,4369,8738,17476,34952,61440],readHints [1020934,515,210961,4116,5647,1021441,1021957,211465,211975]),([8,15,240,4369,8738,17476,61440],readHints [87046,1022475,212485])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_277 : K_277.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_278 : List (List ℕ × List (ℕ × ℕ)) := [([8,15,240,4369,8738,34952,61440],readHints [87046,1022984,87564]),([8,15,240,4369,17476,34952,61440],readHints [88070,115207,87554]),([8,15,240,8738,17476,34952,61440],readHints [88070,1023497,114701]),([8,15,3840,4369,8738,17476,34952,61440],readHints [1024003,0,517,1024516,33315,1025033,1025543,17410,8714,1026056,112140,6157,1026571,1027089]),([8,15,3840,4369,8738,17476,61440],readHints [1027595,1028099,67076]),([8,15,3840,4369,8738,34952,61440],readHints [213000,213516,41987]),([8,15,3840,4369,17476,34952,61440],readHints [212999,213506,41987]),([8,15,3840,8738,17476,34952,61440],readHints [1028617,1029133,38922])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_278 : K_278.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_279 : List (List ℕ × List (ℕ × ℕ)) := [([8,240,3840,4369,8738,17476,34952,61440],readHints [1029633,4,211019,1030144,1030662,211465,212012]),([8,240,3840,4369,8738,17476,61440],readHints [87041,1031179,212480,214060]),([8,240,3840,4369,8738,34952,61440],readHints [87041,115208,87564,214060]),([8,240,3840,4369,17476,34952,61440],readHints [88065,115207,87554]),([8,240,3840,8738,17476,34952,61440],readHints [88065,1031689,1032236,114701])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_279 : K_279.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = (((((((((K_0 ++ K_1) ++ (K_2 ++ K_3)) ++ ((K_4 ++ K_5) ++ (K_6 ++ K_7))) ++ (((K_8 ++ K_9) ++ (K_10 ++ K_11)) ++ ((K_12 ++ K_13) ++ (K_14 ++ (K_15 ++ K_16))))) ++ ((((K_17 ++ K_18) ++ (K_19 ++ K_20)) ++ ((K_21 ++ K_22) ++ (K_23 ++ (K_24 ++ K_25)))) ++ (((K_26 ++ K_27) ++ (K_28 ++ K_29)) ++ ((K_30 ++ K_31) ++ (K_32 ++ (K_33 ++ K_34)))))) ++ (((((K_35 ++ K_36) ++ (K_37 ++ K_38)) ++ ((K_39 ++ K_40) ++ (K_41 ++ K_42))) ++ (((K_43 ++ K_44) ++ (K_45 ++ K_46)) ++ ((K_47 ++ K_48) ++ (K_49 ++ (K_50 ++ K_51))))) ++ ((((K_52 ++ K_53) ++ (K_54 ++ K_55)) ++ ((K_56 ++ K_57) ++ (K_58 ++ (K_59 ++ K_60)))) ++ (((K_61 ++ K_62) ++ (K_63 ++ K_64)) ++ ((K_65 ++ K_66) ++ (K_67 ++ (K_68 ++ K_69))))))) ++ ((((((K_70 ++ K_71) ++ (K_72 ++ K_73)) ++ ((K_74 ++ K_75) ++ (K_76 ++ K_77))) ++ (((K_78 ++ K_79) ++ (K_80 ++ K_81)) ++ ((K_82 ++ K_83) ++ (K_84 ++ (K_85 ++ K_86))))) ++ ((((K_87 ++ K_88) ++ (K_89 ++ K_90)) ++ ((K_91 ++ K_92) ++ (K_93 ++ (K_94 ++ K_95)))) ++ (((K_96 ++ K_97) ++ (K_98 ++ K_99)) ++ ((K_100 ++ K_101) ++ (K_102 ++ (K_103 ++ K_104)))))) ++ (((((K_105 ++ K_106) ++ (K_107 ++ K_108)) ++ ((K_109 ++ K_110) ++ (K_111 ++ K_112))) ++ (((K_113 ++ K_114) ++ (K_115 ++ K_116)) ++ ((K_117 ++ K_118) ++ (K_119 ++ (K_120 ++ K_121))))) ++ ((((K_122 ++ K_123) ++ (K_124 ++ K_125)) ++ ((K_126 ++ K_127) ++ (K_128 ++ (K_129 ++ K_130)))) ++ (((K_131 ++ K_132) ++ (K_133 ++ K_134)) ++ ((K_135 ++ K_136) ++ (K_137 ++ (K_138 ++ K_139)))))))) ++ (((((((K_140 ++ K_141) ++ (K_142 ++ K_143)) ++ ((K_144 ++ K_145) ++ (K_146 ++ K_147))) ++ (((K_148 ++ K_149) ++ (K_150 ++ K_151)) ++ ((K_152 ++ K_153) ++ (K_154 ++ (K_155 ++ K_156))))) ++ ((((K_157 ++ K_158) ++ (K_159 ++ K_160)) ++ ((K_161 ++ K_162) ++ (K_163 ++ (K_164 ++ K_165)))) ++ (((K_166 ++ K_167) ++ (K_168 ++ K_169)) ++ ((K_170 ++ K_171) ++ (K_172 ++ (K_173 ++ K_174)))))) ++ (((((K_175 ++ K_176) ++ (K_177 ++ K_178)) ++ ((K_179 ++ K_180) ++ (K_181 ++ K_182))) ++ (((K_183 ++ K_184) ++ (K_185 ++ K_186)) ++ ((K_187 ++ K_188) ++ (K_189 ++ (K_190 ++ K_191))))) ++ ((((K_192 ++ K_193) ++ (K_194 ++ K_195)) ++ ((K_196 ++ K_197) ++ (K_198 ++ (K_199 ++ K_200)))) ++ (((K_201 ++ K_202) ++ (K_203 ++ K_204)) ++ ((K_205 ++ K_206) ++ (K_207 ++ (K_208 ++ K_209))))))) ++ ((((((K_210 ++ K_211) ++ (K_212 ++ K_213)) ++ ((K_214 ++ K_215) ++ (K_216 ++ K_217))) ++ (((K_218 ++ K_219) ++ (K_220 ++ K_221)) ++ ((K_222 ++ K_223) ++ (K_224 ++ (K_225 ++ K_226))))) ++ ((((K_227 ++ K_228) ++ (K_229 ++ K_230)) ++ ((K_231 ++ K_232) ++ (K_233 ++ (K_234 ++ K_235)))) ++ (((K_236 ++ K_237) ++ (K_238 ++ K_239)) ++ ((K_240 ++ K_241) ++ (K_242 ++ (K_243 ++ K_244)))))) ++ (((((K_245 ++ K_246) ++ (K_247 ++ K_248)) ++ ((K_249 ++ K_250) ++ (K_251 ++ K_252))) ++ (((K_253 ++ K_254) ++ (K_255 ++ K_256)) ++ ((K_257 ++ K_258) ++ (K_259 ++ (K_260 ++ K_261))))) ++ ((((K_262 ++ K_263) ++ (K_264 ++ K_265)) ++ ((K_266 ++ K_267) ++ (K_268 ++ (K_269 ++ K_270)))) ++ (((K_271 ++ K_272) ++ (K_273 ++ K_274)) ++ ((K_275 ++ K_276) ++ (K_277 ++ (K_278 ++ K_279)))))))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app (all_app (all_app (all_app c_0 c_1) (all_app c_2 c_3)) (all_app (all_app c_4 c_5) (all_app c_6 c_7))) (all_app (all_app (all_app c_8 c_9) (all_app c_10 c_11)) (all_app (all_app c_12 c_13) (all_app c_14 (all_app c_15 c_16))))) (all_app (all_app (all_app (all_app c_17 c_18) (all_app c_19 c_20)) (all_app (all_app c_21 c_22) (all_app c_23 (all_app c_24 c_25)))) (all_app (all_app (all_app c_26 c_27) (all_app c_28 c_29)) (all_app (all_app c_30 c_31) (all_app c_32 (all_app c_33 c_34)))))) (all_app (all_app (all_app (all_app (all_app c_35 c_36) (all_app c_37 c_38)) (all_app (all_app c_39 c_40) (all_app c_41 c_42))) (all_app (all_app (all_app c_43 c_44) (all_app c_45 c_46)) (all_app (all_app c_47 c_48) (all_app c_49 (all_app c_50 c_51))))) (all_app (all_app (all_app (all_app c_52 c_53) (all_app c_54 c_55)) (all_app (all_app c_56 c_57) (all_app c_58 (all_app c_59 c_60)))) (all_app (all_app (all_app c_61 c_62) (all_app c_63 c_64)) (all_app (all_app c_65 c_66) (all_app c_67 (all_app c_68 c_69))))))) (all_app (all_app (all_app (all_app (all_app (all_app c_70 c_71) (all_app c_72 c_73)) (all_app (all_app c_74 c_75) (all_app c_76 c_77))) (all_app (all_app (all_app c_78 c_79) (all_app c_80 c_81)) (all_app (all_app c_82 c_83) (all_app c_84 (all_app c_85 c_86))))) (all_app (all_app (all_app (all_app c_87 c_88) (all_app c_89 c_90)) (all_app (all_app c_91 c_92) (all_app c_93 (all_app c_94 c_95)))) (all_app (all_app (all_app c_96 c_97) (all_app c_98 c_99)) (all_app (all_app c_100 c_101) (all_app c_102 (all_app c_103 c_104)))))) (all_app (all_app (all_app (all_app (all_app c_105 c_106) (all_app c_107 c_108)) (all_app (all_app c_109 c_110) (all_app c_111 c_112))) (all_app (all_app (all_app c_113 c_114) (all_app c_115 c_116)) (all_app (all_app c_117 c_118) (all_app c_119 (all_app c_120 c_121))))) (all_app (all_app (all_app (all_app c_122 c_123) (all_app c_124 c_125)) (all_app (all_app c_126 c_127) (all_app c_128 (all_app c_129 c_130)))) (all_app (all_app (all_app c_131 c_132) (all_app c_133 c_134)) (all_app (all_app c_135 c_136) (all_app c_137 (all_app c_138 c_139)))))))) (all_app (all_app (all_app (all_app (all_app (all_app (all_app c_140 c_141) (all_app c_142 c_143)) (all_app (all_app c_144 c_145) (all_app c_146 c_147))) (all_app (all_app (all_app c_148 c_149) (all_app c_150 c_151)) (all_app (all_app c_152 c_153) (all_app c_154 (all_app c_155 c_156))))) (all_app (all_app (all_app (all_app c_157 c_158) (all_app c_159 c_160)) (all_app (all_app c_161 c_162) (all_app c_163 (all_app c_164 c_165)))) (all_app (all_app (all_app c_166 c_167) (all_app c_168 c_169)) (all_app (all_app c_170 c_171) (all_app c_172 (all_app c_173 c_174)))))) (all_app (all_app (all_app (all_app (all_app c_175 c_176) (all_app c_177 c_178)) (all_app (all_app c_179 c_180) (all_app c_181 c_182))) (all_app (all_app (all_app c_183 c_184) (all_app c_185 c_186)) (all_app (all_app c_187 c_188) (all_app c_189 (all_app c_190 c_191))))) (all_app (all_app (all_app (all_app c_192 c_193) (all_app c_194 c_195)) (all_app (all_app c_196 c_197) (all_app c_198 (all_app c_199 c_200)))) (all_app (all_app (all_app c_201 c_202) (all_app c_203 c_204)) (all_app (all_app c_205 c_206) (all_app c_207 (all_app c_208 c_209))))))) (all_app (all_app (all_app (all_app (all_app (all_app c_210 c_211) (all_app c_212 c_213)) (all_app (all_app c_214 c_215) (all_app c_216 c_217))) (all_app (all_app (all_app c_218 c_219) (all_app c_220 c_221)) (all_app (all_app c_222 c_223) (all_app c_224 (all_app c_225 c_226))))) (all_app (all_app (all_app (all_app c_227 c_228) (all_app c_229 c_230)) (all_app (all_app c_231 c_232) (all_app c_233 (all_app c_234 c_235)))) (all_app (all_app (all_app c_236 c_237) (all_app c_238 c_239)) (all_app (all_app c_240 c_241) (all_app c_242 (all_app c_243 c_244)))))) (all_app (all_app (all_app (all_app (all_app c_245 c_246) (all_app c_247 c_248)) (all_app (all_app c_249 c_250) (all_app c_251 c_252))) (all_app (all_app (all_app c_253 c_254) (all_app c_255 c_256)) (all_app (all_app c_257 c_258) (all_app c_259 (all_app c_260 c_261))))) (all_app (all_app (all_app (all_app c_262 c_263) (all_app c_264 c_265)) (all_app (all_app c_266 c_267) (all_app c_268 (all_app c_269 c_270)))) (all_app (all_app (all_app c_271 c_272) (all_app c_273 c_274)) (all_app (all_app c_275 c_276) (all_app c_277 (all_app c_278 c_279)))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 8 ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 4 => (4702 : ℕ).testBit (4 * u.val + v.val)) C :=
  signed_rep_lb 4702 8 1 0 PD_ PM_ XS_ G_ T_cert (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel)

end PEqualNP.Outside.L_meta_19053_Negation

theorem PEqualNP.Outside.L_meta_19053_Negation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4702 : ℕ).testBit (4 * u.val + v.val)) C) :=
  PEqualNP.Outside.L_meta_19053_Negation.lower
