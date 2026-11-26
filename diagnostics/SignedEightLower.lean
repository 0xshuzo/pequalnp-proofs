import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20532.Lower

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



def pairCode (p : Fin 3 × Fin 5) : Nat := 2 ^ p.1.val ||| 2 ^ (3 + p.2.val)
def reference (x : Fin 8 → Bool) : Bool :=
  x 3 || (x 0 && (x 5 || x 7)) || (x 1 && (x 4 || x 6)) || (x 2 && (x 4 || x 5))
def pairInput (i : Fin 3) (j : Fin 5) := oneEach i j
theorem codeInputs : ∀ p : Fin 3 × Fin 5, List.ofFn (pt 8 (pairCode p)) = pairInput p.1 p.2 := by
  decide +kernel
theorem graphRow : ∀ (i : Fin 3) (j : Fin 5), reference (pt 8 (pairCode (i,j))) =
    (7541 : ℕ).testBit (5 * i.val + j.val) := by decide +kernel
def samplePairs : List (Fin 3 × Fin 5) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def M_ : ℕ := 32767

def Y_ : ℕ := 7541

def XS_ : List ℕ := [63, 1986, 30852, 233736, 860688, 1715376]

def PD_ : List (ℕ × ℕ) := [(1, 5071), (2, 6696), (3, 3803), (4, 1186), (5, 414), (6, 256), (7, 79), (8, 104), (9, 59), (10, 18), (11, 6), (12, 4), (13, 1), (14, 1)]

def PM_ : List (ℕ × ℕ) := [(1, 7541), (3, 7541), (7, 7541), (9, 7541), (13, 7541), (14, 7541)]

def G_ : List (List ℕ) := [[5,7,6,9,8,0,2,1,4,3,10,12,11,14,13]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,1077,2114,5092,32008] BT.lf) [3,1333,2114,5092,31744] BT.lf) [3,7167,11242,21151] (BT.nd BT.lf [3,10570,13375] BT.lf)) [4,10,9192,16912,31876] (BT.nd (BT.nd (BT.nd BT.lf [4,20,1057,2114,5092,32008] BT.lf) [4,31,992,8458,17040] BT.lf) [4,31,1057,2114,5108,32008] (BT.nd BT.lf [4,31,1073,2114,5092,32008] BT.lf))) [4,31,1377,2114,4228,32272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,31,2114,6117,16912,32041] BT.lf) [4,31,3171,5092,16912,32041] BT.lf) [4,31,3171,5092,17969,32008] (BT.nd BT.lf [4,31,3171,6117,16912,32008] BT.lf)) [4,31,8456,17055,31810] (BT.nd (BT.nd BT.lf [4,31,9194,16912,31876] BT.lf) [4,31,10570,13345] (BT.nd BT.lf [4,138,9192,16912,31744] BT.lf)))) [4,276,1057,2114,5092,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1057,2114,5108,8479,31744] BT.lf) [4,1057,2143,5092,8456,31760] BT.lf) [4,1057,2143,5092,32008,32272] (BT.nd BT.lf [4,1057,2143,5108,8456,31744] BT.lf)) [4,1057,10570,12319] (BT.nd (BT.nd (BT.nd BT.lf [4,1057,10570,19424] BT.lf) [4,1073,2114,5092,8479,31744] BT.lf) [4,1073,2143,5092,8456,31744] (BT.nd BT.lf [4,1077,2114,5092,8456,31744] BT.lf))) [4,1087,2114,5092,17969,32008] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1087,2114,6117,16912,32008] BT.lf) [4,1087,8456,14402] BT.lf) [4,1087,10570,12288] (BT.nd BT.lf [4,1087,10570,19442] BT.lf)) [4,2114,4228,9535,18417,31744] (BT.nd (BT.nd BT.lf [4,2114,5092,9535,17969,31744] BT.lf) [4,2114,5119,9192,21151] (BT.nd BT.lf [4,2114,5285,8479,17392,31777] BT.lf))))) [4,2114,5285,9535,17392,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2114,6117,8479,16912,31777] BT.lf) [4,2114,6117,9535,16912,31744] BT.lf) [4,2114,8456,13375] (BT.nd BT.lf [4,2114,9192,16927,31872] BT.lf)) [4,2114,9192,17055,31744] (BT.nd (BT.nd (BT.nd BT.lf [4,2143,5092,9513,17969,31744] BT.lf) [4,2143,5285,8456,17392,31777] BT.lf) [4,2143,5285,9513,17392,31744] (BT.nd BT.lf [4,2143,6117,8456,16912,31777] BT.lf))) [4,2143,6117,9513,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,3042,4255,11242,21151] BT.lf) [4,3042,5119,8456,21151] BT.lf) [4,3042,7167,8456,21151] (BT.nd BT.lf [4,3042,8456,17055,31744] BT.lf)) [4,3171,5285,8479,17392,31744] (BT.nd (BT.nd BT.lf [4,3171,6117,8479,16912,31744] BT.lf) [4,3199,6117,8456,16912,31744] (BT.nd BT.lf [4,8479,18417,21140] BT.lf)))) [4,9192,16927,31810,31876] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2,31,992,8456,17040] BT.lf) [5,2,31,9192,16912,31876] BT.lf) [5,2,992,9192,16912,31876] (BT.nd BT.lf [5,2,4228,9192,16927,31744] BT.lf)) [5,2,4255,9192,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [5,10,992,8456,16912,31876] BT.lf) [5,10,4228,9192,16912,31744] BT.lf) [5,16,31,1057,2114,5092,32008] (BT.nd BT.lf [5,16,1057,2114,5092,8479,31744] BT.lf))) [5,16,1057,2143,5092,8456,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,20,992,1057,2114,4228,32008] BT.lf) [5,20,1057,2114,5092,8456,31744] BT.lf) [5,31,130,992,8456,16912] (BT.nd BT.lf [5,31,130,3042,8456,16912] BT.lf)) [5,31,159,8456,16912,31810] (BT.nd (BT.nd BT.lf [5,31,891,2114,9192,16912] BT.lf) [5,31,992,1057,2114,4244,32008] (BT.nd BT.lf [5,31,992,1073,2114,4228,32008] BT.lf)))))) [5,31,992,2114,5285,8456,32305] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,992,2114,5285,9513,32272] BT.lf) [5,31,992,2114,5285,16912,32041] BT.lf) [5,31,992,2114,5285,17969,32008] (BT.nd BT.lf [5,31,992,2114,8456,17055] BT.lf)) [5,31,992,3171,5285,8456,32272] (BT.nd (BT.nd (BT.nd BT.lf [5,31,992,8456,17040,31810] BT.lf) [5,31,994,8456,16912,31876] BT.lf) [5,31,1008,1057,2114,4228,32008] (BT.nd BT.lf [5,31,1057,2114,5092,8456,31760] BT.lf))) [5,31,1057,2114,5092,16912,32000] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,1057,2114,5092,16912,32008] BT.lf) [5,31,1057,2114,5092,16912,32041] BT.lf) [5,31,1057,2114,5092,17392,32008] (BT.nd BT.lf [5,31,1057,2114,5092,17969,32008] BT.lf)) [5,31,1057,2114,5092,21140,32008] (BT.nd (BT.nd BT.lf [5,31,1057,2114,5092,21492,32008] BT.lf) [5,31,1057,2114,5092,32008,32272] (BT.nd BT.lf [5,31,1057,2114,5108,8456,31744] BT.lf)))) [5,31,1057,2114,6117,16912,32008] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,1057,2370,4228,17392,31744] BT.lf) [5,31,1057,2370,5092,16912,31744] BT.lf) [5,31,1057,2543,4228] (BT.nd BT.lf [5,31,1057,3171,5092,16912,32008] BT.lf)) [5,31,1057,4228,29200] (BT.nd (BT.nd (BT.nd BT.lf [5,31,1057,4228,30224] BT.lf) [5,31,1057,6276,32272] BT.lf) [5,31,1057,6342,32338] (BT.nd BT.lf [5,31,1057,8456,14402] BT.lf))) [5,31,1057,8456,15426] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,1057,8456,17341] BT.lf) [5,31,1057,10570,12288] BT.lf) [5,31,1057,10570,19442] (BT.nd BT.lf [5,31,1057,12288,21140] BT.lf)) [5,31,1057,19442,21140] (BT.nd (BT.nd BT.lf [5,31,1057,24840,31810] BT.lf) [5,31,1057,25368,32338] (BT.nd BT.lf [5,31,1073,2114,5092,8456,31744] BT.lf))))) [5,31,1313,2114,4228,17392,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,1313,2114,5092,16912,31744] BT.lf) [5,31,1377,2114,4228,16912,31744] BT.lf) [5,31,2017,2114,4228,9513,32272] (BT.nd BT.lf [5,31,2017,2114,4228,16912,32041] BT.lf)) [5,31,2017,3171,4228,8456,32272] (BT.nd (BT.nd (BT.nd BT.lf [5,31,2017,3171,4228,16912,32008] BT.lf) [5,31,2017,4228,25104] BT.lf) [5,31,2017,6276,16912] (BT.nd BT.lf [5,31,2017,6342,19026] BT.lf))) [5,31,2017,6342,21140] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,2017,12684,21140] BT.lf) [5,31,2017,12684,25368] BT.lf) [5,31,2017,19026,21140] (BT.nd BT.lf [5,31,2017,21140,25368] BT.lf)) [5,31,2114,4228,9513,18417,31744] (BT.nd (BT.nd BT.lf [5,31,2114,5092,9513,17969,31744] BT.lf) [5,31,2114,5285,8456,17392,31777] (BT.nd BT.lf [5,31,2114,5285,9513,17392,31744] BT.lf)))) [5,31,2114,5285,32305] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,2114,6117,8456,16912,31777] BT.lf) [5,31,2114,6117,9513,16912,31744] BT.lf) [5,31,2114,8456,13345] (BT.nd BT.lf [5,31,2114,8456,15393] BT.lf)) [5,31,2114,8456,15407] (BT.nd (BT.nd BT.lf [5,31,2114,8456,17055,31744] BT.lf) [5,31,2114,8456,17296] (BT.nd BT.lf [5,31,2114,8456,17360] BT.lf))) [5,31,2114,8456,17374] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,2114,8456,17392,32404] BT.lf) [5,31,2114,8488,17392] BT.lf) [5,31,2114,9192,15855,31876] (BT.nd BT.lf [5,31,2114,9192,16912,31872] BT.lf)) [5,31,2114,9192,16912,31876] (BT.nd (BT.nd BT.lf [5,31,2114,9192,16927,31876] BT.lf) [5,31,2114,9192,17040,31744] (BT.nd BT.lf [5,31,2114,9513,18417] BT.lf))))))) [5,31,2114,11242,16912,31876] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,2114,16912,23575,31876] BT.lf) [5,31,2114,18417,21140] BT.lf) [5,31,2114,24840,31777] (BT.nd BT.lf [5,31,2114,25368,32305] BT.lf)) [5,31,2146,8456,17392] (BT.nd (BT.nd (BT.nd BT.lf [5,31,3042,4228,11242,16927] BT.lf) [5,31,3042,4255,11242,16912] BT.lf) [5,31,3042,5285,17969] (BT.nd BT.lf [5,31,3042,5285,21140] BT.lf))) [5,31,3042,8456,17040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,3042,8456,17040,31744] BT.lf) [5,31,3042,9192,16912,31876] BT.lf) [5,31,3042,12684,21140] (BT.nd BT.lf [5,31,3042,12684,25368] BT.lf)) [5,31,3042,17969,21140] (BT.nd (BT.nd BT.lf [5,31,3042,21140,25368] BT.lf) [5,31,3071,4228,11242,16912] (BT.nd BT.lf [5,31,3105,4228,32272] BT.lf)))) [5,31,3171,4228,8456,17392,31777] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,3171,4228,8456,18417,31744] BT.lf) [5,31,3171,4228,9513,17392,31744] BT.lf) [5,31,3171,4228,32305] (BT.nd BT.lf [5,31,3171,4228,32338] BT.lf)) [5,31,3171,5092,8456,16912,31777] (BT.nd (BT.nd (BT.nd BT.lf [5,31,3171,5092,8456,17969,31744] BT.lf) [5,31,3171,5092,9513,16912,31744] BT.lf) [5,31,3171,5285,8456,17392,31744] (BT.nd BT.lf [5,31,3171,5285,32272] BT.lf))) [5,31,3171,6117,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,3171,6342,32272] BT.lf) [5,31,3171,8456,18417] BT.lf) [5,31,3171,8456,19442] (BT.nd BT.lf [5,31,3171,9513,17392] BT.lf)) [5,31,3171,10570,17392] (BT.nd (BT.nd BT.lf [5,31,4065,4228,16912] BT.lf) [5,31,4228,9192,16912,31746] (BT.nd BT.lf [5,31,4228,9194,16912,31744] BT.lf))))) [5,31,4228,25104,31777] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,4228,25368,32305] BT.lf) [5,31,4228,25368,32338] BT.lf) [5,31,5285,6342,32272] (BT.nd BT.lf [5,31,8456,16912,31842] BT.lf)) [5,31,8456,17040,31810] (BT.nd (BT.nd (BT.nd BT.lf [5,31,8456,18417,21140] BT.lf) [5,31,8456,19442,21140] BT.lf) [5,31,8488,16912,31810] (BT.nd BT.lf [5,31,9192,10570,16912,31876] BT.lf))) [5,31,9192,11242,16912,31876] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,9192,16912,30653,31876] BT.lf) [5,31,9192,16912,31810,31876] BT.lf) [5,31,9513,10570,17392] (BT.nd BT.lf [5,31,9513,17969,31810] BT.lf)) [5,31,9513,25368,31810] (BT.nd (BT.nd BT.lf [5,31,10570,19026,31777] BT.lf) [5,31,10570,25368,31777] (BT.nd BT.lf [5,31,12684,21140,31777] BT.lf)))) [5,31,12684,21140,31810] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,31,12684,25368,31777] BT.lf) [5,31,12684,25368,31810] BT.lf) [5,31,17969,25368,31810] (BT.nd BT.lf [5,31,19026,25368,31777] BT.lf)) [5,31,21140,25368,31777] (BT.nd (BT.nd (BT.nd BT.lf [5,31,21140,25368,31810] BT.lf) [5,63,2114,8456,17392] BT.lf) [5,63,8456,16912,31810] (BT.nd BT.lf [5,130,3042,4255,8456,16912] BT.lf))) [5,159,2114,9192,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,159,3042,8456,16912] BT.lf) [5,159,3042,8456,16912,31744] BT.lf) [5,287,1057,2114,4228,17392,31744] (BT.nd BT.lf [5,287,1057,2114,5092,16912,31744] BT.lf)) [5,1023,2114,4228,9192,16927] (BT.nd (BT.nd BT.lf [5,1023,2114,4255,9192,16912] BT.lf) [5,1023,3042,4255,8456,16912] (BT.nd BT.lf [5,1057,1087,2114,5092,16912,32008] BT.lf)))))) [5,1057,2079,4228,32272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1057,2114,2143,5092,16912,32008] BT.lf) [5,1057,2114,4228,8479,17392,31744] BT.lf) [5,1057,2114,4228,8479,17392,31777] (BT.nd BT.lf [5,1057,2114,4228,8479,17392,32008] BT.lf)) [5,1057,2114,4228,8479,18417,31744] (BT.nd (BT.nd (BT.nd BT.lf [5,1057,2114,4228,8479,21492,31744] BT.lf) [5,1057,2114,5092,8479,16912,31744] BT.lf) [5,1057,2114,5092,8479,16912,31777] (BT.nd BT.lf [5,1057,2114,5092,8479,16912,32008] BT.lf))) [5,1057,2114,5092,8479,17392,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1057,2114,5092,8479,17969,31744] BT.lf) [5,1057,2114,5092,8479,21140,31744] BT.lf) [5,1057,2114,5092,8479,21492,31744] (BT.nd BT.lf [5,1057,2114,5092,9535,16912,31744] BT.lf)) [5,1057,2114,5092,10591,16912,31744] (BT.nd (BT.nd BT.lf [5,1057,2114,5285,8479,17392,31744] BT.lf) [5,1057,2114,6117,8479,16912,31744] (BT.nd BT.lf [5,1057,2114,8456,12319] BT.lf)))) [5,1057,2114,8456,19424] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1057,2143,5092,8456,16912,31744] BT.lf) [5,1057,2143,5092,8456,16912,31777] BT.lf) [5,1057,2143,5092,8456,17392,31744] (BT.nd BT.lf [5,1057,2143,5092,8456,17969,31744] BT.lf)) [5,1057,2143,5092,8456,21140,31744] (BT.nd (BT.nd (BT.nd BT.lf [5,1057,2143,5092,8456,21492,31744] BT.lf) [5,1057,2143,5092,8456,31744,32272] BT.lf) [5,1057,2143,5285,8456,17392,31744] (BT.nd BT.lf [5,1057,2143,6117,8456,16912,31744] BT.lf))) [5,1057,3042,4255,10570] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1057,8456,16415,31810] BT.lf) [5,1057,8479,10570,17392] BT.lf) [5,1087,2017,2114,4228,8456,32272] (BT.nd BT.lf [5,1087,2114,4228,8456,17392,31777] BT.lf)) [5,1087,2114,4228,8456,18417,31744] (BT.nd (BT.nd BT.lf [5,1087,2114,4228,32305] BT.lf) [5,1087,2114,5092,8456,16912,31777] (BT.nd BT.lf [5,1087,2114,5092,8456,17969,31744] BT.lf))))) [5,1087,2114,5285,8456,17392,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1087,2114,5285,32272] BT.lf) [5,1087,2114,6117,8456,16912,31744] BT.lf) [5,1087,2114,8456,12288] (BT.nd BT.lf [5,1087,2114,8456,15360] BT.lf)) [5,1087,2114,8456,15375] (BT.nd (BT.nd (BT.nd BT.lf [5,1087,2114,8456,17376] BT.lf) [5,1087,2114,8456,17392] BT.lf) [5,1087,2114,8456,17407] (BT.nd BT.lf [5,1087,2114,8456,18417] BT.lf))) [5,1087,2114,8456,18431] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1087,2114,8456,19442] BT.lf) [5,1087,2114,10570,17392] BT.lf) [5,1087,2114,17392,24311] (BT.nd BT.lf [5,1087,2114,24840,31744] BT.lf)) [5,1087,2114,25368,32272] (BT.nd (BT.nd BT.lf [5,1087,3042,4228,10570] BT.lf) [5,1087,3042,4228,17969] (BT.nd BT.lf [5,1087,3042,5285,16912] BT.lf)))) [5,1087,3042,10570,16912] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1087,6210,8456,31744] BT.lf) [5,1087,6342,8456,31810] BT.lf) [5,1087,6342,10570,31744] (BT.nd BT.lf [5,1087,6342,12684,31744] BT.lf)) [5,1087,8456,10570,17392] (BT.nd (BT.nd BT.lf [5,1087,8456,16927,31810] BT.lf) [5,1087,8456,17392,30653] (BT.nd BT.lf [5,1087,8456,17969,31810] BT.lf))) [5,1087,10570,12684,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1087,10570,19026,31744] BT.lf) [5,1087,10570,25368,31744] BT.lf) [5,1087,19026,25368,31744] (BT.nd BT.lf [5,2114,4228,9192,15840,31744] BT.lf)) [5,2114,4228,9192,16927,31744] (BT.nd (BT.nd BT.lf [5,2114,4228,9192,16927,31810] BT.lf) [5,2114,4228,9192,21151,31744] (BT.nd BT.lf [5,2114,4255,5119,9192,16912] BT.lf)))))))) [5,2114,4255,9192,15855,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2114,4255,9192,16912,31744] BT.lf) [5,2114,4255,9192,16912,31876] BT.lf) [5,2114,4255,9192,16927,31744] (BT.nd BT.lf [5,2114,4255,9192,21151,31744] BT.lf)) [5,2114,4255,11242,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [5,2114,4255,16912,23575,31744] BT.lf) [5,2114,5183,8456,31744] BT.lf) [5,2114,5311,8456,31807] (BT.nd BT.lf [5,2114,8456,9535,17392] BT.lf))) [5,2114,8456,17392,31680] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2114,9192,16912,16927,31876] BT.lf) [5,2114,9192,16912,21151,31744] BT.lf) [5,2114,9192,16912,28512,31744] (BT.nd BT.lf [5,2114,9192,16912,31876,32736] BT.lf)) [5,2114,9192,16912,31876,32740] (BT.nd (BT.nd BT.lf [5,2114,9192,16927,21140,31744] BT.lf) [5,2114,9192,16927,21151,31744] (BT.nd BT.lf [5,2114,9192,16927,28539,31744] BT.lf)))) [5,2114,9192,16927,31744,31876] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3042,3071,4255,8456,16912] BT.lf) [5,3042,3171,4255,8456] BT.lf) [5,3042,4255,7167,8456,16912] (BT.nd BT.lf [5,3042,4255,8456,15855] BT.lf)) [5,3042,4255,8456,15855,31744] (BT.nd (BT.nd (BT.nd BT.lf [5,3042,4255,8456,16912] BT.lf) [5,3042,4255,8456,16912,31744] BT.lf) [5,3042,4255,8456,16912,31777] (BT.nd BT.lf [5,3042,4255,8456,16912,31810] BT.lf))) [5,3042,4255,8456,16927] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3042,4255,8456,16927,31744] BT.lf) [5,3042,4255,8456,21140] BT.lf) [5,3042,4255,8456,21151] (BT.nd BT.lf [5,3042,4255,8456,21151,31744] BT.lf)) [5,3042,4255,8456,25368] (BT.nd (BT.nd BT.lf [5,3042,8456,12703,16912] BT.lf) [5,3042,8456,16912,21151,31744] (BT.nd BT.lf [5,3042,8456,16912,28512] BT.lf))))) [5,3042,8456,16912,28512,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3042,8456,16927,21140,31744] BT.lf) [5,3042,8456,16927,21151,31744] BT.lf) [5,3042,8456,16927,28539,31744] (BT.nd BT.lf [5,3042,9192,16912,31876] BT.lf)) [5,8456,16912,31807,31909] (BT.nd (BT.nd (BT.nd BT.lf [6,1,992,4228,8479,16912] BT.lf) [6,1,992,8456,16912,31876] BT.lf) [6,2,31,128,992,8456,16912] (BT.nd BT.lf [6,2,31,992,4228,9192,16912] BT.lf))) [6,2,31,992,8456,16912,31876] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2,31,4228,9192,16912,31744] BT.lf) [6,2,992,4228,8456,16927,31744] BT.lf) [6,2,992,4228,9192,16912,31744] (BT.nd BT.lf [6,2,992,4255,8456,16912] BT.lf)) [6,2,992,4255,8456,16912,31744] (BT.nd (BT.nd BT.lf [6,2,992,8456,16912,31876] BT.lf) [6,10,992,4228,8456,16912,31744] (BT.nd BT.lf [6,16,31,992,1057,2114,4228,32008] BT.lf)))) [6,16,31,1057,2114,5092,8456,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,16,992,1057,2114,4228,8479,31744] BT.lf) [6,16,992,1057,2143,4228,8456,31744] BT.lf) [6,18,992,4228,8456,16912] (BT.nd BT.lf [6,20,992,1057,2114,4228,8456,31744] BT.lf)) [6,29,992,4228,8456,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,30,992,4228,8456,16912] BT.lf) [6,30,4228,8456,16912,31744] BT.lf) [6,31,159,992,2114,8456,16912] (BT.nd BT.lf [6,31,159,2114,8456,16912,31744] BT.lf))) [6,31,495,1057,2114,4228] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,891,992,2114,8456,16912] BT.lf) [6,31,957,1057,8456,16912] BT.lf) [6,31,957,4228,8456,16912] (BT.nd BT.lf [6,31,990,2114,8456,16912] BT.lf)) [6,31,990,4228,8456,16912] (BT.nd (BT.nd BT.lf [6,31,992,1057,2114,4228,8456,31760] BT.lf) [6,31,992,1057,2114,4228,8456,32272] (BT.nd BT.lf [6,31,992,1057,2114,4228,8456,32305] BT.lf)))))) [6,31,992,1057,2114,4228,8479,32272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,1057,2114,4228,9513,32272] BT.lf) [6,31,992,1057,2114,4228,10570,32272] BT.lf) [6,31,992,1057,2114,4228,32008,32272] (BT.nd BT.lf [6,31,992,1057,2114,4244,8456,31744] BT.lf)) [6,31,992,1057,2114,5092,16912,32008] (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,1057,2114,5285,8456,32272] BT.lf) [6,31,992,1057,2114,5285,16912,32008] BT.lf) [6,31,992,1057,2114,24840] (BT.nd BT.lf [6,31,992,1057,6210,8456] BT.lf))) [6,31,992,1057,6342,10570] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,1057,6342,12684] BT.lf) [6,31,992,1057,10570,12684] BT.lf) [6,31,992,1057,10570,19026] (BT.nd BT.lf [6,31,992,1057,10570,25368] BT.lf)) [6,31,992,1057,12684,25368] (BT.nd (BT.nd BT.lf [6,31,992,1073,2114,4228,8456,31744] BT.lf) [6,31,992,2114,4228,9192,16927] (BT.nd BT.lf [6,31,992,2114,4228,9513,17969,31744] BT.lf)))) [6,31,992,2114,4255,9192,16912] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,2114,5153,8456] BT.lf) [6,31,992,2114,5285,8456,16912,31777] BT.lf) [6,31,992,2114,5285,8456,17969,31744] (BT.nd BT.lf [6,31,992,2114,5285,9513] BT.lf)) [6,31,992,2114,5285,9513,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,2114,5285,12684] BT.lf) [6,31,992,2114,5285,17969] BT.lf) [6,31,992,2114,5285,21140] (BT.nd BT.lf [6,31,992,2114,8456,15855,31876] BT.lf))) [6,31,992,2114,8456,16912,31872] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,2114,8456,16912,31876] BT.lf) [6,31,992,2114,8456,16912,32404] BT.lf) [6,31,992,2114,8456,16927,31876] (BT.nd BT.lf [6,31,992,2114,8456,17040] BT.lf)) [6,31,992,2114,8456,17040,31744] (BT.nd (BT.nd BT.lf [6,31,992,2114,8488,16912] BT.lf) [6,31,992,2114,9192,16912,31876] (BT.nd BT.lf [6,31,992,2114,9513,12684] BT.lf))))) [6,31,992,2114,9513,17969] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,2114,9513,25368] BT.lf) [6,31,992,2114,10570,16912,31876] BT.lf) [6,31,992,2114,12684,21140] (BT.nd BT.lf [6,31,992,2114,12684,25368] BT.lf)) [6,31,992,2114,16912,24311,31876] (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,2114,17969,21140] BT.lf) [6,31,992,2114,17969,25368] BT.lf) [6,31,992,2114,21140,25368] (BT.nd BT.lf [6,31,992,2146,8456,16912] BT.lf))) [6,31,992,3042,4255,8456,16912] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,3042,8456,16912,31876] BT.lf) [6,31,992,3171,5285,8456] BT.lf) [6,31,992,3171,5285,8456,16912,31744] (BT.nd BT.lf [6,31,992,3171,6342,8456] BT.lf)) [6,31,992,3171,6342,16912] (BT.nd (BT.nd BT.lf [6,31,992,3171,8456,17969] BT.lf) [6,31,992,3171,8456,19026] (BT.nd BT.lf [6,31,992,3171,9513,16912] BT.lf)))) [6,31,992,3171,10570,16912] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,992,6342,8456,19026] BT.lf) [6,31,992,6342,8456,21140] BT.lf) [6,31,992,8456,10570,16912,31876] (BT.nd BT.lf [6,31,992,8456,16912,28539,31810] BT.lf)) [6,31,992,8456,16912,31810,31876] (BT.nd (BT.nd BT.lf [6,31,992,8456,17969,19026] BT.lf) [6,31,992,8456,17969,21140] (BT.nd BT.lf [6,31,992,8456,19026,21140] BT.lf))) [6,31,993,4228,8456,16912] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,994,4228,8456,16912] BT.lf) [6,31,994,4228,8456,16912,31744] BT.lf) [6,31,1008,1057,2114,4228,8456,31744] (BT.nd BT.lf [6,31,1023,2114,4228,9192,16912] BT.lf)) [6,31,1023,3042,4228,8456,16912] (BT.nd (BT.nd BT.lf [6,31,1057,2017,2114,4228,8456,32272] BT.lf) [6,31,1057,2017,2114,4228,16912,32008] (BT.nd BT.lf [6,31,1057,2048,4228,32272] BT.lf))))))) [6,31,1057,2114,4228,5092,8456,32272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,2114,4228,5092,16912,32008] BT.lf) [6,31,1057,2114,4228,8456,17392,31744] BT.lf) [6,31,1057,2114,4228,8456,17392,31777] (BT.nd BT.lf [6,31,1057,2114,4228,8456,17392,32008] BT.lf)) [6,31,1057,2114,4228,8456,17392,32272] (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,2114,4228,8456,18417,31744] BT.lf) [6,31,1057,2114,4228,8456,21492,31744] BT.lf) [6,31,1057,2114,4228,8479,17392,31744] (BT.nd BT.lf [6,31,1057,2114,4228,9513,17392,31744] BT.lf))) [6,31,1057,2114,4228,10570,17392,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,2114,4228,32272] BT.lf) [6,31,1057,2114,4228,32305] BT.lf) [6,31,1057,2114,4228,32338] (BT.nd BT.lf [6,31,1057,2114,5092,8456,16912,31744] BT.lf)) [6,31,1057,2114,5092,8456,16912,31777] (BT.nd (BT.nd BT.lf [6,31,1057,2114,5092,8456,16912,32008] BT.lf) [6,31,1057,2114,5092,8456,17392,31744] (BT.nd BT.lf [6,31,1057,2114,5092,8456,17969,31744] BT.lf)))) [6,31,1057,2114,5092,8456,21140,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,2114,5092,8456,21492,31744] BT.lf) [6,31,1057,2114,5092,8456,31744,32272] BT.lf) [6,31,1057,2114,5092,8479,16912,31744] (BT.nd BT.lf [6,31,1057,2114,5092,9513,16912,31744] BT.lf)) [6,31,1057,2114,5092,10570,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,2114,5092,16912,31744,32008] BT.lf) [6,31,1057,2114,5092,16912,32008] BT.lf) [6,31,1057,2114,5092,32008] (BT.nd BT.lf [6,31,1057,2114,5285,8456,17392,31744] BT.lf))) [6,31,1057,2114,5285,32272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,2114,6117,8456,16912,31744] BT.lf) [6,31,1057,2114,6342,32272] BT.lf) [6,31,1057,2114,8456,12288] (BT.nd BT.lf [6,31,1057,2114,8456,15360] BT.lf)) [6,31,1057,2114,8456,15375] (BT.nd (BT.nd BT.lf [6,31,1057,2114,8456,17376] BT.lf) [6,31,1057,2114,8456,17392] (BT.nd BT.lf [6,31,1057,2114,8456,17407] BT.lf))))) [6,31,1057,2114,8456,18417] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,2114,8456,19442] BT.lf) [6,31,1057,2114,9192,16912,31876] BT.lf) [6,31,1057,2114,9513,17392] (BT.nd BT.lf [6,31,1057,2114,10570,17392] BT.lf)) [6,31,1057,2114,17392,21140] (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,2114,17392,24311] BT.lf) [6,31,1057,2114,24840,31744] BT.lf) [6,31,1057,2114,25368,32272] (BT.nd BT.lf [6,31,1057,2114,28539,32272] BT.lf))) [6,31,1057,2143,4228,8456,17392,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,2143,4228,32272] BT.lf) [6,31,1057,2143,5092,8456,16912,31744] BT.lf) [6,31,1057,3040,4228,16912] (BT.nd BT.lf [6,31,1057,3042,4228,10570] BT.lf)) [6,31,1057,3042,4228,15855] (BT.nd (BT.nd BT.lf [6,31,1057,3042,4228,16912] BT.lf) [6,31,1057,3042,4228,17969] (BT.nd BT.lf [6,31,1057,3042,4228,21140] BT.lf)))) [6,31,1057,3042,5285,16912] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,3042,10570,16912] BT.lf) [6,31,1057,3042,16912,21140] BT.lf) [6,31,1057,3042,16912,28539] (BT.nd BT.lf [6,31,1057,3071,4228,16912] BT.lf)) [6,31,1057,3171,4228,8456,17392,31744] (BT.nd (BT.nd BT.lf [6,31,1057,3171,4228,32272] BT.lf) [6,31,1057,3171,5092,8456,16912,31744] (BT.nd BT.lf [6,31,1057,3171,8456,17392] BT.lf))) [6,31,1057,4067,4228,16912] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,4228,6342,32272] BT.lf) [6,31,1057,4228,12288,16912] BT.lf) [6,31,1057,4228,16912,19442] (BT.nd BT.lf [6,31,1057,4228,16912,29696] BT.lf)) [6,31,1057,4228,16912,29725] (BT.nd (BT.nd BT.lf [6,31,1057,4228,25104,31744] BT.lf) [6,31,1057,4228,25368,32272] (BT.nd BT.lf [6,31,1057,4228,30653,32272] BT.lf)))))) [6,31,1057,6210,8456,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,6276,16912,31744] BT.lf) [6,31,1057,6342,8456,31810] BT.lf) [6,31,1057,6342,10570,31744] (BT.nd BT.lf [6,31,1057,6342,12684,31744] BT.lf)) [6,31,1057,6342,16912,31810] (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,6342,19026,31744] BT.lf) [6,31,1057,6342,21140,31744] BT.lf) [6,31,1057,8456,10570,17392] (BT.nd BT.lf [6,31,1057,8456,15855,31810] BT.lf))) [6,31,1057,8456,16384,31810] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,8456,16912,31810] BT.lf) [6,31,1057,8456,16912,31843] BT.lf) [6,31,1057,8456,16912,32338] (BT.nd BT.lf [6,31,1057,8456,16927,31810] BT.lf)) [6,31,1057,8456,17392,21140] (BT.nd (BT.nd BT.lf [6,31,1057,8456,17392,30653] BT.lf) [6,31,1057,8456,17969,31810] (BT.nd BT.lf [6,31,1057,8456,25368,31810] BT.lf)))) [6,31,1057,9192,16912,31876] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,9513,16912,31810] BT.lf) [6,31,1057,10570,12684,31744] BT.lf) [6,31,1057,10570,19026,31744] (BT.nd BT.lf [6,31,1057,10570,25368,31744] BT.lf)) [6,31,1057,12684,21140,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,12684,25368,31744] BT.lf) [6,31,1057,16912,24311,31810] BT.lf) [6,31,1057,16912,25368,31810] (BT.nd BT.lf [6,31,1057,19026,21140,31744] BT.lf))) [6,31,1057,19026,25368,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,1057,21140,25368,31744] BT.lf) [6,31,1087,2114,8456,17392] BT.lf) [6,31,1087,8456,16912,31810] (BT.nd BT.lf [6,31,2017,2048,4228,16912] BT.lf)) [6,31,2017,2114,4228,8456,16912,31777] (BT.nd (BT.nd BT.lf [6,31,2017,2114,4228,9513] BT.lf) [6,31,2017,2114,4228,9513,16912,31744] (BT.nd BT.lf [6,31,2017,2114,4228,15855] BT.lf))))) [6,31,2017,2114,4228,16912] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2017,2114,4228,19026] BT.lf) [6,31,2017,2114,4228,21140] BT.lf) [6,31,2017,2114,6342,16912] (BT.nd BT.lf [6,31,2017,2114,9513,16912] BT.lf)) [6,31,2017,2114,16912,21140] (BT.nd (BT.nd (BT.nd BT.lf [6,31,2017,2114,16912,28539] BT.lf) [6,31,2017,2143,4228,16912] BT.lf) [6,31,2017,3042,4228,16912] (BT.nd BT.lf [6,31,2017,3171,4228,8456] BT.lf))) [6,31,2017,3171,4228,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2017,3171,4228,16912] BT.lf) [6,31,2017,3171,8456,16912] BT.lf) [6,31,2017,4067,4228,16912] (BT.nd BT.lf [6,31,2017,4228,6342,16912] BT.lf)) [6,31,2017,4228,8192,16912] (BT.nd (BT.nd BT.lf [6,31,2017,4228,8456,15855] BT.lf) [6,31,2017,4228,8456,16912] (BT.nd BT.lf [6,31,2017,4228,8456,16912,31810] BT.lf)))) [6,31,2017,4228,8456,21140] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2017,4228,8456,25368] BT.lf) [6,31,2017,4228,8479,16912] BT.lf) [6,31,2017,4228,9192,16912] (BT.nd BT.lf [6,31,2017,4228,9513,16912] BT.lf)) [6,31,2017,4228,10217,16912] (BT.nd (BT.nd BT.lf [6,31,2017,4228,12684,16912] BT.lf) [6,31,2017,4228,16912,19026] (BT.nd BT.lf [6,31,2017,4228,16912,24311] BT.lf))) [6,31,2017,4228,16912,25368] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2017,4228,16912,30653] BT.lf) [6,31,2017,8456,12684,16912] BT.lf) [6,31,2017,8456,16912,21140] (BT.nd BT.lf [6,31,2017,8456,16912,28539] BT.lf)) [6,31,2114,3042,8456,16912,31876] (BT.nd (BT.nd BT.lf [6,31,2114,3171,4228,32272] BT.lf) [6,31,2114,3171,8456,17392] (BT.nd BT.lf [6,31,2114,4067,4228,16912] BT.lf))))))))) [6,31,2114,4228,5285,32272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,4228,8456,17392,32272] BT.lf) [6,31,2114,4228,9192,15855,31744] BT.lf) [6,31,2114,4228,9192,16912,31744] (BT.nd BT.lf [6,31,2114,4228,9192,16912,31810] BT.lf)) [6,31,2114,4228,9192,16912,31876] (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,4228,9192,16927,31744] BT.lf) [6,31,2114,4228,9192,21140,31744] BT.lf) [6,31,2114,4228,11242,16912,31744] (BT.nd BT.lf [6,31,2114,4228,16912,18417] BT.lf))) [6,31,2114,4228,16912,23575,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,4228,16912,30750] BT.lf) [6,31,2114,4228,25368,32272] BT.lf) [6,31,2114,4228,31710,32272] (BT.nd BT.lf [6,31,2114,4255,9192,16912,31744] BT.lf)) [6,31,2114,5092,8456,21140,31744] (BT.nd (BT.nd BT.lf [6,31,2114,5153,8456,31744] BT.lf) [6,31,2114,5285,8456,31777] (BT.nd BT.lf [6,31,2114,5285,9513,31744] BT.lf)))) [6,31,2114,5285,12684,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,5285,16912,31777] BT.lf) [6,31,2114,5285,17969,31744] BT.lf) [6,31,2114,5285,21140,31744] (BT.nd BT.lf [6,31,2114,8456,9192,16912,31876] BT.lf)) [6,31,2114,8456,9513,17392] (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,8456,15855,31777] BT.lf) [6,31,2114,8456,16384,31777] BT.lf) [6,31,2114,8456,16912,17392,31876] (BT.nd BT.lf [6,31,2114,8456,16912,31744,31903] BT.lf))) [6,31,2114,8456,16912,31775,31876] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,8456,16912,31776] BT.lf) [6,31,2114,8456,16912,31777] BT.lf) [6,31,2114,8456,16912,31807] (BT.nd BT.lf [6,31,2114,8456,16912,31843] BT.lf)) [6,31,2114,8456,16912,32305] (BT.nd (BT.nd BT.lf [6,31,2114,8456,16927,31744,31876] BT.lf) [6,31,2114,8456,16927,31777] (BT.nd BT.lf [6,31,2114,8456,17040,31744] BT.lf))))) [6,31,2114,8456,17392,21140] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,8456,17392,21140,31744] BT.lf) [6,31,2114,8456,17392,31710] BT.lf) [6,31,2114,8456,19026,31777] (BT.nd BT.lf [6,31,2114,8456,25368,31777] BT.lf)) [6,31,2114,8488,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,9192,16912,21140,31744] BT.lf) [6,31,2114,9192,16912,28539,31744] BT.lf) [6,31,2114,9192,16912,31744,31876] (BT.nd BT.lf [6,31,2114,9192,16912,31876] BT.lf))) [6,31,2114,9513,12684,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,9513,17969,31744] BT.lf) [6,31,2114,9513,25368,31744] BT.lf) [6,31,2114,10570,16912,31777] (BT.nd BT.lf [6,31,2114,12684,21140,31744] BT.lf)) [6,31,2114,12684,25368,31744] (BT.nd (BT.nd BT.lf [6,31,2114,16912,24311,31777] BT.lf) [6,31,2114,16912,25368,31777] (BT.nd BT.lf [6,31,2114,17969,21140,31744] BT.lf)))) [6,31,2114,17969,25368,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,2114,21140,25368,31744] BT.lf) [6,31,2146,8456,16912,31744] BT.lf) [6,31,3042,3071,4228,8456,16912] (BT.nd BT.lf [6,31,3042,3171,4228,8456] BT.lf)) [6,31,3042,3171,4228,16912] (BT.nd (BT.nd (BT.nd BT.lf [6,31,3042,3171,8456,16912] BT.lf) [6,31,3042,4067,4228,16912] BT.lf) [6,31,3042,4228,5285,16912] (BT.nd BT.lf [6,31,3042,4228,8456,15855] BT.lf))) [6,31,3042,4228,8456,15855,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,3042,4228,8456,16912] BT.lf) [6,31,3042,4228,8456,16912,31744] BT.lf) [6,31,3042,4228,8456,16912,31777] (BT.nd BT.lf [6,31,3042,4228,8456,16912,31810] BT.lf)) [6,31,3042,4228,8456,16912,31876] (BT.nd (BT.nd BT.lf [6,31,3042,4228,8456,16927] BT.lf) [6,31,3042,4228,8456,16927,31744] (BT.nd BT.lf [6,31,3042,4228,8456,21140] BT.lf)))))) [6,31,3042,4228,8456,21140,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,3042,4228,8456,25368] BT.lf) [6,31,3042,4228,9192,16912] BT.lf) [6,31,3042,4228,9192,16912,31744] (BT.nd BT.lf [6,31,3042,4228,10570,16912] BT.lf)) [6,31,3042,4228,10570,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,31,3042,4228,11242,16912] BT.lf) [6,31,3042,4228,11242,16912,31744] BT.lf) [6,31,3042,4228,12684,16912] (BT.nd BT.lf [6,31,3042,4228,16912,17969] BT.lf))) [6,31,3042,4228,16912,24311] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,3042,4228,16912,24311,31744] BT.lf) [6,31,3042,4228,16912,25368] BT.lf) [6,31,3042,4228,16912,31710] (BT.nd BT.lf [6,31,3042,4255,8456,16912] BT.lf)) [6,31,3042,4255,8456,16912,31744] (BT.nd (BT.nd BT.lf [6,31,3042,8456,12684,16912] BT.lf) [6,31,3042,8456,16912,21140] (BT.nd BT.lf [6,31,3042,8456,16912,21140,31744] BT.lf)))) [6,31,3042,8456,16912,28539] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,3042,8456,16912,28539,31744] BT.lf) [6,31,3042,8456,16912,31744,31876] BT.lf) [6,31,3105,4228,16912,31744] (BT.nd BT.lf [6,31,3171,4228,8456,31777] BT.lf)) [6,31,3171,4228,8456,31810] (BT.nd (BT.nd (BT.nd BT.lf [6,31,3171,4228,9513,31744] BT.lf) [6,31,3171,4228,10570,31744] BT.lf) [6,31,3171,4228,16912,31777] (BT.nd BT.lf [6,31,3171,4228,16912,31810] BT.lf))) [6,31,3171,4228,17969,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,3171,4228,19026,31744] BT.lf) [6,31,3171,5285,8456,31744] BT.lf) [6,31,3171,5285,16912,31744] (BT.nd BT.lf [6,31,3171,6342,8456,31744] BT.lf)) [6,31,3171,6342,16912,31744] (BT.nd (BT.nd BT.lf [6,31,3171,8456,16912,31777] BT.lf) [6,31,3171,8456,16912,31810] (BT.nd BT.lf [6,31,3171,8456,17969,31744] BT.lf))))) [6,31,3171,8456,19026,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,3171,9513,16912,31744] BT.lf) [6,31,3171,10570,16912,31744] BT.lf) [6,31,4228,8192,16912,31777] (BT.nd BT.lf [6,31,4228,8456,9192,16912,31810] BT.lf)) [6,31,4228,8456,11242,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,31,4228,8456,15855,31777] BT.lf) [6,31,4228,8456,15855,31810] BT.lf) [6,31,4228,8456,16912,18417] (BT.nd BT.lf [6,31,4228,8456,16912,19442] BT.lf))) [6,31,4228,8456,16912,29725] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,4228,8456,16912,29725,31744] BT.lf) [6,31,4228,8456,16912,30750] BT.lf) [6,31,4228,8456,16912,31745] (BT.nd BT.lf [6,31,4228,8456,16912,31746] BT.lf)) [6,31,4228,8456,16912,31775,31810] (BT.nd (BT.nd BT.lf [6,31,4228,8456,16912,31777] BT.lf) [6,31,4228,8456,16912,31810] (BT.nd BT.lf [6,31,4228,8456,16912,31810,31839] BT.lf)))) [6,31,4228,8456,16912,32305] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,4228,8456,16912,32338] BT.lf) [6,31,4228,8456,16913,31744] BT.lf) [6,31,4228,8456,16927,31744,31810] (BT.nd BT.lf [6,31,4228,8456,16927,31810] BT.lf)) [6,31,4228,8456,21140,31777] (BT.nd (BT.nd BT.lf [6,31,4228,8456,21140,31810] BT.lf) [6,31,4228,8456,25368,31777] (BT.nd BT.lf [6,31,4228,8456,25368,31810] BT.lf))) [6,31,4228,8458,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,4228,8479,16912,31777] BT.lf) [6,31,4228,9192,10570,16912,31744] BT.lf) [6,31,4228,9192,11242,16912,31744] (BT.nd BT.lf [6,31,4228,9192,16912,30653,31744] BT.lf)) [6,31,4228,9192,16912,31744,31810] (BT.nd (BT.nd BT.lf [6,31,4228,9513,10570,31744] BT.lf) [6,31,4228,9513,17969,31744] (BT.nd BT.lf [6,31,4228,9513,25368,31744] BT.lf))))))) [6,31,4228,10570,19026,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,4228,10570,25368,31744] BT.lf) [6,31,4228,12684,16912,31777] BT.lf) [6,31,4228,12684,16912,31810] (BT.nd BT.lf [6,31,4228,16912,24311,31777] BT.lf)) [6,31,4228,16912,24311,31810] (BT.nd (BT.nd (BT.nd BT.lf [6,31,4228,16912,25368,31777] BT.lf) [6,31,4228,16912,25368,31810] BT.lf) [6,31,4228,17969,19026,31744] (BT.nd BT.lf [6,31,4228,17969,25368,31744] BT.lf))) [6,31,4228,19026,25368,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,4229,8456,16912,31744] BT.lf) [6,31,4255,8456,16912,31744,31810] BT.lf) [6,31,4255,8456,16912,31810] (BT.nd BT.lf [6,31,5285,6342,8456,31744] BT.lf)) [6,31,5285,6342,16912,31744] (BT.nd (BT.nd BT.lf [6,31,5285,8456,16912,31777] BT.lf) [6,31,5285,8456,17969,31744] (BT.nd BT.lf [6,31,5285,8456,21140,31744] BT.lf)))) [6,31,5285,9513,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,5285,12684,16912,31744] BT.lf) [6,31,6342,8456,16912,31810] BT.lf) [6,31,6342,8456,19026,31744] (BT.nd BT.lf [6,31,6342,8456,21140,31744] BT.lf)) [6,31,6342,10570,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,31,6342,12684,16912,31744] BT.lf) [6,31,8456,9513,16912,31810] BT.lf) [6,31,8456,10570,16912,31777] (BT.nd BT.lf [6,31,8456,12684,16912,31777] BT.lf))) [6,31,8456,12684,16912,31810] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,8456,16912,17969,31810] BT.lf) [6,31,8456,16912,19026,31777] BT.lf) [6,31,8456,16912,21140,31777] (BT.nd BT.lf [6,31,8456,16912,21140,31810] BT.lf)) [6,31,8456,16912,28539,31777] (BT.nd (BT.nd BT.lf [6,31,8456,16912,28539,31810] BT.lf) [6,31,8456,16912,30653,31777] (BT.nd BT.lf [6,31,8456,16912,31710,31810] BT.lf))))) [6,31,8456,16912,31777,31810] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,8456,16912,31777,31843] BT.lf) [6,31,8456,16912,31777,31876] BT.lf) [6,31,8456,16912,31777,31909] (BT.nd BT.lf [6,31,8456,16912,31810,31843] BT.lf)) [6,31,8456,16912,31810,31876] (BT.nd (BT.nd (BT.nd BT.lf [6,31,8456,16912,31810,31942] BT.lf) [6,31,8456,17969,19026,31744] BT.lf) [6,31,8456,17969,21140,31744] (BT.nd BT.lf [6,31,8456,19026,21140,31744] BT.lf))) [6,31,9513,10570,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,31,9513,12684,16912,31744] BT.lf) [6,31,10570,12684,16912,31744] BT.lf) [6,63,2114,8456,16912,31744] (BT.nd BT.lf [6,1023,1087,2114,4228,8456] BT.lf)) [6,1023,1087,2114,8456,16912] (BT.nd (BT.nd BT.lf [6,1057,1087,2114,4228,8456,17392,31744] BT.lf) [6,1057,1087,2114,4228,32272] (BT.nd BT.lf [6,1057,1087,2114,5092,8456,16912,31744] BT.lf)))) [6,1057,1087,2114,8456,17392] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1057,1087,3042,4228,16912] BT.lf) [6,1057,1087,8456,16912,31810] BT.lf) [6,1057,2079,4228,16912,31744] (BT.nd BT.lf [6,1057,2114,2143,4228,8456,17392,31744] BT.lf)) [6,1057,2114,2143,5092,8456,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,1057,2114,3042,4255,8456] BT.lf) [6,1057,2114,4127,8456,31744] BT.lf) [6,1057,2114,4228,8456,8479,17392,31744] (BT.nd BT.lf [6,1057,2114,4228,8479,17392] BT.lf))) [6,1057,2114,4228,8479,17392,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1057,2114,4228,9192,16927,31744] BT.lf) [6,1057,2114,4228,31775,32008] BT.lf) [6,1057,2114,4255,8456,31775] (BT.nd BT.lf [6,1057,2114,4255,9192,16912,31744] BT.lf)) [6,1057,2114,5092,8456,8479,16912,31744] (BT.nd (BT.nd BT.lf [6,1057,2114,5092,8479,16912,31744] BT.lf) [6,1057,2114,8456,8479,17392] (BT.nd BT.lf [6,1057,2114,8456,16415,31744] BT.lf)))))) [6,1057,2114,8456,17376,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1057,2114,8456,17392,32736] BT.lf) [6,1057,2143,5092,8456,16912,31744] BT.lf) [6,1057,3042,4255,8456,16912] (BT.nd BT.lf [6,1057,3042,4255,8456,16912,31744] BT.lf)) [6,1057,8456,16912,31775,31876] (BT.nd (BT.nd (BT.nd BT.lf [6,1087,2017,2114,4228,8456] BT.lf) [6,1087,2017,2114,4228,8456,16912,31744] BT.lf) [6,1087,2017,2114,8456,16912] (BT.nd BT.lf [6,1087,2047,2114,4228,8456] BT.lf))) [6,1087,2047,2114,8456,16912] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1087,2114,3042,4228,8456] BT.lf) [6,1087,2114,3042,8456,16912] BT.lf) [6,1087,2114,4096,8456,31744] (BT.nd BT.lf [6,1087,2114,4228,8456,17392] BT.lf)) [6,1087,2114,4228,8456,31744] (BT.nd (BT.nd BT.lf [6,1087,2114,4228,8456,31775] BT.lf) [6,1087,2114,4228,8456,31777] (BT.nd BT.lf [6,1087,2114,4228,8456,31807] BT.lf)))) [6,1087,2114,4228,8456,31810] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1087,2114,4228,8456,32272] BT.lf) [6,1087,2114,4228,10570,31744] BT.lf) [6,1087,2114,4228,12684,31744] (BT.nd BT.lf [6,1087,2114,4228,16912,31777] BT.lf)) [6,1087,2114,4228,17969,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,1087,2114,4228,24311,31744] BT.lf) [6,1087,2114,4228,31744,32008] BT.lf) [6,1087,2114,4255,8456,31744] (BT.nd BT.lf [6,1087,2114,5092,8456,31744] BT.lf))) [6,1087,2114,5285,8456,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1087,2114,5285,16912,31744] BT.lf) [6,1087,2114,5311,8456,31744] BT.lf) [6,1087,2114,6342,8456,31744] (BT.nd BT.lf [6,1087,2114,8456,12684,31744] BT.lf)) [6,1087,2114,8456,15855,31744] (BT.nd (BT.nd BT.lf [6,1087,2114,8456,16384,31744] BT.lf) [6,1087,2114,8456,16912,17392] (BT.nd BT.lf [6,1087,2114,8456,16912,31744] BT.lf))))) [6,1087,2114,8456,16912,31775] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1087,2114,8456,16912,31777] BT.lf) [6,1087,2114,8456,16912,31807] BT.lf) [6,1087,2114,8456,16912,31810] (BT.nd BT.lf [6,1087,2114,8456,16912,32272] BT.lf)) [6,1087,2114,8456,16927,31744] (BT.nd (BT.nd (BT.nd BT.lf [6,1087,2114,8456,17392] BT.lf) [6,1087,2114,8456,17392,31744] BT.lf) [6,1087,2114,8456,17969,31744] (BT.nd BT.lf [6,1087,2114,8456,17983,31744] BT.lf))) [6,1087,2114,8456,19026,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1087,2114,8456,25368,31744] BT.lf) [6,1087,2114,8456,28539,31744] BT.lf) [6,1087,2114,10570,16912,31744] (BT.nd BT.lf [6,1087,2114,16912,24311,31744] BT.lf)) [6,1087,2114,16912,25368,31744] (BT.nd (BT.nd BT.lf [6,1087,4228,6342,8456,31744] BT.lf) [6,1087,4228,8456,10570,31744] (BT.nd BT.lf [6,1087,4228,8456,16912,31777] BT.lf)))) [6,1087,4228,8456,17969,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1087,4228,8456,30653,31744] BT.lf) [6,1087,5285,8456,16912,31744] BT.lf) [6,1087,8456,10570,16912,31744] (BT.nd BT.lf [6,1087,8456,16912,19026,31744] BT.lf)) [6,1087,8456,16912,30653,31744] (BT.nd (BT.nd BT.lf [6,1087,8456,16912,31744,31810] BT.lf) [6,2114,3042,4228,8456,16927,31744] (BT.nd BT.lf [6,2114,3042,4255,8456,16912] BT.lf))) [6,2114,3042,4255,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2114,4228,8456,9192,16927,31744] BT.lf) [6,2114,4228,8456,16927,31744,31775] BT.lf) [6,2114,4228,8456,31680,31744] (BT.nd BT.lf [6,2114,4228,9192,16927,31744] BT.lf)) [6,2114,4255,8456,9192,16912,31744] (BT.nd (BT.nd BT.lf [6,2114,4255,8456,16912,17392] BT.lf) [6,2114,4255,8456,16912,31744,31775] (BT.nd BT.lf [6,2114,4255,8456,16912,31775] BT.lf)))))))) [6,2114,4255,8456,16927,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2114,4255,9192,16912,31744] BT.lf) [6,2114,8456,16912,31680,31744] BT.lf) [6,2114,8456,16912,31744,31807] (BT.nd BT.lf [6,2114,8456,16912,31775,31777] BT.lf)) [6,2114,8456,16912,31775,31876] (BT.nd (BT.nd (BT.nd BT.lf [6,2114,8456,16912,31777,31807] BT.lf) [6,2114,8456,16912,31777,32736] BT.lf) [6,2114,8456,16912,31777,32737] (BT.nd BT.lf [6,3042,4255,8456,16912] BT.lf))) [6,3042,4255,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,1,31,992,4228,8456,16912] BT.lf) [7,1,31,4228,8456,16912,31744] BT.lf) [7,1,992,4228,8456,16912,31744] (BT.nd BT.lf [7,2,31,992,4228,8456,16912] BT.lf)) [7,2,31,992,4228,8456,16912,31744] (BT.nd (BT.nd BT.lf [7,2,31,4228,8456,16912,31744] BT.lf) [7,2,992,4228,8456,16912,31744] (BT.nd BT.lf [7,16,31,992,1057,2114,4228,8456,31744] BT.lf)))) [7,31,992,1023,2114,4228,8456,16912] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,1057,2048,4228,16912] BT.lf) [7,31,992,1057,2114,4228,8456] BT.lf) [7,31,992,1057,2114,4228,8456,16912,31744] (BT.nd BT.lf [7,31,992,1057,2114,4228,8456,16912,31777] BT.lf)) [7,31,992,1057,2114,4228,8456,16912,32008] (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,1057,2114,4228,8456,17392,31744] BT.lf) [7,31,992,1057,2114,4228,8456,17969,31744] BT.lf) [7,31,992,1057,2114,4228,8456,21140,31744] (BT.nd BT.lf [7,31,992,1057,2114,4228,8456,31744,32272] BT.lf))) [7,31,992,1057,2114,4228,8456,32272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,1057,2114,4228,9513] BT.lf) [7,31,992,1057,2114,4228,10570] BT.lf) [7,31,992,1057,2114,4228,12684] (BT.nd BT.lf [7,31,992,1057,2114,4228,15855] BT.lf)) [7,31,992,1057,2114,4228,32008] (BT.nd (BT.nd BT.lf [7,31,992,1057,2114,4255,8456] BT.lf) [7,31,992,1057,2114,5092,8456] (BT.nd BT.lf [7,31,992,1057,2114,5092,8456,16912,31744] BT.lf))))) [7,31,992,1057,2114,5285,8456] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,1057,2114,5285,8456,16912,31744] BT.lf) [7,31,992,1057,2114,5285,16912] BT.lf) [7,31,992,1057,2114,6342,8456] (BT.nd BT.lf [7,31,992,1057,2114,6342,16912] BT.lf)) [7,31,992,1057,2114,8456,12684] (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,1057,2114,8456,15855] BT.lf) [7,31,992,1057,2114,8456,16384] BT.lf) [7,31,992,1057,2114,8456,16912] (BT.nd BT.lf [7,31,992,1057,2114,8456,16912,31876] BT.lf))) [7,31,992,1057,2114,8456,16927] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,1057,2114,8456,17392] BT.lf) [7,31,992,1057,2114,8456,17969] BT.lf) [7,31,992,1057,2114,8456,19026] (BT.nd BT.lf [7,31,992,1057,2114,8456,25368] BT.lf)) [7,31,992,1057,2114,8456,28539] (BT.nd (BT.nd BT.lf [7,31,992,1057,2114,9513,16912] BT.lf) [7,31,992,1057,2114,10570,16912] (BT.nd BT.lf [7,31,992,1057,2114,16912,21140] BT.lf)))) [7,31,992,1057,2114,16912,24311] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,1057,2114,16912,25368] BT.lf) [7,31,992,1057,2114,16912,28539] BT.lf) [7,31,992,1057,3171,8456,16912] (BT.nd BT.lf [7,31,992,1057,8456,10570,16912] BT.lf)) [7,31,992,1057,8456,12684,16912] (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,1057,8456,16912,28539] BT.lf) [7,31,992,1057,8456,16912,31810] BT.lf) [7,31,992,1087,2114,4228,8456] (BT.nd BT.lf [7,31,992,1087,2114,8456,16912] BT.lf))) [7,31,992,2114,3171,4228,8456] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,2114,3171,4228,16912] BT.lf) [7,31,992,2114,3171,8456,16912] BT.lf) [7,31,992,2114,4228,8456,9513] (BT.nd BT.lf [7,31,992,2114,4228,8456,15855] BT.lf)) [7,31,992,2114,4228,8456,15855,31744] (BT.nd (BT.nd BT.lf [7,31,992,2114,4228,8456,16912] BT.lf) [7,31,992,2114,4228,8456,16912,31744] (BT.nd BT.lf [7,31,992,2114,4228,8456,16912,31777] BT.lf)))))) [7,31,992,2114,4228,8456,16912,31810] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,2114,4228,8456,16912,32008] BT.lf) [7,31,992,2114,4228,8456,16927] BT.lf) [7,31,992,2114,4228,8456,16927,31744] (BT.nd BT.lf [7,31,992,2114,4228,8456,19026] BT.lf)) [7,31,992,2114,4228,8456,21140] (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,2114,4228,8456,21140,31744] BT.lf) [7,31,992,2114,4228,8456,25368] BT.lf) [7,31,992,2114,4228,8456,31710] (BT.nd BT.lf [7,31,992,2114,4255,8456,16912] BT.lf))) [7,31,992,2114,4255,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,2114,6342,8456,16912] BT.lf) [7,31,992,2114,8456,9513,16912] BT.lf) [7,31,992,2114,8456,12684,16912] (BT.nd BT.lf [7,31,992,2114,8456,16912,17969] BT.lf)) [7,31,992,2114,8456,16912,21140] (BT.nd (BT.nd BT.lf [7,31,992,2114,8456,16912,21140,31744] BT.lf) [7,31,992,2114,8456,16912,28539] (BT.nd BT.lf [7,31,992,2114,8456,16912,28539,31744] BT.lf)))) [7,31,992,2114,8456,16912,31710] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,992,2114,8456,16912,31744,31876] BT.lf) [7,31,992,2114,8456,16912,31777] BT.lf) [7,31,992,2114,8456,16912,31876] (BT.nd BT.lf [7,31,1023,1057,2114,4228,8456] BT.lf)) [7,31,1023,1057,2114,4228,16912] (BT.nd (BT.nd (BT.nd BT.lf [7,31,1023,1057,2114,8456,16912] BT.lf) [7,31,1023,1057,4228,8456,16912] BT.lf) [7,31,1023,2114,4228,8456,16912] (BT.nd BT.lf [7,31,1057,2017,2114,4228,8456] BT.lf))) [7,31,1057,2017,2114,4228,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,2017,2114,4228,16912] BT.lf) [7,31,1057,2017,2114,8456,16912] BT.lf) [7,31,1057,2017,4228,8456,16912] (BT.nd BT.lf [7,31,1057,2048,4228,16912,31744] BT.lf)) [7,31,1057,2114,3042,4228,8456] (BT.nd (BT.nd BT.lf [7,31,1057,2114,3042,4228,16912] BT.lf) [7,31,1057,2114,3042,8456,16912] (BT.nd BT.lf [7,31,1057,2114,4096,8456,31744] BT.lf))))) [7,31,1057,2114,4228,5092,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,2114,4228,8456,16912,17392,31744] BT.lf) [7,31,1057,2114,4228,8456,17392] BT.lf) [7,31,1057,2114,4228,8456,17392,31744] (BT.nd BT.lf [7,31,1057,2114,4228,8456,31744] BT.lf)) [7,31,1057,2114,4228,8456,31775] (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,2114,4228,8456,31777] BT.lf) [7,31,1057,2114,4228,8456,31810] BT.lf) [7,31,1057,2114,4228,8456,32272] (BT.nd BT.lf [7,31,1057,2114,4228,9192,16912,31744] BT.lf))) [7,31,1057,2114,4228,9513,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,2114,4228,10570,31744] BT.lf) [7,31,1057,2114,4228,12684,31744] BT.lf) [7,31,1057,2114,4228,15855,31744] (BT.nd BT.lf [7,31,1057,2114,4228,16912,17392] BT.lf)) [7,31,1057,2114,4228,16912,31744] (BT.nd (BT.nd BT.lf [7,31,1057,2114,4228,16912,31775] BT.lf) [7,31,1057,2114,4228,16912,31777] (BT.nd BT.lf [7,31,1057,2114,4228,16912,31810] BT.lf)))) [7,31,1057,2114,4228,16912,32272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,2114,4228,17969,31744] BT.lf) [7,31,1057,2114,4228,19026,31744] BT.lf) [7,31,1057,2114,4228,21140,31744] (BT.nd BT.lf [7,31,1057,2114,4228,24311,31744] BT.lf)) [7,31,1057,2114,4228,31744,32008] (BT.nd (BT.nd BT.lf [7,31,1057,2114,4228,31744,32272] BT.lf) [7,31,1057,2114,4228,32272] (BT.nd BT.lf [7,31,1057,2114,4255,8456,31744] BT.lf))) [7,31,1057,2114,5092,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,2114,5092,8456,31744] BT.lf) [7,31,1057,2114,5285,8456,31744] BT.lf) [7,31,1057,2114,5285,16912,31744] (BT.nd BT.lf [7,31,1057,2114,6342,8456,31744] BT.lf)) [7,31,1057,2114,6342,16912,31744] (BT.nd (BT.nd BT.lf [7,31,1057,2114,8456,12684,31744] BT.lf) [7,31,1057,2114,8456,15855,31744] (BT.nd BT.lf [7,31,1057,2114,8456,16384,31744] BT.lf))))))) [7,31,1057,2114,8456,16912,17392] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,2114,8456,16912,31744] BT.lf) [7,31,1057,2114,8456,16912,31775] BT.lf) [7,31,1057,2114,8456,16912,31777] (BT.nd BT.lf [7,31,1057,2114,8456,16912,31810] BT.lf)) [7,31,1057,2114,8456,16912,32272] (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,2114,8456,16927,31744] BT.lf) [7,31,1057,2114,8456,17392] BT.lf) [7,31,1057,2114,8456,17392,31744] (BT.nd BT.lf [7,31,1057,2114,8456,17969,31744] BT.lf))) [7,31,1057,2114,8456,19026,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,2114,8456,25368,31744] BT.lf) [7,31,1057,2114,8456,28539,31744] BT.lf) [7,31,1057,2114,9513,16912,31744] (BT.nd BT.lf [7,31,1057,2114,10570,16912,31744] BT.lf)) [7,31,1057,2114,16912,21140,31744] (BT.nd (BT.nd BT.lf [7,31,1057,2114,16912,24311,31744] BT.lf) [7,31,1057,2114,16912,25368,31744] (BT.nd BT.lf [7,31,1057,2114,16912,28539,31744] BT.lf)))) [7,31,1057,2143,4228,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,3042,4228,8456,16912] BT.lf) [7,31,1057,3042,4228,8456,16912,31744] BT.lf) [7,31,1057,3042,4228,16912] (BT.nd BT.lf [7,31,1057,3042,4228,16912,31744] BT.lf)) [7,31,1057,3171,4228,8456,31744] (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,3171,4228,16912,31744] BT.lf) [7,31,1057,3171,8456,16912,31744] BT.lf) [7,31,1057,4228,6342,8456,31744] (BT.nd BT.lf [7,31,1057,4228,6342,16912,31744] BT.lf))) [7,31,1057,4228,8192,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,4228,8456,10570,31744] BT.lf) [7,31,1057,4228,8456,15855,31744] BT.lf) [7,31,1057,4228,8456,16912,17392] (BT.nd BT.lf [7,31,1057,4228,8456,16912,31744] BT.lf)) [7,31,1057,4228,8456,16912,31775] (BT.nd (BT.nd BT.lf [7,31,1057,4228,8456,16912,31777] BT.lf) [7,31,1057,4228,8456,16912,31810] (BT.nd BT.lf [7,31,1057,4228,8456,16912,32272] BT.lf))))) [7,31,1057,4228,8456,17969,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,4228,8456,21140,31744] BT.lf) [7,31,1057,4228,8456,25368,31744] BT.lf) [7,31,1057,4228,8456,30653,31744] (BT.nd BT.lf [7,31,1057,4228,8479,16912,31744] BT.lf)) [7,31,1057,4228,9192,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,4228,9513,16912,31744] BT.lf) [7,31,1057,4228,12684,16912,31744] BT.lf) [7,31,1057,4228,16912,19026,31744] (BT.nd BT.lf [7,31,1057,4228,16912,24311,31744] BT.lf))) [7,31,1057,4228,16912,25368,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,4228,16912,30653,31744] BT.lf) [7,31,1057,5285,8456,16912,31744] BT.lf) [7,31,1057,8456,10570,16912,31744] (BT.nd BT.lf [7,31,1057,8456,12684,16912,31744] BT.lf)) [7,31,1057,8456,16912,19026,31744] (BT.nd (BT.nd BT.lf [7,31,1057,8456,16912,21140,31744] BT.lf) [7,31,1057,8456,16912,28539,31744] (BT.nd BT.lf [7,31,1057,8456,16912,30653,31744] BT.lf)))) [7,31,1057,8456,16912,31744,31810] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,1057,8456,16912,31744,31876] BT.lf) [7,31,1057,8456,16912,31810] BT.lf) [7,31,1087,2114,4228,8456,31744] (BT.nd BT.lf [7,31,1087,2114,8456,16912,31744] BT.lf)) [7,31,2017,2114,4228,8456,16912] (BT.nd (BT.nd BT.lf [7,31,2017,2114,4228,8456,16912,31744] BT.lf) [7,31,2017,2114,4228,16912] (BT.nd BT.lf [7,31,2017,2114,4228,16912,31744] BT.lf))) [7,31,2017,4228,8456,16912] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,2017,4228,8456,16912,31744] BT.lf) [7,31,2114,3042,4228,8456,16912] BT.lf) [7,31,2114,3042,4228,8456,16912,31744] (BT.nd BT.lf [7,31,2114,3171,4228,8456,31744] BT.lf)) [7,31,2114,3171,4228,16912,31744] (BT.nd (BT.nd BT.lf [7,31,2114,3171,8456,16912,31744] BT.lf) [7,31,2114,4228,5092,8456,16912,31744] (BT.nd BT.lf [7,31,2114,4228,5285,8456,31744] BT.lf)))))) [7,31,2114,4228,5285,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,2114,4228,8456,9192,16912,31744] BT.lf) [7,31,2114,4228,8456,9513,31744] BT.lf) [7,31,2114,4228,8456,15855,31744] (BT.nd BT.lf [7,31,2114,4228,8456,16912,17392] BT.lf)) [7,31,2114,4228,8456,16912,17392,31744] (BT.nd (BT.nd (BT.nd BT.lf [7,31,2114,4228,8456,16912,31744] BT.lf) [7,31,2114,4228,8456,16912,31744,31775] BT.lf) [7,31,2114,4228,8456,16912,31775] (BT.nd BT.lf [7,31,2114,4228,8456,16912,31777] BT.lf))) [7,31,2114,4228,8456,16912,31810] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,2114,4228,8456,16912,32272] BT.lf) [7,31,2114,4228,8456,16927,31744] BT.lf) [7,31,2114,4228,8456,19026,31744] (BT.nd BT.lf [7,31,2114,4228,8456,21140,31744] BT.lf)) [7,31,2114,4228,8456,25368,31744] (BT.nd (BT.nd BT.lf [7,31,2114,4228,8456,31710,31744] BT.lf) [7,31,2114,4228,9192,16912,31744] (BT.nd BT.lf [7,31,2114,4228,10570,16912,31744] BT.lf)))) [7,31,2114,4228,12684,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,2114,4228,16912,17969,31744] BT.lf) [7,31,2114,4228,16912,24311,31744] BT.lf) [7,31,2114,4228,16912,25368,31744] (BT.nd BT.lf [7,31,2114,4228,16912,31710,31744] BT.lf)) [7,31,2114,4255,8456,16912,31744] (BT.nd (BT.nd (BT.nd BT.lf [7,31,2114,6342,8456,16912,31744] BT.lf) [7,31,2114,8456,9513,16912,31744] BT.lf) [7,31,2114,8456,12684,16912,31744] (BT.nd BT.lf [7,31,2114,8456,16912,17969,31744] BT.lf))) [7,31,2114,8456,16912,21140,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,2114,8456,16912,28539,31744] BT.lf) [7,31,2114,8456,16912,31710,31744] BT.lf) [7,31,2114,8456,16912,31744,31777] (BT.nd BT.lf [7,31,2114,8456,16912,31744,31876] BT.lf)) [7,31,2114,8456,16912,31777] (BT.nd (BT.nd BT.lf [7,31,3042,4228,8456,16912] BT.lf) [7,31,3042,4228,8456,16912,31744] (BT.nd BT.lf [7,31,4228,5285,8456,16912,31744] BT.lf))))) [7,31,4228,6342,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,31,4228,8456,9513,16912,31744] BT.lf) [7,31,4228,8456,10570,16912,31744] BT.lf) [7,31,4228,8456,16912,17969,31744] (BT.nd BT.lf [7,31,4228,8456,16912,19026,31744] BT.lf)) [7,31,4228,8456,16912,30653,31744] (BT.nd (BT.nd (BT.nd BT.lf [7,31,4228,8456,16912,31710,31744] BT.lf) [7,31,4228,8456,16912,31744,31777] BT.lf) [7,31,4228,8456,16912,31744,31810] (BT.nd BT.lf [7,31,4228,8456,16912,31777] BT.lf))) [7,31,4228,8456,16912,31810] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,1057,1087,2114,4228,8456,31744] BT.lf) [7,1057,1087,2114,4228,16912,31744] BT.lf) [7,1057,1087,2114,8456,16912,31744] (BT.nd BT.lf [7,1057,1087,4228,8456,16912,31744] BT.lf)) [7,1057,2114,4228,8456,31744,31775] (BT.nd (BT.nd BT.lf [7,1057,2114,4228,8456,31744,32736] BT.lf) [7,1057,2114,8456,16912,31744,31775] (BT.nd BT.lf [7,1057,2114,8456,16912,31744,32736] BT.lf)))) [7,1087,2114,4228,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,1087,2114,4228,8456,31744] BT.lf) [7,1087,2114,8456,16912,31744] BT.lf) [7,2114,4228,8456,16912,31744,31775] (BT.nd BT.lf [8,31,992,1057,2114,4228,8456] BT.lf)) [8,31,992,1057,2114,4228,8456,16912] (BT.nd (BT.nd BT.lf [8,31,992,1057,2114,4228,8456,16912,31744] BT.lf) [8,31,992,1057,2114,4228,8456,31744] (BT.nd BT.lf [8,31,992,1057,2114,8456,16912] BT.lf))) [8,31,992,1057,2114,8456,16912,31744] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [8,31,992,2114,4228,8456,16912] BT.lf) [8,31,992,2114,4228,8456,16912,31744] BT.lf) [8,31,1057,2114,4228,8456,16912,31744] (BT.nd BT.lf [8,31,1057,2114,4228,8456,31744] BT.lf)) [8,31,1057,2114,4228,16912,31744] (BT.nd (BT.nd BT.lf [8,31,1057,2114,8456,16912,31744] BT.lf) [8,31,1057,4228,8456,16912,31744] (BT.nd BT.lf [8,31,2114,4228,8456,16912,31744] BT.lf))))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,1077,2114,5092,32008],[]),([3,1333,2114,5092,31744],[]),([3,7167,11242,21151],[]),([3,10570,13375],[(0,7362),(2,1224),(4,7362),(6,197640)]),([4,10,9192,16912,31876],[]),([4,20,1057,2114,5092,32008],[]),([4,31,992,8458,17040],[]),([4,31,1057,2114,5108,32008],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([4,31,1073,2114,5092,32008],[]),([4,31,1377,2114,4228,32272],[(72,0)]),([4,31,2114,6117,16912,32041],[]),([4,31,3171,5092,16912,32041],[]),([4,31,3171,5092,17969,32008],[]),([4,31,3171,6117,16912,32008],[]),([4,31,8456,17055,31810],[]),([4,31,9194,16912,31876],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([4,31,10570,13345],[(0,171214),(2,197704),(4,171214),(6,66760),(8,171214),(10,210088),(73,72898),(74,171214)]),([4,138,9192,16912,31744],[]),([4,276,1057,2114,5092,31744],[]),([4,1057,2114,5108,8479,31744],[]),([4,1057,2143,5092,8456,31760],[]),([4,1057,2143,5092,32008,32272],[]),([4,1057,2143,5108,8456,31744],[]),([4,1057,10570,12319],[(0,72898),(2,72898),(4,72898),(6,66760),(8,72898),(10,197704),(57,72898),(58,72898),(73,203778),(74,72898)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,1057,10570,19424],[(0,197704),(2,197704),(4,197704),(6,66760),(8,197704),(10,72898),(57,197704),(58,197704),(74,197704),(77,197640)]),([4,1073,2114,5092,8479,31744],[]),([4,1073,2143,5092,8456,31744],[]),([4,1077,2114,5092,8456,31744],[]),([4,1087,2114,5092,17969,32008],[]),([4,1087,2114,6117,16912,32008],[]),([4,1087,8456,14402],[(0,203778),(2,197640),(4,203778),(6,3336),(8,203778),(10,1224)]),([4,1087,10570,12288],[(0,400590),(2,197640),(4,400590),(6,1224),(8,400590),(10,210312),(73,7362),(74,400590)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,1087,10570,19442],[(0,210312),(2,197768),(4,210312),(6,3272),(8,210312),(10,400590),(74,210312),(77,199688)]),([4,2114,4228,9535,18417,31744],[]),([4,2114,5092,9535,17969,31744],[]),([4,2114,5119,9192,21151],[]),([4,2114,5285,8479,17392,31777],[]),([4,2114,5285,9535,17392,31744],[]),([4,2114,6117,8479,16912,31777],[]),([4,2114,6117,9535,16912,31744],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([4,2114,8456,13375],[(0,7362),(2,1224),(4,7362),(6,3336),(8,7362),(10,197640),(57,7362),(58,7362)]),([4,2114,9192,16927,31872],[]),([4,2114,9192,17055,31744],[]),([4,2143,5092,9513,17969,31744],[]),([4,2143,5285,8456,17392,31777],[]),([4,2143,5285,9513,17392,31744],[]),([4,2143,6117,8456,16912,31777],[]),([4,2143,6117,9513,16912,31744],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([4,3042,4255,11242,21151],[]),([4,3042,5119,8456,21151],[]),([4,3042,7167,8456,21151],[]),([4,3042,8456,17055,31744],[]),([4,3171,5285,8479,17392,31744],[]),([4,3171,6117,8479,16912,31744],[]),([4,3199,6117,8456,16912,31744],[]),([4,8479,18417,21140],[(0,66728),(2,361608),(4,66728),(6,66728),(8,66728),(10,1416)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([4,9192,16927,31810,31876],[]),([5,2,31,992,8456,17040],[(72,275458)]),([5,2,31,9192,16912,31876],[]),([5,2,992,9192,16912,31876],[(56,164868),(72,0)]),([5,2,4228,9192,16927,31744],[(72,0),(128,0)]),([5,2,4255,9192,16912,31744],[(72,0)]),([5,10,992,8456,16912,31876],[(72,263240)]),([5,10,4228,9192,16912,31744],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([5,16,31,1057,2114,5092,32008],[]),([5,16,1057,2114,5092,8479,31744],[]),([5,16,1057,2143,5092,8456,31744],[]),([5,20,992,1057,2114,4228,32008],[(72,0)]),([5,20,1057,2114,5092,8456,31744],[]),([5,31,130,992,8456,16912],[]),([5,31,130,3042,8456,16912],[(56,275458),(136,275586)]),([5,31,159,8456,16912,31810],[(96,7338)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,891,2114,9192,16912],[]),([5,31,992,1057,2114,4244,32008],[]),([5,31,992,1073,2114,4228,32008],[]),([5,31,992,2114,5285,8456,32305],[(72,0)]),([5,31,992,2114,5285,9513,32272],[(72,0)]),([5,31,992,2114,5285,16912,32041],[]),([5,31,992,2114,5285,17969,32008],[]),([5,31,992,2114,8456,17055],[(80,275458)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,992,3171,5285,8456,32272],[(72,0)]),([5,31,992,8456,17040,31810],[(96,0)]),([5,31,994,8456,16912,31876],[]),([5,31,1008,1057,2114,4228,32008],[]),([5,31,1057,2114,5092,8456,31760],[]),([5,31,1057,2114,5092,16912,32000],[(72,0)]),([5,31,1057,2114,5092,16912,32008],[]),([5,31,1057,2114,5092,16912,32041],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,1057,2114,5092,17392,32008],[]),([5,31,1057,2114,5092,17969,32008],[]),([5,31,1057,2114,5092,21140,32008],[]),([5,31,1057,2114,5092,21492,32008],[]),([5,31,1057,2114,5092,32008,32272],[]),([5,31,1057,2114,5108,8456,31744],[]),([5,31,1057,2114,6117,16912,32008],[]),([5,31,1057,2370,4228,17392,31744],[(72,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,1057,2370,5092,16912,31744],[(72,0)]),([5,31,1057,2543,4228],[(0,66760),(2,197704),(4,66760),(6,66760),(8,66760),(10,132298),(12,66760),(14,203842),(57,66760),(82,66760),(105,205954),(106,66760)]),([5,31,1057,3171,5092,16912,32008],[]),([5,31,1057,4228,29200],[(0,132298),(2,197704),(4,132298),(6,132298),(8,132298),(10,132298),(12,132298),(14,66760),(57,132298),(62,132266),(81,132298),(82,132298),(105,66760),(106,132298)]),([5,31,1057,4228,30224],[(0,132298),(2,197704),(4,132298),(6,132298),(8,132298),(10,132298),(12,132298),(14,66760),(57,132298),(81,132298),(82,132298),(106,132298)]),([5,31,1057,6276,32272],[(0,132298),(2,197704),(4,132298),(6,132298),(8,132298),(10,132298),(12,132298),(14,66760),(57,132298),(81,132298),(82,132298),(106,132298)]),([5,31,1057,6342,32338],[(0,134210),(2,197704),(4,134210),(6,134210),(8,134210),(10,134210),(12,134210),(14,68738),(57,134210),(81,134210),(82,134210),(106,134210)]),([5,31,1057,8456,14402],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,68872),(12,203842),(14,66760),(57,203842),(58,203778),(81,203842),(82,203842),(105,269380),(106,203842)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,1057,8456,15426],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,68872),(12,203842),(14,66760),(57,203842),(58,203778),(81,203842),(82,203842),(105,269380),(106,203842)]),([5,31,1057,8456,17341],[(0,66760),(2,197704),(4,66760),(6,66760),(8,66760),(10,68872),(12,66760),(14,203842),(57,66760),(58,1224),(81,66760),(82,66760),(106,66760),(109,66760)]),([5,31,1057,10570,12288],[(0,400590),(2,197704),(4,400590),(6,400590),(8,400590),(10,66760),(12,400590),(14,210312),(57,400590),(58,400590),(81,400590),(82,400590),(97,72898),(98,400590),(105,203842),(106,400590)]),([5,31,1057,10570,19442],[(0,210312),(2,197768),(4,210312),(6,210312),(8,210312),(10,68808),(12,210312),(14,400590),(57,210312),(58,210312),(81,210312),(82,210312),(98,210312),(101,199752),(106,210312),(109,210248)]),([5,31,1057,12288,21140],[(0,66760),(2,197704),(4,66760),(6,66760),(8,66760),(10,66760),(12,66760),(14,400590),(57,66760),(62,66728),(72,0),(73,66760),(74,66760),(81,66760),(82,66760),(105,400590),(106,66760)]),([5,31,1057,19442,21140],[(0,68808),(2,197768),(4,68808),(6,68808),(8,68808),(10,68808),(12,68808),(14,210312),(57,68808),(74,66760),(77,68808),(81,68776),(82,68808),(105,210312),(106,68808)]),([5,31,1057,24840,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,269380),(57,203842),(58,203778),(81,203842),(82,203842),(105,269380),(106,203842)]),([5,31,1057,25368,32338],[(0,134210),(2,197704),(4,134210),(6,134210),(8,134210),(10,134210),(12,134210),(14,132164),(57,134210),(58,134146),(81,134210),(82,134210),(105,132164),(106,134210)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,1073,2114,5092,8456,31744],[]),([5,31,1313,2114,4228,17392,31744],[(72,0)]),([5,31,1313,2114,5092,16912,31744],[(72,0)]),([5,31,1377,2114,4228,16912,31744],[(72,0)]),([5,31,2017,2114,4228,9513,32272],[(72,0)]),([5,31,2017,2114,4228,16912,32041],[]),([5,31,2017,3171,4228,8456,32272],[(72,0)]),([5,31,2017,3171,4228,16912,32008],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,2017,4228,25104],[(0,132266),(2,361614),(4,132266),(6,400386),(8,132266),(10,171074),(12,132266),(14,173186),(57,132106),(73,132266),(105,1416),(113,66728),(114,132266)]),([5,31,2017,6276,16912],[(0,132266),(2,132266),(4,132266),(6,367618),(8,132266),(10,171074),(12,132266),(14,173186),(57,132106),(73,132266),(101,66568),(105,1384),(113,66728),(114,132266)]),([5,31,2017,6342,19026],[(0,134210),(2,361615),(4,134210),(6,400388),(8,134210),(10,132164),(12,134210),(14,66692),(57,134154),(101,203786),(105,3464)]),([5,31,2017,6342,21140],[(0,66730),(2,361615),(4,66730),(6,400388),(8,66730),(10,66730),(12,66730),(14,173122),(57,66570),(74,66730),(82,66728)]),([5,31,2017,12684,21140],[(0,68778),(2,361615),(4,68778),(6,400386),(8,68778),(10,68778),(12,68778),(14,407918),(57,68618),(72,0),(73,68778),(74,66730),(82,68776)]),([5,31,2017,12684,25368],[(0,132164),(2,361615),(4,132164),(6,400386),(8,132164),(10,132164),(12,132164),(14,66692),(57,132106),(73,132164)]),([5,31,2017,19026,21140],[(0,68776),(2,361615),(4,68776),(6,400388),(8,68776),(10,68776),(12,68776),(14,374159),(57,68616),(74,66728),(77,68616),(81,68776),(82,68776)]),([5,31,2017,21140,25368],[(0,66728),(2,361615),(4,66728),(6,400386),(8,66728),(10,171074),(12,66728),(14,66728),(57,66568),(98,66728),(106,66728)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,2114,4228,9513,18417,31744],[(56,0)]),([5,31,2114,5092,9513,17969,31744],[]),([5,31,2114,5285,8456,17392,31777],[]),([5,31,2114,5285,9513,17392,31744],[]),([5,31,2114,5285,32305],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,68872),(58,132362),(81,134410),(82,134410),(106,134410),(109,132298)]),([5,31,2114,6117,8456,16912,31777],[]),([5,31,2114,6117,9513,16912,31744],[]),([5,31,2114,8456,13345],[(0,171278),(2,197704),(4,171278),(6,66760),(8,171278),(10,68872),(12,171278),(14,275624),(81,171278),(82,171278),(97,72898),(98,171278),(105,203842),(106,171278)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,2114,8456,15393],[(0,171278),(2,197704),(4,171278),(6,66760),(8,171278),(10,68872),(12,171278),(14,275624),(81,171278),(82,171278),(97,72898),(98,171278),(105,203842),(106,171278)]),([5,31,2114,8456,15407],[(0,171278),(2,361608),(4,171278),(6,1224),(8,171278),(10,3336),(12,171278),(14,275624),(73,171268),(81,171278),(82,171278),(98,171278),(106,171278)]),([5,31,2114,8456,17055,31744],[]),([5,31,2114,8456,17296],[(0,275624),(2,197768),(4,275624),(6,275624),(8,275624),(10,3336),(12,275624),(14,171278),(62,275624),(73,265384),(81,275624),(82,275624),(98,275624),(105,132296),(106,275624)]),([5,31,2114,8456,17360],[(0,275624),(2,361608),(4,275624),(6,1224),(8,275624),(10,3336),(12,275624),(14,171278),(73,265384),(81,275624),(82,275624),(98,275624),(106,275624)]),([5,31,2114,8456,17374],[(0,275624),(2,197704),(4,275624),(6,66760),(8,275624),(10,68872),(12,275624),(14,171278),(81,275624),(82,275624),(98,275624),(101,275464),(106,275624),(109,275624)]),([5,31,2114,8456,17392,32404],[(112,134312)]),([5,31,2114,8488,17392],[(0,177480),(2,361608),(4,177480),(6,1224),(8,177480),(10,3240),(12,177480),(14,335022),(73,167240),(81,177480),(82,177480),(98,177480),(106,177480)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,2114,9192,15855,31876],[]),([5,31,2114,9192,16912,31872],[]),([5,31,2114,9192,16912,31876],[]),([5,31,2114,9192,16927,31876],[]),([5,31,2114,9192,17040,31744],[]),([5,31,2114,9513,18417],[(0,3464),(2,361608),(4,3464),(6,66760),(8,3464),(10,68776),(12,3464),(14,400388),(73,3464),(81,3464),(82,3464),(106,3464)]),([5,31,2114,11242,16912,31876],[]),([5,31,2114,16912,23575,31876],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,2114,18417,21140],[(0,68776),(2,361608),(4,68776),(6,68776),(8,68776),(10,68776),(12,68776),(14,3464),(58,66728),(81,68776),(82,68776),(105,66760),(106,68776)]),([5,31,2114,24840,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,269380),(81,171278),(82,171278),(97,72898),(98,171278),(105,203842),(106,171278)]),([5,31,2114,25368,32305],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,269380),(81,134410),(82,134410),(105,203842),(106,134410)]),([5,31,2146,8456,17392],[(0,275784),(2,361608),(4,275784),(6,1192),(8,275784),(10,3336),(12,275784),(14,335118),(73,265544),(81,275784),(82,275784),(98,275784),(106,275784)]),([5,31,3042,4228,11242,16927],[(56,0),(72,14504)]),([5,31,3042,4255,11242,16912],[(56,0),(72,145570),(128,14504)]),([5,31,3042,5285,17969],[(0,134346),(2,197775),(4,134346),(6,400590),(8,134346),(10,203844),(12,134346),(14,205956),(58,132298),(73,134346),(105,210312)]),([5,31,3042,5285,21140],[(0,134312),(2,197775),(4,134312),(6,400590),(8,134312),(10,134312),(12,134312),(14,171140),(58,132264),(73,134312),(82,134312)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,3042,8456,17040],[(0,275458),(2,165007),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(73,145570),(82,145570),(98,275458),(105,275458),(113,134408),(114,269444)]),([5,31,3042,8456,17040,31744],[]),([5,31,3042,9192,16912,31876],[]),([5,31,3042,12684,21140],[(0,68778),(2,165007),(4,68778),(6,1294),(8,68778),(10,68778),(12,68778),(14,407556),(73,68778),(82,68776)]),([5,31,3042,12684,25368],[(0,269380),(2,165007),(4,269380),(6,1294),(8,269380),(10,269380),(12,269380),(14,271492),(73,269380)]),([5,31,3042,17969,21140],[(0,68778),(2,197775),(4,68778),(6,400590),(8,68778),(10,68778),(12,68778),(14,3471),(58,66730),(81,68778),(82,68776)]),([5,31,3042,21140,25368],[(0,134312),(2,165007),(4,134312),(6,1294),(8,134312),(10,171140),(12,134312),(14,134312),(106,134312)]),([5,31,3071,4228,11242,16912],[(72,0),(128,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,3105,4228,32272],[(0,132298),(2,197704),(4,132298),(6,132298),(8,132298),(10,132298),(12,132298),(14,66760),(57,132298),(81,132298),(82,132298),(106,132298)]),([5,31,3171,4228,8456,17392,31777],[(56,0),(96,0)]),([5,31,3171,4228,8456,18417,31744],[(56,0),(96,0)]),([5,31,3171,4228,9513,17392,31744],[]),([5,31,3171,4228,32305],[(0,1290),(2,197704),(4,1290),(6,1290),(8,1290),(10,1290),(12,1290),(14,68872),(58,1290),(81,1290),(82,1290),(109,132298)]),([5,31,3171,4228,32338],[(0,134146),(2,197704),(4,134146),(6,134146),(8,134146),(10,134146),(12,134146),(14,68872),(81,134146),(82,134146)]),([5,31,3171,5092,8456,16912,31777],[(56,0),(96,0)]),([5,31,3171,5092,8456,17969,31744],[(56,0),(96,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,3171,5092,9513,16912,31744],[]),([5,31,3171,5285,8456,17392,31744],[(56,0)]),([5,31,3171,5285,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,1288),(58,132362),(106,134410)]),([5,31,3171,6117,8456,16912,31744],[]),([5,31,3171,6342,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,68610),(106,134410)]),([5,31,3171,8456,18417],[(0,1416),(2,361608),(4,1416),(6,66728),(8,1416),(10,68872),(12,1416),(14,400386),(73,1416),(81,1416),(82,1416)]),([5,31,3171,8456,19442],[(0,275458),(2,165000),(4,275458),(6,132264),(8,275458),(10,68872),(12,275458),(14,1294),(73,265218),(81,275458),(82,275458),(101,265288),(109,275784)]),([5,31,3171,9513,17392],[(0,275848),(2,361608),(4,275848),(6,66564),(8,275848),(10,68610),(12,275848),(14,400654),(73,265608),(98,275848),(106,275848)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,3171,10570,17392],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,1288),(12,275848),(14,400654),(58,275848),(98,275848),(106,275848)]),([5,31,4065,4228,16912],[(0,132266),(2,132266),(4,132266),(6,400386),(8,132266),(10,171074),(12,132266),(14,173186),(57,132106),(73,132266),(101,66568),(105,1416),(113,66728),(114,132266)]),([5,31,4228,9192,16912,31746],[(96,0)]),([5,31,4228,9194,16912,31744],[(56,0),(96,0)]),([5,31,4228,25104,31777],[(0,132270),(2,197704),(4,132270),(6,203842),(8,132270),(10,177282),(12,132270),(14,132270),(81,66760),(82,132270),(97,72898),(105,66760),(114,66760)]),([5,31,4228,25368,32305],[(0,1290),(2,197704),(4,1290),(6,1290),(8,1290),(10,1290),(12,1290),(14,66760),(74,1290),(81,1290),(82,1290),(105,66760),(117,66760)]),([5,31,4228,25368,32338],[(0,134146),(2,197704),(4,134146),(6,134146),(8,134146),(10,134146),(12,134146),(14,132100),(58,134146),(81,134146),(82,134146),(105,203842)]),([5,31,5285,6342,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,369832),(74,132362)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,8456,16912,31842],[(0,171010),(2,164872),(4,171010),(6,171010),(8,171010),(10,171010),(12,171010),(14,269316),(74,171010),(81,171010),(82,171010),(114,171010),(117,171010)]),([5,31,8456,17040,31810],[(0,138434),(2,197768),(4,138434),(6,138434),(8,138434),(10,138434),(12,138434),(14,138434),(81,134408),(82,269444),(114,132296)]),([5,31,8456,18417,21140],[(0,66728),(2,361608),(4,66728),(6,66728),(8,66728),(10,66728),(12,66728),(14,1416),(57,66728),(58,66728),(81,66728),(105,68872),(106,66728)]),([5,31,8456,19442,21140],[(0,132264),(2,165000),(4,132264),(6,132264),(8,132264),(10,132264),(12,132264),(14,275458),(57,132264),(77,132264),(81,132264),(105,68872),(106,132264),(118,275458)]),([5,31,8488,16912,31810],[(0,203778),(2,166920),(4,203778),(6,203778),(8,203778),(10,203778),(12,203778),(14,171012),(74,203778),(81,203778),(82,203778),(114,203778),(117,203778)]),([5,31,9192,10570,16912,31876],[(140,140482)]),([5,31,9192,11242,16912,31876],[(140,145570)]),([5,31,9192,16912,30653,31876],[(100,328872)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,9192,16912,31810,31876],[]),([5,31,9513,10570,17392],[(0,275848),(2,361608),(4,275848),(6,373928),(8,275848),(10,3272),(12,275848),(14,400654),(56,0),(57,265608),(58,275848),(98,275848)]),([5,31,9513,17969,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,3279),(114,203842)]),([5,31,9513,25368,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,171140),(105,171140)]),([5,31,10570,19026,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,373935),(74,171278),(97,72898),(98,171278),(114,171278),(117,171214)]),([5,31,10570,25368,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,203842),(74,171278),(97,72898),(98,171278),(105,203842),(117,203842)]),([5,31,12684,21140,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,68783),(58,1294),(97,72898),(109,66735)]),([5,31,12684,21140,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,68778)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([5,31,12684,25368,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,132164),(97,72898),(105,66692)]),([5,31,12684,25368,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,269380),(105,271492)]),([5,31,17969,25368,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,269380),(105,134410),(106,203842)]),([5,31,19026,25368,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,132164),(97,72898),(98,171278),(105,134210),(106,171278)]),([5,31,21140,25368,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,66760),(74,1294),(97,72898),(105,66760),(117,66760)]),([5,31,21140,25368,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,134312),(105,134312)]),([5,63,2114,8456,17392],[(0,275784),(2,361608),(4,275784),(6,1224),(8,275784),(10,3336),(12,275784),(14,335118),(73,265544),(81,275784),(82,275784),(98,275784),(106,275784)]),([5,63,8456,16912,31810],[(0,203778),(2,197640),(4,203778),(6,203778),(8,203778),(10,203778),(12,203778),(14,269316),(74,203778),(81,203778),(82,203778),(114,203778),(117,203778)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([5,130,3042,4255,8456,16912],[(56,145570),(72,145570),(96,145666),(128,275586)]),([5,159,2114,9192,16912,31744],[]),([5,159,3042,8456,16912],[(0,275458),(2,165007),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(73,145570),(82,145570),(98,275458),(105,275458),(113,134410),(114,271492)]),([5,159,3042,8456,16912,31744],[]),([5,287,1057,2114,4228,17392,31744],[(72,0)]),([5,287,1057,2114,5092,16912,31744],[(72,0)]),([5,1023,2114,4228,9192,16927],[]),([5,1023,2114,4255,9192,16912],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([5,1023,3042,4255,8456,16912],[(60,145570),(76,275458)]),([5,1057,1087,2114,5092,16912,32008],[]),([5,1057,2079,4228,32272],[(0,132298),(2,132298),(4,132298),(6,132298),(8,132298),(10,132298),(12,132298),(14,66760),(58,132298),(73,132298),(74,132298),(98,132298)]),([5,1057,2114,2143,5092,16912,32008],[]),([5,1057,2114,4228,8479,17392,31744],[]),([5,1057,2114,4228,8479,17392,31777],[(56,0)]),([5,1057,2114,4228,8479,17392,32008],[]),([5,1057,2114,4228,8479,18417,31744],[(56,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([5,1057,2114,4228,8479,21492,31744],[]),([5,1057,2114,5092,8479,16912,31744],[]),([5,1057,2114,5092,8479,16912,31777],[(56,0)]),([5,1057,2114,5092,8479,16912,32008],[]),([5,1057,2114,5092,8479,17392,31744],[]),([5,1057,2114,5092,8479,17969,31744],[(56,0)]),([5,1057,2114,5092,8479,21140,31744],[]),([5,1057,2114,5092,8479,21492,31744],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([5,1057,2114,5092,9535,16912,31744],[]),([5,1057,2114,5092,10591,16912,31744],[]),([5,1057,2114,5285,8479,17392,31744],[]),([5,1057,2114,6117,8479,16912,31744],[]),([5,1057,2114,8456,12319],[(0,72898),(2,72898),(4,72898),(6,66760),(8,72898),(10,68872),(12,72898),(14,197704),(57,72898),(58,72898),(73,72898),(74,72898),(81,72898),(82,72898),(97,269316),(98,72898)]),([5,1057,2114,8456,19424],[(0,197704),(2,197704),(4,197704),(6,66760),(8,197704),(10,68872),(12,197704),(14,72898),(57,197704),(58,197704),(73,197704),(74,197704),(81,197704),(82,197704),(98,197704),(101,197640)]),([5,1057,2143,5092,8456,16912,31744],[]),([5,1057,2143,5092,8456,16912,31777],[(56,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([5,1057,2143,5092,8456,17392,31744],[]),([5,1057,2143,5092,8456,17969,31744],[(56,0)]),([5,1057,2143,5092,8456,21140,31744],[]),([5,1057,2143,5092,8456,21492,31744],[]),([5,1057,2143,5092,8456,31744,32272],[]),([5,1057,2143,5285,8456,17392,31744],[(56,0)]),([5,1057,2143,6117,8456,16912,31744],[]),([5,1057,3042,4255,10570],[(0,205892),(2,205892),(4,205892),(6,72910),(8,205892),(10,197711),(12,205892),(14,68810),(58,205892),(73,205828),(74,205892),(97,80066),(98,205892)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([5,1057,8456,16415,31810],[(0,203842),(2,203842),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,72898),(57,203842),(58,203842),(73,203778),(74,203842),(97,72898),(98,203842)]),([5,1057,8479,10570,17392],[(0,263560),(2,263560),(4,263560),(6,361608),(8,263560),(10,66760),(12,263560),(14,400642),(56,0),(57,263560),(58,263560),(73,263560),(74,263560),(98,263560),(101,263496)]),([5,1087,2017,2114,4228,8456,32272],[(72,0)]),([5,1087,2114,4228,8456,17392,31777],[(56,0)]),([5,1087,2114,4228,8456,18417,31744],[(56,0)]),([5,1087,2114,4228,32305],[(0,3338),(2,3338),(4,3338),(6,3338),(8,3338),(10,3338),(12,3338),(14,68872),(58,1290),(81,3338),(82,3338),(106,3338),(109,1226)]),([5,1087,2114,5092,8456,16912,31777],[(56,0)]),([5,1087,2114,5092,8456,17969,31744],[(56,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([5,1087,2114,5285,8456,17392,31744],[(56,0)]),([5,1087,2114,5285,32272],[(0,134410),(2,134410),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,3336),(58,132362),(81,134410),(82,134410),(106,134410),(109,132298)]),([5,1087,2114,6117,8456,16912,31744],[]),([5,1087,2114,8456,12288],[(0,400654),(2,197640),(4,400654),(6,1224),(8,400654),(10,3336),(12,400654),(14,275848),(81,400654),(82,400654),(97,7362),(98,400654),(105,203778),(106,400654)]),([5,1087,2114,8456,15360],[(0,400654),(2,197640),(4,400654),(6,1224),(8,400654),(10,3336),(12,400654),(14,275848),(81,400654),(82,400654),(97,7362),(98,400654),(105,203778),(106,400654)]),([5,1087,2114,8456,15375],[(0,400654),(2,361608),(4,400654),(6,1224),(8,400654),(10,3336),(12,400654),(14,275848),(73,400644),(81,400654),(82,400654),(98,400654),(106,400654)]),([5,1087,2114,8456,17376],[(0,275848),(2,361640),(4,275848),(6,1224),(8,275848),(10,3336),(12,275848),(14,400654),(73,265608),(81,275848),(82,275848),(98,275848),(106,275848)]),([5,1087,2114,8456,17392],[(0,275848),(2,361608),(4,275848),(6,1224),(8,275848),(10,3336),(12,275848),(14,400654),(73,265608),(81,275848),(82,275848),(98,275848),(106,275848)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([5,1087,2114,8456,17407],[(0,275848),(2,197640),(4,275848),(6,1224),(8,275848),(10,3336),(12,275848),(14,400654),(81,275848),(82,275848),(98,275848),(101,275784),(106,275848),(109,275816)]),([5,1087,2114,8456,18417],[(0,275848),(2,361480),(4,275848),(6,66760),(8,275848),(10,68872),(12,275848),(14,400654),(73,265608),(81,275848),(82,275848),(98,275848),(106,275848)]),([5,1087,2114,8456,18431],[(0,275848),(2,197640),(4,275848),(6,1224),(8,275848),(10,3336),(12,275848),(14,400654),(81,275848),(82,275848),(98,275848),(101,275848),(106,275848),(109,275816)]),([5,1087,2114,8456,19442],[(0,275848),(2,197768),(4,275848),(6,132296),(8,275848),(10,3336),(12,275848),(14,400654),(73,265608),(81,275848),(82,275848),(98,275848),(101,265224),(106,275848),(109,275848)]),([5,1087,2114,10570,17392],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,3336),(12,275848),(14,400654),(58,275848),(82,275848),(85,275848),(98,275848),(105,203780),(106,275848)]),([5,1087,2114,17392,24311],[(0,3336),(2,361608),(4,3336),(6,1224),(8,3336),(10,3336),(12,3336),(14,275848),(74,3336),(82,3336),(101,396552),(106,3336),(109,3336)]),([5,1087,2114,24840,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,269316),(81,400654),(82,400654),(97,7362),(98,400654),(105,203778),(106,400654)]),([5,1087,2114,25368,32272],[(0,134410),(2,134410),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,269316),(81,134410),(82,134410),(105,203778),(106,134410)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([5,1087,3042,4228,10570],[(0,205828),(2,197647),(4,205828),(6,400590),(8,205828),(10,205828),(12,205828),(14,3274),(58,205826),(73,205828),(74,205828),(82,203780),(113,203844),(114,205828)]),([5,1087,3042,4228,17969],[(0,3274),(2,197647),(4,3274),(6,400590),(8,3274),(10,203844),(12,3274),(14,205828),(58,1226),(73,3274),(105,210312),(113,68808),(114,3274)]),([5,1087,3042,5285,16912],[(0,134346),(2,197775),(4,134346),(6,400590),(8,134346),(10,203780),(12,134346),(14,205956),(58,132298),(105,210312),(113,3272),(114,134346)]),([5,1087,3042,10570,16912],[(0,203780),(2,197775),(4,203780),(6,400590),(8,203780),(10,3272),(12,203780),(14,203780),(58,203778),(98,203780),(105,210312),(106,203780),(113,203780),(114,205956)]),([5,1087,6210,8456,31744],[(0,269316),(2,197640),(4,269316),(6,1224),(8,269316),(10,3336),(12,269316),(14,269316),(81,203778),(82,269316),(98,269316),(106,269316),(113,269316),(118,269316)]),([5,1087,6342,8456,31810],[(0,203842),(2,203842),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,271364),(81,203842),(82,203842),(109,269316),(113,271364)]),([5,1087,6342,10570,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,203780),(58,400654),(98,400654),(109,203778),(113,203780)]),([5,1087,6342,12684,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,66564),(98,400654),(113,66564),(118,66564)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([5,1087,8456,10570,17392],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,1224),(12,275848),(14,400654),(56,0),(57,265608),(58,275848),(82,275848),(85,275848),(98,275848),(105,203778)]),([5,1087,8456,16927,31810],[(0,203778),(2,203778),(4,203778),(6,203778),(8,203778),(10,203778),(12,203778),(14,269316),(57,203778),(82,203778),(97,269316),(117,204046)]),([5,1087,8456,17392,30653],[(0,1224),(2,361608),(4,1224),(6,1224),(8,1224),(10,1224),(12,1224),(14,275848),(57,1224),(74,1224),(106,1224),(109,1224),(117,275848)]),([5,1087,8456,17969,31810],[(0,203842),(2,203842),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,328911),(81,203842),(82,203842),(114,203842),(117,203778)]),([5,1087,10570,12684,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,407918),(74,400654),(98,400654),(117,407918),(118,400654)]),([5,1087,10570,19026,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,374159),(74,400654),(97,7362),(98,400654),(114,400654),(117,400590)]),([5,1087,10570,25368,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,203778),(74,400654),(97,7362),(98,400654),(105,203778),(117,203778)]),([5,1087,19026,25368,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,132100),(97,7362),(98,400654),(105,134146),(106,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([5,2114,4228,9192,15840,31744],[(96,328719)]),([5,2114,4228,9192,16927,31744],[]),([5,2114,4228,9192,16927,31810],[(56,203791)]),([5,2114,4228,9192,21151,31744],[]),([5,2114,4255,5119,9192,16912],[]),([5,2114,4255,9192,15855,31744],[]),([5,2114,4255,9192,16912,31744],[]),([5,2114,4255,9192,16912,31876],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([5,2114,4255,9192,16927,31744],[]),([5,2114,4255,9192,21151,31744],[]),([5,2114,4255,11242,16912,31744],[]),([5,2114,4255,16912,23575,31744],[]),([5,2114,5183,8456,31744],[(0,269316),(2,1224),(4,269316),(6,197640),(8,269316),(10,3336),(12,269316),(14,269316),(73,203778),(74,269316),(98,269316),(106,269316),(113,269316),(118,269316)]),([5,2114,5311,8456,31807],[(0,7438),(2,7438),(4,7438),(6,7438),(8,7438),(10,7438),(12,7438),(14,271364),(73,7438),(74,7438),(81,7428),(98,7438),(109,269316)]),([5,2114,8456,9535,17392],[(0,265608),(2,1224),(4,265608),(6,265608),(8,265608),(10,361608),(12,265608),(14,400644),(56,0),(57,265608),(58,265608),(82,265608),(85,265608),(98,265608),(105,138594)]),([5,2114,8456,17392,31680],[(0,361608),(2,361608),(4,361608),(6,361608),(8,361608),(10,361608),(12,361608),(14,275848),(57,361608),(58,361608),(74,197768),(106,361608),(117,275848)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([5,2114,9192,16912,16927,31876],[]),([5,2114,9192,16912,21151,31744],[]),([5,2114,9192,16912,28512,31744],[(96,328878)]),([5,2114,9192,16912,31876,32736],[(128,166914)]),([5,2114,9192,16912,31876,32740],[(128,166914)]),([5,2114,9192,16927,21140,31744],[]),([5,2114,9192,16927,21151,31744],[]),([5,2114,9192,16927,28539,31744],[(108,334863)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([5,2114,9192,16927,31744,31876],[]),([5,3042,3071,4255,8456,16912],[(60,145570),(84,275458),(96,0)]),([5,3042,3171,4255,8456],[(0,271428),(2,1294),(4,271428),(6,271428),(8,271428),(10,164943),(12,271428),(14,68874),(81,271364),(105,80034),(106,271428),(113,80034)]),([5,3042,4255,7167,8456,16912],[(76,145570),(84,145570),(96,0)]),([5,3042,4255,8456,15855],[(0,145570),(2,1294),(4,145570),(6,165007),(8,145570),(10,145570),(12,145570),(14,145570),(74,145570),(81,145570),(101,140450),(106,275458),(114,145570),(117,145570)]),([5,3042,4255,8456,15855,31744],[]),([5,3042,4255,8456,16912],[(0,145570),(2,1294),(4,145570),(6,165007),(8,145570),(10,145570),(12,145570),(14,145570),(74,145570),(81,145570),(97,275458),(106,275458),(113,134410),(114,271492)]),([5,3042,4255,8456,16912,31744],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([5,3042,4255,8456,16912,31777],[]),([5,3042,4255,8456,16912,31810],[]),([5,3042,4255,8456,16927],[(0,14504),(2,1294),(4,14504),(6,171023),(8,14504),(10,14504),(12,14504),(14,14504),(74,14504),(81,14504),(106,275458),(114,271364)]),([5,3042,4255,8456,16927,31744],[]),([5,3042,4255,8456,21140],[(0,80034),(2,1294),(4,80034),(6,164943),(8,80034),(10,80034),(12,80034),(14,80034),(74,80034),(81,80034),(106,275458),(113,68874),(114,271428)]),([5,3042,4255,8456,21151],[(0,275458),(2,1294),(4,275458),(6,275458),(8,275458),(10,275458),(12,275458),(14,275458),(81,275458),(106,275458),(109,275458),(114,271364)]),([5,3042,4255,8456,21151,31744],[]),([5,3042,4255,8456,25368],[(0,271492),(2,1294),(4,271492),(6,165007),(8,271492),(10,134410),(12,271492),(14,271492),(81,145570),(106,271364),(114,271492),(117,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([5,3042,8456,12703,16912],[(0,145570),(2,1284),(4,145570),(6,3330),(8,145570),(10,165007),(12,145570),(14,145570),(77,263172),(82,145570),(85,145570),(97,265218),(105,263172),(106,145570),(114,263172)]),([5,3042,8456,16912,21151,31744],[(148,275458)]),([5,3042,8456,16912,28512],[(0,165007),(2,1294),(4,165007),(6,165007),(8,165007),(10,165007),(12,165007),(14,145570),(58,165007),(73,165002),(81,165007),(82,165007),(106,165007),(117,275458)]),([5,3042,8456,16912,28512,31744],[(152,165007)]),([5,3042,8456,16927,21140,31744],[]),([5,3042,8456,16927,21151,31744],[(100,0),(148,275458)]),([5,3042,8456,16927,28539,31744],[(100,334863)]),([5,3042,9192,16912,31876],[(0,361615),(2,361615),(4,361615),(6,361615),(8,361615),(10,361615),(12,361615),(14,164868),(73,361615),(81,361615),(97,166914)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([5,8456,16912,31807,31909],[(0,1167),(2,1167),(4,1167),(6,1167),(8,1167),(10,1167),(12,1167),(14,7362),(57,1167),(58,1167),(77,1167),(98,1167),(101,1167)]),([6,1,992,4228,8479,16912],[(0,132266),(2,132266),(4,132266),(6,400642),(8,132266),(10,171074),(12,132266),(14,328847),(16,132266),(18,173186),(56,0),(57,132266),(58,132266),(72,0),(73,132266),(74,132266),(98,132266),(101,132266),(106,132266),(114,132266),(128,0),(129,145730),(130,132266),(137,263560),(145,66728),(146,132266)]),([6,1,992,8456,16912,31876],[(0,66703),(2,66703),(4,66703),(6,66703),(8,66703),(10,66703),(12,66703),(14,66703),(16,66703),(18,132175),(56,0),(57,66703),(58,66703),(73,66703),(74,66703),(82,66703),(96,0),(97,66703),(98,66703),(113,66703),(114,66703),(128,0),(129,132175),(130,66703),(146,66703),(149,66703)]),([6,2,31,128,992,8456,16912],[(80,275464),(96,275458),(128,0)]),([6,2,31,992,4228,9192,16912],[(72,177154),(104,145576),(128,0)]),([6,2,31,992,8456,16912,31876],[(60,265288),(96,0)]),([6,2,31,4228,9192,16912,31744],[]),([6,2,992,4228,8456,16927,31744],[(56,0),(96,0),(168,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([6,2,992,4228,9192,16912,31744],[(56,164868),(96,0)]),([6,2,992,4255,8456,16912],[(0,145576),(2,145576),(4,145576),(6,7438),(8,145576),(10,171151),(12,145576),(14,145576),(16,145576),(18,145576),(56,0),(57,145576),(58,145576),(74,145576),(77,145576),(96,0),(97,145576),(98,145576),(106,145576),(113,145576),(129,145576),(130,145576),(137,275464),(146,275464),(153,134410),(154,271492)]),([6,2,992,4255,8456,16912,31744],[(56,0),(96,0)]),([6,2,992,8456,16912,31876],[(0,265288),(2,265288),(4,265288),(6,72964),(8,265288),(10,265288),(12,265288),(14,265288),(16,265288),(18,265288),(57,0),(58,265288),(72,0),(73,265288),(74,265288),(97,265288),(98,265288),(113,134410),(114,271492),(129,265288),(130,265288),(146,269380)]),([6,10,992,4228,8456,16912,31744],[(96,263240)]),([6,16,31,992,1057,2114,4228,32008],[]),([6,16,31,1057,2114,5092,8456,31744],[]),([6,16,992,1057,2114,4228,8479,31744],[(56,0),(72,0),(128,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([6,16,992,1057,2143,4228,8456,31744],[(56,0),(72,0),(128,0),(216,0)]),([6,18,992,4228,8456,16912],[(0,132111),(2,1167),(4,132111),(6,72964),(8,132111),(10,132111),(12,132111),(14,132111),(16,132111),(18,14466),(57,132111),(58,132111),(73,132111),(74,132111),(86,132111),(96,0),(97,132111),(98,132111),(106,132111),(113,132111),(114,132111),(137,265288),(145,265288),(146,132111),(153,265288),(154,132111)]),([6,20,992,1057,2114,4228,8456,31744],[(72,0)]),([6,29,992,4228,8456,16912,31744],[(72,1192),(104,328878),(128,328719),(184,328872)]),([6,30,992,4228,8456,16912],[(0,132111),(2,1167),(4,132111),(6,400654),(8,132111),(10,171074),(12,132111),(14,132111),(16,132111),(18,14466),(57,132111),(58,132111),(73,132111),(96,0),(97,132111),(98,132111),(106,132111),(113,132111),(114,132111),(137,275848),(145,66728),(146,132111),(153,134410),(154,132111)]),([6,30,4228,8456,16912,31744],[(0,400654),(2,1096),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132106),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72706),(130,400654),(137,66568),(149,132106),(154,400654)]),([6,31,159,992,2114,8456,16912],[(56,275464),(100,275464),(112,275458),(168,14504)]),([6,31,159,2114,8456,16912,31744],[(128,7338),(168,7438)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,495,1057,2114,4228],[(0,68872),(2,197704),(4,68872),(6,134410),(8,68872),(10,68872),(12,68872),(14,68872),(16,68872),(18,269380),(73,68872),(81,68872),(98,66824),(105,68872),(106,66760),(113,68872),(114,68872),(145,271492),(146,68872),(153,66760),(154,68872)]),([6,31,891,992,2114,8456,16912],[(56,197770),(100,265288)]),([6,31,957,1057,8456,16912],[(0,269380),(2,197704),(4,269380),(6,203842),(8,269380),(10,269380),(12,269380),(14,68872),(16,269380),(18,269380),(73,269380),(74,269316),(81,269380),(86,269380),(113,66760),(114,269380),(130,269380),(137,66760),(138,269380),(145,269380),(146,269380),(153,269380),(154,271492)]),([6,31,957,4228,8456,16912],[(0,1416),(2,197704),(4,1416),(6,400386),(8,1416),(10,1416),(12,1416),(14,1416),(16,1416),(18,1416),(74,1416),(86,72898),(113,269380),(114,68872),(130,1416),(137,1416),(145,1416),(146,1416),(153,134410),(154,271492)]),([6,31,990,2114,8456,16912],[(0,269380),(2,197704),(4,269380),(6,171278),(8,269380),(10,66760),(12,269380),(14,68872),(16,269380),(18,269380),(58,269316),(61,269326),(81,269380),(86,269380),(113,203842),(114,269380),(130,269380),(137,275624),(138,269380),(145,203842),(146,269380),(153,269380),(154,271492)]),([6,31,990,4228,8456,16912],[(0,132271),(2,197704),(4,132271),(6,1294),(8,132271),(10,203842),(12,132271),(14,132271),(16,132271),(18,178306),(61,132111),(86,132271),(98,132271),(106,132271),(113,132271),(114,132271),(137,275458),(145,66760),(146,132271),(153,134410),(154,132271)]),([6,31,992,1057,2114,4228,8456,31760],[(96,0)]),([6,31,992,1057,2114,4228,8456,32272],[(96,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,1057,2114,4228,8456,32305],[(72,0),(96,0),(112,0)]),([6,31,992,1057,2114,4228,8479,32272],[(96,0)]),([6,31,992,1057,2114,4228,9513,32272],[(96,0),(112,0)]),([6,31,992,1057,2114,4228,10570,32272],[(96,0),(180,0)]),([6,31,992,1057,2114,4228,32008,32272],[(96,0)]),([6,31,992,1057,2114,4244,8456,31744],[(96,0),(168,0)]),([6,31,992,1057,2114,5092,16912,32008],[]),([6,31,992,1057,2114,5285,8456,32272],[(72,0),(96,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,1057,2114,5285,16912,32008],[(72,0),(112,0)]),([6,31,992,1057,2114,24840],[(0,269380),(2,269380),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(57,269380),(58,269380),(72,0),(73,269380),(74,269316),(81,269380),(86,269316),(101,269380),(105,269380),(113,269380),(114,269380),(129,203842),(145,203842),(146,269380),(153,203842),(154,269380)]),([6,31,992,1057,6210,8456],[(0,269380),(2,361551),(4,269380),(6,269380),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(57,269380),(58,269380),(72,0),(73,269380),(74,269316),(81,269380),(105,269380),(113,269380),(114,269380),(129,80226),(141,203842),(145,203842),(146,269380),(153,203842),(154,269380)]),([6,31,992,1057,6342,10570],[(0,203842),(2,361615),(4,203842),(6,400654),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,66760),(57,203842),(58,203842),(72,0),(73,203842),(74,203780),(81,203842),(98,203842),(106,203842),(113,203842),(114,203842),(145,275848),(146,203842)]),([6,31,992,1057,6342,12684],[(0,66692),(2,361615),(4,66692),(6,400654),(8,66692),(10,66692),(12,66692),(14,132164),(16,66692),(18,134210),(57,66692),(58,66692),(72,0),(73,66692),(74,66564),(81,66692),(113,66692),(114,66692),(129,145762),(141,66692),(145,68738),(146,66692)]),([6,31,992,1057,10570,12684],[(0,407918),(2,361615),(4,407918),(6,400654),(8,407918),(10,407918),(12,407918),(14,68810),(16,407918),(18,374159),(57,407918),(58,407918),(72,0),(73,407918),(74,407918),(81,407918),(113,407918),(114,407918),(128,0),(129,145762),(130,407918),(138,407918),(141,402638),(145,205892),(146,407918)]),([6,31,992,1057,10570,19026],[(0,374159),(2,361615),(4,374159),(6,400654),(8,374159),(10,374159),(12,374159),(14,68810),(16,374159),(18,407918),(57,374159),(58,374159),(72,0),(73,374159),(74,374159),(81,374159),(86,374095),(113,374159),(114,374159),(130,374159),(133,363599),(137,275848),(138,374159),(145,205892),(146,374159)]),([6,31,992,1057,10570,25368],[(0,203842),(2,361615),(4,203842),(6,400654),(8,203842),(10,203842),(12,203842),(14,66760),(16,203842),(18,203842),(57,203842),(58,203842),(72,0),(73,203842),(74,203778),(81,203842),(86,203778),(113,275848),(114,203842),(130,203842),(138,203842),(145,203842),(146,203842)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,1057,12684,25368],[(0,132164),(2,361615),(4,132164),(6,400654),(8,132164),(10,132164),(12,132164),(14,132164),(16,132164),(18,66692),(57,132164),(58,132164),(73,132164),(78,132164),(81,132164),(82,132164),(97,132164),(109,132164),(113,132164),(114,132164),(145,66692),(146,132164)]),([6,31,992,1073,2114,4228,8456,31744],[(96,0),(168,0)]),([6,31,992,2114,4228,9192,16927],[(80,177154),(96,14504)]),([6,31,992,2114,4228,9513,17969,31744],[(72,0),(128,0)]),([6,31,992,2114,4255,9192,16912],[(76,145576),(80,177154),(96,145576),(168,14504)]),([6,31,992,2114,5153,8456],[(0,269380),(2,361551),(4,269380),(6,269380),(8,269380),(10,66760),(12,269380),(14,269380),(16,269380),(18,68872),(57,269380),(58,269380),(81,269380),(96,0),(97,269380),(98,269316),(105,269380),(113,269380),(114,269380),(129,80226),(141,203842),(145,203842),(146,269380),(153,203842),(154,269380)]),([6,31,992,2114,5285,8456,16912,31777],[(72,0),(128,0)]),([6,31,992,2114,5285,8456,17969,31744],[(72,0),(128,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,2114,5285,9513],[(0,171140),(2,361615),(4,171140),(6,400654),(8,171140),(10,132298),(12,171140),(14,171140),(16,171140),(18,134312),(57,171140),(58,171140),(81,171140),(97,171140),(106,171140),(113,171140),(114,171140),(129,145762),(145,205954),(146,171140)]),([6,31,992,2114,5285,9513,16912,31744],[(72,0),(128,0)]),([6,31,992,2114,5285,12684],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,132298),(12,271492),(14,269380),(16,271492),(18,134410),(57,271492),(58,271492),(81,271492),(97,271492),(113,271492),(114,271492),(129,145762),(141,68872),(145,205954),(146,271492)]),([6,31,992,2114,5285,17969],[(0,134410),(2,361615),(4,134410),(6,400654),(8,134410),(10,134410),(12,134410),(14,269380),(16,134410),(18,271492),(57,134410),(58,134410),(74,132362),(81,134410),(82,134346),(97,134410),(113,134410),(114,134410),(137,275848),(145,132298),(146,134410)]),([6,31,992,2114,5285,21140],[(0,134312),(2,361615),(4,134312),(6,400654),(8,134312),(10,134312),(12,134312),(14,134312),(16,134312),(18,171140),(57,134312),(58,134312),(74,132264),(81,134312),(82,134312),(97,134312),(106,134312),(113,134312),(114,134312),(145,132298),(146,134312)]),([6,31,992,2114,8456,15855,31876],[(76,265288),(128,361640)]),([6,31,992,2114,8456,16912,31872],[(76,265354),(128,0)]),([6,31,992,2114,8456,16912,31876],[(76,265288)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,2114,8456,16912,32404],[(104,145572),(152,134312)]),([6,31,992,2114,8456,16927,31876],[]),([6,31,992,2114,8456,17040],[(0,145762),(2,361615),(4,145762),(6,145762),(8,145762),(10,145762),(12,145762),(14,145762),(16,145762),(18,145762),(57,145762),(58,138434),(81,145602),(82,145762),(97,145762),(106,145762),(109,138434),(113,145762),(114,145762),(137,138594),(145,132296),(146,203906),(153,134408),(154,269444)]),([6,31,992,2114,8456,17040,31744],[(76,265352),(128,0)]),([6,31,992,2114,8488,16912],[(0,171012),(2,361615),(4,171012),(6,335022),(8,171012),(10,1224),(12,171012),(14,3240),(16,171012),(18,171012),(57,171012),(58,171012),(81,171012),(97,145762),(113,203778),(114,171012),(130,171012),(137,177480),(138,171012),(145,203778),(146,171012),(153,171012),(154,173188)]),([6,31,992,2114,9192,16912,31876],[]),([6,31,992,2114,9513,12684],[(0,407556),(2,361615),(4,407556),(6,400654),(8,407556),(10,132298),(12,407556),(14,68778),(16,407556),(18,3471),(57,407556),(58,407556),(81,407556),(97,407556),(113,407556),(114,407556),(129,145762),(138,407556),(141,402436),(145,205954),(146,407556)]),([6,31,992,2114,9513,17969],[(0,3471),(2,361615),(4,3471),(6,400654),(8,3471),(10,66760),(12,3471),(14,68778),(16,3471),(18,407556),(57,3471),(58,3471),(81,3471),(97,3471),(113,3471),(114,3471),(137,275848),(138,3471),(145,203842),(146,3471)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,2114,9513,25368],[(0,171140),(2,361615),(4,171140),(6,400654),(8,171140),(10,66760),(12,171140),(14,134312),(16,171140),(18,171140),(57,171140),(58,171140),(81,171140),(97,145762),(113,203842),(114,171140),(138,171140),(145,203842),(146,171140)]),([6,31,992,2114,10570,16912,31876],[(72,361640),(80,367620),(144,373930)]),([6,31,992,2114,12684,21140],[(0,68778),(2,361615),(4,68778),(6,400654),(8,68778),(10,68778),(12,68778),(14,68778),(16,68778),(18,407556),(57,68778),(58,68778),(78,68778),(81,68778),(82,68778),(97,68778),(106,68776),(109,68778),(113,68778),(114,68778),(145,132298),(146,68778)]),([6,31,992,2114,12684,25368],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,269380),(16,269380),(18,271492),(57,269380),(58,269380),(78,269380),(81,269380),(82,269380),(97,269380),(109,269380),(113,269380),(114,269380),(145,132298),(146,269380)]),([6,31,992,2114,16912,24311,31876],[(76,265288)]),([6,31,992,2114,17969,21140],[(0,68778),(2,361615),(4,68778),(6,400654),(8,68778),(10,68778),(12,68778),(14,68778),(16,68778),(18,3471),(57,68778),(58,68778),(74,66730),(81,68778),(82,68778),(105,68778),(106,68776),(113,68778),(114,68778),(145,66760),(146,68778)]),([6,31,992,2114,17969,25368],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,66760),(12,269380),(14,269380),(16,269380),(18,134410),(57,269380),(58,269380),(81,269380),(105,269380),(113,269380),(114,269380),(145,203842),(146,269380)]),([6,31,992,2114,21140,25368],[(0,134312),(2,361615),(4,134312),(6,400654),(8,134312),(10,134312),(12,134312),(14,171140),(16,134312),(18,134312),(57,134312),(58,134312),(78,134312),(81,134312),(82,134312),(113,66760),(114,134312),(138,134312),(145,134312),(146,134312)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,2146,8456,16912],[(0,269316),(2,361615),(4,269316),(6,335118),(8,269316),(10,1192),(12,269316),(14,3336),(16,269316),(18,269316),(57,269316),(58,269316),(81,269316),(97,145762),(113,171010),(114,269316),(130,269316),(137,275784),(138,269316),(145,171010),(146,269316),(153,269316),(154,271492)]),([6,31,992,3042,4255,8456,16912],[(60,145570),(76,145576),(80,275458),(96,145576),(108,275458),(136,177154),(168,14504)]),([6,31,992,3042,8456,16912,31876],[(76,265288),(180,275458)]),([6,31,992,3171,5285,8456],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,132264),(12,271492),(14,271492),(16,271492),(18,134410),(57,271492),(58,271492),(81,271492),(97,271492),(106,269444),(129,145762),(145,171138),(146,271492),(153,269380),(154,271492)]),([6,31,992,3171,5285,8456,16912,31744],[(72,0),(128,0),(248,0)]),([6,31,992,3171,6342,8456],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,66730),(12,271492),(14,1423),(16,271492),(18,134410),(57,271492),(58,271492),(81,271492),(106,269444),(129,145762),(145,173122),(146,271492),(153,407554),(154,271492)]),([6,31,992,3171,6342,16912],[(0,134410),(2,361615),(4,134410),(6,400654),(8,134410),(10,66564),(12,134410),(14,1092),(16,134410),(18,271492),(57,134410),(58,134410),(81,134410),(137,275848),(145,3138),(146,134410),(153,68610),(154,134410)]),([6,31,992,3171,8456,17969],[(0,1423),(2,361615),(4,1423),(6,400654),(8,1423),(10,66730),(12,1423),(14,68872),(16,1423),(18,407554),(57,1423),(58,1423),(81,1423),(97,1423),(113,1423),(114,1423),(137,275848),(138,1423),(153,269380),(154,1423)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_54 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,3171,8456,19026],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,132264),(12,269380),(14,68872),(16,269380),(18,269380),(57,269380),(58,269380),(81,269380),(97,145762),(113,171138),(114,269380),(133,269380),(137,275848),(138,269380),(153,269380),(154,271492)]),([6,31,992,3171,9513,16912],[(0,1092),(2,361615),(4,1092),(6,400654),(8,1092),(10,66564),(12,1092),(14,68610),(16,1092),(18,1092),(57,1092),(58,1092),(81,1092),(97,145762),(130,1092),(137,275848),(138,1092),(145,3138),(146,1092),(153,1092),(154,271492)]),([6,31,992,3171,10570,16912],[(0,269314),(2,361615),(4,269314),(6,400654),(8,269314),(10,269314),(12,269314),(14,1288),(16,269314),(18,269314),(57,269314),(58,269314),(74,269314),(81,269314),(130,269314),(137,275848),(138,269314),(145,269314),(146,269314),(153,269314),(154,271492)]),([6,31,992,6342,8456,19026],[(0,203842),(2,361615),(4,203842),(6,400654),(8,203842),(10,132298),(12,203842),(14,203842),(16,203842),(18,66760),(57,203842),(58,203842),(97,203842),(106,203842),(113,203842),(114,203842),(133,203791),(137,275848),(153,134410),(154,203842)]),([6,31,992,6342,8456,21140],[(0,66730),(2,361615),(4,66730),(6,400654),(8,66730),(10,1423),(12,66730),(14,66730),(16,66730),(18,173122),(57,66730),(58,66730),(82,66728),(97,66730),(106,66730),(113,66730),(114,66730),(153,134410),(154,66730)]),([6,31,992,8456,10570,16912,31876],[(72,263496),(144,271362)]),([6,31,992,8456,16912,28539,31810],[(96,0),(140,334850)]),([6,31,992,8456,16912,31810,31876],[(96,0),(132,265288),(180,140482)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_54 : K_54.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_55 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,992,8456,17969,19026],[(0,203842),(2,361615),(4,203842),(6,400654),(8,203842),(10,68872),(12,203842),(14,203842),(16,203842),(18,132298),(57,203842),(58,203842),(73,203842),(105,203842),(113,269380),(114,132298),(133,203791),(137,275848),(145,269380),(146,203842)]),([6,31,992,8456,17969,21140],[(0,66730),(2,361615),(4,66730),(6,400654),(8,66730),(10,66730),(12,66730),(14,66730),(16,66730),(18,1423),(57,66730),(58,66730),(72,0),(73,66730),(74,66730),(82,66730),(105,66730),(106,66728),(113,66730),(114,1423),(145,68872),(146,66730)]),([6,31,992,8456,19026,21140],[(0,132264),(2,361615),(4,132264),(6,400654),(8,132264),(10,132264),(12,132264),(14,132264),(16,132264),(18,171138),(57,132264),(58,132264),(73,132264),(82,132264),(101,132264),(105,132264),(106,132264),(113,132264),(114,132264),(145,68872),(146,132264)]),([6,31,993,4228,8456,16912],[(0,132266),(2,328847),(4,132266),(6,400386),(8,132266),(10,171074),(12,132266),(14,132266),(16,132266),(18,173186),(57,132106),(73,132266),(96,0),(97,132266),(98,132266),(106,132266),(113,132266),(114,132266),(137,1416),(145,66728),(146,132266),(153,134410),(154,132266)]),([6,31,994,4228,8456,16912],[(0,275458),(2,165007),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,275458),(72,0),(73,145570),(74,275458),(86,275458),(97,145570),(106,145570),(113,269380),(114,68872),(130,275458),(137,275458),(145,275458),(146,275458),(153,134410),(154,271492)]),([6,31,994,4228,8456,16912,31744],[(72,0),(128,0)]),([6,31,1008,1057,2114,4228,8456,31744],[(96,0),(168,0)]),([6,31,1023,2114,4228,9192,16912],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_55 : K_55.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_56 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1023,3042,4228,8456,16912],[(60,275458),(84,275458),(108,275458),(168,0)]),([6,31,1057,2017,2114,4228,8456,32272],[(96,0)]),([6,31,1057,2017,2114,4228,16912,32008],[(56,0)]),([6,31,1057,2048,4228,32272],[(0,132298),(2,197704),(4,132298),(6,132298),(8,132298),(10,132298),(12,132298),(14,132298),(16,132298),(18,66760),(57,132298),(73,132298),(74,132298),(81,132298),(82,132298),(105,132298),(106,132298),(113,132298),(114,132298),(138,132298),(146,132298),(149,132298)]),([6,31,1057,2114,4228,5092,8456,32272],[(72,0)]),([6,31,1057,2114,4228,5092,16912,32008],[]),([6,31,1057,2114,4228,8456,17392,31744],[(72,0)]),([6,31,1057,2114,4228,8456,17392,31777],[(72,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_56 : K_56.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_57 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,2114,4228,8456,17392,32008],[]),([6,31,1057,2114,4228,8456,17392,32272],[(72,0),(128,0)]),([6,31,1057,2114,4228,8456,18417,31744],[(72,0)]),([6,31,1057,2114,4228,8456,21492,31744],[(72,0)]),([6,31,1057,2114,4228,8479,17392,31744],[(72,0)]),([6,31,1057,2114,4228,9513,17392,31744],[(72,0),(128,0)]),([6,31,1057,2114,4228,10570,17392,31744],[(72,0),(128,0)]),([6,31,1057,2114,4228,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(57,134410),(74,132362),(81,134410),(82,134410),(105,134410),(106,134410),(113,134410),(114,134410),(138,134410),(146,134410),(149,132298)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_57 : K_57.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_58 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,2114,4228,32305],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(57,134410),(58,3338),(74,132362),(81,134410),(82,134410),(105,134410),(106,134410),(113,134410),(114,134410),(138,134410),(141,134410),(146,134410),(149,132298)]),([6,31,1057,2114,4228,32338],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(57,134410),(81,134410),(82,134410),(105,134410),(106,134410),(113,134410),(114,134410),(138,134410),(146,134410),(149,134410)]),([6,31,1057,2114,5092,8456,16912,31744],[]),([6,31,1057,2114,5092,8456,16912,31777],[]),([6,31,1057,2114,5092,8456,16912,32008],[]),([6,31,1057,2114,5092,8456,17392,31744],[]),([6,31,1057,2114,5092,8456,17969,31744],[]),([6,31,1057,2114,5092,8456,21140,31744],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_58 : K_58.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_59 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,2114,5092,8456,21492,31744],[]),([6,31,1057,2114,5092,8456,31744,32272],[]),([6,31,1057,2114,5092,8479,16912,31744],[(72,0)]),([6,31,1057,2114,5092,9513,16912,31744],[(72,0)]),([6,31,1057,2114,5092,10570,16912,31744],[(72,0)]),([6,31,1057,2114,5092,16912,31744,32008],[(72,0)]),([6,31,1057,2114,5092,16912,32008],[]),([6,31,1057,2114,5092,32008],[(0,269444),(2,269444),(4,269444),(6,269444),(8,269444),(10,269444),(12,269444),(14,269444),(16,269444),(18,203906),(57,269444),(58,269316),(73,269444),(81,269444),(82,269444),(98,269380),(101,269444),(106,269444),(114,269444),(129,361604),(138,269444),(146,269444),(157,203842)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_59 : K_59.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_60 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,2114,5285,8456,17392,31744],[]),([6,31,1057,2114,5285,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(57,134410),(58,134410),(74,132362),(81,134410),(82,134410),(106,134410),(109,134410),(113,134410),(114,134410),(137,68872),(138,134410),(146,134410),(149,132298)]),([6,31,1057,2114,6117,8456,16912,31744],[]),([6,31,1057,2114,6342,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(57,134410),(81,134410),(82,134410),(105,134410),(106,134410),(114,134410),(117,134410),(138,134410),(145,203842),(146,134410)]),([6,31,1057,2114,8456,12288],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,66760),(12,400654),(14,68872),(16,400654),(18,275848),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(137,269380),(138,400654),(145,203842),(146,400654)]),([6,31,1057,2114,8456,15360],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,66760),(12,400654),(14,68872),(16,400654),(18,275848),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(137,269380),(138,400654),(145,203842),(146,400654)]),([6,31,1057,2114,8456,15375],[(0,400654),(2,361608),(4,400654),(6,400654),(8,400654),(10,66760),(12,400654),(14,68872),(16,400654),(18,275848),(57,400654),(58,400654),(81,400654),(82,400654),(97,400644),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,269316),(138,400654),(146,400654)]),([6,31,1057,2114,8456,17376],[(0,275848),(2,275848),(4,275848),(6,275848),(8,275848),(10,66760),(12,275848),(14,68872),(16,275848),(18,400654),(57,275848),(58,275848),(77,265288),(81,275848),(82,275848),(97,265608),(105,275848),(106,275848),(113,275848),(114,275848),(129,197704),(130,275848),(138,275848),(141,275784),(146,275848)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_60 : K_60.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_61 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,2114,8456,17392],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,66760),(12,275848),(14,68872),(16,275848),(18,400654),(57,275848),(58,275848),(81,275848),(82,275848),(97,265608),(105,275848),(106,275848),(113,275848),(114,275848),(130,275848),(138,275848),(141,275784),(146,275848)]),([6,31,1057,2114,8456,17407],[(0,275848),(2,197704),(4,275848),(6,275848),(8,275848),(10,66760),(12,275848),(14,68872),(16,275848),(18,400654),(57,275848),(58,275848),(81,275848),(82,275848),(105,275848),(106,275848),(113,275848),(114,275848),(130,275848),(133,275848),(138,275848),(141,275784),(146,275848),(149,275816)]),([6,31,1057,2114,8456,18417],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,66760),(12,275848),(14,68872),(16,275848),(18,400654),(57,275848),(58,275848),(81,275848),(82,275848),(97,265608),(105,275848),(106,275848),(113,275848),(114,275848),(130,275848),(138,275848),(141,275848),(146,275848)]),([6,31,1057,2114,8456,19442],[(0,275848),(2,197768),(4,275848),(6,275848),(8,275848),(10,132296),(12,275848),(14,68872),(16,275848),(18,400654),(57,275848),(58,275848),(81,275848),(82,275848),(97,265608),(105,275848),(106,275848),(113,275848),(114,275848),(130,275848),(133,265288),(138,275848),(141,275784),(146,275848),(149,275848)]),([6,31,1057,2114,9192,16912,31876],[]),([6,31,1057,2114,9513,17392],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,66760),(12,275848),(14,68872),(16,275848),(18,400654),(57,275848),(81,275848),(82,275848),(97,265608),(106,275848),(109,275848),(113,275848),(114,275848),(130,275848),(137,171076),(138,275848),(146,275848)]),([6,31,1057,2114,10570,17392],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,275848),(12,275848),(14,68872),(16,275848),(18,400654),(57,275848),(58,275848),(74,275848),(81,275848),(82,275848),(105,275848),(106,275848),(114,275848),(117,275848),(130,275848),(138,275848),(141,275784),(145,203844),(146,275848)]),([6,31,1057,2114,17392,21140],[(0,68872),(2,361608),(4,68872),(6,68872),(8,68872),(10,68872),(12,68872),(14,68872),(16,68872),(18,275848),(57,68872),(74,66824),(81,68872),(82,68872),(98,68872),(105,68776),(106,68872),(113,68808),(114,68872),(137,275848),(138,68872),(145,66760),(146,68872)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_61 : K_61.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_62 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,2114,17392,24311],[(0,68872),(2,361608),(4,68872),(6,68872),(8,68872),(10,66760),(12,68872),(14,68872),(16,68872),(18,275848),(57,68872),(58,3336),(81,68872),(82,68872),(98,68872),(106,68872),(109,3336),(114,68872),(133,396552),(138,68872),(141,68872),(146,68872),(149,68872)]),([6,31,1057,2114,24840,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269380),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(137,269380),(138,400654),(145,203842),(146,400654)]),([6,31,1057,2114,25368,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,269380),(57,134410),(58,134410),(81,134410),(82,134410),(105,134410),(106,134410),(113,134410),(114,134410),(137,269380),(138,134410),(145,203842),(146,134410)]),([6,31,1057,2114,28539,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,269380),(57,134410),(74,132362),(81,134410),(82,134410),(106,134410),(109,134410),(114,134410),(117,134410),(138,134410),(146,134410),(149,132298)]),([6,31,1057,2143,4228,8456,17392,31744],[(72,0),(128,0)]),([6,31,1057,2143,4228,32272],[(0,132362),(2,132362),(4,132362),(6,132362),(8,132362),(10,132362),(12,132362),(14,132362),(16,132362),(18,66824),(57,132362),(74,132362),(77,132362),(82,132362),(97,132362),(105,132362),(106,132362),(113,132362),(129,66824),(138,132362),(149,400586)]),([6,31,1057,2143,5092,8456,16912,31744],[(128,0)]),([6,31,1057,3040,4228,16912],[(0,132298),(2,132298),(4,132298),(6,132298),(8,132298),(10,400590),(12,132298),(14,203842),(16,132298),(18,205954),(57,132298),(73,132298),(74,132298),(81,132266),(82,132298),(97,132298),(105,132298),(106,132298),(133,66760),(137,66760),(138,132298),(145,210312),(153,66760),(154,132298)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_62 : K_62.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_63 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,3042,4228,10570],[(0,205956),(2,197775),(4,205956),(6,205956),(8,205956),(10,400590),(12,205956),(14,205956),(16,205956),(18,134346),(57,205956),(58,205828),(74,205954),(82,205956),(97,205956),(98,205892),(105,205956),(106,205956),(114,203908),(137,210312),(138,205956),(153,203844),(154,205956)]),([6,31,1057,3042,4228,15855],[(0,205956),(2,197775),(4,205956),(6,205956),(8,205956),(10,400590),(12,205956),(14,203844),(16,205956),(18,134346),(57,205956),(74,205954),(81,173188),(82,205956),(97,205956),(105,205956),(106,205956),(138,205956),(141,205956),(149,68808),(154,205956),(157,205956)]),([6,31,1057,3042,4228,16912],[(0,134346),(2,197775),(4,134346),(6,134346),(8,134346),(10,400590),(12,134346),(14,203844),(16,134346),(18,205956),(57,134346),(74,132298),(81,134314),(82,134346),(97,134346),(105,134346),(106,134346),(137,68808),(138,134346),(145,210312),(153,68808),(154,134346)]),([6,31,1057,3042,4228,17969],[(0,134346),(2,197775),(4,134346),(6,134346),(8,134346),(10,400590),(12,134346),(14,203844),(16,134346),(18,205956),(57,134346),(58,3274),(74,132298),(82,134346),(97,134346),(105,134346),(106,134346),(138,134346),(141,134346),(145,210312),(153,68808),(154,134346)]),([6,31,1057,3042,4228,21140],[(0,134346),(2,197775),(4,134346),(6,134346),(8,134346),(10,400590),(12,134346),(14,134346),(16,134346),(18,205956),(57,134346),(74,132298),(81,134314),(82,134346),(96,0),(97,134346),(98,68810),(105,134346),(106,134346),(114,134344),(137,210312),(138,134346),(154,134346),(157,134346)]),([6,31,1057,3042,5285,16912],[(0,134346),(2,197775),(4,134346),(6,134346),(8,134346),(10,400590),(12,134346),(14,203844),(16,134346),(18,205956),(57,134346),(58,134346),(74,132298),(82,134346),(85,134346),(97,134346),(106,134346),(109,134346),(137,68808),(138,134346),(145,210312),(153,68808),(154,134346)]),([6,31,1057,3042,10570,16912],[(0,203844),(2,197775),(4,203844),(6,203844),(8,203844),(10,400590),(12,203844),(14,68808),(16,203844),(18,203844),(57,203844),(58,203780),(74,203842),(82,203844),(85,203780),(105,210312),(106,203844),(130,203844),(137,203844),(138,203844),(145,210312),(146,203844),(153,203844),(154,205956)]),([6,31,1057,3042,16912,21140],[(0,68808),(2,197775),(4,68808),(6,68808),(8,68808),(10,400590),(12,68808),(14,68808),(16,68808),(18,203844),(57,68808),(74,66760),(81,68776),(82,68808),(98,68808),(105,68808),(106,68808),(113,68808),(114,68808),(137,210312),(138,68808),(154,68808),(157,68808)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_63 : K_63.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_64 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,3042,16912,28539],[(0,203844),(2,197775),(4,203844),(6,203844),(8,203844),(10,400590),(12,203844),(14,203844),(16,203844),(18,134346),(57,203844),(74,203842),(81,171076),(82,203844),(105,203844),(106,203844),(113,203844),(133,203854),(138,203844),(141,203844),(154,203844),(157,203844)]),([6,31,1057,3071,4228,16912],[(0,132298),(2,197704),(4,132298),(6,132298),(8,132298),(10,400590),(12,132298),(14,203842),(16,132298),(18,205954),(57,132298),(74,132298),(77,132298),(82,132298),(105,132298),(106,132298),(137,66760),(138,132298),(145,210312),(150,66760),(153,66760),(154,132298)]),([6,31,1057,3171,4228,8456,17392,31744],[(72,0),(128,0)]),([6,31,1057,3171,4228,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(57,134410),(62,134410),(74,132362),(82,134410),(85,134410),(105,134410),(106,134410),(113,134410),(114,134410),(137,68872),(138,134410),(146,134410),(149,132298)]),([6,31,1057,3171,5092,8456,16912,31744],[(72,0),(128,0)]),([6,31,1057,3171,8456,17392],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,66760),(12,275848),(14,68872),(16,275848),(18,400654),(57,275848),(62,275848),(82,275848),(85,275848),(97,265608),(105,275848),(106,275848),(113,275848),(114,275848),(130,275848),(137,269380),(138,275848),(146,275848)]),([6,31,1057,4067,4228,16912],[(0,134346),(2,197775),(4,134346),(6,134346),(8,134346),(10,400590),(12,134346),(14,203844),(16,134346),(18,205956),(57,134346),(62,134314),(74,132298),(82,134346),(85,134346),(97,134346),(105,134346),(106,134346),(137,68808),(138,134346),(145,210312),(153,68808),(154,134346)]),([6,31,1057,4228,6342,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,66760),(57,134410),(81,134410),(82,134410),(98,132362),(105,134410),(106,134410),(114,134410),(117,134410),(138,134410),(145,66760),(157,132298)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_64 : K_64.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_65 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,4228,12288,16912],[(0,132298),(2,197704),(4,132298),(6,132298),(8,132298),(10,203842),(12,132298),(14,210312),(16,132298),(18,205954),(57,132298),(62,132266),(81,132298),(82,132298),(96,0),(97,132298),(98,132298),(105,132298),(106,132298),(137,400590),(138,132298),(145,66760),(146,132298),(153,400590),(154,132298)]),([6,31,1057,4228,16912,19442],[(0,210312),(2,197770),(4,210312),(6,210312),(8,210312),(10,203844),(12,210312),(14,210312),(16,210312),(18,132298),(57,210312),(73,209992),(81,210312),(82,210312),(105,210312),(106,210312),(113,68808),(114,132298),(130,210312),(133,199752),(137,132266),(138,210312),(154,210312),(157,210312)]),([6,31,1057,4228,16912,29696],[(0,400590),(2,197704),(4,400590),(6,400590),(8,400590),(10,400590),(12,400590),(14,400590),(16,400590),(18,132298),(57,400590),(81,400590),(82,400590),(105,400590),(106,400590),(113,400590),(114,400590),(129,72898),(130,400590),(138,400590),(153,132298),(154,400590)]),([6,31,1057,4228,16912,29725],[(0,400590),(2,197775),(4,400590),(6,400590),(8,400590),(10,400590),(12,400590),(14,400590),(16,400590),(18,134346),(57,400590),(73,72910),(81,400590),(82,400590),(105,400590),(106,400590),(113,400590),(114,400590),(130,400590),(138,400590),(141,400558),(154,400590)]),([6,31,1057,4228,25104,31744],[(0,132298),(2,197704),(4,132298),(6,132298),(8,132298),(10,203842),(12,132298),(14,205954),(16,132298),(18,132298),(57,132298),(62,132266),(81,132298),(82,132298),(105,66760),(106,132298),(113,66760),(114,132298),(129,72898),(130,132298),(137,132298),(138,132298),(145,66760),(150,132298),(154,66760)]),([6,31,1057,4228,25368,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,66760),(57,134410),(62,134410),(81,134410),(82,134410),(98,132362),(105,134410),(106,134410),(113,134410),(114,134410),(137,66760),(138,134410),(145,66760),(157,66760)]),([6,31,1057,4228,30653,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(57,134410),(81,134410),(82,134410),(98,132362),(106,134410),(109,134410),(114,134410),(117,134410),(138,134410),(157,66760),(158,134410)]),([6,31,1057,6210,8456,31744],[(0,269380),(2,197704),(4,269380),(6,269380),(8,269380),(10,66760),(12,269380),(14,68872),(16,269380),(18,269380),(57,269380),(58,269316),(81,269380),(82,269380),(105,203842),(106,269380),(113,203842),(114,269380),(129,72898),(130,269380),(138,269380),(146,269380),(153,269380),(158,269380)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_65 : K_65.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_66 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,6276,16912,31744],[(0,367822),(2,197704),(4,367822),(6,367822),(8,367822),(10,367822),(12,367822),(14,367822),(16,367822),(18,132298),(57,367822),(81,367822),(82,367822),(105,367822),(106,367822),(113,367822),(114,367822),(129,72898),(130,367822),(138,367822),(153,132298),(154,367822)]),([6,31,1057,6342,8456,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,271492),(57,203842),(58,203842),(74,203842),(81,203842),(82,203842),(105,203842),(106,203842),(113,203842),(114,203842),(138,203842),(149,269380),(153,271492)]),([6,31,1057,6342,10570,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,203842),(57,400654),(58,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(149,203842),(153,203842)]),([6,31,1057,6342,12684,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,66692),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(153,66692),(158,66692)]),([6,31,1057,6342,16912,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,134410),(57,203842),(81,203842),(82,203842),(105,203842),(106,203842),(113,203842),(114,203842),(138,203842),(153,134410),(154,203842)]),([6,31,1057,6342,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,134210),(57,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(153,134210),(154,400654)]),([6,31,1057,6342,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,66760),(57,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(149,66760),(153,66760)]),([6,31,1057,8456,10570,17392],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,275848),(12,275848),(14,66760),(16,275848),(18,400654),(57,275848),(58,275848),(73,265608),(74,275848),(81,275848),(82,275848),(105,275848),(106,275848),(114,275848),(117,275848),(130,275848),(138,275848),(141,275784),(145,203842)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_66 : K_66.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_67 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,8456,15855,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(57,203842),(58,203778),(81,203842),(82,203842),(98,203842),(106,203842),(109,203842),(114,203842),(117,203842),(137,269380),(138,203842),(157,269380),(158,203842)]),([6,31,1057,8456,16384,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(57,203842),(58,203778),(81,203842),(82,203842),(97,203842),(98,203842),(105,203842),(106,203842),(113,203842),(114,203842),(137,269380),(138,203842),(154,203842),(157,203842)]),([6,31,1057,8456,16912,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(57,203842),(58,203778),(81,203842),(82,203842),(98,203842),(105,203842),(106,203842),(113,203842),(114,203842),(137,269380),(138,203842),(154,203842),(157,203842)]),([6,31,1057,8456,16912,31843],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(57,203842),(62,171074),(81,203842),(82,203842),(98,203842),(105,203842),(106,203842),(113,203842),(114,203842),(138,203842),(141,203842),(154,203842),(157,203842)]),([6,31,1057,8456,16912,32338],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,132298),(57,203842),(58,203778),(81,203842),(82,203842),(105,203842),(106,203842),(113,203842),(114,203842),(137,132298),(138,203842),(154,203842),(157,203842)]),([6,31,1057,8456,16927,31810],[(0,203842),(2,203842),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(57,203842),(58,203778),(73,203842),(81,203842),(82,203842),(98,203842),(101,203842),(105,203778),(106,203842),(114,203842),(129,269380),(137,269380),(138,203842),(157,204046)]),([6,31,1057,8456,17392,21140],[(0,66760),(2,361608),(4,66760),(6,66760),(8,66760),(10,66760),(12,66760),(14,66760),(16,66760),(18,275848),(57,66760),(62,66728),(72,0),(73,66760),(74,66760),(81,66760),(82,66760),(98,66760),(105,66728),(106,66760),(113,66760),(137,275848),(138,66760),(145,68872),(146,66760)]),([6,31,1057,8456,17392,30653],[(0,66760),(2,361608),(4,66760),(6,66760),(8,66760),(10,66760),(12,66760),(14,66760),(16,66760),(18,275848),(57,66760),(58,1224),(73,66760),(81,66760),(82,66760),(98,66760),(106,66760),(109,1224),(138,66760),(141,66760),(146,66760),(149,66760),(157,275848)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_67 : K_67.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_68 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,8456,17969,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(57,203842),(58,203842),(81,203842),(82,203842),(98,203842),(106,203842),(109,203842),(113,203842),(114,203842),(138,203842),(154,203842),(157,203842)]),([6,31,1057,8456,25368,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,271492),(57,203842),(58,203778),(81,203842),(82,203842),(98,203842),(105,203842),(106,203842),(114,203842),(117,203842),(137,271492),(138,203842),(145,271492),(157,203842)]),([6,31,1057,9192,16912,31876],[(0,66760),(2,66760),(4,66760),(6,66760),(8,66760),(10,66760),(12,66760),(14,66760),(16,66760),(18,132298),(57,66760),(62,66728),(74,66760),(77,66703),(81,66728),(82,66760),(97,66703),(105,66760),(106,66760),(113,66760),(129,66703),(137,132298),(138,66760),(149,132298),(154,66760)]),([6,31,1057,9513,16912,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(57,203842),(82,203842),(85,203842),(98,203842),(105,203842),(106,203842),(113,203842),(114,203842),(138,203842),(154,203842),(157,203842)]),([6,31,1057,10570,12684,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,407918),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(157,407918),(158,400654)]),([6,31,1057,10570,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,374159),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,374095),(138,400654),(154,400654),(157,400590)]),([6,31,1057,10570,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,203842),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,203842),(138,400654),(145,203842),(157,203842)]),([6,31,1057,12684,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,68810),(57,400654),(62,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,68810),(138,400654),(149,66760),(150,68810)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_68 : K_68.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_69 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,1057,12684,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132164),(57,400654),(62,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,132164),(138,400654),(145,66692),(150,132164)]),([6,31,1057,16912,24311,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,68872),(57,203842),(58,203778),(74,203842),(81,203842),(82,203842),(106,203842),(109,203842),(114,203842),(117,203842),(137,68872),(138,203842),(146,203842),(149,203842)]),([6,31,1057,16912,25368,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(57,203842),(58,203778),(81,203842),(82,203842),(105,203842),(106,203842),(114,203842),(117,203842),(137,269380),(138,203842),(145,134410),(146,203842)]),([6,31,1057,19026,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,68810),(57,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(146,400654),(149,400590)]),([6,31,1057,19026,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132164),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,132164),(138,400654),(145,134210),(146,400654)]),([6,31,1057,21140,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,66760),(57,400654),(62,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,66760),(138,400654),(145,66760),(157,66760)]),([6,31,1087,2114,8456,17392],[(0,275848),(2,275848),(4,275848),(6,275848),(8,275848),(10,1224),(12,275848),(14,3336),(16,275848),(18,400654),(57,275848),(58,275848),(61,275848),(73,275848),(77,275848),(81,275848),(97,275848),(101,275848),(105,275848),(113,275848),(114,275848),(129,269316),(130,275848),(133,275848),(138,275848),(141,275784),(146,275848)]),([6,31,1087,8456,16912,31810],[(0,203778),(2,203778),(4,203778),(6,203778),(8,203778),(10,203778),(12,203778),(14,203778),(16,203778),(18,269316),(58,203778),(61,203778),(73,203778),(81,203778),(97,203778),(98,203778),(105,203778),(106,203778),(113,203778),(114,203778),(133,204046),(137,269316),(154,203778),(157,203778)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_69 : K_69.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_70 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2017,2048,4228,16912],[(0,132266),(2,132266),(4,132266),(6,400386),(8,132266),(10,132266),(12,132266),(14,171074),(16,132266),(18,173186),(57,132106),(73,132266),(74,132266),(81,132266),(82,132266),(97,132266),(113,132266),(114,132266),(133,66568),(137,1416),(145,66728),(146,132266),(153,66728),(154,132266)]),([6,31,2017,2114,4228,8456,16912,31777],[(72,0),(128,0)]),([6,31,2017,2114,4228,9513],[(0,173188),(2,361615),(4,173188),(6,400388),(8,173188),(10,132298),(12,173188),(14,173188),(16,173188),(18,134314),(57,9348),(81,173188),(96,0),(97,173188),(98,173124),(106,171140),(113,173188),(114,173188),(129,145762),(145,205954),(146,173188),(153,171076),(154,173188)]),([6,31,2017,2114,4228,9513,16912,31744],[(72,0),(128,0)]),([6,31,2017,2114,4228,15855],[(0,173188),(2,361615),(4,173188),(6,400388),(8,173188),(10,173188),(12,173188),(14,171076),(16,173188),(18,134314),(57,9348),(74,173186),(81,173188),(82,173188),(97,173188),(113,173188),(114,173188),(141,68776),(146,173188),(149,173188),(154,173188),(157,173188)]),([6,31,2017,2114,4228,16912],[(0,134314),(2,361615),(4,134314),(6,400388),(8,134314),(10,134314),(12,134314),(14,171076),(16,134314),(18,173188),(57,134154),(74,132266),(81,134314),(82,134314),(97,134314),(113,134314),(114,134314),(137,3464),(145,132298),(146,134314),(153,68776),(154,134314)]),([6,31,2017,2114,4228,19026],[(0,134314),(2,361615),(4,134314),(6,400388),(8,134314),(10,132298),(12,134314),(14,171076),(16,134314),(18,173188),(57,134154),(81,134314),(97,134314),(113,134314),(114,134314),(133,68616),(137,3464),(146,134314),(149,134314),(153,68776),(154,134314)]),([6,31,2017,2114,4228,21140],[(0,134314),(2,361615),(4,134314),(6,400388),(8,134314),(10,134314),(12,134314),(14,134314),(16,134314),(18,173188),(57,134154),(74,132266),(81,134314),(82,134314),(96,0),(97,134314),(98,68778),(106,134312),(113,134314),(114,134314),(145,132298),(146,134314),(154,134314),(157,134314)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_70 : K_70.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_71 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2017,2114,6342,16912],[(0,134314),(2,361615),(4,134314),(6,400388),(8,134314),(10,66760),(12,134314),(14,171076),(16,134314),(18,173188),(57,134154),(81,134314),(114,134314),(117,134314),(137,3464),(145,203842),(146,134314),(153,68776),(154,134314)]),([6,31,2017,2114,9513,16912],[(0,171076),(2,361615),(4,171076),(6,400388),(8,171076),(10,66760),(12,171076),(14,68776),(16,171076),(18,171076),(57,7236),(81,171076),(97,145762),(113,203842),(114,171076),(130,171076),(137,3464),(138,171076),(145,203842),(146,171076),(153,171076),(154,173188)]),([6,31,2017,2114,16912,21140],[(0,68776),(2,361615),(4,68776),(6,400388),(8,68776),(10,68776),(12,68776),(14,68776),(16,68776),(18,171076),(57,68616),(74,66728),(81,68776),(82,68776),(98,68776),(105,68776),(106,68776),(113,68776),(114,68776),(145,66760),(146,68776),(154,68776),(157,68776)]),([6,31,2017,2114,16912,28539],[(0,171076),(2,361615),(4,171076),(6,400388),(8,171076),(10,171076),(12,171076),(14,171076),(16,171076),(18,134314),(57,7236),(74,171074),(81,171076),(82,171076),(105,171076),(113,171076),(114,171076),(133,171086),(146,171076),(149,171076),(154,171076),(157,171076)]),([6,31,2017,2143,4228,16912],[(0,132266),(2,132266),(4,132266),(6,400386),(8,132266),(10,132266),(12,132266),(14,171074),(16,132266),(18,173186),(57,132266),(74,132266),(77,132266),(82,132266),(97,132266),(113,132266),(129,66728),(137,1416),(145,132298),(153,66728),(154,132266)]),([6,31,2017,3042,4228,16912],[(0,134314),(2,361615),(4,134314),(6,134314),(8,134314),(10,134314),(12,134314),(14,171076),(16,134314),(18,173188),(57,134314),(74,132266),(81,134314),(82,134314),(97,134314),(105,134314),(113,134314),(137,68776),(145,132266),(153,68776),(154,134314)]),([6,31,2017,3171,4228,8456],[(0,271492),(2,361615),(4,271492),(6,400386),(8,271492),(10,132266),(12,271492),(14,271492),(16,271492),(18,134410),(57,271492),(96,0),(97,271492),(98,271428),(106,269444),(113,271492),(114,271492),(129,145762),(145,173186),(146,271492),(153,269380),(154,271492)]),([6,31,2017,3171,4228,8456,16912,31744],[(72,0),(128,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_71 : K_71.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_72 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2017,3171,4228,16912],[(0,134410),(2,361615),(4,134410),(6,400386),(8,134410),(10,134410),(12,134410),(14,269380),(16,134410),(18,271492),(57,134410),(74,132362),(82,134314),(97,134410),(113,134410),(114,134410),(137,1416),(145,132266),(146,134410),(153,68872),(154,134410)]),([6,31,2017,3171,8456,16912],[(0,269380),(2,361615),(4,269380),(6,400386),(8,269380),(10,66728),(12,269380),(14,68872),(16,269380),(18,269380),(57,269380),(97,145762),(113,171074),(114,269380),(130,269380),(137,1416),(138,269380),(145,171074),(146,269380),(153,269380),(154,271492)]),([6,31,2017,4067,4228,16912],[(0,134314),(2,361615),(4,134314),(6,134314),(8,134314),(10,134314),(12,134314),(14,171076),(16,134314),(18,173188),(57,134154),(62,134314),(74,132266),(82,134314),(85,134314),(97,134314),(105,134314),(113,134314),(137,68776),(145,132266),(153,68776),(154,134314)]),([6,31,2017,4228,6342,16912],[(0,134314),(2,361615),(4,134314),(6,400388),(8,134314),(10,203842),(12,134314),(14,134314),(16,134314),(18,173188),(57,134154),(73,134314),(98,132266),(106,134314),(114,134314),(117,134314),(137,3464),(145,66760),(146,134314),(153,132298),(154,134314)]),([6,31,2017,4228,8192,16912],[(0,132266),(2,361615),(4,132266),(6,400386),(8,132266),(10,171074),(12,132266),(14,132266),(16,132266),(18,173186),(57,132106),(73,132266),(96,0),(97,132266),(98,132266),(105,132266),(106,132266),(113,132266),(114,132266),(137,1416),(145,66728),(146,132266),(153,66728),(154,132266)]),([6,31,2017,4228,8456,15855],[(0,173186),(2,361615),(4,173186),(6,400386),(8,173186),(10,171074),(12,173186),(14,173186),(16,173186),(18,132266),(57,9346),(73,173186),(96,0),(97,173186),(98,173186),(106,173186),(113,173186),(114,173186),(141,369794),(146,173186),(149,173186),(154,173186),(157,173186)]),([6,31,2017,4228,8456,16912],[(0,132266),(2,361615),(4,132266),(6,400386),(8,132266),(10,171074),(12,132266),(14,132266),(16,132266),(18,173186),(57,132106),(73,132266),(96,0),(97,132266),(98,132266),(106,132266),(113,132266),(114,132266),(137,1416),(145,66728),(146,132266),(153,134410),(154,132266)]),([6,31,2017,4228,8456,16912,31810],[(84,140482),(96,134314),(196,132266)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_72 : K_72.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_73 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2017,4228,8456,21140],[(0,132266),(2,361615),(4,132266),(6,400386),(8,132266),(10,132266),(12,132266),(14,132266),(16,132266),(18,173186),(57,132106),(72,0),(73,132266),(74,66730),(82,132264),(96,0),(97,132266),(98,132266),(106,132266),(113,132266),(114,132266),(146,132266),(149,132266),(153,134410),(154,132266)]),([6,31,2017,4228,8456,25368],[(0,132266),(2,361615),(4,132266),(6,400386),(8,132266),(10,171074),(12,132266),(14,132266),(16,132266),(18,271492),(57,132106),(73,132266),(97,132266),(113,132266),(114,132266),(145,66728),(146,132266),(154,132266),(157,132266)]),([6,31,2017,4228,8479,16912],[(0,132266),(2,132266),(4,132266),(6,400386),(8,132266),(10,171074),(12,132266),(14,132266),(16,132266),(18,173186),(57,132266),(61,132266),(73,132266),(77,132266),(96,0),(97,132266),(98,132266),(101,132266),(106,132266),(114,132266),(129,145774),(133,66728),(137,1416),(145,66728),(146,132266),(153,132362)]),([6,31,2017,4228,9192,16912],[(0,132266),(2,361615),(4,132266),(6,132266),(8,132266),(10,171074),(12,132266),(14,132266),(16,132266),(18,173186),(57,132266),(73,132266),(81,132266),(96,0),(97,132266),(98,132266),(106,132266),(114,132266),(137,66728),(145,66728),(146,132266),(153,134314)]),([6,31,2017,4228,9513,16912],[(0,132298),(2,361615),(4,132298),(6,400388),(8,132298),(10,203842),(12,132298),(14,132298),(16,132298),(18,205954),(57,132298),(73,132298),(96,0),(97,132298),(98,132298),(106,132266),(113,132298),(114,132298),(137,3464),(145,66760),(146,132298),(153,134314),(154,132298)]),([6,31,2017,4228,10217,16912],[(0,132266),(2,361615),(4,132266),(6,132266),(8,132266),(10,171074),(12,132266),(14,132266),(16,132266),(18,173186),(57,132106),(73,132266),(81,132266),(96,0),(97,132106),(98,132266),(106,132266),(109,132266),(114,132266),(137,66728),(145,66728),(146,132266),(153,134314)]),([6,31,2017,4228,12684,16912],[(0,132266),(2,361615),(4,132266),(6,400386),(8,132266),(10,269380),(12,132266),(14,132266),(16,132266),(18,173186),(57,132106),(73,132266),(96,0),(97,132266),(98,132266),(106,132266),(114,132266),(117,132266),(137,1416),(145,68872),(146,132266),(153,134410),(154,132266)]),([6,31,2017,4228,16912,19026],[(0,132298),(2,361615),(4,132298),(6,400388),(8,132298),(10,171076),(12,132298),(14,205954),(16,132298),(18,132298),(57,132298),(73,132298),(105,3464),(113,68776),(114,132298),(130,132298),(133,132298),(137,3464),(138,132266),(145,68776),(146,132298),(154,132298),(157,132298)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_73 : K_73.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_74 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2017,4228,16912,24311],[(0,132266),(2,361615),(4,132266),(6,400386),(8,132266),(10,171074),(12,132266),(14,173186),(16,132266),(18,132266),(57,132106),(73,132266),(105,1416),(113,66728),(114,132266),(130,132266),(133,132266),(138,132266),(146,132266),(149,132266),(154,132266),(157,132266)]),([6,31,2017,4228,16912,25368],[(0,134410),(2,361615),(4,134410),(6,400386),(8,134410),(10,171074),(12,134410),(14,271492),(16,134410),(18,134410),(57,134410),(73,134410),(105,1416),(113,66728),(114,134410),(130,132362),(138,134314),(145,66728),(146,134410),(154,134410),(157,134410)]),([6,31,2017,4228,16912,30653],[(0,134314),(2,361615),(4,134314),(6,400388),(8,134314),(10,171076),(12,134314),(14,173188),(16,134314),(18,134314),(57,134154),(73,134314),(105,3464),(113,68776),(114,134314),(130,132266),(138,134314),(141,134314),(146,134314),(149,134314),(154,134314),(157,134314)]),([6,31,2017,8456,12684,16912],[(0,132266),(2,361615),(4,132266),(6,400386),(8,132266),(10,68872),(12,132266),(14,171074),(16,132266),(18,173186),(57,132106),(73,132266),(97,132266),(114,132266),(117,132266),(137,1416),(145,269380),(146,132266),(153,66728),(154,132266)]),([6,31,2017,8456,16912,21140],[(0,66728),(2,361615),(4,66728),(6,400386),(8,66728),(10,66728),(12,66728),(14,66728),(16,66728),(18,171074),(57,66568),(72,0),(73,66728),(74,66728),(82,66728),(98,66728),(105,66728),(106,66728),(113,66728),(114,66728),(145,68872),(146,66728),(154,66728),(157,66728)]),([6,31,2017,8456,16912,28539],[(0,171074),(2,361615),(4,171074),(6,400386),(8,171074),(10,171074),(12,171074),(14,171074),(16,171074),(18,132266),(57,7234),(72,0),(73,171074),(74,171074),(82,171074),(105,171074),(113,171074),(114,171074),(133,132266),(146,171074),(149,171074),(154,171074),(157,171074)]),([6,31,2114,3042,8456,16912,31876],[(104,367620)]),([6,31,2114,3171,4228,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(62,134410),(82,134410),(85,134410),(105,134410),(106,134410),(113,134410),(114,134410),(137,68872),(138,134410),(146,134410)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_74 : K_74.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_75 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2114,3171,8456,17392],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,275848),(12,275848),(14,68872),(16,275848),(18,400654),(62,275848),(74,275848),(82,275848),(85,275848),(97,265608),(105,275848),(106,275848),(113,275848),(114,275848),(130,275848),(137,269380),(138,275848),(146,275848),(149,275784)]),([6,31,2114,4067,4228,16912],[(0,134314),(2,197775),(4,134314),(6,134314),(8,134314),(10,400388),(12,134314),(14,171076),(16,134314),(18,173188),(62,134314),(82,134314),(85,134314),(97,134314),(105,134314),(106,134314),(137,68776),(138,134314),(145,3464),(153,68776),(154,134314)]),([6,31,2114,4228,5285,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,271492),(58,132362),(74,134410),(81,134410),(82,134410),(105,134410),(106,134410),(114,134410),(117,134410),(138,134410),(141,132298),(145,72898)]),([6,31,2114,4228,8456,17392,32272],[(72,138410),(152,134314)]),([6,31,2114,4228,9192,15855,31744],[]),([6,31,2114,4228,9192,16912,31744],[]),([6,31,2114,4228,9192,16912,31810],[(72,210306),(80,203842),(184,203842)]),([6,31,2114,4228,9192,16912,31876],[(80,66734),(128,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_75 : K_75.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_76 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2114,4228,9192,16927,31744],[]),([6,31,2114,4228,9192,21140,31744],[(72,407716),(80,66730),(112,400558)]),([6,31,2114,4228,11242,16912,31744],[(128,0)]),([6,31,2114,4228,16912,18417],[(0,3464),(2,361610),(4,3464),(6,3464),(8,3464),(10,171076),(12,3464),(14,3464),(16,3464),(18,400388),(58,1416),(73,3144),(81,3464),(82,3464),(98,3464),(105,3464),(106,3464),(113,68776),(114,3464),(137,68776),(138,3464),(154,3464),(157,3464)]),([6,31,2114,4228,16912,23575,31744],[(96,0),(144,335022)]),([6,31,2114,4228,16912,30750],[(0,400388),(2,361615),(4,400388),(6,400388),(8,400388),(10,400388),(12,400388),(14,400388),(16,400388),(18,134314),(58,400386),(73,72708),(81,400388),(82,400388),(105,400388),(106,400388),(113,400388),(114,400388),(133,400398),(138,400388),(141,400388),(154,400388)]),([6,31,2114,4228,25368,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,271492),(62,134410),(74,134410),(81,134410),(82,134410),(105,134410),(106,134410),(113,134410),(114,134410),(137,72898),(138,134410),(145,72898)]),([6,31,2114,4228,31710,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(58,132362),(81,134410),(82,134410),(101,134410),(106,134410),(109,134410),(114,134410),(117,134410),(138,134410),(141,132298),(158,134410)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_76 : K_76.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_77 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2114,4255,9192,16912,31744],[(168,145576),(184,145762)]),([6,31,2114,5092,8456,21140,31744],[(80,66728),(112,400558),(176,400386)]),([6,31,2114,5153,8456,31744],[(0,269380),(2,197704),(4,269380),(6,66760),(8,269380),(10,269380),(12,269380),(14,68872),(16,269380),(18,269380),(73,269380),(74,269316),(81,269380),(82,269380),(105,203842),(106,269380),(113,203842),(114,269380),(129,72898),(130,269380),(138,269380),(146,269380),(153,269380),(158,269380)]),([6,31,2114,5285,8456,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,271492),(74,171278),(81,171278),(82,171278),(105,171278),(106,171278),(113,171278),(114,171278),(129,72898),(130,171278),(138,171278),(149,269380),(153,271492)]),([6,31,2114,5285,9513,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,171140),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(153,171140)]),([6,31,2114,5285,12684,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271492),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(153,271492),(158,271492)]),([6,31,2114,5285,16912,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,134410),(58,171278),(81,171278),(82,171278),(105,171278),(106,171278),(113,171278),(114,171278),(129,72898),(130,171278),(138,171278),(141,171214),(153,134410),(154,171278)]),([6,31,2114,5285,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,134410),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(141,400590),(153,134410),(154,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_77 : K_77.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_78 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2114,5285,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,134312),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(141,400590),(153,134312)]),([6,31,2114,8456,9192,16912,31876],[(76,361615),(196,140482)]),([6,31,2114,8456,9513,17392],[(0,275848),(2,361608),(4,275848),(6,66760),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,400654),(73,265608),(81,275848),(82,275848),(97,265608),(98,275848),(105,275848),(106,275848),(114,275848),(117,275848),(130,275848),(138,275848),(145,203842),(157,203778)]),([6,31,2114,8456,15855,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269380),(81,171278),(82,171278),(98,171278),(106,171278),(109,171278),(114,171278),(117,171278),(129,72898),(130,171278),(137,203842),(138,171278),(157,269380),(158,171278)]),([6,31,2114,8456,16384,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269380),(81,171278),(82,171278),(97,171278),(98,171278),(105,171278),(106,171278),(113,171278),(114,171278),(129,72898),(130,171278),(137,203842),(138,171278),(154,171278),(157,171278)]),([6,31,2114,8456,16912,17392,31876],[(144,134314)]),([6,31,2114,8456,16912,31744,31903],[(96,9384),(136,334850)]),([6,31,2114,8456,16912,31775,31876],[(60,72964),(128,361615)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_78 : K_78.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_79 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2114,8456,16912,31776],[(0,171278),(2,197640),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269316),(81,171278),(82,171278),(98,171278),(105,171278),(106,171278),(113,171278),(114,171278),(129,7362),(130,171278),(137,203778),(138,171278),(154,171278),(157,171278)]),([6,31,2114,8456,16912,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269380),(81,171278),(82,171278),(98,171278),(105,171278),(106,171278),(113,171278),(114,171278),(129,72898),(130,171278),(137,203842),(138,171278),(154,171278),(157,171278)]),([6,31,2114,8456,16912,31807],[(0,171278),(2,361615),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269316),(73,171268),(81,171278),(82,171278),(98,171278),(105,171278),(106,171278),(113,171278),(114,171278),(130,171278),(133,171278),(138,171278),(154,171278),(157,171278)]),([6,31,2114,8456,16912,31843],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269380),(62,171278),(81,171278),(82,171278),(98,171278),(105,171278),(106,171278),(113,171278),(114,171278),(130,171278),(138,171278),(141,171278),(154,171278),(157,171278)]),([6,31,2114,8456,16912,32305],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269380),(81,171278),(82,171278),(98,171278),(105,171278),(106,171278),(113,171278),(114,171278),(130,171278),(137,203842),(138,171278),(154,171278),(157,171278)]),([6,31,2114,8456,16927,31744,31876],[(136,334850),(168,9384)]),([6,31,2114,8456,16927,31777],[(0,171278),(2,171278),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269380),(57,171278),(73,171278),(81,171278),(82,171278),(98,171278),(101,171278),(106,171278),(114,171278),(130,171278),(137,203842),(138,171278),(154,171278),(157,171278)]),([6,31,2114,8456,17040,31744],[(0,138434),(2,197768),(4,138434),(6,138434),(8,138434),(10,138434),(12,138434),(14,138434),(16,138434),(18,138434),(62,138500),(81,138434),(82,138434),(105,132296),(106,203906),(113,134408),(114,269444),(129,138434),(130,145762),(137,138434),(138,138434),(150,138434),(154,138434)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_79 : K_79.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_80 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2114,8456,17392,21140],[(0,275848),(2,361608),(4,275848),(6,275848),(8,275848),(10,275848),(12,275848),(14,400654),(16,275848),(18,275848),(62,275848),(73,265608),(81,275848),(82,275848),(98,275848),(105,138594),(106,275848),(113,138594),(130,275848),(137,66760),(138,275848),(145,68872),(146,275848),(158,138594)]),([6,31,2114,8456,17392,21140,31744],[(104,132264),(112,134312),(156,138434),(176,138562)]),([6,31,2114,8456,17392,31710],[(0,275848),(2,361608),(4,275848),(6,66760),(8,275848),(10,68872),(12,275848),(14,400654),(16,275848),(18,275848),(73,265608),(81,275848),(82,275848),(98,275848),(106,275848),(130,275848),(133,275848),(138,275848),(141,275848),(146,275848),(149,275848),(157,275848),(158,269316)]),([6,31,2114,8456,19026,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269380),(81,171278),(82,171278),(98,171278),(106,171278),(109,171278),(113,171278),(114,171278),(129,72898),(130,171278),(138,171278),(154,171278),(157,171278)]),([6,31,2114,8456,25368,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,271492),(81,171278),(82,171278),(98,171278),(105,171278),(106,171278),(114,171278),(117,171278),(129,72898),(130,171278),(137,203842),(138,171278),(145,271492),(157,269380)]),([6,31,2114,8488,16912,31744],[(0,335022),(2,166920),(4,335022),(6,335022),(8,335022),(10,335022),(12,335022),(14,335022),(16,335022),(18,171012),(81,335022),(82,335022),(98,335022),(105,335022),(106,335022),(113,335022),(114,335022),(129,7332),(130,335022),(137,203778),(138,335022),(154,335022),(157,335022)]),([6,31,2114,9192,16912,21140,31744],[(104,132264),(112,134312),(200,145572)]),([6,31,2114,9192,16912,28539,31744],[(148,335022)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_80 : K_80.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_81 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2114,9192,16912,31744,31876],[(128,361615),(168,361615)]),([6,31,2114,9192,16912,31876],[(57,361640),(77,361615),(105,132298),(106,205954),(113,134314),(129,361615),(130,145762),(137,66760),(138,203842),(150,145572),(154,145572)]),([6,31,2114,9513,12684,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,407556),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(158,400654)]),([6,31,2114,9513,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,3471),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,203842),(138,400654),(154,400654)]),([6,31,2114,9513,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,171140),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,203842),(138,400654),(145,171140)]),([6,31,2114,10570,16912,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269380),(58,171278),(82,171278),(85,171278),(98,171278),(105,171278),(106,171278),(113,171278),(114,171278),(129,72898),(130,171278),(138,171278),(141,171214),(154,171278),(157,171278)]),([6,31,2114,12684,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,68778),(62,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,68778),(138,400654),(150,68778)]),([6,31,2114,12684,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269380),(62,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,269380),(138,400654),(145,271492),(150,269380)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_81 : K_81.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_82 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,2114,16912,24311,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,68872),(74,171278),(81,171278),(82,171278),(106,171278),(109,171278),(114,171278),(117,171278),(129,72898),(130,171278),(137,203842),(138,171278),(146,171278),(149,171278)]),([6,31,2114,16912,25368,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,269380),(81,171278),(82,171278),(105,171278),(106,171278),(114,171278),(117,171278),(129,72898),(130,171278),(137,203842),(138,171278),(145,134410),(146,171278)]),([6,31,2114,17969,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,68778),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(138,400654),(141,400590),(146,400654)]),([6,31,2114,17969,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269380),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,203842),(138,400654),(145,134410),(146,400654)]),([6,31,2114,21140,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,134312),(62,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,134312),(138,400654),(145,134312)]),([6,31,2146,8456,16912,31744],[(0,335118),(2,164872),(4,335118),(6,335118),(8,335118),(10,335118),(12,335118),(14,335118),(16,335118),(18,269316),(81,335118),(82,335118),(98,335118),(105,335118),(106,335118),(113,335118),(114,335118),(129,7330),(130,335118),(137,171010),(138,335118),(154,335118),(157,335118)]),([6,31,3042,3071,4228,8456,16912],[(76,275458),(84,275458),(116,275458),(168,0)]),([6,31,3042,3171,4228,8456],[(0,271492),(2,165007),(4,271492),(6,1294),(8,271492),(10,271492),(12,271492),(14,271492),(16,271492),(18,134410),(74,271364),(97,271492),(98,271428),(106,269444),(113,271492),(114,271492),(129,145570),(145,275458),(146,271492),(153,269380),(154,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_82 : K_82.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_83 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,3042,3171,4228,16912],[(0,134410),(2,165007),(4,134410),(6,1294),(8,134410),(10,134410),(12,134410),(14,269380),(16,134410),(18,271492),(82,134314),(97,134410),(113,134410),(114,134410),(137,275458),(145,68872),(146,134410),(153,68872),(154,134410)]),([6,31,3042,3171,8456,16912],[(0,269380),(2,165007),(4,269380),(6,1294),(8,269380),(10,269380),(12,269380),(14,68872),(16,269380),(18,269380),(74,269316),(86,269316),(97,145570),(113,275458),(114,269380),(130,269380),(137,275458),(138,269380),(145,269380),(146,269380),(153,269380),(154,271492)]),([6,31,3042,4067,4228,16912],[(0,134314),(2,165007),(4,134314),(6,134314),(8,134314),(10,134314),(12,134314),(14,171076),(16,134314),(18,173188),(62,134314),(82,134314),(85,134314),(97,134314),(105,134314),(113,134314),(137,68776),(145,68776),(153,68776),(154,134314)]),([6,31,3042,4228,5285,16912],[(0,134346),(2,197775),(4,134346),(6,400590),(8,134346),(10,134346),(12,134346),(14,134346),(16,134346),(18,205956),(58,132298),(72,0),(73,134346),(74,134346),(86,134346),(97,134346),(106,134314),(114,134346),(117,134346),(137,210312),(145,210312),(146,134346),(153,210312),(154,134346)]),([6,31,3042,4228,8456,15855],[(0,275458),(2,165007),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,275458),(73,145570),(74,275458),(86,275458),(97,145570),(106,145570),(113,269380),(114,68872),(130,275458),(141,275458),(146,275458),(149,275458),(154,275458),(157,275458)]),([6,31,3042,4228,8456,15855,31744],[]),([6,31,3042,4228,8456,16912],[(0,275458),(2,165007),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,275458),(73,145570),(74,275458),(86,275458),(97,145570),(106,145570),(113,269380),(114,68872),(130,275458),(137,275458),(145,275458),(146,275458),(153,134410),(154,271492)]),([6,31,3042,4228,8456,16912,31744],[(128,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_83 : K_83.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_84 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,3042,4228,8456,16912,31777],[]),([6,31,3042,4228,8456,16912,31810],[(84,140482),(128,0)]),([6,31,3042,4228,8456,16912,31876],[(72,0),(128,80232),(188,275458)]),([6,31,3042,4228,8456,16927],[(0,275458),(2,275458),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,275458),(57,0),(73,275458),(74,275458),(86,275458),(97,275458),(113,269380),(114,68872),(130,275458),(133,275458),(145,275458),(146,275458),(154,271364)]),([6,31,3042,4228,8456,16927,31744],[(128,0)]),([6,31,3042,4228,8456,21140],[(0,275458),(2,165007),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,275458),(73,145570),(74,275458),(82,145570),(97,145570),(106,145570),(113,275458),(114,275458),(130,275458),(146,275458),(149,275458),(153,134410),(154,271492)]),([6,31,3042,4228,8456,21140,31744],[(72,407714),(80,66728),(112,68778),(128,0),(188,275458)]),([6,31,3042,4228,8456,25368],[(0,271492),(2,165007),(4,271492),(6,1294),(8,271492),(10,271492),(12,271492),(14,134410),(16,271492),(18,271492),(73,271492),(74,271492),(86,271492),(97,145570),(113,275458),(114,271492),(130,271364),(145,271492),(146,271492),(154,271492),(157,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_84 : K_84.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_85 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,3042,4228,9192,16912],[(0,177154),(2,361615),(4,177154),(6,1198),(8,177154),(10,177154),(12,177154),(14,177154),(16,177154),(18,177154),(72,0),(73,145762),(74,177154),(81,177154),(86,177154),(97,145762),(106,145570),(114,68776),(117,177154),(130,177154),(137,177154),(145,177154),(146,177154),(153,134314)]),([6,31,3042,4228,9192,16912,31744],[(72,0),(128,0)]),([6,31,3042,4228,10570,16912],[(0,210312),(2,197775),(4,210312),(6,400590),(8,210312),(10,210312),(12,210312),(14,210312),(16,210312),(18,210312),(58,210312),(72,0),(73,145602),(74,210312),(86,145602),(106,145570),(113,203844),(114,68808),(130,210312),(137,210312),(145,210312),(146,210312),(153,134346),(154,205956)]),([6,31,3042,4228,10570,16912,31744],[(72,373768),(128,373770),(184,367620)]),([6,31,3042,4228,11242,16912],[(0,145570),(2,165007),(4,145570),(6,145570),(8,145570),(10,145570),(12,145570),(14,145570),(16,145570),(18,145570),(72,0),(73,145570),(81,145570),(86,145570),(106,145570),(109,145570),(114,68776),(117,145570),(137,145570),(145,145570),(146,145570),(153,134314)]),([6,31,3042,4228,11242,16912,31744],[(72,0),(128,0)]),([6,31,3042,4228,12684,16912],[(0,68872),(2,165007),(4,68872),(6,1294),(8,68872),(10,269380),(12,68872),(14,68872),(16,68872),(18,68872),(73,145570),(97,145570),(106,68776),(114,68872),(117,68872),(130,68872),(137,275458),(145,68872),(146,275458),(153,134410),(154,271492)]),([6,31,3042,4228,16912,17969],[(0,68808),(2,197775),(4,68808),(6,400590),(8,68808),(10,203844),(12,68808),(14,68808),(16,68808),(18,68808),(58,66760),(73,145602),(98,68808),(105,210312),(113,68808),(114,210312),(137,210312),(138,68776),(145,68808),(146,210312),(154,68808),(157,68808)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_85 : K_85.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_86 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,3042,4228,16912,24311],[(0,275458),(2,165007),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,275458),(72,0),(73,145570),(74,275458),(86,275458),(98,275458),(105,275458),(113,275458),(114,275458),(133,265218),(138,145570),(146,275458),(149,275458),(154,275458),(157,275458)]),([6,31,3042,4228,16912,24311,31744],[(72,0),(96,0)]),([6,31,3042,4228,16912,25368],[(0,134410),(2,165007),(4,134410),(6,1294),(8,134410),(10,134410),(12,134410),(14,271492),(16,134410),(18,134410),(72,0),(73,134410),(74,134410),(86,134410),(105,275458),(113,275458),(114,134410),(138,134314),(145,269380),(146,134410),(154,134410),(157,134410)]),([6,31,3042,4228,16912,31710],[(0,134346),(2,197775),(4,134346),(6,400590),(8,134346),(10,203844),(12,134346),(14,205956),(16,134346),(18,134346),(58,132298),(73,134346),(105,210312),(113,68808),(114,134346),(133,134346),(138,134314),(141,134346),(146,134346),(149,134346),(154,134346),(157,134346)]),([6,31,3042,4255,8456,16912],[(0,275458),(2,275458),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,275458),(61,145576),(73,275458),(74,275458),(77,275458),(97,275458),(101,145570),(113,269316),(129,145576),(130,275458),(133,275458),(137,275458),(145,275458),(146,275458),(153,134410),(154,271492)]),([6,31,3042,4255,8456,16912,31744],[(84,140548),(168,145576),(172,145570)]),([6,31,3042,8456,12684,16912],[(0,269380),(2,165007),(4,269380),(6,1294),(8,269380),(10,68872),(12,269380),(14,269380),(16,269380),(18,269380),(73,145570),(97,145570),(98,269316),(110,269316),(114,269380),(117,269380),(130,269380),(137,275458),(145,269380),(146,275458),(153,269380),(154,269380)]),([6,31,3042,8456,16912,21140],[(0,275458),(2,165007),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,275458),(73,145570),(82,145570),(98,275458),(105,275458),(106,145570),(113,275458),(114,275458),(130,275458),(142,275458),(145,68872),(146,269380),(154,275458),(157,275458)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_86 : K_86.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_87 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,3042,8456,16912,21140,31744],[(104,132264),(112,134312),(196,275458)]),([6,31,3042,8456,16912,28539],[(0,275458),(2,165007),(4,275458),(6,1294),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,275458),(73,145570),(82,145570),(98,275458),(105,275458),(113,134410),(114,271492),(130,275458),(133,275458),(142,145570),(146,275458),(149,275458),(154,275458),(157,275458)]),([6,31,3042,8456,16912,28539,31744],[(140,171010),(200,275458)]),([6,31,3042,8456,16912,31744,31876],[(96,367695),(128,361615),(168,361615)]),([6,31,3105,4228,16912,31744],[(0,400590),(2,197704),(4,400590),(6,400590),(8,400590),(10,400590),(12,400590),(14,400590),(16,400590),(18,132298),(57,400590),(81,400590),(82,400590),(105,400590),(106,400590),(113,400590),(114,400590),(129,72898),(130,400590),(138,400590),(153,132298),(154,400590)]),([6,31,3171,4228,8456,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,271492),(74,1294),(81,1294),(82,1294),(105,1294),(106,1294),(113,1294),(114,1294),(129,72898),(149,1294),(153,271492)]),([6,31,3171,4228,8456,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,271492),(58,400386),(74,400386),(81,400386),(82,400386),(105,400386),(106,400386),(113,400386),(114,400386),(149,269380),(153,271492)]),([6,31,3171,4228,9513,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,1156),(74,400654),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(149,1092),(153,1156)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_87 : K_87.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_88 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,3171,4228,10570,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271362),(58,400654),(74,400654),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(149,269314),(153,271362)]),([6,31,3171,4228,16912,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,134410),(58,1294),(81,1294),(82,1294),(105,1294),(106,1294),(113,1294),(114,1294),(129,72898),(141,400590),(153,134410),(154,1294)]),([6,31,3171,4228,16912,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,134410),(81,400386),(82,400386),(105,400386),(106,400386),(113,400386),(114,400386),(153,134410),(154,400386)]),([6,31,3171,4228,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,1290),(58,400654),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(153,1290),(154,400654)]),([6,31,3171,4228,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,134146),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(153,134146),(154,400654)]),([6,31,3171,5285,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271492),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(153,271492)]),([6,31,3171,5285,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,134410),(58,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(153,134410),(154,400654)]),([6,31,3171,6342,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271492),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(153,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_88 : K_88.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_89 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,3171,6342,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,134410),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(153,134410),(154,400654)]),([6,31,3171,8456,16912,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,269380),(81,1294),(82,1294),(98,1294),(105,1294),(106,1294),(113,1294),(114,1294),(129,72898),(137,203842),(154,1294),(157,1294)]),([6,31,3171,8456,16912,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,269380),(58,400386),(81,400386),(82,400386),(98,400386),(105,400386),(106,400386),(113,400386),(114,400386),(137,269380),(154,400386),(157,400386)]),([6,31,3171,8456,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,1423),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(154,400654)]),([6,31,3171,8456,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269380),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(154,400654)]),([6,31,3171,9513,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,1092),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(154,400654),(157,400654)]),([6,31,3171,10570,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269314),(58,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(138,400654),(154,400654),(157,400654)]),([6,31,4228,8192,16912,31777],[(0,132271),(2,197704),(4,132271),(6,203842),(8,132271),(10,132271),(12,132271),(14,178306),(16,132271),(18,132271),(73,132271),(74,132271),(81,132271),(82,132271),(105,66760),(106,132271),(113,66760),(114,132271),(129,72898),(137,66760),(146,132271),(149,132271),(154,66760)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_89 : K_89.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_90 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,4228,8456,9192,16912,31810],[(108,140482),(116,400386),(128,0)]),([6,31,4228,8456,11242,16912,31744],[(56,0),(128,0),(188,145570)]),([6,31,4228,8456,15855,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,178306),(74,1294),(81,1294),(82,1294),(106,1294),(109,1294),(114,1294),(117,1294),(129,72898),(137,66760),(149,178306),(158,205954)]),([6,31,4228,8456,15855,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,1416),(58,400386),(81,400386),(82,400386),(98,400386),(106,400386),(109,400386),(114,400386),(117,400386),(137,203842),(158,400386)]),([6,31,4228,8456,16912,18417],[(0,1416),(2,361610),(4,1416),(6,171074),(8,1416),(10,1416),(12,1416),(14,1416),(16,1416),(18,400386),(57,1096),(72,0),(73,1416),(74,1416),(81,1416),(82,1416),(98,1416),(105,66728),(106,1416),(113,1416),(114,1416),(145,66728),(154,1416),(157,1416)]),([6,31,4228,8456,16912,19442],[(0,275458),(2,165002),(4,275458),(6,275458),(8,275458),(10,275458),(12,275458),(14,275458),(16,275458),(18,132266),(56,0),(57,275458),(58,275458),(73,265218),(81,275458),(82,275458),(105,275458),(106,132266),(113,275458),(114,132266),(133,265288),(141,275458),(145,132266),(154,275458),(157,275458)]),([6,31,4228,8456,16912,29725],[(0,1294),(2,165007),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,275458),(56,0),(57,1294),(58,1294),(73,1284),(81,1294),(82,1294),(98,1294),(105,1294),(106,1294),(113,1294),(114,1294),(137,145570),(149,145570),(154,1294)]),([6,31,4228,8456,16912,29725,31744],[(56,0),(96,0),(136,1192),(200,1294)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_90 : K_90.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_91 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,4228,8456,16912,30750],[(0,400386),(2,361615),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,132266),(57,72706),(72,0),(73,400386),(74,400386),(81,400386),(82,400386),(105,400386),(106,400386),(113,400386),(114,400386),(133,400654),(149,400386),(154,400386)]),([6,31,4228,8456,16912,31745],[(0,1294),(2,164936),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,132266),(74,1294),(81,1294),(82,1294),(105,1294),(106,1294),(113,1294),(114,1294),(129,72866),(137,66728),(149,132266),(154,1294)]),([6,31,4228,8456,16912,31746],[(0,400386),(2,265288),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,1416),(58,400386),(81,400386),(82,400386),(98,400386),(105,400386),(106,400386),(113,400386),(114,400386),(137,334914),(154,400386)]),([6,31,4228,8456,16912,31775,31810],[(96,0),(132,400386),(136,334850),(148,400386),(204,400386)]),([6,31,4228,8456,16912,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,132271),(74,1294),(81,1294),(82,1294),(105,1294),(106,1294),(113,1294),(114,1294),(129,72898),(137,66760),(149,132271),(154,1294)]),([6,31,4228,8456,16912,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,1416),(58,400386),(81,400386),(82,400386),(98,400386),(105,400386),(106,400386),(113,400386),(114,400386),(137,203842),(154,400386)]),([6,31,4228,8456,16912,31810,31839],[(96,0),(172,400386),(176,203778),(188,400386),(204,400386)]),([6,31,4228,8456,16912,32305],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,66760),(74,1294),(81,1294),(82,1294),(98,1294),(105,1294),(106,1294),(113,1294),(114,1294),(137,66760),(149,66760),(154,1294),(157,1294)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_91 : K_91.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_92 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,4228,8456,16912,32338],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,132298),(58,400386),(81,400386),(82,400386),(105,400386),(106,400386),(113,400386),(114,400386),(137,203842),(154,400386),(157,400386)]),([6,31,4228,8456,16913,31744],[(0,400654),(2,164874),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,1194),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,9378),(130,400654),(137,66728),(149,1194),(154,400654)]),([6,31,4228,8456,16927,31744,31810],[(56,7338),(128,0),(136,334850),(200,400386)]),([6,31,4228,8456,16927,31810],[(0,400386),(2,400386),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,1416),(56,0),(57,400386),(58,400386),(73,400386),(81,400386),(82,400386),(98,400386),(101,400386),(105,400386),(106,400386),(114,400386),(129,0),(137,203842)]),([6,31,4228,8456,21140,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,132271),(58,1294),(74,1294),(81,1294),(82,1294),(106,1294),(109,1294),(113,1294),(114,1294),(129,72898),(141,1294),(149,132271)]),([6,31,4228,8456,21140,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,1416),(58,400386),(81,400386),(82,400386),(98,400386),(106,400386),(109,400386),(113,400386),(114,400386),(141,72898)]),([6,31,4228,8456,25368,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,132271),(81,1294),(82,1294),(105,1294),(106,1294),(114,1294),(117,1294),(129,72898),(137,66760),(145,271492)]),([6,31,4228,8456,25368,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,271492),(58,400386),(81,400386),(82,400386),(98,400386),(105,400386),(106,400386),(114,400386),(117,400386),(137,203842),(145,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_92 : K_92.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_93 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,4228,8458,16912,31744],[(0,400654),(2,263240),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,275848),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72962),(130,400654),(137,72962),(154,400654)]),([6,31,4228,8479,16912,31777],[(0,1294),(2,263182),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,132271),(57,1294),(74,1294),(77,1294),(82,1294),(97,1294),(105,1294),(106,1294),(113,1294),(137,66760),(149,132271),(154,1294)]),([6,31,4228,9192,10570,16912,31744],[(56,0),(128,0)]),([6,31,4228,9192,11242,16912,31744],[(56,0),(128,0),(188,145570)]),([6,31,4228,9192,16912,30653,31744],[(56,0),(96,0),(132,328878)]),([6,31,4228,9192,16912,31744,31810],[(56,394446),(96,0)]),([6,31,4228,9513,10570,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,205828),(58,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(141,203780)]),([6,31,4228,9513,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,3274),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,66760),(154,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_93 : K_93.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_94 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,4228,9513,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132100),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,66760),(145,1156)]),([6,31,4228,10570,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,373930),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,373930),(154,400654)]),([6,31,4228,10570,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271362),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,271362),(145,271362)]),([6,31,4228,12684,16912,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,132271),(74,1294),(82,1294),(85,1294),(105,1294),(106,1294),(113,1294),(114,1294),(129,72898),(149,132271),(154,1294)]),([6,31,4228,12684,16912,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,68872),(82,400386),(85,400386),(98,400386),(105,400386),(106,400386),(113,400386),(114,400386),(154,400386)]),([6,31,4228,16912,24311,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,132271),(81,1294),(82,1294),(98,1294),(106,1294),(109,1294),(114,1294),(117,1294),(129,72898),(137,66760),(146,1294),(157,132271)]),([6,31,4228,16912,24311,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,1416),(58,400386),(74,400386),(81,400386),(82,400386),(106,400386),(109,400386),(114,400386),(117,400386),(137,203842),(146,400386)]),([6,31,4228,16912,25368,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,134410),(81,1294),(82,1294),(98,1294),(105,1294),(106,1294),(114,1294),(117,1294),(129,72898),(137,66760),(145,134410),(146,1294),(157,132298)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_94 : K_94.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_95 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,4228,16912,25368,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,134410),(58,400386),(81,400386),(82,400386),(105,400386),(106,400386),(114,400386),(117,400386),(137,203842),(145,134410),(146,400386)]),([6,31,4228,17969,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,373930),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(129,72898),(130,400654),(146,400654),(154,400654)]),([6,31,4228,17969,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,1290),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,66760),(145,1290),(146,400654)]),([6,31,4228,19026,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132100),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(137,132100),(145,134146),(146,400654)]),([6,31,4229,8456,16912,31744],[(0,400654),(2,164872),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132266),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,7330),(130,400654),(137,1192),(149,132266),(154,400654)]),([6,31,4255,8456,16912,31744,31810],[(96,7338),(136,334850),(200,400386)]),([6,31,4255,8456,16912,31810],[(0,400386),(2,394248),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,1416),(58,400386),(61,400386),(73,400386),(81,400386),(96,0),(97,400386),(98,400386),(105,400386),(106,400386),(113,400386),(114,400386),(137,203778),(154,400386)]),([6,31,5285,6342,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271492),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(153,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_95 : K_95.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_96 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,5285,6342,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,134410),(74,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(153,134410),(154,400654)]),([6,31,5285,8456,16912,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,132298),(74,171278),(81,171278),(82,171278),(105,171278),(106,171278),(113,171278),(114,171278),(129,72898),(130,171278),(137,66760),(149,132298),(154,171278)]),([6,31,5285,8456,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132298),(74,400654),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654),(149,132298),(154,400654)]),([6,31,5285,8456,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132264),(74,400654),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654),(149,132264)]),([6,31,5285,9513,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132298),(74,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(154,400654)]),([6,31,5285,12684,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132298),(74,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(150,132298),(154,400654)]),([6,31,6342,8456,16912,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,66760),(58,203778),(81,203842),(82,203842),(98,203842),(105,203842),(106,203842),(113,203842),(114,203842),(137,203842),(154,203842)]),([6,31,6342,8456,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,203842),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654),(154,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_96 : K_96.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_97 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,6342,8456,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,66730),(81,400654),(82,400654),(113,400654),(114,400654),(129,72898),(130,400654)]),([6,31,6342,10570,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,203780),(58,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(154,400654)]),([6,31,6342,12684,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,66564),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(150,66564),(154,400654)]),([6,31,8456,9513,16912,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,66760),(74,203778),(82,203842),(85,203842),(98,203842),(105,203842),(106,203842),(113,203842),(114,203842),(145,72898),(154,203842),(157,203842)]),([6,31,8456,10570,16912,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,203842),(58,171278),(82,171278),(85,171278),(98,171278),(105,171278),(106,171278),(113,171278),(114,171278),(129,72898),(130,171278),(141,203842),(145,203842),(154,171278),(157,171278)]),([6,31,8456,12684,16912,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,132271),(82,1294),(85,1294),(105,1294),(106,1294),(113,1294),(114,1294),(129,72898),(145,66760),(154,1294)]),([6,31,8456,12684,16912,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,269380),(74,400386),(82,400386),(85,400386),(98,400386),(105,400386),(106,400386),(113,400386),(114,400386),(145,203842),(154,400386)]),([6,31,8456,16912,17969,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(74,203842),(81,203842),(82,203842),(98,203778),(105,203842),(106,203842),(114,203842),(117,203842),(146,203842),(153,269380),(154,203842)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_97 : K_97.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_98 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,8456,16912,19026,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,203842),(81,171278),(82,171278),(105,171278),(106,171278),(114,171278),(117,171278),(129,72898),(130,171278),(146,171278),(153,203842),(154,171278)]),([6,31,8456,16912,21140,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,66760),(58,1294),(74,1294),(81,1294),(82,1294),(105,1294),(106,1294),(114,1294),(117,1294),(129,72898),(141,66760),(146,1294),(149,1294),(153,66760)]),([6,31,8456,16912,21140,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,1416),(74,400386),(81,400386),(82,400386),(98,400386),(105,400386),(106,400386),(114,400386),(117,400386),(146,400386),(149,400386),(153,203842)]),([6,31,8456,16912,28539,31777],[(0,1294),(2,197704),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,203842),(58,1294),(81,1294),(82,1294),(106,1294),(109,1294),(114,1294),(117,1294),(129,72898),(141,203842),(146,1294),(153,203842)]),([6,31,8456,16912,28539,31810],[(0,400386),(2,197704),(4,400386),(6,400386),(8,400386),(10,400386),(12,400386),(14,400386),(16,400386),(18,1416),(74,400386),(81,400386),(82,400386),(98,400386),(106,400386),(109,400386),(114,400386),(117,400386),(146,400386),(153,72898)]),([6,31,8456,16912,30653,31777],[(0,171278),(2,197704),(4,171278),(6,171278),(8,171278),(10,171278),(12,171278),(14,171278),(16,171278),(18,66760),(74,171278),(81,171278),(82,171278),(106,171278),(109,171278),(114,171278),(117,171278),(129,72898),(130,171278),(146,171278),(149,171278),(153,66760),(158,66760)]),([6,31,8456,16912,31710,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(74,203842),(81,203842),(82,203842),(98,203778),(101,203842),(106,203842),(109,203842),(114,203842),(117,203842),(146,203842),(149,203842),(153,203842),(158,203842)]),([6,31,8456,16912,31777,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(74,203842),(81,203842),(82,203842),(97,203842),(98,203778),(106,203842),(114,203842),(117,203842),(138,203842),(146,203842),(149,203842),(153,269380),(154,203842)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_98 : K_98.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_99 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,8456,16912,31777,31843],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(74,203842),(81,203842),(82,203842),(97,203842),(102,171074),(106,203842),(114,203842),(117,203842),(138,203842),(146,203842),(149,203842),(154,203842),(157,203842)]),([6,31,8456,16912,31777,31876],[(0,66760),(2,197704),(4,66760),(6,66760),(8,66760),(10,66760),(12,66760),(14,66760),(16,66760),(18,132298),(58,66760),(81,66760),(82,66760),(97,66760),(106,66760),(109,66760),(114,66760),(138,66760),(141,66760),(146,66760),(154,66760)]),([6,31,8456,16912,31777,31909],[(0,66760),(2,197704),(4,66760),(6,66760),(8,66760),(10,66760),(12,66760),(14,66760),(16,66760),(18,132271),(58,66760),(81,66760),(82,66760),(97,66760),(98,1224),(106,66760),(109,66760),(114,66760),(138,66760),(141,66760),(146,66760),(154,66760),(157,66760)]),([6,31,8456,16912,31810,31843],[(0,269380),(2,197704),(4,269380),(6,68872),(8,269380),(10,269380),(12,269380),(14,269380),(16,269380),(18,269380),(74,269380),(81,269380),(82,271492),(102,171278),(106,171278),(114,269380),(117,269380),(130,269316),(138,72898),(146,269380),(149,269380),(154,269380),(157,269380)]),([6,31,8456,16912,31810,31876],[(0,334850),(2,197704),(4,334850),(6,334850),(8,334850),(10,334850),(12,334850),(14,1352),(16,334850),(18,334850),(74,334850),(81,334850),(82,334850),(106,334850),(114,334850),(130,334850),(138,334850),(146,334850),(154,203842)]),([6,31,8456,16912,31810,31942],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,66760),(16,203842),(18,203842),(74,203842),(81,203842),(82,203842),(106,203842),(114,203842),(130,203778),(138,203842),(146,203842),(154,203842),(157,203842)]),([6,31,8456,17969,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,203842),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(146,400654),(154,400654)]),([6,31,8456,17969,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,66730),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(141,66730),(146,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_99 : K_99.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_100 : List (List ℕ × List (ℕ × ℕ)) := [([6,31,8456,19026,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132264),(81,400654),(82,400654),(105,400654),(106,400654),(129,72898),(130,400654),(146,400654)]),([6,31,9513,10570,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,203780),(58,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(154,400654),(157,400654)]),([6,31,9513,12684,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132298),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(150,132298),(154,400654)]),([6,31,10570,12684,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269314),(74,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(150,400654),(154,400654)]),([6,63,2114,8456,16912,31744],[(0,335118),(2,197640),(4,335118),(6,335118),(8,335118),(10,335118),(12,335118),(14,335118),(16,335118),(18,269316),(81,335118),(82,335118),(98,335118),(105,335118),(106,335118),(113,335118),(114,335118),(129,7362),(130,335118),(137,203778),(138,335118),(154,335118),(157,335118)]),([6,1023,1087,2114,4228,8456],[(0,271364),(2,400654),(4,271364),(6,197642),(8,271364),(10,1226),(12,271364),(14,271364),(16,271364),(18,3338),(57,271364),(73,271364),(98,269316),(106,271364),(113,271364),(114,271364),(134,205826),(145,205826),(146,271364),(153,269380),(154,271364)]),([6,1023,1087,2114,8456,16912],[(0,269316),(2,400654),(4,269316),(6,197640),(8,269316),(10,1224),(12,269316),(14,3336),(16,269316),(18,269316),(57,269316),(62,269316),(73,269316),(78,269316),(113,203778),(114,269316),(129,275848),(130,269316),(138,269316),(145,203778),(146,269316),(153,269316),(154,271492)]),([6,1057,1087,2114,4228,8456,17392,31744],[(80,0),(136,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_100 : K_100.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_101 : List (List ℕ × List (ℕ × ℕ)) := [([6,1057,1087,2114,4228,32272],[(0,134410),(2,134410),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,68872),(58,134410),(61,134410),(73,134410),(74,134410),(82,132362),(97,134410),(98,134410),(113,134410),(114,134410),(129,68872),(130,134410),(146,134410),(149,132298)]),([6,1057,1087,2114,5092,8456,16912,31744],[(80,0)]),([6,1057,1087,2114,8456,17392],[(0,275848),(2,275848),(4,275848),(6,361608),(8,275848),(10,66760),(12,275848),(14,68872),(16,275848),(18,400654),(57,275848),(58,275848),(61,275848),(73,275848),(74,275848),(77,275848),(97,275848),(98,275848),(101,275848),(105,265608),(113,275848),(114,275848),(129,269380),(130,275848),(133,275848),(138,275848),(146,275848)]),([6,1057,1087,3042,4228,16912],[(0,134346),(2,134346),(4,134346),(6,197775),(8,134346),(10,400590),(12,134346),(14,203844),(16,134346),(18,205956),(58,134346),(61,134346),(74,134346),(82,132298),(97,134346),(98,134346),(105,134346),(129,68808),(130,134346),(145,210312),(153,68808),(154,134346)]),([6,1057,1087,8456,16912,31810],[(0,203842),(2,203842),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,269380),(58,203842),(61,203842),(73,203842),(74,203842),(97,203842),(98,203842),(106,203842),(113,203842),(114,203842),(130,203842),(133,203778),(154,203842),(157,203842)]),([6,1057,2079,4228,16912,31744],[(0,361678),(2,361678),(4,361678),(6,361678),(8,361678),(10,361678),(12,361678),(14,361678),(16,361678),(18,132298),(58,361678),(73,361678),(74,361678),(97,361678),(98,361678),(113,361678),(114,361678),(130,361678),(153,132298),(154,361678)]),([6,1057,2114,2143,4228,8456,17392,31744],[(80,0),(136,0),(144,0)]),([6,1057,2114,2143,5092,8456,16912,31744],[(136,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_101 : K_101.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_102 : List (List ℕ × List (ℕ × ℕ)) := [([6,1057,2114,3042,4255,8456],[(0,271428),(2,271428),(4,271428),(6,271428),(8,271428),(10,72974),(12,271428),(14,197711),(16,271428),(18,68874),(57,271428),(58,271428),(74,271428),(82,271428),(85,271428),(97,271364),(98,271428),(105,271428),(129,80066),(130,271428),(137,80066),(138,271428),(153,80066)]),([6,1057,2114,4127,8456,31744],[(0,269380),(2,269380),(4,269380),(6,66760),(8,269380),(10,197704),(12,269380),(14,68872),(16,269380),(18,269380),(57,269380),(58,269380),(73,269316),(74,269380),(97,72898),(98,269380),(105,203842),(106,269380),(130,269380),(138,269380),(146,269380),(153,269380),(158,269380)]),([6,1057,2114,4228,8456,8479,17392,31744],[]),([6,1057,2114,4228,8479,17392],[(0,134536),(2,134536),(4,134536),(6,134536),(8,134536),(10,134536),(12,134536),(14,361610),(16,134536),(18,400516),(57,134536),(58,134536),(73,134536),(74,134536),(81,134536),(82,134536),(98,134536),(105,132488),(114,134216),(117,134536),(130,134536),(138,134536),(141,132458),(145,138594)]),([6,1057,2114,4228,8479,17392,31744],[(58,0),(98,0),(106,0)]),([6,1057,2114,4228,9192,16927,31744],[]),([6,1057,2114,4228,31775,32008],[(0,271492),(2,271492),(4,271492),(6,271492),(8,271492),(10,271492),(12,271492),(14,271492),(16,271492),(18,72898),(57,271492),(58,271492),(73,271492),(74,271492),(81,271492),(82,271492),(98,271492),(117,269444),(130,271492),(146,271492),(149,269380)]),([6,1057,2114,4255,8456,31775],[(0,72974),(2,72974),(4,72974),(6,72974),(8,72974),(10,72974),(12,72974),(14,72974),(16,72974),(18,271428),(57,72974),(58,72974),(73,7438),(74,72974),(97,72974),(98,72974),(105,72974),(106,72974),(113,72964),(130,72974),(138,72974),(149,269380)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_102 : K_102.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_103 : List (List ℕ × List (ℕ × ℕ)) := [([6,1057,2114,4255,9192,16912,31744],[(200,145668)]),([6,1057,2114,5092,8456,8479,16912,31744],[]),([6,1057,2114,5092,8479,16912,31744],[(58,0),(176,134511)]),([6,1057,2114,8456,8479,17392],[(0,265608),(2,265608),(4,265608),(6,66760),(8,265608),(10,265608),(12,265608),(14,361608),(16,265608),(18,400644),(57,265608),(58,265608),(73,265608),(74,265608),(81,265608),(82,265608),(97,265608),(98,265608),(114,265608),(117,265608),(130,265608),(133,265544),(138,265608),(145,138594)]),([6,1057,2114,8456,16415,31744],[(0,400463),(2,400463),(4,400463),(6,400463),(8,400463),(10,400463),(12,400463),(14,400463),(16,400463),(18,72898),(57,400463),(58,400463),(73,400463),(74,400463),(81,400463),(82,400463),(97,400399),(98,400463),(129,72898),(130,400463),(137,203842),(138,400463)]),([6,1057,2114,8456,17376,31744],[(0,197704),(2,197704),(4,197704),(6,66760),(8,197704),(10,68872),(12,197704),(14,72898),(16,197704),(18,197704),(57,197704),(58,197704),(73,197704),(74,197704),(81,197704),(82,197704),(98,197704),(101,197640),(129,197704),(130,197704),(137,203842),(142,197704),(146,197704),(154,275848)]),([6,1057,2114,8456,17392,32736],[(0,361608),(2,361608),(4,361608),(6,361608),(8,361608),(10,361608),(12,361608),(14,361608),(16,361608),(18,275848),(57,361608),(58,361608),(73,361608),(74,361608),(81,361608),(82,361608),(98,361608),(101,361608),(106,197768),(130,361608),(133,361608),(146,361608),(157,275848)]),([6,1057,2143,5092,8456,16912,31744],[(58,0),(98,0),(106,0),(118,0),(168,132431),(193,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_103 : K_103.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_104 : List (List ℕ × List (ℕ × ℕ)) := [([6,1057,3042,4255,8456,16912],[(0,145602),(2,145602),(4,145602),(6,66830),(8,145602),(10,197775),(12,145602),(14,145602),(16,145602),(18,145602),(57,145570),(58,145602),(61,145602),(73,275458),(74,145602),(77,145570),(97,145602),(98,145602),(101,145570),(106,145602),(113,145602),(118,79042),(129,145602),(130,145602),(133,145570),(137,275522),(142,80066),(146,275522),(153,134410),(154,271492)]),([6,1057,3042,4255,8456,16912,31744],[(172,145570)]),([6,1057,8456,16912,31775,31876],[(0,66703),(2,66703),(4,66703),(6,66703),(8,66703),(10,66703),(12,66703),(14,66703),(16,66703),(18,72898),(57,66703),(58,66703),(73,66703),(74,66703),(81,66703),(82,66703),(98,66703),(101,66703),(109,66703),(129,72898),(130,66703),(138,66703),(141,66703)]),([6,1087,2017,2114,4228,8456],[(0,271492),(2,361482),(4,271492),(6,400654),(8,271492),(10,132298),(12,271492),(14,271492),(16,271492),(18,134410),(58,271364),(81,271492),(97,271492),(98,271428),(106,269444),(113,271492),(114,271492),(129,9570),(145,205954),(146,271492),(153,269380),(154,271492)]),([6,1087,2017,2114,4228,8456,16912,31744],[(72,0),(128,0),(248,0)]),([6,1087,2017,2114,8456,16912],[(0,269380),(2,361480),(4,269380),(6,400654),(8,269380),(10,66760),(12,269380),(14,68872),(16,269380),(18,269380),(58,269316),(81,269380),(97,7522),(113,203842),(114,269380),(130,269380),(137,275848),(138,269380),(145,203842),(146,269380),(153,269380),(154,271492)]),([6,1087,2047,2114,4228,8456],[(0,271364),(2,197642),(4,271364),(6,400654),(8,271364),(10,1226),(12,271364),(14,271364),(16,271364),(18,3338),(58,271364),(61,271364),(81,271364),(98,271364),(106,269316),(113,271364),(114,271364),(142,205826),(145,205826),(146,271364),(153,269380),(154,271364)]),([6,1087,2047,2114,8456,16912],[(0,269316),(2,197640),(4,269316),(6,400654),(8,269316),(10,1224),(12,269316),(14,3336),(16,269316),(18,269316),(58,269316),(61,269316),(81,269316),(86,269316),(113,203778),(114,269316),(130,269316),(137,275848),(138,269316),(145,203778),(146,269316),(153,269316),(154,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_104 : K_104.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_105 : List (List ℕ × List (ℕ × ℕ)) := [([6,1087,2114,3042,4228,8456],[(0,271364),(2,197647),(4,271364),(6,165066),(8,271364),(10,400654),(12,271364),(14,271364),(16,271364),(18,3338),(74,271364),(82,271364),(85,271364),(97,271364),(98,271364),(105,271364),(106,271364),(114,269316),(129,14530),(137,205986),(138,271364),(153,269380),(154,271364)]),([6,1087,2114,3042,8456,16912],[(0,269316),(2,197775),(4,269316),(6,165064),(8,269316),(10,400654),(12,269316),(14,3336),(16,269316),(18,269316),(74,269316),(82,269316),(85,269316),(97,145602),(105,203938),(106,269316),(130,269316),(137,203938),(138,269316),(145,275848),(146,269316),(153,269316),(154,271492)]),([6,1087,2114,4096,8456,31744],[(0,269316),(2,197640),(4,269316),(6,1224),(8,269316),(10,269316),(12,269316),(14,3336),(16,269316),(18,269316),(73,269316),(74,269316),(81,269316),(82,269316),(105,203778),(106,269316),(113,203778),(114,269316),(130,269316),(138,269316),(146,269316),(149,269316),(153,269316),(158,269316)]),([6,1087,2114,4228,8456,17392],[(0,275848),(2,361610),(4,275848),(6,1226),(8,275848),(10,275848),(12,275848),(14,3338),(16,275848),(18,400654),(73,275528),(74,275848),(78,275848),(81,275848),(82,275848),(86,275848),(97,265608),(105,275848),(106,275848),(113,275848),(114,275848),(117,275848),(130,275848),(138,275848),(145,269316),(149,275850)]),([6,1087,2114,4228,8456,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(149,269316),(153,271364)]),([6,1087,2114,4228,8456,31775],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(73,72974),(74,400654),(81,400654),(82,400654),(97,400644),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(149,269316)]),([6,1087,2114,4228,8456,31777],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271492),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(149,269380),(153,271492)]),([6,1087,2114,4228,8456,31807],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(73,72974),(74,400654),(81,400654),(82,400654),(97,400644),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(133,400654),(138,400654),(149,269316)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_105 : K_105.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_106 : List (List ℕ × List (ℕ × ℕ)) := [([6,1087,2114,4228,8456,31810],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(149,269316),(153,271364)]),([6,1087,2114,4228,8456,32272],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,369666),(74,400654),(81,400654),(82,400654),(102,400650),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(149,269316),(153,134410)]),([6,1087,2114,4228,10570,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(58,400654),(74,400654),(81,400654),(82,400654),(106,400654),(109,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400590),(149,269316),(153,271364)]),([6,1087,2114,4228,12684,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(130,400654),(138,400654),(153,271364),(158,271364)]),([6,1087,2114,4228,16912,31777],[(0,3342),(2,3342),(4,3342),(6,3342),(8,3342),(10,3342),(12,3342),(14,3342),(16,3342),(18,134410),(58,1294),(81,3342),(82,3342),(105,3342),(106,3342),(113,3342),(114,3342),(138,3342),(141,1230),(153,134410),(154,3342)]),([6,1087,2114,4228,17969,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,3338),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400590),(153,3338),(154,400654)]),([6,1087,2114,4228,24311,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,3338),(74,400654),(81,400654),(82,400654),(106,400654),(109,400654),(114,400654),(117,400654),(130,400654),(138,400654),(149,3336),(153,3338)]),([6,1087,2114,4228,31744,32008],[(0,271364),(2,271364),(4,271364),(6,271364),(8,271364),(10,271364),(12,271364),(14,271364),(16,271364),(18,331022),(74,271364),(81,271364),(82,271364),(106,271364),(114,271364),(117,269316),(138,271364),(146,271364),(149,269316),(154,271364),(157,271364)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_106 : K_106.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_107 : List (List ℕ × List (ℕ × ℕ)) := [([6,1087,2114,4255,8456,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(57,400654),(74,400654),(82,400654),(97,400654),(105,400654),(106,400654),(113,400654),(130,400654),(138,400654),(149,269316),(153,271364)]),([6,1087,2114,5092,8456,31744],[(0,269316),(2,269316),(4,269316),(6,1224),(8,269316),(10,269316),(12,269316),(14,3336),(16,269316),(18,269316),(57,269316),(74,269316),(82,269316),(97,203778),(105,203778),(106,269316),(113,400654),(130,269316),(138,269316),(149,269316),(150,269316),(153,269316),(154,203778)]),([6,1087,2114,5285,8456,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271492),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,7362),(130,400654),(138,400654),(149,269316),(153,271492)]),([6,1087,2114,5285,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,134410),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,7362),(130,400654),(138,400654),(141,400590),(153,134410),(154,400654)]),([6,1087,2114,5311,8456,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(57,400654),(74,400654),(77,400654),(82,400654),(97,400654),(105,400654),(106,400654),(113,400654),(129,271364),(130,400654),(138,400654),(149,269316),(153,271364)]),([6,1087,2114,6342,8456,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(74,400654),(82,400654),(85,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,203842),(138,400654),(149,269316),(153,271364)]),([6,1087,2114,8456,12684,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269380),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(114,400654),(117,400654),(130,400654),(138,400654),(157,269316),(158,400654)]),([6,1087,2114,8456,15855,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(81,400654),(82,400654),(98,400654),(106,400654),(109,400654),(114,400654),(117,400654),(129,7362),(130,400654),(137,203778),(138,400654),(157,269316),(158,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_107 : K_107.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_108 : List (List ℕ × List (ℕ × ℕ)) := [([6,1087,2114,8456,16384,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(81,400654),(82,400654),(97,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,7362),(130,400654),(137,203778),(138,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,16912,17392],[(0,275848),(2,361610),(4,275848),(6,1224),(8,275848),(10,3336),(12,275848),(14,275848),(16,275848),(18,400654),(73,265608),(81,275848),(82,275848),(98,275848),(102,275848),(105,203778),(106,275848),(110,275848),(113,269316),(114,275848),(118,275848),(130,275848),(138,275848),(153,269316),(154,275848),(157,275848)]),([6,1087,2114,8456,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,7362),(130,400654),(137,203778),(138,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,16912,31775],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(73,400644),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,16912,31777],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269380),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,72898),(130,400654),(137,203842),(138,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,16912,31807],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(73,400644),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(133,400654),(138,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,16912,31810],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(62,204046),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,16912,32272],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,203778),(138,400654),(154,400654),(157,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_108 : K_108.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_109 : List (List ℕ × List (ℕ × ℕ)) := [([6,1087,2114,8456,16927,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(57,400654),(73,400654),(81,400654),(82,400654),(98,400654),(106,400654),(114,400654),(129,269316),(130,400654),(137,203778),(138,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,17392],[(1,275848),(3,275848),(5,275848),(7,275848),(9,275848),(11,275848),(13,269316),(15,269316),(59,275848),(63,275848),(75,275848),(79,275848),(83,275848),(87,275848),(99,269316),(103,275848),(107,269316),(111,275848),(115,203778),(119,203778)]),([6,1087,2114,8456,17392,31744],[(0,269316),(2,269316),(4,269316),(6,1224),(8,269316),(10,3336),(12,269316),(14,269316),(16,269316),(18,269316),(57,198031),(73,265615),(81,203778),(82,269316),(98,269316),(101,197640),(106,269316),(114,269444),(129,361615),(130,269316),(134,275848),(137,203778),(138,269316),(142,275848),(146,275855),(150,269316),(154,275848),(157,400654),(158,275848)]),([6,1087,2114,8456,17969,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269380),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,203842),(138,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,17983,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(57,400654),(73,400654),(81,400654),(82,400654),(98,400654),(101,400654),(106,400654),(114,400654),(130,400654),(137,203778),(138,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,19026,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(81,400654),(82,400654),(98,400654),(106,400654),(109,400654),(113,400654),(114,400654),(129,7362),(130,400654),(138,400654),(154,400654),(157,400654)]),([6,1087,2114,8456,25368,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271492),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(114,400654),(117,400654),(129,7362),(130,400654),(137,203778),(138,400654),(145,271492),(157,269316)]),([6,1087,2114,8456,28539,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(81,400654),(82,400654),(98,400654),(106,400654),(109,400654),(114,400654),(117,400654),(130,400654),(138,400654),(145,271364),(157,269316)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_109 : K_109.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_110 : List (List ℕ × List (ℕ × ℕ)) := [([6,1087,2114,10570,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(58,400654),(82,400654),(85,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,7362),(130,400654),(138,400654),(141,400590),(154,400654),(157,400654)]),([6,1087,2114,16912,24311,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,3336),(74,400654),(81,400654),(82,400654),(106,400654),(109,400654),(114,400654),(117,400654),(129,7362),(130,400654),(137,203778),(138,400654),(146,400654),(149,400654)]),([6,1087,2114,16912,25368,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,269316),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(129,7362),(130,400654),(137,203778),(138,400654),(145,134410),(146,400654)]),([6,1087,4228,6342,8456,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,271364),(82,400654),(85,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,66760),(153,271364)]),([6,1087,4228,8456,10570,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,205826),(58,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(130,400654),(141,203778),(149,205826)]),([6,1087,4228,8456,16912,31777],[(0,1294),(2,1294),(4,1294),(6,1294),(8,1294),(10,1294),(12,1294),(14,1294),(16,1294),(18,132298),(74,1294),(81,1294),(82,1294),(105,1294),(106,1294),(113,1294),(114,1294),(129,72898),(137,66760),(149,132298),(154,1294)]),([6,1087,4228,8456,17969,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,1226),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,66760),(149,1226),(154,400654)]),([6,1087,4228,8456,30653,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,1226),(58,400654),(81,400654),(82,400654),(106,400654),(109,400654),(114,400654),(117,400654),(130,400654),(141,1224),(145,271364),(158,1226)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_110 : K_110.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_111 : List (List ℕ × List (ℕ × ℕ)) := [([6,1087,5285,8456,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,132298),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,7362),(130,400654),(137,1224),(149,132298),(154,400654)]),([6,1087,8456,10570,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,203778),(58,400654),(82,400654),(85,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,7362),(130,400654),(141,203778),(145,203778),(154,400654),(157,400654)]),([6,1087,8456,16912,19026,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,203778),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(129,7362),(130,400654),(146,400654),(153,203778),(154,400654)]),([6,1087,8456,16912,30653,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,1224),(74,400654),(81,400654),(82,400654),(106,400654),(109,400654),(114,400654),(117,400654),(129,7362),(130,400654),(146,400654),(149,400654),(153,1224),(158,1224)]),([6,1087,8456,16912,31744,31810],[(0,203778),(2,203778),(4,203778),(6,203778),(8,203778),(10,203778),(12,203778),(14,203778),(16,203778),(18,269316),(74,203778),(81,203778),(82,203778),(97,203778),(102,203778),(106,203778),(114,203778),(117,203778),(138,203778),(146,203778),(149,203778),(154,203778),(157,203778)]),([6,2114,3042,4228,8456,16927,31744],[(56,0),(96,373770),(104,0),(168,0)]),([6,2114,3042,4255,8456,16912],[(0,145576),(2,145576),(4,145576),(6,7438),(8,145576),(10,171151),(12,145576),(14,145576),(16,145576),(18,145576),(57,145570),(58,145576),(61,145576),(73,275458),(77,145576),(96,0),(97,145576),(98,145576),(101,145570),(106,145576),(113,145576),(129,145576),(130,145576),(133,145570),(137,275464),(146,275464),(153,134410),(154,271492)]),([6,2114,3042,4255,8456,16912,31744],[(96,373768),(172,145570)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_111 : K_111.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_112 : List (List ℕ × List (ℕ × ℕ)) := [([6,2114,4228,8456,9192,16927,31744],[(72,0),(96,0),(168,0)]),([6,2114,4228,8456,16927,31744,31775],[(128,0),(176,9384)]),([6,2114,4228,8456,31680,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,197642),(57,400654),(58,400654),(73,400654),(74,400654),(81,400654),(82,400654),(109,400654),(130,400654),(141,197640),(145,271364),(158,197642)]),([6,2114,4228,9192,16927,31744],[(2,0),(10,0),(57,66760),(58,203842),(73,0),(74,0),(82,400399),(85,0),(98,361487),(129,0),(138,0)]),([6,2114,4255,8456,9192,16912,31744],[(72,0),(96,0),(188,145572)]),([6,2114,4255,8456,16912,17392],[(0,275464),(2,275464),(4,275464),(6,171146),(8,275464),(10,275464),(12,275464),(14,275464),(16,275464),(18,138410),(61,275464),(73,275464),(74,275464),(81,265224),(97,275464),(98,138410),(113,275464),(114,138410),(128,0),(129,138410),(130,275464),(145,138410),(154,275464),(157,275464)]),([6,2114,4255,8456,16912,31744,31775],[(200,7438)]),([6,2114,4255,8456,16912,31775],[(0,7438),(2,7438),(4,7438),(6,7438),(8,7438),(10,7438),(12,7438),(14,7438),(16,7438),(18,145576),(61,7438),(73,7438),(74,7438),(81,7428),(97,7438),(98,7438),(106,7438),(113,7438),(114,7438),(130,7438),(133,7438),(149,145576),(154,7438)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_112 : K_112.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_113 : List (List ℕ × List (ℕ × ℕ)) := [([6,2114,4255,8456,16927,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,7338),(58,400654),(61,400654),(73,400654),(74,400654),(81,400654),(98,400654),(101,400654),(114,400654),(128,0),(129,7338),(130,400654),(137,9384),(154,400654)]),([6,2114,4255,9192,16912,31744],[(2,0),(58,361646),(73,0),(85,361615),(97,132298),(98,205954),(113,134314),(129,394446),(130,210306),(137,361615),(138,145762),(150,145572),(154,145572)]),([6,2114,8456,16912,31680,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,197640),(57,400654),(58,400654),(73,400654),(74,400654),(81,400654),(82,400654),(117,400654),(129,203778),(130,400654),(146,400654),(149,400654),(153,197640),(158,197640)]),([6,2114,8456,16912,31744,31807],[(0,7362),(2,7362),(4,7362),(6,7362),(8,7362),(10,7362),(12,7362),(14,7362),(16,7362),(18,361615),(57,7362),(58,7362),(73,7362),(74,7362),(81,7362),(82,7362),(97,203778),(106,361615),(117,7362),(149,7362),(154,7362),(157,7362)]),([6,2114,8456,16912,31775,31777],[(0,171151),(2,171151),(4,171151),(6,171151),(8,171151),(10,171151),(12,171151),(14,171151),(16,171151),(18,72898),(57,171151),(58,171151),(73,171151),(74,171151),(81,171151),(82,171151),(117,171151),(129,203842),(138,171151),(149,72898),(153,72898)]),([6,2114,8456,16912,31775,31876],[(0,361615),(2,361615),(4,361615),(6,361615),(8,361615),(10,361615),(12,361615),(14,361615),(16,361615),(18,72898),(57,361615),(58,361615),(73,361615),(74,361615),(81,361615),(82,361615),(101,361615),(109,361615),(129,66760),(138,361615)]),([6,2114,8456,16912,31777,31807],[(0,72898),(2,72898),(4,72898),(6,72898),(8,72898),(10,72898),(12,72898),(14,72898),(16,72898),(18,361615),(57,72898),(58,72898),(73,72898),(74,72898),(81,72898),(82,72898),(97,203842),(106,361615),(117,72898),(149,72898),(154,72898),(157,72898)]),([6,2114,8456,16912,31777,32736],[(0,197704),(2,197704),(4,197704),(6,197704),(8,197704),(10,197704),(12,197704),(14,197704),(16,197704),(18,171278),(57,197704),(58,197704),(73,197704),(74,197704),(81,197704),(82,197704),(97,197704),(98,197704),(114,197704),(117,197704),(149,197704),(154,197704),(157,197640)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_113 : K_113.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_114 : List (List ℕ × List (ℕ × ℕ)) := [([6,2114,8456,16912,31777,32737],[(0,197704),(2,197704),(4,197704),(6,197704),(8,197704),(10,197704),(12,197704),(14,197704),(16,197704),(18,7438),(57,197704),(58,197704),(73,197704),(74,197704),(81,197704),(82,197704),(96,0),(97,197704),(98,197704),(114,197704),(117,197704),(149,197704),(154,197704),(157,197704)]),([6,3042,4255,8456,16912],[(1,145570),(2,0),(3,145570),(5,275458),(7,275458),(9,145570),(10,0),(11,145570),(13,145570),(15,145570),(74,0),(75,145570),(79,145570),(83,275458),(87,145570),(97,0),(99,145570),(103,145570),(107,275458),(111,275458),(113,0),(115,145570),(119,145570)]),([6,3042,4255,8456,16912,31744],[(2,0),(10,0),(61,140548),(62,265354),(73,0),(74,0),(81,263172),(97,132266),(113,134410),(114,271492),(129,394510),(130,275842),(134,145570),(137,361615),(138,145762),(142,145570),(146,275458),(150,145570),(154,145570),(158,275458)]),([7,1,31,992,4228,8456,16912],[(0,132266),(2,132266),(4,132266),(6,328847),(8,132266),(10,400654),(12,132266),(14,171074),(16,132266),(18,132266),(20,132266),(22,173186),(58,132266),(61,132266),(73,132266),(74,132266),(81,132266),(82,132266),(96,0),(97,132266),(98,132266),(105,132266),(129,132266),(130,132266),(137,132266),(138,132266),(146,132266),(153,132266),(154,132266),(168,0),(169,66728),(170,132266),(185,275848),(193,66728),(194,132266),(201,134410),(202,132266)]),([7,1,31,4228,8456,16912,31744],[(0,400654),(2,400654),(4,400654),(6,164936),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132266),(58,400654),(61,400654),(73,400654),(74,400654),(97,400654),(98,400654),(106,400654),(113,400654),(114,400654),(129,400654),(130,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,132266),(170,400654),(177,72866),(178,400654),(185,66728),(197,132266),(202,400654)]),([7,1,992,4228,8456,16912,31744],[(0,328847),(2,328847),(4,328847),(6,72866),(8,328847),(10,328847),(12,328847),(14,328847),(16,328847),(18,328847),(20,328847),(22,132266),(56,0),(57,328847),(58,328847),(72,0),(73,328847),(74,328847),(97,328847),(98,328847),(106,328847),(113,328847),(114,328847),(128,0),(129,328847),(130,328847),(145,328847),(146,328847),(153,328847),(154,328847),(168,0),(169,132266),(170,328847),(177,164936),(178,328847),(185,66728),(186,328847),(194,328847),(197,328847)]),([7,2,31,992,4228,8456,16912],[(0,275848),(2,275848),(4,275848),(6,275848),(8,275848),(10,400654),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(58,275848),(61,275848),(73,0),(74,275848),(81,265288),(82,275848),(97,275848),(98,275848),(105,275528),(106,275848),(128,0),(129,275848),(130,275848),(137,265608),(153,269380),(154,68872),(169,275848),(170,275848),(178,275848),(181,265288),(185,275848),(193,275848),(194,275848),(201,134410),(202,271492)]),([7,2,31,992,4228,8456,16912,31744],[(60,265288),(116,140548),(128,0),(216,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_114 : K_114.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_115 : List (List ℕ × List (ℕ × ℕ)) := [([7,2,31,4228,8456,16912,31744],[(0,400654),(2,400654),(4,400654),(6,265288),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(58,400654),(61,400654),(73,400654),(74,400654),(82,400654),(97,400654),(98,400654),(113,400654),(114,400654),(129,400654),(130,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72964),(170,400654),(177,72964),(178,400654),(185,72964),(202,400654)]),([7,2,992,4228,8456,16912,31744],[(0,265288),(2,265288),(4,265288),(6,72964),(8,265288),(10,265288),(12,265288),(14,265288),(16,265288),(18,265288),(20,265288),(22,265288),(57,0),(58,265288),(73,265288),(74,265288),(86,265354),(96,0),(97,265288),(98,265288),(113,269380),(114,68872),(129,265288),(130,265288),(145,265288),(146,265288),(153,134410),(154,271492),(169,265288),(170,265288),(177,265288),(178,275848),(185,265288),(186,265288),(194,265288),(206,265288)]),([7,16,31,992,1057,2114,4228,8456,31744],[]),([7,31,992,1023,2114,4228,8456,16912],[(72,145762),(76,275848),(80,275848),(84,275848),(100,265288),(116,275848),(128,0),(140,140482),(148,145762),(216,0)]),([7,31,992,1057,2048,4228,16912],[(0,132298),(2,132298),(4,132298),(6,400590),(8,132298),(10,132298),(12,132298),(14,132298),(16,132298),(18,203842),(20,132298),(22,205954),(57,132298),(58,132298),(73,132298),(81,132298),(82,132266),(97,132298),(98,132298),(105,132298),(106,132298),(112,0),(113,132298),(114,132298),(129,132298),(145,132298),(146,132298),(152,0),(153,132298),(154,132298),(173,66760),(177,210312),(185,66760),(186,132298),(193,66760),(194,132298),(201,66760),(202,132298)]),([7,31,992,1057,2114,4228,8456],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,132298),(16,271492),(18,271492),(20,271492),(22,134410),(57,271492),(58,271492),(72,0),(73,271492),(74,271364),(81,271492),(105,271492),(113,271492),(114,271492),(128,0),(129,271492),(130,271428),(138,269444),(145,271492),(146,271492),(153,271492),(154,271492),(169,145762),(185,205954),(186,271492),(193,205954),(194,271492),(201,269380),(202,271492)]),([7,31,992,1057,2114,4228,8456,16912,31744],[(96,0),(168,0),(312,0)]),([7,31,992,1057,2114,4228,8456,16912,31777],[(72,0),(96,0),(112,0),(168,0),(312,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_115 : K_115.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_116 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,1057,2114,4228,8456,16912,32008],[(168,0),(312,0)]),([7,31,992,1057,2114,4228,8456,17392,31744],[(96,0),(168,0),(180,0),(312,0)]),([7,31,992,1057,2114,4228,8456,17969,31744],[(72,0),(96,0),(112,0),(168,0),(312,0)]),([7,31,992,1057,2114,4228,8456,21140,31744],[(96,0),(168,0),(312,0)]),([7,31,992,1057,2114,4228,8456,31744,32272],[(96,0)]),([7,31,992,1057,2114,4228,8456,32272],[(72,374786),(73,0),(96,0),(97,0),(98,0),(114,0),(128,374850),(176,407816),(180,72898),(182,0),(252,269380)]),([7,31,992,1057,2114,4228,9513],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,132298),(16,271492),(18,271492),(20,271492),(22,134410),(57,271492),(58,271492),(73,271492),(81,271492),(82,173188),(105,271492),(112,0),(113,271492),(114,271492),(128,0),(129,271492),(130,271428),(138,269444),(145,271492),(146,271492),(153,271492),(154,271492),(169,145762),(186,271492),(189,271492),(193,205954),(194,271492),(201,269380),(202,271492)]),([7,31,992,1057,2114,4228,10570],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,271492),(16,271492),(18,271492),(20,271492),(22,134410),(57,271492),(58,271492),(72,0),(73,271492),(74,271364),(81,271492),(98,271490),(105,271492),(106,205956),(112,0),(113,271492),(114,271492),(128,0),(129,271492),(130,271428),(138,269444),(145,271492),(146,271492),(153,271492),(154,271492),(185,275848),(186,271492),(194,271492),(197,271492),(201,269380),(202,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_116 : K_116.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_117 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,1057,2114,4228,12684],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,132298),(16,271492),(18,269380),(20,271492),(22,134410),(57,271492),(58,271492),(72,0),(73,271492),(74,271364),(81,271492),(105,271492),(113,271492),(114,271492),(129,271492),(145,271492),(146,271492),(153,271492),(154,271492),(169,145762),(181,68872),(185,68872),(186,271492),(193,205954),(194,271492),(202,271492),(205,271492)]),([7,31,992,1057,2114,4228,15855],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,271492),(16,271492),(18,269380),(20,271492),(22,134410),(57,271492),(58,271492),(73,271492),(81,271492),(82,173188),(98,271490),(105,271492),(106,205956),(113,271492),(114,271492),(129,271492),(145,271492),(146,271492),(153,271492),(154,271492),(181,68872),(186,271492),(189,271492),(194,271492),(197,271492),(202,271492),(205,271492)]),([7,31,992,1057,2114,4228,32008],[(0,271492),(2,271492),(4,271492),(6,271492),(8,271492),(10,271492),(12,271492),(14,271492),(16,271492),(18,271492),(20,271492),(22,205954),(57,271492),(58,271492),(61,271492),(73,271492),(74,271364),(77,271492),(81,271492),(97,271492),(101,271492),(105,271492),(113,271492),(114,271492),(129,271492),(130,271428),(133,271492),(137,271492),(138,269444),(145,271492),(146,271492),(153,271492),(154,271492),(169,361604),(173,271502),(181,400516),(186,271492),(194,271492),(202,271492),(205,269380)]),([7,31,992,1057,2114,4255,8456],[(0,271428),(2,271428),(4,271428),(6,400654),(8,271428),(10,271428),(12,271428),(14,66762),(16,271428),(18,271428),(20,271428),(22,68874),(57,271428),(58,271428),(61,271428),(72,0),(73,271428),(74,271364),(77,271428),(81,271428),(97,271428),(101,271428),(105,271428),(113,271428),(114,271428),(128,0),(129,271428),(130,271428),(133,271428),(138,269380),(145,271364),(146,271428),(154,271428),(169,205890),(173,80226),(185,205890),(186,271428),(193,205890),(194,271428),(201,269380)]),([7,31,992,1057,2114,5092,8456],[(0,269444),(2,361615),(4,269444),(6,269444),(8,269444),(10,269444),(12,269444),(14,132296),(16,269444),(18,269444),(20,269444),(22,134408),(57,269444),(58,269444),(72,0),(73,269444),(74,269316),(81,269444),(105,269444),(113,269444),(114,269444),(128,0),(129,269444),(130,269380),(138,269444),(141,269444),(146,269444),(154,269444),(169,145762),(177,203906),(185,203906),(186,269444),(193,203906),(194,269444),(201,269380)]),([7,31,992,1057,2114,5092,8456,16912,31744],[(96,0),(168,0),(180,0)]),([7,31,992,1057,2114,5285,8456],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,132298),(16,271492),(18,271492),(20,271492),(22,134410),(57,271492),(58,271492),(72,0),(73,271492),(74,271492),(81,271492),(86,271492),(105,271492),(113,271492),(114,271492),(128,0),(129,271492),(130,271428),(138,269444),(146,271492),(149,271492),(153,271492),(154,271492),(169,145762),(185,205954),(186,271492),(193,205954),(194,271492),(201,269380),(202,271492)]),([7,31,992,1057,2114,5285,8456,16912,31744],[(72,0),(96,0),(168,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_117 : K_117.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_118 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,1057,2114,5285,16912],[(0,134410),(2,361615),(4,134410),(6,400654),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,269380),(20,134410),(22,271492),(57,134410),(58,134410),(72,0),(73,134410),(74,134410),(81,134410),(86,134410),(98,132362),(105,134410),(106,134346),(112,0),(113,134410),(114,134410),(129,134410),(146,134410),(149,134410),(153,134410),(154,134410),(177,275848),(185,68872),(186,134410),(193,132298),(194,134410),(201,68872),(202,134410)]),([7,31,992,1057,2114,6342,8456],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,66760),(16,271492),(18,271492),(20,271492),(22,134410),(57,271492),(58,271492),(72,0),(73,271492),(74,271364),(81,271492),(105,271492),(113,271492),(114,271492),(130,271428),(138,269444),(145,271492),(146,271492),(154,271492),(157,271492),(169,145762),(185,203842),(186,271492),(193,203842),(194,271492),(201,269380),(202,271492)]),([7,31,992,1057,2114,6342,16912],[(0,134410),(2,361615),(4,134410),(6,400654),(8,134410),(10,134410),(12,134410),(14,66760),(16,134410),(18,269380),(20,134410),(22,271492),(57,134410),(58,134410),(73,134410),(81,134410),(82,134314),(105,134410),(113,134410),(114,134410),(145,134410),(146,134410),(154,134410),(157,134410),(177,275848),(185,68872),(186,134410),(192,0),(193,203842),(194,134410),(201,68872),(202,134410)]),([7,31,992,1057,2114,8456,12684],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,132298),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(72,0),(73,269380),(74,269380),(81,269380),(105,269380),(113,269380),(114,269380),(129,145762),(145,205954),(146,269380),(153,205954),(154,269380),(168,0),(169,145762),(170,269380),(178,269380),(181,269380),(185,269380),(186,269380),(193,205954),(194,269380),(202,269380),(205,269380)]),([7,31,992,1057,2114,8456,15855],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(72,0),(73,269380),(74,269316),(81,269380),(86,269316),(105,269380),(113,269380),(114,269380),(129,145762),(145,203842),(146,269380),(153,203842),(154,269380),(170,269380),(178,269380),(181,269380),(186,269380),(189,269380),(194,269380),(197,269380),(202,269380),(205,269380)]),([7,31,992,1057,2114,8456,16384],[(0,269380),(2,269380),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(72,0),(73,269380),(74,269316),(81,269380),(86,269316),(101,269380),(105,269380),(113,269380),(114,269380),(129,203842),(145,203842),(146,269380),(153,203842),(154,269380),(169,269380),(170,269380),(177,275848),(178,269380),(185,269380),(186,269380),(193,203842),(194,269380),(201,269380),(202,203842)]),([7,31,992,1057,2114,8456,16912],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(72,0),(73,269380),(74,269316),(81,269380),(86,269316),(105,269380),(113,269380),(114,269380),(129,145762),(145,203842),(146,269380),(153,203842),(154,269380),(170,269380),(177,275848),(178,269380),(185,269380),(186,269380),(193,203842),(194,269380),(201,269380),(202,271492)]),([7,31,992,1057,2114,8456,16912,31876],[(72,0),(76,361615),(96,132495),(100,265288),(176,271758),(260,269380)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_118 : K_118.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_119 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,1057,2114,8456,16927],[(0,269380),(2,269380),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(72,0),(73,269380),(74,269316),(81,269380),(86,269316),(97,269380),(105,269380),(113,269380),(114,269380),(129,203842),(145,203842),(146,269380),(153,203842),(154,269380),(170,269380),(173,269380),(177,275848),(178,269380),(185,269316),(186,269380),(194,269380),(202,271428)]),([7,31,992,1057,2114,8456,17392],[(0,269380),(2,361615),(4,269380),(6,269380),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(62,275848),(72,0),(73,269380),(74,269316),(81,269380),(84,0),(85,275848),(86,269316),(105,269380),(109,275848),(113,269380),(114,269380),(129,145762),(137,275855),(141,203842),(145,203842),(146,269380),(153,203842),(154,269380),(170,269380),(177,269380),(178,269380),(181,269380),(186,269380),(189,269316),(194,269380),(202,269444)]),([7,31,992,1057,2114,8456,17969],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(72,0),(73,269380),(74,269380),(81,269380),(105,269380),(113,269380),(114,269380),(129,145762),(145,203842),(146,269380),(153,203842),(154,269380),(170,269380),(177,275848),(178,269380),(186,269380),(189,269380),(193,203842),(194,269380),(201,269380),(202,271492)]),([7,31,992,1057,2114,8456,19026],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,132298),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(72,0),(73,269380),(74,269316),(81,269380),(86,269316),(105,269380),(113,269380),(114,269380),(129,145762),(145,205954),(146,269380),(153,205954),(154,269380),(170,269380),(173,269380),(177,275848),(178,269380),(185,269380),(186,269380),(194,269380),(197,269380),(201,269380),(202,271492)]),([7,31,992,1057,2114,8456,25368],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,66760),(16,271492),(18,134410),(20,271492),(22,271492),(57,271492),(58,271492),(72,0),(73,271492),(74,271492),(81,271492),(86,271492),(105,271492),(113,271492),(114,271492),(129,145762),(145,203842),(146,271492),(153,203842),(154,271492),(170,271428),(178,269444),(185,271492),(186,271492),(193,203842),(194,271492),(202,271492),(205,271492)]),([7,31,992,1057,2114,8456,28539],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,132298),(16,271492),(18,134410),(20,271492),(22,271492),(57,271492),(58,271492),(72,0),(73,271492),(74,271364),(81,271492),(105,271492),(113,271492),(114,271492),(129,145762),(145,205954),(146,271492),(153,205954),(154,271492),(170,271428),(173,271492),(178,269444),(186,271492),(189,271492),(194,271492),(197,271492),(202,271492),(205,271492)]),([7,31,992,1057,2114,9513,16912],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(73,269380),(81,269380),(82,171076),(105,269380),(113,269380),(114,269380),(129,145762),(146,269380),(149,269380),(153,203842),(154,269380),(170,269380),(177,275848),(178,269380),(185,269380),(186,269380),(193,203842),(194,269380),(201,269380),(202,271492)]),([7,31,992,1057,2114,10570,16912],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,269380),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(72,0),(73,269380),(74,269316),(81,269380),(86,269316),(98,269378),(105,269380),(106,203844),(113,269380),(114,269380),(145,275848),(146,269380),(154,269380),(157,269380),(170,269380),(177,275848),(178,269380),(185,269380),(186,269380),(193,269380),(194,269380),(201,269380),(202,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_119 : K_119.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_120 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,1057,2114,16912,21140],[(0,68872),(2,361615),(4,68872),(6,400654),(8,68872),(10,68872),(12,68872),(14,68872),(16,68872),(18,68872),(20,68872),(22,269380),(57,68872),(58,68872),(73,68872),(81,68872),(82,68776),(98,66824),(105,68872),(106,68808),(113,68872),(114,68872),(130,68872),(137,68872),(138,68872),(145,68872),(146,68872),(152,0),(153,68872),(154,68872),(185,275848),(186,68872),(193,66760),(194,68872),(202,68872),(205,68872)]),([7,31,992,1057,2114,16912,24311],[(0,68872),(2,361615),(4,68872),(6,400654),(8,68872),(10,68872),(12,68872),(14,66760),(16,68872),(18,68872),(20,68872),(22,269380),(57,68872),(58,68872),(72,0),(73,68872),(74,3336),(81,68872),(86,3336),(105,68872),(113,68872),(114,68872),(130,68872),(137,68872),(138,68872),(145,68872),(146,68872),(153,68872),(154,68872),(173,396552),(186,68872),(189,68872),(194,68872),(197,68872),(202,68872),(205,68872)]),([7,31,992,1057,2114,16912,25368],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,269380),(20,269380),(22,134410),(57,269380),(58,269380),(72,0),(73,269380),(74,269316),(81,269380),(86,269316),(105,269380),(113,269380),(114,269380),(137,269380),(145,269380),(146,269380),(152,0),(153,269380),(154,269380),(185,134410),(186,269380),(193,203842),(194,269380),(202,269380),(205,269380)]),([7,31,992,1057,2114,16912,28539],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,269380),(16,269380),(18,269380),(20,269380),(22,134410),(57,269380),(58,269380),(73,269380),(81,269380),(82,171076),(98,269378),(105,269380),(106,203844),(113,269380),(114,269380),(137,269380),(145,269380),(146,269380),(153,269380),(154,269380),(173,269390),(186,269380),(189,269380),(194,269380),(197,269380),(202,269380),(205,269380)]),([7,31,992,1057,3171,8456,16912],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(73,269380),(78,269380),(81,269380),(82,269380),(105,269380),(114,269380),(117,269380),(129,145762),(145,203842),(146,269380),(153,203842),(154,269380),(170,269380),(177,275848),(178,269380),(185,269380),(186,269380),(193,203842),(194,269380),(201,269380),(202,271492)]),([7,31,992,1057,8456,10570,16912],[(0,203842),(2,361615),(4,203842),(6,400654),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,66760),(20,203842),(22,203842),(57,203842),(58,203842),(72,0),(73,203842),(74,203778),(81,203842),(86,203778),(96,0),(97,203842),(98,203842),(106,203842),(112,0),(113,203842),(114,203842),(145,275848),(146,203842),(154,203842),(157,203842),(170,203842),(177,275848),(178,203842),(185,203842),(186,203842),(193,203842),(194,203842),(201,203842),(202,205954)]),([7,31,992,1057,8456,12684,16912],[(0,132298),(2,361615),(4,132298),(6,400654),(8,132298),(10,132298),(12,132298),(14,68872),(16,132298),(18,203842),(20,132298),(22,205954),(57,132298),(58,132298),(73,132298),(78,132266),(81,132298),(82,132266),(97,132298),(112,0),(113,132298),(114,132298),(129,132298),(141,132298),(145,132298),(146,132298),(154,132298),(157,132298),(177,275848),(185,66760),(186,132298),(193,269380),(194,132298),(201,66760),(202,132298)]),([7,31,992,1057,8456,16912,28539],[(0,203842),(2,361615),(4,203842),(6,400654),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,203842),(20,203842),(22,132298),(57,203842),(58,203842),(73,203842),(78,171074),(81,203842),(82,171074),(96,0),(97,203842),(98,203842),(106,203842),(113,203842),(114,203842),(137,203842),(145,203842),(146,203842),(153,203842),(154,203842),(173,132298),(186,203842),(189,203842),(194,203842),(197,203842),(202,203842),(205,203842)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_120 : K_120.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_121 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,1057,8456,16912,31810],[(0,203842),(2,203842),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,203842),(20,203842),(22,269380),(57,203842),(58,203842),(62,203842),(73,203842),(74,203778),(81,203842),(84,0),(85,203842),(86,203778),(97,203842),(105,203842),(109,203842),(113,203842),(114,203842),(128,0),(129,203842),(130,203842),(137,203842),(138,203842),(141,203842),(145,203842),(146,203842),(153,203842),(154,203842),(173,203919),(177,204046),(181,367682),(185,269380),(186,203842),(194,203842),(202,203842),(205,203842)]),([7,31,992,1087,2114,4228,8456],[(0,271364),(2,271364),(4,271364),(6,400654),(8,271364),(10,271364),(12,271364),(14,1226),(16,271364),(18,271364),(20,271364),(22,3338),(57,271364),(58,271364),(61,271364),(72,0),(73,271364),(74,271364),(77,271364),(81,271364),(97,271364),(101,271364),(105,271364),(113,271364),(128,0),(129,271364),(130,271364),(133,271364),(138,269316),(145,271364),(146,271364),(153,271364),(154,271364),(169,205826),(173,205826),(185,205826),(193,205826),(194,271364),(201,269380),(202,271364)]),([7,31,992,1087,2114,8456,16912],[(0,269316),(2,269316),(4,269316),(6,400654),(8,269316),(10,269316),(12,269316),(14,1224),(16,269316),(18,3336),(20,269316),(22,269316),(57,269316),(58,269316),(61,269316),(72,0),(73,269316),(74,269316),(77,269316),(81,269316),(86,269316),(97,269316),(101,269316),(105,269316),(113,269316),(129,203778),(133,269710),(145,203778),(153,203778),(154,269316),(168,0),(169,269316),(170,269316),(173,269316),(177,275848),(178,269316),(185,269316),(186,269316),(193,203778),(194,269316),(201,269316),(202,271492)]),([7,31,992,2114,3171,4228,8456],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,271492),(16,271492),(18,271492),(20,271492),(22,134410),(57,271492),(58,271492),(78,271492),(81,271492),(82,271492),(98,271364),(105,271492),(114,271492),(117,271492),(128,0),(129,271492),(130,271428),(138,269444),(145,271492),(146,271492),(153,271492),(154,271492),(169,145762),(184,0),(185,275848),(186,271492),(193,275848),(194,271492),(201,269380),(202,271492)]),([7,31,992,2114,3171,4228,16912],[(0,134410),(2,361615),(4,134410),(6,400654),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,269380),(20,134410),(22,271492),(57,134410),(58,134410),(78,134410),(81,134410),(82,134410),(105,134410),(106,134314),(114,134410),(117,134410),(129,134410),(145,134410),(146,134410),(153,134410),(154,134410),(177,275848),(184,0),(185,68872),(186,134410),(193,68872),(194,134410),(201,68872),(202,134410)]),([7,31,992,2114,3171,8456,16912],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,269380),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(78,269380),(81,269380),(82,269380),(98,269316),(105,269380),(110,269316),(114,269380),(117,269380),(129,145762),(145,275848),(146,269380),(153,275848),(154,269380),(170,269380),(177,275848),(178,269380),(185,269380),(186,269380),(193,269380),(194,269380),(201,269380),(202,271492)]),([7,31,992,2114,4228,8456,9513],[(0,205954),(2,361615),(4,205954),(6,400654),(8,205954),(10,132298),(12,205954),(14,205954),(16,205954),(18,205954),(20,205954),(22,205954),(57,205954),(58,205954),(81,275848),(96,0),(97,145762),(98,205890),(106,203906),(113,205954),(114,203842),(129,145762),(138,205954),(144,0),(145,205954),(146,275848),(153,205954),(154,205954),(168,0),(169,145762),(170,205826),(185,205954),(186,275848),(193,205954),(194,205954),(202,205954),(205,205954)]),([7,31,992,2114,4228,8456,15855],[(0,275848),(2,361615),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(57,145762),(58,275848),(78,275848),(81,275848),(82,145762),(96,0),(97,145762),(98,275848),(110,145762),(113,66760),(114,203842),(129,145762),(138,145762),(145,275848),(146,275848),(153,269380),(154,68872),(170,275848),(181,275848),(186,275848),(189,275848),(194,275848),(197,275848),(202,275848),(205,275848)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_121 : K_121.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_122 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,2114,4228,8456,15855,31744],[(76,265288),(96,0),(108,140482),(168,197704),(232,0)]),([7,31,992,2114,4228,8456,16912],[(0,275848),(2,361615),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(57,145762),(58,275848),(78,275848),(81,275848),(82,145762),(96,0),(97,145762),(98,275848),(110,145762),(113,66760),(114,203842),(129,145762),(138,145762),(145,275848),(146,275848),(153,269380),(154,68872),(170,275848),(177,275848),(185,132298),(186,205954),(193,275848),(194,275848),(201,134410),(202,271492)]),([7,31,992,2114,4228,8456,16912,31744],[(76,265288),(96,0),(108,140482),(168,0),(232,0)]),([7,31,992,2114,4228,8456,16912,31777],[(72,132431),(76,265288),(84,1294),(96,0),(100,171151),(104,269646),(108,140482)]),([7,31,992,2114,4228,8456,16912,31810],[(76,265288),(84,400386),(96,0),(108,140482),(112,203842),(168,0),(232,0),(236,275848),(240,203842)]),([7,31,992,2114,4228,8456,16912,32008],[(76,265288),(80,275458),(96,275464),(128,0),(168,275466),(200,271492),(232,0),(240,269380),(252,275848)]),([7,31,992,2114,4228,8456,16927],[(0,275848),(2,275848),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(57,0),(58,275848),(73,275848),(78,275848),(81,275848),(82,0),(96,0),(97,275848),(98,275848),(110,0),(113,66760),(114,203842),(129,275848),(145,275848),(146,275848),(153,269380),(154,68872),(170,275848),(173,275848),(177,275848),(186,205826),(189,275848),(193,275848),(194,275848),(202,271364)]),([7,31,992,2114,4228,8456,16927,31744],[(96,0),(108,0),(168,0),(232,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_122 : K_122.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_123 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,2114,4228,8456,19026],[(0,205954),(2,361615),(4,205954),(6,400654),(8,205954),(10,132298),(12,205954),(14,205954),(16,205954),(18,205954),(20,205954),(22,205954),(57,205954),(58,205954),(81,275848),(96,0),(97,145762),(98,205954),(110,205954),(113,205954),(114,275848),(129,145762),(138,205954),(144,0),(145,205954),(146,275848),(153,269380),(154,68872),(170,205826),(173,205954),(177,275848),(186,205954),(189,205954),(193,205954),(194,205954),(201,134410),(202,271492)]),([7,31,992,2114,4228,8456,21140],[(0,275848),(2,361615),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(57,145762),(58,275848),(78,275848),(81,275848),(82,145762),(96,0),(97,145762),(98,275848),(106,145762),(113,275848),(114,275848),(129,145762),(138,145762),(145,275848),(146,275848),(153,275848),(154,275848),(170,275848),(185,132298),(186,205954),(194,275848),(197,275848),(201,134410),(202,271492)]),([7,31,992,2114,4228,8456,21140,31744],[(76,265288),(96,0),(112,66730),(152,68778),(168,0),(232,0),(244,80226)]),([7,31,992,2114,4228,8456,25368],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,271492),(16,271492),(18,134410),(20,271492),(22,271492),(57,271492),(58,271492),(78,271492),(81,271492),(82,271492),(96,0),(97,271492),(98,271492),(110,271492),(113,271492),(114,271492),(129,145762),(144,0),(145,275848),(146,271492),(153,275848),(154,271492),(170,271364),(185,132298),(186,271492),(193,271492),(194,271492),(202,271492),(205,271492)]),([7,31,992,2114,4228,8456,31710],[(0,271492),(2,361615),(4,271492),(6,400654),(8,271492),(10,132298),(12,271492),(14,271492),(16,271492),(18,134410),(20,271492),(22,271492),(57,271492),(58,271492),(81,271492),(96,0),(97,271492),(98,271428),(106,269444),(113,271492),(114,271492),(129,145762),(145,205954),(146,271492),(153,269380),(154,271492),(170,271364),(173,271492),(181,271492),(186,271492),(189,271492),(194,271492),(197,271492),(202,271492),(205,271492)]),([7,31,992,2114,4255,8456,16912],[(0,275848),(2,275848),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(57,0),(58,275848),(61,145576),(73,275848),(77,145576),(78,275848),(81,275848),(96,0),(97,275464),(98,275848),(101,275848),(110,145762),(114,203778),(117,275848),(129,275848),(133,145576),(145,275848),(146,275848),(153,269316),(168,0),(169,145576),(170,275848),(173,275464),(177,275848),(185,132298),(186,205954),(193,275848),(194,275848),(201,134410),(202,271492)]),([7,31,992,2114,4255,8456,16912,31744],[(96,0),(108,140482),(168,0),(216,145576),(220,145576),(232,0),(240,145762)]),([7,31,992,2114,6342,8456,16912],[(0,203842),(2,361615),(4,203842),(6,400654),(8,203842),(10,66760),(12,203842),(14,203842),(16,203842),(18,203842),(20,203842),(22,203842),(57,203842),(58,203842),(81,275848),(98,203778),(110,203778),(114,203842),(117,203842),(129,145762),(138,203842),(144,0),(145,203842),(146,275848),(153,269380),(154,68872),(170,203842),(177,275848),(185,203842),(186,275848),(193,203842),(194,203842),(201,134410),(202,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_123 : K_123.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_124 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,2114,8456,9513,16912],[(0,203842),(2,361615),(4,203842),(6,400654),(8,203842),(10,66760),(12,203842),(14,203842),(16,203842),(18,203842),(20,203842),(22,203842),(57,203842),(58,203842),(81,275848),(97,145762),(106,203842),(112,0),(113,203842),(114,275848),(128,0),(129,145762),(130,203778),(142,203778),(145,203842),(146,275848),(154,203842),(157,203842),(170,203842),(177,275848),(178,203842),(185,203842),(186,205954),(193,203842),(194,203842),(201,203842),(202,203842)]),([7,31,992,2114,8456,12684,16912],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,68872),(16,269380),(18,269380),(20,269380),(22,269380),(57,269380),(58,269380),(78,269380),(81,269380),(82,269380),(97,145762),(112,0),(113,275848),(114,269380),(128,0),(129,145762),(130,269316),(140,0),(141,269380),(142,269316),(145,66760),(146,269380),(154,269380),(157,269380),(170,269380),(177,275848),(185,132298),(186,269380),(193,269380),(194,275848),(201,269380),(202,269380)]),([7,31,992,2114,8456,16912,17969],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,66760),(12,269380),(14,68872),(16,269380),(18,269380),(20,269380),(22,269380),(57,269380),(58,269380),(81,269380),(97,145762),(113,203842),(114,269380),(130,269380),(137,275848),(145,203842),(146,269380),(153,269380),(154,203842),(170,269316),(177,275848),(182,269316),(185,203842),(186,269380),(193,269380),(194,203842),(202,269380),(205,269380)]),([7,31,992,2114,8456,16912,21140],[(0,275848),(2,361615),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(57,145762),(58,275848),(78,275848),(81,275848),(82,145762),(97,145762),(106,145762),(113,275848),(114,275848),(130,275848),(137,275848),(138,145762),(145,275848),(146,275848),(153,275848),(154,275848),(170,275848),(182,145762),(185,66760),(186,203842),(193,68872),(194,269380),(202,275848),(205,275848)]),([7,31,992,2114,8456,16912,21140,31744],[(76,265288),(128,0),(144,132264),(152,134312),(168,0),(180,0),(232,0),(252,275848)]),([7,31,992,2114,8456,16912,28539],[(0,275848),(2,361615),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(57,145762),(58,275848),(78,275848),(81,275848),(82,145762),(97,145762),(106,145762),(113,275848),(114,275848),(130,275848),(137,275848),(145,132298),(146,205954),(153,134410),(154,271492),(170,275848),(173,275528),(182,145762),(186,275848),(189,275848),(194,275848),(197,275848),(202,275848),(205,275848)]),([7,31,992,2114,8456,16912,28539,31744],[(76,265288),(128,0),(168,361615),(180,0),(256,145762)]),([7,31,992,2114,8456,16912,31710],[(0,269380),(2,361615),(4,269380),(6,400654),(8,269380),(10,66760),(12,269380),(14,68872),(16,269380),(18,269380),(20,269380),(22,269380),(57,269380),(58,269380),(81,269380),(97,145762),(113,203842),(114,269380),(130,269380),(137,275848),(138,269380),(145,203842),(146,269380),(153,269380),(154,271492),(170,269316),(173,269380),(180,0),(181,269380),(182,269316),(186,269380),(189,269380),(194,269380),(197,269380),(202,269380),(205,269380)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_124 : K_124.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_125 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,992,2114,8456,16912,31744,31876],[(76,265288),(128,0),(168,361615),(172,361615),(216,361615),(228,140482)]),([7,31,992,2114,8456,16912,31777],[(0,269380),(2,269380),(4,269380),(6,269380),(8,269380),(10,66760),(12,269380),(14,68872),(16,269380),(18,269380),(20,269380),(22,269380),(57,269380),(58,269380),(61,171151),(62,171278),(73,269380),(77,171151),(81,269380),(85,171278),(97,203842),(101,171151),(105,171278),(109,203842),(113,203842),(114,269380),(129,171151),(130,269380),(133,269326),(137,269380),(138,269380),(141,171278),(145,203842),(146,269380),(153,269380),(154,271492),(169,361615),(170,269316),(173,171151),(177,171278),(181,335118),(182,269316),(185,203842),(186,269380),(194,203842),(202,269380),(205,269380)]),([7,31,992,2114,8456,16912,31876],[(2,0),(10,0),(57,197704),(58,72898),(61,361615),(73,361640),(77,265288),(97,265544),(101,361615),(129,0),(133,361640),(145,132298),(146,205954),(153,134410),(154,271492),(169,361615),(170,145762),(173,361615),(181,140482),(182,145762),(185,66760),(186,203842),(194,269380)]),([7,31,1023,1057,2114,4228,8456],[(0,271492),(2,197704),(4,271492),(6,400654),(8,271492),(10,271492),(12,271492),(14,132298),(16,271492),(18,271492),(20,271492),(22,134410),(58,271492),(61,271492),(73,271492),(74,271364),(81,271492),(105,271492),(113,271492),(114,271492),(130,271428),(138,269380),(145,271492),(146,271492),(153,271492),(154,271492),(182,205954),(185,205954),(186,271492),(193,205954),(194,271492),(201,269380),(202,271492)]),([7,31,1023,1057,2114,4228,16912],[(0,134410),(2,197704),(4,134410),(6,400654),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,269380),(20,134410),(22,271492),(58,134410),(61,134410),(73,134410),(81,134410),(98,132362),(105,134410),(106,132298),(113,134410),(114,134410),(145,134410),(146,134410),(153,134410),(154,134410),(177,275848),(182,68872),(185,68872),(186,134410),(193,132298),(194,134410),(201,68872),(202,134410)]),([7,31,1023,1057,2114,8456,16912],[(0,269380),(2,197704),(4,269380),(6,400654),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(58,269380),(61,269380),(73,269380),(74,269316),(81,269380),(86,269380),(105,269380),(110,269380),(113,269380),(114,269380),(145,203842),(146,269380),(153,203842),(154,269380),(170,269380),(177,275848),(178,269380),(185,269380),(186,269380),(193,203842),(194,269380),(201,269380),(202,271492)]),([7,31,1023,1057,4228,8456,16912],[(0,132298),(2,197704),(4,132298),(6,400654),(8,132298),(10,132298),(12,132298),(14,203842),(16,132298),(18,132298),(20,132298),(22,205954),(58,132298),(61,132298),(73,132298),(78,132266),(81,132298),(86,132298),(110,132298),(113,132298),(114,132298),(130,132298),(138,132298),(145,132298),(146,132298),(153,132298),(154,132298),(177,275848),(185,66760),(186,132298),(193,66760),(194,132298),(201,134410),(202,132298)]),([7,31,1023,2114,4228,8456,16912],[(0,275848),(2,197704),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(58,275848),(61,275848),(78,275848),(81,275848),(86,275848),(98,275848),(110,72898),(113,66760),(114,203842),(145,275848),(146,275848),(153,269380),(154,68872),(170,275848),(177,275848),(185,132298),(186,205954),(193,275848),(194,275848),(201,134410),(202,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_125 : K_125.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_126 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,2017,2114,4228,8456],[(0,271492),(2,361615),(4,271492),(6,271492),(8,271492),(10,400654),(12,271492),(14,132298),(16,271492),(18,271492),(20,271492),(22,134410),(57,271492),(58,271492),(73,271492),(74,271492),(82,271492),(85,271492),(105,271492),(106,271492),(113,271492),(128,0),(129,271492),(130,271428),(137,271492),(138,271492),(146,269444),(153,271492),(154,271492),(169,145762),(177,205954),(178,271492),(193,205954),(194,271492),(201,269380),(202,271492)]),([7,31,1057,2017,2114,4228,8456,16912,31744],[(96,0),(168,0)]),([7,31,1057,2017,2114,4228,16912],[(0,134410),(2,361615),(4,134410),(6,134410),(8,134410),(10,400654),(12,134410),(14,134410),(16,134410),(18,269380),(20,134410),(22,271492),(56,0),(57,134410),(58,134410),(62,134314),(73,134410),(74,134410),(81,134314),(82,134410),(85,134410),(98,132362),(105,134410),(106,134410),(109,134314),(113,134410),(114,134346),(129,134410),(137,134410),(138,134410),(141,134314),(153,134410),(154,134410),(177,68872),(178,134410),(181,134314),(185,275848),(193,132298),(194,134410),(201,68872),(202,134410)]),([7,31,1057,2017,2114,8456,16912],[(0,269380),(2,361615),(4,269380),(6,269380),(8,269380),(10,400654),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269380),(73,269380),(74,269380),(82,269380),(85,269380),(105,269380),(106,269380),(113,269380),(129,145762),(137,203842),(138,269380),(153,203842),(154,269380),(170,269380),(177,269380),(178,269380),(185,275848),(186,269380),(193,203842),(194,269380),(201,269380),(202,271492)]),([7,31,1057,2017,4228,8456,16912],[(0,132298),(2,361615),(4,132298),(6,132298),(8,132298),(10,400654),(12,132298),(14,203842),(16,132298),(18,132298),(20,132298),(22,205954),(56,0),(57,132298),(58,132298),(62,132266),(73,132298),(74,132298),(81,132266),(82,132298),(85,132298),(97,132298),(105,132298),(106,132298),(109,132266),(128,0),(129,132298),(130,132298),(137,132298),(138,132298),(141,132266),(146,132298),(153,132298),(154,132298),(177,66760),(178,132298),(181,132266),(185,275848),(193,66760),(194,132298),(201,134410),(202,132298)]),([7,31,1057,2048,4228,16912,31744],[(0,400590),(2,197704),(4,400590),(6,400590),(8,400590),(10,400590),(12,400590),(14,400590),(16,400590),(18,400590),(20,400590),(22,132298),(57,400590),(73,400590),(74,400590),(81,400590),(82,400590),(105,400590),(106,400590),(113,400590),(114,400590),(137,400590),(138,400590),(145,400590),(146,400590),(153,400590),(154,400590),(169,72898),(170,400590),(178,400590),(186,400590),(189,400590),(201,132298),(202,400590)]),([7,31,1057,2114,3042,4228,8456],[(0,271492),(2,197775),(4,271492),(6,271492),(8,271492),(10,271492),(12,271492),(14,400654),(16,271492),(18,271492),(20,271492),(22,134410),(57,271492),(58,271364),(74,271492),(81,271492),(82,271492),(98,271492),(106,271492),(114,271492),(117,271492),(129,271492),(130,271428),(137,271492),(138,271492),(145,271492),(146,271492),(154,269444),(169,145602),(177,275848),(178,271492),(185,275848),(186,271492),(201,269380),(202,271492)]),([7,31,1057,2114,3042,4228,16912],[(0,134410),(2,197775),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,400654),(16,134410),(18,269380),(20,134410),(22,271492),(57,134410),(74,134410),(78,134346),(81,134410),(82,134410),(86,134346),(98,134410),(105,134314),(106,134410),(113,134346),(114,134410),(117,134410),(129,134410),(137,134410),(138,134410),(145,134410),(146,134410),(149,134346),(177,68872),(178,134410),(185,68872),(186,134410),(189,134346),(193,275848),(201,68872),(202,134410)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_126 : K_126.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_127 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,2114,3042,8456,16912],[(0,269380),(2,197775),(4,269380),(6,269380),(8,269380),(10,269380),(12,269380),(14,400654),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269316),(74,269380),(81,269380),(82,269380),(98,269380),(106,269380),(109,269316),(114,269380),(117,269380),(129,145602),(137,275848),(138,269380),(145,275848),(146,269380),(170,269380),(177,269380),(178,269380),(185,269380),(186,269380),(193,275848),(194,269380),(201,269380),(202,271492)]),([7,31,1057,2114,4096,8456,31744],[(0,269380),(2,197704),(4,269380),(6,269380),(8,269380),(10,66760),(12,269380),(14,269380),(16,269380),(18,68872),(20,269380),(22,269380),(57,269380),(58,269316),(81,269380),(82,269380),(97,269380),(98,269380),(105,269380),(106,269380),(113,269380),(114,269380),(137,203842),(138,269380),(145,203842),(146,269380),(153,203842),(154,269380),(169,72898),(170,269380),(178,269380),(186,269380),(194,269380),(197,269380),(201,269380),(206,269380)]),([7,31,1057,2114,4228,5092,8456,16912,31744],[(72,0),(168,0)]),([7,31,1057,2114,4228,8456,16912,17392,31744],[(72,0),(128,0)]),([7,31,1057,2114,4228,8456,17392],[(0,275848),(2,361610),(4,275848),(6,275848),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,400654),(57,275848),(58,275848),(74,132488),(81,275848),(82,275848),(97,275528),(98,275848),(102,275848),(105,275848),(106,275848),(110,275848),(113,275848),(114,275848),(118,275848),(129,265608),(130,134536),(137,275848),(138,275848),(145,275848),(146,275848),(153,275848),(154,275848),(157,275848),(170,275848),(178,275848),(181,275786),(186,275848),(189,132458),(193,138594),(197,275850),(205,134536)]),([7,31,1057,2114,4228,8456,17392,31744],[(56,271364),(72,0),(205,0),(240,271758),(244,269380)]),([7,31,1057,2114,4228,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(186,400654),(197,269380),(201,271492)]),([7,31,1057,2114,4228,8456,31775],[(0,400654),(2,361615),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(81,400654),(82,400654),(97,72974),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,400644),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(173,400654),(178,400654),(186,400654),(197,269444)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_127 : K_127.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_128 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,2114,4228,8456,31777],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(181,400654),(186,400654),(197,269380),(201,271492)]),([7,31,1057,2114,4228,8456,31810],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(74,400514),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(178,400654),(186,400654),(189,400654),(197,269380),(201,271492)]),([7,31,1057,2114,4228,8456,32272],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(57,400654),(58,400654),(74,132366),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,134414),(134,400650),(137,400654),(138,400654),(142,134410),(145,400654),(146,400654),(150,134410),(153,400654),(154,400654),(158,134410),(170,400654),(178,400654),(181,400554),(186,400654),(189,132298),(197,269380),(201,134410),(205,134410)]),([7,31,1057,2114,4228,9192,16912,31744],[(256,407816)]),([7,31,1057,2114,4228,9513,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(186,400654),(197,269380),(201,271492)]),([7,31,1057,2114,4228,10570,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(74,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(146,400654),(149,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(186,400654),(189,400590),(197,269380),(201,271492)]),([7,31,1057,2114,4228,12684,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(186,400654),(201,271492),(206,271492)]),([7,31,1057,2114,4228,15855,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(186,400654),(189,400590),(201,271492),(206,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_128 : K_128.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_129 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,2114,4228,16912,17392],[(0,275848),(2,361610),(4,275848),(6,275848),(8,275848),(10,275848),(12,275848),(14,269380),(16,275848),(18,275848),(20,275848),(22,400654),(57,275848),(74,275848),(81,275848),(82,275848),(97,275528),(105,275848),(106,275848),(113,275848),(114,275848),(130,134536),(137,275848),(138,275848),(145,275848),(146,275848),(153,68872),(154,275848),(170,275848),(177,68776),(178,275848),(185,68808),(186,275848),(202,275848),(205,275848)]),([7,31,1057,2114,4228,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(186,400654),(189,400590),(201,134410),(202,400654)]),([7,31,1057,2114,4228,16912,31775],[(0,400654),(2,361615),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(74,400654),(81,400654),(82,400654),(97,72974),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(173,400654),(178,400654),(181,400558),(186,400654),(189,400590),(202,400654)]),([7,31,1057,2114,4228,16912,31777],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(58,3342),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(181,400654),(186,400654),(189,400590),(201,134410),(202,400654)]),([7,31,1057,2114,4228,16912,31810],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(178,400654),(186,400654),(189,400654),(201,134410),(202,400654)]),([7,31,1057,2114,4228,16912,32272],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,68872),(57,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,134414),(134,400650),(137,400654),(138,400654),(142,134410),(145,400654),(146,400654),(150,134410),(153,400654),(154,400654),(158,134410),(170,400654),(178,400654),(186,400654),(189,400590),(201,68872),(202,400654),(205,400654)]),([7,31,1057,2114,4228,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(58,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(186,400654),(189,400590),(201,134410),(202,400654)]),([7,31,1057,2114,4228,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(146,400654),(149,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(186,400654),(201,134410),(202,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_129 : K_129.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_130 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,2114,4228,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(74,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(186,400654),(189,400590),(197,68872),(201,134410)]),([7,31,1057,2114,4228,24311,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(186,400654),(197,68872),(201,134410)]),([7,31,1057,2114,4228,31744,32008],[(0,271492),(2,197704),(4,271492),(6,271492),(8,271492),(10,271492),(12,271492),(14,271492),(16,271492),(18,271492),(20,271492),(22,205954),(57,271492),(58,271364),(81,271492),(82,271492),(98,271428),(105,271492),(106,271492),(113,271492),(114,271492),(129,271492),(130,271492),(138,271492),(146,271492),(154,271492),(157,269380),(178,271492),(186,271492),(194,271492),(197,269380),(202,271492),(205,271492)]),([7,31,1057,2114,4228,31744,32272],[(0,134410),(2,197704),(4,134410),(6,134410),(8,134410),(10,134410),(12,134410),(14,134410),(16,134410),(18,134410),(20,134410),(22,68872),(57,134410),(74,132362),(81,134410),(82,134410),(105,134410),(106,134410),(113,134410),(114,134410),(129,134410),(130,134410),(134,134410),(138,134410),(142,134410),(146,134410),(149,132298),(150,134410),(154,134410),(158,134410),(178,134410),(186,134410),(189,132298),(194,134410),(201,68872),(202,134410),(205,134410)]),([7,31,1057,2114,4228,32272],[(1,134410),(2,0),(3,134410),(5,134410),(7,134410),(9,134410),(11,134410),(13,134410),(15,134410),(17,68872),(19,68872),(59,134410),(63,134410),(75,134410),(79,134410),(83,134410),(87,134410),(99,134410),(103,134410),(107,134410),(111,134410),(115,134410),(119,134410),(131,68872),(135,400650),(139,68872),(143,134410),(147,68872),(151,134410),(155,72898),(159,134410)]),([7,31,1057,2114,4255,8456,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271428),(57,400654),(58,400654),(73,400654),(81,400654),(82,400654),(98,400654),(101,400654),(105,400654),(106,400654),(114,400654),(129,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(169,271428),(170,400654),(178,400654),(186,400654),(197,269380),(201,271428)]),([7,31,1057,2114,5092,8456,16912,31744],[(56,269316),(108,335118),(158,0),(224,269646),(232,269678)]),([7,31,1057,2114,5092,8456,31744],[(0,269444),(2,269444),(4,269444),(6,269444),(8,269444),(10,132296),(12,269444),(14,269444),(16,269444),(18,134408),(20,269444),(22,269444),(57,269444),(58,269316),(73,269444),(81,269444),(82,269444),(98,269380),(101,361615),(106,269444),(114,269444),(129,203906),(137,203906),(138,269444),(145,203906),(146,269444),(153,400654),(169,361615),(170,269444),(178,269444),(186,269444),(197,269380),(198,269444),(201,269444),(202,203906)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_130 : K_130.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_131 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,2114,5285,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(106,400654),(109,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,271492),(178,400654),(186,400654),(197,269380),(201,271492)]),([7,31,1057,2114,5285,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(58,400654),(74,400654),(81,400654),(82,400654),(106,400654),(109,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,134410),(178,400654),(186,400654),(189,400590),(201,134410),(202,400654)]),([7,31,1057,2114,6342,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(114,400654),(117,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,203842),(186,400654),(197,269380),(201,271492)]),([7,31,1057,2114,6342,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,203842),(186,400654),(201,134410),(202,400654)]),([7,31,1057,2114,8456,12684,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(186,400654),(205,269380),(206,400654)]),([7,31,1057,2114,8456,15855,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,269380),(178,400654),(185,203842),(186,400654),(205,269380),(206,400654)]),([7,31,1057,2114,8456,16384,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,269380),(178,400654),(185,203842),(186,400654),(202,400654),(205,400654)]),([7,31,1057,2114,8456,16912,17392],[(0,275848),(2,361610),(4,275848),(6,275848),(8,275848),(10,66760),(12,275848),(14,68872),(16,275848),(18,275848),(20,275848),(22,400654),(57,275848),(58,275848),(81,275848),(82,275848),(97,265608),(105,275848),(106,275848),(113,275848),(114,275848),(130,275848),(134,275848),(137,275848),(138,275848),(142,275848),(145,203842),(146,275848),(150,275848),(153,269380),(154,275848),(158,275848),(170,275848),(178,275848),(181,275784),(186,275848),(201,269380),(202,275848),(205,275848)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_131 : K_131.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_132 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,2114,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,269380),(178,400654),(185,203842),(186,400654),(202,400654),(205,400654)]),([7,31,1057,2114,8456,16912,31775],[(0,400654),(2,361615),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(81,400654),(82,400654),(97,400644),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(173,400654),(177,269316),(178,400654),(186,400654),(202,400654),(205,400654)]),([7,31,1057,2114,8456,16912,31777],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(62,171278),(81,400654),(82,400654),(85,171278),(105,400654),(106,400654),(109,171278),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(141,171278),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,269380),(178,400654),(181,400654),(185,203842),(186,400654),(202,400654),(205,400654)]),([7,31,1057,2114,8456,16912,31810],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(74,400450),(78,204046),(81,400654),(82,400654),(86,203842),(105,400654),(106,400654),(113,400654),(114,400654),(117,203842),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(149,203842),(153,400654),(154,400654),(170,400654),(177,269380),(178,400654),(185,269380),(186,400654),(189,400654),(202,400654),(205,400654)]),([7,31,1057,2114,8456,16912,32272],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(177,269380),(178,400654),(185,203842),(186,400654),(202,400654),(205,400654)]),([7,31,1057,2114,8456,16927,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(73,400654),(81,400654),(82,400654),(97,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(133,400654),(137,400654),(138,400654),(146,400654),(154,400654),(169,269380),(170,400654),(177,269380),(178,400654),(185,203842),(186,400654),(202,400654),(205,400654)]),([7,31,1057,2114,8456,17392],[(1,275848),(3,275848),(5,275848),(7,275848),(9,275848),(11,275848),(13,275848),(15,275848),(17,269380),(19,269380),(59,275848),(63,275848),(75,275848),(79,275848),(83,275848),(87,275848),(99,275848),(103,275848),(107,275848),(111,275848),(115,275848),(119,275848),(131,269380),(135,275848),(139,269380),(141,0),(143,275848),(147,269380),(151,275848),(155,203842),(159,203842)]),([7,31,1057,2114,8456,17392,31744],[(0,269380),(2,269380),(4,269380),(6,269380),(8,269380),(10,66760),(12,269380),(14,68872),(16,269380),(18,269380),(20,269380),(22,269380),(57,269380),(58,269316),(73,198031),(81,269380),(82,269380),(97,265615),(105,203842),(106,269380),(113,203842),(114,269380),(130,269380),(133,197704),(138,269380),(141,269316),(146,269380),(154,269444),(169,361615),(170,269380),(174,275848),(177,269380),(178,269380),(182,275848),(185,203842),(186,269380),(190,275848),(194,275855),(198,269380),(202,275848),(205,400654),(206,275848)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_132 : K_132.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_133 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,2114,8456,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,203842),(186,400654),(202,400654),(205,400654)]),([7,31,1057,2114,8456,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(146,400654),(149,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,269380),(178,400654),(186,400654),(202,400654),(205,400654)]),([7,31,1057,2114,8456,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,271492),(178,400654),(185,203842),(186,400654),(193,271492),(205,269380)]),([7,31,1057,2114,8456,28539,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(186,400654),(193,271492),(205,269380)]),([7,31,1057,2114,9513,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(81,400654),(82,400654),(106,400654),(109,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,203842),(186,400654),(202,400654),(205,400654)]),([7,31,1057,2114,10570,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,269380),(178,400654),(186,400654),(189,400590),(202,400654),(205,400654)]),([7,31,1057,2114,16912,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,68872),(57,400654),(74,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(186,400654),(189,400590),(194,400654),(197,400654)]),([7,31,1057,2114,16912,24311,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,68872),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,68872),(178,400654),(185,203842),(186,400654),(194,400654),(197,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_133 : K_133.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_134 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,2114,16912,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,269380),(178,400654),(185,203842),(186,400654),(193,134410),(194,400654)]),([7,31,1057,2114,16912,28539,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(186,400654),(189,400590),(193,134410),(194,400654)]),([7,31,1057,2143,4228,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132362),(57,400654),(74,400654),(77,400654),(82,400654),(97,400654),(105,400654),(106,400654),(113,400654),(129,400654),(137,400654),(138,400654),(145,400654),(153,400654),(154,400654),(169,132362),(170,400654),(178,400654),(186,400654),(189,400590),(201,132362),(202,400654)]),([7,31,1057,3042,4228,8456,16912],[(0,275848),(2,197775),(4,275848),(6,275848),(8,275848),(10,400654),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(57,275848),(58,275458),(62,275848),(74,132298),(81,145570),(82,275848),(85,275458),(97,145602),(98,275522),(105,275848),(106,275848),(109,275458),(118,275522),(129,145602),(130,134346),(134,406728),(137,275848),(138,275848),(141,275458),(142,134346),(146,145602),(150,134346),(153,269380),(154,68872),(158,134346),(170,275586),(177,275848),(178,275848),(181,275458),(185,275848),(190,407752),(193,275848),(194,275848),(201,134410),(202,271492),(205,134346)]),([7,31,1057,3042,4228,8456,16912,31744],[(168,0),(228,275458),(248,406728),(252,134346)]),([7,31,1057,3042,4228,16912],[(1,134346),(2,0),(3,134346),(5,134346),(7,134346),(9,134346),(11,134346),(13,134346),(15,134346),(17,68808),(19,68808),(59,134346),(63,134346),(75,134346),(79,134346),(83,134346),(87,134346),(97,0),(99,134346),(103,134346),(107,134346),(111,134346),(115,134346),(119,134346),(131,68808),(135,68808),(139,68808),(143,134346),(147,68808),(151,68808),(155,210312),(159,134346)]),([7,31,1057,3042,4228,16912,31744],[(0,134346),(2,134346),(4,134346),(6,134346),(8,134346),(10,134346),(12,134346),(14,203844),(16,134346),(18,205956),(20,134346),(22,134346),(57,134346),(74,132298),(77,134346),(81,134314),(82,134346),(97,134346),(105,134346),(106,134346),(113,134346),(129,68808),(137,68808),(138,134346),(145,132298),(153,68808),(154,134346),(169,361615),(170,134346),(174,134346),(178,134346),(182,134346),(186,134346),(189,400590),(190,134346),(194,134346),(198,134346),(201,134346),(202,68808),(206,134346)]),([7,31,1057,3171,4228,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(62,400654),(82,400654),(85,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,271492),(178,400654),(186,400654),(197,269380),(201,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_134 : K_134.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_135 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,3171,4228,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(62,400654),(74,400654),(82,400654),(85,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,134410),(178,400654),(186,400654),(189,400590),(201,134410),(202,400654)]),([7,31,1057,3171,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(62,400654),(82,400654),(85,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,269380),(178,400654),(185,203842),(186,400654),(202,400654),(205,400654)]),([7,31,1057,4228,6342,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,66760),(201,271492)]),([7,31,1057,4228,6342,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(114,400654),(117,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,66760),(197,132298),(201,134410),(202,400654)]),([7,31,1057,4228,8192,16912,31744],[(0,132298),(2,197704),(4,132298),(6,132298),(8,132298),(10,203842),(12,132298),(14,132298),(16,132298),(18,205954),(20,132298),(22,132298),(57,132298),(62,132266),(81,132298),(82,132298),(96,0),(97,132298),(98,132298),(105,132298),(106,132298),(113,132298),(114,132298),(137,66760),(138,132298),(145,66760),(146,132298),(153,66760),(154,132298),(169,72898),(170,132298),(177,132298),(178,132298),(185,66760),(190,132298),(194,132298),(197,132298),(202,66760)]),([7,31,1057,4228,8456,10570,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,205954),(57,400654),(58,400654),(74,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(189,203842),(197,205954)]),([7,31,1057,4228,8456,15855,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,205954),(57,400654),(62,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,205954),(178,400654),(185,66760),(197,205954),(206,205954)]),([7,31,1057,4228,8456,16912,17392],[(0,275848),(2,361610),(4,275848),(6,275848),(8,275848),(10,203842),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,400654),(57,275848),(62,275848),(73,275528),(81,275848),(82,275848),(96,0),(97,265608),(98,275848),(105,275848),(106,275848),(113,275848),(114,275848),(130,132488),(137,275848),(138,275848),(145,66760),(146,275848),(153,275848),(154,275848),(170,275848),(177,66728),(178,275848),(193,66760),(202,275848),(205,275848)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_135 : K_135.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_136 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,4228,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(62,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,132298),(178,400654),(185,66760),(197,132298),(202,400654)]),([7,31,1057,4228,8456,16912,31775],[(0,400654),(2,361615),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(62,400654),(73,72974),(81,400654),(82,400654),(96,0),(97,400644),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(173,400654),(178,400654),(181,400654),(197,132298),(202,400654)]),([7,31,1057,4228,8456,16912,31777],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(58,1294),(62,400654),(81,400654),(82,400654),(85,1294),(98,400654),(105,400654),(106,400654),(109,1294),(113,400654),(114,400654),(137,400654),(138,400654),(141,1294),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,132271),(178,400654),(181,400654),(185,66760),(197,132298),(202,400654)]),([7,31,1057,4228,8456,16912,31810],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(57,400654),(58,400386),(62,400654),(74,400450),(78,204046),(81,400654),(82,400654),(85,400386),(86,203842),(98,400654),(105,400654),(106,400654),(109,400386),(113,400654),(114,400654),(117,203842),(130,400514),(137,400654),(138,400654),(141,400386),(145,400654),(146,400654),(149,203842),(153,400654),(154,400654),(170,400654),(177,72898),(178,400654),(181,400386),(185,203842),(189,203842),(197,134351),(202,400654),(205,205954)]),([7,31,1057,4228,8456,16912,32272],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,66760),(57,400654),(62,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,132366),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(177,66760),(178,400654),(185,66760),(197,66760),(202,400654),(205,400654)]),([7,31,1057,4228,8456,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,66760),(197,132298),(202,400654)]),([7,31,1057,4228,8456,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(62,400654),(74,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(146,400654),(149,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,132298),(178,400654),(189,66760),(197,132298)]),([7,31,1057,4228,8456,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(62,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,132298),(178,400654),(185,66760),(193,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_136 : K_136.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_137 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,4228,8456,30653,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(58,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(189,66760),(193,271492),(206,132298)]),([7,31,1057,4228,8479,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(62,400654),(73,400654),(81,400654),(82,400654),(98,400654),(101,400654),(106,400654),(109,400654),(114,400654),(129,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(168,0),(169,132298),(170,400654),(177,132298),(178,400654),(185,66760),(197,132298),(202,400654)]),([7,31,1057,4228,9192,16912,31744],[(0,132298),(2,132298),(4,132298),(6,132298),(8,132298),(10,203842),(12,132298),(14,132298),(16,132298),(18,205954),(20,132298),(22,132298),(57,132298),(62,132266),(73,132298),(81,132298),(82,132298),(98,132298),(101,361615),(105,132266),(106,132298),(114,400590),(129,66760),(137,66760),(138,132298),(145,66760),(146,132298),(153,134346),(169,361615),(170,132298),(177,132298),(178,132298),(185,66760),(186,132298),(197,132298),(198,132298),(202,66760)]),([7,31,1057,4228,9513,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(81,400654),(82,400654),(98,400654),(106,400654),(109,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,66760),(197,132298),(202,400654)]),([7,31,1057,4228,12684,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(62,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(114,400654),(117,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,132298),(178,400654),(197,132298),(198,132298),(202,400654)]),([7,31,1057,4228,16912,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(194,400654),(202,400654),(205,400590)]),([7,31,1057,4228,16912,24311,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(62,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,132298),(178,400654),(185,66760),(194,400654),(205,132298)]),([7,31,1057,4228,16912,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(62,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,134410),(178,400654),(185,66760),(193,134410),(194,400654),(205,132298)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_137 : K_137.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_138 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,4228,16912,30653,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(57,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(193,134410),(194,400654),(205,132298),(206,400654)]),([7,31,1057,5285,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(58,400654),(82,400654),(85,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,132298),(178,400654),(185,66760),(197,132298),(202,400654)]),([7,31,1057,8456,10570,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,203842),(57,400654),(58,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,203842),(178,400654),(189,203842),(193,203842),(202,400654),(205,400654)]),([7,31,1057,8456,12684,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(57,400654),(62,400654),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,132298),(178,400654),(193,66760),(198,132298),(202,400654)]),([7,31,1057,8456,16912,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,203842),(57,400654),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,203842),(178,400654),(194,400654),(201,203842),(202,400654)]),([7,31,1057,8456,16912,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,66760),(57,400654),(62,400654),(74,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,66760),(178,400654),(189,66760),(194,400654),(197,400654),(201,66760)]),([7,31,1057,8456,16912,28539,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,203842),(57,400654),(62,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,203842),(178,400654),(189,203842),(194,400654),(201,203842)]),([7,31,1057,8456,16912,30653,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,66760),(57,400654),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,66760),(178,400654),(194,400654),(197,400654),(201,66760),(206,66760)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_138 : K_138.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_139 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,1057,8456,16912,31744,31810],[(0,203842),(2,197704),(4,203842),(6,203842),(8,203842),(10,203842),(12,203842),(14,203842),(16,203842),(18,203842),(20,203842),(22,269380),(57,203842),(58,203778),(81,203842),(82,203842),(98,203842),(105,203842),(106,203842),(113,203842),(114,203842),(129,203842),(130,203842),(134,203842),(137,203842),(138,203842),(142,203842),(146,203842),(150,203842),(154,203842),(157,203842),(158,203842),(177,269380),(178,203842),(186,203842),(194,203842),(197,203842),(201,269380),(202,203842),(205,203842)]),([7,31,1057,8456,16912,31744,31876],[(0,66760),(2,197704),(4,66760),(6,66760),(8,66760),(10,66760),(12,66760),(14,66760),(16,66760),(18,66760),(20,66760),(22,132298),(57,66760),(62,66728),(74,66760),(81,66760),(82,66760),(105,66760),(106,66760),(113,66760),(114,66760),(129,66760),(130,66760),(137,66760),(138,66760),(146,66760),(149,66760),(154,66760),(177,132298),(178,66760),(186,66760),(189,66760),(194,66760),(202,66760),(205,66760)]),([7,31,1057,8456,16912,31810],[(1,203842),(2,0),(3,203842),(5,203842),(7,203842),(9,203842),(11,203842),(13,203842),(15,203842),(17,269380),(19,269380),(59,203842),(63,203842),(75,203842),(79,203842),(83,203842),(87,203842),(99,203842),(103,203842),(107,203842),(111,203842),(115,203842),(119,203842),(131,269380),(135,204046),(139,269380),(143,203842),(147,72898),(151,203842),(155,269380),(159,203842)]),([7,31,1087,2114,4228,8456,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271364),(57,400654),(58,400654),(61,400654),(73,400654),(77,400654),(81,400654),(97,400654),(98,400654),(101,400654),(105,400654),(106,400654),(113,400654),(114,400654),(129,400654),(133,400654),(137,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,271364),(170,400654),(173,400654),(178,400654),(186,400654),(197,269316),(201,271364)]),([7,31,1087,2114,8456,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269316),(57,400654),(58,400654),(61,400654),(73,400654),(77,400654),(81,400654),(97,400654),(101,400654),(105,400654),(113,400654),(114,400654),(129,400654),(130,400654),(133,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,269316),(170,400654),(173,400654),(177,269316),(178,400654),(185,203778),(186,400654),(202,400654),(205,400654)]),([7,31,2017,2114,4228,8456,16912],[(0,275848),(2,361615),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(57,145762),(58,275848),(74,132266),(78,275848),(81,275848),(82,145762),(86,132266),(97,145762),(98,275848),(110,145762),(113,66760),(114,203842),(117,132266),(128,0),(129,145762),(130,134314),(134,406696),(138,145762),(142,134314),(145,275848),(146,275848),(149,132266),(150,134314),(153,269380),(154,68872),(158,134314),(170,275848),(177,275848),(182,407720),(185,132298),(186,205954),(189,132266),(193,275848),(194,275848),(201,134410),(202,271492),(205,134314)]),([7,31,2017,2114,4228,8456,16912,31744],[(72,132266),(76,265288),(108,140482),(128,134314),(132,361615),(236,132266),(248,406696),(252,134314)]),([7,31,2017,2114,4228,16912],[(1,134314),(2,0),(3,134314),(5,134314),(7,134314),(9,134314),(11,134314),(13,134314),(15,134314),(17,68776),(19,68776),(57,0),(59,134314),(63,134314),(75,134314),(79,134314),(83,134314),(87,134314),(97,0),(99,134314),(103,134314),(107,134314),(111,134314),(115,134314),(119,134314),(131,68776),(135,68776),(139,68776),(143,68776),(147,68776),(151,134314),(155,3464),(159,134314)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_139 : K_139.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_140 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,2017,2114,4228,16912,31744],[(0,134314),(2,134314),(4,134314),(6,134314),(8,134314),(10,134314),(12,134314),(14,171076),(16,134314),(18,173188),(20,134314),(22,134314),(57,134154),(61,361615),(72,0),(73,134314),(74,132266),(77,134154),(81,134314),(82,134314),(97,134314),(101,361615),(105,134314),(113,134314),(114,134314),(129,134154),(133,68616),(137,68776),(145,132298),(146,134314),(153,68776),(154,134314),(169,361615),(170,134314),(173,361615),(174,134314),(178,134314),(182,134314),(186,134314),(189,132266),(190,134314),(194,134314),(198,134314),(201,134314),(202,68776),(206,134314)]),([7,31,2017,4228,8456,16912],[(1,132266),(2,0),(3,132266),(5,132266),(7,132266),(9,132266),(11,132266),(13,132266),(15,132266),(17,66728),(19,66728),(57,0),(59,132266),(63,132266),(73,0),(75,132266),(79,132266),(83,132266),(87,132266),(96,0),(97,0),(99,132266),(103,132266),(107,132266),(111,132266),(115,132266),(119,132266),(131,66728),(135,66728),(139,66728),(143,132463),(147,1416),(151,132266),(155,66728),(159,132266)]),([7,31,2017,4228,8456,16912,31744],[(0,132266),(2,132266),(4,132266),(6,132266),(8,132266),(10,171074),(12,132266),(14,132266),(16,132266),(18,173186),(20,132266),(22,132266),(57,132106),(61,361615),(62,400654),(73,132266),(77,361615),(81,132266),(96,0),(97,132266),(98,132266),(101,361615),(105,132266),(106,132266),(113,132266),(114,132266),(129,132106),(133,66568),(137,66728),(145,66728),(146,132266),(153,134410),(154,132266),(169,361615),(170,132266),(173,361615),(174,132266),(177,400654),(178,132266),(182,132266),(185,66728),(186,132266),(190,132266),(194,132266),(197,132266),(198,132266),(202,66728),(206,132266)]),([7,31,2114,3042,4228,8456,16912],[(0,275848),(2,197775),(4,275848),(6,275848),(8,275848),(10,400654),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(58,275458),(62,275848),(74,275848),(81,145570),(82,275848),(85,275848),(97,145602),(98,275848),(105,275848),(106,275848),(109,275458),(118,145602),(129,145602),(137,275848),(138,275848),(141,275458),(146,145602),(153,269380),(154,68872),(170,275848),(177,275848),(178,275848),(181,275458),(185,275848),(193,275848),(194,275848),(201,134410),(202,271492)]),([7,31,2114,3042,4228,8456,16912,31744],[(60,265288),(84,400654),(116,140482),(228,275458)]),([7,31,2114,3171,4228,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(62,400654),(74,400654),(82,400654),(85,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,271492),(178,400654),(186,400654),(197,269380),(201,271492)]),([7,31,2114,3171,4228,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(62,400654),(82,400654),(85,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,134410),(178,400654),(186,400654),(201,134410),(202,400654)]),([7,31,2114,3171,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(62,400654),(74,400654),(82,400654),(85,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,269380),(178,400654),(185,269380),(186,400654),(202,400654),(205,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_140 : K_140.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_141 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,2114,4228,5092,8456,16912,31744],[(104,66728),(116,400654),(152,400558),(168,400399),(224,400386)]),([7,31,2114,4228,5285,8456,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(74,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(114,400654),(117,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,271492),(201,271492)]),([7,31,2114,4228,5285,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(58,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(181,400590),(185,134410),(201,134410),(202,400654)]),([7,31,2114,4228,8456,9192,16912,31744],[(100,361615),(148,140482),(156,400654),(244,145572)]),([7,31,2114,4228,8456,9513,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,205954),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(189,203842)]),([7,31,2114,4228,8456,15855,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(62,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,72898),(178,400654),(185,72898),(206,400654)]),([7,31,2114,4228,8456,16912,17392],[(0,275848),(2,361610),(4,275848),(6,275848),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,400654),(62,275848),(73,275528),(74,275848),(81,275848),(82,275848),(97,265608),(105,275848),(106,275848),(113,275848),(114,275848),(130,275848),(137,275848),(138,275848),(145,275848),(146,275848),(153,275848),(154,275848),(170,275848),(177,140642),(178,275848),(189,140642),(193,140642),(202,275848),(205,275848)]),([7,31,2114,4228,8456,16912,17392,31744],[(72,138410),(176,132266),(188,140482),(192,134314),(204,400654),(224,140610)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_141 : K_141.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_142 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,2114,4228,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(62,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,72898),(178,400654),(185,72898),(202,400654)]),([7,31,2114,4228,8456,16912,31744,31775],[(60,72964),(216,72898),(220,400654),(228,400654),(244,72898),(256,400654),(260,400654)]),([7,31,2114,4228,8456,16912,31775],[(0,400654),(2,361615),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(62,400654),(73,72974),(74,400654),(81,400654),(82,400654),(97,400644),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(173,400654),(178,400654),(181,400654),(185,145762),(197,145762),(202,400654)]),([7,31,2114,4228,8456,16912,31777],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(58,1294),(62,400654),(74,400654),(78,171278),(81,400654),(82,400654),(85,1294),(86,171278),(98,3342),(105,400654),(106,400654),(109,1294),(113,400654),(114,400654),(117,171278),(130,400654),(137,400654),(138,400654),(141,1294),(145,400654),(146,400654),(149,171278),(153,400654),(154,400654),(169,72898),(170,400654),(177,72898),(178,400654),(181,1294),(185,72898),(189,171278),(197,134319),(202,400654),(205,173326)]),([7,31,2114,4228,8456,16912,31810],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(58,400386),(62,400654),(74,400654),(81,400654),(82,400654),(85,400386),(105,400654),(106,400654),(109,400386),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(141,400386),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(177,72898),(178,400654),(181,400654),(185,72898),(202,400654)]),([7,31,2114,4228,8456,16912,32272],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(62,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(177,72898),(178,400654),(185,72898),(202,400654),(205,400654)]),([7,31,2114,4228,8456,16927,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(57,400654),(62,400654),(73,400654),(74,400654),(81,400654),(82,400654),(97,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(133,400654),(138,400654),(141,400654),(145,400654),(146,400654),(154,400654),(170,400654),(178,400654),(202,400654)]),([7,31,2114,4228,8456,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,205954),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(185,205954),(202,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_142 : K_142.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_143 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,2114,4228,8456,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(62,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(146,400654),(149,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,72898),(178,400654),(189,72898)]),([7,31,2114,4228,8456,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(62,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,271492),(178,400654),(185,271492),(193,271492)]),([7,31,2114,4228,8456,31710,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(133,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(189,269380),(193,271492),(206,400654)]),([7,31,2114,4228,9192,16912,31744],[(2,0),(57,361646),(73,0),(81,66760),(82,203842),(101,361615),(114,400558),(117,0),(129,0),(137,132298),(138,205954),(153,134314),(169,361615),(170,145762),(198,145572),(202,145572)]),([7,31,2114,4228,10570,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(58,400654),(74,400654),(81,400654),(82,400654),(106,400654),(109,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(178,400654),(181,400590),(185,72898),(202,400654)]),([7,31,2114,4228,12684,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,68872),(62,400654),(81,400654),(82,400654),(105,400654),(106,400654),(114,400654),(117,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,68872),(178,400654),(198,400654),(202,400654)]),([7,31,2114,4228,16912,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,68872),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(181,400590),(194,400654),(202,400654)]),([7,31,2114,4228,16912,24311,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(62,400654),(74,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,72898),(178,400654),(185,72898),(194,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_143 : K_143.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_144 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,2114,4228,16912,25368,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(62,400654),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,134410),(178,400654),(185,134410),(193,134410),(194,400654)]),([7,31,2114,4228,16912,31710,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(133,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(178,400654),(181,400590),(193,134410),(194,400654),(206,400654)]),([7,31,2114,4255,8456,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(57,400654),(62,400654),(74,400654),(77,400654),(82,400654),(85,400654),(97,400654),(105,400654),(106,400654),(113,400654),(129,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(170,400654),(178,400654),(202,400654)]),([7,31,2114,6342,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,203842),(74,400654),(82,400654),(85,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,203842),(178,400654),(185,203842),(202,400654)]),([7,31,2114,8456,9513,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,203842),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(114,400654),(117,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,203842),(178,400654),(193,203842),(202,400654),(205,400654)]),([7,31,2114,8456,12684,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(62,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(114,400654),(117,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,269380),(178,400654),(193,335118),(198,400654),(202,400654)]),([7,31,2114,8456,16912,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,203842),(178,400654),(194,400654),(201,269380),(202,400654)]),([7,31,2114,8456,16912,21140,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(62,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,72898),(178,400654),(194,400654),(197,400654),(201,72898)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_144 : K_144.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_145 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,2114,8456,16912,28539,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(62,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,72898),(178,400654),(194,400654),(201,72898)]),([7,31,2114,8456,16912,31710,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(133,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,203842),(178,400654),(194,400654),(197,400654),(201,335118),(206,400654)]),([7,31,2114,8456,16912,31744,31777],[(0,269380),(2,197704),(4,269380),(6,66760),(8,269380),(10,68872),(12,269380),(14,269380),(16,269380),(18,269380),(20,269380),(22,269380),(81,203842),(82,269380),(98,269380),(105,203842),(106,269380),(113,269380),(114,271492),(129,72898),(130,269380),(134,171278),(137,203842),(138,269380),(142,171278),(146,171278),(150,269380),(154,269380),(157,269380),(158,171278),(169,72898),(170,269316),(177,203842),(178,269380),(186,203842),(194,269380),(197,269380),(201,269380),(202,269380),(205,269380)]),([7,31,2114,8456,16912,31744,31876],[(0,72898),(2,197704),(4,72898),(6,72898),(8,72898),(10,72898),(12,72898),(14,72898),(16,72898),(18,72898),(20,72898),(22,72898),(62,72964),(81,72898),(82,72898),(105,132298),(106,205954),(113,134410),(114,271492),(129,72898),(137,72898),(138,72898),(146,72898),(154,72898),(177,66760),(178,203842),(186,335118),(194,72898),(202,72898),(205,72898)]),([7,31,2114,8456,16912,31777],[(1,171278),(3,171278),(5,171278),(7,171278),(9,171278),(11,171278),(13,171278),(15,171278),(17,269380),(19,269380),(59,171278),(63,171278),(75,171278),(79,171278),(83,171278),(87,171278),(99,171278),(103,171278),(107,171278),(111,171278),(115,171278),(119,171278),(131,269380),(135,171278),(139,269380),(143,171278),(147,203842),(151,269380),(155,269380),(159,171278)]),([7,31,3042,4228,8456,16912],[(1,275458),(2,0),(3,275458),(5,145570),(7,145570),(9,275458),(11,275458),(13,275458),(15,275458),(17,275458),(19,275458),(63,275848),(73,0),(75,275458),(79,275458),(83,145570),(86,0),(87,275458),(97,0),(99,275458),(103,275458),(107,145570),(111,145570),(115,275458),(119,275458),(131,275458),(135,275458),(139,145570),(143,275458),(147,275458),(151,275458),(155,275458),(159,275458)]),([7,31,3042,4228,8456,16912,31744],[(2,0),(61,265288),(62,400654),(73,0),(81,66728),(86,0),(97,263172),(113,269380),(114,68872),(128,0),(129,0),(137,132266),(153,134410),(154,271492),(169,361615),(170,145762),(174,275458),(177,400654),(178,275848),(182,275458),(190,275458),(194,275458),(198,145570),(202,145570),(206,275458)]),([7,31,4228,5285,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(58,400654),(78,400654),(82,400654),(85,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,132298),(185,132298),(197,132298),(202,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_145 : K_145.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_146 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,4228,6342,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,66760),(78,400654),(82,400654),(85,400654),(105,400654),(106,400654),(113,400654),(114,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,66760),(185,66760),(202,400654)]),([7,31,4228,8456,9513,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(81,400654),(82,400654),(102,400654),(105,400654),(106,400654),(114,400654),(117,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,66760),(193,132298),(202,400654)]),([7,31,4228,8456,10570,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(58,400654),(74,400654),(81,400654),(82,400654),(102,400654),(105,400654),(106,400654),(114,400654),(117,400654),(130,400654),(137,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,72898),(170,400654),(177,72898),(189,72898),(193,72898),(202,400654)]),([7,31,4228,8456,16912,17969,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,66760),(74,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(134,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,66760),(189,66760),(194,400654),(201,66760),(202,400654)]),([7,31,4228,8456,16912,19026,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(58,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(134,400654),(137,400654),(138,400654),(145,400654),(146,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,132298),(194,400654),(201,132298),(202,400654)]),([7,31,4228,8456,16912,30653,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,275848),(58,400654),(81,400654),(82,400654),(98,400654),(105,400654),(106,400654),(113,400654),(114,400654),(134,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,72898),(194,400654),(201,400654),(206,400654)]),([7,31,4228,8456,16912,31710,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(74,400654),(81,400654),(82,400654),(105,400654),(106,400654),(113,400654),(114,400654),(133,400654),(134,400654),(138,400654),(141,400654),(146,400654),(149,400654),(154,400654),(157,400654),(169,72898),(170,400654),(177,66760),(189,132298),(194,400654),(201,400654),(206,400654)]),([7,31,4228,8456,16912,31744,31777],[(0,132298),(2,197704),(4,132298),(6,203842),(8,132298),(10,132298),(12,132298),(14,205954),(16,132298),(18,132298),(20,132298),(22,132298),(74,132298),(81,132298),(82,132298),(105,66760),(106,132298),(113,134410),(114,132298),(128,0),(129,72898),(130,132298),(134,1294),(137,66760),(138,132298),(142,1294),(146,1294),(149,132298),(150,132271),(154,66760),(158,1294),(169,72898),(174,400654),(177,66760),(178,132298),(186,132298),(189,132298),(194,66760),(201,132271),(202,132298),(205,132298)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_146 : K_146.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_147 : List (List ℕ × List (ℕ × ℕ)) := [([7,31,4228,8456,16912,31744,31810],[(0,72898),(2,197704),(4,72898),(6,72898),(8,72898),(10,72898),(12,72898),(14,72898),(16,72898),(18,72898),(20,72898),(22,72898),(81,269380),(82,68872),(105,72898),(106,72898),(113,134410),(114,271492),(129,72898),(134,400386),(137,72898),(138,400386),(142,72898),(146,72898),(150,400386),(154,72898),(158,400386),(174,400654),(177,203842),(178,66760),(186,72898),(194,132298),(201,72898),(202,72898),(205,72898)]),([7,31,4228,8456,16912,31777],[(1,1294),(2,0),(3,1294),(5,1294),(7,1294),(9,1294),(11,1294),(13,1294),(15,1294),(17,132271),(19,132271),(59,1294),(63,1294),(75,1294),(79,1294),(83,1294),(87,1294),(99,1294),(103,1294),(107,1294),(111,1294),(115,1294),(119,1294),(129,0),(131,132271),(135,400654),(139,132271),(143,1294),(147,132271),(151,132271),(155,66760),(159,1294)]),([7,31,4228,8456,16912,31810],[(1,400386),(2,0),(3,400386),(5,400386),(7,400386),(9,400386),(11,400386),(13,400386),(15,400386),(17,72898),(19,72898),(59,400386),(63,400386),(75,400386),(79,400386),(83,400386),(87,400386),(99,400386),(103,400386),(107,400386),(111,400386),(115,400386),(119,400386),(135,400654),(139,72898),(143,72898),(147,72898),(151,400386),(155,72898),(159,400386)]),([7,1057,1087,2114,4228,8456,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,271492),(57,400654),(58,400654),(61,400654),(73,400654),(74,400654),(77,400654),(97,400654),(98,400654),(101,400654),(106,400654),(113,400654),(114,400654),(129,400654),(130,400654),(133,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,271492),(170,400654),(173,400654),(177,72898),(178,400654),(186,400654),(197,269380),(201,271492)]),([7,1057,1087,2114,4228,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,134410),(58,400654),(61,400654),(73,400654),(74,400654),(82,400654),(97,400654),(98,400654),(113,400654),(114,400654),(129,400654),(130,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,134410),(170,400654),(177,72898),(178,400654),(186,400654),(189,400590),(201,134410),(202,400654)]),([7,1057,1087,2114,8456,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,269380),(57,400654),(58,400654),(61,400654),(73,400654),(74,400654),(77,400654),(97,400654),(98,400654),(101,400654),(113,400654),(114,400654),(129,400654),(130,400654),(133,400654),(138,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,269380),(170,400654),(173,400654),(177,72898),(178,400654),(185,203842),(186,400654),(202,400654),(205,400654)]),([7,1057,1087,4228,8456,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,132298),(58,400654),(61,400654),(73,400654),(74,400654),(97,400654),(98,400654),(106,400654),(113,400654),(114,400654),(129,400654),(130,400654),(145,400654),(146,400654),(153,400654),(154,400654),(169,132298),(170,400654),(177,72898),(178,400654),(185,66760),(197,132298),(202,400654)]),([7,1057,2114,4228,8456,31744,31775],[(0,72898),(2,72898),(4,72898),(6,72898),(8,72898),(10,72898),(12,72898),(14,72898),(16,72898),(18,72898),(20,72898),(22,361615),(57,72898),(58,72898),(73,72898),(74,72898),(81,72898),(82,72898),(97,72898),(98,72898),(105,72898),(106,72898),(113,72898),(114,72898),(130,361615),(146,361615),(149,72898),(153,271492),(154,361615),(170,72898),(189,138434),(202,72898),(205,72898)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_147 : K_147.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_148 : List (List ℕ × List (ℕ × ℕ)) := [([7,1057,2114,4228,8456,31744,32736],[(0,197704),(2,197704),(4,197704),(6,197704),(8,197704),(10,197704),(12,197704),(14,197704),(16,197704),(18,197704),(20,197704),(22,400654),(57,197704),(58,197704),(73,197704),(74,197704),(81,197704),(82,197704),(97,197704),(98,197704),(105,197704),(106,197704),(113,197704),(114,197704),(130,197704),(138,197704),(149,197704),(153,197704),(170,197704),(173,197642),(189,197706),(202,197704),(205,197704)]),([7,1057,2114,8456,16912,31744,31775],[(0,72898),(2,72898),(4,72898),(6,72898),(8,72898),(10,72898),(12,72898),(14,72898),(16,72898),(18,72898),(20,72898),(22,361615),(57,72898),(58,72898),(73,72898),(74,72898),(81,72898),(82,72898),(97,72898),(98,72898),(105,72898),(106,72898),(113,72898),(114,72898),(129,72898),(130,361615),(137,203842),(146,361615),(157,72898),(169,361615),(170,72898),(197,72898),(202,72898),(205,72898)]),([7,1057,2114,8456,16912,31744,32736],[(0,197704),(2,197704),(4,197704),(6,197704),(8,197704),(10,197704),(12,197704),(14,197704),(16,197704),(18,197704),(20,197704),(22,400654),(57,197704),(58,197704),(73,197704),(74,197704),(81,197704),(82,197704),(97,197704),(98,197704),(105,197704),(106,197704),(113,197704),(114,197704),(129,197704),(130,197704),(136,0),(137,197704),(138,197704),(154,197704),(157,197704),(170,197704),(173,197640),(197,197704),(202,197704),(205,197704)]),([7,1087,2114,4228,8456,16912,31744],[(0,400654),(2,400654),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,72898),(62,400654),(74,400654),(78,400654),(81,400654),(82,400654),(86,400654),(102,400654),(105,400654),(106,400654),(113,400654),(114,400654),(117,400654),(130,400654),(134,400654),(137,400654),(138,400654),(142,400654),(145,400654),(146,400654),(149,400654),(150,400654),(153,400654),(154,400654),(158,400654),(169,72898),(170,400654),(177,72898),(178,400654),(185,72898),(189,269316),(193,331022),(201,374786),(202,400654),(205,400654)]),([7,1087,2114,4228,8456,31744],[(1,400654),(3,400654),(5,400654),(7,400654),(9,400654),(11,400654),(13,400654),(15,400654),(17,271364),(19,271364),(59,400654),(63,400654),(75,400654),(79,400654),(83,400654),(87,400654),(99,400654),(103,400654),(107,400654),(111,400654),(115,400654),(119,400654),(131,271364),(135,400654),(139,271364),(143,400654),(147,271364),(151,271364),(155,205826),(159,271364)]),([7,1087,2114,8456,16912,31744],[(1,400654),(3,400654),(5,400654),(7,400654),(9,400654),(11,400654),(13,400654),(15,400654),(17,269316),(19,269316),(59,400654),(63,400654),(75,400654),(79,400654),(83,400654),(87,400654),(99,400654),(103,400654),(107,400654),(111,400654),(115,400654),(119,400654),(131,269316),(135,400654),(139,269316),(143,400654),(147,203778),(151,269316),(155,269316),(159,400654)]),([7,2114,4228,8456,16912,31744,31775],[(0,72898),(2,72898),(4,72898),(6,72898),(8,72898),(10,72898),(12,72898),(14,72898),(16,72898),(18,72898),(20,72898),(22,361615),(57,72898),(58,72898),(73,72898),(74,72898),(81,72898),(82,72898),(97,72898),(98,72898),(105,72898),(106,72898),(113,72898),(114,72898),(129,72898),(137,72898),(138,361615),(146,361615),(173,72964),(177,361615),(189,72898),(202,72898),(205,72898)]),([8,31,992,1057,2114,4228,8456],[(1,271492),(2,0),(3,271492),(5,271492),(7,271492),(9,271492),(11,271492),(13,271492),(14,0),(15,271492),(17,271492),(19,271492),(21,205954),(22,0),(23,205954),(57,0),(59,271492),(63,271492),(72,0),(73,0),(75,271492),(79,271492),(83,271492),(87,271492),(99,271492),(103,271492),(107,271492),(111,271492),(114,0),(115,271492),(119,271492),(128,0),(129,0),(131,271492),(135,271492),(139,271492),(143,271492),(145,0),(147,271492),(151,271492),(153,0),(155,271492),(159,271492),(169,0),(171,205954),(175,205954),(179,205954),(183,205954),(187,205954),(191,271492),(193,0),(195,275848),(199,271492),(203,205954),(207,271492)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_148 : K_148.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_149 : List (List ℕ × List (ℕ × ℕ)) := [([8,31,992,1057,2114,4228,8456,16912],[(0,275848),(2,361615),(4,275848),(6,400654),(8,275848),(10,275848),(12,275848),(14,275848),(16,275848),(18,275848),(20,275848),(22,275848),(24,275848),(26,275848),(57,145762),(58,275848),(72,0),(73,145762),(74,275848),(78,275848),(81,275848),(82,145762),(86,275848),(98,275848),(102,275848),(105,275848),(106,145762),(110,132463),(113,275848),(114,275848),(117,275848),(118,132298),(128,0),(129,145762),(130,275848),(134,269710),(138,145762),(142,145762),(145,275848),(146,275848),(149,275848),(150,269380),(153,66760),(154,203842),(157,132298),(158,269380),(168,0),(169,145762),(170,275848),(174,406792),(178,145762),(182,145762),(185,275848),(186,275848),(189,275848),(190,134410),(193,275848),(194,275848),(197,132298),(198,134410),(201,269380),(202,68872),(205,269380),(206,134410),(218,275848),(222,275848),(225,275848),(226,145762),(230,374914),(233,275848),(234,275848),(237,275848),(238,271492),(241,132298),(242,205954),(245,132298),(246,271492),(249,275848),(250,275848),(253,269380),(254,271492),(257,134410),(258,271492),(261,134410),(262,271492)]),([8,31,992,1057,2114,4228,8456,16912,31744],[(72,0),(73,0),(76,361615),(84,400654),(96,0),(97,0),(98,0),(100,265288),(108,400654),(114,0),(128,0),(132,361615),(140,140482),(168,0),(169,0),(170,0),(172,361615),(180,72898),(182,0),(186,0),(194,0),(216,0),(220,197704),(228,400654),(292,275848),(296,0),(300,132298),(308,269380),(312,0),(313,0),(316,134410),(322,0),(324,271492)]),([8,31,992,1057,2114,4228,8456,31744],[(0,271492),(2,271492),(4,271492),(6,271492),(8,271492),(10,271492),(12,271492),(14,132298),(16,271492),(18,271492),(20,271492),(22,134410),(24,271492),(26,271492),(57,271492),(58,271492),(61,361615),(62,400654),(72,0),(73,271492),(74,271364),(77,361615),(81,271492),(85,400654),(97,271492),(101,271492),(105,271492),(109,400654),(113,271492),(114,271492),(128,0),(129,271492),(130,271428),(133,361615),(137,271492),(138,269444),(141,271492),(145,271492),(146,271492),(153,271492),(154,271492),(169,205954),(173,361615),(177,205954),(181,205954),(185,205954),(186,271492),(193,205954),(194,271492),(201,269380),(202,271492),(217,361615),(218,271492),(221,361615),(222,271492),(225,400654),(226,271492),(229,400654),(230,271492),(234,271492),(238,271492),(242,271492),(246,271492),(250,271492),(252,0),(253,269380),(254,271492),(257,271492),(258,205954),(262,271492)]),([8,31,992,1057,2114,8456,16912],[(1,269380),(2,0),(3,269380),(5,269380),(7,269380),(9,269380),(11,269380),(13,269380),(14,0),(15,269380),(17,203842),(19,203842),(21,269380),(23,269380),(57,0),(59,269380),(63,269380),(72,0),(73,0),(75,269380),(79,269380),(83,269380),(86,0),(87,269380),(99,269380),(103,269380),(107,269380),(111,269380),(115,269380),(119,269380),(129,0),(131,203842),(135,269710),(139,203842),(143,203842),(147,203842),(151,269380),(155,275848),(159,269380),(171,269380),(175,269380),(179,269380),(183,269380),(187,269380),(191,269380),(193,0),(195,269380),(199,269380),(203,203842),(207,269380)]),([8,31,992,1057,2114,8456,16912,31744],[(0,269380),(2,269380),(4,269380),(6,269380),(8,269380),(10,269380),(12,269380),(14,66760),(16,269380),(18,68872),(20,269380),(22,269380),(24,269380),(26,269380),(57,269380),(58,269380),(61,361615),(62,400654),(72,0),(73,269380),(74,269316),(77,361615),(81,269380),(84,0),(85,400654),(86,269316),(97,269380),(101,269380),(105,269380),(109,400654),(113,269380),(114,269380),(129,203842),(133,361615),(137,203842),(141,203842),(145,203842),(146,269380),(153,203842),(154,269380),(168,0),(169,269380),(170,269380),(173,269380),(177,269380),(178,269380),(181,400654),(185,269380),(186,269380),(193,203842),(194,269380),(201,269380),(202,271492),(217,361615),(218,269380),(221,361615),(222,269380),(225,400654),(226,269380),(229,400654),(230,269380),(233,269380),(234,269380),(238,269380),(241,203842),(242,269380),(246,269380),(250,203842),(254,269380),(258,269380),(261,269380),(262,269380)]),([8,31,992,2114,4228,8456,16912],[(1,275848),(2,0),(3,275848),(5,145762),(7,145762),(9,275848),(10,0),(11,275848),(13,275848),(15,275848),(17,275848),(18,0),(19,275848),(21,275848),(23,275848),(57,0),(63,275848),(75,275848),(79,275848),(82,0),(83,145762),(87,275848),(96,0),(97,0),(99,275848),(103,275848),(107,145762),(110,0),(111,145762),(113,0),(115,275848),(119,275848),(129,0),(131,275848),(135,275848),(138,0),(139,145762),(143,145762),(145,0),(146,0),(147,275848),(151,275848),(154,0),(155,275848),(159,275848),(171,275848),(175,275848),(179,145762),(183,275848),(185,0),(187,275848),(191,275848),(195,275848),(199,275848),(201,0),(203,275848),(207,275848)]),([8,31,992,2114,4228,8456,16912,31744],[(2,0),(10,0),(18,0),(57,197704),(58,72898),(61,361615),(62,400654),(73,0),(77,265288),(82,0),(85,400654),(96,0),(97,0),(101,361615),(108,0),(109,140482),(110,0),(113,66760),(114,203842),(129,0),(133,361615),(138,0),(141,72898),(145,0),(146,0),(153,269380),(154,68872),(168,0),(169,0),(173,197704),(181,400654),(185,132298),(186,205954),(201,134410),(202,271492),(217,361615),(218,145762),(221,361615),(222,275848),(225,400654),(226,275848),(229,400654),(230,275848),(232,0),(233,0),(238,275848),(242,0),(246,145762),(254,145762),(258,0),(262,275848)]),([8,31,1057,2114,4228,8456,16912,31744],[(0,400654),(2,197704),(4,400654),(6,400654),(8,400654),(10,400654),(12,400654),(14,400654),(16,400654),(18,400654),(20,400654),(22,400654),(24,400654),(26,275848),(57,400654),(58,400654),(62,400654),(74,400654),(78,400654),(81,400654),(82,400654),(85,400654),(86,400654),(98,400654),(102,400654),(105,400654),(106,400654),(109,400654),(110,400654),(113,400654),(114,400654),(117,400654),(118,400654),(130,400654),(134,400654),(137,400654),(138,400654),(141,400654),(142,400654),(145,400654),(146,400654),(149,400654),(150,400654),(153,400654),(154,400654),(157,400654),(158,400654),(170,400654),(174,400654),(177,400654),(178,400654),(181,400654),(182,400654),(185,400654),(186,400654),(189,400654),(190,400654),(193,400654),(194,400654),(197,400654),(198,400654),(201,400654),(202,400654),(205,400654),(206,400654),(217,72898),(218,400654),(225,72898),(226,400654),(229,400654),(233,72898),(234,400654),(237,400654),(241,72898),(245,269380),(249,72898),(253,134410),(257,72898),(258,400654),(261,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_149 : K_149.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_150 : List (List ℕ × List (ℕ × ℕ)) := [([8,31,1057,2114,4228,8456,31744],[(1,400654),(3,400654),(5,400654),(7,400654),(9,400654),(11,400654),(13,400654),(15,400654),(17,400654),(19,400654),(21,271492),(23,271492),(59,400654),(63,400654),(75,400654),(79,400654),(83,400654),(87,400654),(99,400654),(103,400654),(107,400654),(111,400654),(115,400654),(119,400654),(131,400654),(135,400654),(139,400654),(143,400654),(147,400654),(151,400654),(155,400654),(159,400654),(171,271492),(175,400654),(179,271492),(183,400654),(187,271492),(191,400654),(195,271492),(199,271492),(203,205954),(207,271492)]),([8,31,1057,2114,4228,16912,31744],[(1,400654),(2,0),(3,400654),(5,400654),(7,400654),(9,400654),(11,400654),(13,400654),(15,400654),(17,400654),(19,400654),(21,134410),(23,134410),(59,400654),(63,400654),(75,400654),(79,400654),(83,400654),(87,400654),(99,400654),(103,400654),(107,400654),(111,400654),(115,400654),(119,400654),(131,400654),(135,400654),(139,400654),(143,400654),(147,400654),(151,400654),(155,400654),(159,400654),(169,0),(171,134410),(175,400654),(179,134410),(183,400654),(187,134410),(191,400654),(195,134410),(199,134410),(203,68872),(207,400654)]),([8,31,1057,2114,8456,16912,31744],[(1,400654),(3,400654),(5,400654),(7,400654),(9,400654),(11,400654),(13,400654),(15,400654),(17,400654),(19,400654),(21,269380),(23,269380),(59,400654),(63,400654),(75,400654),(79,400654),(83,400654),(87,400654),(99,400654),(103,400654),(107,400654),(111,400654),(115,400654),(119,400654),(131,400654),(135,400654),(139,400654),(143,400654),(147,400654),(151,400654),(155,400654),(159,400654),(171,269380),(175,400654),(179,269380),(183,400654),(187,269380),(191,400654),(195,203842),(199,269380),(203,269380),(207,400654)]),([8,31,1057,4228,8456,16912,31744],[(1,400654),(2,0),(3,400654),(5,400654),(7,400654),(9,400654),(11,400654),(13,400654),(15,400654),(17,400654),(19,400654),(21,132298),(23,132298),(59,400654),(63,400654),(75,400654),(79,400654),(83,400654),(87,400654),(99,400654),(103,400654),(107,400654),(111,400654),(115,400654),(119,400654),(131,400654),(135,400654),(139,400654),(143,400654),(147,400654),(151,400654),(155,400654),(159,400654),(169,0),(171,132298),(175,400654),(179,132298),(183,400654),(187,132298),(191,132298),(195,132298),(199,132298),(203,66760),(207,400654)]),([8,31,2114,4228,8456,16912,31744],[(1,400654),(2,0),(3,400654),(5,400654),(7,400654),(9,400654),(11,400654),(13,400654),(15,400654),(17,400654),(19,400654),(21,72898),(23,72898),(59,400654),(63,400654),(75,400654),(79,400654),(83,400654),(87,400654),(99,400654),(103,400654),(107,400654),(111,400654),(115,400654),(119,400654),(131,400654),(135,400654),(139,400654),(143,400654),(147,400654),(151,400654),(155,400654),(159,400654),(175,400654),(179,72898),(183,400654),(187,72898),(191,72898),(195,72898),(199,72898),(203,72898),(207,400654)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_150 : K_150.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((((((((K_0 ++ K_1) ++ (K_2 ++ K_3)) ++ ((K_4 ++ K_5) ++ (K_6 ++ (K_7 ++ K_8)))) ++ (((K_9 ++ K_10) ++ (K_11 ++ K_12)) ++ ((K_13 ++ K_14) ++ (K_15 ++ (K_16 ++ K_17))))) ++ ((((K_18 ++ K_19) ++ (K_20 ++ K_21)) ++ ((K_22 ++ K_23) ++ (K_24 ++ (K_25 ++ K_26)))) ++ (((K_27 ++ K_28) ++ (K_29 ++ (K_30 ++ K_31))) ++ ((K_32 ++ K_33) ++ (K_34 ++ (K_35 ++ K_36)))))) ++ (((((K_37 ++ K_38) ++ (K_39 ++ K_40)) ++ ((K_41 ++ K_42) ++ (K_43 ++ (K_44 ++ K_45)))) ++ (((K_46 ++ K_47) ++ (K_48 ++ (K_49 ++ K_50))) ++ ((K_51 ++ K_52) ++ (K_53 ++ (K_54 ++ K_55))))) ++ ((((K_56 ++ K_57) ++ (K_58 ++ K_59)) ++ ((K_60 ++ K_61) ++ (K_62 ++ (K_63 ++ K_64)))) ++ (((K_65 ++ K_66) ++ (K_67 ++ (K_68 ++ K_69))) ++ ((K_70 ++ K_71) ++ (K_72 ++ (K_73 ++ K_74))))))) ++ ((((((K_75 ++ K_76) ++ (K_77 ++ K_78)) ++ ((K_79 ++ K_80) ++ (K_81 ++ (K_82 ++ K_83)))) ++ (((K_84 ++ K_85) ++ (K_86 ++ (K_87 ++ K_88))) ++ ((K_89 ++ K_90) ++ (K_91 ++ (K_92 ++ K_93))))) ++ ((((K_94 ++ K_95) ++ (K_96 ++ K_97)) ++ ((K_98 ++ K_99) ++ (K_100 ++ (K_101 ++ K_102)))) ++ (((K_103 ++ K_104) ++ (K_105 ++ (K_106 ++ K_107))) ++ ((K_108 ++ K_109) ++ (K_110 ++ (K_111 ++ K_112)))))) ++ (((((K_113 ++ K_114) ++ (K_115 ++ K_116)) ++ ((K_117 ++ K_118) ++ (K_119 ++ (K_120 ++ K_121)))) ++ (((K_122 ++ K_123) ++ (K_124 ++ (K_125 ++ K_126))) ++ ((K_127 ++ K_128) ++ (K_129 ++ (K_130 ++ K_131))))) ++ ((((K_132 ++ K_133) ++ (K_134 ++ K_135)) ++ ((K_136 ++ K_137) ++ (K_138 ++ (K_139 ++ K_140)))) ++ (((K_141 ++ K_142) ++ (K_143 ++ (K_144 ++ K_145))) ++ ((K_146 ++ K_147) ++ (K_148 ++ (K_149 ++ K_150))))))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app (all_app (all_app c_0 c_1) (all_app c_2 c_3)) (all_app (all_app c_4 c_5) (all_app c_6 (all_app c_7 c_8)))) (all_app (all_app (all_app c_9 c_10) (all_app c_11 c_12)) (all_app (all_app c_13 c_14) (all_app c_15 (all_app c_16 c_17))))) (all_app (all_app (all_app (all_app c_18 c_19) (all_app c_20 c_21)) (all_app (all_app c_22 c_23) (all_app c_24 (all_app c_25 c_26)))) (all_app (all_app (all_app c_27 c_28) (all_app c_29 (all_app c_30 c_31))) (all_app (all_app c_32 c_33) (all_app c_34 (all_app c_35 c_36)))))) (all_app (all_app (all_app (all_app (all_app c_37 c_38) (all_app c_39 c_40)) (all_app (all_app c_41 c_42) (all_app c_43 (all_app c_44 c_45)))) (all_app (all_app (all_app c_46 c_47) (all_app c_48 (all_app c_49 c_50))) (all_app (all_app c_51 c_52) (all_app c_53 (all_app c_54 c_55))))) (all_app (all_app (all_app (all_app c_56 c_57) (all_app c_58 c_59)) (all_app (all_app c_60 c_61) (all_app c_62 (all_app c_63 c_64)))) (all_app (all_app (all_app c_65 c_66) (all_app c_67 (all_app c_68 c_69))) (all_app (all_app c_70 c_71) (all_app c_72 (all_app c_73 c_74))))))) (all_app (all_app (all_app (all_app (all_app (all_app c_75 c_76) (all_app c_77 c_78)) (all_app (all_app c_79 c_80) (all_app c_81 (all_app c_82 c_83)))) (all_app (all_app (all_app c_84 c_85) (all_app c_86 (all_app c_87 c_88))) (all_app (all_app c_89 c_90) (all_app c_91 (all_app c_92 c_93))))) (all_app (all_app (all_app (all_app c_94 c_95) (all_app c_96 c_97)) (all_app (all_app c_98 c_99) (all_app c_100 (all_app c_101 c_102)))) (all_app (all_app (all_app c_103 c_104) (all_app c_105 (all_app c_106 c_107))) (all_app (all_app c_108 c_109) (all_app c_110 (all_app c_111 c_112)))))) (all_app (all_app (all_app (all_app (all_app c_113 c_114) (all_app c_115 c_116)) (all_app (all_app c_117 c_118) (all_app c_119 (all_app c_120 c_121)))) (all_app (all_app (all_app c_122 c_123) (all_app c_124 (all_app c_125 c_126))) (all_app (all_app c_127 c_128) (all_app c_129 (all_app c_130 c_131))))) (all_app (all_app (all_app (all_app c_132 c_133) (all_app c_134 c_135)) (all_app (all_app c_136 c_137) (all_app c_138 (all_app c_139 c_140)))) (all_app (all_app (all_app c_141 c_142) (all_app c_143 (all_app c_144 c_145))) (all_app (all_app c_146 c_147) (all_app c_148 (all_app c_149 c_150))))))))


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun (u : Fin 3) (v : Fin 5) => (7541 : ℕ).testBit (5 * u.val + v.val)) C) := by

  rintro ⟨C,hfan,hsize,hr⟩
  let f : BFn 8 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 3 × Fin 5) : f (pt 8 (pairCode p)) = reference (pt 8 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 8 (pairCode (i,j)))) = _
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
  have nc : ∃ x y : Fin 8 → Bool, f x ≠ f y := by
    refine ⟨pt 8 (pairCode (0,0)),pt 8 (pairCode (0,1)),?_⟩
    rw [he (0,0),he (0,1)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 8 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end PEqualNP.Outside.L_meta_20532.Lower

theorem PEqualNP.Outside.L_meta_20532 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun (u : Fin 3) (v : Fin 5) => (7541 : ℕ).testBit (5 * u.val + v.val)) C) := PEqualNP.Outside.L_meta_20532.Lower.lower
