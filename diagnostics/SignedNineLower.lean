import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25035.Lower

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
  (!((x 4 && (x 1 || x 2)) || ((x 5 && (!(x 0 || x 1))) || (x 3 && (x 4 || (x 1 || x 2))))))
def pairInput (i j : Fin 6) := List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)
theorem codeInputs : ∀ p : Fin 6 × Fin 6, List.ofFn (pt 6 (pairCode p)) = pairInput p.1 p.2 := by
  decide +kernel
theorem graphRow : ∀ i j : Fin 6, reference (pt 6 (pairCode (i,j))) =
    (270551487 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel
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

def Y_ : ℕ := 298239

def XS_ : List ℕ := [63, 1986, 30852, 233736, 860688, 1721376]

def PD_ : List (ℕ × ℕ) := [(1, 445056), (2, 372672), (3, 7520), (4, 50224), (5, 43160), (6, 7884), (7, 1510), (8, 2163), (9, 3769), (10, 1500), (11, 110), (12, 183), (13, 219), (14, 109), (15, 54), (16, 27), (17, 13), (18, 6), (19, 3), (20, 1)]

def PM_ : List (ℕ × ℕ) := [(8, 298239), (9, 298239), (12, 298239), (13, 298239), (14, 298239), (16, 298239), (17, 298239), (19, 298239), (20, 298239)]

def G_ : List (List ℕ) := [[0,1,2,4,3,5,6,7,9,8,10,11,13,12,14,18,16,19,15,17,20]]



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

def b0 : List Row := [([3,2047,13056,1786912],[]),([3,2047,78592,1721376],[]),([3,32710,1822984,2056720],[]),([3,67583,78592,1721376],[]),([3,233736,1736646,2056720],[]),([3,233736,1736678,2056720],[]),([4,63,1986,13056,1786912],[]),([4,63,1986,78592,1721376],[]),([4,63,32710,1823016,2056752],[]),([4,63,67522,78592,1721376],[]),([4,63,233736,1736678,2056752],[]),([4,1056,32710,1824040,2057776],[]),([4,1056,233736,1736678,2057776],[]),([4,1087,32710,1824040,2057776],[]),([4,1087,233736,1736678,2057776],[]),([4,1188,233736,1736678,2057776],[]),([4,1215,233736,1736678,2057776],[]),([4,1986,30852,1822984,2056720],[])]
def b1 : List Row := [([4,1986,233736,1735844,2056720],[]),([4,2047,4352,74240,1721376],[]),([4,2047,13056,65536,1721376],[]),([4,2047,30852,1028888,1787874],[]),([4,2047,32710,1028888,1786912],[]),([4,2047,96388,1028888,1722338],[]),([4,2047,98246,1028888,1721376],[]),([4,2047,233736,860688,1734432],[]),([4,2047,233736,860688,1734626],[]),([4,2047,242440,884694,1721376],[]),([4,14335,233736,860688,1734626],[]),([4,15302,233736,376831,860688],[]),([4,16326,233736,376831,860688],[]),([4,16383,233736,860688,1736678],[]),([4,30852,67583,1028888,1787874],[]),([4,30852,233736,1722306,2056720],[]),([4,30852,233736,1722338,2056720],[]),([4,31686,233736,376831,860688],[])]
def t0 : BT := .nd (blockTree b0) [4,1986,233736,1734788,2056720] (blockTree b1)
def b2 : List Row := [([4,32710,102664,376831,860688],[]),([4,32710,233736,376831,860688],[]),([4,32710,233736,376831,1236463],[]),([4,32710,233736,860688,1720320],[]),([4,32710,233736,1236463,1720320],[]),([4,32710,233736,1720320,2056720],[]),([4,32710,233736,1721376,2056720],[]),([4,32742,233736,376831,860688],[]),([4,32742,233736,860688,1720320],[]),([4,32767,233736,877072,1736678],[]),([4,67583,98246,1028888,1721376],[]),([4,233736,362495,860688,1722338],[]),([4,233736,376831,860688,1736678],[]),([4,233736,376831,860688,2064441],[]),([4,233736,860688,1720320,1736646],[(72,0)]),([4,233736,860688,1720320,1736678],[(72,0)]),([4,233736,860688,1720320,2064441],[]),([4,233736,860688,1722338,1734656],[])]
def b3 : List Row := [([5,32,32710,233736,860688,1720352],[]),([5,61,32710,233736,860688,1720352],[]),([5,63,1024,32710,1824040,2057776],[]),([5,63,1024,233736,1736678,2057776],[]),([5,63,1152,233736,1736678,2057776],[]),([5,63,1986,4352,74240,1721376],[]),([5,63,1986,13056,65536,1721376],[]),([5,63,1986,30852,1028888,1787874],[]),([5,63,1986,30852,1823016,2056752],[]),([5,63,1986,32710,1028888,1786912],[]),([5,63,1986,96388,1028888,1722338],[]),([5,63,1986,98246,1028888,1721376],[]),([5,63,1986,233736,860688,1734432],[]),([5,63,1986,233736,860688,1734626],[]),([5,63,1986,233736,1734820,2056752],[]),([5,63,1986,233736,1735844,2056752],[]),([5,63,1986,242440,884694,1721376],[])]
def t1 : BT := .nd (blockTree b2) [5,32,32710,233736,376799,860688] (blockTree b3)
def t2 : BT := .nd t0 [4,32706,233736,860688,1720320] t1
def b4 : List Row := [([5,63,15302,233736,376799,860688],[]),([5,63,16326,233736,376799,860688],[]),([5,63,16326,233736,860688,1736678],[]),([5,63,30852,67522,1028888,1787874],[]),([5,63,30852,233736,1722338,2056752],[]),([5,63,30852,1823016,2056752,2095165],[]),([5,63,31686,233736,376799,860688],[]),([5,63,32710,102664,376799,860688],[]),([5,63,32710,233736,376770,860688],[]),([5,63,32710,233736,376799,860688],[]),([5,63,32710,233736,376799,860735],[]),([5,63,32710,233736,376799,1236463],[]),([5,63,32710,233736,376831,860688],[]),([5,63,32710,233736,860688,1720320],[]),([5,63,32710,233736,860688,1720352],[]),([5,63,32710,233736,860688,1720381],[]),([5,63,32710,233736,860688,1720383],[]),([5,63,32710,233736,860735,1720352],[])]
def b5 : List Row := [([5,63,32710,233736,1236463,1720352],[]),([5,63,32710,233736,1720352,2056752],[]),([5,63,32710,233736,1721376,2056752],[]),([5,63,32710,234760,861712,1721376],[]),([5,63,32767,233736,376799,860688],[]),([5,63,32767,233736,376831,860688],[]),([5,63,32767,233736,860688,1720320],[]),([5,63,32767,233736,860688,1720352],[]),([5,63,67522,98246,1028888,1721376],[]),([5,63,233736,362459,860688,1722338],[]),([5,63,233736,376799,860688,1736678],[]),([5,63,233736,376799,860688,2064441],[]),([5,63,233736,860688,1720352,1736678],[(104,0)]),([5,63,233736,860688,1720352,2064441],[]),([5,63,233736,860688,1722338,1734692],[]),([5,63,233736,1734820,2056752,2095165],[]),([5,63,233736,1735844,2056752,2095165],[]),([5,962,30852,233736,376831,860688],[])]
def t3 : BT := .nd (blockTree b4) [5,63,32710,233736,877072,1736678] (blockTree b5)
def b6 : List Row := [([5,1024,32710,233736,860688,1721344],[(1024,335893),(1024,336917)]),([5,1056,1986,30852,1824040,2057776],[(1024,172074)]),([5,1056,1986,233736,1735844,2057776],[(1024,173165)]),([5,1056,30852,233736,1722338,2057776],[]),([5,1056,32710,233736,375775,860688],[]),([5,1056,32710,233736,860688,1721376],[]),([5,1056,32710,233736,861744,1721376],[(1024,173077),(1024,180245)]),([5,1056,32710,233736,1236463,1721376],[]),([5,1056,32710,233736,1721376,2057776],[]),([5,1056,32742,233736,860688,1721376],[(1024,172053),(1024,173077)]),([5,1056,233736,860688,1721376,1736678],[(104,0)]),([5,1056,233736,860688,1721376,2064441],[]),([5,1087,1986,30852,1824040,2057776],[]),([5,1087,1986,233736,1735844,2057776],[]),([5,1087,30852,233736,1722338,2057776],[]),([5,1087,32710,233736,375775,860688],[]),([5,1087,32710,233736,860688,1721376],[]),([5,1087,32710,233736,860688,1721407],[])]
def b7 : List Row := [([5,1087,32710,233736,861712,1721376],[]),([5,1087,32710,233736,861759,1721376],[]),([5,1087,32710,233736,1236463,1721376],[]),([5,1087,32710,233736,1721376,2057776],[]),([5,1087,32767,233736,860688,1721376],[]),([5,1087,32767,233736,860688,1721407],[(1024,8399),(1024,9423)]),([5,1087,233736,860688,1721376,1736678],[(104,0)]),([5,1087,233736,860688,1721376,2064441],[]),([5,1188,1986,233736,1735844,2057776],[(1024,173165)]),([5,1188,32710,233736,860688,1721376],[]),([5,1188,233736,860688,1721376,1736678],[(104,0)]),([5,1188,233736,860688,1722338,1735844],[]),([5,1215,1986,233736,1735844,2057776],[]),([5,1215,32710,233736,860688,1721376],[]),([5,1215,233736,860688,1721376,1736678],[(104,0)]),([5,1215,233736,860688,1722338,1735844],[]),([5,1320,32710,233736,860688,1721376],[])]
def t4 : BT := .nd (blockTree b6) [5,1087,32710,233736,860735,1721376] (blockTree b7)
def t5 : BT := .nd t3 [5,1024,32710,233736,375807,860688] t4
def t6 : BT := .nd t2 [5,63,14274,233736,860688,1734626] t5
def b8 : List Row := [([5,1519,30852,233736,860688,1722338],[]),([5,1519,30852,233736,1236463,1722338],[]),([5,1519,32710,233736,860688,1721376],[]),([5,1519,32710,233736,1236463,1721376],[]),([5,1535,30852,233736,860688,1722338],[]),([5,1535,30852,233736,1236463,1722338],[]),([5,1535,32710,233736,860688,1721376],[]),([5,1535,32710,233736,1236463,1721376],[]),([5,1915,32710,233736,860688,1721376],[]),([5,1919,30852,233736,860688,1722210],[]),([5,1919,32710,233736,860688,1721376],[]),([5,1919,233736,860688,1722210,2066299],[]),([5,1984,30852,233736,860688,1722304],[]),([5,1984,32708,233736,860688,1721344],[]),([5,1984,32710,233736,860688,1721344],[]),([5,1986,2047,30852,1028888,1786912],[]),([5,1986,2047,96388,1028888,1721376],[]),([5,1986,2047,233736,860688,1733664],[])]
def b9 : List Row := [([5,1986,14340,233736,374847,860688],[(1024,211053)]),([5,1986,14468,233736,376831,860688],[]),([5,1986,15302,233736,375807,860688],[(1024,342121)]),([5,1986,16326,233736,375807,860688],[(1024,342121)]),([5,1986,30720,233736,860688,1720320],[]),([5,1986,30848,233736,860688,1722304],[]),([5,1986,30848,233736,860688,1722306],[]),([5,1986,30852,39423,1824040],[(1024,41290),(1024,106833),(1024,335914),(1024,336937)]),([5,1986,30852,102664,376831,860688],[]),([5,1986,30852,233728,860688,1722304],[]),([5,1986,30852,233728,860688,1722306],[]),([5,1986,30852,233736,374845,860688],[]),([5,1986,30852,233736,374847,860688],[]),([5,1986,30852,233736,374847,1236463],[]),([5,1986,30852,233736,376831,860688],[]),([5,1986,30852,233736,376831,1236463],[]),([5,1986,30852,233736,860688,1720320],[]),([5,1986,30852,233736,860688,1722304],[])]
def t7 : BT := .nd (blockTree b8) [5,1986,2047,1735844,1824040,2057776] (blockTree b9)
def b10 : List Row := [([5,1986,30852,233736,1236463,1720320],[]),([5,1986,30852,233736,1236463,1722304],[]),([5,1986,30852,233736,1236463,1722306],[]),([5,1986,30852,233736,1720320,2056720],[]),([5,1986,30852,233736,1721376,2056720],[]),([5,1986,30852,1824000,2057776],[(1024,140625),(1024,335914),(1024,336937)]),([5,1986,30852,1824008,2057744],[(1024,106833),(1024,335914),(1024,336937)]),([5,1986,30852,1824008,2057776],[(1024,106833),(1024,335914),(1024,336937)]),([5,1986,31686,233736,375807,860688],[]),([5,1986,32704,233736,860688,1721344],[]),([5,1986,32706,233736,860688,1721344],[]),([5,1986,32708,233736,860688,1721344],[]),([5,1986,32710,102664,375807,860688],[]),([5,1986,32710,233728,860688,1721344],[]),([5,1986,32710,233736,374847,860688],[]),([5,1986,32710,233736,375807,860688],[]),([5,1986,32710,233736,375807,1236463],[]),([5,1986,32710,233736,376831,860688],[])]
def b11 : List Row := [([5,1986,32710,233736,860688,1721344],[]),([5,1986,32710,233736,860688,1722304],[]),([5,1986,32710,233736,860688,1722306],[]),([5,1986,32710,233736,1236463,1721344],[]),([5,1986,39423,233736,1735844],[(1024,106830),(1024,110922),(1024,337005)]),([5,1986,233736,360511,860688,1721376],[]),([5,1986,233736,360511,860688,1722338],[]),([5,1986,233736,361343,860688,1722338],[]),([5,1986,233736,361343,2057776],[(1024,106830),(1024,110922),(1024,337005)]),([5,1986,233736,362495,860688,1721376],[]),([5,1986,233736,374847,860688,1735844],[]),([5,1986,233736,374847,860688,1736678],[]),([5,1986,233736,374847,860688,2066299],[]),([5,1986,233736,375807,860688,1736678],[]),([5,1986,233736,375807,860688,2064441],[]),([5,1986,233736,376831,860688,1735844],[]),([5,1986,233736,376831,860688,2066299],[])]
def t8 : BT := .nd (blockTree b10) [5,1986,32710,233736,860688,1720320] (blockTree b11)
def t9 : BT := .nd t7 [5,1986,30852,233736,860688,1722306] t8
def b12 : List Row := [([5,1986,233736,860688,1720320,1735844],[(104,0)]),([5,1986,233736,860688,1720320,2066299],[]),([5,1986,233736,860688,1721344,1736646],[]),([5,1986,233736,860688,1721344,1736678],[]),([5,1986,233736,860688,1721344,2064441],[]),([5,1986,233736,860688,1721376,1734656],[]),([5,1986,233736,860688,1721376,1734788],[]),([5,1986,233736,860688,1721376,1736640],[]),([5,1986,233736,860688,1721376,1736642],[]),([5,1986,233736,860688,1721376,1736644],[]),([5,1986,233736,860688,1721376,1736646],[]),([5,1986,233736,860688,1722304,1735844],[]),([5,1986,233736,860688,1722304,1736644],[]),([5,1986,233736,860688,1722304,1736678],[]),([5,1986,233736,860688,1722304,2066299],[]),([5,1986,233736,860688,1722306,1735812],[]),([5,1986,233736,860688,1722306,1735844],[]),([5,1986,233736,860688,1722306,1736646],[])]
def b13 : List Row := [([5,1986,233736,860688,1722338,1735808],[]),([5,1986,233736,860688,1722338,1735812],[]),([5,1986,233736,860688,1722338,1736640],[]),([5,1986,233736,860688,1722338,1736644],[]),([5,1986,233736,1735808,2057776],[(1024,106830),(1024,110922),(1024,337005)]),([5,1986,233736,1735812,2057744],[(1024,106830),(1024,110922),(1024,337005)]),([5,1986,233736,1735812,2057776],[(1024,106830),(1024,110922),(1024,337005)]),([5,1986,233736,1735844,2057728],[(1024,106830),(1024,110922),(1024,337005)]),([5,1986,233736,1735844,2057744],[(1024,106830),(1024,110922),(1024,337005)]),([5,2018,30852,233736,374813,860688],[]),([5,2018,30852,233736,376831,860688],[]),([5,2018,30852,233736,860688,1720320],[]),([5,2018,30852,233736,860688,1722338],[]),([5,2018,30852,233736,1236463,1722338],[]),([5,2018,30852,1824040,2057776],[(1024,106673),(1024,172074),(1024,173097)]),([5,2018,30884,233736,860688,1722338],[]),([5,2018,30886,233736,860688,1722338],[])]
def t10 : BT := .nd (blockTree b12) [5,1986,233736,860688,1722306,2066299] (blockTree b13)
def b14 : List Row := [([5,2018,32710,233736,860688,1721376],[]),([5,2018,32710,233736,860688,1722338],[]),([5,2018,32710,233736,860720,1721376],[]),([5,2018,32710,233736,1236463,1721376],[]),([5,2018,32742,233736,375775,860688],[]),([5,2018,32742,233736,860688,1721376],[]),([5,2018,32742,233736,860688,1722338],[]),([5,2018,32742,233736,1236463,1721376],[]),([5,2018,233736,860688,1721376,1736678],[]),([5,2018,233736,860688,1721376,2064409],[]),([5,2018,233736,860688,1721376,2064441],[]),([5,2018,233736,860688,1722338,1735844],[]),([5,2018,233736,860688,1722338,1736678],[]),([5,2018,233736,860688,1722338,2066299],[]),([5,2018,233736,1735844,2057776],[(1024,106670),(1024,110762),(1024,173165)]),([5,2022,30852,233736,860688,1722338],[]),([5,2022,30852,233736,860688,1722342],[]),([5,2022,32710,233736,860688,1721376],[])]
def b15 : List Row := [([5,2022,233736,860688,1721376,1736678],[]),([5,2022,233736,860688,1722338,1735844],[]),([5,2022,233736,860688,1722338,1736678],[]),([5,2022,233736,860688,1722342,1735844],[]),([5,2022,233736,1735844,2057776],[(1024,106670),(1024,110762),(1024,173165)]),([5,2026,30852,233736,860688,1722338],[]),([5,2026,32710,233736,860688,1721376],[]),([5,2031,30852,233736,860688,1722338],[]),([5,2031,30852,233736,1236463,1722338],[]),([5,2031,32710,233736,860688,1721376],[]),([5,2031,32710,233736,1236463,1721376],[]),([5,2043,30852,233736,860688,1722338],[]),([5,2043,32710,233736,860688,1721376],[]),([5,2043,233736,860688,1721376,2064441],[]),([5,2043,233736,860688,1722338,2066299],[]),([5,2047,4352,262094,860688,1721376],[(104,0)]),([5,2047,12288,233736,860688,1722338],[])]
def t11 : BT := .nd (blockTree b14) [5,2022,32742,233736,860688,1721376] (blockTree b15)
def t12 : BT := .nd t10 [5,2018,32710,233736,375775,860688] t11
def t13 : BT := .nd t9 [5,1986,233736,860688,1720320,1734788] t12
def t14 : BT := .nd t6 [5,1343,32710,233736,860688,1721376] t13
def b16 : List Row := [([5,2047,14274,233736,860688,1721376],[]),([5,2047,14340,233736,374813,860688],[]),([5,2047,14340,233736,860688,1722338],[]),([5,2047,14468,233736,860688,1722338],[]),([5,2047,15302,233736,375775,860688],[]),([5,2047,15302,233736,860688,1721376],[]),([5,2047,16326,233736,375775,860688],[]),([5,2047,16326,233736,860688,1721376],[]),([5,2047,30720,233736,860688,1722338],[]),([5,2047,30724,233736,860688,1722338],[]),([5,2047,30848,233736,860688,1722338],[]),([5,2047,30852,65536,1028888,1722338],[]),([5,2047,30852,67522,1028888,1721376],[]),([5,2047,30852,102664,860688,1722338],[]),([5,2047,30852,233728,860688,1722338],[]),([5,2047,30852,233736,374813,860688],[]),([5,2047,30852,233736,374813,1236463],[]),([5,2047,30852,233736,374847,860688],[])]
def b17 : List Row := [([5,2047,30852,233736,860688,1722210],[]),([5,2047,30852,233736,860688,1722304],[]),([5,2047,30852,233736,860688,1722306],[]),([5,2047,30852,233736,860688,1722336],[]),([5,2047,30852,233736,860688,1722338],[]),([5,2047,30852,233736,860688,1722342],[]),([5,2047,30852,233736,860688,1726434],[]),([5,2047,30852,233736,860688,1787874],[]),([5,2047,30852,233736,860692,1722338],[]),([5,2047,30852,233736,860696,1722338],[]),([5,2047,30852,233736,860944,1722338],[]),([5,2047,30852,233736,860952,1722338],[]),([5,2047,30852,233736,864784,1722338],[]),([5,2047,30852,233736,877072,1722338],[]),([5,2047,30852,233736,991760,1722338],[]),([5,2047,30852,233736,992016,1722338],[]),([5,2047,30852,233736,1236463,1722338],[]),([5,2047,30852,233736,1236479,1722338],[])]
def t15 : BT := .nd (blockTree b16) [5,2047,30852,233736,860688,1722144] (blockTree b17)
def b18 : List Row := [([5,2047,30852,234248,862162,1721376],[]),([5,2047,30852,1236463,1722338,1863415],[]),([5,2047,30852,1824063,2057791],[(1024,8394),(1024,9417),(1024,499729)]),([5,2047,30854,233736,860688,1722338],[]),([5,2047,30860,233736,860688,1722338],[]),([5,2047,30884,233736,860688,1722338],[]),([5,2047,30886,233736,860688,1722338],[]),([5,2047,30911,233736,374813,860688],[]),([5,2047,30911,233736,860688,1722338],[]),([5,2047,30911,233736,1236463,1722338],[]),([5,2047,30911,1824040,2057776],[(1024,336074),(1024,337097),(1024,499821),(1024,503913)]),([5,2047,31108,233736,860688,1722338],[]),([5,2047,31116,233736,860688,1722338],[]),([5,2047,31620,233736,860688,1721376],[]),([5,2047,31686,233736,375775,860688],[]),([5,2047,31686,233736,860688,1721376],[]),([5,2047,31876,233736,860688,1722338],[]),([5,2047,31908,233736,860688,1722338],[])]
def b19 : List Row := [([5,2047,32706,233736,860688,1721376],[]),([5,2047,32708,233736,860688,1721376],[]),([5,2047,32710,65536,1028888,1721376],[]),([5,2047,32710,69888,860688,1721376],[(108,0)]),([5,2047,32710,102664,375775,860688],[]),([5,2047,32710,102664,860688,1721376],[]),([5,2047,32710,233728,860688,1721376],[]),([5,2047,32710,233736,374784,860688],[]),([5,2047,32710,233736,374813,860688],[]),([5,2047,32710,233736,375744,860688],[]),([5,2047,32710,233736,375775,860688],[]),([5,2047,32710,233736,375775,1236463],[]),([5,2047,32710,233736,375807,860688],[]),([5,2047,32710,233736,376799,860688],[]),([5,2047,32710,233736,376831,860688],[]),([5,2047,32710,233736,860688,1720320],[]),([5,2047,32710,233736,860688,1720352],[])]
def t16 : BT := .nd (blockTree b18) [5,2047,32704,233736,860688,1721376] (blockTree b19)
def t17 : BT := .nd t15 [5,2047,30852,233736,1722338,1760751] t16
def b20 : List Row := [([5,2047,32710,233736,860688,1721376],[]),([5,2047,32710,233736,860688,1721378],[]),([5,2047,32710,233736,860688,1721380],[]),([5,2047,32710,233736,860688,1721382],[]),([5,2047,32710,233736,860688,1721384],[]),([5,2047,32710,233736,860688,1721407],[]),([5,2047,32710,233736,860688,1721504],[]),([5,2047,32710,233736,860688,1721508],[]),([5,2047,32710,233736,860688,1721632],[]),([5,2047,32710,233736,860688,1721640],[]),([5,2047,32710,233736,860688,1722338],[]),([5,2047,32710,233736,860688,1722342],[]),([5,2047,32710,233736,860688,1722367],[]),([5,2047,32710,233736,860688,1725472],[]),([5,2047,32710,233736,860688,1725728],[]),([5,2047,32710,233736,860688,1786912],[]),([5,2047,32710,233736,860696,1721376],[]),([5,2047,32710,233736,860720,1721376],[])]
def b21 : List Row := [([5,2047,32710,233736,860952,1721376],[]),([5,2047,32710,233736,864784,1721376],[]),([5,2047,32710,233736,865040,1721376],[(80,0)]),([5,2047,32710,233736,877072,1721376],[]),([5,2047,32710,233736,991760,1721376],[]),([5,2047,32710,233736,1236463,1721376],[]),([5,2047,32710,233736,1236463,1721407],[]),([5,2047,32710,233736,1236463,1722338],[]),([5,2047,32710,233736,1236463,1722367],[]),([5,2047,32710,233736,1236479,1721376],[]),([5,2047,32710,233736,1721376,1760751],[]),([5,2047,32710,1236463,1721376,1863415],[]),([5,2047,32710,1721376,1824040,2057776],[(1024,172074),(1024,335914)]),([5,2047,32710,1824040,2057776],[(1024,335914),(1024,336937)]),([5,2047,32742,233736,860688,1721376],[]),([5,2047,32742,233736,860688,1722338],[]),([5,2047,32767,233736,374813,860688],[]),([5,2047,32767,233736,860688,1722338],[])]
def t18 : BT := .nd (blockTree b20) [5,2047,32710,233736,860944,1721376] (blockTree b21)
def b22 : List Row := [([5,2047,96388,233736,860688,1722338],[]),([5,2047,98246,233736,860688,1721376],[]),([5,2047,161924,233736,860688,1722338],[]),([5,2047,162180,233736,860688,1722338],[]),([5,2047,163782,233736,860688,1721376],[]),([5,2047,233736,360473,860688,1721376],[]),([5,2047,233736,360473,860688,1722338],[]),([5,2047,233736,361307,860688,1722338],[]),([5,2047,233736,374813,860688,1735844],[]),([5,2047,233736,374813,860688,1736678],[]),([5,2047,233736,374813,860688,2066299],[]),([5,2047,233736,375775,860688,1736678],[]),([5,2047,233736,375775,860688,2064441],[]),([5,2047,233736,860688,1721376,1736678],[]),([5,2047,233736,860688,1721376,2064441],[]),([5,2047,233736,860688,1721376,2064447],[]),([5,2047,233736,860688,1721376,2081849],[]),([5,2047,233736,860688,1721407,1736678],[])]
def b23 : List Row := [([5,2047,233736,860688,1722210,2066299],[]),([5,2047,233736,860688,1722338,1735844],[]),([5,2047,233736,860688,1722338,1735871],[]),([5,2047,233736,860688,1722338,1736678],[]),([5,2047,233736,860688,1722338,1736703],[]),([5,2047,233736,860688,1722338,2064384],[]),([5,2047,233736,860688,1722338,2064441],[]),([5,2047,233736,860688,1722338,2066240],[]),([5,2047,233736,860688,1722338,2066299],[]),([5,2047,233736,860688,1722338,2066303],[]),([5,2047,233736,860688,1722338,2066427],[]),([5,2047,233736,860688,1722338,2066431],[]),([5,2047,233736,860688,1722338,2082683],[]),([5,2047,233736,860688,1722338,2082811],[]),([5,2047,233736,860688,1722367,1736678],[]),([5,2047,233736,860688,1722367,2064441],[]),([5,2047,233736,860688,1736678,1824040],[])]
def t19 : BT := .nd (blockTree b22) [5,2047,233736,860688,1721407,2064441] (blockTree b23)
def t20 : BT := .nd t18 [5,2047,32767,233736,1236463,1722338] t19
def t21 : BT := .nd t17 [5,2047,32710,233736,860688,1721344] t20
def b24 : List Row := [([5,2047,233736,1236463,1721376,1736678],[]),([5,2047,233736,1236463,1721376,2064441],[]),([5,2047,233736,1236463,1722338,1735844],[]),([5,2047,233736,1236463,1722338,1736678],[]),([5,2047,233736,1236463,1722338,2066299],[]),([5,2047,233736,1721376,1736678,2057776],[(1024,172074)]),([5,2047,233736,1735844,1736678,2057776],[(1024,173165)]),([5,2047,233736,1735871,2057776],[(1024,106989),(1024,499821),(1024,503913)]),([5,2047,233736,1735871,2057791],[(1024,9709),(1024,499726),(1024,503818)]),([5,6143,30852,233736,860688,1722338],[]),([5,6143,30852,233736,860688,1726434],[]),([5,6143,32710,233736,860688,1721376],[]),([5,14274,14335,233736,860688,1721376],[]),([5,16326,16383,233736,375775,860688],[]),([5,16326,16383,233736,860688,1721376],[]),([5,16326,233736,375807,860688],[(1024,106831),(1024,342121)]),([5,16384,32767,233736,860688,1736678],[(72,0)]),([5,30720,233736,860688,1722338,2095104],[])]
def b25 : List Row := [([5,30852,32710,233736,860688,1720320],[]),([5,30852,67522,67583,1028888,1721376],[]),([5,30852,67583,233736,860688,1722338],[]),([5,30852,67583,233736,860688,1787874],[]),([5,30852,133090,233736,860688,1722338],[]),([5,30852,133119,233736,860688,1722338],[]),([5,30852,233736,235466,374847,860688],[]),([5,30852,233736,235466,860688,1722304],[]),([5,30852,233736,235466,860688,1722306],[]),([5,30852,233736,235498,860688,1722338],[]),([5,30852,233736,235519,374813,860688],[]),([5,30852,233736,235519,860688,1722338],[]),([5,30852,233736,235519,1236463,1722338],[]),([5,30852,233736,374813,376831,860688],[]),([5,30852,233736,374813,860688,2095104],[]),([5,30852,233736,374845,860688,2095165],[]),([5,30852,233736,374847,376799,860688],[]),([5,30852,233736,374847,376831,860688],[])]
def t22 : BT := .nd (blockTree b24) [5,30852,32710,233736,376831,860688] (blockTree b25)
def b26 : List Row := [([5,30852,233736,376831,860688,1722338],[]),([5,30852,233736,376831,860688,2095165],[]),([5,30852,233736,860688,1030143,1722338],[]),([5,30852,233736,860688,1234944,1722338],[]),([5,30852,233736,860688,1720320,1722306],[(104,0)]),([5,30852,233736,860688,1720320,1722338],[(104,0)]),([5,30852,233736,860688,1720320,2095133],[]),([5,30852,233736,860688,1720320,2095165],[]),([5,30852,233736,860688,1720320,2095167],[]),([5,30852,233736,860688,1722304,2095165],[]),([5,30852,233736,860688,1722306,2095104],[]),([5,30852,233736,860688,1722306,2095165],[]),([5,30852,233736,860688,1722338,2095104],[]),([5,30852,233736,860688,1722338,2095133],[]),([5,30852,233736,860688,1722338,2095368],[]),([5,30852,233736,862207,1236463,1722338],[]),([5,30852,233736,1236463,1722338,2095104],[]),([5,30911,32710,233736,376799,860688],[])]
def b27 : List Row := [([5,30911,32710,1824040,2057776],[(1024,110929),(1024,335914),(1024,335918),(1024,336941),(1024,342193)]),([5,30911,233736,860688,1722338,2095104],[]),([5,32706,233736,860688,1721376,2095104],[]),([5,32710,32767,233736,376799,860688],[]),([5,32710,32767,233736,860688,1720352],[]),([5,32710,32767,233736,877072,1721376],[]),([5,32710,67583,233736,860688,1721376],[]),([5,32710,132128,233736,860688,1721376],[]),([5,32710,132159,233736,860688,1721376],[]),([5,32710,133090,233736,860688,1721376],[]),([5,32710,133119,233736,860688,1721376],[]),([5,32710,233736,233791,376799,860688],[]),([5,32710,233736,233791,860688,1720352],[]),([5,32710,233736,234792,860688,1721376],[]),([5,32710,233736,234815,860688,1721376],[]),([5,32710,233736,235466,375807,860688],[]),([5,32710,233736,235466,860688,1721344],[])]
def t23 : BT := .nd (blockTree b26) [5,30911,32710,233736,860688,1720352] (blockTree b27)
def t24 : BT := .nd t22 [5,30852,233736,374847,860688,2095165] t23
def b28 : List Row := [([5,32710,233736,235519,375775,860688],[]),([5,32710,233736,235519,860688,1721376],[]),([5,32710,233736,235519,860688,1722338],[]),([5,32710,233736,235519,1236463,1721376],[]),([5,32710,233736,375775,376831,860688],[(148,0)]),([5,32710,233736,375775,860688,2095104],[]),([5,32710,233736,375807,376799,860688],[(1024,342121)]),([5,32710,233736,375807,376831,860688],[(148,0),(1024,342121)]),([5,32710,233736,375807,860688,2095165],[]),([5,32710,233736,376799,376831,860688],[(148,0)]),([5,32710,233736,376799,860688,2097088],[]),([5,32710,233736,376831,860688],[(6,0),(118,0)]),([5,32710,233736,376831,860688,1721376],[]),([5,32710,233736,860688,1030143,1721376],[]),([5,32710,233736,860688,1234944,1721376],[]),([5,32710,233736,860688,1720320],[(6,0),(105,0)]),([5,32710,233736,860688,1720320,1721376],[(104,0)]),([5,32710,233736,860688,1720320,2095104],[])]
def b29 : List Row := [([5,32710,233736,860688,1721344,2095165],[]),([5,32710,233736,860688,1721376,2095104],[]),([5,32710,233736,860688,1721376,2095133],[]),([5,32710,233736,860688,1721376,2095236],[]),([5,32710,233736,860688,1721376,2095368],[]),([5,32710,233736,860688,1721376,2096064],[]),([5,32710,233736,860688,1721376,2096095],[]),([5,32710,233736,860688,1721407,2095104],[]),([5,32710,233736,860688,1722338,2095104],[]),([5,32710,233736,860688,1722367,2095104],[]),([5,32710,233736,862207,1236463,1721376],[]),([5,32710,233736,1236463,1721376,2095104],[]),([5,32742,233736,235498,860688,1721376],[]),([5,32742,233736,860688,1721376,2095133],[]),([5,32767,233736,860688,1722338,2095104],[]),([5,67583,98246,233736,860688,1721376],[]),([5,133090,163814,233736,860688,1721376],[])]
def t25 : BT := .nd (blockTree b28) [5,32710,233736,860688,1720352,2097088] (blockTree b29)
def b30 : List Row := [([5,233736,235519,860688,1721376,1736678],[]),([5,233736,235519,860688,1721376,2064441],[]),([5,233736,235519,860688,1722338,1735844],[]),([5,233736,235519,860688,1722338,1736678],[]),([5,233736,235519,860688,1722338,2066299],[]),([5,233736,860688,1721376,1736678,2095104],[]),([5,233736,860688,1721376,2064441,2095104],[]),([5,233736,860688,1722338,1735844,2095104],[]),([5,233736,860688,1722338,1736678,2095104],[]),([5,233736,860688,1722338,2066299,2095104],[]),([6,2,2047,30852,233736,860688,1722338],[]),([6,2,2047,32710,233736,860688,1721376],[]),([6,4,2047,30852,233736,860688,1722338],[(96,0)]),([6,4,2047,32710,233736,860688,1721376],[]),([6,6,2047,32710,233736,860688,1721376],[]),([6,8,2047,30852,233736,860688,1722338],[]),([6,8,2047,32710,233736,860688,1721376],[]),([6,32,1024,32710,233736,860688,1721376],[(1024,335893),(1024,336917)])]
def b31 : List Row := [([6,32,1986,30852,233736,376799,860688],[(1024,184425)]),([6,32,1986,30852,233736,860688,1720352],[(1024,184425)]),([6,32,1986,30852,233736,860688,1722338],[]),([6,32,1986,30852,233736,860720,1722338],[(1024,177173),(1024,180245)]),([6,32,1986,30852,233736,1236463,1722338],[]),([6,32,1986,30852,1824040,2057776],[(1024,106833),(1024,335914),(1024,336937)]),([6,32,1986,30884,233736,860688,1722338],[(1024,176149),(1024,177173)]),([6,32,1986,32710,233736,375775,860688],[]),([6,32,1986,32710,233736,860688,1721376],[]),([6,32,1986,32710,233736,860688,1722338],[]),([6,32,1986,32710,233736,860720,1721376],[(1024,177173),(1024,180245)]),([6,32,1986,32710,233736,1236463,1721376],[]),([6,32,1986,32742,233736,860688,1721376],[(1024,176149),(1024,177173)]),([6,32,1986,233736,860688,1721376,1736678],[]),([6,32,1986,233736,860688,1721376,2064441],[]),([6,32,1986,233736,860688,1722338,1735844],[]),([6,32,1986,233736,860688,1722338,1736678],[])]
def t26 : BT := .nd (blockTree b30) [6,32,1986,30852,233736,374813,860688] (blockTree b31)
def t27 : BT := .nd t25 [5,133119,163782,233736,860688,1721376] t26
def t28 : BT := .nd t24 [5,32710,233736,235498,860688,1721376] t27
def t29 : BT := .nd t21 [5,2047,233736,860688,1736678,1824746] t28
def t30 : BT := .nd t14 [5,2047,13056,233736,860688,1721376] t29
def b32 : List Row := [([6,32,1986,233736,1735844,2057776],[(1024,106830),(1024,110922),(1024,337005)]),([6,32,2018,30852,233736,860688,1722338],[]),([6,32,2018,32710,233736,860688,1721376],[(96,0)]),([6,32,2018,32742,233736,860688,1721376],[(1024,172053),(1024,173077)]),([6,32,2047,30852,233736,860688,1722338],[]),([6,32,2047,32710,233736,860688,1721376],[(96,0)]),([6,32,30852,233736,235466,860688,1722338],[(1024,53417)]),([6,32,30852,233736,860688,1720352,2095165],[]),([6,32,30852,233736,860688,1722338,2095165],[]),([6,32,32710,233736,235466,860688,1721376],[(1024,342194)]),([6,32,32710,233736,860688,1721376,2095165],[]),([6,34,1986,30852,233736,374813,860688],[]),([6,34,1986,30852,233736,860688,1722338],[]),([6,34,1986,30852,233736,860722,1722338],[(1024,177173),(1024,180245)]),([6,34,1986,30852,233736,1236463,1722338],[]),([6,34,1986,30886,233736,860688,1722338],[(1024,176149),(1024,177173)]),([6,34,1986,32710,233736,860688,1721376],[]),([6,34,1986,32710,233736,860688,1722338],[])]
def b33 : List Row := [([6,34,1986,233736,860688,1722338,1735844],[]),([6,34,1986,233736,860688,1722338,1736678],[]),([6,34,1986,233736,860688,1722338,2066299],[]),([6,34,2018,30852,233736,860688,1722338],[]),([6,34,2047,30852,233736,860688,1722338],[]),([6,34,30852,233736,235466,860688,1722338],[]),([6,34,30852,233736,860688,1722338,2095165],[]),([6,36,1986,30852,233736,860688,1722338],[]),([6,36,1986,32710,233736,860688,1721376],[]),([6,36,1986,233736,860688,1721376,1736678],[]),([6,36,1986,233736,860688,1722338,1735844],[]),([6,36,1986,233736,1735844,2057776],[(1024,106830),(1024,110922),(1024,337005)]),([6,38,1986,30852,233736,860688,1722338],[]),([6,38,1986,32710,233736,860688,1721376],[]),([6,38,1986,233736,860688,1721376,1736678],[]),([6,38,1986,233736,860688,1722338,1736678],[]),([6,40,1986,30852,233736,860688,1722338],[]),([6,40,1986,30852,1824040,2057776],[(1024,140625),(1024,335914),(1024,336937)])]
def t31 : BT := .nd (blockTree b32) [6,34,1986,233736,860688,1721376,1736678] (blockTree b33)
def b34 : List Row := [([6,40,1986,860688,1735844,1824040],[(1024,140621),(1024,144713),(1024,335981),(1024,336014)]),([6,42,1986,30852,233736,860688,1722338],[]),([6,47,1986,30852,233736,860688,1722338],[]),([6,47,1986,30852,233736,1236463,1722338],[]),([6,47,1986,32710,233736,860688,1721376],[]),([6,47,1986,32710,233736,1236463,1721376],[]),([6,57,1986,32710,233736,860688,1721376],[]),([6,57,1986,233736,860688,1721376,2064441],[]),([6,59,1986,30852,233736,860688,1722338],[]),([6,59,1986,32710,233736,860688,1721376],[]),([6,59,1986,233736,860688,1722338,2066299],[]),([6,61,1986,30852,233736,860688,1720352],[]),([6,61,1986,30852,233736,860688,1722338],[]),([6,61,1986,32710,233736,860688,1721376],[]),([6,61,30852,233736,860688,1720352,2095165],[]),([6,61,30852,233736,860688,1722338,2095165],[]),([6,61,32710,233736,860688,1721376,2095165],[]),([6,63,962,30852,233736,376799,860688],[])]
def b35 : List Row := [([6,63,1024,1986,233736,1735844,2057776],[(1024,337389),(1024,345577)]),([6,63,1024,30852,233736,1722338,2057776],[]),([6,63,1024,32710,233736,375775,860688],[(1024,211273),(1024,342218)]),([6,63,1024,32710,233736,860688,1721376],[(1024,336079),(1024,337103)]),([6,63,1024,32710,233736,860688,1721407],[(1024,336079),(1024,337103)]),([6,63,1024,32710,233736,860735,1721376],[(1024,336079),(1024,337103)]),([6,63,1024,32710,233736,861712,1721376],[(1024,337103)]),([6,63,1024,32710,233736,1236463,1721376],[(1024,336079)]),([6,63,1024,32710,233736,1721376,2057776],[(1024,342217)]),([6,63,1024,32767,233736,860688,1721376],[(1024,336079),(1024,337103)]),([6,63,1024,233736,860688,1721376,1736678],[(144,0)]),([6,63,1024,233736,860688,1721376,2064441],[(1024,500050),(1024,500052)]),([6,63,1026,32710,233736,860688,1721376],[(1024,336079),(1024,337103)]),([6,63,1026,32710,233736,860688,1721407],[(1024,336079),(1024,337103)]),([6,63,1056,32710,233736,860688,1721376],[(1024,336079),(1024,337103)]),([6,63,1056,32767,233736,860688,1721376],[(1024,336079),(1024,337103)]),([6,63,1087,32710,233736,860688,1721376],[(96,0),(1024,336079),(1024,337103)])]
def t32 : BT := .nd (blockTree b34) [6,63,1024,1986,30852,1824040,2057776] (blockTree b35)
def t33 : BT := .nd t31 [6,40,1986,32710,233736,860688,1721376] t32
def b36 : List Row := [([6,63,1152,32710,233736,860688,1721376],[]),([6,63,1152,233736,860688,1721376,1736678],[(144,0)]),([6,63,1152,233736,860688,1722338,1735844],[]),([6,63,1280,32710,233736,860688,1721376],[(1024,336079),(1024,337103)]),([6,63,1474,30852,233736,860688,1722338],[]),([6,63,1474,30852,233736,1236463,1722338],[]),([6,63,1474,32710,233736,860688,1721376],[]),([6,63,1474,32710,233736,1236463,1721376],[]),([6,63,1858,30852,233736,860688,1722210],[]),([6,63,1858,32710,233736,860688,1721376],[]),([6,63,1858,233736,860688,1722210,2066299],[]),([6,63,1984,30852,233736,860688,1722336],[]),([6,63,1984,30852,233736,860688,1722338],[]),([6,63,1984,32708,233736,860688,1721376],[]),([6,63,1984,32710,233736,860688,1721376],[]),([6,63,1986,4352,262094,860688,1721376],[(144,0)]),([6,63,1986,12288,233736,860688,1722338],[(1024,211437)]),([6,63,1986,13056,233736,860688,1721376],[(1024,342505)])]
def b37 : List Row := [([6,63,1986,14340,233736,374813,860688],[(1024,211437)]),([6,63,1986,14340,233736,860688,1722338],[(1024,211437)]),([6,63,1986,14468,233736,376799,860688],[]),([6,63,1986,14468,233736,860688,1722338],[(1024,211437)]),([6,63,1986,15302,233736,375775,860688],[(1024,342505)]),([6,63,1986,15302,233736,860688,1721376],[(1024,342505)]),([6,63,1986,16326,233736,375775,860688],[(1024,342505)]),([6,63,1986,16326,233736,860688,1721376],[(1024,211437),(1024,342505)]),([6,63,1986,30724,233736,860688,1720352],[]),([6,63,1986,30724,233736,860688,1722338],[]),([6,63,1986,30848,233736,860688,1722338],[]),([6,63,1986,30852,39375,1824040],[(1024,205130),(1024,336074),(1024,336937),(1024,336973),(1024,337097),(1024,500049)]),([6,63,1986,30852,65536,1028888,1722338],[(1024,217585)]),([6,63,1986,30852,67522,1028888,1721376],[(1024,217585),(1024,342513),(1024,348649)]),([6,63,1986,30852,102664,376799,860688],[]),([6,63,1986,30852,102664,860688,1722338],[]),([6,63,1986,30852,233728,860688,1722338],[]),([6,63,1986,30852,233736,374784,860688],[])]
def t34 : BT := .nd (blockTree b36) [6,63,1986,14274,233736,860688,1721376] (blockTree b37)
def b38 : List Row := [([6,63,1986,30852,233736,374813,860735],[]),([6,63,1986,30852,233736,374813,1236463],[]),([6,63,1986,30852,233736,374847,860688],[]),([6,63,1986,30852,233736,376770,860688],[(1024,374889)]),([6,63,1986,30852,233736,376799,860688],[]),([6,63,1986,30852,233736,376799,860735],[]),([6,63,1986,30852,233736,376799,1236463],[]),([6,63,1986,30852,233736,376831,860688],[]),([6,63,1986,30852,233736,860688,1720320],[]),([6,63,1986,30852,233736,860688,1720352],[]),([6,63,1986,30852,233736,860688,1720381],[(1024,106863)]),([6,63,1986,30852,233736,860688,1720383],[(1024,106863)]),([6,63,1986,30852,233736,860688,1722144],[]),([6,63,1986,30852,233736,860688,1722210],[]),([6,63,1986,30852,233736,860688,1722304],[]),([6,63,1986,30852,233736,860688,1722306],[]),([6,63,1986,30852,233736,860688,1722336],[]),([6,63,1986,30852,233736,860688,1722338],[])]
def b39 : List Row := [([6,63,1986,30852,233736,860688,1722346],[]),([6,63,1986,30852,233736,860688,1722367],[]),([6,63,1986,30852,233736,860688,1726434],[]),([6,63,1986,30852,233736,860688,1787874],[]),([6,63,1986,30852,233736,860690,1722338],[]),([6,63,1986,30852,233736,860692,1722338],[]),([6,63,1986,30852,233736,860696,1722338],[]),([6,63,1986,30852,233736,860720,1722338],[]),([6,63,1986,30852,233736,860722,1722338],[]),([6,63,1986,30852,233736,860735,1720352],[]),([6,63,1986,30852,233736,860735,1722338],[]),([6,63,1986,30852,233736,860735,1722367],[(1024,13679),(1024,16751)]),([6,63,1986,30852,233736,860944,1722338],[]),([6,63,1986,30852,233736,864784,1722338],[]),([6,63,1986,30852,233736,877072,1722338],[(1024,217581)]),([6,63,1986,30852,233736,991760,1722338],[]),([6,63,1986,30852,233736,992016,1722338],[(1024,242031)])]
def t35 : BT := .nd (blockTree b38) [6,63,1986,30852,233736,860688,1722342] (blockTree b39)
def t36 : BT := .nd t34 [6,63,1986,30852,233736,374813,860688] t35
def t37 : BT := .nd t33 [6,63,1152,1986,233736,1735844,2057776] t36
def b40 : List Row := [([6,63,1986,30852,233736,1236463,1720352],[]),([6,63,1986,30852,233736,1236463,1722338],[]),([6,63,1986,30852,233736,1236463,1722367],[]),([6,63,1986,30852,233736,1236479,1722338],[]),([6,63,1986,30852,233736,1720352,2056752],[]),([6,63,1986,30852,233736,1721376,2056752],[]),([6,63,1986,30852,233736,1722338,1760751],[]),([6,63,1986,30852,233791,860735,1722338],[(1024,12490),(1024,16751),(1024,41162)]),([6,63,1986,30852,233791,1236463,1722338],[]),([6,63,1986,30852,234248,862162,1721376],[]),([6,63,1986,30852,234760,861712,1721376],[]),([6,63,1986,30852,1028888,1786912],[(1024,336369),(1024,342505),(1024,348265),(1024,348649),(1024,500053)]),([6,63,1986,30852,1236463,1722338,1863415],[]),([6,63,1986,30852,1824040,2057776],[(1024,335914),(1024,335950),(1024,336074),(1024,337097),(1024,500049)]),([6,63,1986,30852,1824040,2057791],[(1024,336074),(1024,337097),(1024,500049)]),([6,63,1986,30852,1824063,2057791],[(1024,41162),(1024,336074),(1024,337097),(1024,500049)]),([6,63,1986,30854,233736,860688,1722338],[]),([6,63,1986,30860,233736,860688,1722338],[])]
def b41 : List Row := [([6,63,1986,30886,233736,860688,1722338],[]),([6,63,1986,30911,233736,374813,860688],[]),([6,63,1986,30911,233736,376799,860688],[(1024,106989)]),([6,63,1986,30911,233736,860688,1720352],[(1024,106989)]),([6,63,1986,30911,233736,860688,1722338],[]),([6,63,1986,30911,233736,860688,1722367],[(1024,12655),(1024,13679),(1024,106989)]),([6,63,1986,30911,233736,860735,1722338],[(1024,12490),(1024,13679),(1024,42477)]),([6,63,1986,30911,233736,1236463,1722338],[]),([6,63,1986,30911,1824040,2057776],[(1024,336074),(1024,337097),(1024,500049)]),([6,63,1986,31108,233736,860688,1722338],[]),([6,63,1986,31620,233736,860688,1721376],[]),([6,63,1986,31686,233736,375775,860688],[]),([6,63,1986,31686,233736,860688,1721376],[]),([6,63,1986,31876,233736,860688,1722338],[]),([6,63,1986,31876,233736,861712,1721376],[(1024,337103)]),([6,63,1986,32704,233736,860688,1721376],[]),([6,63,1986,32706,233736,860688,1721376],[]),([6,63,1986,32708,233736,860688,1721376],[])]
def t38 : BT := .nd (blockTree b40) [6,63,1986,30884,233736,860688,1722338] (blockTree b41)
def b42 : List Row := [([6,63,1986,32710,69888,860688,1721376],[(148,0)]),([6,63,1986,32710,102664,375775,860688],[]),([6,63,1986,32710,102664,860688,1721376],[]),([6,63,1986,32710,233728,860688,1721376],[]),([6,63,1986,32710,233736,374813,860688],[]),([6,63,1986,32710,233736,375744,860688],[]),([6,63,1986,32710,233736,375775,860688],[]),([6,63,1986,32710,233736,375775,860735],[]),([6,63,1986,32710,233736,375775,1236463],[]),([6,63,1986,32710,233736,375807,860688],[]),([6,63,1986,32710,233736,376799,860688],[]),([6,63,1986,32710,233736,860688,1720352],[]),([6,63,1986,32710,233736,860688,1721344],[]),([6,63,1986,32710,233736,860688,1721376],[]),([6,63,1986,32710,233736,860688,1721378],[]),([6,63,1986,32710,233736,860688,1721380],[]),([6,63,1986,32710,233736,860688,1721382],[]),([6,63,1986,32710,233736,860688,1721384],[])]
def b43 : List Row := [([6,63,1986,32710,233736,860688,1721504],[]),([6,63,1986,32710,233736,860688,1721632],[]),([6,63,1986,32710,233736,860688,1722338],[]),([6,63,1986,32710,233736,860688,1722367],[]),([6,63,1986,32710,233736,860688,1725472],[]),([6,63,1986,32710,233736,860688,1725728],[]),([6,63,1986,32710,233736,860688,1786912],[]),([6,63,1986,32710,233736,860690,1721376],[]),([6,63,1986,32710,233736,860692,1721376],[]),([6,63,1986,32710,233736,860694,1721376],[]),([6,63,1986,32710,233736,860696,1721376],[]),([6,63,1986,32710,233736,860720,1721376],[]),([6,63,1986,32710,233736,860735,1721376],[]),([6,63,1986,32710,233736,860735,1721407],[(1024,13679),(1024,16751),(1024,42351)]),([6,63,1986,32710,233736,860735,1722338],[]),([6,63,1986,32710,233736,860944,1721376],[]),([6,63,1986,32710,233736,864784,1721376],[])]
def t39 : BT := .nd (blockTree b42) [6,63,1986,32710,233736,860688,1721407] (blockTree b43)
def t40 : BT := .nd t38 [6,63,1986,32710,65536,1028888,1721376] t39
def b44 : List Row := [([6,63,1986,32710,233736,877072,1721376],[(1024,217581),(1024,348649)]),([6,63,1986,32710,233736,991760,1721376],[]),([6,63,1986,32710,233736,1236416,1721376],[]),([6,63,1986,32710,233736,1236463,1721376],[]),([6,63,1986,32710,233736,1236463,1721407],[]),([6,63,1986,32710,233736,1236463,1722338],[]),([6,63,1986,32710,233736,1236479,1721376],[]),([6,63,1986,32710,233736,1721376,1760751],[]),([6,63,1986,32710,233791,860735,1721376],[(1024,12490),(1024,16751),(1024,41162)]),([6,63,1986,32710,233791,1236463,1721376],[]),([6,63,1986,32710,1236463,1721376,1863415],[]),([6,63,1986,32710,1721376,1824040,2057776],[(1024,335914),(1024,336074)]),([6,63,1986,32710,1824040,2057776],[(1024,335914),(1024,336074),(1024,337097)]),([6,63,1986,32718,233736,860688,1721376],[]),([6,63,1986,32742,233736,860688,1721376],[]),([6,63,1986,32767,233736,375775,860688],[]),([6,63,1986,32767,233736,860688,1721376],[]),([6,63,1986,32767,233736,860688,1721407],[(1024,12655),(1024,13679),(1024,106863)])]
def b45 : List Row := [([6,63,1986,32767,233736,860688,1722367],[]),([6,63,1986,32767,233736,860735,1721376],[(1024,12490),(1024,13679)]),([6,63,1986,32767,233736,1236463,1721376],[]),([6,63,1986,39375,233736,1735844],[(1024,337005),(1024,337389),(1024,500046),(1024,504138)]),([6,63,1986,96388,233736,860688,1722338],[]),([6,63,1986,96388,1028888,1721376],[(1024,336370),(1024,342505),(1024,348265),(1024,348649),(1024,500053)]),([6,63,1986,98246,233736,860688,1721376],[]),([6,63,1986,161924,233736,860688,1722338],[]),([6,63,1986,162180,233736,860688,1722338],[]),([6,63,1986,163782,233736,860688,1721376],[]),([6,63,1986,233736,360473,860688,1721376],[]),([6,63,1986,233736,360473,860688,1722338],[]),([6,63,1986,233736,361307,860688,1722338],[]),([6,63,1986,233736,361307,2057776],[(1024,110922),(1024,337389),(1024,341097),(1024,500046),(1024,504138)]),([6,63,1986,233736,362459,860688,1721376],[]),([6,63,1986,233736,374813,860688,1735844],[]),([6,63,1986,233736,374813,860688,1736678],[])]
def t41 : BT := .nd (blockTree b44) [6,63,1986,32767,233736,860688,1722338] (blockTree b45)
def b46 : List Row := [([6,63,1986,233736,375775,860688,1736678],[]),([6,63,1986,233736,375775,860688,2064441],[]),([6,63,1986,233736,376799,860688,1735844],[]),([6,63,1986,233736,376799,860688,2066299],[]),([6,63,1986,233736,860688,1720352,1734820],[(144,0)]),([6,63,1986,233736,860688,1720352,1735844],[(144,0)]),([6,63,1986,233736,860688,1720352,2066299],[]),([6,63,1986,233736,860688,1721376,1734692],[]),([6,63,1986,233736,860688,1721376,1734820],[]),([6,63,1986,233736,860688,1721376,1736678],[]),([6,63,1986,233736,860688,1721376,1736703],[]),([6,63,1986,233736,860688,1721376,2064384],[]),([6,63,1986,233736,860688,1721376,2064441],[]),([6,63,1986,233736,860688,1721376,2064447],[]),([6,63,1986,233736,860688,1721376,2081849],[]),([6,63,1986,233736,860688,1721407,1736678],[]),([6,63,1986,233736,860688,1721407,1736703],[(1024,106863)]),([6,63,1986,233736,860688,1721407,2064441],[])]
def b47 : List Row := [([6,63,1986,233736,860688,1722338,1735844],[]),([6,63,1986,233736,860688,1722338,1735871],[]),([6,63,1986,233736,860688,1722338,1736678],[]),([6,63,1986,233736,860688,1722338,1736703],[]),([6,63,1986,233736,860688,1722338,2064441],[]),([6,63,1986,233736,860688,1722338,2066240],[]),([6,63,1986,233736,860688,1722338,2066299],[]),([6,63,1986,233736,860688,1722338,2066303],[]),([6,63,1986,233736,860688,1722338,2066427],[]),([6,63,1986,233736,860688,1722338,2082683],[]),([6,63,1986,233736,860688,1722338,2082811],[]),([6,63,1986,233736,860688,1722367,1735844],[]),([6,63,1986,233736,860688,1722367,1735871],[(1024,106989)]),([6,63,1986,233736,860688,1722367,1736678],[]),([6,63,1986,233736,860688,1722367,1736703],[]),([6,63,1986,233736,860688,1722367,2066299],[]),([6,63,1986,233736,860688,1733664],[(1024,336365),(1024,337486),(1024,342121),(1024,342154),(1024,342505),(1024,500047)])]
def t42 : BT := .nd (blockTree b46) [6,63,1986,233736,860688,1722210,2066299] (blockTree b47)
def t43 : BT := .nd t41 [6,63,1986,233736,374813,860688,2066299] t42
def t44 : BT := .nd t40 [6,63,1986,32710,233736,865040,1721376] t43
def t45 : BT := .nd t37 [6,63,1986,30852,233736,1236416,1722338] t44
def b48 : List Row := [([6,63,1986,233736,860688,1736678,1824746],[]),([6,63,1986,233736,860735,1721376,1736678],[]),([6,63,1986,233736,860735,1721376,2064441],[]),([6,63,1986,233736,860735,1722338,1735844],[]),([6,63,1986,233736,860735,1722338,1736678],[]),([6,63,1986,233736,860735,1722338,2066299],[]),([6,63,1986,233736,1236463,1721376,1736678],[]),([6,63,1986,233736,1236463,1721376,2064441],[]),([6,63,1986,233736,1236463,1722338,1735844],[]),([6,63,1986,233736,1236463,1722338,1736678],[]),([6,63,1986,233736,1236463,1722338,2066299],[]),([6,63,1986,233736,1721376,1736678,2057776],[(1024,336074)]),([6,63,1986,233736,1735844,1736678,2057776],[(1024,337005),(1024,337389)]),([6,63,1986,233736,1735844,2057776],[(1024,337005),(1024,337389),(1024,500046),(1024,504138)]),([6,63,1986,233736,1735844,2057791],[(1024,337389),(1024,500046),(1024,504138)]),([6,63,1986,233736,1735871,2057776],[(1024,337389),(1024,500046),(1024,504138)]),([6,63,1986,233736,1735871,2057791],[(1024,42477),(1024,337389),(1024,500046),(1024,504138)]),([6,63,1986,233791,1735844,2057776],[(1024,337389),(1024,500046),(1024,504138)])]
def b49 : List Row := [([6,63,1986,1735844,1824040,2057776],[(1024,336074),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([6,63,1986,1824040,2057776,2066299],[(1024,335914),(1024,335950),(1024,336074),(1024,337097),(1024,500049)]),([6,63,1990,30852,233736,860688,1722338],[]),([6,63,1990,30852,233736,860688,1722342],[]),([6,63,1990,32710,233736,860688,1721376],[]),([6,63,1994,30852,233736,860688,1722338],[]),([6,63,1994,30852,233736,860688,1722346],[]),([6,63,1994,32710,233736,860688,1721376],[]),([6,63,1994,32718,233736,860688,1721376],[]),([6,63,2018,30852,233736,860688,1722338],[]),([6,63,2018,32710,233736,860688,1721376],[]),([6,63,2018,32742,233736,860688,1721376],[]),([6,63,2047,30852,233736,374784,860688],[(1024,106989)]),([6,63,2047,30852,233736,374813,860688],[]),([6,63,2047,30852,233736,376799,860688],[(1024,106989)]),([6,63,2047,30852,233736,376831,860688],[(1024,106989)]),([6,63,2047,30852,233736,860688,1720320],[(1024,106863),(1024,106989)]),([6,63,2047,30852,233736,860688,1720352],[(1024,106863),(1024,106989)])]
def t46 : BT := .nd (blockTree b48) [6,63,1986,1236463,1735844,1824040] (blockTree b49)
def b50 : List Row := [([6,63,2047,30852,233736,860688,1722367],[(1024,106989)]),([6,63,2047,30852,233736,860735,1722338],[(1024,41162),(1024,42477)]),([6,63,2047,30852,233736,860735,1722367],[(1024,8394),(1024,9709)]),([6,63,2047,30852,233736,1236463,1722338],[]),([6,63,2047,30852,233736,1236463,1722367],[(1024,106989)]),([6,63,2047,30852,1824040,2057776],[(1024,336074),(1024,337097),(1024,500049)]),([6,63,2047,30911,233736,860688,1722338],[(1024,41453),(1024,42477),(1024,106989)]),([6,63,2047,30911,233736,860688,1722367],[(1024,8685),(1024,9709),(1024,106989)]),([6,63,2047,32710,233736,375775,860688],[]),([6,63,2047,32710,233736,860688,1721376],[]),([6,63,2047,32710,233736,860688,1721407],[(1024,41327),(1024,42351),(1024,106863)]),([6,63,2047,32710,233736,860688,1722338],[]),([6,63,2047,32710,233736,860688,1722367],[]),([6,63,2047,32710,233736,860735,1721376],[(1024,41162),(1024,42351)]),([6,63,2047,32710,233736,1236463,1721376],[]),([6,63,2047,32767,233736,375775,860688],[]),([6,63,2047,32767,233736,860688,1721376],[(1024,106863)]),([6,63,2047,32767,233736,860688,1721407],[(1024,8559),(1024,9583),(1024,106863)])]
def b51 : List Row := [([6,63,2047,32767,233736,860688,1722367],[]),([6,63,2047,32767,233736,860735,1721376],[(1024,8394),(1024,9583)]),([6,63,2047,32767,233736,1236463,1721376],[(1024,106863)]),([6,63,2047,233736,860688,1721376,1736678],[]),([6,63,2047,233736,860688,1721376,1736703],[(1024,106863)]),([6,63,2047,233736,860688,1721376,2064384],[(1024,106863)]),([6,63,2047,233736,860688,1721376,2064441],[]),([6,63,2047,233736,860688,1722338,1735844],[]),([6,63,2047,233736,860688,1722338,1736678],[]),([6,63,2047,233736,860688,1722338,2066299],[]),([6,63,2047,233736,860688,1722367,1735844],[(1024,106989)]),([6,63,2047,233736,860688,1722367,1736703],[]),([6,63,2047,233736,860688,1722367,2066299],[]),([6,63,2047,233736,1735844,2057776],[(1024,177641),(1024,337389),(1024,500046),(1024,504138)]),([6,63,6082,30852,233736,860688,1722338],[]),([6,63,6082,30852,233736,860688,1726434],[]),([6,63,6082,32710,233736,860688,1721376],[])]
def t47 : BT := .nd (blockTree b50) [6,63,2047,32767,233736,860688,1722338] (blockTree b51)
def t48 : BT := .nd t46 [6,63,2047,30852,233736,860688,1722338] t47
def b52 : List Row := [([6,63,16326,233736,375775,860688],[(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([6,63,16326,233736,860688,1721376],[(1024,336367),(1024,337487),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([6,63,16384,32710,233736,860688,1736678],[(104,0)]),([6,63,30724,233736,860688,1720352,2095165],[]),([6,63,30724,233736,860688,1722338,2095165],[]),([6,63,30852,32710,233736,376799,860688],[]),([6,63,30852,32710,233736,860688,1720352],[]),([6,63,30852,32710,1824040,2057776],[(1024,335914),(1024,335950),(1024,336074),(1024,337097),(1024,500049)]),([6,63,30852,67522,233736,860688,1722338],[(1024,217585)]),([6,63,30852,67522,233736,860688,1787874],[]),([6,63,30852,67522,1028888,1721376],[(1024,336370),(1024,342505),(1024,348265),(1024,348649),(1024,500053)]),([6,63,30852,133058,233736,860688,1722338],[]),([6,63,30852,233736,235466,374813,860688],[]),([6,63,30852,233736,235466,860688,1722338],[]),([6,63,30852,233736,235466,860688,1722367],[]),([6,63,30852,233736,235466,860735,1722338],[]),([6,63,30852,233736,235466,1236463,1722338],[]),([6,63,30852,233736,235519,860688,1722338],[])]
def b53 : List Row := [([6,63,30852,233736,374813,376799,860688],[]),([6,63,30852,233736,374813,860688,2095165],[]),([6,63,30852,233736,376799,860688,1722338],[]),([6,63,30852,233736,376799,860688,2095165],[]),([6,63,30852,233736,860688,1030106,1722338],[]),([6,63,30852,233736,860688,1234989,1722338],[]),([6,63,30852,233736,860688,1720320,2095104],[(1024,499733),(1024,499821)]),([6,63,30852,233736,860688,1720352,1722338],[(144,0)]),([6,63,30852,233736,860688,1720352,2095165],[]),([6,63,30852,233736,860688,1720352,2095167],[]),([6,63,30852,233736,860688,1720352,2095293],[]),([6,63,30852,233736,860688,1720352,2096189],[]),([6,63,30852,233736,860688,1720381,2095165],[]),([6,63,30852,233736,860688,1720383,2095165],[]),([6,63,30852,233736,860688,1722338,2095104],[]),([6,63,30852,233736,860688,1722338,2095165],[]),([6,63,30852,233736,860688,1722338,2095167],[])]
def t49 : BT := .nd (blockTree b52) [6,63,30852,233736,235519,860688,1722367] (blockTree b53)
def b54 : List Row := [([6,63,30852,233736,860688,1722367,2095104],[(1024,106989)]),([6,63,30852,233736,860688,1722367,2095165],[]),([6,63,30852,233736,860735,862162,1722338],[]),([6,63,30852,233736,860735,862207,1722338],[]),([6,63,30852,233736,860735,1720352,2095165],[]),([6,63,30852,233736,860735,1722338,2095165],[]),([6,63,30852,233736,862162,1236463,1722338],[]),([6,63,30852,233736,1236463,1720352,2095165],[]),([6,63,30852,233736,1236463,1722338,2095165],[]),([6,63,30852,233736,1720352,2056752,2095165],[]),([6,63,30852,233736,1721376,2056752,2095165],[]),([6,63,30852,235466,862162,1028888,1721376],[(1024,348649)]),([6,63,30852,1824040,2057776,2095165],[(1024,106833),(1024,140625),(1024,336074),(1024,500049)]),([6,63,30911,233736,235466,860688,1722338],[]),([6,63,30911,233736,860688,1720352,2095165],[]),([6,63,30911,233736,860688,1722338,2095165],[]),([6,63,32710,67522,233736,860688,1721376],[(1024,342513)]),([6,63,32710,132096,233736,860688,1721376],[(1024,336079),(1024,337103)])]
def b55 : List Row := [([6,63,32710,233736,234760,860688,1721376],[(1024,336079),(1024,342057)]),([6,63,32710,233736,235466,375775,860688],[]),([6,63,32710,233736,235466,860688,1721376],[]),([6,63,32710,233736,235466,860688,1721407],[]),([6,63,32710,233736,235466,860688,1722338],[]),([6,63,32710,233736,235466,860735,1721376],[]),([6,63,32710,233736,235466,1236463,1721376],[]),([6,63,32710,233736,235519,860688,1721376],[]),([6,63,32710,233736,375775,376799,860688],[(196,0),(1024,342505)]),([6,63,32710,233736,375775,860688,2095165],[]),([6,63,32710,233736,376799,860688],[(10,0),(74,0),(129,0),(158,0)]),([6,63,32710,233736,376799,860688,1721376],[(1024,342505)]),([6,63,32710,233736,860688,1030106,1721376],[(1024,342505)]),([6,63,32710,233736,860688,1234989,1721376],[]),([6,63,32710,233736,860688,1720352],[(10,0),(74,0),(97,0),(145,0)]),([6,63,32710,233736,860688,1720352,1721376],[(144,0)]),([6,63,32710,233736,860688,1720352,2095165],[])]
def t50 : BT := .nd (blockTree b54) [6,63,32710,133058,233736,860688,1721376] (blockTree b55)
def t51 : BT := .nd t49 [6,63,30852,233736,860688,1722338,2095421] t50
def t52 : BT := .nd t48 [6,63,14274,233736,860688,1721376] t51
def b56 : List Row := [([6,63,32710,233736,860688,1721376,2095165],[]),([6,63,32710,233736,860688,1721376,2095167],[]),([6,63,32710,233736,860688,1721376,2095293],[]),([6,63,32710,233736,860688,1721376,2095421],[]),([6,63,32710,233736,860688,1721376,2096127],[]),([6,63,32710,233736,860688,1721407,2095165],[]),([6,63,32710,233736,860688,1722338,2095165],[]),([6,63,32710,233736,860735,862162,1721376],[]),([6,63,32710,233736,860735,862207,1721376],[]),([6,63,32710,233736,860735,1721376,2095165],[]),([6,63,32710,233736,861712,1721376],[(1024,336917),(1024,336943),(1024,337010),(1024,337044),(1024,337103),(1024,342218),(1024,500052)]),([6,63,32710,233736,862162,1236463,1721376],[]),([6,63,32710,233736,877072,1721376],[(1024,336370),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([6,63,32710,233736,1236463,1721376,2095165],[]),([6,63,32767,233736,235466,860688,1721376],[]),([6,63,32767,233736,235519,860688,1721376],[(1024,106863)]),([6,63,32767,233736,860688,1721376,2095104],[(1024,106863)]),([6,63,32767,233736,860688,1721376,2095165],[])]
def b57 : List Row := [([6,63,133058,163782,233736,860688,1721376],[]),([6,63,233736,235466,860688,1721376,1736678],[]),([6,63,233736,235466,860688,1721376,2064441],[]),([6,63,233736,235466,860688,1722338,1735844],[]),([6,63,233736,235466,860688,1722338,1736678],[]),([6,63,233736,235466,860688,1722338,2066299],[]),([6,63,233736,860688,1720352,1734820,2095165],[(104,0)]),([6,63,233736,860688,1720352,1735844,2095165],[(104,0)]),([6,63,233736,860688,1720352,2066299,2095165],[]),([6,63,233736,860688,1721376,1734692,2095165],[]),([6,63,233736,860688,1721376,1734820,2095165],[]),([6,63,233736,860688,1721376,1736678,2095165],[]),([6,63,233736,860688,1721376,2064441,2095165],[]),([6,63,233736,860688,1721376,2064441,2095293],[]),([6,63,233736,860688,1722338,1735844,2095165],[]),([6,63,233736,860688,1722338,1736678,2095165],[]),([6,63,233736,860688,1722338,2066299,2095165],[]),([6,63,233736,1735844,2057776,2095165],[(1024,106830),(1024,337389),(1024,500046)])]
def t53 : BT := .nd (blockTree b56) [6,63,67522,98246,233736,860688,1721376] (blockTree b57)
def b58 : List Row := [([6,128,2047,32710,233736,860688,1721376],[]),([6,132,2047,30852,233736,860688,1722338],[(1024,238061),(1024,239085)]),([6,132,2047,32710,233736,860688,1721376],[]),([6,191,1986,30852,233736,860688,1722338],[]),([6,191,1986,32710,233736,860688,1721376],[]),([6,256,2047,30852,233736,860688,1722338],[]),([6,256,2047,30852,235466,860688,1721376],[(128,0)]),([6,256,2047,32710,233736,860688,1721376],[]),([6,264,2047,30852,233736,860688,1722338],[]),([6,264,2047,32710,233736,860688,1721376],[]),([6,319,1986,30852,233736,860688,1722338],[]),([6,319,1986,32710,233736,860688,1721376],[]),([6,768,2047,30852,233736,860688,1721376],[]),([6,962,1986,30852,233736,375807,860688],[(1024,348265)]),([6,962,2047,30852,233736,375775,860688],[]),([6,962,2047,30852,233736,860688,1721376],[]),([6,1024,1087,32710,233736,860688,1721376],[(96,0)]),([6,1024,1986,30852,233736,375807,860688],[(1024,20809),(1024,20810),(1024,342121),(1024,348265)])]
def b59 : List Row := [([6,1024,2047,30852,233736,860688,1722338],[]),([6,1024,2047,32710,233736,860688,1721376],[(1024,336239),(1024,337263)]),([6,1024,30911,32710,233736,860688,1721376],[(1024,335919),(1024,336943),(1024,348269)]),([6,1024,32710,32767,233736,860688,1721376],[(1024,335919),(1024,336943)]),([6,1024,32710,233736,233791,860688,1721376],[(1024,337010),(1024,342057)]),([6,1024,32710,233736,860688,1721376,2097088],[(1024,336079),(1024,337103)]),([6,1056,1986,30852,233736,375775,860688],[(1024,184425)]),([6,1056,1986,30852,233736,860688,1721376],[(1024,184425)]),([6,1056,1986,30852,233736,860688,1722338],[]),([6,1056,1986,30852,233736,861744,1721376],[(1024,173077),(1024,177173),(1024,180245)]),([6,1056,1986,30852,233736,1236463,1721376],[(1024,184425)]),([6,1056,1986,30852,233736,1721376,2057776],[(1024,173204)]),([6,1056,1986,31908,233736,860688,1721376],[(1024,176149),(1024,177173),(1024,178281)]),([6,1056,1986,32710,233736,860688,1721376],[]),([6,1056,1986,233736,860688,1721376,1735844],[(144,0),(1024,178281)]),([6,1056,1986,233736,860688,1721376,2066299],[(1024,184425)]),([6,1056,2018,30852,233736,860688,1721376],[(1024,172053),(1024,173077),(1024,178281),(1024,184425)])]
def t54 : BT := .nd (blockTree b58) [6,1024,1986,30852,233736,860688,1721344] (blockTree b59)
def t55 : BT := .nd t53 [6,128,2047,30852,233736,860688,1722338] t54
def b60 : List Row := [([6,1056,2047,32710,233736,860688,1721376],[(1024,336239),(1024,337263)]),([6,1056,30852,32710,233736,860688,1721376],[(1024,184425)]),([6,1056,30852,233736,860688,1721376,1722338],[(144,0)]),([6,1056,30852,233736,860688,1721376,2095165],[]),([6,1056,32710,233736,860688,1721376],[(10,0),(74,0),(97,0),(145,0)]),([6,1087,1986,30852,233736,375775,860688],[]),([6,1087,1986,30852,233736,860688,1721376],[]),([6,1087,1986,30852,233736,860688,1721407],[(1024,106863)]),([6,1087,1986,30852,233736,860688,1722338],[]),([6,1087,1986,30852,233736,860735,1721376],[]),([6,1087,1986,30852,233736,861712,1721376],[]),([6,1087,1986,30852,233736,861759,1721376],[]),([6,1087,1986,30852,233736,1236463,1721376],[]),([6,1087,1986,30852,233736,1721376,2057776],[]),([6,1087,1986,30911,233736,860688,1721376],[(1024,106989)]),([6,1087,1986,31876,233736,860688,1721376],[]),([6,1087,1986,31935,233736,860688,1721376],[(1024,106989)]),([6,1087,1986,32710,233736,860688,1721376],[])]
def b61 : List Row := [([6,1087,1986,233736,860688,1721376,2066299],[]),([6,1087,2047,30852,233736,860688,1721376],[(1024,106863),(1024,106989)]),([6,1087,2047,30852,233736,860688,1721407],[(1024,8559),(1024,9583),(1024,14825),(1024,106863)]),([6,1087,30852,32710,233736,860688,1721376],[]),([6,1087,30852,233736,860688,1721376,1722338],[(144,0)]),([6,1087,30852,233736,860688,1721376,2095165],[]),([6,1087,32710,233736,860688,1721376],[(10,0),(74,0),(97,0),(145,0)]),([6,1188,1986,30852,233736,860688,1721376],[(1024,184425)]),([6,1188,1986,233736,860688,1721376,1735844],[(144,0),(1024,178281)]),([6,1215,1986,30852,233736,860688,1721376],[]),([6,1215,1986,233736,860688,1721376,1735844],[(144,0)]),([6,1320,1986,30852,233736,860688,1721376],[]),([6,1343,1986,30852,233736,860688,1721376],[]),([6,1519,1986,30852,233736,860688,1721376],[]),([6,1519,1986,30852,233736,1236463,1721376],[]),([6,1535,1986,30852,233736,860688,1721376],[]),([6,1535,1986,30852,233736,1236463,1721376],[])]
def t56 : BT := .nd (blockTree b60) [6,1087,1986,233736,860688,1721376,1735844] (blockTree b61)
def b62 : List Row := [([6,1858,1919,233736,860688,1721376,2066299],[]),([6,1858,2047,30852,233736,860688,1721376],[]),([6,1858,2047,233736,860688,1721376,2066299],[]),([6,1915,1986,30852,233736,860688,1721376],[]),([6,1915,1986,233736,860688,1721376,2066299],[]),([6,1919,1986,30852,233736,860688,1721376],[]),([6,1919,1986,233736,860688,1721376,2066299],[]),([6,1984,1986,30852,233736,860688,1721344],[(1024,348265)]),([6,1984,2047,30852,233736,860688,1721376],[]),([6,1984,30852,233736,860688,1721344],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([6,1984,30852,233736,860688,1722336,2097088],[]),([6,1984,30852,233736,860688,1722338,2097088],[]),([6,1984,32708,233736,860688,1721376,2097088],[]),([6,1984,32710,233736,860688,1721376,2097088],[]),([6,1986,1986,30852,233736,375807,860688],[(1024,348265)]),([6,1986,1986,30852,233736,860688,1721344],[(1024,348265)]),([6,1986,2018,30852,233736,375775,860688],[(1024,184425)]),([6,1986,2018,30852,233736,860688,1721376],[(1024,184425)])]
def b63 : List Row := [([6,1986,2018,30852,233736,860720,1721376],[(1024,173077),(1024,177173)]),([6,1986,2018,30852,233736,1236463,1721376],[(1024,184425)]),([6,1986,2018,30884,233736,860688,1721376],[(1024,178281)]),([6,1986,2018,32710,233736,860688,1721376],[]),([6,1986,2018,32742,233736,860688,1721376],[]),([6,1986,2018,233736,860688,1721376,1735844],[(1024,178281),(1024,335981),(1024,337005)]),([6,1986,2018,233736,860688,1721376,2066299],[(1024,184425)]),([6,1986,2022,30852,233736,860688,1721376],[(1024,184425)]),([6,1986,2022,233736,860688,1721376,1735844],[(1024,178281),(1024,335981),(1024,337005)]),([6,1986,2026,30852,233736,860688,1721376],[]),([6,1986,2031,30852,233736,860688,1721376],[]),([6,1986,2031,30852,233736,1236463,1721376],[]),([6,1986,2043,30852,233736,860688,1721376],[]),([6,1986,2043,233736,860688,1721376,2066299],[]),([6,1986,2047,12288,233736,860688,1721376],[]),([6,1986,2047,14468,233736,375775,860688],[]),([6,1986,2047,14468,233736,860688,1721376],[])]
def t57 : BT := .nd (blockTree b62) [6,1986,2018,30852,233736,860688,1722338] (blockTree b63)
def t58 : BT := .nd t56 [6,1858,1919,30852,233736,860688,1721376] t57
def t59 : BT := .nd t55 [6,1056,2047,30852,233736,860688,1722338] t58
def t60 : BT := .nd t52 [6,63,32710,233736,860688,1721376,2095104] t59
def t61 : BT := .nd t45 [6,63,1986,233736,860688,1736678,1824040] t60
def t62 : BT := .nd t30 [6,32,1986,233736,860688,1722338,2066299] t61
def b64 : List Row := [([6,1986,2047,30724,233736,860688,1721376],[]),([6,1986,2047,30848,233736,860688,1721376],[]),([6,1986,2047,30852,65536,1028888,1721376],[]),([6,1986,2047,30852,102664,375775,860688],[]),([6,1986,2047,30852,102664,860688,1721376],[]),([6,1986,2047,30852,233728,860688,1721376],[]),([6,1986,2047,30852,233736,374784,860688],[(1024,374889)]),([6,1986,2047,30852,233736,374813,860688],[]),([6,1986,2047,30852,233736,375744,860688],[(1024,374889)]),([6,1986,2047,30852,233736,375775,860688],[]),([6,1986,2047,30852,233736,375775,1236463],[]),([6,1986,2047,30852,233736,375807,860688],[(1024,348265)]),([6,1986,2047,30852,233736,376799,860688],[]),([6,1986,2047,30852,233736,376831,860688],[]),([6,1986,2047,30852,233736,860688,1720320],[]),([6,1986,2047,30852,233736,860688,1720352],[]),([6,1986,2047,30852,233736,860688,1721344],[(1024,348265)]),([6,1986,2047,30852,233736,860688,1721376],[])]
def b65 : List Row := [([6,1986,2047,30852,233736,860688,1721380],[]),([6,1986,2047,30852,233736,860688,1721384],[]),([6,1986,2047,30852,233736,860688,1721407],[(1024,106863)]),([6,1986,2047,30852,233736,860688,1721504],[]),([6,1986,2047,30852,233736,860688,1721508],[]),([6,1986,2047,30852,233736,860688,1721632],[]),([6,1986,2047,30852,233736,860688,1721640],[]),([6,1986,2047,30852,233736,860688,1722338],[]),([6,1986,2047,30852,233736,860688,1722367],[]),([6,1986,2047,30852,233736,860688,1725472],[]),([6,1986,2047,30852,233736,860688,1786912],[]),([6,1986,2047,30852,233736,860692,1721376],[]),([6,1986,2047,30852,233736,860696,1721376],[]),([6,1986,2047,30852,233736,860720,1721376],[]),([6,1986,2047,30852,233736,860944,1721376],[(96,0)]),([6,1986,2047,30852,233736,860952,1721376],[]),([6,1986,2047,30852,233736,864784,1721376],[]),([6,1986,2047,30852,233736,877072,1721376],[])]
def t63 : BT := .nd (blockTree b64) [6,1986,2047,30852,233736,860688,1721378] (blockTree b65)
def b66 : List Row := [([6,1986,2047,30852,233736,1236463,1721376],[]),([6,1986,2047,30852,233736,1236463,1721407],[(1024,106863)]),([6,1986,2047,30852,233736,1236463,1722338],[]),([6,1986,2047,30852,233736,1236463,1722367],[]),([6,1986,2047,30852,233736,1236479,1721376],[]),([6,1986,2047,30852,233736,1721376,1760751],[]),([6,1986,2047,30852,1236463,1721376,1863415],[]),([6,1986,2047,30852,1721376,1824040,2057776],[(1024,172074),(1024,335914)]),([6,1986,2047,30852,1824040,2057776],[(1024,335914),(1024,336937)]),([6,1986,2047,30854,233736,860688,1721376],[]),([6,1986,2047,30860,233736,860688,1721376],[]),([6,1986,2047,30884,233736,860688,1721376],[]),([6,1986,2047,30911,233736,375775,860688],[(1024,106989)]),([6,1986,2047,30911,233736,860688,1721376],[(1024,106989)]),([6,1986,2047,30911,233736,860688,1721407],[(1024,14825),(1024,106863),(1024,106989)]),([6,1986,2047,30911,233736,860688,1722338],[]),([6,1986,2047,30911,233736,860688,1722367],[(1024,106989)]),([6,1986,2047,30911,233736,1236463,1721376],[(1024,106989)])]
def b67 : List Row := [([6,1986,2047,31116,233736,860688,1721376],[]),([6,1986,2047,31876,233736,860688,1721376],[]),([6,1986,2047,31908,233736,860688,1721376],[]),([6,1986,2047,32710,233736,375775,860688],[]),([6,1986,2047,32710,233736,860688,1721376],[]),([6,1986,2047,32710,233736,860688,1721407],[]),([6,1986,2047,32710,233736,860688,1722338],[]),([6,1986,2047,32710,233736,860688,1722367],[]),([6,1986,2047,32710,233736,1236463,1721376],[]),([6,1986,2047,32767,233736,375775,860688],[]),([6,1986,2047,32767,233736,860688,1721376],[]),([6,1986,2047,32767,233736,860688,1721407],[(1024,106863)]),([6,1986,2047,32767,233736,860688,1722338],[]),([6,1986,2047,32767,233736,860688,1722367],[]),([6,1986,2047,32767,233736,1236463,1721376],[]),([6,1986,2047,96388,233736,860688,1721376],[]),([6,1986,2047,161924,233736,860688,1721376],[])]
def t64 : BT := .nd (blockTree b66) [6,1986,2047,31108,233736,860688,1721376] (blockTree b67)
def t65 : BT := .nd t63 [6,1986,2047,30852,233736,991760,1721376] t64
def b68 : List Row := [([6,1986,2047,233736,375775,860688,1735844],[]),([6,1986,2047,233736,375775,860688,2066299],[]),([6,1986,2047,233736,860688,1721376,1735844],[(1024,336365),(1024,337389)]),([6,1986,2047,233736,860688,1721376,1735871],[(1024,106989),(1024,336365),(1024,337389)]),([6,1986,2047,233736,860688,1721376,1736678],[]),([6,1986,2047,233736,860688,1721376,1736703],[]),([6,1986,2047,233736,860688,1721376,2064384],[(1024,503913)]),([6,1986,2047,233736,860688,1721376,2064441],[]),([6,1986,2047,233736,860688,1721376,2066240],[(1024,503913)]),([6,1986,2047,233736,860688,1721376,2066299],[]),([6,1986,2047,233736,860688,1721376,2066303],[]),([6,1986,2047,233736,860688,1721376,2066427],[]),([6,1986,2047,233736,860688,1721376,2066431],[]),([6,1986,2047,233736,860688,1721376,2082683],[]),([6,1986,2047,233736,860688,1721407,1735844],[(1024,106863)]),([6,1986,2047,233736,860688,1721407,1735871],[(1024,14825),(1024,41453),(1024,42477),(1024,106863),(1024,106989)]),([6,1986,2047,233736,860688,1721407,2066299],[(1024,106863)]),([6,1986,2047,233736,860688,1722338,1735844],[])]
def b69 : List Row := [([6,1986,2047,233736,860688,1722338,2066299],[]),([6,1986,2047,233736,860688,1722367,1735844],[]),([6,1986,2047,233736,860688,1722367,1736703],[]),([6,1986,2047,233736,860688,1722367,2066299],[]),([6,1986,2047,233736,860688,1735844,1824040],[(1024,336365)]),([6,1986,2047,233736,1236463,1721376,1735844],[(1024,336365)]),([6,1986,2047,233736,1236463,1721376,2066299],[]),([6,1986,2047,233736,1721376,1735844,2057776],[(1024,173549),(1024,337389)]),([6,1986,2047,233736,1735844,2057776],[(1024,337005),(1024,337389),(1024,504138)]),([6,1986,4159,30852,233736,860688,1722338],[]),([6,1986,4159,32710,233736,860688,1721376],[]),([6,1986,4415,32710,233736,860688,1721376],[]),([6,1986,6143,30852,233736,860688,1721376],[]),([6,1986,14468,233736,375807,860688],[(1024,106831),(1024,342121)]),([6,1986,16416,30852,233736,860688,1722338],[(1024,53357)]),([6,1986,16416,32710,233736,860688,1721376],[(1024,53357),(1024,348265)]),([6,1986,16447,30852,233736,860688,1722338],[]),([6,1986,16447,32710,233736,860688,1721376],[(1024,348335)])]
def t66 : BT := .nd (blockTree b68) [6,1986,2047,233736,860688,1722338,1736678] (blockTree b69)
def b70 : List Row := [([6,1986,16575,30852,233736,860688,1722338],[]),([6,1986,17440,30852,233736,860688,1721376],[(1024,184425)]),([6,1986,17440,32710,233736,860688,1721376],[]),([6,1986,17471,30852,233736,860688,1721376],[]),([6,1986,17471,32710,233736,860688,1721376],[]),([6,1986,18402,30852,233736,860688,1721376],[(1024,184425)]),([6,1986,18431,30852,233736,860688,1721376],[]),([6,1986,30720,233736,860688,1721376,2095104],[]),([6,1986,30848,233736,860688,1721344],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([6,1986,30848,233736,860688,1722338,2097088],[]),([6,1986,30852,30884,233736,860688,1722338],[]),([6,1986,30852,30886,233736,860688,1722338],[]),([6,1986,30852,30911,233736,374813,860688],[]),([6,1986,30852,30911,233736,376799,860688],[]),([6,1986,30852,30911,233736,860688,1720352],[]),([6,1986,30852,30911,233736,860688,1722338],[]),([6,1986,30852,30911,233736,1236463,1722338],[]),([6,1986,30852,30911,1824040,2057776],[(1024,335914),(1024,335950),(1024,336973),(1024,500049)])]
def b71 : List Row := [([6,1986,30852,31935,233736,860688,1721376],[]),([6,1986,30852,32710,233736,375807,860688],[(1024,348265)]),([6,1986,30852,32710,233736,860688,1721344],[(1024,348265)]),([6,1986,30852,32742,233736,860688,1721376],[(1024,184425)]),([6,1986,30852,32767,233736,375775,860688],[]),([6,1986,30852,32767,233736,860688,1721376],[]),([6,1986,30852,32767,233736,860688,1722338],[]),([6,1986,30852,32767,233736,1236463,1721376],[]),([6,1986,30852,39423,233736,1721376],[(1024,106836),(1024,337492),(1024,342121),(1024,345193),(1024,609610)]),([6,1986,30852,65599,233736,860688,1722338],[]),([6,1986,30852,67583,233736,860688,1721376],[]),([6,1986,30852,102664,375807,860688],[(1024,106834),(1024,342121),(1024,345193)]),([6,1986,30852,131104,233736,860688,1722338],[]),([6,1986,30852,131135,233736,860688,1722338],[]),([6,1986,30852,131362,233736,860688,1722338],[]),([6,1986,30852,131391,233736,860688,1722338],[]),([6,1986,30852,132128,233736,860688,1721376],[(1024,184425)])]
def t67 : BT := .nd (blockTree b70) [6,1986,30852,31908,233736,860688,1721376] (blockTree b71)
def t68 : BT := .nd t66 [6,1986,16546,30852,233736,860688,1722338] t67
def t69 : BT := .nd t65 [6,1986,2047,233736,361307,860688,1721376] t68
def b72 : List Row := [([6,1986,30852,133090,233736,860688,1721376],[(1024,184425)]),([6,1986,30852,133119,233736,860688,1721376],[]),([6,1986,30852,233728,860688,1721344],[(1024,140629),(1024,336370),(1024,337044),(1024,342154),(1024,348298)]),([6,1986,30852,233728,860688,1722338,2097088],[]),([6,1986,30852,233736,233768,860688,1722338],[(1024,53417)]),([6,1986,30852,233736,233770,860688,1722338],[]),([6,1986,30852,233736,233791,374813,860688],[]),([6,1986,30852,233736,233791,376799,860688],[]),([6,1986,30852,233736,233791,860688,1720352],[]),([6,1986,30852,233736,233791,860688,1722338],[]),([6,1986,30852,233736,233791,1236463,1722338],[]),([6,1986,30852,233736,234792,860688,1721376],[]),([6,1986,30852,233736,234815,860688,1721376],[]),([6,1986,30852,233736,235466,375807,860688],[(1024,348265)]),([6,1986,30852,233736,235466,860688,1721344],[(1024,348265)]),([6,1986,30852,233736,235498,860688,1721376],[]),([6,1986,30852,233736,235519,375775,860688],[]),([6,1986,30852,233736,235519,860688,1721376],[])]
def b73 : List Row := [([6,1986,30852,233736,235519,1236463,1721376],[]),([6,1986,30852,233736,260543,860688,1722338],[]),([6,1986,30852,233736,262143,860688,1721376],[]),([6,1986,30852,233736,374813,374847,860688],[]),([6,1986,30852,233736,374813,860688,2097088],[]),([6,1986,30852,233736,374847,860688],[(10,0),(129,0)]),([6,1986,30852,233736,374847,860688,1721376],[]),([6,1986,30852,233736,374847,860688,1722338],[]),([6,1986,30852,233736,375775,376831,860688],[(196,0)]),([6,1986,30852,233736,375775,860688,2095104],[]),([6,1986,30852,233736,375807,376799,860688],[(1024,342121),(1024,345193),(1024,347241),(1024,348265)]),([6,1986,30852,233736,375807,376831,860688],[(196,0),(1024,342121),(1024,345193),(1024,347241),(1024,348265)]),([6,1986,30852,233736,375807,860688],[(1024,106837),(1024,342121),(1024,345193),(1024,347241),(1024,348265)]),([6,1986,30852,233736,375807,860688,1722338],[(1024,348265)]),([6,1986,30852,233736,375807,860688,2095165],[(1024,348265)]),([6,1986,30852,233736,375807,1236463],[(1024,106837),(1024,150858),(1024,342121),(1024,345193),(1024,348265)]),([6,1986,30852,233736,375807,2057776],[(1024,106836),(1024,145738),(1024,148810),(1024,150858),(1024,337044),(1024,347241)]),([6,1986,30852,233736,376799,376831,860688],[(196,0)])]
def t70 : BT := .nd (blockTree b72) [6,1986,30852,233736,235519,860688,1722338] (blockTree b73)
def b74 : List Row := [([6,1986,30852,233736,376831,860688],[(10,0),(158,0)]),([6,1986,30852,233736,376831,860688,1721376],[]),([6,1986,30852,233736,860688,1028927,1722338],[]),([6,1986,30852,233736,860688,1030143,1721376],[]),([6,1986,30852,233736,860688,1234944,1721376],[]),([6,1986,30852,233736,860688,1236416,1722338],[]),([6,1986,30852,233736,860688,1720320],[(10,0),(145,0)]),([6,1986,30852,233736,860688,1720320,1721376],[(144,0)]),([6,1986,30852,233736,860688,1720320,2095104],[]),([6,1986,30852,233736,860688,1720352,2097088],[]),([6,1986,30852,233736,860688,1721344],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([6,1986,30852,233736,860688,1721344,1722306],[(1024,348265)]),([6,1986,30852,233736,860688,1721344,1722338],[(1024,348265)]),([6,1986,30852,233736,860688,1721344,2095165],[(1024,348265)]),([6,1986,30852,233736,860688,1721376,1722304],[(1024,348265)]),([6,1986,30852,233736,860688,1721376,1722306],[(1024,348265)]),([6,1986,30852,233736,860688,1721376,2064384],[]),([6,1986,30852,233736,860688,1721376,2095104],[])]
def b75 : List Row := [([6,1986,30852,233736,860688,1721376,2095236],[]),([6,1986,30852,233736,860688,1721376,2095368],[]),([6,1986,30852,233736,860688,1721376,2096064],[]),([6,1986,30852,233736,860688,1721376,2096095],[]),([6,1986,30852,233736,860688,1721407,2095104],[]),([6,1986,30852,233736,860688,1722304],[(10,0),(97,0)]),([6,1986,30852,233736,860688,1722304,1722338],[]),([6,1986,30852,233736,860688,1722304,2097088],[(196,0)]),([6,1986,30852,233736,860688,1722306],[(10,0),(97,0)]),([6,1986,30852,233736,860688,1722306,2097088],[(196,0)]),([6,1986,30852,233736,860688,1722336,2097088],[]),([6,1986,30852,233736,860688,1722338,2066240],[]),([6,1986,30852,233736,860688,1722338,2095104],[]),([6,1986,30852,233736,860688,1722338,2097088],[]),([6,1986,30852,233736,860688,1722338,2097090],[]),([6,1986,30852,233736,860688,1722338,2097092],[]),([6,1986,30852,233736,860688,1722338,2097096],[])]
def t71 : BT := .nd (blockTree b74) [6,1986,30852,233736,860688,1721376,2095133] (blockTree b75)
def t72 : BT := .nd t70 [6,1986,30852,233736,376799,860688,2097088] t71
def b76 : List Row := [([6,1986,30852,233736,860688,1722338,2097119],[]),([6,1986,30852,233736,860688,1722367,2095104],[]),([6,1986,30852,233736,860688,1722367,2097088],[]),([6,1986,30852,233736,860735,861712,1721376],[(1024,342058)]),([6,1986,30852,233736,860735,1236463,1722338],[]),([6,1986,30852,233736,860735,1722338,2097088],[]),([6,1986,30852,233736,862207,1236463,1721376],[]),([6,1986,30852,233736,1236463,1721344],[(1024,106837),(1024,335986),(1024,342121),(1024,347241),(1024,348265)]),([6,1986,30852,233736,1236463,1721376,2095104],[]),([6,1986,30852,233736,1236463,1722338,2097088],[]),([6,1986,30852,233736,1721344,2057744],[(1024,106836),(1024,150858),(1024,337044),(1024,342121),(1024,345193)]),([6,1986,30852,233736,1721344,2057776],[(1024,106836),(1024,150858),(1024,337044),(1024,342121),(1024,345193)]),([6,1986,30852,233736,1721376,2057728],[(112,0),(1024,106836),(1024,337492),(1024,342121),(1024,345193),(1024,609610)]),([6,1986,30852,233736,1721376,2057744],[(112,0),(1024,106836),(1024,150858),(1024,337044),(1024,342121),(1024,345193)]),([6,1986,30852,233768,860720,1721376],[(1024,41140),(1024,106837),(1024,180245),(1024,181290)]),([6,1986,30852,233791,860735,1721407],[(1024,16623),(1024,16751),(1024,17610),(1024,204820),(1024,500053)]),([6,1986,30852,1824040,2057776,2097088],[(156,0),(1024,335914),(1024,335950),(1024,336074),(1024,336937),(1024,337097),(1024,500049)]),([6,1986,30884,32710,233736,860688,1721376],[(1024,348265)])]
def b77 : List Row := [([6,1986,30911,31876,233736,860688,1721376],[(1024,348269)]),([6,1986,30911,32710,233736,375775,860688],[(1024,348269)]),([6,1986,30911,32710,233736,860688,1721376],[(1024,348269)]),([6,1986,30911,32710,233736,860688,1722338],[]),([6,1986,30911,32710,233736,1236463,1721376],[(1024,348269)]),([6,1986,30911,233736,860688,1721376,2064441],[]),([6,1986,30911,233736,860688,1721376,2095104],[]),([6,1986,30911,233736,860688,1722338,2066299],[]),([6,1986,30911,233736,860688,1722338,2097088],[]),([6,1986,30911,233736,860735,1721407],[(1024,13551),(1024,13679),(1024,14538),(1024,336370),(1024,500053),(1024,503828)]),([6,1986,30911,233791,860735,1721376],[(1024,12490),(1024,13513),(1024,16877),(1024,204814),(1024,205837),(1024,500053),(1024,503825)]),([6,1986,32704,233736,860688,1721376,2097088],[]),([6,1986,32706,233736,860688,1721376,2097088],[]),([6,1986,32708,233736,860688,1721376,2097088],[]),([6,1986,32710,32742,233736,860688,1721376],[]),([6,1986,32710,32767,233736,375775,860688],[]),([6,1986,32710,32767,233736,860688,1721376],[])]
def t73 : BT := .nd (blockTree b76) [6,1986,30884,233736,860720,1721376] (blockTree b77)
def b78 : List Row := [([6,1986,32710,32767,233736,1236463,1721376],[]),([6,1986,32710,65599,233736,860688,1721376],[]),([6,1986,32710,131104,233736,860688,1721376],[]),([6,1986,32710,131135,233736,860688,1721376],[]),([6,1986,32710,233728,860688,1721376,2097088],[]),([6,1986,32710,233736,233768,860688,1721376],[(1024,342194)]),([6,1986,32710,233736,233791,375775,860688],[]),([6,1986,32710,233736,233791,860688,1721376],[]),([6,1986,32710,233736,233791,860688,1722338],[]),([6,1986,32710,233736,233791,1236463,1721376],[]),([6,1986,32710,233736,235519,860688,1721376],[]),([6,1986,32710,233736,260543,860688,1721376],[(1024,184655)]),([6,1986,32710,233736,262143,860688,1721376],[]),([6,1986,32710,233736,375775,375807,860688],[(196,0)]),([6,1986,32710,233736,375775,860688,2097088],[]),([6,1986,32710,233736,375807,860688],[(10,0),(129,0),(158,0)]),([6,1986,32710,233736,375807,860688,1721376],[(1024,116041),(1024,150858)]),([6,1986,32710,233736,860688,1028927,1721376],[])]
def b79 : List Row := [([6,1986,32710,233736,860688,1721344],[(10,0),(97,0),(1024,335986),(1024,337044)]),([6,1986,32710,233736,860688,1721344,1721376],[(1024,335986),(1024,337044)]),([6,1986,32710,233736,860688,1721344,2097088],[(196,0)]),([6,1986,32710,233736,860688,1721376,2064384],[(1024,342197)]),([6,1986,32710,233736,860688,1721376,2066240],[(1024,342197)]),([6,1986,32710,233736,860688,1721376,2095104],[]),([6,1986,32710,233736,860688,1721376,2097088],[]),([6,1986,32710,233736,860688,1721376,2097090],[]),([6,1986,32710,233736,860688,1721376,2097092],[]),([6,1986,32710,233736,860688,1721376,2097094],[]),([6,1986,32710,233736,860688,1721376,2097096],[]),([6,1986,32710,233736,860688,1721376,2097119],[]),([6,1986,32710,233736,860688,1721407,2097088],[]),([6,1986,32710,233736,860688,1722338,2097088],[]),([6,1986,32710,233736,860735,1236463,1721376],[]),([6,1986,32710,233736,860735,1721376,2097088],[]),([6,1986,32710,233736,1236463,1721376,2097088],[])]
def t74 : BT := .nd (blockTree b78) [6,1986,32710,233736,860688,1236416,1721376] (blockTree b79)
def t75 : BT := .nd t73 [6,1986,32710,32767,233736,860688,1722338] t74
def t76 : BT := .nd t72 [6,1986,30852,233736,860688,1722338,2097117] t75
def t77 : BT := .nd t69 [6,1986,30852,132159,233736,860688,1721376] t76
def b80 : List Row := [([6,1986,32767,233736,860688,1721376,2066299],[]),([6,1986,32767,233736,860688,1721376,2095104],[]),([6,1986,32767,233736,860688,1721376,2097088],[]),([6,1986,233736,233791,860688,1721376,1736678],[]),([6,1986,233736,233791,860688,1721376,2064441],[]),([6,1986,233736,233791,860688,1722338,1735844],[]),([6,1986,233736,233791,860688,1722338,1736678],[]),([6,1986,233736,233791,860688,1722338,2066299],[]),([6,1986,233736,233791,1735844,2057776],[(1024,106830),(1024,110922),(1024,337005),(1024,337038)]),([6,1986,233736,235519,860688,1721376,1735844],[(1024,337005)]),([6,1986,233736,235519,860688,1721376,2066299],[]),([6,1986,233736,361343,860688,1721376],[(136,0),(1024,106831),(1024,342121)]),([6,1986,233736,375807,860688,1735844],[(1024,106831),(1024,342121)]),([6,1986,233736,375807,860688,2066299],[(1024,106837),(1024,342121),(1024,345193),(1024,347241),(1024,348265)]),([6,1986,233736,860688,1721344,1735812],[(104,0),(1024,106831),(1024,342121)]),([6,1986,233736,860688,1721344,1735844],[(104,0),(1024,106831),(1024,342121)]),([6,1986,233736,860688,1721344,2066299],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([6,1986,233736,860688,1721376,1735808],[(104,0),(1024,106831),(1024,342121)])]
def b81 : List Row := [([6,1986,233736,860688,1721376,1735844,2095104],[(1024,336365),(1024,337389)]),([6,1986,233736,860688,1721376,1736678,2097088],[]),([6,1986,233736,860688,1721376,2064441,2097088],[]),([6,1986,233736,860688,1721376,2066299,2095104],[]),([6,1986,233736,860688,1722338,1735844,2097088],[]),([6,1986,233736,860688,1722338,1736678,2097088],[]),([6,1986,233736,860688,1722338,2066299,2097088],[]),([6,1986,233736,1735844,2057776,2097088],[(1024,337005),(1024,337389),(1024,341097),(1024,500046),(1024,504138)]),([6,1990,2047,30852,233736,860688,1721376],[]),([6,1990,2047,32710,233736,860688,1721376],[]),([6,2018,2018,30852,233736,860688,1721376],[(1024,184425)]),([6,2018,2047,30852,233736,860688,1721376],[(1024,184425)]),([6,2018,2047,30852,233736,860688,1722338],[]),([6,2018,30852,32710,233736,860688,1721376],[(1024,184425)]),([6,2018,30852,32742,233736,860688,1721376],[(1024,184425)]),([6,2018,30852,233736,235498,860688,1721376],[(1024,184425)]),([6,2018,30852,233736,375775,860688],[(1024,106677),(1024,178281),(1024,181353),(1024,183401),(1024,184425)]),([6,2018,30852,233736,860688,1721376],[(1024,106677),(1024,172146),(1024,173204),(1024,178281),(1024,184425)])]
def t78 : BT := .nd (blockTree b80) [6,1986,233736,860688,1721376,1735812] (blockTree b81)
def b82 : List Row := [([6,2018,30852,233736,860688,1721376,2095133],[(1024,184425)]),([6,2018,30852,233736,860688,1721376,2095165],[(1024,184425)]),([6,2018,30852,233736,860688,1722338],[(10,0),(97,0)]),([6,2018,30852,233736,860720,1721376],[(1024,20650),(1024,106676),(1024,173077),(1024,173204),(1024,183401),(1024,335986)]),([6,2018,30852,233736,1236463,1721376],[(1024,106677),(1024,172146),(1024,178281),(1024,183401),(1024,184425)]),([6,2018,30852,233736,1721376,2057776],[(1024,106676),(1024,150698),(1024,173204),(1024,178281),(1024,181353)]),([6,2018,30884,233736,860688,1721376],[(1024,106671),(1024,178281),(1024,335986),(1024,337044)]),([6,2018,32710,233736,860688,1721376],[(10,0),(97,0),(1024,335986),(1024,337044)]),([6,2018,32742,233736,860688,1721376],[(10,0),(97,0),(1024,172146),(1024,173204)]),([6,2018,233736,860688,1721376,1735844],[(104,0),(1024,106671),(1024,178281)]),([6,2018,233736,860688,1721376,2066299],[(1024,106677),(1024,172146),(1024,173204),(1024,178281),(1024,184425)]),([6,2022,30852,233736,860688,1721376],[(1024,106677),(1024,172146),(1024,173204),(1024,178281),(1024,184425)]),([6,2022,233736,860688,1721376,1735844],[(104,0),(1024,106671),(1024,178281)]),([6,2047,2047,30852,233736,860688,1722338],[]),([6,2047,2047,32710,233736,860688,1721376],[]),([6,2047,4096,30852,233736,860688,1722338],[]),([6,2047,4096,32710,233736,860688,1721376],[]),([6,2047,4352,32710,233736,860688,1721376],[])]
def b83 : List Row := [([6,2047,16384,30852,233736,860688,1722338],[(104,0)]),([6,2047,16384,32710,233736,860688,1721376],[(104,0)]),([6,2047,16512,30852,233736,860688,1722338],[(1024,238061),(1024,239085)]),([6,2047,17408,32710,233736,860688,1721376],[(1024,336370),(1024,337394)]),([6,2047,18370,30852,233736,860688,1721376],[]),([6,2047,30724,233736,860688,1721376,2095165],[]),([6,2047,30852,30852,233736,860688,1722338],[]),([6,2047,30852,30911,233736,860688,1722338],[]),([6,2047,30852,30911,233736,860688,1722367],[(1024,106989)]),([6,2047,30852,32710,233736,375775,860688],[]),([6,2047,30852,32710,233736,860688,1721376],[]),([6,2047,30852,32710,233736,860688,1721407],[(1024,106863)]),([6,2047,30852,32710,233736,860688,1722338],[]),([6,2047,30852,32710,233736,860688,1722367],[]),([6,2047,30852,32710,233736,1236463,1721376],[]),([6,2047,30852,32767,233736,860688,1722338],[]),([6,2047,30852,65536,233736,860688,1722338],[])]
def t79 : BT := .nd (blockTree b82) [6,2047,6082,30852,233736,860688,1721376] (blockTree b83)
def t80 : BT := .nd t78 [6,2018,30852,233736,860688,1721376,1722338] t79
def b84 : List Row := [([6,2047,30852,131072,233736,860688,1722338],[]),([6,2047,30852,131328,233736,860688,1722338],[]),([6,2047,30852,133058,233736,860688,1721376],[]),([6,2047,30852,233736,233736,860688,1722338],[]),([6,2047,30852,233736,233791,860688,1722338],[]),([6,2047,30852,233736,235466,860688,1722338],[]),([6,2047,30852,233736,235519,860688,1722338],[]),([6,2047,30852,233736,260492,860688,1722338],[]),([6,2047,30852,233736,374813,860688],[(10,0),(129,0)]),([6,2047,30852,233736,374813,860688,1721376],[]),([6,2047,30852,233736,374813,860688,1722338],[]),([6,2047,30852,233736,375744,860688],[(1024,106863),(1024,374889),(1024,374922),(1024,499733),(1024,509033)]),([6,2047,30852,233736,375775,860688,1722338],[(156,0),(1024,184425)]),([6,2047,30852,233736,375775,860688,2095165],[]),([6,2047,30852,233736,860688,1028888,1722338],[]),([6,2047,30852,233736,860688,1236463,1722338],[]),([6,2047,30852,233736,860688,1720352,2095165],[]),([6,2047,30852,233736,860688,1721376,1722338],[(1024,184425)])]
def b85 : List Row := [([6,2047,30852,233736,860688,1721376,2064441],[]),([6,2047,30852,233736,860688,1721376,2095165],[]),([6,2047,30852,233736,860688,1721376,2095167],[]),([6,2047,30852,233736,860688,1721376,2095293],[]),([6,2047,30852,233736,860688,1721376,2096189],[]),([6,2047,30852,233736,860688,1721407],[(1024,8690),(1024,9812),(1024,14825),(1024,106863),(1024,374889),(1024,499733)]),([6,2047,30852,233736,860688,1721407,1722338],[]),([6,2047,30852,233736,860688,1721407,1722367],[(1024,106863),(1024,106989)]),([6,2047,30852,233736,860688,1721407,2095165],[(1024,106863)]),([6,2047,30852,233736,860688,1722338],[(10,0),(97,0)]),([6,2047,30852,233736,860688,1722338,1722338],[]),([6,2047,30852,233736,860688,1722338,1722367],[]),([6,2047,30852,233736,860688,1722338,1735844],[]),([6,2047,30852,233736,860688,1722338,1736678],[]),([6,2047,30852,233736,860688,1722338,1824040],[]),([6,2047,30852,233736,860688,1722338,1824746],[]),([6,2047,30852,233736,860688,1722338,2066299],[])]
def t81 : BT := .nd (blockTree b84) [6,2047,30852,233736,860688,1721376,1736678] (blockTree b85)
def b86 : List Row := [([6,2047,30852,233736,860688,1722338,2095165],[]),([6,2047,30852,233736,860688,1722338,2097088],[(196,0)]),([6,2047,30852,233736,860688,1722367,2095165],[(1024,106863)]),([6,2047,30852,233736,860688,1722367,2097088],[]),([6,2047,30852,233736,860735,1721407],[(1024,9455),(1024,9583),(1024,9812),(1024,19945),(1024,336370),(1024,374794),(1024,499732)]),([6,2047,30852,233736,1236463,1721376,1722338],[(1024,184425)]),([6,2047,30852,233736,1236463,1721376,2095165],[]),([6,2047,30852,233736,1236463,1721407],[(1024,8690),(1024,14825),(1024,106863),(1024,374889),(1024,499733)]),([6,2047,30852,233736,1236463,1722338],[]),([6,2047,30852,233736,1721376,1722338,2057776],[(1024,172074),(1024,173204),(1024,173549)]),([6,2047,30852,233736,1721407,2057776],[(1024,9812),(1024,107092),(1024,145897),(1024,148969),(1024,499860),(1024,609385)]),([6,2047,30852,233736,1721407,2057791],[(1024,9812),(1024,14825),(1024,17897),(1024,106698),(1024,499732),(1024,609290)]),([6,2047,30852,233791,860735,1721376],[(1024,8394),(1024,9417),(1024,204810),(1024,205833),(1024,499729)]),([6,2047,30911,32710,233736,860688,1721376],[]),([6,2047,30911,32767,233736,860688,1721376],[(1024,106989)]),([6,2047,30911,233736,375775,860688],[(1024,106989),(1024,499821),(1024,503913)]),([6,2047,30911,233736,860688,1721376],[(1024,106989),(1024,336370),(1024,337492),(1024,499821),(1024,503913)]),([6,2047,30911,233736,860688,1721376,1722338],[(1024,106989)])]
def b87 : List Row := [([6,2047,30911,233736,860688,1721407],[(1024,14825),(1024,106863),(1024,106989),(1024,336370),(1024,337492),(1024,499727)]),([6,2047,30911,233736,860688,1722338],[(10,0),(1024,106989)]),([6,2047,30911,233736,860688,1722367],[(1024,106989),(1024,110959),(1024,144751),(1024,503913)]),([6,2047,30911,233736,860735,1721376],[(1024,9709),(1024,336370),(1024,337492),(1024,499726),(1024,503818)]),([6,2047,30911,233736,1236463,1721376],[(1024,106989),(1024,336370),(1024,499821),(1024,503913)]),([6,2047,30911,233736,1721376,2057776],[(1024,106989),(1024,337492),(1024,499821),(1024,503913),(1024,609610)]),([6,2047,32710,32710,233736,860688,1721376],[]),([6,2047,32710,32767,233736,860688,1721376],[]),([6,2047,32710,65536,233736,860688,1721376],[]),([6,2047,32710,131072,233736,860688,1721376],[]),([6,2047,32710,233736,233736,860688,1721376],[]),([6,2047,32710,233736,233791,860688,1721376],[]),([6,2047,32710,233736,235466,860688,1721376],[]),([6,2047,32710,233736,235519,860688,1721376],[]),([6,2047,32710,233736,260492,860688,1721376],[]),([6,2047,32710,233736,262094,860688,1721376],[(156,0)]),([6,2047,32710,233736,375775,860688],[(10,0),(129,0),(158,0)])]
def t82 : BT := .nd (blockTree b86) [6,2047,30911,233736,860688,1721376,2095165] (blockTree b87)
def t83 : BT := .nd t81 [6,2047,30852,233736,860688,1722338,2095104] t82
def t84 : BT := .nd t80 [6,2047,30852,67522,233736,860688,1721376] t83
def b88 : List Row := [([6,2047,32710,233736,860688,1028888,1721376],[]),([6,2047,32710,233736,860688,1236463,1721376],[]),([6,2047,32710,233736,860688,1721376],[(10,0),(97,0),(1024,336370),(1024,337492)]),([6,2047,32710,233736,860688,1721376,1721376],[(1024,336370),(1024,337492)]),([6,2047,32710,233736,860688,1721376,1721407],[(1024,336370),(1024,337492)]),([6,2047,32710,233736,860688,1721376,1722338],[]),([6,2047,32710,233736,860688,1721376,1722367],[]),([6,2047,32710,233736,860688,1721376,1735844],[(1024,336370),(1024,337492)]),([6,2047,32710,233736,860688,1721376,1736678],[]),([6,2047,32710,233736,860688,1721376,1824040],[(1024,336370),(1024,337492)]),([6,2047,32710,233736,860688,1721376,2064441],[]),([6,2047,32710,233736,860688,1721376,2066299],[]),([6,2047,32710,233736,860688,1721376,2095104],[]),([6,2047,32710,233736,860688,1721376,2095165],[]),([6,2047,32710,233736,860688,1721376,2097088],[(196,0)]),([6,2047,32710,233736,860688,1721407],[(10,0),(1024,41458),(1024,42580),(1024,106863)]),([6,2047,32710,233736,860688,1722338],[(10,0),(97,0)]),([6,2047,32710,233736,860688,1722367],[(10,0)])]
def b89 : List Row := [([6,2047,32710,233736,1721376,2057776],[(1024,337492),(1024,609610)]),([6,2047,32767,233736,860688,1721376,1721407],[(1024,106863),(1024,106994),(1024,107092)]),([6,2047,32767,233736,860688,1721376,1722338],[]),([6,2047,32767,233736,860688,1721376,2095165],[(1024,106989)]),([6,2047,32767,233736,860688,1721376,2097088],[]),([6,2047,32767,233736,860688,1721407],[(1024,8690),(1024,9812),(1024,106863),(1024,374889)]),([6,2047,32767,233736,860688,1722338],[(10,0)]),([6,2047,233736,860688,1721376,1722338,1735844],[(1024,172525),(1024,173549),(1024,178281)]),([6,2047,233736,860688,1721376,1722338,1736678],[]),([6,2047,233736,860688,1721376,1722338,2066299],[(1024,184425)]),([6,2047,233736,860688,1721376,1735844,1736678],[(104,0),(1024,178281)]),([6,2047,233736,860688,1721376,1735844,2095165],[(1024,336365),(1024,337389)]),([6,2047,233736,860688,1721376,1735871],[(104,0),(1024,106989),(1024,499821),(1024,503913)]),([6,2047,233736,860688,1721376,1736678],[(6,0),(73,0),(105,0),(114,0)]),([6,2047,233736,860688,1721376,2064441],[(6,0),(73,0),(1024,336370),(1024,337492)]),([6,2047,233736,860688,1721376,2066240],[(1024,106989),(1024,499821),(1024,503913)]),([6,2047,233736,860688,1721376,2066299,2095165],[]),([6,2047,233736,860688,1721407,1735844],[(1024,14825),(1024,80361),(1024,106863),(1024,374889),(1024,499791)])]
def t85 : BT := .nd (blockTree b88) [6,2047,32710,233736,1236463,1721376] (blockTree b89)
def b90 : List Row := [([6,2047,233736,860688,1721407,2066299],[(1024,8690),(1024,9812),(1024,106863),(1024,106994),(1024,374889),(1024,499733)]),([6,2047,233736,860688,1722338,1735844],[(6,0),(73,0)]),([6,2047,233736,860688,1722338,1736678],[(6,0),(73,0),(114,0)]),([6,2047,233736,860688,1722338,2066299],[(6,0),(73,0)]),([6,6082,6143,30852,233736,860688,1721376],[]),([6,16384,32710,32767,233736,860688,1721376],[(96,0)]),([6,16416,32710,233736,860688,1721376],[(1024,53423),(1024,106837),(1024,184655),(1024,335986),(1024,337044),(1024,342197),(1024,348265)]),([6,16447,32710,233736,860688,1721376],[(1024,178517),(1024,184655),(1024,336370),(1024,337492),(1024,342197),(1024,348265),(1024,348335)]),([6,17440,30852,32710,233736,860688,1721376],[(1024,184425)]),([6,17471,30852,32710,233736,860688,1721376],[]),([6,18370,18431,30852,233736,860688,1721376],[]),([6,18402,30852,233736,860688,1721376],[(1024,106677),(1024,172146),(1024,173204),(1024,184425)]),([6,30852,30911,233736,235466,860688,1722338],[]),([6,30852,30911,233736,860688,1720352,2095165],[]),([6,30852,30911,233736,860688,1722338,2095165],[]),([6,30852,32710,32742,233736,860688,1721376],[(1024,184425)]),([6,30852,32710,32767,233736,375775,860688],[]),([6,30852,32710,32767,233736,860688,1721376],[])]
def b91 : List Row := [([6,30852,32710,233736,235519,860688,1721376],[]),([6,30852,32710,233736,262143,860688,1721376],[]),([6,30852,32710,233736,375807,860688],[(1024,106837),(1024,345193),(1024,347241),(1024,348265)]),([6,30852,32710,233736,860688,1721344],[(1024,106837),(1024,335986),(1024,337044),(1024,348265)]),([6,30852,32710,233736,860688,1721376,2064384],[]),([6,30852,32710,233736,860688,1721376,2095104],[]),([6,30852,32742,233736,860688,1721376],[(1024,106677),(1024,172146),(1024,173204),(1024,184425)]),([6,30852,32767,233736,860688,1721376,1722338],[(1024,184425)]),([6,30852,32767,233736,860688,1721376,1736678],[(1024,184425)]),([6,30852,32767,233736,860688,1721376,2064441],[]),([6,30852,32767,233736,860688,1721376,2095165],[]),([6,30852,67522,67583,233736,860688,1721376],[]),([6,30852,133058,133119,233736,860688,1721376],[]),([6,30852,133090,233736,860688,1721376],[(1024,106677),(1024,118953),(1024,173204),(1024,178281),(1024,184425)]),([6,30852,233736,233791,235466,860688,1722338],[]),([6,30852,233736,233791,235519,860688,1722338],[]),([6,30852,233736,233791,860688,862162,1722338],[])]
def t86 : BT := .nd (blockTree b90) [6,30852,32710,32767,233736,1236463,1721376] (blockTree b91)
def t87 : BT := .nd t85 [6,2047,233736,860688,1721407,1735871] t86
def b92 : List Row := [([6,30852,233736,233791,860688,1722338,2095165],[]),([6,30852,233736,235466,235519,860688,1722338],[]),([6,30852,233736,235466,860688,1722338,2097088],[]),([6,30852,233736,235519,860688,1721376,1722338],[(1024,184425)]),([6,30852,233736,235519,860688,1721376,2095165],[]),([6,30852,233736,235519,860688,1722338],[(6,0),(10,0)]),([6,30852,233736,375807,860688,2095165],[(1024,106831),(1024,106834),(1024,106836),(1024,106837),(1024,348265)]),([6,30852,233736,860688,1720352,2095165,2097088],[]),([6,30852,233736,860688,1721344,2095165],[(1024,106831),(1024,106834),(1024,106836),(1024,106837),(1024,348265)]),([6,30852,233736,860688,1721376,1722338,2095104],[]),([6,30852,233736,860688,1721376,2095104,2095165],[]),([6,30852,233736,860688,1721376,2095104,2095167],[]),([6,30852,233736,860688,1721376,2095133],[(1024,106671),(1024,106674),(1024,106676),(1024,106677),(1024,184425)]),([6,30852,233736,860688,1721407,2095104],[(1024,106863),(1024,499727),(1024,499730),(1024,499732),(1024,499733)]),([6,30852,233736,860688,1722338,2095104],[(6,0),(146,0)]),([6,30852,233736,860688,1722338,2095165,2097088],[]),([6,30884,32710,233736,860688,1721376],[(1024,106837),(1024,184655),(1024,335986),(1024,337044),(1024,342197),(1024,348265)]),([6,30911,32710,32767,233736,860688,1721376],[(1024,348269)])]
def b93 : List Row := [([6,30911,32710,233736,375775,860688],[(1024,110933),(1024,184655),(1024,342197),(1024,345197),(1024,347245),(1024,348269)]),([6,30911,32710,233736,860688,1721376],[(1024,110933),(1024,184655),(1024,336370),(1024,337492),(1024,342197),(1024,348265),(1024,348269)]),([6,30911,32710,233736,860688,1721376,2095165],[(1024,348269)]),([6,30911,32710,233736,1236463,1721376],[(1024,110933),(1024,184655),(1024,336370),(1024,342197),(1024,347245),(1024,348265),(1024,348269)]),([6,30911,32710,233736,1721376,2057776],[(1024,110932),(1024,337044),(1024,337492),(1024,342196),(1024,345197),(1024,609610)]),([6,30911,233736,860688,1721376,2064441],[(1024,106837),(1024,110930),(1024,110932),(1024,110933),(1024,342197),(1024,348269)]),([6,30911,233736,860688,1721376,2095104],[(1024,106989),(1024,499821)]),([6,32710,32767,233736,235466,860688,1721376],[]),([6,32710,32767,233736,260492,860688,1721376],[]),([6,32710,32767,233736,860688,1721376,2066299],[]),([6,32710,32767,233736,860688,1721376,2095165],[(1024,348269)]),([6,32710,233736,233791,235466,860688,1721376],[]),([6,32710,233736,233791,235519,860688,1721376],[]),([6,32710,233736,233791,860688,862162,1721376],[]),([6,32710,233736,233791,860688,1721376,2095165],[]),([6,32710,233736,235466,235519,860688,1721376],[]),([6,32710,233736,235466,860688,1721376,2097088],[])]
def t88 : BT := .nd (blockTree b92) [6,30911,32710,233736,235466,860688,1721376] (blockTree b93)
def b94 : List Row := [([6,32710,233736,260543,860688,1721376],[(1024,106837),(1024,184655),(1024,337492),(1024,342197)]),([6,32710,233736,860688,1721376,2066240],[(1024,342194),(1024,342196),(1024,342197),(1024,348269)]),([6,32710,233736,860688,1721376,2095104],[(6,0),(146,0),(1024,336370),(1024,337492)]),([6,32710,233736,860688,1721376,2095165,2097088],[]),([7,2,63,1986,30852,233736,860688,1722338],[(128,0)]),([7,2,63,1986,32710,233736,860688,1721376],[(128,0)]),([7,2,1986,2047,30852,233736,860688,1721376],[]),([7,4,63,1986,30852,233736,860688,1722338],[(128,0)]),([7,4,63,1986,32710,233736,860688,1721376],[(128,0)]),([7,4,1986,2047,30852,233736,860688,1721376],[(128,0)]),([7,6,63,1986,32710,233736,860688,1721376],[(128,0)]),([7,8,63,1986,30852,233736,860688,1722338],[]),([7,8,63,1986,32710,233736,860688,1721376],[]),([7,8,1986,2047,30852,233736,860688,1721376],[]),([7,32,63,1986,30852,233736,860688,1722338],[(128,0)]),([7,32,63,1986,32710,233736,860688,1721376],[(128,0)]),([7,32,1024,1986,30852,233736,860688,1721376],[(1024,184425),(1024,335893),(1024,336917),(1024,342121),(1024,348265)]),([7,32,1986,1986,30852,233736,860688,1721376],[(1024,348265)])]
def b95 : List Row := [([7,32,1986,2047,30852,233736,860688,1721376],[(128,0),(1024,348265)]),([7,32,1986,30852,32710,233736,860688,1721376],[(1024,348265)]),([7,32,1986,30852,233736,235466,860688,1721376],[(1024,184361),(1024,184425),(1024,348265)]),([7,32,1986,30852,233736,375775,860688],[(1024,106837),(1024,342121),(1024,345193),(1024,347241),(1024,348265)]),([7,32,1986,30852,233736,860688,1721376],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([7,32,1986,30852,233736,860688,1721376,1722338],[(1024,348265)]),([7,32,1986,30852,233736,860688,1721376,2095165],[(1024,348265)]),([7,32,1986,30852,233736,860688,1722338],[(14,0),(98,0),(129,0),(137,0)]),([7,32,1986,30852,233736,860720,1721376],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([7,32,1986,30852,233736,1236463,1721376],[(1024,106837),(1024,335986),(1024,342121),(1024,347241),(1024,348265)]),([7,32,1986,30852,233736,1721376,2057776],[(1024,106836),(1024,150858),(1024,337044),(1024,342121),(1024,345193)]),([7,32,1986,30884,233736,860688,1721376],[(96,0),(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([7,32,1986,32710,233736,860688,1721376],[(14,0),(98,0),(129,0),(137,0),(1024,335986),(1024,337044)]),([7,32,1986,233736,860688,1721376,1735844],[(144,0),(1024,106831),(1024,342121)]),([7,32,1986,233736,860688,1721376,2066299],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([7,32,2018,30852,233736,860688,1721376],[(96,0),(1024,106837),(1024,184425),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([7,32,30852,32710,233736,860688,1721376],[(1024,106837),(1024,335986),(1024,337044),(1024,348265)])]
def t89 : BT := .nd (blockTree b94) [7,32,1986,2018,30852,233736,860688,1721376] (blockTree b95)
def t90 : BT := .nd t88 [6,32710,233736,235519,860688,1721376] t89
def t91 : BT := .nd t87 [6,30852,233736,233791,860688,1720352,2095165] t90
def t92 : BT := .nd t84 [6,2047,32710,233736,375775,860688,1721376] t91
def t93 : BT := .nd t77 [6,1986,32767,233736,860688,1721376,2064441] t92
def b96 : List Row := [([7,34,63,1986,30852,233736,860688,1722338],[(128,0)]),([7,34,1986,30852,233736,860688,1721376],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([7,34,1986,30852,233736,860688,1721376,1722338],[(1024,348265)]),([7,34,1986,30852,233736,860688,1722338],[(14,0),(98,0),(129,0),(137,0)]),([7,36,1986,30852,233736,860688,1721376],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([7,36,1986,233736,860688,1721376,1735844],[(144,0),(1024,106831),(1024,342121)]),([7,40,1986,30852,233736,860688,1721376],[(1024,140629),(1024,336370),(1024,337044),(1024,342154),(1024,348265),(1024,348298)]),([7,40,1986,30852,860688,1721376,1824040],[(1024,140626),(1024,335986),(1024,336370),(1024,342154),(1024,345226),(1024,509257)]),([7,47,1986,30852,233736,860688,1721376],[(1024,140629),(1024,336370),(1024,337044),(1024,342154),(1024,348265),(1024,348298)]),([7,47,1986,30852,233736,1236463,1721376],[(1024,140629),(1024,336370),(1024,342154),(1024,347274),(1024,348265),(1024,348298)]),([7,59,1986,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,59,1986,233736,860688,1721376,2066299],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,61,1986,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,61,1986,30852,233736,860688,1721376,2095165],[(1024,348649)]),([7,61,30852,233736,860688,1721376,2095165],[(1024,106837),(1024,140629),(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,63,1986,30852,233736,860688,1722338],[(128,0)]),([7,63,63,1986,32710,233736,860688,1721376],[(128,0)]),([7,63,128,1986,30852,233736,860688,1722338],[(1024,238061),(1024,239085)])]
def b97 : List Row := [([7,63,256,1986,30852,233736,860688,1722338],[]),([7,63,256,1986,30852,235466,860688,1721376],[(176,0)]),([7,63,256,1986,32710,233736,860688,1721376],[]),([7,63,768,1986,30852,233736,860688,1721376],[(1024,348265),(1024,348649),(1024,348746)]),([7,63,962,1986,30852,233736,375775,860688],[(1024,348265),(1024,348649)]),([7,63,962,1986,30852,233736,860688,1721376],[(1024,348265),(1024,348649)]),([7,63,1024,1986,30852,233736,375775,860688],[(1024,342505),(1024,348649),(1024,375113),(1024,375114)]),([7,63,1024,1986,30852,233736,860688,1721376],[(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1024,1986,30852,233736,860688,1721407],[(1024,106863),(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1024,1986,30852,233736,860688,1722338],[]),([7,63,1024,1986,30852,233736,860735,1721376],[(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1024,1986,30852,233736,861712,1721376],[(1024,337263)]),([7,63,1024,1986,30852,233736,1236463,1721376],[(1024,336239),(1024,342505),(1024,348649)]),([7,63,1024,1986,30852,233736,1721376,2057776],[(1024,337492),(1024,342505),(1024,345577)]),([7,63,1024,1986,30911,233736,860688,1721376],[(1024,106989),(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1024,1986,31876,233736,860688,1721376],[(136,0),(1024,342505)]),([7,63,1024,1986,32710,233736,860688,1721376],[(1024,336239),(1024,337263)]),([7,63,1024,1986,233736,860688,1721376,1735844],[(192,0),(1024,342505),(1024,345577),(1024,347625)])]
def t94 : BT := .nd (blockTree b96) [7,63,128,1986,32710,233736,860688,1721376] (blockTree b97)
def b98 : List Row := [([7,63,1024,2047,30852,233736,860688,1721376],[(1024,106863),(1024,106989),(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1024,30852,32710,233736,860688,1721376],[(1024,336111),(1024,337135),(1024,348649)]),([7,63,1024,30852,233736,860688,1721376,1722338],[(192,0)]),([7,63,1024,30852,233736,860688,1721376,2095165],[(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,1024,32710,233736,860688,1721376],[(14,0),(98,0),(104,0),(106,0),(129,0),(137,0),(193,0)]),([7,63,1026,1986,30852,233736,860688,1721376],[(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1026,1986,30852,233736,860688,1721407],[(1024,106863),(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1056,1986,30852,233736,860688,1721376],[(1024,336239),(1024,337263),(1024,342505),(1024,348265),(1024,348649)]),([7,63,1056,2047,30852,233736,860688,1721376],[(1024,106863),(1024,106989),(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1087,1986,30852,233736,860688,1721376],[(128,0),(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1152,1986,30852,233736,860688,1721376],[(1024,244201),(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1152,1986,233736,860688,1721376,1735844],[(192,0),(1024,238061),(1024,239085),(1024,244201),(1024,342505)]),([7,63,1280,1986,30852,233736,860688,1721376],[(1024,336239),(1024,337263),(1024,342602),(1024,348649),(1024,348746)]),([7,63,1474,1986,30852,233736,860688,1721376],[(1024,217674),(1024,342602),(1024,348649)]),([7,63,1474,1986,30852,233736,1236463,1721376],[(1024,217674),(1024,342602),(1024,348649),(1024,374346)]),([7,63,1858,1986,30852,233736,860688,1721376],[(1024,348649)]),([7,63,1858,1986,233736,860688,1721376,2066299],[(1024,348649)]),([7,63,1858,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)])]
def b99 : List Row := [([7,63,1984,1986,30852,233736,860688,1721376],[(1024,348649)]),([7,63,1984,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,1986,30852,233736,375775,860688],[(1024,348649)]),([7,63,1986,1986,30852,233736,860688,1721376],[(1024,348649)]),([7,63,1986,1986,30852,233736,860688,1721407],[(1024,348649)]),([7,63,1986,1986,30852,233736,860688,1722338],[]),([7,63,1986,1986,30852,233736,860735,1721376],[(1024,348649)]),([7,63,1986,1986,30852,233736,1236463,1721376],[(1024,348649)]),([7,63,1986,1986,30911,233736,860688,1721376],[(1024,348649)]),([7,63,1986,1986,32710,233736,860688,1721376],[]),([7,63,1986,1986,233736,860688,1721376,1735844],[(1024,336365),(1024,337389),(1024,342505)]),([7,63,1986,1986,233736,860688,1721376,2066299],[(1024,348649)]),([7,63,1986,1990,30852,233736,860688,1721376],[(1024,348649)]),([7,63,1986,1994,30852,233736,860688,1721376],[(1024,348649)]),([7,63,1986,2018,30852,233736,860688,1721376],[(1024,184425),(1024,348265),(1024,348649)]),([7,63,1986,2047,30852,233736,375775,860688],[(1024,348649)]),([7,63,1986,2047,30852,233736,860688,1721376],[(1024,348649)])]
def t95 : BT := .nd (blockTree b98) [7,63,1858,233736,860688,1721376,2066299] (blockTree b99)
def t96 : BT := .nd t94 [7,63,1024,1986,233736,860688,1721376,2066299] t95
def b100 : List Row := [([7,63,1986,2047,30852,233736,860688,1722338],[]),([7,63,1986,2047,30852,233736,860688,1722367],[]),([7,63,1986,2047,30852,233736,860735,1721376],[(1024,41162),(1024,42351),(1024,42477),(1024,348649)]),([7,63,1986,2047,30852,233736,1236463,1721376],[(1024,348649)]),([7,63,1986,2047,30911,233736,860688,1721376],[(1024,41453),(1024,42477),(1024,106989),(1024,348649)]),([7,63,1986,2047,32710,233736,860688,1721376],[]),([7,63,1986,2047,32767,233736,860688,1721376],[]),([7,63,1986,2047,233736,860688,1721376,1735844],[(1024,336365),(1024,337389),(1024,342505)]),([7,63,1986,2047,233736,860688,1721376,2066299],[(1024,348649)]),([7,63,1986,4096,30852,233736,860688,1722338],[]),([7,63,1986,4096,32710,233736,860688,1721376],[]),([7,63,1986,4352,32710,233736,860688,1721376],[(1024,342609)]),([7,63,1986,6082,30852,233736,860688,1721376],[(1024,348649)]),([7,63,1986,12288,233736,860688,1721376],[(1024,336367),(1024,337487),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([7,63,1986,14468,233736,375775,860688],[(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([7,63,1986,14468,233736,860688,1721376],[(1024,336367),(1024,337487),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([7,63,1986,16384,30852,233736,860688,1722338],[(144,0),(1024,217581)]),([7,63,1986,16384,32710,233736,860688,1721376],[(144,0),(1024,217581),(1024,348649)])]
def b101 : List Row := [([7,63,1986,17408,30852,233736,860688,1721376],[(1024,336370),(1024,337394),(1024,342505),(1024,348649)]),([7,63,1986,17408,32710,233736,860688,1721376],[(1024,336370),(1024,337394)]),([7,63,1986,18370,30852,233736,860688,1721376],[(1024,348649)]),([7,63,1986,30724,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30724,233736,860688,1721376,2095165],[(1024,348649)]),([7,63,1986,30848,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,30852,233736,860688,1722338],[]),([7,63,1986,30852,30911,233736,860688,1722338],[]),([7,63,1986,30852,31876,233736,860688,1721376],[(1024,342505),(1024,348649)]),([7,63,1986,30852,32710,233736,375775,860688],[(1024,348649)]),([7,63,1986,30852,32710,233736,860688,1721376],[(1024,348649)]),([7,63,1986,30852,32710,233736,860688,1721407],[(1024,348649)]),([7,63,1986,30852,32710,233736,860688,1722338],[]),([7,63,1986,30852,32710,233736,860735,1721376],[(1024,348649)]),([7,63,1986,30852,32710,233736,1236463,1721376],[(1024,348649)]),([7,63,1986,30852,32767,233736,860688,1721376],[(1024,348649)]),([7,63,1986,30852,39375,233736,1721376],[(1024,337044),(1024,337492),(1024,342505),(1024,345577),(1024,347625),(1024,500052),(1024,609610)]),([7,63,1986,30852,65536,233736,860688,1722338],[])]
def t97 : BT := .nd (blockTree b100) [7,63,1986,16512,30852,233736,860688,1722338] (blockTree b101)
def b102 : List Row := [([7,63,1986,30852,67522,233736,860688,1721376],[(1024,348649)]),([7,63,1986,30852,102664,375775,860688],[(1024,342505),(1024,345193),(1024,345226),(1024,345577),(1024,500050)]),([7,63,1986,30852,102664,860688,1721376],[(1024,336370),(1024,337490),(1024,342505),(1024,345193),(1024,345226),(1024,345577),(1024,500050),(1024,509257)]),([7,63,1986,30852,131072,233736,860688,1722338],[]),([7,63,1986,30852,131328,233736,860688,1722338],[(1024,242031)]),([7,63,1986,30852,132096,233736,860688,1721376],[(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,63,1986,30852,133058,233736,860688,1721376],[(1024,348649)]),([7,63,1986,30852,233728,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,233736,860688,1722338],[]),([7,63,1986,30852,233736,233791,860688,1722338],[(104,0),(152,0)]),([7,63,1986,30852,233736,234760,860688,1721376],[(96,0),(1024,336239),(1024,348649)]),([7,63,1986,30852,233736,235466,375775,860688],[(1024,348649)]),([7,63,1986,30852,233736,235466,860688,1721376],[(1024,348649)]),([7,63,1986,30852,233736,235466,860688,1721407],[(1024,106863),(1024,348649)]),([7,63,1986,30852,233736,235466,860688,1722338],[]),([7,63,1986,30852,233736,235466,860735,1721376],[(1024,348649)]),([7,63,1986,30852,233736,235466,1236463,1721376],[(1024,348649)]),([7,63,1986,30852,233736,235519,860688,1721376],[(1024,348649)])]
def b103 : List Row := [([7,63,1986,30852,233736,262094,860688,1721376],[(1024,347625),(1024,348649)]),([7,63,1986,30852,233736,374813,860688],[(14,0),(98,0),(169,0),(177,0)]),([7,63,1986,30852,233736,374813,860688,1721376],[(1024,342505)]),([7,63,1986,30852,233736,374813,860688,1722338],[]),([7,63,1986,30852,233736,375744,860688],[(1024,342505),(1024,345577),(1024,347625),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,375775,376799,860688],[(252,0),(1024,342505),(1024,345577),(1024,347625),(1024,348649)]),([7,63,1986,30852,233736,375775,860688],[(1024,342505),(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,375775,860688,1722338],[(204,0),(1024,348265),(1024,348649)]),([7,63,1986,30852,233736,375775,860688,2095165],[(1024,348649)]),([7,63,1986,30852,233736,375775,860735],[(1024,342505),(1024,345577),(1024,347625),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,375775,1236463],[(1024,342505),(1024,345577),(1024,348265),(1024,348298),(1024,348649),(1024,500053),(1024,609610)]),([7,63,1986,30852,233736,375775,2057776],[(1024,337492),(1024,347241),(1024,347625),(1024,500052),(1024,604490),(1024,607562),(1024,609610)]),([7,63,1986,30852,233736,375807,860688],[(1024,342505),(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,376799,860688],[(14,0),(98,0),(169,0),(206,0)]),([7,63,1986,30852,233736,376799,860688,1721376],[(1024,342505),(1024,345577),(1024,347625),(1024,348649)]),([7,63,1986,30852,233736,860688,1028888,1722338],[(1024,217585),(1024,217681)]),([7,63,1986,30852,233736,860688,1030106,1721376],[(1024,342505),(1024,348649)])]
def t98 : BT := .nd (blockTree b102) [7,63,1986,30852,233736,260492,860688,1722338] (blockTree b103)
def t99 : BT := .nd t97 [7,63,1986,30852,65536,1028888,1721376] t98
def t100 : BT := .nd t96 [7,63,1986,2047,30852,233736,860688,1721407] t99
def b104 : List Row := [([7,63,1986,30852,233736,860688,1236463,1722338],[]),([7,63,1986,30852,233736,860688,1720352],[(14,0),(98,0),(129,0),(193,0)]),([7,63,1986,30852,233736,860688,1720352,1721376],[(192,0),(1024,348265),(1024,348649)]),([7,63,1986,30852,233736,860688,1720352,2095165],[]),([7,63,1986,30852,233736,860688,1721344],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860688,1721376,1722338],[(1024,348265),(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,1722367],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,1736678],[(1024,348265),(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,2064441],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,2095104],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,2095165],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,2095167],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,2095293],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,2095421],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,2096127],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721376,2096189],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721378],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)])]
def b105 : List Row := [([7,63,1986,30852,233736,860688,1721384],[(1024,336370),(1024,337492),(1024,342505),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860688,1721407],[(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860688,1721407,1722338],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721407,1722367],[(1024,348649)]),([7,63,1986,30852,233736,860688,1721407,2095165],[(1024,53737),(1024,348649)]),([7,63,1986,30852,233736,860688,1721504],[(1024,243817),(1024,243850),(1024,244201),(1024,336370),(1024,337492),(1024,499951)]),([7,63,1986,30852,233736,860688,1721632],[(1024,337492),(1024,342602),(1024,348298),(1024,348746),(1024,599381)]),([7,63,1986,30852,233736,860688,1722338],[(14,0),(98,0),(129,0),(137,0)]),([7,63,1986,30852,233736,860688,1722338,1722338],[]),([7,63,1986,30852,233736,860688,1722338,1722367],[]),([7,63,1986,30852,233736,860688,1722338,1735844],[(1024,244201)]),([7,63,1986,30852,233736,860688,1722338,1736678],[]),([7,63,1986,30852,233736,860688,1722338,1824040],[(1024,348746)]),([7,63,1986,30852,233736,860688,1722338,1824746],[]),([7,63,1986,30852,233736,860688,1722338,2066299],[]),([7,63,1986,30852,233736,860688,1722338,2095165],[]),([7,63,1986,30852,233736,860688,1722338,2097088],[(96,0),(252,0)]),([7,63,1986,30852,233736,860688,1722367],[(14,0),(98,0),(137,0)])]
def t101 : BT := .nd (blockTree b104) [7,63,1986,30852,233736,860688,1721380] (blockTree b105)
def b106 : List Row := [([7,63,1986,30852,233736,860688,1786912],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860690,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860692,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860696,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860720,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860735,862162,1721376],[(1024,348649)]),([7,63,1986,30852,233736,860735,862207,1721376],[(1024,348649)]),([7,63,1986,30852,233736,860735,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860735,1721376,1722338],[(1024,348649)]),([7,63,1986,30852,233736,860735,1721376,2095165],[(1024,348649)]),([7,63,1986,30852,233736,860735,1721407],[(1024,42351),(1024,79215),(1024,115055),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,860735,1722338],[(14,0)]),([7,63,1986,30852,233736,860816,1721376],[(1024,238701),(1024,238734),(1024,239085),(1024,243177),(1024,336370),(1024,337492),(1024,499950),(1024,504042)]),([7,63,1986,30852,233736,860944,1721376],[(106,0),(1024,337492),(1024,342602),(1024,345674),(1024,348298),(1024,348746),(1024,599381)]),([7,63,1986,30852,233736,861712,1721376],[(1024,336917),(1024,336975),(1024,337010),(1024,337044),(1024,337135),(1024,337263),(1024,337492),(1024,347625),(1024,375114),(1024,500052)]),([7,63,1986,30852,233736,862162,1028888,1721376],[(1024,217585),(1024,342513),(1024,348650),(1024,348746)]),([7,63,1986,30852,233736,862162,1236463,1721376],[(1024,348649)]),([7,63,1986,30852,233736,864784,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)])]
def b107 : List Row := [([7,63,1986,30852,233736,991760,1721376],[(1024,336373),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053),(1024,512329)]),([7,63,1986,30852,233736,1236416,1721376],[(1024,336370),(1024,342505),(1024,347625),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,1236463,1721376],[(1024,336370),(1024,342505),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,1236463,1721376,1722338],[(1024,348265),(1024,348649)]),([7,63,1986,30852,233736,1236463,1721376,2095165],[(1024,348649)]),([7,63,1986,30852,233736,1236463,1721407],[(1024,336370),(1024,342505),(1024,347625),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,1236463,1722338],[]),([7,63,1986,30852,233736,1236479,1721376],[(1024,336370),(1024,342505),(1024,347625),(1024,348265),(1024,348649),(1024,500053)]),([7,63,1986,30852,233736,1721376,1722338,2057776],[(1024,336074),(1024,337044),(1024,337389),(1024,337492)]),([7,63,1986,30852,233736,1721376,1760751],[(1024,336370),(1024,342505),(1024,347241),(1024,347274),(1024,347625),(1024,500052)]),([7,63,1986,30852,233736,1721376,2057776],[(1024,337044),(1024,337492),(1024,342505),(1024,345577),(1024,500052),(1024,609610)]),([7,63,1986,30852,233736,1721376,2057791],[(1024,337492),(1024,342505),(1024,345577),(1024,500052),(1024,609610)]),([7,63,1986,30852,233736,1721407,2057776],[(152,0),(1024,337492),(1024,342505),(1024,345577),(1024,500052),(1024,609610)]),([7,63,1986,30852,233736,1721407,2057791],[(1024,42580),(1024,337492),(1024,342505),(1024,345577),(1024,500052),(1024,609610)]),([7,63,1986,30852,233736,1735844,2057776],[(1024,337044),(1024,337389),(1024,337486),(1024,337492),(1024,341481),(1024,500052),(1024,609610)]),([7,63,1986,30852,233736,1824040,2057776],[(1024,336074),(1024,336369),(1024,337044),(1024,337261),(1024,337492),(1024,500052),(1024,609610)]),([7,63,1986,30852,233791,860735,1721376],[(1024,41162),(1024,78026),(1024,181450),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)])]
def t102 : BT := .nd (blockTree b106) [7,63,1986,30852,233736,877072,1721376] (blockTree b107)
def t103 : BT := .nd t101 [7,63,1986,30852,233736,860688,1725472] t102
def b108 : List Row := [([7,63,1986,30852,233791,1721376,2057776],[(152,0),(1024,337492),(1024,342505),(1024,345577),(1024,500052),(1024,609610)]),([7,63,1986,30852,1236463,1721376,1824040],[(1024,335986),(1024,336370),(1024,342505),(1024,500050),(1024,509257)]),([7,63,1986,30852,1236463,1721376,1863415],[(1024,342505),(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30852,1721376,1824040,2057776],[(1024,336074),(1024,337097),(1024,342505),(1024,345193),(1024,345226),(1024,345577),(1024,500050)]),([7,63,1986,30852,1824040,2057776],[(14,0),(98,0),(133,0),(1024,336074),(1024,336369),(1024,337097),(1024,344553)]),([7,63,1986,30854,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30860,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30884,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,30911,32710,233736,860688,1721376],[(1024,348269),(1024,348649)]),([7,63,1986,30911,32767,233736,860688,1721376],[(1024,348649)]),([7,63,1986,30911,233736,235466,860688,1721376],[(1024,106989),(1024,348649)]),([7,63,1986,30911,233736,375775,860688],[(1024,342505),(1024,345577),(1024,347625),(1024,348649),(1024,500053)]),([7,63,1986,30911,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,1986,30911,233736,860688,1721376,1722338],[(1024,348649)]),([7,63,1986,30911,233736,860688,1721376,2095165],[(1024,348649)]),([7,63,1986,30911,233736,860688,1721407],[(96,0),(1024,110959),(1024,144751),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,1986,30911,233736,860688,1722338],[(14,0),(98,0),(137,0)]),([7,63,1986,30911,233736,860735,1721376],[(1024,42477),(1024,110794),(1024,178378),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)])]
def b109 : List Row := [([7,63,1986,30911,233736,1721376,2057776],[(1024,337492),(1024,342505),(1024,345577),(1024,500052),(1024,609610)]),([7,63,1986,31108,233736,860688,1721376],[(1024,337492),(1024,342602),(1024,345674),(1024,348298),(1024,348746),(1024,599381)]),([7,63,1986,31876,233736,860688,1721376],[(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([7,63,1986,32710,32710,233736,860688,1721376],[]),([7,63,1986,32710,32767,233736,860688,1721376],[]),([7,63,1986,32710,65536,233736,860688,1721376],[]),([7,63,1986,32710,131072,233736,860688,1721376],[]),([7,63,1986,32710,233736,233736,860688,1721376],[]),([7,63,1986,32710,233736,233791,860688,1721376],[(104,0),(152,0)]),([7,63,1986,32710,233736,235466,860688,1721376],[]),([7,63,1986,32710,233736,260492,860688,1721376],[(1024,348649),(1024,348746)]),([7,63,1986,32710,233736,262094,860688,1721376],[(204,0)]),([7,63,1986,32710,233736,375775,860688],[(14,0),(98,0),(169,0),(177,0),(206,0)]),([7,63,1986,32710,233736,375775,860688,1721376],[(204,0),(1024,509257),(1024,609610)]),([7,63,1986,32710,233736,860688,1028888,1721376],[(1024,342513),(1024,342609)]),([7,63,1986,32710,233736,860688,1236463,1721376],[]),([7,63,1986,32710,233736,860688,1721376],[(14,0),(98,0),(129,0),(137,0),(1024,336370),(1024,337492)])]
def t104 : BT := .nd (blockTree b108) [7,63,1986,30911,233736,1236463,1721376] (blockTree b109)
def b110 : List Row := [([7,63,1986,32710,233736,860688,1721376,1721407],[(1024,336370),(1024,337492)]),([7,63,1986,32710,233736,860688,1721376,1722338],[]),([7,63,1986,32710,233736,860688,1721376,1735844],[(1024,336370),(1024,337492),(1024,342505)]),([7,63,1986,32710,233736,860688,1721376,1736678],[]),([7,63,1986,32710,233736,860688,1721376,1824040],[(1024,336370),(1024,337492)]),([7,63,1986,32710,233736,860688,1721376,2064441],[(1024,348649)]),([7,63,1986,32710,233736,860688,1721376,2066299],[(1024,348649)]),([7,63,1986,32710,233736,860688,1721376,2095165],[(1024,348649)]),([7,63,1986,32710,233736,860688,1721376,2097088],[(96,0),(252,0)]),([7,63,1986,32710,233736,860688,1721407],[(14,0),(98,0),(137,0),(1024,336370),(1024,337492)]),([7,63,1986,32710,233736,860688,1722338],[(14,0),(98,0),(129,0),(137,0)]),([7,63,1986,32710,233736,860735,1721376],[(14,0),(1024,336370),(1024,337492)]),([7,63,1986,32710,233736,1236463,1721376],[(1024,336370)]),([7,63,1986,32710,233736,1721376,2057776],[(1024,337044),(1024,337492),(1024,609610)]),([7,63,1986,32767,233736,860688,1721376],[(14,0),(98,0),(137,0),(1024,336370),(1024,337492)]),([7,63,1986,96388,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,161924,233736,860688,1721376],[(1024,336373),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053),(1024,512329)]),([7,63,1986,233736,235466,860688,1721376,1735844],[(1024,244201),(1024,336365),(1024,337389),(1024,342505)])]
def b111 : List Row := [([7,63,1986,233736,361307,860688,1721376],[(184,0),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([7,63,1986,233736,375775,860688,1735844],[(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([7,63,1986,233736,375775,860688,2066299],[(1024,342505),(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,233736,860688,1721376,1722338,1735844],[(1024,336365),(1024,337389),(1024,342121),(1024,342505)]),([7,63,1986,233736,860688,1721376,1722338,1736678],[]),([7,63,1986,233736,860688,1721376,1722338,2066299],[(1024,342505),(1024,348265),(1024,348649)]),([7,63,1986,233736,860688,1721376,1735844],[(144,0),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([7,63,1986,233736,860688,1721376,1735844,1736678],[(144,0),(1024,342121),(1024,342505)]),([7,63,1986,233736,860688,1721376,1735844,2095165],[(1024,336365),(1024,337389),(1024,342505)]),([7,63,1986,233736,860688,1721376,1735871],[(144,0),(1024,342505),(1024,500047)]),([7,63,1986,233736,860688,1721376,1736678],[(10,0),(74,0),(97,0),(105,0),(145,0),(154,0)]),([7,63,1986,233736,860688,1721376,2064441],[(10,0),(74,0),(97,0),(105,0),(1024,336370),(1024,337492),(1024,348649),(1024,500053)]),([7,63,1986,233736,860688,1721376,2066240],[(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,1986,233736,860688,1721376,2066299],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,233736,860688,1721376,2066299,2095165],[(1024,348649),(1024,500053)]),([7,63,1986,233736,860688,1721376,2066303],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,233736,860688,1721376,2066427],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)])]
def t105 : BT := .nd (blockTree b110) [7,63,1986,233736,235466,860688,1721376,2066299] (blockTree b111)
def t106 : BT := .nd t104 [7,63,1986,32710,233736,860688,1721376,1721376] t105
def t107 : BT := .nd t103 [7,63,1986,30852,233791,1236463,1721376] t106
def t108 : BT := .nd t100 [7,63,1986,30852,233736,860688,1234989,1721376] t107
def b112 : List Row := [([7,63,1986,233736,860688,1721407,1735844],[(144,0),(1024,342505),(1024,500047)]),([7,63,1986,233736,860688,1721407,1735871],[(144,0),(1024,342505),(1024,500047)]),([7,63,1986,233736,860688,1721407,2066299],[(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,1986,233736,860688,1722338,1735844],[(10,0),(74,0),(97,0),(105,0),(1024,244201),(1024,244298)]),([7,63,1986,233736,860688,1722338,1736678],[(10,0),(74,0),(97,0),(105,0),(154,0)]),([7,63,1986,233736,860688,1722338,2066299],[(10,0),(74,0),(97,0),(105,0)]),([7,63,1986,233736,860688,1735844,1824040],[(184,0),(1024,244201),(1024,336365),(1024,336367),(1024,340554),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([7,63,1986,233736,860735,1721376,1735844],[(144,0),(1024,342505),(1024,500047)]),([7,63,1986,233736,860735,1721376,2066299],[(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,1986,233736,1236463,1721376,1735844],[(1024,342121),(1024,342154),(1024,342505),(1024,500047)]),([7,63,1986,233736,1236463,1721376,2066299],[(1024,336370),(1024,342505),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1986,233736,1721376,1735844,2057776],[(1024,337389),(1024,341481),(1024,342121),(1024,342505),(1024,500047)]),([7,63,1986,233736,1721376,2057776,2066299],[(1024,337044),(1024,337487),(1024,337492),(1024,345577),(1024,500052),(1024,609610)]),([7,63,1986,233736,1735844,2057776],[(10,0),(133,0),(1024,337389),(1024,337486),(1024,341481)]),([7,63,1990,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,1994,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348298),(1024,348649),(1024,500053)]),([7,63,2018,30852,233736,860688,1721376],[(1024,184425),(1024,184458),(1024,184809),(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,2047,2047,30852,233736,860688,1721376],[(1024,106863),(1024,106989),(1024,348649)])]
def b113 : List Row := [([7,63,2047,30852,32767,233736,860688,1721376],[(1024,106863),(1024,348649)]),([7,63,2047,30852,233736,235466,860688,1721376],[(1024,106863),(1024,106989),(1024,348649)]),([7,63,2047,30852,233736,235519,860688,1721376],[(1024,106863),(1024,106989),(1024,348649)]),([7,63,2047,30852,233736,375775,860688],[(1024,184809),(1024,342505),(1024,345577),(1024,347625),(1024,348649),(1024,500053)]),([7,63,2047,30852,233736,860688,1721376],[(1024,184809),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,2047,30852,233736,860688,1721376,1722338],[(1024,348649)]),([7,63,2047,30852,233736,860688,1721376,1722367],[(1024,106989),(1024,348649)]),([7,63,2047,30852,233736,860688,1721376,2095104],[(1024,106863),(1024,106989),(1024,348649),(1024,500053)]),([7,63,2047,30852,233736,860688,1721376,2095165],[(1024,348649),(1024,500053)]),([7,63,2047,30852,233736,860688,1721407],[(96,0),(1024,20969),(1024,80361),(1024,106863),(1024,140655),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,2047,30852,233736,860688,1722338],[(14,0),(98,0),(129,0),(133,0),(137,0)]),([7,63,2047,30852,233736,860688,1722367],[(14,0),(98,0),(137,0)]),([7,63,2047,30852,233736,860735,1721376],[(1024,79337),(1024,106698),(1024,183785),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,2047,30852,233736,1236463,1721376],[(1024,184809),(1024,336370),(1024,342505),(1024,347625),(1024,348649),(1024,500053)]),([7,63,2047,30852,233736,1721376,2057776],[(1024,183785),(1024,337492),(1024,342505),(1024,345577),(1024,500052),(1024,609610)]),([7,63,2047,30911,233736,860688,1721376],[(96,0),(1024,106989),(1024,111081),(1024,140781),(1024,178665),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,2047,32710,233736,860688,1721376],[(14,0),(98,0),(129,0),(133,0),(137,0),(1024,336370),(1024,337492)]),([7,63,2047,32767,233736,860688,1721376],[(14,0),(98,0),(137,0),(1024,336370),(1024,337492)])]
def t109 : BT := .nd (blockTree b112) [7,63,2047,30852,32710,233736,860688,1721376] (blockTree b113)
def b114 : List Row := [([7,63,2047,233736,860688,1721376,2066299],[(1024,184809),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,63,6082,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,16384,32710,233736,860688,1721376],[(104,0),(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,17408,30852,32710,233736,860688,1721376],[(1024,184655),(1024,336370),(1024,337394),(1024,348649)]),([7,63,18370,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,30724,233736,860688,1721376,2095165],[(1024,106837),(1024,140629),(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,32710,32710,233736,860688,1721376],[(1024,184655),(1024,348649)]),([7,63,30852,32710,32767,233736,860688,1721376],[(1024,348649)]),([7,63,30852,32710,233736,235466,860688,1721376],[(1024,348649)]),([7,63,30852,32710,233736,262094,860688,1721376],[(1024,184655),(1024,347625),(1024,348649)]),([7,63,30852,32710,233736,375775,860688],[(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,30852,32710,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,30852,32710,233736,860688,1721376,1722338],[(1024,217581),(1024,348265),(1024,348269),(1024,348649)]),([7,63,30852,32710,233736,860688,1721376,1736678],[(1024,348265),(1024,348335),(1024,348649)]),([7,63,30852,32710,233736,860688,1721376,2064441],[(1024,184655),(1024,348649),(1024,500053)]),([7,63,30852,32710,233736,860688,1721376,2095165],[(1024,348649),(1024,500053)]),([7,63,30852,32710,233736,860688,1721407],[(1024,336370),(1024,337492),(1024,348649),(1024,500053)]),([7,63,30852,32710,233736,860735,1721376],[(1024,336370),(1024,337492),(1024,348649),(1024,500053)])]
def b115 : List Row := [([7,63,30852,32710,233736,1721376,2057776],[(1024,337044),(1024,337492),(1024,345577),(1024,500052),(1024,609610)]),([7,63,30852,32767,233736,860688,1721376],[(1024,184809),(1024,336370),(1024,337492),(1024,348649),(1024,500053)]),([7,63,30852,67522,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,30852,133058,233736,860688,1721376],[(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053),(1024,512329)]),([7,63,30852,233736,235466,860688,862162,1721376],[(1024,348649)]),([7,63,30852,233736,235466,860688,1721376,1722338],[(1024,348649)]),([7,63,30852,233736,235466,860688,1721376,2095165],[(1024,500053)]),([7,63,30852,233736,235466,860688,1722338],[(10,0),(14,0),(74,0),(129,0),(1024,217681),(1024,242031)]),([7,63,30852,233736,375775,860688,2095165],[(1024,106837),(1024,140629),(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,233736,860688,1720352,1721376,2095165],[(144,0),(1024,106837),(1024,500053)]),([7,63,30852,233736,860688,1720352,2095165],[(10,0),(74,0),(97,0),(145,0)]),([7,63,30852,233736,860688,1721376,1722338,2095165],[(1024,106837),(1024,500053)]),([7,63,30852,233736,860688,1721376,2064441],[(1024,106837),(1024,140629),(1024,348649),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,233736,860688,1721376,2095104],[(1024,348649),(1024,499893),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,233736,860688,1721376,2095165],[(1024,106837),(1024,140629),(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,233736,860688,1721376,2095165,2095165],[(1024,500053)]),([7,63,30852,233736,860688,1721376,2095165,2095167],[(1024,500053)])]
def t110 : BT := .nd (blockTree b114) [7,63,30852,32710,233736,1236463,1721376] (blockTree b115)
def t111 : BT := .nd t109 [7,63,2047,233736,860688,1721376,1735844] t110
def b116 : List Row := [([7,63,30852,233736,860688,1721376,2095165,2095421],[(1024,500053),(1024,599241)]),([7,63,30852,233736,860688,1721376,2095165,2096189],[(1024,500053)]),([7,63,30852,233736,860688,1721376,2095167],[(1024,106837),(1024,140629),(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,233736,860688,1721376,2095293],[(1024,106837),(1024,140629),(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,233736,860688,1721407,2095165],[(1024,348649),(1024,499765),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,233736,860688,1722338,2095165],[(10,0),(74,0),(97,0),(194,0)]),([7,63,30852,233736,860735,1721376,2095165],[(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,233736,1236463,1721376,2095165],[(1024,106837),(1024,140629),(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,30852,233736,1721376,2057776,2095165],[(1024,106836),(1024,337492),(1024,500047),(1024,500050),(1024,500052)]),([7,63,30911,32710,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,348269),(1024,348302),(1024,348335),(1024,348649),(1024,500053)]),([7,63,30911,32767,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,348649),(1024,500053)]),([7,63,30911,233736,860688,1721376,2095165],[(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,63,32710,233736,235466,860688,1721376],[(10,0),(14,0),(74,0),(129,0),(1024,336370),(1024,337492),(1024,342609)]),([7,63,32710,233736,260492,860688,1721376],[(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,348746),(1024,500053)]),([7,63,32710,233736,860688,1721376,2066299],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,63,32710,233736,860688,1721376,2095165],[(10,0),(74,0),(97,0),(194,0),(1024,336370),(1024,337492),(1024,348649),(1024,500053)]),([7,63,233736,860688,1721376,1735844,2095165],[(104,0),(1024,106831),(1024,140623),(1024,342505),(1024,500047)]),([7,63,233736,860688,1721376,2066299,2095165],[(1024,106837),(1024,140629),(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)])]
def b117 : List Row := [([7,132,1986,2047,30852,233736,860688,1721376],[(1024,238061),(1024,239085)]),([7,191,1986,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,256,1986,2047,30852,233736,860688,1721376],[]),([7,264,1986,2047,30852,233736,860688,1721376],[]),([7,319,1986,30852,233736,860688,1721376],[(1024,106837),(1024,337492),(1024,342121),(1024,345193),(1024,348265)]),([7,1024,1087,1986,30852,233736,860688,1721376],[(128,0)]),([7,1024,1986,2047,30852,233736,860688,1721376],[(1024,336239),(1024,337263)]),([7,1024,1986,30852,30911,233736,860688,1721376],[(1024,335951),(1024,336975),(1024,348649)]),([7,1024,1986,30852,233736,233791,860688,1721376],[(96,0),(1024,337010),(1024,342121),(1024,348265)]),([7,1024,1986,30852,233736,860688,1721376,2097088],[(1024,336239),(1024,337263),(1024,342505),(1024,348649)]),([7,1056,1986,2047,30852,233736,860688,1721376],[(1024,336239),(1024,337263)]),([7,1056,1986,30852,233736,860688,1721376],[(14,0),(98,0),(129,0),(193,0)]),([7,1087,1986,30852,233736,860688,1721376],[(14,0),(98,0),(129,0),(193,0)]),([7,1984,1986,30852,233736,860688,1721376,2097088],[(1024,348649)]),([7,1984,30852,233736,860688,1721376,2097088],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,1986,2047,30852,233736,860688,1721376],[]),([7,1986,1986,30852,30911,233736,860688,1721376],[(1024,348649)])]
def t112 : BT := .nd (blockTree b116) [7,128,1986,2047,30852,233736,860688,1721376] (blockTree b117)
def b118 : List Row := [([7,1986,1986,30852,233736,860688,1721376,2097088],[(1024,348649)]),([7,1986,2018,30852,233736,860688,1721376],[(14,0),(137,0),(1024,184425),(1024,184458),(1024,335986),(1024,337044)]),([7,1986,2047,2047,30852,233736,860688,1721376],[]),([7,1986,2047,4096,30852,233736,860688,1721376],[]),([7,1986,2047,16384,30852,233736,860688,1721376],[(144,0)]),([7,1986,2047,30852,30852,233736,860688,1721376],[]),([7,1986,2047,30852,30911,233736,860688,1721376],[(1024,106989),(1024,348649)]),([7,1986,2047,30852,32710,233736,860688,1721376],[]),([7,1986,2047,30852,32767,233736,860688,1721376],[]),([7,1986,2047,30852,65536,233736,860688,1721376],[]),([7,1986,2047,30852,131072,233736,860688,1721376],[]),([7,1986,2047,30852,233736,233736,860688,1721376],[]),([7,1986,2047,30852,233736,233791,860688,1721376],[(1024,140653),(1024,348265)]),([7,1986,2047,30852,233736,235466,860688,1721376],[]),([7,1986,2047,30852,233736,235519,860688,1721376],[]),([7,1986,2047,30852,233736,260492,860688,1721376],[]),([7,1986,2047,30852,233736,375775,860688],[(14,0),(177,0),(206,0)]),([7,1986,2047,30852,233736,375775,860688,1721376],[(204,0),(1024,509257),(1024,609610)])]
def b119 : List Row := [([7,1986,2047,30852,233736,860688,1236463,1721376],[]),([7,1986,2047,30852,233736,860688,1721376],[(14,0),(137,0),(1024,336370),(1024,337492)]),([7,1986,2047,30852,233736,860688,1721376,1721376],[(1024,336370),(1024,337492)]),([7,1986,2047,30852,233736,860688,1721376,1721407],[(1024,106863),(1024,184809),(1024,336370),(1024,337492)]),([7,1986,2047,30852,233736,860688,1721376,1722338],[]),([7,1986,2047,30852,233736,860688,1721376,1722367],[]),([7,1986,2047,30852,233736,860688,1721376,1735844],[(1024,336370),(1024,337492)]),([7,1986,2047,30852,233736,860688,1721376,1824040],[(1024,336370),(1024,337492)]),([7,1986,2047,30852,233736,860688,1721376,2066299],[]),([7,1986,2047,30852,233736,860688,1721376,2095104],[(1024,348649)]),([7,1986,2047,30852,233736,860688,1721376,2095165],[(1024,348649)]),([7,1986,2047,30852,233736,860688,1721376,2097088],[(252,0),(1024,348649)]),([7,1986,2047,30852,233736,860688,1721407],[(14,0),(1024,41458),(1024,42580),(1024,106863),(1024,140655)]),([7,1986,2047,30852,233736,860688,1722338],[(14,0),(129,0),(133,0),(137,0)]),([7,1986,2047,30852,233736,860688,1722367],[(14,0)]),([7,1986,2047,30852,233736,1236463,1721376],[(1024,336370)]),([7,1986,2047,30852,233736,1721376,2057776],[(1024,337492),(1024,609610)])]
def t113 : BT := .nd (blockTree b118) [7,1986,2047,30852,233736,860688,1028888,1721376] (blockTree b119)
def t114 : BT := .nd t112 [7,1986,1986,30852,233736,233791,860688,1721376] t113
def t115 : BT := .nd t111 [7,63,30852,233736,860688,1721376,2095165,2095293] t114
def b120 : List Row := [([7,1986,2047,32710,233736,860688,1721376],[(14,0),(129,0),(133,0),(137,0),(1024,336370),(1024,337492)]),([7,1986,2047,32767,233736,860688,1721376],[(14,0),(1024,336370),(1024,337492)]),([7,1986,2047,233736,860688,1721376,1735844],[(10,0),(105,0),(144,0),(145,0),(154,0)]),([7,1986,2047,233736,860688,1721376,2066299],[(10,0),(105,0),(1024,336370),(1024,337492)]),([7,1986,4159,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,16416,30852,233736,860688,1721376],[(1024,86191),(1024,106837),(1024,335986),(1024,337044),(1024,348265)]),([7,1986,16447,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30848,233736,860688,1721376,2097088],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,30884,233736,860688,1721376],[(1024,106837),(1024,184429),(1024,184462),(1024,335986),(1024,337044),(1024,348265)]),([7,1986,30852,30911,32710,233736,860688,1721376],[(1024,184655),(1024,348269),(1024,348649)]),([7,1986,30852,30911,32767,233736,860688,1721376],[(1024,348649)]),([7,1986,30852,30911,233736,235466,860688,1721376],[(1024,348649)]),([7,1986,30852,30911,233736,375775,860688],[(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,30911,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,30911,233736,860688,1721376,1722338],[(1024,348265),(1024,348269),(1024,348649)]),([7,1986,30852,30911,233736,860688,1721376,2095165],[(1024,348649)]),([7,1986,30852,30911,233736,860688,1722338],[(14,0),(129,0),(145,0)]),([7,1986,30852,30911,233736,1236463,1721376],[(1024,336370),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)])]
def b121 : List Row := [([7,1986,30852,32710,32767,233736,860688,1721376],[]),([7,1986,30852,32710,233736,233791,860688,1721376],[(1024,348265)]),([7,1986,30852,32710,233736,860688,1721376,2097088],[(1024,348649)]),([7,1986,30852,32767,233736,860688,1721376],[(14,0),(145,0),(1024,336370),(1024,337492)]),([7,1986,30852,65599,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,131104,233736,860688,1721376],[(1024,106837),(1024,118962),(1024,337044),(1024,342121),(1024,348265)]),([7,1986,30852,131135,233736,860688,1721376],[(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,233728,860688,1721376,2097088],[(1024,336370),(1024,337492),(1024,342505),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,233736,233768,860688,1721376],[(1024,106837),(1024,184361),(1024,184397),(1024,184465),(1024,337044),(1024,342121),(1024,348265)]),([7,1986,30852,233736,233791,235466,860688,1721376],[(1024,348237),(1024,348265)]),([7,1986,30852,233736,233791,235519,860688,1721376],[(1024,348265)]),([7,1986,30852,233736,233791,375775,860688],[(1024,106837),(1024,342121),(1024,347241),(1024,348265)]),([7,1986,30852,233736,233791,860688,862162,1721376],[(1024,348265)]),([7,1986,30852,233736,233791,860688,1721376],[(1024,106837),(1024,337492),(1024,342121),(1024,348265)]),([7,1986,30852,233736,233791,860688,1721376,1722338],[(1024,348265),(1024,348298)]),([7,1986,30852,233736,233791,860688,1721376,2095165],[(1024,348265),(1024,348746)]),([7,1986,30852,233736,233791,860688,1722338],[(10,0),(14,0)]),([7,1986,30852,233736,233791,1236463,1721376],[(1024,106837),(1024,342121),(1024,347241),(1024,348265)])]
def t116 : BT := .nd (blockTree b120) [7,1986,30852,30911,233736,1721376,2057776] (blockTree b121)
def b122 : List Row := [([7,1986,30852,233736,235466,235519,860688,1721376],[]),([7,1986,30852,233736,235466,860688,1721376,2097088],[(1024,348265),(1024,348649)]),([7,1986,30852,233736,235519,860688,1721376],[(10,0),(14,0),(1024,337492)]),([7,1986,30852,233736,260543,860688,1721376],[(1024,106837),(1024,337492),(1024,348265)]),([7,1986,30852,233736,375775,375807,860688],[(196,0),(1024,106837),(1024,342121),(1024,345193),(1024,347241),(1024,348265)]),([7,1986,30852,233736,375775,860688,2097088],[(1024,342505),(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,233736,375807,860688],[(10,0),(131,0),(158,0),(1024,348265),(1024,348298)]),([7,1986,30852,233736,375807,860688,1721376],[(184,0),(1024,106837),(1024,342121),(1024,345193),(1024,347241),(1024,348265)]),([7,1986,30852,233736,860688,1028927,1721376],[(1024,106837),(1024,342121),(1024,348265)]),([7,1986,30852,233736,860688,1236416,1721376],[(1024,140629),(1024,336370),(1024,342154),(1024,348265),(1024,348298),(1024,348649)]),([7,1986,30852,233736,860688,1721344],[(10,0),(99,0),(145,0),(1024,348265),(1024,348298)]),([7,1986,30852,233736,860688,1721344,1721376],[(144,0),(184,0),(1024,106837),(1024,342121),(1024,345193),(1024,347241),(1024,348265)]),([7,1986,30852,233736,860688,1721344,2097088],[(196,0),(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,233736,860688,1721376,1722338,2097088],[(1024,348649)]),([7,1986,30852,233736,860688,1721376,2066240],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,233736,860688,1721376,2095104],[(10,0),(194,0),(1024,336370),(1024,337492),(1024,348649),(1024,500053)]),([7,1986,30852,233736,860688,1721376,2095165,2097088],[(1024,348649),(1024,500053)]),([7,1986,30852,233736,860688,1721376,2097088],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)])]
def b123 : List Row := [([7,1986,30852,233736,860688,1721376,2097092],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,233736,860688,1721376,2097096],[(1024,106837),(1024,335986),(1024,337492),(1024,342121),(1024,348265)]),([7,1986,30852,233736,860688,1721376,2097119],[(1024,106837),(1024,335986),(1024,337044),(1024,342121),(1024,348265)]),([7,1986,30852,233736,860688,1721407,2097088],[(1024,53737),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,1986,30852,233736,860688,1722338,2097088],[(10,0),(97,0),(194,0),(197,0)]),([7,1986,30852,233736,860735,1236463,1721376],[(1024,140629),(1024,336370),(1024,342154),(1024,348265),(1024,348298)]),([7,1986,30852,233736,860735,1721376,2097088],[(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,1986,30852,233736,1236463,1721376,2097088],[(1024,336370),(1024,342505),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30852,233736,1721376,2057776,2097088],[(1024,337492),(1024,342505),(1024,345577),(1024,347241),(1024,500052),(1024,609610)]),([7,1986,30911,32710,233736,860688,1721376],[(14,0),(129,0),(137,0),(1024,184655),(1024,336370),(1024,337492),(1024,348269),(1024,348649)]),([7,1986,30911,233736,860688,1721376,2066299],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,1986,30911,233736,860688,1721376,2097088],[(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,1986,32710,32767,233736,860688,1721376],[(14,0),(129,0),(145,0),(1024,336370),(1024,337492)]),([7,1986,32710,233736,233791,860688,1721376],[(10,0),(14,0),(1024,337492)]),([7,1986,32710,233736,860688,1721376,2097088],[(10,0),(97,0),(194,0),(197,0),(1024,336370),(1024,337492)]),([7,1986,233736,233791,860688,1721376,1735844],[(1024,106831),(1024,342121)]),([7,1986,233736,233791,860688,1721376,2066299],[(1024,106837),(1024,337492),(1024,342121),(1024,348265)])]
def t117 : BT := .nd (blockTree b122) [7,1986,30852,233736,860688,1721376,2097090] (blockTree b123)
def t118 : BT := .nd t116 [7,1986,30852,233736,233791,1721376,2057776] t117
def b124 : List Row := [([7,1986,233736,860688,1721376,2066299,2097088],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([7,2018,30852,233736,860688,1721376],[(10,0),(99,0),(145,0),(1024,184425),(1024,184458)]),([7,2047,30852,30911,233736,860688,1721376],[(1024,106989),(1024,107086),(1024,111081),(1024,178665),(1024,184809),(1024,336370),(1024,337492),(1024,348649),(1024,500053)]),([7,2047,30852,32710,233736,860688,1721376],[(14,0),(129,0),(137,0),(141,0),(1024,336370),(1024,337492)]),([7,2047,30852,233736,860688,1721376,1721407],[(144,0),(1024,20969),(1024,106863),(1024,106994),(1024,107092),(1024,178665),(1024,181737),(1024,183785),(1024,184809),(1024,499893)]),([7,2047,30852,233736,860688,1721376,1722338],[(10,0),(97,0),(145,0),(154,0),(158,0)]),([7,2047,30852,233736,860688,1721376,2095165],[(10,0),(97,0),(1024,336370),(1024,337492),(1024,348649),(1024,500053)]),([7,2047,30852,233736,860688,1721376,2097088],[(1024,184809),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([7,2047,30852,233736,860688,1721407],[(10,0),(145,0),(1024,20969),(1024,106863),(1024,106994),(1024,140655),(1024,140884)]),([7,2047,30852,233736,860688,1722338],[(10,0),(11,0),(13,0),(97,0),(99,0),(103,0),(107,0),(111,0),(155,0),(159,0)]),([7,2047,30911,233736,860688,1721376],[(10,0),(145,0),(1024,106989),(1024,111081),(1024,140878),(1024,348649)]),([7,2047,32710,233736,860688,1721376],[(10,0),(11,0),(13,0),(97,0),(99,0),(103,0),(107,0),(111,0),(145,0),(155,0),(159,0)]),([7,30852,30911,32710,233736,860688,1721376],[(1024,184655),(1024,336370),(1024,337492),(1024,348265),(1024,348269),(1024,348298),(1024,348302),(1024,348335),(1024,348649),(1024,500053)]),([7,30852,30911,32767,233736,860688,1721376],[(1024,184809),(1024,336370),(1024,337492),(1024,348649),(1024,500053)]),([7,30852,30911,233736,860688,1721376,2095165],[(1024,106837),(1024,140629),(1024,348649),(1024,500050),(1024,500052),(1024,500053)]),([7,30852,32710,32767,233736,860688,1721376],[(14,0),(129,0),(145,0),(1024,336370),(1024,337492)]),([7,30852,32710,233736,233791,860688,1721376],[(1024,106837),(1024,337492),(1024,348265)]),([7,30852,32710,233736,860688,1721376,2097088],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)])]
def b125 : List Row := [([7,30852,233736,860688,1721376,2095165,2097088],[(1024,106837),(1024,140629),(1024,348649),(1024,500047),(1024,500050),(1024,500052),(1024,500053)]),([7,30911,32710,233736,860688,1721376],[(10,0),(97,0),(145,0),(1024,184655),(1024,348269),(1024,348302),(1024,348335),(1024,348649)]),([8,2,63,1986,30852,233736,860688,1721376],[(128,0),(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,4,63,1986,30852,233736,860688,1721376],[(128,0),(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,8,63,1986,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348298),(1024,348649),(1024,500053)]),([8,32,63,1986,30852,233736,860688,1721376],[(128,0),(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,32,1986,30852,233736,860688,1721376],[(14,0),(98,0),(129,0),(139,0),(193,0),(1024,348265),(1024,348298)]),([8,63,63,1986,30852,233736,860688,1721376],[(128,0),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]),([8,63,128,1986,30852,233736,860688,1721376],[(136,0),(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,256,1986,30852,233736,860688,1721376],[(1024,337492),(1024,342602),(1024,345674),(1024,348298),(1024,348649),(1024,348746),(1024,599381)]),([8,63,1024,1986,30852,233736,860688,1721376],[(18,0),(130,0),(136,0),(138,0),(169,0),(177,0),(249,0),(1024,348649)]),([8,63,1986,1986,30852,233736,860688,1721376],[(18,0),(130,0),(169,0),(177,0),(1024,336370),(1024,337492),(1024,348649),(1024,348746)]),([8,63,1986,2047,30852,233736,860688,1721376],[(18,0),(130,0),(169,0),(173,0),(177,0),(185,0),(1024,336370),(1024,337492),(1024,348649),(1024,348746)]),([8,63,1986,4096,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,16384,30852,233736,860688,1721376],[(144,0),(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,30852,30852,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,30852,30911,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,348649),(1024,500053)])]
def t119 : BT := .nd (blockTree b124) [7,30852,233736,233791,860688,1721376,2095165] (blockTree b125)
def b126 : List Row := [([8,63,1986,30852,65536,233736,860688,1721376],[(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,30852,131072,233736,860688,1721376],[(1024,336373),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053),(1024,512329)]),([8,63,1986,30852,233736,233736,860688,1721376],[(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,348746),(1024,500053)]),([8,63,1986,30852,233736,233791,860688,1721376],[(106,0),(152,0),(1024,337492),(1024,342505),(1024,348265),(1024,348649),(1024,348746),(1024,500053)]),([8,63,1986,30852,233736,235466,860688,1721376],[(14,0),(18,0),(98,0),(169,0),(193,0),(1024,238061),(1024,336370),(1024,337492),(1024,348649),(1024,348746)]),([8,63,1986,30852,233736,260492,860688,1721376],[(1024,238061),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,348746),(1024,500053)]),([8,63,1986,30852,233736,375775,860688],[(14,0),(98,0),(169,0),(179,0),(206,0),(1024,348649),(1024,348746)]),([8,63,1986,30852,233736,375775,860688,1721376],[(204,0),(240,0),(1024,342505),(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,30852,233736,860688,1028888,1721376],[(106,0),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,30852,233736,860688,1236463,1721376],[(1024,336370),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,30852,233736,860688,1721376],[(14,0),(98,0),(129,0),(139,0),(193,0),(1024,348649),(1024,348746)]),([8,63,1986,30852,233736,860688,1721376,1721376],[(192,0),(1024,342505),(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,30852,233736,860688,1721376,1721407],[(192,0),(240,0),(1024,342505),(1024,345577),(1024,347625),(1024,348649),(1024,500053)]),([8,63,1986,30852,233736,860688,1721376,1722338],[(14,0),(98,0),(129,0),(137,0),(193,0),(202,0),(206,0),(1024,348649),(1024,348746)]),([8,63,1986,30852,233736,860688,1721376,1735844],[(192,0),(1024,342505),(1024,345577),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,30852,233736,860688,1721376,1824040],[(240,0),(1024,336370),(1024,336373),(1024,342505),(1024,345674),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053),(1024,512329)]),([8,63,1986,30852,233736,860688,1721376,2066299],[(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]),([8,63,1986,30852,233736,860688,1721376,2095165],[(14,0),(98,0),(129,0),(137,0),(250,0),(1024,336370),(1024,337492),(1024,348649),(1024,348746),(1024,500053),(1024,599381)])]
def b127 : List Row := [([8,63,1986,30852,233736,860688,1721407],[(14,0),(98,0),(139,0),(193,0),(1024,348649),(1024,348746)]),([8,63,1986,30852,233736,860688,1722338],[(14,0),(15,0),(17,0),(98,0),(129,0),(131,0),(135,0),(137,0),(139,0),(143,0),(147,0),(151,0),(203,0),(207,0)]),([8,63,1986,30852,233736,860735,1721376],[(14,0),(193,0),(1024,348649),(1024,348746)]),([8,63,1986,30852,233736,1236463,1721376],[(1024,348649),(1024,348746)]),([8,63,1986,30852,233736,1721376,2057776],[(14,0),(173,0),(1024,337492),(1024,347625)]),([8,63,1986,30911,233736,860688,1721376],[(14,0),(98,0),(139,0),(193,0),(1024,348649),(1024,348746)]),([8,63,1986,32710,233736,860688,1721376],[(14,0),(15,0),(17,0),(98,0),(129,0),(131,0),(135,0),(137,0),(139,0),(143,0),(147,0),(151,0),(193,0),(203,0),(207,0)]),([8,63,1986,233736,860688,1721376,1735844],[(10,0),(74,0),(97,0),(107,0),(144,0),(145,0),(154,0),(1024,342505),(1024,342602)]),([8,63,1986,233736,860688,1721376,2066299],[(10,0),(74,0),(97,0),(107,0),(145,0),(1024,348649),(1024,348746)]),([8,63,2047,30852,233736,860688,1721376],[(14,0),(98,0),(139,0),(193,0),(1024,348649),(1024,348746)]),([8,63,30852,32710,233736,860688,1721376],[(14,0),(98,0),(129,0),(137,0),(147,0),(193,0),(1024,348649),(1024,348746)]),([8,63,30852,233736,860688,1721376,2095165],[(10,0),(74,0),(97,0),(145,0),(195,0),(1024,500053),(1024,599381)]),([8,1986,2047,30852,233736,860688,1721376],[(14,0),(15,0),(17,0),(131,0),(135,0),(137,0),(139,0),(143,0),(147,0),(151,0),(193,0),(203,0),(207,0)]),([8,1986,30852,30911,233736,860688,1721376],[(14,0),(131,0),(145,0),(193,0),(1024,348649),(1024,348746)]),([8,1986,30852,233736,233791,860688,1721376],[(10,0),(14,0),(1024,348265),(1024,348746)]),([8,1986,30852,233736,860688,1721376,2097088],[(10,0),(99,0),(145,0),(194,0),(197,0),(1024,348649),(1024,348746)]),([9,63,1986,30852,233736,860688,1721376],[(14,0),(15,0),(17,0),(98,0),(129,0),(131,0),(135,0),(139,0),(143,0),(147,0),(151,0),(193,0),(203,0),(207,0)])]
def t120 : BT := .nd (blockTree b126) [8,63,1986,30852,233736,860688,1721376,2097088] (blockTree b127)
def t121 : BT := .nd t119 [8,63,1986,30852,32710,233736,860688,1721376] t120
def t122 : BT := .nd t118 [7,1986,233736,860688,1721376,1735844,2097088] t121
def t123 : BT := .nd t115 [7,1986,2047,30911,233736,860688,1721376] t122
def t124 : BT := .nd t108 [7,63,1986,233736,860688,1721376,2082683] t123
def t125 : BT := .nd t93 [7,32,30852,233736,860688,1721376,2095165] t124
def t126 : BT := .nd t62 [6,1986,2047,30720,233736,860688,1721376] t125
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
theorem ct0 : Covered mP t0 := coveredNode cb0 cb1 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct1 : Covered mP t1 := coveredNode cb2 cb3 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct2 : Covered mP t2 := coveredNode ct0 ct1 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct3 : Covered mP t3 := coveredNode cb4 cb5 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct4 : Covered mP t4 := coveredNode cb6 cb7 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct5 : Covered mP t5 := coveredNode ct3 ct4 (h := [(1024,20809),(1024,342058)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct6 : Covered mP t6 := coveredNode ct2 ct5 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct7 : Covered mP t7 := coveredNode cb8 cb9 (h := [(1024,172074)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct8 : Covered mP t8 := coveredNode cb10 cb11 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct9 : Covered mP t9 := coveredNode ct7 ct8 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct10 : Covered mP t10 := coveredNode cb12 cb13 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct11 : Covered mP t11 := coveredNode cb14 cb15 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct12 : Covered mP t12 := coveredNode ct10 ct11 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct13 : Covered mP t13 := coveredNode ct9 ct12 (h := [(104,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct14 : Covered mP t14 := coveredNode ct6 ct13 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct15 : Covered mP t15 := coveredNode cb16 cb17 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct16 : Covered mP t16 := coveredNode cb18 cb19 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct17 : Covered mP t17 := coveredNode ct15 ct16 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct18 : Covered mP t18 := coveredNode cb20 cb21 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct19 : Covered mP t19 := coveredNode cb22 cb23 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct20 : Covered mP t20 := coveredNode ct18 ct19 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct21 : Covered mP t21 := coveredNode ct17 ct20 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct22 : Covered mP t22 := coveredNode cb24 cb25 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct23 : Covered mP t23 := coveredNode cb26 cb27 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct24 : Covered mP t24 := coveredNode ct22 ct23 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct25 : Covered mP t25 := coveredNode cb28 cb29 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct26 : Covered mP t26 := coveredNode cb30 cb31 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct27 : Covered mP t27 := coveredNode ct25 ct26 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct28 : Covered mP t28 := coveredNode ct24 ct27 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct29 : Covered mP t29 := coveredNode ct21 ct28 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct30 : Covered mP t30 := coveredNode ct14 ct29 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct31 : Covered mP t31 := coveredNode cb32 cb33 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct32 : Covered mP t32 := coveredNode cb34 cb35 (h := [(1024,336074),(1024,342505)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct33 : Covered mP t33 := coveredNode ct31 ct32 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct34 : Covered mP t34 := coveredNode cb36 cb37 (h := [(1024,211437),(1024,342505)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct35 : Covered mP t35 := coveredNode cb38 cb39 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct36 : Covered mP t36 := coveredNode ct34 ct35 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct37 : Covered mP t37 := coveredNode ct33 ct36 (h := [(1024,238061),(1024,239085),(1024,337389)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct38 : Covered mP t38 := coveredNode cb40 cb41 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct39 : Covered mP t39 := coveredNode cb42 cb43 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct40 : Covered mP t40 := coveredNode ct38 ct39 (h := [(1024,342513)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct41 : Covered mP t41 := coveredNode cb44 cb45 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct42 : Covered mP t42 := coveredNode cb46 cb47 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct43 : Covered mP t43 := coveredNode ct41 ct42 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct44 : Covered mP t44 := coveredNode ct40 ct43 (h := [(112,0),(1024,342609)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct45 : Covered mP t45 := coveredNode ct37 ct44 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct46 : Covered mP t46 := coveredNode cb48 cb49 (h := [(1024,335981),(1024,336014),(1024,336365),(1024,500045),(1024,504137)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct47 : Covered mP t47 := coveredNode cb50 cb51 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct48 : Covered mP t48 := coveredNode ct46 ct47 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct49 : Covered mP t49 := coveredNode cb52 cb53 (h := [(1024,110959)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct50 : Covered mP t50 := coveredNode cb54 cb55 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct51 : Covered mP t51 := coveredNode ct49 ct50 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct52 : Covered mP t52 := coveredNode ct48 ct51 (h := [(1024,336367),(1024,337487),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct53 : Covered mP t53 := coveredNode cb56 cb57 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct54 : Covered mP t54 := coveredNode cb58 cb59 (h := [(1024,335893),(1024,336917),(1024,342121),(1024,348265)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct55 : Covered mP t55 := coveredNode ct53 ct54 (h := [(1024,238061),(1024,239085)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct56 : Covered mP t56 := coveredNode cb60 cb61 (h := [(144,0)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct57 : Covered mP t57 := coveredNode cb62 cb63 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct58 : Covered mP t58 := coveredNode ct56 ct57 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct59 : Covered mP t59 := coveredNode ct55 ct58 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct60 : Covered mP t60 := coveredNode ct52 ct59 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct61 : Covered mP t61 := coveredNode ct45 ct60 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct62 : Covered mP t62 := coveredNode ct30 ct61 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct63 : Covered mP t63 := coveredNode cb64 cb65 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct64 : Covered mP t64 := coveredNode cb66 cb67 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct65 : Covered mP t65 := coveredNode ct63 ct64 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct66 : Covered mP t66 := coveredNode cb68 cb69 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct67 : Covered mP t67 := coveredNode cb70 cb71 (h := [(1024,184425)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct68 : Covered mP t68 := coveredNode ct66 ct67 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct69 : Covered mP t69 := coveredNode ct65 ct68 (h := [(1024,504137),(1024,504138)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct70 : Covered mP t70 := coveredNode cb72 cb73 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct71 : Covered mP t71 := coveredNode cb74 cb75 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct72 : Covered mP t72 := coveredNode ct70 ct71 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct73 : Covered mP t73 := coveredNode cb76 cb77 (h := [(1024,106837),(1024,110772),(1024,177173),(1024,178218),(1024,335986)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct74 : Covered mP t74 := coveredNode cb78 cb79 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct75 : Covered mP t75 := coveredNode ct73 ct74 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct76 : Covered mP t76 := coveredNode ct72 ct75 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct77 : Covered mP t77 := coveredNode ct69 ct76 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct78 : Covered mP t78 := coveredNode cb80 cb81 (h := [(104,0),(1024,106831),(1024,342121)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct79 : Covered mP t79 := coveredNode cb82 cb83 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct80 : Covered mP t80 := coveredNode ct78 ct79 (h := [(1024,184425)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct81 : Covered mP t81 := coveredNode cb84 cb85 (h := [(1024,184425)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct82 : Covered mP t82 := coveredNode cb86 cb87 (h := [(1024,106989)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct83 : Covered mP t83 := coveredNode ct81 ct82 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct84 : Covered mP t84 := coveredNode ct80 ct83 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct85 : Covered mP t85 := coveredNode cb88 cb89 (h := [(1024,336370)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct86 : Covered mP t86 := coveredNode cb90 cb91 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct87 : Covered mP t87 := coveredNode ct85 ct86 (h := [(104,0),(1024,14825),(1024,106863),(1024,106989),(1024,140781),(1024,499727)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct88 : Covered mP t88 := coveredNode cb92 cb93 (h := [(1024,348269)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct89 : Covered mP t89 := coveredNode cb94 cb95 (h := [(128,0),(1024,184425),(1024,348265)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct90 : Covered mP t90 := coveredNode ct88 ct89 (h := [(6,0),(10,0),(1024,337492)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct91 : Covered mP t91 := coveredNode ct87 ct90 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct92 : Covered mP t92 := coveredNode ct84 ct91 (h := [(156,0),(1024,509257),(1024,609610)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct93 : Covered mP t93 := coveredNode ct77 ct92 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct94 : Covered mP t94 := coveredNode cb96 cb97 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct95 : Covered mP t95 := coveredNode cb98 cb99 (h := [(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct96 : Covered mP t96 := coveredNode ct94 ct95 (h := [(1024,336239),(1024,337263),(1024,348649)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct97 : Covered mP t97 := coveredNode cb100 cb101 (h := [(1024,238061),(1024,239085)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct98 : Covered mP t98 := coveredNode cb102 cb103 (h := [(1024,242031)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct99 : Covered mP t99 := coveredNode ct97 ct98 (h := [(1024,336370),(1024,342505),(1024,348265),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct100 : Covered mP t100 := coveredNode ct96 ct99 (h := [(1024,41327),(1024,42351),(1024,106863),(1024,348649)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct101 : Covered mP t101 := coveredNode cb104 cb105 (h := [(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct102 : Covered mP t102 := coveredNode cb106 cb107 (h := [(1024,336370),(1024,337492),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct103 : Covered mP t103 := coveredNode ct101 ct102 (h := [(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct104 : Covered mP t104 := coveredNode cb108 cb109 (h := [(1024,336370),(1024,342505),(1024,347625),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct105 : Covered mP t105 := coveredNode cb110 cb111 (h := [(1024,348649)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct106 : Covered mP t106 := coveredNode ct104 ct105 (h := [(1024,336370),(1024,337492)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct107 : Covered mP t107 := coveredNode ct103 ct106 (h := [(1024,336370),(1024,342505),(1024,347625),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct108 : Covered mP t108 := coveredNode ct100 ct107 (h := [(1024,348298)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct109 : Covered mP t109 := coveredNode cb112 cb113 (h := [(1024,348649)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct110 : Covered mP t110 := coveredNode cb114 cb115 (h := [(1024,336370),(1024,347625),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct111 : Covered mP t111 := coveredNode ct109 ct110 (h := [(144,0),(1024,178665),(1024,342505),(1024,500047)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct112 : Covered mP t112 := coveredNode cb116 cb117 (h := [(1024,238061),(1024,239085)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct113 : Covered mP t113 := coveredNode cb118 cb119 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct114 : Covered mP t114 := coveredNode ct112 ct113 (h := [(1024,348265)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct115 : Covered mP t115 := coveredNode ct111 ct114 (h := [(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct116 : Covered mP t116 := coveredNode cb120 cb121 (h := [(1024,337044),(1024,337492),(1024,345577),(1024,500052),(1024,609610)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct117 : Covered mP t117 := coveredNode cb122 cb123 (h := [(1024,336370),(1024,337492),(1024,342505),(1024,348265),(1024,348298),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct118 : Covered mP t118 := coveredNode ct116 ct117 (h := [(1024,106836),(1024,337044),(1024,337492),(1024,342121),(1024,609610)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct119 : Covered mP t119 := coveredNode cb124 cb125 (h := [(1024,106831),(1024,106836),(1024,106837),(1024,348265),(1024,599381)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct120 : Covered mP t120 := coveredNode cb126 cb127 (h := [(96,0),(252,0),(1024,336370),(1024,337492),(1024,342505),(1024,348649),(1024,500053)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct121 : Covered mP t121 := coveredNode ct119 ct120 (h := [(18,0),(130,0),(169,0),(177,0),(185,0),(189,0),(193,0),(1024,336370),(1024,337492),(1024,348649),(1024,348746)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct122 : Covered mP t122 := coveredNode ct118 ct121 (h := [(104,0),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct123 : Covered mP t123 := coveredNode ct115 ct122 (h := [(14,0),(1024,106989),(1024,140781),(1024,336370),(1024,337492),(1024,348649)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct124 : Covered mP t124 := coveredNode ct108 ct123 (h := [(1024,336367),(1024,337487),(1024,342121),(1024,342154),(1024,342505),(1024,500047)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct125 : Covered mP t125 := coveredNode ct93 ct124 (h := [(1024,106831),(1024,106834),(1024,106836),(1024,106837),(1024,348265)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct126 : Covered mP t126 := coveredNode ct62 ct125 (h := []) (by decide +kernel)
theorem hT_cert : Covered mP T_cert := ct126
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270551487 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by

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
    refine ⟨pt 6 (pairCode (0,0)),pt 6 (pairCode (1,3)),?_⟩
    rw [he (0,0),he (1,3)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 9 10 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 9 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end PEqualNP.Outside.L_meta_25035.Lower

theorem PEqualNP.Outside.L_meta_25035 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270551487 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := PEqualNP.Outside.L_meta_25035.Lower.lower
