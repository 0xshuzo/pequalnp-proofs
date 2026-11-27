import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24070.Lower

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



def pairCode (p : Fin 5 × Fin 5) : Nat := 2 ^ p.1.val ||| 2 ^ p.2.val
def reference (x : Fin 5 → Bool) : Bool :=
  (!((x 3 && (x 0 || x 2)) || ((x 1 && (x 3 || (x 0 || x 2))) || (x 4 && (!(x 0 || x 1))))))
def pairInput (i j : Fin 5) := List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)
theorem codeInputs : ∀ p : Fin 5 × Fin 5, List.ofFn (pt 5 (pairCode p)) = pairInput p.1 p.2 := by
  decide +kernel
theorem graphRow : ∀ i j : Fin 5, reference (pt 5 (pairCode (i,j))) =
    (266837 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by decide +kernel
def samplePairs : List (Fin 5 × Fin 5) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def M_ : ℕ := 32767

def Y_ : ℕ := 4917

def XS_ : List ℕ := [31, 482, 3652, 13448, 26896]

def PD_ : List (ℕ × ℕ) := [(1, 6831), (2, 6136), (3, 339), (4, 518), (5, 940), (6, 377), (7, 19), (8, 38), (9, 60), (10, 17), (11, 7), (12, 4), (13, 1), (14, 1)]

def PM_ : List (ℕ × ℕ) := [(1, 4917), (3, 4917), (6, 4917), (7, 4917), (10, 4917), (11, 4917), (13, 4917), (14, 4917)]

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

def b0 : List Row := [([3,482,28255,31880],[]),([3,511,1226,26896],[]),([3,1226,1535,26896],[]),([3,3679,27106,31880],[]),([3,13448,27106,28255],[]),([4,31,482,1226,26896],[]),([4,31,482,28228,31880],[]),([4,31,1226,1514,26896],[(1024,273410)]),([4,31,3652,27106,31880],[]),([4,31,13448,27106,28228],[]),([4,66,511,1160,26896],[]),([4,128,511,1098,26896],[]),([4,136,511,1098,26896],[]),([4,159,482,1226,26896],[])]
def b1 : List Row := [([4,226,3679,6143,13448],[]),([4,272,482,28511,32152],[(1024,132100)]),([4,272,3679,27122,32152],[]),([4,272,13448,27122,28511],[]),([4,415,28500,32250],[(1024,132263),(1024,164999),(1024,170114)]),([4,480,3679,13448,27106],[]),([4,482,1615,6143,13448],[]),([4,482,1631,5256],[(1024,1196),(1024,3468),(1024,164876),(1024,404484)]),([4,482,1631,6143,13448],[(1024,404484)]),([4,482,1631,27511],[(1024,1196),(1024,3468),(1024,164876),(1024,404484)]),([4,482,3652,26655,31880],[]),([4,482,3663,6143,13448],[]),([4,482,3679,5256,6143],[(1024,404484)])]
def t0 : BT := .nd (blockTree b0) [4,194,511,1032,26896] (blockTree b1)
def b2 : List Row := [([4,482,3679,6143,13448],[]),([4,482,3679,6143,19319],[]),([4,482,3679,7304],[(1024,1198),(1024,3470),(1024,164878),(1024,406532)]),([4,482,3679,13448,26624],[]),([4,482,3679,13448,27106],[]),([4,482,3679,19319,26624],[]),([4,482,3679,19319,27106],[]),([4,482,3679,26624,31880],[]),([4,482,3679,26896,31880],[]),([4,482,5256,31136],[(1024,1196),(1024,164876),(1024,404484)]),([4,482,6143,13448,29088],[]),([4,482,9823,13448],[(1024,1196),(1024,3468),(1024,164876),(1024,404484)]),([4,482,11871,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)])]
def b3 : List Row := [([4,482,13448,26624,29088],[]),([4,482,13448,27106,29088],[]),([4,482,28511,32136],[(1024,1284),(1024,263172),(1024,269474)]),([4,498,28511,32152],[(1024,1156),(1024,132100),(1024,138402)]),([4,511,1098,13448,27122],[]),([4,511,1098,13448,27135],[]),([4,511,1514,16095,26896],[]),([4,511,1615,13448,27122],[]),([4,511,3652,13514,27135],[]),([4,511,3662,13448,27122],[]),([4,511,3663,13448,27122],[]),([4,511,3679,13448,27106],[]),([4,511,3679,13514,27122],[])]
def t1 : BT := .nd (blockTree b2) [4,482,13448,26624,28255] (blockTree b3)
def t2 : BT := .nd t0 [4,482,3679,5661,13448] t1
def b4 : List Row := [([4,511,3807,13802,26896],[]),([4,511,4095,13514,26896],[]),([4,511,13448,27122,31152],[]),([4,1098,13448,13823,27122],[]),([4,1226,3652,4095,26896],[]),([4,1514,1535,16095,26896],[(1024,273410)]),([4,1535,13535,13802,26896],[(1024,142722),(1024,175106)]),([4,1631,5256,32285],[(1024,1196),(1024,404484)]),([4,1631,8674,13448],[(1024,1196),(1024,3468),(1024,164876),(1024,404484)]),([4,2530,3679,5256],[(1024,1198),(1024,3470),(1024,164878),(1024,406532)]),([4,2530,3679,27511],[(1024,1198),(1024,3470),(1024,164878),(1024,406532)]),([4,2530,11871,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([4,3652,10734,13471],[(1024,1099),(1024,10306),(1024,14498),(1024,164879)])]
def b5 : List Row := [([4,3652,13448,26655,27106],[]),([4,3662,13448,13823,27122],[]),([4,3679,4070,13448,27106],[]),([4,3679,4095,13448,27106],[]),([4,3679,5661,13448,32285],[]),([4,3679,6143,13448,32285],[]),([4,3679,8674,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([4,3679,10432,13802],[(1024,1199),(1024,164879),(1024,178178)]),([4,3679,10722,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([4,3679,10722,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([4,3679,10722,19319],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([4,3679,13448,13802,27106],[]),([4,3679,13448,22045],[(1024,1199),(1024,164879),(1024,407556)])]
def t3 : BT := .nd (blockTree b4) [4,3652,13448,13792,27106] (blockTree b5)
def b6 : List Row := [([4,3679,13448,26624,32285],[]),([4,3679,13448,27106,32256],[]),([4,3679,13448,27106,32285],[]),([4,10722,11871,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([4,10722,13448,29088],[(1024,164879),(1024,407556)]),([5,10,511,3652,13448,27122],[(1024,145796)]),([5,10,3652,13448,13823,27122],[]),([5,15,482,3652,6143,13448],[]),([5,15,511,3652,13448,27122],[]),([5,16,482,3679,5645,13448],[(1024,142340)]),([5,16,482,3679,6127,13448],[(1024,11394),(1024,142340)]),([5,16,482,3679,13448,26640],[(1024,132108),(1024,134156)]),([5,16,482,3679,13448,27122],[(1024,134156)])]
def b7 : List Row := [([5,16,482,3679,19319,27122],[]),([5,16,482,13448,27122,29088],[(1024,165006)]),([5,16,482,28511,32152],[(1024,1284),(1024,263172),(1024,269474)]),([5,16,498,3679,13448,27122],[(1024,132100)]),([5,16,511,3679,13448,27122],[(1024,134146)]),([5,16,3679,4070,13448,27122],[(1024,134210),(1024,178306)]),([5,16,3679,4095,13448,27122],[(1024,134146)]),([5,16,3679,13448,13802,27122],[(1024,142504)]),([5,16,3679,13448,26640,32285],[(1024,134156)]),([5,16,3679,13448,27122,32285],[(1024,134156)]),([5,20,482,3679,13448,27122],[]),([5,20,482,28511,32152],[(1024,1284),(1024,263172),(1024,269474)]),([5,24,482,3679,13448,27122],[(1024,134156)])]
def t4 : BT := .nd (blockTree b6) [5,16,482,3679,13464,27122] (blockTree b7)
def t5 : BT := .nd t3 [4,3679,13448,26624,27106] t4
def t6 : BT := .nd t2 [4,511,3679,13514,27135] t5
def b8 : List Row := [([5,27,482,28500,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292)]),([5,29,482,3652,13448,26655],[]),([5,29,482,3679,13448,26640],[]),([5,29,482,3679,13448,27122],[]),([5,29,3652,13448,26655,32285],[]),([5,29,3679,13448,26640,32285],[]),([5,29,3679,13448,27122,32285],[]),([5,31,66,482,1160,26896],[(1024,273410)]),([5,31,128,482,1098,26896],[(1024,273416)]),([5,31,194,482,1032,26896],[(1024,273410)]),([5,31,226,3652,6143,13448],[]),([5,31,226,3679,6127,13448],[]),([5,31,272,482,28500,32152],[(1024,134311),(1024,268292)])]
def b9 : List Row := [([5,31,272,13448,27122,28500],[(1024,132263)]),([5,31,384,28500,32250],[(1024,132263),(1024,164999),(1024,170114),(1024,171271)]),([5,31,480,3652,13448,27106],[]),([5,31,482,615,4267],[(1024,1291),(1024,134311),(1024,165003),(1024,170116),(1024,268292)]),([5,31,482,615,28500],[(1024,1291),(1024,134311),(1024,165003),(1024,170116),(1024,268292)]),([5,31,482,1098,13448,27122],[(1024,142498)]),([5,31,482,1514,16095,26896],[(1024,178180),(1024,276482)]),([5,31,482,1604,5256],[(1024,1196),(1024,3468),(1024,164876),(1024,170284),(1024,404484)]),([5,31,482,1604,6143,13448],[(1024,404484)]),([5,31,482,1604,27511],[(1024,1196),(1024,3468),(1024,164876),(1024,170284),(1024,404484)]),([5,31,482,1615,5256],[(1024,1196),(1024,3468),(1024,170284),(1024,306343),(1024,404484)]),([5,31,482,1615,6127,13448],[(1024,142498),(1024,404484)]),([5,31,482,1615,13448,27122],[(1024,142498)])]
def t7 : BT := .nd (blockTree b8) [5,31,272,3652,27122,32152] (blockTree b9)
def b10 : List Row := [([5,31,482,1631,6127,13448],[(1024,142498),(1024,404484)]),([5,31,482,2935,3652,26896],[]),([5,31,482,2935,3679,26896],[]),([5,31,482,3648,13448,27106],[]),([5,31,482,3652,5256,6143],[(1024,404484)]),([5,31,482,3652,5661,13448],[]),([5,31,482,3652,6112,13448],[]),([5,31,482,3652,6143,13448],[]),([5,31,482,3652,6143,19319],[]),([5,31,482,3652,7304],[(1024,1198),(1024,3470),(1024,164878),(1024,170286),(1024,406532)]),([5,31,482,3652,13448,26624],[]),([5,31,482,3652,13448,26655],[]),([5,31,482,3652,13448,27106],[])]
def b11 : List Row := [([5,31,482,3652,19319,26624],[]),([5,31,482,3652,19319,26655],[]),([5,31,482,3652,19319,27106],[]),([5,31,482,3652,26624,31880],[]),([5,31,482,3652,26896,29832],[]),([5,31,482,3652,26896,31880],[]),([5,31,482,3662,13448,27122],[]),([5,31,482,3663,6127,13448],[]),([5,31,482,3663,13448,27122],[]),([5,31,482,3668,13464,27122],[(1024,134156)]),([5,31,482,3679,5256,6127],[(1024,404484)]),([5,31,482,3679,6114,13448],[(1024,306178)]),([5,31,482,3679,6127,13448],[])]
def t8 : BT := .nd (blockTree b10) [5,31,482,3652,13450,27135] (blockTree b11)
def t9 : BT := .nd t7 [5,31,482,1631,5256] t8
def b12 : List Row := [([5,31,482,3679,6143,13448],[]),([5,31,482,3679,13448,26624],[]),([5,31,482,3679,13448,26640],[]),([5,31,482,3679,13448,26653],[(1024,1324)]),([5,31,482,3679,13448,26655],[]),([5,31,482,3679,13448,27106],[]),([5,31,482,3679,13450,27122],[]),([5,31,482,3679,13514,27122],[]),([5,31,482,3679,19319,26640],[]),([5,31,482,3679,26896,29832],[]),([5,31,482,3807,13802,26896],[]),([5,31,482,3908,13704,26911],[]),([5,31,482,3924,13720,26896],[(1024,134156)])]
def b13 : List Row := [([5,31,482,4095,13514,26896],[]),([5,31,482,4267,32152],[(1024,1291),(1024,165003),(1024,170116),(1024,268292)]),([5,31,482,5256,31163],[(1024,1196),(1024,164876),(1024,170060),(1024,170284),(1024,404484)]),([5,31,482,6127,13448,29088],[]),([5,31,482,6143,13448,29115],[]),([5,31,482,9796,13448],[(1024,1196),(1024,3468),(1024,164876),(1024,170284),(1024,404484)]),([5,31,482,11844,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([5,31,482,12704,13448,26896],[]),([5,31,482,12731,13448,26896],[]),([5,31,482,12735,13448,26896],[]),([5,31,482,13448,20036,26896],[]),([5,31,482,13448,20063,26896],[]),([5,31,482,13448,26624,28228],[])]
def t10 : BT := .nd (blockTree b12) [5,31,482,3935,13704,26896] (blockTree b13)
def b14 : List Row := [([5,31,482,13448,26640,28255],[]),([5,31,482,13448,26640,29088],[]),([5,31,482,13448,26655,28244],[]),([5,31,482,13448,26655,28255],[]),([5,31,482,13448,26655,29115],[]),([5,31,482,13448,26896,28228],[]),([5,31,482,13448,26896,28255],[]),([5,31,482,13448,27106,29115],[]),([5,31,482,13448,27122,31152],[]),([5,31,482,13512,27920],[(1024,1292),(1024,134539),(1024,165004),(1024,175234),(1024,273410)]),([5,31,482,13512,27984],[(1024,1292),(1024,165004),(1024,175234),(1024,273410)]),([5,31,482,16076,27924],[(1024,1295),(1024,68907),(1024,164939),(1024,305220),(1024,309252)]),([5,31,482,16076,27928],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,309415)])]
def b15 : List Row := [([5,31,482,27984,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292)]),([5,31,482,28244,31896],[(1024,134311),(1024,165003),(1024,170116)]),([5,31,482,28484,32136],[(1024,1291),(1024,268292),(1024,269479)]),([5,31,482,28496,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292)]),([5,31,482,28500,32136],[(1024,1291),(1024,268292),(1024,269479)]),([5,31,482,28500,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292)]),([5,31,482,28500,32154],[(1024,134311),(1024,268290),(1024,268292),(1024,268363),(1024,301323),(1024,396427)]),([5,31,482,28500,32156],[(1024,1291),(1024,68775),(1024,164939),(1024,268292)]),([5,31,482,28502,32152],[(1024,66827),(1024,134311),(1024,263172),(1024,263243),(1024,268292),(1024,396427)]),([5,31,482,28502,32154],[(1024,132363),(1024,134311),(1024,263307),(1024,268292),(1024,268363)]),([5,31,486,28500,32152],[(1024,1291),(1024,66727),(1024,164935),(1024,268292)]),([5,31,490,28500,32152],[(1024,1291),(1024,165003),(1024,268456),(1024,269479)]),([5,31,498,28500,32152],[(1024,1291),(1024,132100),(1024,137220),(1024,268292),(1024,269479)])]
def t11 : BT := .nd (blockTree b14) [5,31,482,27511,31163] (blockTree b15)
def t12 : BT := .nd t10 [5,31,482,13448,26624,29115] t11
def t13 : BT := .nd t9 [5,31,482,3679,6127,19319] t12
def t14 : BT := .nd t6 [5,26,482,28500,32152] t13
def b16 : List Row := [([5,31,506,28500,32152],[(1024,1291),(1024,134311),(1024,137291),(1024,268363),(1024,268456)]),([5,31,511,3652,13448,27106],[]),([5,31,511,3652,13450,27122],[(1024,145796)]),([5,31,511,3652,13450,27135],[]),([5,31,511,3654,13448,27122],[(1024,145796)]),([5,31,511,3780,13802,26896],[]),([5,31,511,3788,13802,26896],[]),([5,31,615,28500,32285],[(1024,1291),(1024,134311),(1024,165003)]),([5,31,1098,13448,13802,27122],[(1024,175234),(1024,175240)]),([5,31,1506,13512,26896],[(1024,1292),(1024,134540),(1024,165004),(1024,175234),(1024,273410)]),([5,31,1510,16076,26896],[(1024,1092),(1024,3138),(1024,66564),(1024,164935)]),([5,31,1514,16076,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482),(1024,309415)]),([5,31,1514,16095,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,276482),(1024,309415)])]
def b17 : List Row := [([5,31,1604,8674,13448],[(1024,1196),(1024,3468),(1024,164876),(1024,170284),(1024,404484)]),([5,31,2530,3652,5256],[(1024,1198),(1024,3470),(1024,164878),(1024,170286),(1024,406532)]),([5,31,2530,3652,27511],[(1024,1198),(1024,3470),(1024,164878),(1024,170286),(1024,406532)]),([5,31,2530,11844,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([5,31,3652,4070,13448,27106],[]),([5,31,3652,5661,13448,32285],[]),([5,31,3652,6112,13448,32285],[]),([5,31,3652,6143,13448,32285],[]),([5,31,3652,8674,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([5,31,3652,10432,13802],[(1024,1199),(1024,164879),(1024,174383),(1024,178178)]),([5,31,3652,10722,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([5,31,3652,10722,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([5,31,3652,10722,19319],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)])]
def t15 : BT := .nd (blockTree b16) [5,31,1604,5256,32285] (blockTree b17)
def b18 : List Row := [([5,31,3652,13448,13802,27106],[]),([5,31,3652,13448,22045],[(1024,1199),(1024,164879),(1024,170287),(1024,407556)]),([5,31,3652,13448,26624,27106],[]),([5,31,3652,13448,26624,32285],[]),([5,31,3652,13448,26655,32285],[]),([5,31,3652,13448,26655,32541],[]),([5,31,3652,13448,27106,32256],[]),([5,31,3652,13448,27106,32285],[]),([5,31,3652,13464,13802,27122],[(1024,142504)]),([5,31,3652,19319,26655,32285],[]),([5,31,3652,27122,31896],[(1024,132100),(1024,134146),(1024,165000)]),([5,31,3662,13448,13802,27122],[(1024,178244)]),([5,31,3668,4070,13448,27122],[(1024,178306)])]
def b19 : List Row := [([5,31,3679,10722,13448],[(1024,1199),(1024,3471),(1024,170287),(1024,178178),(1024,407556),(1024,407563)]),([5,31,3679,13448,26640,32285],[]),([5,31,3679,13448,26640,32541],[]),([5,31,3679,13448,26653,32285],[]),([5,31,3679,13448,26655,32285],[]),([5,31,3679,19319,26640,32285],[]),([5,31,4036,13802,26896],[(1024,165007),(1024,170254),(1024,268364),(1024,268462),(1024,273410)]),([5,31,4070,13802,16095,26896],[]),([5,31,4070,15560,27122],[(1024,132271),(1024,165007),(1024,178306)]),([5,31,4095,13802,16076,26896],[(1024,276482)]),([5,31,4095,13802,16095,26896],[(1024,276482)]),([5,31,4267,32152,32285],[(1024,1291),(1024,165003),(1024,268292)]),([5,31,8674,13448,31163],[(1024,164876),(1024,170060),(1024,170284),(1024,404484)])]
def t16 : BT := .nd (blockTree b18) [5,31,3679,6127,13448,32285] (blockTree b19)
def t17 : BT := .nd t15 [5,31,3652,10734,13448] t16
def b20 : List Row := [([5,31,10722,13448,29115],[(1024,164879),(1024,170063),(1024,170287),(1024,407556)]),([5,31,11972,13802,26896],[(1024,1295),(1024,165007),(1024,178178),(1024,178306),(1024,273410),(1024,276482)]),([5,31,11972,13802,27122],[(1024,3247),(1024,165007),(1024,175108),(1024,178178),(1024,178180),(1024,178306)]),([5,31,12714,13448,27122],[(1024,132263),(1024,164999),(1024,169986),(1024,169988),(1024,170114)]),([5,31,13448,20053,27122],[(1024,1191),(1024,3239),(1024,132263),(1024,164999),(1024,170114)]),([5,31,13448,26640,28255,32285],[]),([5,31,13448,26640,29088,32285],[]),([5,31,13448,26655,28244,32285],[]),([5,31,13448,26655,28255,32285],[]),([5,31,13448,26655,29115,32285],[]),([5,31,13448,26896,28255,32285],[]),([5,31,13448,27122,28244],[(1024,132263),(1024,164999),(1024,170114)]),([5,31,28244,31896,32285],[(1024,134311),(1024,165003),(1024,170116)])]
def b21 : List Row := [([5,66,511,3652,13448,27135],[]),([5,66,511,3679,13448,27122],[]),([5,66,511,3679,13448,27135],[]),([5,66,511,4095,13448,26896],[]),([5,66,1160,3652,4095,26896],[]),([5,95,482,13448,27920],[(1024,1292),(1024,134539),(1024,165004),(1024,175234),(1024,273410)]),([5,95,482,28500,32152],[(1024,1291),(1024,134539),(1024,165003),(1024,403588)]),([5,95,1506,13448,26896],[(1024,1292),(1024,134540),(1024,165004),(1024,175234),(1024,273410)]),([5,128,511,3679,13802,26896],[]),([5,136,511,3679,13802,26896],[]),([5,159,482,3807,13802,26896],[]),([5,159,482,28500,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292)]),([5,159,511,3652,13802,26896],[])]
def t18 : BT := .nd (blockTree b20) [5,31,28500,32152,32285] (blockTree b21)
def b22 : List Row := [([5,226,482,3679,5887,13448],[(1024,276482)]),([5,226,511,3652,13448,26911],[]),([5,226,511,3679,5871,13448],[]),([5,226,511,3679,13448,26896],[]),([5,256,482,3679,5887,13448],[(1024,11522),(1024,11528),(1024,276482)]),([5,256,482,3679,13448,26880],[(1024,263180),(1024,269324),(1024,276482)]),([5,272,482,3652,26911,32152],[(1024,132100)]),([5,272,482,3679,5871,13448],[(1024,11394),(1024,142340)]),([5,272,482,3679,13448,26896],[(1024,132108),(1024,134156)]),([5,272,482,3679,13448,27122],[]),([5,272,482,3679,13720,26896],[(1024,134156),(1024,269324)]),([5,272,482,3679,19319,26896],[(1024,132108)]),([5,272,482,3679,26896,32152],[(1024,269710)])]
def b23 : List Row := [([5,272,482,13448,26896,28511],[(1024,132108)]),([5,272,482,13448,26896,29088],[(1024,132108),(1024,165006)]),([5,272,498,3679,13448,26896],[(1024,132108),(1024,269324)]),([5,272,511,3679,13448,27122],[]),([5,272,3652,13448,26911,27122],[]),([5,272,3679,13448,26896,27122],[]),([5,272,3679,13448,26896,32285],[(1024,1294)]),([5,287,482,3679,5871,13448],[]),([5,287,482,3679,13448,26896],[]),([5,287,482,3679,13448,26911],[]),([5,287,482,3679,13704,26896],[]),([5,287,482,3679,19319,26896],[]),([5,287,482,3935,13704,26896],[])]
def t19 : BT := .nd (blockTree b22) [5,272,482,3935,13448,26896] (blockTree b23)
def t20 : BT := .nd t18 [5,194,511,3679,13448,26896] t19
def t21 : BT := .nd t17 [5,31,10722,11844,13448] t20
def b24 : List Row := [([5,287,482,28500,32152],[(1024,134311),(1024,165003),(1024,170116)]),([5,287,3652,27122,32152],[(1024,132100),(1024,134146),(1024,165000)]),([5,287,3679,13448,26896,32285],[]),([5,287,13448,27122,28500],[(1024,132263),(1024,164999),(1024,170114)]),([5,340,482,3679,13448,26896],[]),([5,351,482,3679,13448,26896],[]),([5,351,482,28500,32152],[(1024,134539),(1024,165003),(1024,263172),(1024,268292)]),([5,375,482,3679,13448,26896],[]),([5,375,482,3679,19319,26896],[]),([5,383,482,3679,13448,26896],[]),([5,383,482,3679,19319,26896],[]),([5,408,482,3679,13448,26896],[(1024,132108),(1024,134156),(1024,269324)]),([5,415,482,3679,13448,26896],[(1024,269486)])]
def b25 : List Row := [([5,415,3652,13802,26896],[(1024,132270),(1024,142498),(1024,165007),(1024,177410),(1024,263244),(1024,263342)]),([5,415,3652,26896,32250],[(1024,132270),(1024,142498),(1024,165006),(1024,177282)]),([5,443,482,3679,13448,26896],[]),([5,447,482,3679,13448,26896],[]),([5,447,482,13448,26896,29088],[]),([5,480,482,3679,13448,26880],[(1024,178178),(1024,276482)]),([5,480,3652,13448,27106,32736],[]),([5,482,482,3679,5887,13448],[(1024,276482)]),([5,482,482,3679,13448,26880],[(1024,276482)]),([5,482,498,3679,5871,13448],[(1024,11394)]),([5,482,498,3679,13448,26896],[(1024,132108)]),([5,482,498,3679,13448,27122],[]),([5,482,498,3679,13464,26896],[(1024,132100),(1024,134156),(1024,276482)])]
def t22 : BT := .nd (blockTree b24) [5,415,482,28500,32152] (blockTree b25)
def b26 : List Row := [([5,482,498,13448,26896,29088],[(1024,132108)]),([5,482,502,3679,13448,26896],[]),([5,482,503,3679,13448,26896],[]),([5,482,503,3679,19319,26896],[]),([5,482,506,3679,13448,26896],[(1024,132108)]),([5,482,507,3679,13448,26896],[]),([5,482,511,1032,16095,26896],[(1024,273410)]),([5,482,511,1098,13448,26896],[(1024,142728)]),([5,482,511,1119,13448,26896],[(1024,11426),(1024,142498)]),([5,482,511,1160,3679,26896],[(1024,273410)]),([5,482,511,1615,5871,13448],[(1024,404484)]),([5,482,511,1615,13448,26896],[]),([5,482,511,1631,5871,13448],[(1024,142498),(1024,404484)])]
def b27 : List Row := [([5,482,511,3652,13448,26655],[]),([5,482,511,3652,13450,26911],[(1024,71980)]),([5,482,511,3652,13450,27135],[]),([5,482,511,3654,13448,26911],[]),([5,482,511,3654,13448,27135],[]),([5,482,511,3662,13448,26896],[]),([5,482,511,3663,5871,13448],[]),([5,482,511,3663,13448,26896],[]),([5,482,511,3679,5256,5871],[(1024,404484)]),([5,482,511,3679,5256,26896],[]),([5,482,511,3679,5632,13448],[(1024,306178)]),([5,482,511,3679,5645,13448],[]),([5,482,511,3679,5856,13448],[(1024,306178)])]
def t23 : BT := .nd (blockTree b26) [5,482,511,1631,13448,26896] (blockTree b27)
def t24 : BT := .nd t22 [5,482,498,3679,19319,26896] t23
def b28 : List Row := [([5,482,511,3679,5871,19319],[]),([5,482,511,3679,5887,13448],[(1024,276482)]),([5,482,511,3679,6127,13448],[]),([5,482,511,3679,6143,13448],[]),([5,482,511,3679,13448,26624],[]),([5,482,511,3679,13448,26640],[]),([5,482,511,3679,13448,26880],[(1024,276482)]),([5,482,511,3679,13448,26896],[]),([5,482,511,3679,13448,26898],[]),([5,482,511,3679,13448,26900],[]),([5,482,511,3679,13448,26904],[]),([5,482,511,3679,13448,26911],[]),([5,482,511,3679,13448,26960],[])]
def b29 : List Row := [([5,482,511,3679,13448,26964],[]),([5,482,511,3679,13448,26975],[]),([5,482,511,3679,13448,27024],[]),([5,482,511,3679,13448,27032],[]),([5,482,511,3679,13448,27122],[]),([5,482,511,3679,13448,27135],[]),([5,482,511,3679,13448,27920],[(1024,142724),(1024,273410)]),([5,482,511,3679,13448,27928],[(1024,142728),(1024,273410)]),([5,482,511,3679,13450,26896],[]),([5,482,511,3679,13512,26896],[]),([5,482,511,3679,13514,26896],[(1024,142728)]),([5,482,511,3679,15496,26896],[(1024,14498),(1024,145570)]),([5,482,511,3679,19319,26896],[])]
def t25 : BT := .nd (blockTree b28) [5,482,511,3679,13448,26962] (blockTree b29)
def b30 : List Row := [([5,482,511,3679,19319,27122],[]),([5,482,511,3679,19319,27135],[]),([5,482,511,3679,26896,27511],[]),([5,482,511,3807,13448,26896],[]),([5,482,511,5871,13448,29088],[]),([5,482,511,11871,13448,26896],[]),([5,482,511,13448,26896,29088],[]),([5,482,511,13448,26896,31152],[]),([5,482,511,13448,26911,29088],[]),([5,482,511,13448,27122,29088],[]),([5,482,511,13448,27135,29088],[]),([5,482,511,19319,26896,29088],[]),([5,482,511,26896,28511,32152],[(1024,132100)])]
def b31 : List Row := [([5,482,1055,13512,26896],[(1024,1292),(1024,11522),(1024,134540),(1024,142498),(1024,165004)]),([5,482,1098,13448,13823,26896],[]),([5,482,1119,1535,13448,26896],[(1024,11426),(1024,142498),(1024,142724)]),([5,482,1119,5871,13448],[(1024,1292),(1024,142498),(1024,165004),(1024,273410)]),([5,482,1119,13448,13823,26896],[(1024,142498)]),([5,482,1119,13448,26896],[(1024,1292),(1024,11522),(1024,134540),(1024,142498),(1024,165004)]),([5,482,1119,13448,26911],[(1024,1292),(1024,11426),(1024,11431),(1024,11522),(1024,169996)]),([5,482,1119,13448,27122],[(1024,11426),(1024,132268),(1024,142498),(1024,165004),(1024,175234)]),([5,482,1119,13448,27984],[(1024,1292),(1024,11522),(1024,142498),(1024,165004)]),([5,482,1119,13448,27999],[(1024,1292),(1024,11426),(1024,11522),(1024,263180)]),([5,482,1119,13471,13802,26896],[(1024,142503),(1024,175108)]),([5,482,1119,13512,26896],[(1024,1292),(1024,11522),(1024,134540),(1024,142498),(1024,165004)]),([5,482,1119,13535,13802,26896],[(1024,11432),(1024,142724),(1024,175108)])]
def t26 : BT := .nd (blockTree b30) [5,482,615,28500,32736] (blockTree b31)
def t27 : BT := .nd t25 [5,482,511,3679,19319,26911] t26
def t28 : BT := .nd t24 [5,482,511,3679,5871,13448] t27
def t29 : BT := .nd t21 [5,287,482,13448,26896,29088] t28
def t30 : BT := .nd t14 [5,31,502,28500,32152] t29
def b32 : List Row := [([5,482,1119,26896,32152],[(1024,1292),(1024,134540),(1024,165004),(1024,404612)]),([5,482,1535,3679,13448,26896],[(1024,142498),(1024,142724)]),([5,482,1604,1631,5256],[(1024,1196),(1024,3468),(1024,11426),(1024,164876),(1024,404484)]),([5,482,1604,5256,32736],[(1024,164876),(1024,404484)]),([5,482,1604,8223,13448],[(1024,1196),(1024,3468),(1024,164876),(1024,170284),(1024,404484)]),([5,482,1615,5887,13448],[(1024,1292),(1024,273410)]),([5,482,1631,2047,5871,13448],[(1024,142498),(1024,142724),(1024,404484)]),([5,482,1631,2047,13448,26896],[(1024,11426),(1024,142498),(1024,142724)]),([5,482,1631,3652,5256],[(1024,1198),(1024,3470),(1024,164878),(1024,404484),(1024,404548),(1024,406532)]),([5,482,1631,5256],[(1024,11426),(1024,175106),(1024,404484),(1024,404648)]),([5,482,1631,5256,5871],[(1024,1292),(1024,11426),(1024,142498),(1024,165004),(1024,273410),(1024,404484)]),([5,482,1631,5256,13448],[(1024,1196),(1024,11426),(1024,164876),(1024,175106),(1024,404484),(1024,404648),(1024,406532),(1024,406696)]),([5,482,1631,5256,26896],[(1024,1292),(1024,11522),(1024,134540),(1024,142498),(1024,165004),(1024,404484),(1024,404612)])]
def b33 : List Row := [([5,482,1631,5871,13448],[(1024,1292),(1024,11426),(1024,142498),(1024,165004),(1024,273410)]),([5,482,1631,5871,19319],[(1024,1292),(1024,3468),(1024,142498),(1024,165004),(1024,273410),(1024,404612)]),([5,482,1631,5871,32152],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,404612)]),([5,482,1631,5887,13448],[(1024,1292),(1024,11426),(1024,273410)]),([5,482,1631,6127,13448],[(1024,11426),(1024,142498),(1024,165004)]),([5,482,1631,7919,13448],[(1024,1196),(1024,3468),(1024,11426),(1024,164876),(1024,404484)]),([5,482,1631,8192,13448],[(1024,1196),(1024,3468),(1024,164876),(1024,404484)]),([5,482,1631,13448,26896],[(1024,1292),(1024,11522),(1024,134540),(1024,142498),(1024,165004),(1024,404484)]),([5,482,1631,13448,26911],[(1024,1292),(1024,11426),(1024,11431),(1024,11522),(1024,169996),(1024,404491)]),([5,482,1631,13448,27122],[(1024,11426),(1024,132268),(1024,142498),(1024,165004),(1024,175234),(1024,404484)]),([5,482,1631,13448,28500],[(1024,1292),(1024,11522),(1024,76962),(1024,164940),(1024,404484)]),([5,482,1631,13448,28511],[(1024,1292),(1024,11426),(1024,11522),(1024,263180),(1024,404648)]),([5,482,1631,19319,26896],[(1024,1292),(1024,11426),(1024,11522),(1024,142498),(1024,165004)])]
def t31 : BT := .nd (blockTree b32) [5,482,1631,5856,13448] (blockTree b33)
def b34 : List Row := [([5,482,2048,3679,5256],[(1024,1198),(1024,3470),(1024,13474),(1024,164878),(1024,406532)]),([5,482,2048,3679,27511],[(1024,1198),(1024,3470),(1024,164878),(1024,406532)]),([5,482,2048,11871,13448],[(1024,1199),(1024,3471),(1024,14498),(1024,164879),(1024,407556)]),([5,482,2304,3679,13448,28511],[(1024,14594),(1024,269710)]),([5,482,2935,3652,3679,26896],[]),([5,482,3648,13448,27106,32736],[]),([5,482,3652,3679,6143,13448],[]),([5,482,3652,3679,13448,26624],[]),([5,482,3652,3679,13448,27106],[]),([5,482,3652,3679,26896,29832],[]),([5,482,3652,5661,13448,32736],[]),([5,482,3652,6112,13448,32736],[]),([5,482,3652,6143,13448,32736],[])]
def b35 : List Row := [([5,482,3652,10252,13471],[(1024,1199),(1024,3147),(1024,10308),(1024,14498),(1024,164879)]),([5,482,3652,10271,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([5,482,3652,13448,13471,26655],[]),([5,482,3652,13448,13792,26880],[]),([5,482,3652,13448,26624,26655],[]),([5,482,3652,13448,26624,32736],[]),([5,482,3652,13448,26655,32256],[]),([5,482,3652,13448,26655,32736],[]),([5,482,3652,13448,27106,32736],[]),([5,482,3652,13448,27106,32740],[]),([5,482,3652,13448,27106,32752],[]),([5,482,3652,13471,13704,26911],[]),([5,482,3652,19319,27106,32736],[])]
def t32 : BT := .nd (blockTree b34) [5,482,3652,8223,15496] (blockTree b35)
def t33 : BT := .nd t31 [5,482,1631,26896,32152] t32
def b36 : List Row := [([5,482,3662,13448,13823,26896],[]),([5,482,3663,5887,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([5,482,3679,4070,5887,13448],[(1024,276482)]),([5,482,3679,4070,13448,26880],[(1024,276482)]),([5,482,3679,4095,5887,13448],[(1024,275458),(1024,276482)]),([5,482,3679,4095,13448,26880],[(1024,275458),(1024,276482)]),([5,482,3679,4095,15496,26896],[(1024,14498),(1024,144546),(1024,145570),(1024,145796)]),([5,482,3679,5256,5887],[(1024,1294),(1024,273410),(1024,275458),(1024,406532)]),([5,482,3679,5663,13448],[(1024,1199),(1024,178178)]),([5,482,3679,5871,6143,13448],[(1024,142498)]),([5,482,3679,5871,13448,13823],[(1024,142498)]),([5,482,3679,5871,13448,32256],[]),([5,482,3679,5871,13464],[(1024,1295),(1024,3212),(1024,134156),(1024,142340),(1024,165006)])]
def b37 : List Row := [([5,482,3679,5887,6127,13448],[(1024,142498),(1024,273410),(1024,275458),(1024,276482)]),([5,482,3679,5887,6143,13448],[(1024,273410),(1024,275458),(1024,276482)]),([5,482,3679,5887,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([5,482,3679,5887,13448,13802],[(1024,273800),(1024,276482)]),([5,482,3679,5887,13448,32285],[]),([5,482,3679,5887,19319],[(1024,1295),(1024,273410),(1024,276482),(1024,406792)]),([5,482,3679,6127,6143,13448],[(1024,142498)]),([5,482,3679,6127,13448,13471],[]),([5,482,3679,6127,13448,32736],[]),([5,482,3679,6143,13448],[]),([5,482,3679,6143,13448,26896],[(1024,142498)]),([5,482,3679,7919,32152],[(1024,1294),(1024,134542),(1024,144546),(1024,165006),(1024,406660)]),([5,482,3679,8192,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)])]
def t34 : BT := .nd (blockTree b36) [5,482,3679,5871,15496] (blockTree b37)
def b38 : List Row := [([5,482,3679,8464,13448,26896],[(1024,132108),(1024,134156)]),([5,482,3679,8479,13448,26896],[]),([5,482,3679,8690,13448,26896],[(1024,132108)]),([5,482,3679,8703,13448,26896],[]),([5,482,3679,10240,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([5,482,3679,10240,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([5,482,3679,10240,19319],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([5,482,3679,10432,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,178178),(1024,407556)]),([5,482,3679,10496,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([5,482,3679,10722,13448],[(1024,3471),(1024,14498),(1024,164879),(1024,407556)]),([5,482,3679,13448,13464,27122],[(1024,134156),(1024,142504)]),([5,482,3679,13448,13471,26640],[]),([5,482,3679,13448,13720,26896],[(1024,134156)])]
def b39 : List Row := [([5,482,3679,13448,13802,26880],[(1024,273800),(1024,276482)]),([5,482,3679,13448,13818,26896],[(1024,142498)]),([5,482,3679,13448,13823,26896],[(1024,142498)]),([5,482,3679,13448,13823,26911],[(1024,11431)]),([5,482,3679,13448,13823,27122],[(1024,142498)]),([5,482,3679,13448,13823,27135],[(1024,11426)]),([5,482,3679,13448,18944,26896],[]),([5,482,3679,13448,22527],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([5,482,3679,13448,26624],[]),([5,482,3679,13448,26624,26896],[]),([5,482,3679,13448,26624,32256],[]),([5,482,3679,13448,26640,32736],[]),([5,482,3679,13448,26880],[(1024,1295),(1024,263180),(1024,269710),(1024,276482)])]
def t35 : BT := .nd (blockTree b38) [5,482,3679,13448,13727,26896] (blockTree b39)
def t36 : BT := .nd t34 [5,482,3679,8208,13448,27122] t35
def t37 : BT := .nd t33 [5,482,3652,26911,32136] t36
def b40 : List Row := [([5,482,3679,13448,26880,32285],[]),([5,482,3679,13448,26896,27106],[(1024,276482)]),([5,482,3679,13448,26896,32256],[]),([5,482,3679,13448,26896,32269],[]),([5,482,3679,13448,26896,32324],[]),([5,482,3679,13448,26896,32392],[]),([5,482,3679,13448,26896,32480],[]),([5,482,3679,13448,26896,32495],[]),([5,482,3679,13448,26911,32256],[]),([5,482,3679,13448,27104],[(1024,1199),(1024,178178)]),([5,482,3679,13448,27106],[]),([5,482,3679,13448,27106,32736],[(1024,178178)]),([5,482,3679,13448,27122,32256],[])]
def b41 : List Row := [([5,482,3679,13448,27122,32751],[]),([5,482,3679,13448,27135,32256],[]),([5,482,3679,13464,26896],[(1024,1295),(1024,134156),(1024,142340),(1024,165006)]),([5,482,3679,13464,27122],[(1024,134146),(1024,134156),(1024,142340),(1024,165006)]),([5,482,3679,13466,26896],[(1024,6415),(1024,134156),(1024,142340),(1024,170126)]),([5,482,3679,13466,27122],[(1024,132271),(1024,134156),(1024,142340),(1024,170126)]),([5,482,3679,13471,13704,26896],[]),([5,482,3679,13720,26896],[(1024,1294),(1024,134156),(1024,142340),(1024,165006)]),([5,482,3679,13823,19319,26896],[(1024,142498)]),([5,482,3679,15496,26896],[(1024,1295),(1024,14594),(1024,145570),(1024,165007),(1024,407556)]),([5,482,3679,15496,26911],[(1024,1295),(1024,14498),(1024,14503),(1024,14594),(1024,169999),(1024,407563)]),([5,482,3679,15496,27122],[(1024,14498),(1024,132271),(1024,145570),(1024,165007),(1024,178306),(1024,407556)]),([5,482,3679,15496,28500],[(1024,1295),(1024,14594),(1024,80034),(1024,164943),(1024,407556)])]
def t38 : BT := .nd (blockTree b40) [5,482,3679,13448,27122,32738] (blockTree b41)
def b42 : List Row := [([5,482,3679,15560,26896],[(1024,1295),(1024,14594),(1024,145570),(1024,165007),(1024,407556)]),([5,482,3679,15560,27122],[(1024,14498),(1024,132271),(1024,145570),(1024,165007),(1024,178306),(1024,407556)]),([5,482,3679,15752,26896],[(1024,1294),(1024,165007),(1024,269710),(1024,406792),(1024,407556)]),([5,482,3679,16076,27928],[(1024,1295),(1024,145570),(1024,165007),(1024,407720)]),([5,482,3679,17271,26896],[(1024,1295),(1024,14498),(1024,14594),(1024,145570),(1024,165007)]),([5,482,3679,19303,26896],[(1024,1295),(1024,3212),(1024,134156),(1024,165006)]),([5,482,3679,19319,26880],[(1024,1295),(1024,263180),(1024,275458),(1024,276482)]),([5,482,3679,19319,26896,32256],[]),([5,482,3679,24848,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([5,482,3679,26880,32136],[(1024,1294),(1024,269710),(1024,273410),(1024,406792)]),([5,482,3679,26896,30104],[(1024,1294),(1024,134156),(1024,142340)]),([5,482,3679,26896,32136],[(1024,1294),(1024,269710),(1024,273410),(1024,406792)]),([5,482,4267,32152,32736],[(1024,165003),(1024,268292)])]
def b43 : List Row := [([5,482,5871,13448,31136],[(1024,1292),(1024,142498),(1024,164876),(1024,165004),(1024,263180)]),([5,482,5887,13448,28511],[(1024,1292),(1024,11522),(1024,263180),(1024,273410)]),([5,482,5887,13448,29088],[(1024,1295),(1024,11522),(1024,275458),(1024,276482)]),([5,482,8223,13448,31163],[(1024,1196),(1024,170060),(1024,170284),(1024,404484)]),([5,482,8703,11871,13448,26896],[]),([5,482,9567,13448,26896],[(1024,132268),(1024,142498),(1024,263468)]),([5,482,10240,11871,13448],[(1024,1199),(1024,3471),(1024,14498),(1024,164879),(1024,407556)]),([5,482,10240,13448,29088],[(1024,1199),(1024,164879),(1024,407556)]),([5,482,13448,13823,26896,29088],[]),([5,482,13448,26880,28511],[(1024,1292),(1024,11522),(1024,263180),(1024,273410)]),([5,482,13448,26880,29088],[(1024,1295),(1024,269710),(1024,273410),(1024,276482)]),([5,482,13448,26896,29088,32256],[]),([5,482,13448,26896,31136],[(1024,1292),(1024,142498),(1024,164876),(1024,165004),(1024,273410)])]
def t39 : BT := .nd (blockTree b42) [5,482,4287,13448,26911] (blockTree b43)
def t40 : BT := .nd t38 [5,482,3679,15496,28511] t39
def b44 : List Row := [([5,482,13448,26911,28480],[(1024,1292),(1024,263180),(1024,268450)]),([5,482,13448,27106,29115,32736],[]),([5,482,13464,26896,29088],[(1024,1295),(1024,134156),(1024,165006)]),([5,482,15496,26896,29088],[(1024,1295),(1024,145570),(1024,164879),(1024,165007),(1024,276482)]),([5,482,28484,32136,32736],[(1024,1291),(1024,268292),(1024,269479)]),([5,482,28496,32152,32736],[(1024,165003),(1024,268292)]),([5,482,28500,32136,32736],[(1024,1291),(1024,268292),(1024,269479)]),([5,482,28500,32152,32736],[(1024,165003),(1024,268292)]),([5,482,28500,32152,32740],[(1024,165003),(1024,268292)]),([5,490,511,3652,13471,26896],[]),([5,490,511,3679,13448,26896],[]),([5,498,3652,26911,32152],[(1024,1156),(1024,132100),(1024,138402)]),([5,498,3679,4070,13448,26896],[(1024,178306)])]
def b45 : List Row := [([5,498,3679,13448,26896],[(1024,1164),(1024,11394),(1024,132108),(1024,269710)]),([5,498,3679,13448,26896,27122],[(1024,132108)]),([5,498,3679,13448,26896,32285],[(1024,132108)]),([5,498,3679,13464,26896],[(1024,1295),(1024,132100),(1024,263180),(1024,269710),(1024,276482)]),([5,498,3679,19319,26896],[(1024,1164),(1024,11394),(1024,132108)]),([5,498,3679,26896,32152],[(1024,1164),(1024,132100),(1024,142338),(1024,269710),(1024,406792)]),([5,498,13448,26896,28511],[(1024,1164),(1024,11394),(1024,132108),(1024,142338)]),([5,498,13448,26896,29088],[(1024,1164),(1024,11394),(1024,132108),(1024,142338),(1024,269710)]),([5,502,13448,26911,28500],[(1024,1100),(1024,66572),(1024,71842)]),([5,506,3679,13448,26896],[(1024,1164),(1024,11394),(1024,132108),(1024,134542)]),([5,506,3679,26896,32152],[(1024,1164),(1024,134542),(1024,142338),(1024,406660)]),([5,511,1088,13471,13802,26896],[(1024,142722),(1024,175106)]),([5,511,1098,13448,26896],[(1024,138636),(1024,142728),(1024,400524)])]
def t41 : BT := .nd (blockTree b44) [5,498,3679,5871,13448] (blockTree b45)
def b46 : List Row := [([5,511,1506,3679,13448,26896],[(1024,142724),(1024,273410)]),([5,511,1514,3679,13448,26896],[(1024,142728),(1024,273410)]),([5,511,2064,3679,13448,27122],[(1024,134146)]),([5,511,2530,3679,13448,26896],[(1024,14498)]),([5,511,3652,5871,13471,13802],[]),([5,511,3652,13448,26655,32285],[]),([5,511,3652,13448,26911,32541],[]),([5,511,3652,13448,27106,32736],[]),([5,511,3652,13448,27122,32752],[]),([5,511,3652,13450,26911],[(1024,6444),(1024,71980),(1024,301071),(1024,306247)]),([5,511,3652,13450,27122],[(1024,145796),(1024,396431)]),([5,511,3652,13454,26896],[(1024,1095),(1024,6210),(1024,66567),(1024,71682),(1024,301131)]),([5,511,3652,13471,13802,26896],[(1024,178178)])]
def b47 : List Row := [([5,511,3652,13471,13802,27122],[(1024,145796),(1024,178178)]),([5,511,3652,13471,13802,27135],[(1024,178178)]),([5,511,3652,13471,18965,26896],[(1024,1191),(1024,1199)]),([5,511,3652,13514,26896],[(1024,132494),(1024,142722),(1024,145794),(1024,394383)]),([5,511,3652,13802,16095,26896],[(1024,145794)]),([5,511,3652,13802,19296,26896],[(1024,164879)]),([5,511,3654,13448,27122],[(1024,145796),(1024,396431)]),([5,511,3679,4070,13448,27122],[(1024,145796)]),([5,511,3679,5645,13448,26896],[]),([5,511,3679,5871,13448,27122],[(1024,11394)]),([5,511,3679,5871,13448,32285],[]),([5,511,3679,8674,13448,26896],[]),([5,511,3679,13448,13802,27122],[])]
def t42 : BT := .nd (blockTree b46) [5,511,3652,13471,13802,26911] (blockTree b47)
def t43 : BT := .nd t41 [5,511,1119,13448,13802,26896] t42
def t44 : BT := .nd t40 [5,482,13448,26896,31648] t43
def t45 : BT := .nd t37 [5,482,3679,13448,26880,27106] t44
def b48 : List Row := [([5,511,3679,13448,26640,32285],[]),([5,511,3679,13448,26896,27122],[(1024,132108)]),([5,511,3679,13448,26896,32285],[]),([5,511,3679,13448,26896,32541],[]),([5,511,3679,13448,26911,32285],[(1024,1324)]),([5,511,3679,13448,27122,32152],[]),([5,511,3679,13448,27122,32285],[]),([5,511,3679,13448,27135,32285],[(1024,1324)]),([5,511,3679,13471,13802,26896],[(1024,178178)]),([5,511,3679,13514,26896],[(1024,132494),(1024,142728),(1024,400524)]),([5,511,3679,13802,16076,26896],[]),([5,511,3679,19319,26896,27122],[(1024,132108)]),([5,511,3679,19319,26896,32285],[])]
def b49 : List Row := [([5,511,13448,26896,27122,28511],[(1024,132100),(1024,132108)]),([5,511,13448,26896,27122,29088],[(1024,132108)]),([5,511,13448,26896,29088,32285],[]),([5,511,13471,13802,26896,29115],[(1024,6306),(1024,178178)]),([5,1119,1506,13448,26896],[(1024,1292),(1024,134540),(1024,165004),(1024,175234),(1024,273410)]),([5,1119,1535,13448,13802,26896],[(1024,142728),(1024,175106),(1024,273410)]),([5,1119,13448,13802,27122],[(1024,132268),(1024,165004),(1024,175106),(1024,175108),(1024,175234)]),([5,1119,13448,26896,32285],[(1024,1292),(1024,142498)]),([5,1506,1535,3679,13448,26896],[(1024,142724),(1024,273410)]),([5,1514,1535,3679,13448,26896],[(1024,142728),(1024,273410)]),([5,1514,3679,13471,26896],[(1024,1295),(1024,142504),(1024,170126),(1024,171148)]),([5,1514,3679,16076,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,407720)]),([5,1631,5871,13448,32285],[(1024,1196),(1024,1292),(1024,132268),(1024,142498)])]
def t46 : BT := .nd (blockTree b48) [5,511,3679,26896,27122,32152] (blockTree b49)
def b50 : List Row := [([5,2048,3679,8674,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,178178),(1024,407556)]),([5,2143,4070,13448,27122],[(1024,132271),(1024,165007),(1024,178306)]),([5,2530,2559,3679,13448,26896],[(1024,14498),(1024,145570)]),([5,2530,3652,8223,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([5,2530,3679,4095,13448,26896],[(1024,14498),(1024,144546),(1024,145570),(1024,145796)]),([5,2530,3679,5871,13448],[(1024,1295),(1024,14498),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([5,2530,3679,8192,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,407556)]),([5,2530,3679,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,407556)]),([5,2530,3679,13448,26911],[(1024,1295),(1024,14498),(1024,14503),(1024,14594),(1024,169999),(1024,407563)]),([5,2530,3679,13448,27122],[(1024,14498),(1024,132271),(1024,145570),(1024,165007),(1024,178306),(1024,407556)]),([5,2530,3679,13448,28500],[(1024,1295),(1024,14594),(1024,80034),(1024,164943),(1024,407556)]),([5,2530,3679,13448,28511],[(1024,1295),(1024,14498),(1024,14594),(1024,263183),(1024,407720)]),([5,2530,3679,15496,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,407556)])]
def b51 : List Row := [([5,2530,3679,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([5,2530,13448,26896,29088],[(1024,1295),(1024,145570),(1024,164879),(1024,165006),(1024,165007),(1024,276482)]),([5,2546,3679,4070,13448,26896],[(1024,145570),(1024,178306)]),([5,3554,3679,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,407556)]),([5,3554,3679,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([5,3652,3679,10722,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,178178),(1024,407556)]),([5,3652,4070,13448,27106,32736],[]),([5,3652,4095,13471,13802,26896],[]),([5,3652,4095,13514,26896],[(1024,132494),(1024,145794),(1024,394383)]),([5,3652,4095,13802,16095,26896],[(1024,145794)]),([5,3652,8351,13802,26896],[(1024,1295),(1024,165007),(1024,178178),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([5,3652,8351,13802,27122],[(1024,3247),(1024,165007),(1024,175108),(1024,178178),(1024,178180),(1024,178306)]),([5,3652,8682,13471,26911],[(1024,10540),(1024,14498),(1024,14504),(1024,76076)])]
def t47 : BT := .nd (blockTree b50) [5,2530,3679,19319,26896] (blockTree b51)
def t48 : BT := .nd t46 [5,1631,13448,26896,32285] t47
def b52 : List Row := [([5,3652,10722,13448,32736],[(1024,164879),(1024,407556)]),([5,3652,13448,13471,26655,32285],[]),([5,3652,13448,13802,27106,32736],[]),([5,3652,13448,26624,32285,32736],[]),([5,3652,13448,26655,32285,32736],[]),([5,3652,13448,27106,32285,32736],[]),([5,3652,13471,13802,26896,32256],[]),([5,3652,13471,13802,27135],[(1024,1199),(1024,76071),(1024,76076),(1024,164879),(1024,175106),(1024,178178)]),([5,3679,4070,4095,13448,27122],[(1024,145796),(1024,177282),(1024,178306)]),([5,3679,4070,5645,13448],[(1024,132271),(1024,165007),(1024,178306)]),([5,3679,4070,13448,26962],[(1024,132367),(1024,134542),(1024,263311),(1024,276610)]),([5,3679,4070,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([5,3679,4070,13471,13802,26896],[])]
def b53 : List Row := [([5,3679,4070,13802,16095,26896],[(1024,276620)]),([5,3679,4070,19319,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([5,3679,4095,13802,16076,26896],[(1024,145570)]),([5,3679,5887,13448,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,276482)]),([5,3679,8674,8703,13448,26896],[]),([5,3679,8690,13448,26896],[(1024,132108),(1024,142338),(1024,407556)]),([5,3679,10240,10722,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,178178),(1024,407556)]),([5,3679,10240,13448,32285],[(1024,1199),(1024,407556)]),([5,3679,10722,13448],[(1024,14498),(1024,178178),(1024,407556),(1024,407720)]),([5,3679,10722,13448,16076],[(1024,1199),(1024,14498),(1024,164879),(1024,178178),(1024,407556),(1024,407620),(1024,407720)]),([5,3679,10722,13448,26896],[(1024,1295),(1024,165007),(1024,178306),(1024,276482),(1024,407556),(1024,407684)]),([5,3679,13448,13471,26640,32285],[]),([5,3679,13448,13802,13823,27122],[(1024,175234)])]
def t49 : BT := .nd (blockTree b52) [5,3679,4070,13514,26896] (blockTree b53)
def b54 : List Row := [([5,3679,13448,13823,26896,32285],[(1024,1292)]),([5,3679,13448,16366,27122],[(1024,14498),(1024,132271),(1024,165007),(1024,178306)]),([5,3679,13448,26640,32285,32736],[]),([5,3679,13448,26880,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,276482)]),([5,3679,13448,26896,27122,32256],[]),([5,3679,13448,26896,30237],[(1024,1199),(1024,1294),(1024,1295),(1024,145570)]),([5,3679,13448,26896,32256,32285],[]),([5,3679,13448,26896,32269],[(1024,1164),(1024,132108)]),([5,3679,13448,27122,28697],[(1024,132271),(1024,165007),(1024,178306)]),([5,3679,13464,26896,32285],[(1024,1295),(1024,134156)]),([5,3679,13471,13802,27122],[(1024,3247),(1024,171148),(1024,175240),(1024,178180)]),([5,3679,13802,16076,27122],[(1024,68783),(1024,165007),(1024,178178),(1024,178180),(1024,178244)]),([5,3679,15496,26896,32285],[(1024,1199),(1024,1295),(1024,145570)])]
def b55 : List Row := [([5,28500,32152,32285,32736],[(1024,1291),(1024,165003)]),([6,2,31,482,3652,13448,27135],[(1024,178178),(1024,178242)]),([6,2,31,482,3679,13448,27122],[(1024,178306)]),([6,2,31,482,28500,32152],[(1024,134311),(1024,268292),(1024,268363),(1024,301323),(1024,396427)]),([6,2,31,511,3652,13448,27122],[(1024,145796)]),([6,2,31,511,3652,13448,27135],[]),([6,2,482,511,3652,13448,26911],[(1024,71980)]),([6,2,482,511,3652,13448,27135],[]),([6,2,482,511,3679,13448,26896],[]),([6,2,511,3652,13448,26911],[(1024,6444),(1024,71980),(1024,301071),(1024,306247)]),([6,2,511,3652,13448,27122],[(1024,145796),(1024,396431)]),([6,4,31,482,28500,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292)]),([6,4,482,511,3679,13448,26896],[])]
def t50 : BT := .nd (blockTree b54) [5,4070,13448,27122,29088] (blockTree b55)
def t51 : BT := .nd t49 [5,3679,13448,13823,26896,27122] t50
def t52 : BT := .nd t48 [5,3652,10271,10722,13448] t51
def b56 : List Row := [([6,8,31,482,28500,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292),(1024,268456),(1024,269479)]),([6,8,482,511,3652,13471,26896],[]),([6,8,482,511,3679,13448,26896],[]),([6,10,31,482,3652,13448,27122],[(1024,145796),(1024,178306)]),([6,10,31,3652,13448,13802,27122],[(1024,145796),(1024,178251),(1024,178306)]),([6,10,482,511,3652,13448,26896],[(1024,145796)]),([6,10,482,3652,13448,13823,26896],[]),([6,15,31,482,3652,6127,13448],[(1024,145570)]),([6,15,31,482,3652,13448,27122],[(1024,178178),(1024,178306)]),([6,15,482,511,3652,5871,13448],[]),([6,15,482,511,3652,13448,26896],[]),([6,15,482,3652,5887,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([6,16,31,482,3652,5645,13448],[(1024,142498),(1024,178306),(1024,306308)])]
def b57 : List Row := [([6,16,31,482,3652,13448,26640],[(1024,132396),(1024,134444),(1024,142498),(1024,145570)]),([6,16,31,482,3652,13448,27122],[(1024,134444),(1024,142498),(1024,178306)]),([6,16,31,482,3652,13464,27122],[(1024,132100),(1024,134444)]),([6,16,31,482,3652,19319,27122],[(1024,142498),(1024,178306)]),([6,16,31,482,3668,13448,27122],[(1024,132263),(1024,142498)]),([6,16,31,482,3679,13448,27122],[(1024,134444),(1024,178306)]),([6,16,31,482,13448,27122,29115],[(1024,134444),(1024,178306)]),([6,16,31,482,28500,32152],[(1024,1291),(1024,134311),(1024,268292),(1024,269479)]),([6,16,31,498,3652,13448,27122],[(1024,132100),(1024,132263)]),([6,16,31,511,3652,13448,27122],[(1024,132263),(1024,134146)]),([6,16,31,3652,4070,13448,27122],[(1024,134439),(1024,178306)]),([6,16,31,3652,13448,13802,27122],[(1024,142498),(1024,178306)]),([6,16,31,3652,13448,26640,32285],[(1024,134444),(1024,142498),(1024,145570)])]
def t53 : BT := .nd (blockTree b56) [6,16,31,482,3652,6127,13448] (blockTree b57)
def b58 : List Row := [([6,16,256,482,3679,13448,26896],[(1024,132108),(1024,134156),(1024,263180),(1024,269324),(1024,276482)]),([6,16,482,482,3679,13448,26896],[(1024,134156),(1024,276482)]),([6,16,482,498,3679,13448,26896],[(1024,132108),(1024,276482)]),([6,16,482,511,3679,13448,26896],[(1024,132396),(1024,134444),(1024,276482)]),([6,16,482,3652,3679,13448,27122],[(1024,134220),(1024,145570)]),([6,16,482,3652,13448,27122,32736],[(1024,165004),(1024,165006),(1024,165007)]),([6,16,482,3652,26911,32152],[(1024,1284),(1024,263172),(1024,269474)]),([6,16,482,3679,4070,13448,26896],[(1024,134220),(1024,145570),(1024,276482)]),([6,16,482,3679,4095,13448,26896],[(1024,132108),(1024,134156),(1024,275458),(1024,276482)]),([6,16,482,3679,5871,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([6,16,482,3679,13448,13802,26896],[(1024,142504),(1024,142728),(1024,273800),(1024,276482)]),([6,16,482,3679,13448,26896],[(1024,1295),(1024,263180),(1024,269710),(1024,276482)]),([6,16,482,3679,13448,26896,27122],[(1024,142340),(1024,276482)])]
def b59 : List Row := [([6,16,482,3679,13448,27122],[]),([6,16,482,3679,13464,26896],[(1024,1295),(1024,134156),(1024,142340),(1024,263180),(1024,269710),(1024,276482)]),([6,16,482,3679,19319,26896],[(1024,1295),(1024,263180),(1024,275458),(1024,276482)]),([6,16,482,3679,26896,32152],[(1024,1294),(1024,269710),(1024,273410),(1024,406792)]),([6,16,482,13448,26896,28511],[(1024,1292),(1024,11522),(1024,263180),(1024,273410)]),([6,16,482,13448,26896,29088],[(1024,1295),(1024,269710),(1024,273410),(1024,276482)]),([6,16,498,3679,13448,26896],[(1024,1295),(1024,132108),(1024,142338),(1024,263180),(1024,269710),(1024,276482)]),([6,16,3679,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,276482)]),([6,18,482,511,3652,13448,26896],[(1024,134444),(1024,142724)]),([6,18,482,511,3652,13448,27122],[(1024,134444),(1024,142724),(1024,145796)]),([6,18,482,3679,13448,26896],[(1024,6415),(1024,132108),(1024,178306),(1024,268300),(1024,269710),(1024,276482),(1024,276487)]),([6,18,482,3679,13448,26896,27122],[(1024,142340),(1024,178306),(1024,276487)]),([6,18,482,3679,13448,27122],[(1024,132271),(1024,178306)])]
def t54 : BT := .nd (blockTree b58) [6,16,482,3679,13448,26896,32285] (blockTree b59)
def t55 : BT := .nd t53 [6,16,31,3652,13448,27122,32285] t54
def b60 : List Row := [([6,20,31,482,28500,32152],[(1024,1291),(1024,134311),(1024,268292),(1024,269479)]),([6,20,482,3679,13448,26896],[(1024,1295),(1024,263180),(1024,269710),(1024,276482)]),([6,20,482,13448,26896,28511],[(1024,1292),(1024,11522),(1024,263180),(1024,273410)]),([6,20,482,13448,26911,28500],[(1024,1292),(1024,263180),(1024,268450)]),([6,23,482,511,3652,13448,26896],[(1024,142724),(1024,178178)]),([6,23,482,511,3652,19319,26896],[(1024,142724),(1024,178178)]),([6,23,482,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,269700),(1024,276482)]),([6,23,482,3652,19319,26911],[(1024,1295),(1024,178178),(1024,263183),(1024,265218),(1024,268588),(1024,276482)]),([6,23,482,3652,19327,26896],[(1024,1188),(1024,76164),(1024,164868),(1024,170276),(1024,171396),(1024,298151),(1024,396456)]),([6,23,482,3679,13448,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([6,23,482,3679,19319,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,24,31,482,3652,13448,27122],[(1024,134444),(1024,142498),(1024,178306)]),([6,24,31,482,28500,32152],[(1024,1291),(1024,134311),(1024,268292),(1024,268363),(1024,268456)])]
def b61 : List Row := [([6,24,482,3679,26896,32152],[(1024,1294),(1024,134542),(1024,269710),(1024,273410),(1024,406660)]),([6,26,482,3652,13448,26896],[(1024,71951),(1024,132111),(1024,134159),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268364),(1024,276551)]),([6,26,482,3652,13448,27122],[(1024,132271),(1024,134159),(1024,145570),(1024,165007),(1024,178306)]),([6,26,482,3652,26896,32152],[(1024,71950),(1024,134542),(1024,165006),(1024,273479),(1024,406660)]),([6,27,482,507,3652,13448,26896],[(1024,145479),(1024,178178),(1024,276482)]),([6,27,482,507,13448,26896,29115],[(1024,145479),(1024,178178),(1024,276482)]),([6,27,482,511,3652,13448,26896],[(1024,276482)]),([6,27,482,511,13448,26896,29115],[(1024,276482)]),([6,27,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([6,27,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268364),(1024,276482)]),([6,27,482,3652,13448,26907],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268364),(1024,276482)]),([6,27,482,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,27,482,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268364),(1024,275458),(1024,276482)])]
def t56 : BT := .nd (blockTree b60) [6,24,482,3679,13448,26896] (blockTree b61)
def b62 : List Row := [([6,27,482,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268364),(1024,276482)]),([6,27,482,5871,13448,29115],[(1024,1295),(1024,77063),(1024,145570),(1024,165007),(1024,275458),(1024,276482)]),([6,27,482,13448,26896,28500],[(1024,1292),(1024,77063),(1024,165004),(1024,268364),(1024,273410)]),([6,27,482,13448,26896,29115],[(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,27,482,13448,26896,29119],[(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,27,482,13448,26896,31163],[(1024,1292),(1024,134540),(1024,165004),(1024,170060),(1024,175234),(1024,273410)]),([6,27,482,13448,26907,29115],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,273410),(1024,276482)]),([6,27,482,13448,27122,29115],[(1024,132271),(1024,165007),(1024,178178),(1024,178306)]),([6,27,482,19319,26896,29115],[(1024,1295),(1024,165007),(1024,178306),(1024,273410),(1024,275458),(1024,276482)]),([6,27,482,26896,29115,32152],[(1024,1294),(1024,134540),(1024,134542),(1024,165006),(1024,406660)]),([6,27,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,27,13448,26896,29115,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,29,31,482,3652,13448,26640],[(1024,14498),(1024,142498),(1024,145570)])]
def b63 : List Row := [([6,29,31,3652,13448,26640,32285],[(1024,14498),(1024,142498),(1024,145570),(1024,301218)]),([6,29,31,3652,13448,27122,32285],[(1024,1199),(1024,132271),(1024,132484),(1024,142498)]),([6,29,482,3679,13448,26896],[(1024,134542),(1024,263468),(1024,276482),(1024,276770),(1024,296207)]),([6,29,482,3679,13448,26896,32285],[(1024,276770)]),([6,29,3652,13448,26896,32287],[(1024,71842),(1024,301218),(1024,394244),(1024,396290)]),([6,29,3679,13448,26896,32285],[(1024,1295),(1024,276770),(1024,296204),(1024,296206),(1024,296207)]),([6,31,31,482,3652,6127,13448],[(1024,145570)]),([6,31,31,482,3652,13448,26640],[(1024,145570)]),([6,31,31,482,28500,32152],[(1024,1291),(1024,134311),(1024,268292),(1024,268456)]),([6,31,31,3652,13448,26640,32285],[(1024,145570)]),([6,31,64,482,13448,27920],[(1024,1292),(1024,134539),(1024,165004),(1024,175234),(1024,273410)]),([6,31,64,482,28500,32152],[(1024,1291),(1024,134539),(1024,165003),(1024,268292),(1024,403588)]),([6,31,64,1506,13448,26896],[(1024,1292),(1024,134540),(1024,165004),(1024,175234),(1024,273410)])]
def t57 : BT := .nd (blockTree b62) [6,29,31,482,3652,13448,27122] (blockTree b63)
def t58 : BT := .nd t56 [6,27,482,3652,26896,32152] t57
def t59 : BT := .nd t55 [6,20,31,482,3652,13448,27122] t58
def t60 : BT := .nd t52 [6,6,511,3652,13448,26896] t59
def t61 : BT := .nd t45 [5,511,3679,13448,13802,27135] t60
def t62 : BT := .nd t30 [5,482,1119,19319,26896] t61
def b64 : List Row := [([6,31,66,482,4095,13448,26896],[(1024,273410)]),([6,31,128,482,3679,13802,26896],[(1024,142504)]),([6,31,128,482,28500,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292)]),([6,31,128,511,3652,13802,26896],[]),([6,31,136,511,3652,13802,26896],[]),([6,31,159,482,3652,13802,26896],[(1024,14504),(1024,142504),(1024,145570)]),([6,31,194,482,3679,13448,26896],[(1024,276482),(1024,276610),(1024,276872)]),([6,31,226,482,3652,5887,13448],[(1024,276482)]),([6,31,226,482,3652,13448,26911],[(1024,178178),(1024,276482)]),([6,31,226,482,3679,5871,13448],[(1024,276482)]),([6,31,226,482,3679,13448,26896],[(1024,178306),(1024,276482)]),([6,31,226,511,3652,5871,13448],[]),([6,31,226,511,3652,13448,26896],[])]
def b65 : List Row := [([6,31,256,482,3652,5856,13448],[(1024,276482),(1024,306439),(1024,306440)]),([6,31,256,482,3652,5887,13448],[(1024,276482),(1024,306434),(1024,306439),(1024,306440)]),([6,31,256,482,3652,13448,26880],[(1024,263468),(1024,268588),(1024,269612),(1024,276482)]),([6,31,256,482,3652,13448,26911],[(1024,268588),(1024,269612),(1024,276482)]),([6,31,256,482,3652,13704,26911],[(1024,263172),(1024,269612)]),([6,31,256,482,3652,19319,26911],[(1024,268588),(1024,276482)]),([6,31,256,482,3679,5871,13448],[(1024,276482),(1024,306439),(1024,306440)]),([6,31,256,482,3679,13448,26896],[(1024,268588),(1024,269612),(1024,276482)]),([6,31,256,482,3679,13448,26911],[(1024,268588),(1024,269612),(1024,276482)]),([6,31,256,482,3679,13704,26896],[(1024,269612)]),([6,31,256,482,3679,19319,26896],[(1024,268588),(1024,276482)]),([6,31,256,482,3908,13448,26911],[(1024,263335),(1024,268588)]),([6,31,256,482,3935,13448,26896],[(1024,263468),(1024,268588)])]
def t63 : BT := .nd (blockTree b64) [6,31,226,3652,6127,13448] (blockTree b65)
def b66 : List Row := [([6,31,256,482,13448,26896,29088],[(1024,269612),(1024,276482)]),([6,31,256,482,13448,26911,28500],[(1024,263335),(1024,268588),(1024,275458)]),([6,31,256,482,13448,26911,28511],[(1024,268588),(1024,275458)]),([6,31,256,482,13448,26911,29115],[(1024,269612),(1024,276482)]),([6,31,256,482,28500,32152],[(1024,134311),(1024,165003),(1024,170116),(1024,268292)]),([6,31,256,3652,13448,26911,32285],[(1024,1292),(1024,1294),(1024,1295)]),([6,31,256,3652,27122,32152],[(1024,132100),(1024,134146),(1024,165000)]),([6,31,256,3679,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295)]),([6,31,256,13448,27122,28500],[(1024,132263),(1024,164999),(1024,170114)]),([6,31,258,482,3679,13448,26896],[(1024,268588),(1024,269612),(1024,276482),(1024,276610)]),([6,31,258,482,3679,13448,26911],[(1024,6444),(1024,268588),(1024,269612),(1024,276482)]),([6,31,258,482,13448,26896,28511],[(1024,263468),(1024,268418),(1024,268588),(1024,275751)]),([6,31,258,482,13448,26911,28500],[(1024,263335),(1024,268290),(1024,268588),(1024,275751)])]
def b67 : List Row := [([6,31,258,511,3652,13448,26911],[(1024,6444),(1024,71980),(1024,269612)]),([6,31,272,482,3652,5871,13448],[(1024,306306),(1024,306308),(1024,306434),(1024,306439)]),([6,31,272,482,3652,13448,26896],[(1024,132396),(1024,134444),(1024,263468),(1024,268588),(1024,276482)]),([6,31,272,482,3652,13448,26911],[(1024,268588),(1024,276482)]),([6,31,272,482,3652,13448,27122],[(1024,178306)]),([6,31,272,482,3652,13720,26896],[(1024,134444),(1024,269612)]),([6,31,272,482,3652,19319,26896],[(1024,132396),(1024,263468),(1024,268588),(1024,276482)]),([6,31,272,482,3652,26896,32152],[(1024,134542),(1024,269710),(1024,273410)]),([6,31,272,482,3679,13448,26896],[(1024,132396),(1024,134444),(1024,268588),(1024,276482)]),([6,31,272,482,3924,13448,26896],[(1024,142498),(1024,268588)]),([6,31,272,482,13448,26896,28500],[(1024,142498),(1024,268588),(1024,275458)]),([6,31,272,482,13448,26896,29115],[(1024,132396),(1024,134444),(1024,263468),(1024,276482)]),([6,31,272,498,3652,13448,26896],[(1024,132396),(1024,268588),(1024,269612)])]
def t64 : BT := .nd (blockTree b66) [6,31,258,511,3652,13448,26896] (blockTree b67)
def t65 : BT := .nd t63 [6,31,256,482,13448,26896,28511] t64
def b68 : List Row := [([6,31,272,3652,13448,26896,27122],[(1024,132271)]),([6,31,272,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,263468)]),([6,31,287,482,3652,5871,13448],[(1024,276482),(1024,306434),(1024,306439)]),([6,31,287,482,3652,13448,26896],[(1024,263468),(1024,268588),(1024,276482)]),([6,31,287,482,3652,13448,26911],[(1024,268588),(1024,276482)]),([6,31,287,482,3652,13704,26896],[(1024,145570),(1024,263172),(1024,269612)]),([6,31,287,482,3652,19319,26896],[(1024,263468),(1024,268588),(1024,276482)]),([6,31,287,482,3679,13448,26896],[(1024,268588),(1024,276482)]),([6,31,287,482,3908,13448,26896],[(1024,145570),(1024,263335),(1024,263468),(1024,268588)]),([6,31,287,482,3935,13448,26896],[(1024,263468),(1024,268588)]),([6,31,287,482,13448,26896,28500],[(1024,132263),(1024,134311),(1024,142498),(1024,263335),(1024,263468),(1024,268588)]),([6,31,287,482,13448,26896,29115],[(1024,263468),(1024,276482)]),([6,31,287,3652,13448,26896,32285],[(1024,1292),(1024,1295),(1024,263468)])]
def b69 : List Row := [([6,31,320,482,3679,13448,26896],[(1024,268588),(1024,269612),(1024,276482)]),([6,31,320,482,28500,32152],[(1024,134311),(1024,134539),(1024,165003),(1024,268292)]),([6,31,322,482,3679,13448,26896],[(1024,142728),(1024,268460),(1024,268588),(1024,269612),(1024,276482),(1024,276610)]),([6,31,340,482,3652,13448,26896],[(1024,132396),(1024,134444),(1024,263468),(1024,268460),(1024,268588),(1024,276482)]),([6,31,351,482,3652,13448,26896],[(1024,263468),(1024,268588),(1024,276482)]),([6,31,354,482,3679,13448,26896],[(1024,142728),(1024,178306),(1024,276482)]),([6,31,354,482,3679,19319,26896],[(1024,3464),(1024,142728),(1024,178306),(1024,276482)]),([6,31,354,511,3652,13448,26896],[(1024,142728),(1024,178178)]),([6,31,354,511,3652,19319,26896],[(1024,142728),(1024,178178)]),([6,31,354,3652,13448,27122],[(1024,132271),(1024,134536),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,354,3652,19319,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,171138),(1024,178178),(1024,178306)]),([6,31,354,3652,19447,26896],[(1024,1192),(1024,3464),(1024,164872),(1024,170280),(1024,302247),(1024,400388)]),([6,31,375,482,3652,13448,26896],[(1024,178178)])]
def t66 : BT := .nd (blockTree b68) [6,31,320,482,3652,13448,26911] (blockTree b69)
def b70 : List Row := [([6,31,383,482,3652,13448,26896],[(1024,178178),(1024,276482)]),([6,31,383,482,3652,19319,26896],[(1024,178178),(1024,276482)]),([6,31,384,482,3652,13448,26911],[(1024,268588),(1024,269486),(1024,269612),(1024,276482)]),([6,31,384,482,3679,13448,26896],[(1024,268588),(1024,269486),(1024,269612),(1024,276482)]),([6,31,384,482,28500,32152],[(1024,134311),(1024,165003),(1024,170116),(1024,268292)]),([6,31,384,3652,13802,26896],[(1024,132270),(1024,165007),(1024,171278),(1024,177416),(1024,269388),(1024,269486),(1024,275624)]),([6,31,384,3652,26896,32250],[(1024,132270),(1024,165006),(1024,171278),(1024,177282),(1024,273576)]),([6,31,408,482,3652,13448,26896],[(1024,132396),(1024,134444),(1024,263468),(1024,268588),(1024,269486),(1024,276482)]),([6,31,415,482,3652,13448,26896],[(1024,263468),(1024,268588),(1024,269486),(1024,276482)]),([6,31,416,482,3679,13448,26896],[(1024,178178),(1024,276482)]),([6,31,416,482,13448,26896,29088],[(1024,178178),(1024,276482),(1024,403458)]),([6,31,418,482,3679,13448,26896],[(1024,178306),(1024,276482)]),([6,31,418,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,170114),(1024,178178),(1024,178306)])]
def b71 : List Row := [([6,31,418,13448,27122,29115],[(1024,132271),(1024,165007),(1024,170114),(1024,178178),(1024,178306)]),([6,31,443,482,3652,13448,26896],[(1024,178178),(1024,276482)]),([6,31,443,482,13448,26896,29115],[(1024,178178),(1024,276482)]),([6,31,447,482,3652,13448,26896],[(1024,178178),(1024,276482)]),([6,31,447,482,13448,26896,29115],[(1024,178178),(1024,276482)]),([6,31,480,482,3652,13448,26880],[(1024,178178),(1024,276482)]),([6,31,480,482,3652,13448,26911],[(1024,178178),(1024,276482)]),([6,31,480,482,3679,13448,26896],[(1024,178178),(1024,276482)]),([6,31,482,482,3652,5887,13448],[(1024,276482)]),([6,31,482,482,3652,13448,26880],[(1024,276482)]),([6,31,482,482,3679,5871,13448],[(1024,276482)]),([6,31,482,482,3679,13448,26896],[(1024,178306),(1024,276482)]),([6,31,482,482,3679,13448,26911],[(1024,178178),(1024,276482)])]
def t67 : BT := .nd (blockTree b70) [6,31,418,13448,26896,29179] (blockTree b71)
def t68 : BT := .nd t66 [6,31,375,482,3652,19319,26896] t67
def t69 : BT := .nd t65 [6,31,272,511,3652,13448,27122] t68
def b72 : List Row := [([6,31,482,482,3679,19319,26896],[(1024,178306),(1024,276482)]),([6,31,482,482,13448,26896,29088],[(1024,178306),(1024,276482)]),([6,31,482,482,28500,32152],[(1024,134311),(1024,165003),(1024,268292),(1024,268456)]),([6,31,482,486,3679,13448,26896],[(1024,178242),(1024,178306),(1024,276482)]),([6,31,482,490,3652,13471,26896],[(1024,178180),(1024,276482)]),([6,31,482,490,3679,13448,26896],[(1024,178306),(1024,276482)]),([6,31,482,498,3652,5871,13448],[(1024,276482),(1024,306306)]),([6,31,482,498,3652,13448,26896],[(1024,132396),(1024,178306),(1024,276482)]),([6,31,482,498,3652,13448,27122],[(1024,178306)]),([6,31,482,498,3652,13464,26896],[(1024,132100),(1024,134444),(1024,276482)]),([6,31,482,498,3652,19319,26896],[(1024,132396),(1024,178306),(1024,276482)]),([6,31,482,498,3668,13448,26896],[(1024,132263),(1024,142498),(1024,276482)]),([6,31,482,498,3679,13448,26896],[(1024,132396),(1024,137228),(1024,178306),(1024,276482),(1024,276487)])]
def b73 : List Row := [([6,31,482,502,3652,13448,26896],[(1024,132396),(1024,178306),(1024,276482)]),([6,31,482,503,3652,13448,26896],[(1024,178178),(1024,276482)]),([6,31,482,503,3652,19319,26896],[(1024,178178),(1024,276482)]),([6,31,482,506,3652,13448,26896],[(1024,132396),(1024,145479),(1024,178306),(1024,276482),(1024,276551)]),([6,31,482,507,3652,13448,26896],[(1024,145479),(1024,178178),(1024,276482)]),([6,31,482,507,13448,26896,29115],[(1024,145479),(1024,178178),(1024,276482)]),([6,31,482,511,1088,13448,26896],[(1024,142724),(1024,175106),(1024,273410)]),([6,31,482,511,1092,13448,26896],[(1024,175106),(1024,273410)]),([6,31,482,511,1160,3652,26896],[(1024,177154),(1024,273410),(1024,275458)]),([6,31,482,511,1604,5871,13448],[(1024,273410),(1024,404484)]),([6,31,482,511,1604,13448,26896],[(1024,175106),(1024,273410)]),([6,31,482,511,3648,13448,26896],[(1024,145703),(1024,178178),(1024,276482)]),([6,31,482,511,3652,5256,5871],[(1024,275458),(1024,404484)])]
def t70 : BT := .nd (blockTree b72) [6,31,482,498,13448,26896,29115] (blockTree b73)
def b74 : List Row := [([6,31,482,511,3652,5632,13448],[(1024,178178),(1024,306178),(1024,306338)]),([6,31,482,511,3652,5645,13448],[(1024,145796),(1024,178306),(1024,306338)]),([6,31,482,511,3652,5856,13448],[(1024,276482),(1024,306178),(1024,306247)]),([6,31,482,511,3652,5871,13448],[(1024,276482)]),([6,31,482,511,3652,5871,19319],[(1024,276482)]),([6,31,482,511,3652,5887,13448],[(1024,276482)]),([6,31,482,511,3652,6127,13448],[(1024,145570)]),([6,31,482,511,3652,6143,13448],[]),([6,31,482,511,3652,13448,26624],[(1024,178178)]),([6,31,482,511,3652,13448,26640],[(1024,145570),(1024,178178)]),([6,31,482,511,3652,13448,26880],[(1024,178178),(1024,276482)]),([6,31,482,511,3652,13448,26896],[(1024,178178),(1024,276482)]),([6,31,482,511,3652,13448,26898],[(1024,178178),(1024,276610)])]
def b75 : List Row := [([6,31,482,511,3652,13448,26904],[(1024,178178),(1024,276482)]),([6,31,482,511,3652,13448,26911],[(1024,71980),(1024,178178),(1024,276482)]),([6,31,482,511,3652,13448,26960],[(1024,145796),(1024,178178),(1024,276482)]),([6,31,482,511,3652,13448,26964],[(1024,178178),(1024,276482)]),([6,31,482,511,3652,13448,27024],[(1024,178178),(1024,276482)]),([6,31,482,511,3652,13448,27032],[(1024,178178),(1024,276482)]),([6,31,482,511,3652,13448,27122],[(1024,145796),(1024,178178),(1024,178306)]),([6,31,482,511,3652,13448,27135],[(1024,178178)]),([6,31,482,511,3652,13448,27920],[(1024,178178),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,511,3652,13450,26896],[(1024,145796),(1024,276775)]),([6,31,482,511,3652,13512,26896],[(1024,145796),(1024,178178),(1024,273410),(1024,276482)]),([6,31,482,511,3652,15496,26896],[(1024,178178),(1024,276482)]),([6,31,482,511,3652,19319,26896],[(1024,178178),(1024,276482)])]
def t71 : BT := .nd (blockTree b74) [6,31,482,511,3652,13448,26900] (blockTree b75)
def t72 : BT := .nd t70 [6,31,482,511,3652,5256,26896] t71
def b76 : List Row := [([6,31,482,511,3652,19319,27122],[(1024,145796),(1024,178178),(1024,178306)]),([6,31,482,511,3652,19319,27135],[(1024,178178)]),([6,31,482,511,3652,26896,27511],[(1024,177154),(1024,275458)]),([6,31,482,511,3654,13448,26896],[(1024,145796),(1024,178242),(1024,276546)]),([6,31,482,511,3660,13448,26896],[(1024,178178),(1024,276482)]),([6,31,482,511,3668,13448,26896],[(1024,132263),(1024,178178),(1024,276482)]),([6,31,482,511,3679,5871,13448],[(1024,276482)]),([6,31,482,511,3679,13448,26896],[(1024,178178),(1024,276482)]),([6,31,482,511,3679,13448,26911],[(1024,6444),(1024,178178),(1024,276482)]),([6,31,482,511,3679,13448,27122],[(1024,178178),(1024,178306)]),([6,31,482,511,3679,13448,27135],[(1024,178178)]),([6,31,482,511,3679,19319,26896],[(1024,178178),(1024,276482)]),([6,31,482,511,3780,13448,26896],[(1024,178178),(1024,276482)])]
def b77 : List Row := [([6,31,482,511,5871,13448,29115],[(1024,276482)]),([6,31,482,511,11844,13448,26896],[(1024,178178),(1024,276482)]),([6,31,482,511,13448,26896,29088],[(1024,178178),(1024,276482)]),([6,31,482,511,13448,26896,29115],[(1024,178178),(1024,276482)]),([6,31,482,511,13448,26896,29119],[(1024,145703),(1024,178178),(1024,276482)]),([6,31,482,511,13448,26896,31163],[(1024,175106),(1024,273410)]),([6,31,482,511,13448,26911,29115],[(1024,71980),(1024,178178),(1024,276482)]),([6,31,482,511,13448,27122,29115],[(1024,145796),(1024,178178),(1024,178306)]),([6,31,482,511,13448,27135,29115],[(1024,178178)]),([6,31,482,511,19319,26896,29115],[(1024,178178),(1024,276482)]),([6,31,482,511,26896,28500,32152],[(1024,134311),(1024,268292),(1024,273410)]),([6,31,482,511,28500,32152],[(1024,134311),(1024,268292),(1024,268456)]),([6,31,482,615,3652,5871],[(1024,1294),(1024,134542),(1024,165006),(1024,404612),(1024,406660)])]
def t73 : BT := .nd (blockTree b76) [6,31,482,511,3788,13448,26896] (blockTree b77)
def b78 : List Row := [([6,31,482,615,3652,27511],[(1024,1294),(1024,3470),(1024,134542),(1024,165006),(1024,406660)]),([6,31,482,615,3652,28500],[(1024,1294),(1024,3335),(1024,134311),(1024,134539),(1024,134542),(1024,165006),(1024,406660)]),([6,31,482,615,3679,26896],[(1024,1294),(1024,134542),(1024,269710),(1024,273410),(1024,275458),(1024,406660)]),([6,31,482,615,13448,28500],[(1024,1292),(1024,134311),(1024,134539),(1024,165004),(1024,268588),(1024,269479),(1024,273410),(1024,306439)]),([6,31,482,615,26896,28500],[(1024,1292),(1024,3335),(1024,134311),(1024,165004),(1024,268588),(1024,269479),(1024,273410),(1024,306439)]),([6,31,482,615,26896,29115],[(1024,1294),(1024,134540),(1024,134542),(1024,165006),(1024,275458),(1024,406660)]),([6,31,482,615,28500],[(1024,3335),(1024,134311),(1024,134539),(1024,269479),(1024,305415)]),([6,31,482,615,28500,32152],[(1024,1291),(1024,134311),(1024,134539),(1024,165003),(1024,170116),(1024,268292),(1024,268456),(1024,268587),(1024,272386)]),([6,31,482,1024,13512,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,273410)]),([6,31,482,1024,28500,32152],[(1024,1292),(1024,134311),(1024,165004),(1024,268292)]),([6,31,482,1028,16076,26896],[(1024,1295),(1024,68907),(1024,134444),(1024,164939),(1024,276482),(1024,305220),(1024,309252)]),([6,31,482,1032,16076,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482),(1024,309415)]),([6,31,482,1032,16095,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,276482),(1024,309415)])]
def b79 : List Row := [([6,31,482,1088,13448,13823,26896],[(1024,273410)]),([6,31,482,1088,13448,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,273410)]),([6,31,482,1088,13448,26911],[(1024,1292),(1024,11522),(1024,175106),(1024,263180),(1024,273410)]),([6,31,482,1088,13448,27122],[(1024,132268),(1024,142498),(1024,165004),(1024,175106),(1024,175234)]),([6,31,482,1088,13448,27984],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,273410)]),([6,31,482,1088,13471,13802,26896],[(1024,11432),(1024,175108),(1024,273800)]),([6,31,482,1088,13512,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,273410)]),([6,31,482,1088,19319,26896],[(1024,1292),(1024,142498),(1024,165004),(1024,175234),(1024,273410)]),([6,31,482,1088,26896,32152],[(1024,1292),(1024,134540),(1024,165004),(1024,273410),(1024,404612)]),([6,31,482,1092,13448,13823,26896],[(1024,273410)]),([6,31,482,1092,13448,26896],[(1024,1292),(1024,69003),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,273410)]),([6,31,482,1098,13448,13802,26896],[(1024,142498),(1024,142504),(1024,142728),(1024,273800)]),([6,31,482,1098,13448,26896],[(1024,269708),(1024,273410),(1024,273800),(1024,400652)])]
def t74 : BT := .nd (blockTree b78) [6,31,482,1088,5871,13448] (blockTree b79)
def t75 : BT := .nd t73 [6,31,482,615,3652,26896] t74
def t76 : BT := .nd t72 [6,31,482,511,3652,19319,26911] t75
def t77 : BT := .nd t69 [6,31,482,482,3679,13448,27122] t76
def b80 : List Row := [([6,31,482,1119,13448,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,142503),(1024,175234),(1024,273410)]),([6,31,482,1160,3652,4095,26896],[(1024,275458)]),([6,31,482,1160,3652,26896],[(1024,1294),(1024,144546),(1024,165006),(1024,177282),(1024,268588),(1024,273410),(1024,275458)]),([6,31,482,1160,3679,4095,26896],[(1024,275458)]),([6,31,482,1160,3679,26896],[(1024,1294),(1024,177282),(1024,268588),(1024,275458)]),([6,31,482,1506,3679,13448,26896],[(1024,178306),(1024,273800),(1024,276482)]),([6,31,482,1514,3679,13448,26896],[(1024,142504),(1024,178306),(1024,273800),(1024,275458),(1024,276482)]),([6,31,482,1535,3652,13448,26896],[(1024,178178),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,1600,5856,13448],[(1024,1292),(1024,11426),(1024,11522),(1024,263180),(1024,273410),(1024,306343)]),([6,31,482,1600,13448,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,268588),(1024,273410),(1024,306439),(1024,404484)]),([6,31,482,1600,13448,26911],[(1024,1292),(1024,11522),(1024,175106),(1024,263180),(1024,268588),(1024,273410),(1024,306439),(1024,404648)]),([6,31,482,1604,3652,5256],[(1024,1198),(1024,3470),(1024,164878),(1024,177154),(1024,404484),(1024,404779),(1024,406532)]),([6,31,482,1604,5256],[(1024,175106),(1024,306343),(1024,404484),(1024,404648)])]
def b81 : List Row := [([6,31,482,1604,5256,13448],[(1024,1196),(1024,11426),(1024,164876),(1024,170284),(1024,175106),(1024,306343),(1024,404484),(1024,404648),(1024,406532),(1024,406696),(1024,406827)]),([6,31,482,1604,5256,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,268588),(1024,273410),(1024,306439),(1024,404484),(1024,404612)]),([6,31,482,1604,5871,13448],[(1024,1292),(1024,142498),(1024,165004),(1024,273410),(1024,306343)]),([6,31,482,1604,5871,19319],[(1024,1292),(1024,3468),(1024,142498),(1024,165004),(1024,273410),(1024,404612)]),([6,31,482,1604,5871,32152],[(1024,1292),(1024,134540),(1024,165004),(1024,273410),(1024,404612)]),([6,31,482,1604,5887,13448],[(1024,1292),(1024,273410),(1024,306343)]),([6,31,482,1604,6127,13448],[(1024,142498),(1024,165004),(1024,306343)]),([6,31,482,1604,7919,13448],[(1024,1196),(1024,3468),(1024,164876),(1024,170284),(1024,306343),(1024,404484)]),([6,31,482,1604,8192,13448],[(1024,1196),(1024,3468),(1024,164876),(1024,170284),(1024,404484)]),([6,31,482,1604,13448,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,268588),(1024,273410),(1024,306439),(1024,404484)]),([6,31,482,1604,13448,26911],[(1024,1292),(1024,11522),(1024,175106),(1024,263180),(1024,268588),(1024,273410),(1024,306439),(1024,404648)]),([6,31,482,1604,13448,27122],[(1024,132268),(1024,142498),(1024,165004),(1024,175106),(1024,175234),(1024,306343),(1024,404484)]),([6,31,482,1604,13448,28500],[(1024,1292),(1024,142498),(1024,165004),(1024,268588),(1024,306343),(1024,306439),(1024,404484)])]
def t78 : BT := .nd (blockTree b80) [6,31,482,1604,5256,5871] (blockTree b81)
def b82 : List Row := [([6,31,482,1604,26896,32152],[(1024,1292),(1024,134540),(1024,165004),(1024,273410),(1024,404612)]),([6,31,482,1615,5871,13448],[(1024,1292),(1024,273410),(1024,306343)]),([6,31,482,1615,13448,26896],[(1024,1292),(1024,268588),(1024,269708),(1024,273410),(1024,306439),(1024,404484)]),([6,31,482,1631,5871,13448],[(1024,1292),(1024,142498),(1024,142503),(1024,273410),(1024,306343)]),([6,31,482,1631,13448,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,142503),(1024,175234),(1024,268588),(1024,273410),(1024,306439),(1024,404484)]),([6,31,482,2048,3652,5256],[(1024,1198),(1024,3470),(1024,164878),(1024,170286),(1024,308391),(1024,406532)]),([6,31,482,2048,3652,27511],[(1024,1198),(1024,3470),(1024,164878),(1024,170286),(1024,406532)]),([6,31,482,2048,11844,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,309415),(1024,407556)]),([6,31,482,2048,28500,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292)]),([6,31,482,2064,3652,13448,27122],[(1024,134542),(1024,142498),(1024,145570),(1024,178306)]),([6,31,482,2064,3679,13448,27122],[(1024,134542),(1024,178306)]),([6,31,482,2304,3652,13448,26911],[(1024,14503),(1024,268588),(1024,269710),(1024,276482)]),([6,31,482,2304,3679,13448,26896],[(1024,14503),(1024,145570),(1024,268588),(1024,269710),(1024,276482)])]
def b83 : List Row := [([6,31,482,2320,3679,13448,26896],[(1024,132494),(1024,134542),(1024,268588),(1024,276482)]),([6,31,482,2335,3652,13448,26896],[(1024,263244),(1024,268588),(1024,276482)]),([6,31,482,2530,3679,13448,26896],[(1024,14503),(1024,145570),(1024,145575),(1024,178306),(1024,276482)]),([6,31,482,2546,3652,13448,26896],[(1024,132494),(1024,178306),(1024,276482)]),([6,31,482,2546,3679,13448,26896],[(1024,132494),(1024,178306),(1024,276482),(1024,276487)]),([6,31,482,2559,3652,13448,26896],[(1024,178178),(1024,276482)]),([6,31,482,2628,20343,26896],[(1024,1195),(1024,3467),(1024,164875),(1024,170283),(1024,305319),(1024,403460)]),([6,31,482,3072,28500,32152],[(1024,1294),(1024,134311),(1024,165006),(1024,268292)]),([6,31,482,3136,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,31,482,3136,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,3136,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]),([6,31,482,3648,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3648,13448,26880],[(1024,1295),(1024,263183),(1024,268588),(1024,269710),(1024,276482)])]
def t79 : BT := .nd (blockTree b82) [6,31,482,2320,3652,13448,26896] (blockTree b83)
def t80 : BT := .nd t78 [6,31,482,1604,19319,26896] t79
def b84 : List Row := [([6,31,482,3648,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,31,482,3648,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,3648,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,31,482,3648,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]),([6,31,482,3652,3668,13448,27122],[(1024,142498),(1024,145570),(1024,178306)]),([6,31,482,3652,3679,6127,13448],[(1024,145570)]),([6,31,482,3652,3679,13448,26640],[(1024,145570)]),([6,31,482,3652,3908,13448,26911],[(1024,268588),(1024,276482)]),([6,31,482,3652,3924,13448,26896],[(1024,263244),(1024,268588),(1024,276482)]),([6,31,482,3652,3935,13448,26896],[(1024,263244),(1024,268588),(1024,276482)]),([6,31,482,3652,4070,5887,13448],[(1024,276482)]),([6,31,482,3652,4070,13448,26880],[(1024,276482)]),([6,31,482,3652,4086,13448,26896],[(1024,276482)])]
def b85 : List Row := [([6,31,482,3652,4095,13448,26896],[(1024,275458),(1024,276482)]),([6,31,482,3652,4095,13448,27122],[(1024,145796),(1024,177282),(1024,178306)]),([6,31,482,3652,4095,19319,26896],[(1024,276482)]),([6,31,482,3652,4267,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,268292),(1024,268587),(1024,275458),(1024,403588),(1024,406660)]),([6,31,482,3652,4847,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3652,5256,5871],[(1024,1294),(1024,144546),(1024,165006),(1024,273410),(1024,275458),(1024,406532)]),([6,31,482,3652,5256,5887],[(1024,1294),(1024,273410),(1024,275458),(1024,406532)]),([6,31,482,3652,5256,6127],[(1024,142498),(1024,144546),(1024,165006),(1024,406532)]),([6,31,482,3652,5256,14063],[(1024,1198),(1024,3470),(1024,164878),(1024,170286),(1024,406532)]),([6,31,482,3652,5256,26896],[(1024,1294),(1024,134542),(1024,144546),(1024,165006),(1024,177282),(1024,268588),(1024,275458),(1024,406532),(1024,406660)]),([6,31,482,3652,5256,26911],[(1024,1294),(1024,13570),(1024,177154),(1024,263182),(1024,268588),(1024,275458),(1024,406532)]),([6,31,482,3652,5256,27122],[(1024,132270),(1024,144546),(1024,165006),(1024,177154),(1024,177282),(1024,406532),(1024,406660)]),([6,31,482,3652,5256,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406532),(1024,406660)])]
def t81 : BT := .nd (blockTree b84) [6,31,482,3652,4095,5871,13448] (blockTree b85)
def b86 : List Row := [([6,31,482,3652,5645,13448],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,3652,5645,19319],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,3652,5663,13448],[(1024,1199),(1024,14498),(1024,178178),(1024,306338)]),([6,31,482,3652,5743,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482)]),([6,31,482,3652,5807,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482)]),([6,31,482,3652,5836,13448],[(1024,1199),(1024,14498),(1024,164879),(1024,175106),(1024,177154),(1024,178178),(1024,306180),(1024,306343),(1024,306344)]),([6,31,482,3652,5856,13448],[(1024,1295),(1024,14498),(1024,14594),(1024,263183),(1024,273410),(1024,276482)]),([6,31,482,3652,5856,19319],[(1024,1295),(1024,14498),(1024,14594),(1024,263183),(1024,273410),(1024,276482)]),([6,31,482,3652,5863,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482)]),([6,31,482,3652,5867,13448],[(1024,1295),(1024,76962),(1024,164940),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3652,5869,13448],[(1024,132367),(1024,145570),(1024,145666),(1024,263311),(1024,273538),(1024,275586),(1024,276482),(1024,276610)]),([6,31,482,3652,5871,6143,13448],[(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)])]
def b87 : List Row := [([6,31,482,3652,5871,13448,32256],[(1024,178178)]),([6,31,482,3652,5871,13450],[(1024,145796),(1024,273703),(1024,275751),(1024,276775),(1024,301327),(1024,396431)]),([6,31,482,3652,5871,13452],[(1024,1295),(1024,68775),(1024,164939),(1024,170052)]),([6,31,482,3652,5871,13464],[(1024,1295),(1024,76932),(1024,134444),(1024,165006),(1024,275458),(1024,306308),(1024,406660)]),([6,31,482,3652,5871,13471,13802],[(1024,142504),(1024,276775)]),([6,31,482,3652,5871,13512],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,273474),(1024,275458),(1024,276482)]),([6,31,482,3652,5871,13704],[(1024,1294),(1024,77064),(1024,165007),(1024,269612),(1024,275458),(1024,306440),(1024,406792)]),([6,31,482,3652,5871,15496],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482),(1024,309415)]),([6,31,482,3652,5871,19319],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482),(1024,406660)]),([6,31,482,3652,5871,27511],[(1024,1294),(1024,3470),(1024,134542),(1024,144546),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]),([6,31,482,3652,5871,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,275458),(1024,404612),(1024,406660)]),([6,31,482,3652,5887,6127,13448],[(1024,142498),(1024,144546),(1024,145570),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3652,5887,6143,13448],[(1024,273410),(1024,275458),(1024,276482)])]
def t82 : BT := .nd (blockTree b86) [6,31,482,3652,5871,13448,13823] (blockTree b87)
def t83 : BT := .nd t81 [6,31,482,3652,5632,13448] t82
def t84 : BT := .nd t80 [6,31,482,3648,13448,26896] t83
def b88 : List Row := [([6,31,482,3652,5887,13448,13802],[(1024,273410),(1024,276482),(1024,276551)]),([6,31,482,3652,5887,13448,32285],[]),([6,31,482,3652,5887,19319],[(1024,1295),(1024,273410),(1024,276482),(1024,406792)]),([6,31,482,3652,6114,13448],[(1024,11426),(1024,14498),(1024,164879),(1024,306178)]),([6,31,482,3652,6127,6143,13448],[(1024,142498),(1024,144546),(1024,145570)]),([6,31,482,3652,6127,13448],[(1024,142498),(1024,144546),(1024,145570),(1024,165007)]),([6,31,482,3652,6127,13448,13471],[(1024,145570)]),([6,31,482,3652,6127,13448,32736],[(1024,145570)]),([6,31,482,3652,6127,19319],[(1024,142498),(1024,145570),(1024,165007),(1024,406660)]),([6,31,482,3652,6143,13448],[]),([6,31,482,3652,6143,13448,26896],[(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3652,7919,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,275458),(1024,406660)]),([6,31,482,3652,8192,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)])]
def b89 : List Row := [([6,31,482,3652,8448,13448,26911],[(1024,268588),(1024,269612),(1024,276482)]),([6,31,482,3652,8458,13448,26896],[(1024,263468),(1024,268588),(1024,269612),(1024,276482),(1024,276610)]),([6,31,482,3652,8464,13448,26896],[(1024,132396),(1024,134444),(1024,263468),(1024,268588),(1024,276482)]),([6,31,482,3652,8479,13448,26896],[(1024,263468),(1024,268588),(1024,276482)]),([6,31,482,3652,8690,13448,26896],[(1024,132396),(1024,178306),(1024,276482)]),([6,31,482,3652,8703,13448,26896],[(1024,178178),(1024,276482)]),([6,31,482,3652,10240,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([6,31,482,3652,10240,15496],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([6,31,482,3652,10240,19319],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([6,31,482,3652,10252,13448],[(1024,1199),(1024,14498),(1024,164879),(1024,170287),(1024,171407),(1024,407556),(1024,407620),(1024,407720)]),([6,31,482,3652,10256,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([6,31,482,3652,10271,13448],[(1024,1199),(1024,3471),(1024,170287),(1024,309415),(1024,407556)]),([6,31,482,3652,10432,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,178178),(1024,403759),(1024,407556)])]
def t85 : BT := .nd (blockTree b88) [6,31,482,3652,8208,13448,27122] (blockTree b89)
def b90 : List Row := [([6,31,482,3652,10722,13448],[(1024,3471),(1024,164879),(1024,170287),(1024,309415),(1024,407556)]),([6,31,482,3652,13448,13464,27122],[(1024,134444),(1024,178306)]),([6,31,482,3652,13448,13471,26640],[(1024,145570)]),([6,31,482,3652,13448,13704,26911],[(1024,269612),(1024,276482)]),([6,31,482,3652,13448,13720,26896],[(1024,134444),(1024,276482)]),([6,31,482,3652,13448,13727,26896],[(1024,276482)]),([6,31,482,3652,13448,13792,26896],[(1024,273410)]),([6,31,482,3652,13448,13802,26880],[(1024,273410),(1024,276482),(1024,276551)]),([6,31,482,3652,13448,13818,26896],[(1024,273410),(1024,276482),(1024,276551)]),([6,31,482,3652,13448,13823,26896],[(1024,273410),(1024,276482)]),([6,31,482,3652,13448,13823,26911],[(1024,273410),(1024,276482)]),([6,31,482,3652,13448,13823,27122],[(1024,175234),(1024,178306)]),([6,31,482,3652,13448,13823,27135],[(1024,175106),(1024,178178)])]
def b91 : List Row := [([6,31,482,3652,13448,18944,26896],[]),([6,31,482,3652,13448,18975,26896],[(1024,276482)]),([6,31,482,3652,13448,22527],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([6,31,482,3652,13448,26624],[]),([6,31,482,3652,13448,26624,26896],[(1024,276482)]),([6,31,482,3652,13448,26624,32256],[]),([6,31,482,3652,13448,26640],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306)]),([6,31,482,3652,13448,26640,26655],[(1024,145570)]),([6,31,482,3652,13448,26640,32736],[(1024,145570)]),([6,31,482,3652,13448,26653],[(1024,1199),(1024,1324),(1024,11426),(1024,14498),(1024,164879),(1024,178178)]),([6,31,482,3652,13448,26655],[(1024,178178)]),([6,31,482,3652,13448,26655,26896],[(1024,145570),(1024,276482)]),([6,31,482,3652,13448,26655,32285],[(1024,1199),(1024,14498)])]
def t86 : BT := .nd (blockTree b90) [6,31,482,3652,13448,16383,26896] (blockTree b91)
def t87 : BT := .nd t85 [6,31,482,3652,10496,13448] t86
def b92 : List Row := [([6,31,482,3652,13448,26880,27106],[(1024,276482)]),([6,31,482,3652,13448,26880,32285],[]),([6,31,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3652,13448,26896,27106],[(1024,178306),(1024,276482)]),([6,31,482,3652,13448,26896,28672],[]),([6,31,482,3652,13448,26896,32256],[]),([6,31,482,3652,13448,26896,32269],[]),([6,31,482,3652,13448,26896,32324],[(1024,276482)]),([6,31,482,3652,13448,26896,32392],[(1024,276482)]),([6,31,482,3652,13448,26896,32480],[(1024,276482)]),([6,31,482,3652,13448,26896,32495],[(1024,276482)]),([6,31,482,3652,13448,26898],[(1024,132367),(1024,134542),(1024,145666),(1024,178306),(1024,263311),(1024,268588),(1024,276482),(1024,276610)]),([6,31,482,3652,13448,26900],[(1024,1295),(1024,134542),(1024,164940),(1024,178306),(1024,268588),(1024,276482)])]
def b93 : List Row := [([6,31,482,3652,13448,26903],[(1024,1295),(1024,3372),(1024,3470),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,31,482,3652,13448,26904],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3652,13448,26906],[(1024,132367),(1024,145666),(1024,178306),(1024,263311),(1024,268588),(1024,276482),(1024,276551),(1024,276610)]),([6,31,482,3652,13448,26907],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,31,482,3652,13448,26908],[(1024,1295),(1024,76962),(1024,164940),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3652,13448,26909],[(1024,1324),(1024,14498),(1024,164879),(1024,178178),(1024,268588),(1024,276482),(1024,276775),(1024,301327)]),([6,31,482,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,31,482,3652,13448,26911,32256],[(1024,301071)]),([6,31,482,3652,13448,26911,32287],[(1024,276482)]),([6,31,482,3652,13448,26911,32511],[(1024,276482)]),([6,31,482,3652,13448,26911,32541],[(1024,276775)]),([6,31,482,3652,13448,26931],[(1024,1199),(1024,3372),(1024,3470),(1024,14498),(1024,164879),(1024,170284),(1024,171308),(1024,178178)]),([6,31,482,3652,13448,26960],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)])]
def t88 : BT := .nd (blockTree b92) [6,31,482,3652,13448,26902] (blockTree b93)
def b94 : List Row := [([6,31,482,3652,13448,26964],[(1024,1295),(1024,134542),(1024,164940),(1024,178306),(1024,276482)]),([6,31,482,3652,13448,26975],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,276482)]),([6,31,482,3652,13448,26994],[(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,171308),(1024,178178),(1024,178306)]),([6,31,482,3652,13448,27024],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3652,13448,27026],[(1024,132367),(1024,145666),(1024,178306),(1024,263311),(1024,268588),(1024,276482),(1024,276610)]),([6,31,482,3652,13448,27032],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3652,13448,27039],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,31,482,3652,13448,27058],[(1024,132271),(1024,145570),(1024,165007),(1024,170284),(1024,178178),(1024,178306)]),([6,31,482,3652,13448,27088],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([6,31,482,3652,13448,27104],[(1024,1199),(1024,164879),(1024,165164),(1024,178178)]),([6,31,482,3652,13448,27106],[(1024,178178)]),([6,31,482,3652,13448,27106,32736],[(1024,164879),(1024,178178)]),([6,31,482,3652,13448,27120],[(1024,1199),(1024,145796),(1024,165164),(1024,178178),(1024,178306),(1024,396431)])]
def b95 : List Row := [([6,31,482,3652,13448,27122,32256],[(1024,396431)]),([6,31,482,3652,13448,27122,32738],[(1024,178306)]),([6,31,482,3652,13448,27122,32751],[(1024,178306)]),([6,31,482,3652,13448,27122,32752],[(1024,178178),(1024,178306)]),([6,31,482,3652,13448,27126],[(1024,132271),(1024,164940),(1024,178178),(1024,178242),(1024,178306)]),([6,31,482,3652,13448,27130],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,3652,13448,27135],[(1024,1199),(1024,14498),(1024,164879),(1024,178178)]),([6,31,482,3652,13448,27135,32256],[]),([6,31,482,3652,13448,27920],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([6,31,482,3652,13448,27924],[(1024,1295),(1024,134542),(1024,164940),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([6,31,482,3652,13448,27928],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([6,31,482,3652,13448,27935],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,273410),(1024,276482)]),([6,31,482,3652,13448,27984],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)])]
def t89 : BT := .nd (blockTree b94) [6,31,482,3652,13448,27122] (blockTree b95)
def t90 : BT := .nd t88 [6,31,482,3652,13448,26962] t89
def t91 : BT := .nd t87 [6,31,482,3652,13448,26880] t90
def t92 : BT := .nd t84 [6,31,482,3652,5887,13448] t91
def t93 : BT := .nd t77 [6,31,482,1119,13448,13802,26896] t92
def b96 : List Row := [([6,31,482,3652,13448,28146],[(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,178178),(1024,178306)]),([6,31,482,3652,13450,26896],[(1024,134542),(1024,145796),(1024,268588),(1024,276775),(1024,301327),(1024,396431)]),([6,31,482,3652,13450,26898],[(1024,134542),(1024,145796),(1024,268588),(1024,276775),(1024,301327),(1024,396431)]),([6,31,482,3652,13450,26911],[(1024,268588),(1024,276775),(1024,301327)]),([6,31,482,3652,13450,27122],[(1024,145796),(1024,396431)]),([6,31,482,3652,13452,26896],[(1024,1295),(1024,68775),(1024,134542),(1024,164939),(1024,170052)]),([6,31,482,3652,13452,26900],[(1024,1295),(1024,68775),(1024,68908),(1024,76076),(1024,134542),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3652,13452,26911],[(1024,1295),(1024,68775),(1024,76076),(1024,170052),(1024,263183)]),([6,31,482,3652,13452,27122],[(1024,68775),(1024,132271),(1024,164939),(1024,170052),(1024,178306)]),([6,31,482,3652,13454,26896],[(1024,66727),(1024,68775),(1024,134542),(1024,170052),(1024,301327),(1024,396363)]),([6,31,482,3652,13464,13802,26896],[(1024,134444),(1024,142504),(1024,276482)]),([6,31,482,3652,13464,26896],[(1024,1295),(1024,134220),(1024,134444),(1024,134542),(1024,165006),(1024,268588),(1024,306308)]),([6,31,482,3652,13464,27122],[(1024,134146),(1024,134220),(1024,134439),(1024,134444),(1024,165006),(1024,306308)])]
def b97 : List Row := [([6,31,482,3652,13466,27122],[(1024,132271),(1024,134159),(1024,134220),(1024,134439),(1024,134444),(1024,306308),(1024,396430)]),([6,31,482,3652,13468,26896],[(1024,1295),(1024,68775),(1024,134444),(1024,134542),(1024,164939),(1024,170052),(1024,306308)]),([6,31,482,3652,13471,13704,26896],[(1024,269612),(1024,276482)]),([6,31,482,3652,13471,13802,26896],[(1024,14504),(1024,142504),(1024,178180),(1024,276775)]),([6,31,482,3652,13471,13802,26911],[(1024,11432),(1024,14504),(1024,178178),(1024,276775)]),([6,31,482,3652,13471,13802,27122],[(1024,14498),(1024,142504),(1024,145796),(1024,178180)]),([6,31,482,3652,13471,18965,26896],[(1024,3239),(1024,3247),(1024,14504),(1024,142504)]),([6,31,482,3652,13512,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([6,31,482,3652,13512,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,273410),(1024,273474),(1024,276482)]),([6,31,482,3652,13512,26960],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([6,31,482,3652,13512,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,178178),(1024,178306)]),([6,31,482,3652,13514,26896],[(1024,134542),(1024,145796),(1024,273800),(1024,276872),(1024,396431),(1024,400655)]),([6,31,482,3652,13516,26896],[(1024,1295),(1024,69003),(1024,134542),(1024,164939),(1024,276482),(1024,403524)])]
def t94 : BT := .nd (blockTree b96) [6,31,482,3652,13466,26896] (blockTree b97)
def b98 : List Row := [([6,31,482,3652,13704,26911],[(1024,1294),(1024,269474),(1024,269612),(1024,275458),(1024,306440)]),([6,31,482,3652,13706,26896],[(1024,134542),(1024,263468),(1024,269388),(1024,269612),(1024,275751),(1024,301326),(1024,306440),(1024,396431)]),([6,31,482,3652,13706,26911],[(1024,263183),(1024,269612),(1024,275751),(1024,301326),(1024,306440)]),([6,31,482,3652,13720,26896],[(1024,1294),(1024,134220),(1024,134444),(1024,134542),(1024,165006),(1024,275458),(1024,306308)]),([6,31,482,3652,13768,26896],[(1024,1294),(1024,134542),(1024,165007),(1024,268588),(1024,269388),(1024,269612),(1024,306440)]),([6,31,482,3652,13802,16095,26896],[(1024,178180),(1024,276872)]),([6,31,482,3652,13802,19296,26896],[(1024,171023),(1024,171148),(1024,178180)]),([6,31,482,3652,13823,19319,26896],[(1024,273410),(1024,276482)]),([6,31,482,3652,15496,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([6,31,482,3652,15496,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268591),(1024,276482),(1024,309511),(1024,407720)]),([6,31,482,3652,15496,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,309415),(1024,407556)]),([6,31,482,3652,15496,28500],[(1024,1295),(1024,145570),(1024,165007),(1024,268591),(1024,309415),(1024,309511),(1024,407556)]),([6,31,482,3652,15500,26896],[(1024,1295),(1024,68775),(1024,134542),(1024,164939),(1024,170052),(1024,309511),(1024,407556)])]
def b99 : List Row := [([6,31,482,3652,15512,26896],[(1024,1295),(1024,134542),(1024,165006),(1024,268591),(1024,406660),(1024,407556)]),([6,31,482,3652,15560,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,407556)]),([6,31,482,3652,15560,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,407556)]),([6,31,482,3652,15752,26896],[(1024,1294),(1024,134542),(1024,165007),(1024,269710),(1024,273410),(1024,406792),(1024,407556)]),([6,31,482,3652,16076,27920],[(1024,1295),(1024,134443),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,407556)]),([6,31,482,3652,17271,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,275458),(1024,276482),(1024,309415),(1024,309511)]),([6,31,482,3652,18704,27511],[(1024,1198),(1024,3470),(1024,164878),(1024,170286),(1024,406532)]),([6,31,482,3652,19063,26896],[(1024,1294),(1024,165007),(1024,269388),(1024,269612),(1024,275458),(1024,306440)]),([6,31,482,3652,19255,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,275458),(1024,276482)]),([6,31,482,3652,19303,26896],[(1024,1295),(1024,134220),(1024,134444),(1024,165006),(1024,268588),(1024,275458),(1024,306308)]),([6,31,482,3652,19315,26896],[(1024,1295),(1024,68775),(1024,164939),(1024,170052)]),([6,31,482,3652,19317,26896],[(1024,145796),(1024,268588),(1024,275751),(1024,276775),(1024,301327),(1024,396431)]),([6,31,482,3652,19319,26640],[(1024,132271),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,178306)])]
def t95 : BT := .nd (blockTree b98) [6,31,482,3652,15500,26911] (blockTree b99)
def t96 : BT := .nd t94 [6,31,482,3652,13704,26896] t95
def b100 : List Row := [([6,31,482,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,31,482,3652,19319,26896,32256],[]),([6,31,482,3652,19319,26898],[(1024,132367),(1024,145666),(1024,178306),(1024,263311),(1024,268588),(1024,275586),(1024,276482),(1024,276610)]),([6,31,482,3652,19319,26900],[(1024,1295),(1024,164940),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,31,482,3652,19319,26903],[(1024,1295),(1024,3372),(1024,178178),(1024,263183),(1024,268588),(1024,275458),(1024,276482)]),([6,31,482,3652,19319,26904],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3652,19319,26911],[(1024,1295),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,31,482,3652,19319,26960],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,275458),(1024,276482)]),([6,31,482,3652,19319,26994],[(1024,132271),(1024,145570),(1024,165007),(1024,171308),(1024,177282),(1024,178178),(1024,178306)]),([6,31,482,3652,19319,27024],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3652,19319,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,3652,19319,27135],[(1024,1199),(1024,164879),(1024,178178)]),([6,31,482,3652,19319,27920],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,275458),(1024,276482)])]
def b101 : List Row := [([6,31,482,3652,26640,31896],[(1024,134542),(1024,142498),(1024,144546),(1024,165006),(1024,406660)]),([6,31,482,3652,26880,32136],[(1024,1294),(1024,269710),(1024,273410),(1024,275458),(1024,406792)]),([6,31,482,3652,26896,27511],[(1024,1294),(1024,3470),(1024,144546),(1024,165006),(1024,177282),(1024,268588),(1024,275458)]),([6,31,482,3652,26896,30104],[(1024,1294),(1024,134220),(1024,134444),(1024,134542),(1024,165006),(1024,275458),(1024,306308)]),([6,31,482,3652,26896,31896],[(1024,134542),(1024,142498),(1024,144546),(1024,165006),(1024,406660)]),([6,31,482,3652,26896,32136],[(1024,1294),(1024,134542),(1024,269710),(1024,273410),(1024,275458),(1024,406792)]),([6,31,482,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]),([6,31,482,3652,26896,32154],[(1024,132494),(1024,134542),(1024,273703),(1024,301326),(1024,396430),(1024,406660)]),([6,31,482,3652,26896,32156],[(1024,1294),(1024,68775),(1024,134542),(1024,164939),(1024,170052),(1024,406660)]),([6,31,482,3652,26896,32216],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]),([6,31,482,3652,26898,32152],[(1024,132100),(1024,134542),(1024,263172),(1024,263243),(1024,273703),(1024,301326),(1024,396430),(1024,406660)]),([6,31,482,3652,26898,32154],[(1024,132366),(1024,134542),(1024,263310),(1024,273538),(1024,406660)]),([6,31,482,3652,26900,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,406660)])]
def t97 : BT := .nd (blockTree b100) [6,31,482,3652,24848,32152] (blockTree b101)
def b102 : List Row := [([6,31,482,3652,26911,27122,32152],[(1024,132100),(1024,134439),(1024,134542),(1024,268292),(1024,269700)]),([6,31,482,3652,26911,27511],[(1024,1294),(1024,3470),(1024,177154),(1024,263182),(1024,268588),(1024,275458)]),([6,31,482,3652,26960,32152],[(1024,1294),(1024,134439),(1024,134542),(1024,165006),(1024,268292),(1024,406660)]),([6,31,482,3652,26960,32216],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([6,31,482,3652,27122,27511],[(1024,3470),(1024,132270),(1024,144546),(1024,165006),(1024,177154),(1024,177282)]),([6,31,482,3652,27511,32152],[(1024,1294),(1024,3470),(1024,134542),(1024,165006),(1024,275458),(1024,406660)]),([6,31,482,3652,27920,32152],[(1024,1294),(1024,134443),(1024,134539),(1024,134542),(1024,165006),(1024,272386),(1024,406660)]),([6,31,482,3652,28500,32152],[(1024,1294),(1024,134539),(1024,134542),(1024,165006),(1024,268292),(1024,268587),(1024,406660)]),([6,31,482,3654,5871,13448],[(1024,66831),(1024,145796),(1024,273474),(1024,275522),(1024,276482),(1024,276546),(1024,396431)]),([6,31,482,3654,13448,26896],[(1024,66831),(1024,134542),(1024,145796),(1024,268588),(1024,276482),(1024,276546),(1024,396431)]),([6,31,482,3654,13448,26898],[(1024,134542),(1024,145796),(1024,268588),(1024,276546),(1024,276610),(1024,276775),(1024,301327),(1024,396431)]),([6,31,482,3654,13448,26911],[(1024,66831),(1024,178242),(1024,268588),(1024,276482),(1024,276546)]),([6,31,482,3654,13448,27122],[(1024,145796),(1024,178242),(1024,178306),(1024,396431)])]
def b103 : List Row := [([6,31,482,3654,19319,26896],[(1024,66831),(1024,145796),(1024,268588),(1024,275522),(1024,276482),(1024,276546),(1024,396431)]),([6,31,482,3654,26896,32152],[(1024,66830),(1024,134542),(1024,273474),(1024,396430),(1024,406660)]),([6,31,482,3660,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3660,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([6,31,482,3660,13448,26904],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([6,31,482,3660,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,31,482,3660,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,3660,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,31,482,3660,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,269710),(1024,273410),(1024,406792)]),([6,31,482,3662,13448,13802,26896],[(1024,145576),(1024,145800),(1024,273800),(1024,276546)]),([6,31,482,3662,13448,26896],[(1024,66831),(1024,268588),(1024,269710),(1024,276482),(1024,276546)]),([6,31,482,3663,5871,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3663,13448,26896],[(1024,1295),(1024,268588),(1024,269710),(1024,276482)])]
def t98 : BT := .nd (blockTree b102) [6,31,482,3654,13450,26896] (blockTree b103)
def t99 : BT := .nd t97 [6,31,482,3652,26900,32156] t98
def t100 : BT := .nd t96 [6,31,482,3652,19319,26880] t99
def b104 : List Row := [([6,31,482,3668,5871,13448],[(1024,1295),(1024,142498),(1024,165004),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3668,13448,26896],[(1024,1295),(1024,142498),(1024,165004),(1024,268588),(1024,269710),(1024,276482)]),([6,31,482,3668,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,31,482,3668,13448,27122],[(1024,132263),(1024,142498),(1024,165004),(1024,178178),(1024,178306)]),([6,31,482,3668,13464,26896],[(1024,1295),(1024,134311),(1024,134444),(1024,141388),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]),([6,31,482,3668,19319,26896],[(1024,1295),(1024,142498),(1024,165004),(1024,268588),(1024,275458),(1024,276482)]),([6,31,482,3668,26896,32152],[(1024,1294),(1024,134542),(1024,165004),(1024,269710),(1024,273410),(1024,406792)]),([6,31,482,3670,13448,26896],[(1024,66831),(1024,142724),(1024,178306),(1024,268588),(1024,269710),(1024,276482),(1024,276546),(1024,396428)]),([6,31,482,3670,13448,27122],[(1024,132271),(1024,142724),(1024,178242),(1024,178306),(1024,396428)]),([6,31,482,3671,13448,26896],[(1024,1295),(1024,3239),(1024,142724),(1024,178306),(1024,268588),(1024,269710),(1024,276482),(1024,396428)]),([6,31,482,3671,19319,26896],[(1024,1295),(1024,3239),(1024,142724),(1024,178306),(1024,268588),(1024,275458),(1024,276482),(1024,396428)]),([6,31,482,3676,13448,26896],[(1024,1295),(1024,134542),(1024,142498),(1024,165004),(1024,268588),(1024,276482)]),([6,31,482,3676,26896,32152],[(1024,1294),(1024,134542),(1024,165004),(1024,273410),(1024,406660)])]
def b105 : List Row := [([6,31,482,3679,3908,13448,26896],[(1024,145570),(1024,268588),(1024,276482)]),([6,31,482,3679,3935,13448,26896],[(1024,268588),(1024,276482)]),([6,31,482,3679,4070,5871,13448],[(1024,145570),(1024,276482),(1024,276546)]),([6,31,482,3679,4070,13448,26896],[(1024,145570),(1024,178306),(1024,276482),(1024,276546)]),([6,31,482,3679,4070,13448,26911],[(1024,276482),(1024,276546)]),([6,31,482,3679,4070,13448,27122],[(1024,145570),(1024,145796),(1024,178306),(1024,178311)]),([6,31,482,3679,4070,19319,26896],[(1024,145570),(1024,178306),(1024,276482),(1024,276546)]),([6,31,482,3679,4095,5871,13448],[(1024,275458),(1024,276482)]),([6,31,482,3679,4095,13448,26896],[(1024,275458),(1024,276482)]),([6,31,482,3679,4095,13448,26911],[(1024,275458),(1024,276482)]),([6,31,482,3679,4095,13448,27122],[(1024,177282),(1024,178306)]),([6,31,482,3679,4095,19319,26896],[(1024,276482)]),([6,31,482,3679,5256,5871],[(1024,1294),(1024,273410),(1024,275458),(1024,406532)])]
def t101 : BT := .nd (blockTree b104) [6,31,482,3677,13448,26896] (blockTree b105)
def b106 : List Row := [([6,31,482,3679,5645,13448],[(1024,132271),(1024,178178),(1024,178306)]),([6,31,482,3679,5645,13448,26896],[(1024,276482)]),([6,31,482,3679,5856,13448],[(1024,1295),(1024,273410),(1024,276482)]),([6,31,482,3679,5871,6127,13448],[(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3679,5871,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3679,5871,13448,13802],[(1024,142504),(1024,142728),(1024,273800),(1024,276482)]),([6,31,482,3679,5871,13448,27122],[(1024,177282),(1024,178306),(1024,276482),(1024,276487),(1024,276610)]),([6,31,482,3679,5871,13448,32285],[(1024,178306),(1024,276770)]),([6,31,482,3679,5871,19319],[(1024,1295),(1024,273410),(1024,276482),(1024,406660)]),([6,31,482,3679,5871,32152],[(1024,1294),(1024,134542),(1024,275458),(1024,404744),(1024,406660)]),([6,31,482,3679,5887,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482),(1024,276487)]),([6,31,482,3679,6127,13448],[]),([6,31,482,3679,6127,13448,26896],[(1024,178306),(1024,273410),(1024,275458),(1024,276482)])]
def b107 : List Row := [([6,31,482,3679,8674,13448,26896],[(1024,178306),(1024,276482)]),([6,31,482,3679,10240,13448],[(1024,1199),(1024,3471),(1024,170287),(1024,309415),(1024,407556),(1024,407563)]),([6,31,482,3679,10256,13448],[(1024,1199),(1024,3471),(1024,170287),(1024,309415),(1024,407556)]),([6,31,482,3679,13448,13704,26896],[(1024,269612),(1024,276482)]),([6,31,482,3679,13448,13802,26896],[(1024,142504),(1024,142728),(1024,178306),(1024,273800),(1024,276482)]),([6,31,482,3679,13448,13802,26911],[(1024,11432),(1024,11656),(1024,178178),(1024,273800),(1024,276482)]),([6,31,482,3679,13448,13802,27122],[(1024,142504),(1024,178306)]),([6,31,482,3679,13448,13823,26896],[(1024,273410),(1024,276482)]),([6,31,482,3679,13448,16366,26896],[(1024,145570),(1024,178306),(1024,276482),(1024,276546),(1024,407556)]),([6,31,482,3679,13448,16383,26896],[(1024,276482),(1024,407556)]),([6,31,482,3679,13448,18965,26896],[(1024,132271),(1024,142504),(1024,142728),(1024,276770)]),([6,31,482,3679,13448,26640],[(1024,132271),(1024,134542),(1024,178306)]),([6,31,482,3679,13448,26640,26896],[(1024,132271),(1024,134542),(1024,276482)])]
def t102 : BT := .nd (blockTree b106) [6,31,482,3679,8448,13448,26896] (blockTree b107)
def t103 : BT := .nd t101 [6,31,482,3679,5256,26896] t102
def b108 : List Row := [([6,31,482,3679,13448,26880],[(1024,1295),(1024,268588),(1024,269710),(1024,276482),(1024,276487)]),([6,31,482,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3679,13448,26896,27122],[(1024,178306),(1024,276482),(1024,276487)]),([6,31,482,3679,13448,26896,28672],[(1024,145575)]),([6,31,482,3679,13448,26896,28697],[(1024,132271),(1024,145570),(1024,145575),(1024,276546)]),([6,31,482,3679,13448,26896,32256],[]),([6,31,482,3679,13448,26896,32285],[(1024,132271),(1024,276770)]),([6,31,482,3679,13448,26896,32287],[(1024,276482)]),([6,31,482,3679,13448,26896,32349],[(1024,132271),(1024,276770),(1024,276775)]),([6,31,482,3679,13448,26896,32351],[(1024,276482)]),([6,31,482,3679,13448,26896,32413],[(1024,132271),(1024,142728),(1024,276482),(1024,276770)]),([6,31,482,3679,13448,26896,32511],[(1024,276482)]),([6,31,482,3679,13448,26896,32541],[(1024,276482),(1024,276770)])]
def b109 : List Row := [([6,31,482,3679,13448,26900],[(1024,1295),(1024,69006),(1024,178242),(1024,268588),(1024,276482)]),([6,31,482,3679,13448,26904],[(1024,1295),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3679,13448,26911],[(1024,1295),(1024,178178),(1024,268588),(1024,276482)]),([6,31,482,3679,13448,26911,32285],[(1024,1199),(1024,276775)]),([6,31,482,3679,13448,26960],[(1024,1295),(1024,134542),(1024,178306),(1024,276482)]),([6,31,482,3679,13448,26962],[(1024,132367),(1024,134542),(1024,178306),(1024,276482),(1024,276610)]),([6,31,482,3679,13448,27024],[(1024,1295),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3679,13448,27122],[(1024,132271),(1024,178178),(1024,178306)]),([6,31,482,3679,13448,27122,28500],[(1024,142498),(1024,276482)]),([6,31,482,3679,13448,27122,32152],[(1024,134542),(1024,178306),(1024,276482)]),([6,31,482,3679,13448,27122,32285],[(1024,132271)]),([6,31,482,3679,13448,27135],[(1024,1199),(1024,178178)]),([6,31,482,3679,13448,27920],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,273800),(1024,276482)])]
def t104 : BT := .nd (blockTree b108) [6,31,482,3679,13448,26898] (blockTree b109)
def b110 : List Row := [([6,31,482,3679,13450,26896],[(1024,134542),(1024,268588),(1024,276487),(1024,276775),(1024,301327)]),([6,31,482,3679,13464,26896],[(1024,1295),(1024,134156),(1024,134444),(1024,134542),(1024,276482),(1024,306308)]),([6,31,482,3679,13471,13802,26896],[(1024,11432),(1024,142504),(1024,178180),(1024,273800),(1024,276775)]),([6,31,482,3679,13512,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,273410),(1024,276482)]),([6,31,482,3679,13514,26896],[(1024,134542),(1024,273800),(1024,276872),(1024,400655)]),([6,31,482,3679,13704,26896],[(1024,1294),(1024,134542),(1024,269324),(1024,269612),(1024,275458),(1024,306440)]),([6,31,482,3679,13802,16076,26896],[(1024,145570),(1024,178244),(1024,276482),(1024,276776)]),([6,31,482,3679,13802,16095,26896],[(1024,142728),(1024,178180),(1024,276776),(1024,276872)]),([6,31,482,3679,13802,19319,26896],[(1024,142728),(1024,178306),(1024,273800),(1024,276482)]),([6,31,482,3679,15496,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,145575),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([6,31,482,3679,15512,26896],[(1024,1295),(1024,134447),(1024,134542),(1024,276482),(1024,406660),(1024,407556)]),([6,31,482,3679,19319,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,31,482,3679,19319,26896,27122],[(1024,177282),(1024,178306),(1024,276482),(1024,276487)])]
def b111 : List Row := [([6,31,482,3679,19319,26911],[(1024,1295),(1024,178178),(1024,268588),(1024,276482)]),([6,31,482,3679,19319,27122],[(1024,132271),(1024,178178),(1024,178306)]),([6,31,482,3679,26896,27122,32152],[(1024,132100),(1024,134542),(1024,268292),(1024,269710)]),([6,31,482,3679,26896,27511],[(1024,1294),(1024,3470),(1024,177282),(1024,268588),(1024,275458)]),([6,31,482,3679,26896,32152],[(1024,1294),(1024,134542),(1024,269710),(1024,273410),(1024,406660)]),([6,31,482,3679,28500,32152],[(1024,1294),(1024,134539),(1024,134542),(1024,268292),(1024,268456),(1024,269710),(1024,406660)]),([6,31,482,3780,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,3780,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3780,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,31,482,3780,13448,27024],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,3780,13448,27122],[(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,3780,13802,26896],[(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,268588)]),([6,31,482,3780,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)])]
def t105 : BT := .nd (blockTree b110) [6,31,482,3679,19319,26896,32285] (blockTree b111)
def t106 : BT := .nd t104 [6,31,482,3679,13448,27928] t105
def t107 : BT := .nd t103 [6,31,482,3679,13448,26640,32285] t106
def t108 : BT := .nd t100 [6,31,482,3668,4070,13448,26896] t107
def b112 : List Row := [([6,31,482,3782,13448,26896],[(1024,66831),(1024,134542),(1024,145796),(1024,268588),(1024,276482),(1024,276546),(1024,396431)]),([6,31,482,3788,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,31,482,3807,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,31,482,3908,5871,13448],[(1024,1292),(1024,77063),(1024,165007),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,3908,13448,26896],[(1024,1292),(1024,134542),(1024,165007),(1024,268364),(1024,268588),(1024,306439)]),([6,31,482,3908,13448,26911],[(1024,1292),(1024,268450),(1024,268588),(1024,306439)]),([6,31,482,3908,13704,26896],[(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,268292),(1024,275458)]),([6,31,482,3908,19319,26896],[(1024,1292),(1024,165007),(1024,268364),(1024,268588),(1024,306439)]),([6,31,482,3908,26896,32152],[(1024,1292),(1024,134542),(1024,165006),(1024,268292),(1024,273410),(1024,406660)]),([6,31,482,3910,13448,26896],[(1024,66828),(1024,134542),(1024,263244),(1024,263468),(1024,268588),(1024,306439),(1024,396431)]),([6,31,482,3910,13448,26911],[(1024,66828),(1024,263183),(1024,268588),(1024,306439)]),([6,31,482,3924,13448,26896],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,3935,13448,26896],[(1024,1292),(1024,134542),(1024,263180),(1024,263468),(1024,268588),(1024,306439)])]
def b113 : List Row := [([6,31,482,4036,26896,32152],[(1024,1292),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]),([6,31,482,4070,13448,16095,26896],[(1024,178306),(1024,276546)]),([6,31,482,4070,13448,26896,29088],[(1024,178306),(1024,276482)]),([6,31,482,4070,13512,26896],[(1024,66828),(1024,134542),(1024,145570),(1024,165007),(1024,273410),(1024,273474)]),([6,31,482,4070,28500,32152],[(1024,134311),(1024,165006),(1024,268292),(1024,268456),(1024,301323)]),([6,31,482,4095,13448,16076,26896],[(1024,276482)]),([6,31,482,4095,13448,16095,26896],[(1024,276482)]),([6,31,482,4095,13448,26896,29088],[(1024,275458),(1024,276482)]),([6,31,482,4095,13448,26896,29115],[(1024,275458),(1024,276482)]),([6,31,482,4256,13448,26896],[(1024,1292),(1024,263180),(1024,263468),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,4256,13448,26911],[(1024,1292),(1024,263180),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,4267,5871,13448],[(1024,1292),(1024,165004),(1024,268588),(1024,306439)]),([6,31,482,4267,13448,26896],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)])]
def t109 : BT := .nd (blockTree b112) [6,31,482,4036,13448,26896] (blockTree b113)
def b114 : List Row := [([6,31,482,4267,13448,31163],[(1024,1292),(1024,165004),(1024,170284),(1024,268364),(1024,268588),(1024,306439)]),([6,31,482,4267,13448,32152],[(1024,1292),(1024,165004),(1024,170116),(1024,268292),(1024,268456),(1024,268587),(1024,268588),(1024,306439)]),([6,31,482,4267,19319,26896],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,4267,26896,32152],[(1024,1292),(1024,134540),(1024,165004),(1024,170116),(1024,268292),(1024,273410),(1024,404612)]),([6,31,482,4267,28500,32152],[(1024,1291),(1024,3335),(1024,134539),(1024,165003),(1024,268292),(1024,268587),(1024,272386)]),([6,31,482,4267,32152],[(1024,170116),(1024,268292),(1024,268456),(1024,268587),(1024,403588)]),([6,31,482,4287,13448,26896],[(1024,1292),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,5256,5871,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,5256,5871,29115],[(1024,1294),(1024,144546),(1024,165006),(1024,170286),(1024,275458),(1024,306439)]),([6,31,482,5256,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,5256,26896,29115],[(1024,1294),(1024,134542),(1024,165006),(1024,177282),(1024,273410),(1024,275458),(1024,406532),(1024,406660)]),([6,31,482,5645,13448,29115],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,5856,13448,28500],[(1024,1292),(1024,263180),(1024,263335),(1024,268588),(1024,273410),(1024,306439)])]
def b115 : List Row := [([6,31,482,5856,13448,29115],[(1024,1295),(1024,14498),(1024,14594),(1024,263183),(1024,276482),(1024,306439)]),([6,31,482,5871,11844,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482),(1024,407556)]),([6,31,482,5871,13448,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,5871,13448,28511],[(1024,1292),(1024,268588),(1024,273410),(1024,306434),(1024,306439)]),([6,31,482,5871,13448,29088],[(1024,1295),(1024,165007),(1024,275458),(1024,276482),(1024,306439)]),([6,31,482,5871,13448,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482),(1024,306439)]),([6,31,482,5871,13448,29119],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482),(1024,306439)]),([6,31,482,5871,13448,31163],[(1024,1292),(1024,142498),(1024,165004),(1024,170284),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,5871,19319,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,5871,19319,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,276482),(1024,306439),(1024,406660)]),([6,31,482,5871,28500,32152],[(1024,1292),(1024,134311),(1024,134540),(1024,165004),(1024,268292),(1024,268588),(1024,273410),(1024,306439),(1024,404612)]),([6,31,482,5871,29115,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]),([6,31,482,5887,13448,28500],[(1024,1292),(1024,77063),(1024,268588),(1024,273410),(1024,306439)])]
def t110 : BT := .nd (blockTree b114) [6,31,482,5856,13448,28511] (blockTree b115)
def t111 : BT := .nd t109 [6,31,482,4267,13448,26911] t110
def b116 : List Row := [([6,31,482,6127,13448,29115],[(1024,142498),(1024,144546),(1024,145570),(1024,165007)]),([6,31,482,8192,13448,31163],[(1024,1196),(1024,164876),(1024,170060),(1024,170284),(1024,404484)]),([6,31,482,8192,28500,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,268292)]),([6,31,482,9216,28500,32152],[(1024,1292),(1024,134311),(1024,165004),(1024,268292)]),([6,31,482,9536,13448,26896],[(1024,132268),(1024,134540),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,10240,11844,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,309415),(1024,407556)]),([6,31,482,10240,13448,29115],[(1024,1199),(1024,164879),(1024,170063),(1024,170287),(1024,407556)]),([6,31,482,11844,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,31,482,11844,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482),(1024,407556)]),([6,31,482,11844,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,407556),(1024,407684)]),([6,31,482,11844,13448,32152],[(1024,1295),(1024,134543),(1024,165007),(1024,407556),(1024,407684)]),([6,31,482,11844,19319,26896],[(1024,1295),(1024,3471),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,482,11844,26896,32152],[(1024,1295),(1024,134543),(1024,165007),(1024,273410),(1024,407684)])]
def b117 : List Row := [([6,31,482,11852,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482),(1024,407620)]),([6,31,482,11860,13448,26896],[(1024,1295),(1024,142498),(1024,165004),(1024,268588),(1024,269711),(1024,276482),(1024,407556),(1024,407816)]),([6,31,482,11871,13448,26896],[(1024,1295),(1024,134543),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,31,482,11972,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,31,482,11972,13448,27122],[(1024,132271),(1024,134543),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,407556),(1024,407684)]),([6,31,482,12100,13448,26896],[(1024,1292),(1024,134543),(1024,165007),(1024,268364),(1024,268588),(1024,306439),(1024,407556)]),([6,31,482,12424,26896,30139],[(1024,1195),(1024,164875),(1024,170059),(1024,170283),(1024,403460)]),([6,31,482,12714,13448,26896],[(1024,11522),(1024,142498),(1024,165004),(1024,169986),(1024,169988),(1024,269710),(1024,273703)]),([6,31,482,13448,13802,26896,29088],[(1024,142504),(1024,142728),(1024,178306),(1024,276482)]),([6,31,482,13448,13823,26896,29115],[(1024,276482)]),([6,31,482,13448,14063,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,16076,27920],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482),(1024,309415)]),([6,31,482,13448,18704,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)])]
def t112 : BT := .nd (blockTree b116) [6,31,482,11852,13448,26896] (blockTree b117)
def b118 : List Row := [([6,31,482,13448,20308,26896],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,20923,26896],[(1024,1295),(1024,134543),(1024,165007),(1024,178306),(1024,273410),(1024,276482),(1024,407556),(1024,407684)]),([6,31,482,13448,24848,31163],[(1024,1196),(1024,164876),(1024,170060),(1024,170284),(1024,404484)]),([6,31,482,13448,26640,28244],[(1024,142498),(1024,165004)]),([6,31,482,13448,26640,29115],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306)]),([6,31,482,13448,26880,28484],[(1024,1292),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,26880,28500],[(1024,1292),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,26880,29115],[(1024,1295),(1024,263183),(1024,269710),(1024,273410),(1024,276482)]),([6,31,482,13448,26896,27122,28511],[(1024,268292),(1024,268300),(1024,268588)]),([6,31,482,13448,26896,27122,29088],[(1024,178306),(1024,276482),(1024,276487)]),([6,31,482,13448,26896,27984],[(1024,1292),(1024,142498),(1024,165004),(1024,273410)]),([6,31,482,13448,26896,28244],[(1024,77058),(1024,142498),(1024,165004),(1024,268588)]),([6,31,482,13448,26896,28480],[(1024,1292),(1024,268588),(1024,273410),(1024,306439)])]
def b119 : List Row := [([6,31,482,13448,26896,28496],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,26896,28502],[(1024,66828),(1024,263468),(1024,268588),(1024,273474),(1024,306439),(1024,396428)]),([6,31,482,13448,26896,28508],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,26896,28511],[(1024,1292),(1024,263180),(1024,263468),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,26896,28628],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,26896,28859],[(1024,1292),(1024,134542),(1024,165007),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,26896,28987],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,31,482,13448,26896,29088],[(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,31,482,13448,26896,29088,32285],[(1024,132271),(1024,276770)]),([6,31,482,13448,26896,29099],[(1024,1295),(1024,142498),(1024,165004),(1024,269710),(1024,273410),(1024,276482)]),([6,31,482,13448,26896,29107],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,269710),(1024,273410),(1024,276482)]),([6,31,482,13448,26896,29113],[(1024,66831),(1024,134542),(1024,145796),(1024,273474),(1024,276482),(1024,276546),(1024,396431)])]
def t113 : BT := .nd (blockTree b118) [6,31,482,13448,26896,28484] (blockTree b119)
def t114 : BT := .nd t112 [6,31,482,13448,20053,26896] t113
def t115 : BT := .nd t111 [6,31,482,5887,13448,29115] t114
def b120 : List Row := [([6,31,482,13448,26896,29115,32256],[]),([6,31,482,13448,26896,29119],[(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,31,482,13448,26896,31152],[(1024,1292),(1024,170284),(1024,269708),(1024,273410)]),([6,31,482,13448,26896,31163],[(1024,1292),(1024,134540),(1024,165004),(1024,170284),(1024,175234),(1024,273410)]),([6,31,482,13448,26896,31167],[(1024,1292),(1024,134540),(1024,165004),(1024,170284),(1024,175234),(1024,273410)]),([6,31,482,13448,26896,31679],[(1024,1292),(1024,134540),(1024,165004),(1024,175234),(1024,273410)]),([6,31,482,13448,26898,28500],[(1024,132263),(1024,263335),(1024,268588),(1024,273703),(1024,301324),(1024,306439),(1024,396428)]),([6,31,482,13448,26898,28502],[(1024,132364),(1024,263308),(1024,268588),(1024,273538),(1024,306439)]),([6,31,482,13448,26898,29115],[(1024,132367),(1024,134542),(1024,178306),(1024,263311),(1024,273538),(1024,276482),(1024,276551),(1024,276610)]),([6,31,482,13448,26900,28500],[(1024,1292),(1024,164940),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,26900,29115],[(1024,1295),(1024,134542),(1024,164940),(1024,178306),(1024,273410),(1024,276482)]),([6,31,482,13448,26904,28500],[(1024,1292),(1024,134311),(1024,165004),(1024,268588),(1024,306439)]),([6,31,482,13448,26904,28508],[(1024,1292),(1024,165004),(1024,268588),(1024,306439)])]
def b121 : List Row := [([6,31,482,13448,26907,29115],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,273410),(1024,276482)]),([6,31,482,13448,26911,27122,28500],[(1024,132263),(1024,137604),(1024,268588)]),([6,31,482,13448,26911,28500],[(1024,1292),(1024,263180),(1024,263335),(1024,268588),(1024,306439)]),([6,31,482,13448,26911,28511],[(1024,1292),(1024,263180),(1024,268588),(1024,306439)]),([6,31,482,13448,26911,29088],[(1024,1295),(1024,178178),(1024,263183),(1024,273410),(1024,276482)]),([6,31,482,13448,26911,29115],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,273410),(1024,276482)]),([6,31,482,13448,26911,29119],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,273410),(1024,276482)]),([6,31,482,13448,26911,31163],[(1024,1292),(1024,11522),(1024,170060),(1024,170284),(1024,175106),(1024,263180),(1024,273410)]),([6,31,482,13448,26911,31167],[(1024,1292),(1024,11522),(1024,170284),(1024,175106),(1024,263180),(1024,273410)]),([6,31,482,13448,26960,29115],[(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,276482)]),([6,31,482,13448,27024,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,269479),(1024,306439)]),([6,31,482,13448,27024,28628],[(1024,1292),(1024,165004),(1024,268588),(1024,306439)]),([6,31,482,13448,27024,29115],[(1024,1295),(1024,165007),(1024,178306),(1024,273410),(1024,276482)])]
def t116 : BT := .nd (blockTree b120) [6,31,482,13448,26904,29115] (blockTree b121)
def b122 : List Row := [([6,31,482,13448,27122,29088],[(1024,132271),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,13448,27122,29115],[(1024,132271),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,13448,27122,29119],[(1024,132271),(1024,165007),(1024,178178),(1024,178306)]),([6,31,482,13448,27122,31163],[(1024,132268),(1024,165004),(1024,170284),(1024,175106),(1024,175234)]),([6,31,482,13448,27135,29115],[(1024,1199),(1024,14498),(1024,164879),(1024,178178)]),([6,31,482,13448,27920,28500],[(1024,1292),(1024,165004),(1024,268587),(1024,268588),(1024,272386),(1024,306439)]),([6,31,482,13448,27920,29115],[(1024,1295),(1024,134542),(1024,142498),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,31,482,13448,28500,31163],[(1024,1292),(1024,165004),(1024,170284),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13448,28500,32152],[(1024,1292),(1024,134311),(1024,165004),(1024,268292),(1024,268456),(1024,268587),(1024,268588),(1024,306439)]),([6,31,482,13448,28500,32159],[(1024,1292),(1024,268450),(1024,268456),(1024,268587),(1024,268588),(1024,306439),(1024,396364)]),([6,31,482,13448,28511,32152],[(1024,1292),(1024,263180),(1024,263468),(1024,268456),(1024,268588),(1024,306439)]),([6,31,482,13448,28511,32159],[(1024,1292),(1024,263180),(1024,268456),(1024,268588),(1024,306439)]),([6,31,482,13450,26896,28500],[(1024,268588),(1024,273703),(1024,301324),(1024,306439),(1024,396428)])]
def b123 : List Row := [([6,31,482,13452,26896,28500],[(1024,1292),(1024,68775),(1024,164939),(1024,268588)]),([6,31,482,13452,26896,29115],[(1024,1295),(1024,68775),(1024,164939),(1024,170052)]),([6,31,482,13464,26896,28500],[(1024,1292),(1024,134311),(1024,134444),(1024,165006),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13464,26896,29115],[(1024,1295),(1024,134220),(1024,134444),(1024,134542),(1024,165006),(1024,306308)]),([6,31,482,13468,26896,28500],[(1024,1292),(1024,68775),(1024,164939),(1024,268588)]),([6,31,482,13471,13802,26896,29115],[(1024,14504),(1024,169988),(1024,178180),(1024,276775)]),([6,31,482,13471,28500,32152],[(1024,1292),(1024,134311),(1024,268292),(1024,268363),(1024,268588),(1024,396427)]),([6,31,482,13512,26896,28500],[(1024,1292),(1024,142498),(1024,165004),(1024,273410),(1024,273474)]),([6,31,482,13512,26896,29115],[(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,31,482,13704,26896,28500],[(1024,1294),(1024,165004),(1024,269479),(1024,273410),(1024,275458)]),([6,31,482,13704,26896,29115],[(1024,1294),(1024,134542),(1024,165007),(1024,269388),(1024,269612),(1024,269710),(1024,306440)]),([6,31,482,13768,26896,28500],[(1024,1294),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,13802,28500,32152],[(1024,165004),(1024,268292),(1024,268456),(1024,269479),(1024,400651)])]
def t117 : BT := .nd (blockTree b122) [6,31,482,13450,26896,29115] (blockTree b123)
def t118 : BT := .nd t116 [6,31,482,13448,27058,29115] t117
def b124 : List Row := [([6,31,482,15496,26896,29115],[(1024,1295),(1024,134542),(1024,165007),(1024,170287),(1024,178306),(1024,276482)]),([6,31,482,16076,28500,32152],[(1024,1295),(1024,69003),(1024,134539),(1024,134543),(1024,165007),(1024,268456),(1024,268587),(1024,268591),(1024,276482),(1024,276775),(1024,276872),(1024,309511),(1024,407684)]),([6,31,482,18704,19319,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,306439)]),([6,31,482,19319,20308,26896],[(1024,1292),(1024,165004),(1024,268588),(1024,306439)]),([6,31,482,19319,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,306439)]),([6,31,482,19319,26896,28511],[(1024,1292),(1024,263180),(1024,263468),(1024,268588),(1024,306439)]),([6,31,482,19319,26896,29088],[(1024,1295),(1024,165007),(1024,178306),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,19319,26896,29115],[(1024,1295),(1024,165007),(1024,178306),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,19319,26896,29119],[(1024,1295),(1024,165007),(1024,178306),(1024,273410),(1024,275458),(1024,276482)]),([6,31,482,19319,26896,31163],[(1024,1292),(1024,165004),(1024,170284),(1024,175234),(1024,273410)]),([6,31,482,19319,26911,28500],[(1024,1292),(1024,263180),(1024,263335),(1024,268588),(1024,306439)]),([6,31,482,19319,26911,28511],[(1024,1292),(1024,263180),(1024,268588),(1024,306439)]),([6,31,482,19319,26911,29115],[(1024,1295),(1024,178178),(1024,263183),(1024,273410),(1024,276482)])]
def b125 : List Row := [([6,31,482,19319,28500,32152],[(1024,1292),(1024,165004),(1024,268292),(1024,268456),(1024,268587),(1024,268588),(1024,273410),(1024,306439)]),([6,31,482,24848,29115,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([6,31,482,26896,27511,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,306439)]),([6,31,482,26896,27511,29115],[(1024,1294),(1024,3470),(1024,165006),(1024,177282),(1024,273410),(1024,275458)]),([6,31,482,26896,28500,32152],[(1024,1292),(1024,134311),(1024,165004),(1024,268292),(1024,273410)]),([6,31,482,26896,28511,32152],[(1024,1292),(1024,268292),(1024,273410)]),([6,31,482,26896,29088,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,269708),(1024,269710),(1024,406660)]),([6,31,482,26896,29115,30104],[(1024,1294),(1024,134220),(1024,134444),(1024,134542),(1024,165006),(1024,306308)]),([6,31,482,26896,29115,32152],[(1024,1294),(1024,134540),(1024,134542),(1024,165006),(1024,406660)]),([6,31,482,26896,29119,32152],[(1024,1294),(1024,134540),(1024,134542),(1024,165006),(1024,406660)]),([6,31,482,26896,31163,32152],[(1024,1292),(1024,134540),(1024,165004),(1024,404612)]),([6,31,482,26911,28500,32152],[(1024,1292),(1024,134311),(1024,170116),(1024,268292),(1024,273410)]),([6,31,482,27122,28500,32152],[(1024,165004),(1024,268292),(1024,268456),(1024,269479)])]
def t119 : BT := .nd (blockTree b124) [6,31,482,19319,27122,29115] (blockTree b125)
def b126 : List Row := [([6,31,482,28500,28500,32152],[(1024,1291),(1024,3335),(1024,165003),(1024,268292),(1024,268587),(1024,272386)]),([6,31,482,28500,28511,32152],[(1024,1291),(1024,3335),(1024,134311),(1024,268292),(1024,268363),(1024,272386)]),([6,31,482,28500,28662,32152],[(1024,165003),(1024,268292),(1024,268456),(1024,269479),(1024,301323)]),([6,31,482,28500,29115,32152],[(1024,1294),(1024,134311),(1024,134539),(1024,134542),(1024,165006),(1024,268292),(1024,275458),(1024,406660)]),([6,31,482,28500,32152],[(1024,134311),(1024,268292),(1024,268456),(1024,268587),(1024,272386)]),([6,31,482,28500,32152,32152],[(1024,1291),(1024,134311),(1024,165003),(1024,170116),(1024,268456),(1024,268587),(1024,272386)]),([6,31,482,28500,32152,32159],[(1024,1291),(1024,134311),(1024,170116),(1024,268292),(1024,268456),(1024,268587),(1024,272386),(1024,396427)]),([6,31,482,28500,32152,32250],[(1024,134311),(1024,165003),(1024,268292),(1024,268456),(1024,400651)]),([6,31,482,28500,32152,32285],[(1024,1291),(1024,134311),(1024,165003),(1024,268292),(1024,268456),(1024,301323),(1024,400651)]),([6,31,482,28500,32152,32732],[(1024,1291),(1024,134311),(1024,134539),(1024,165003),(1024,268292),(1024,268456),(1024,268587)]),([6,31,482,28500,32152,32736],[(1024,1291),(1024,134311),(1024,165003),(1024,268292),(1024,268456),(1024,396427)]),([6,31,486,3652,5871,13448],[(1024,1295),(1024,66727),(1024,164935),(1024,170050)]),([6,31,486,3652,13448,26896],[(1024,1295),(1024,66727),(1024,134542),(1024,164935),(1024,170050)])]
def b127 : List Row := [([6,31,486,3652,13448,26911],[(1024,1295),(1024,14594),(1024,66727),(1024,71980),(1024,170050),(1024,263183)]),([6,31,486,3652,13448,27122],[(1024,66727),(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,31,486,3652,13448,27126],[(1024,66727),(1024,132271),(1024,164935),(1024,170050),(1024,178306)]),([6,31,486,3652,13452,26896],[(1024,1295),(1024,66564),(1024,71684),(1024,134542),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,486,3652,19319,26896],[(1024,1295),(1024,66727),(1024,164935),(1024,170050)]),([6,31,486,3652,26896,32152],[(1024,1294),(1024,66727),(1024,134542),(1024,164935),(1024,170050),(1024,406660)]),([6,31,486,13448,26896,28500],[(1024,1292),(1024,66727),(1024,164935),(1024,268588)]),([6,31,486,13448,26896,29115],[(1024,1295),(1024,66727),(1024,164935),(1024,170050)]),([6,31,490,511,3652,13448,26896],[(1024,178178),(1024,276482)]),([6,31,490,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([6,31,490,3652,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([6,31,490,3652,13448,26904],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([6,31,490,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,269710),(1024,276482)])]
def t120 : BT := .nd (blockTree b126) [6,31,486,3652,13448,26900] (blockTree b127)
def t121 : BT := .nd t119 [6,31,482,27920,28500,32152] t120
def t122 : BT := .nd t118 [6,31,482,15496,26896,28500] t121
def t123 : BT := .nd t115 [6,31,482,13448,26896,29115] t122
def t124 : BT := .nd t108 [6,31,482,3780,26896,32152] t123
def t125 : BT := .nd t93 [6,31,482,3652,13448,28048] t124
def t126 : BT := .nd t62 [6,31,66,482,3679,13448,27122] t125
def b128 : List Row := [([6,31,490,3652,13448,27130],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,31,490,3652,13471,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([6,31,490,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,31,490,3652,26896,32152],[(1024,1294),(1024,165006),(1024,269710),(1024,273410),(1024,406792)]),([6,31,490,3660,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([6,31,490,3679,13448,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([6,31,490,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,490,13448,26896,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,269710),(1024,273410),(1024,276482)]),([6,31,494,3652,13448,26896],[(1024,1295),(1024,66727),(1024,71842),(1024,164935),(1024,170050),(1024,269710)]),([6,31,498,3652,4070,13448,26896],[(1024,132396),(1024,178306),(1024,276482)]),([6,31,498,3652,5871,13448],[(1024,1295),(1024,76930),(1024,132396),(1024,145410),(1024,306306),(1024,406658)]),([6,31,498,3652,13448,13802,26896],[(1024,132396),(1024,142728),(1024,145479),(1024,178306),(1024,276482)]),([6,31,498,3652,13448,26896],[(1024,1295),(1024,132111),(1024,132172),(1024,132396),(1024,268588),(1024,269710),(1024,306306)]),([6,31,498,3652,13448,26896,27122],[(1024,132396)])]
def b129 : List Row := [([6,31,498,3652,13464,26896],[(1024,1295),(1024,132100),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]),([6,31,498,3652,19319,26896],[(1024,1295),(1024,132111),(1024,132172),(1024,132396),(1024,268588),(1024,306306)]),([6,31,498,3652,26896,32152],[(1024,1294),(1024,132100),(1024,144386),(1024,269710),(1024,273410),(1024,406792)]),([6,31,498,3668,13448,26896],[(1024,1295),(1024,132263),(1024,132396),(1024,137292),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]),([6,31,498,3679,13448,26896],[(1024,1295),(1024,132108),(1024,132396),(1024,269710),(1024,276482),(1024,306306)]),([6,31,498,13448,26896,28500],[(1024,1292),(1024,132263),(1024,132396),(1024,137292),(1024,142338),(1024,268588),(1024,273410),(1024,306439)]),([6,31,498,13448,26896,29115],[(1024,1295),(1024,132111),(1024,132172),(1024,132396),(1024,132494),(1024,269710),(1024,306306)]),([6,31,502,3652,13448,26896],[(1024,1295),(1024,66727),(1024,71842),(1024,132396),(1024,164935),(1024,170050),(1024,269710),(1024,306306)]),([6,31,502,13448,26896,28500],[(1024,1292),(1024,66727),(1024,164935),(1024,268588)]),([6,31,506,3652,13448,26896],[(1024,1295),(1024,132111),(1024,132172),(1024,132396),(1024,134542),(1024,268588),(1024,306306)]),([6,31,506,3652,26896,32152],[(1024,1294),(1024,132494),(1024,134542),(1024,144386),(1024,273410),(1024,406660)]),([6,31,511,1088,13448,13802,26896],[(1024,142728),(1024,175106),(1024,273410)]),([6,31,511,1506,3652,13448,26896],[(1024,178178),(1024,273410),(1024,275458),(1024,276482)])]
def t127 : BT := .nd (blockTree b128) [6,31,498,3652,13448,26896,32285] (blockTree b129)
def b130 : List Row := [([6,31,511,3652,4070,13448,27122],[(1024,145796),(1024,178178),(1024,178306)]),([6,31,511,3652,5645,13448,26896],[]),([6,31,511,3652,5871,13448,13802],[(1024,142728),(1024,276482)]),([6,31,511,3652,5871,13448,27122],[(1024,306306)]),([6,31,511,3652,5871,13448,32285],[(1024,1295)]),([6,31,511,3652,8674,13448,26896],[(1024,178178),(1024,276482)]),([6,31,511,3652,13448,13802,26896],[(1024,142728),(1024,178178),(1024,276482)]),([6,31,511,3652,13448,13802,26911],[(1024,11656),(1024,71980),(1024,178178),(1024,276482)]),([6,31,511,3652,13448,13802,27122],[(1024,178178),(1024,178306)]),([6,31,511,3652,13448,13802,27135],[(1024,178178)]),([6,31,511,3652,13448,18965,26896],[(1024,1191),(1024,1199),(1024,142728)]),([6,31,511,3652,13448,26640,32285],[(1024,1199),(1024,145570)]),([6,31,511,3652,13448,26896,27122],[(1024,132396)])]
def b131 : List Row := [([6,31,511,3652,13448,26896,32413],[(1024,1199),(1024,142728)]),([6,31,511,3652,13448,26896,32541],[]),([6,31,511,3652,13448,26911,32285],[(1024,1199),(1024,1295),(1024,1324)]),([6,31,511,3652,13448,27122,28500],[]),([6,31,511,3652,13448,27122,32152],[]),([6,31,511,3652,13448,27122,32285],[(1024,1199),(1024,132271)]),([6,31,511,3652,13448,27135,32285],[(1024,1199),(1024,1324)]),([6,31,511,3652,13450,26896],[(1024,132494),(1024,145703),(1024,268588),(1024,276775),(1024,301327)]),([6,31,511,3652,13471,13802,26896],[(1024,178178),(1024,276482),(1024,276775)]),([6,31,511,3652,13802,16076,26896],[(1024,178178)]),([6,31,511,3652,13802,19319,26896],[(1024,142728),(1024,178178),(1024,276482)]),([6,31,511,3652,19319,26896,27122],[(1024,132396)]),([6,31,511,3652,19319,26896,32285],[(1024,1199),(1024,1295)])]
def t128 : BT := .nd (blockTree b130) [6,31,511,3652,13448,26896,32285] (blockTree b131)
def t129 : BT := .nd t127 [6,31,511,2530,3652,13448,26896] t128
def b132 : List Row := [([6,31,511,3679,13448,13802,26896],[(1024,11656),(1024,142728),(1024,178178),(1024,273800),(1024,276482)]),([6,31,511,3679,13448,26896,27122],[(1024,132396)]),([6,31,511,3679,13448,26896,32285],[(1024,1199),(1024,1295),(1024,276770)]),([6,31,511,13448,13802,26896,29115],[(1024,169986),(1024,178178),(1024,276482)]),([6,31,511,13448,26896,27122,28500],[(1024,132263),(1024,268292),(1024,268588)]),([6,31,511,13448,26896,27122,29115],[(1024,132396)]),([6,31,511,13448,26896,29115,32285],[(1024,1199),(1024,1295)]),([6,31,615,3652,26896,32285],[(1024,1292),(1024,1294),(1024,134542),(1024,165006)]),([6,31,1088,1506,13448,26896],[(1024,1292),(1024,134540),(1024,165004),(1024,175234),(1024,273410)]),([6,31,1088,13448,13802,27122],[(1024,132268),(1024,165004),(1024,175106),(1024,175108),(1024,175234)]),([6,31,1088,13448,26896,32285],[(1024,1292),(1024,142498),(1024,165004),(1024,273410)]),([6,31,1506,1535,3652,13448,26896],[(1024,178178),(1024,273410),(1024,275458),(1024,276482)]),([6,31,1506,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)])]
def b133 : List Row := [([6,31,1506,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,273410),(1024,276482)]),([6,31,1506,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,178178),(1024,178306)]),([6,31,1506,3652,13448,27920],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([6,31,1506,3652,13448,28146],[(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,178178),(1024,178306)]),([6,31,1506,3652,16076,26896],[(1024,1295),(1024,134444),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,407556)]),([6,31,1506,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,275458),(1024,276482)]),([6,31,1506,3652,26896,32152],[(1024,1294),(1024,134444),(1024,134540),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]),([6,31,1506,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,273800),(1024,276482)]),([6,31,1506,13448,16076,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482),(1024,309415)]),([6,31,1506,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,31,1506,13448,26896,29115],[(1024,1295),(1024,134542),(1024,142498),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,31,1510,3652,13448,26896],[(1024,1295),(1024,66727),(1024,134542),(1024,164935),(1024,170050),(1024,273410),(1024,276482)]),([6,31,1514,3652,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,273410),(1024,275458),(1024,276482)])]
def t130 : BT := .nd (blockTree b132) [6,31,1506,3652,13448,26896] (blockTree b133)
def b134 : List Row := [([6,31,1604,5871,13448,32285],[(1024,1196),(1024,1292),(1024,132268),(1024,165004),(1024,273410)]),([6,31,1604,13448,26896,32285],[(1024,1196),(1024,1292),(1024,142498),(1024,165004),(1024,273410)]),([6,31,2048,3652,8674,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,178178),(1024,407556)]),([6,31,2112,4070,13448,27122],[(1024,132271),(1024,165007),(1024,178306)]),([6,31,2530,2559,3652,13448,26896],[(1024,178178),(1024,276482)]),([6,31,2530,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482),(1024,309415)]),([6,31,2530,3652,8192,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]),([6,31,2530,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,309511),(1024,407556)]),([6,31,2530,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,276482),(1024,309511),(1024,407720)]),([6,31,2530,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,309415),(1024,407556)]),([6,31,2530,3652,13448,28500],[(1024,1295),(1024,145570),(1024,165007),(1024,268591),(1024,309415),(1024,309511),(1024,407556)]),([6,31,2530,3652,15496,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([6,31,2530,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,275458),(1024,276482),(1024,309415),(1024,309511)])]
def b135 : List Row := [([6,31,2530,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,145575),(1024,178306),(1024,276482),(1024,309511),(1024,407556)]),([6,31,2530,13448,26896,29115],[(1024,1295),(1024,134542),(1024,165007),(1024,170287),(1024,178306),(1024,276482)]),([6,31,2534,3652,13448,26896],[(1024,1295),(1024,66727),(1024,134542),(1024,164935),(1024,170050),(1024,309511),(1024,407556)]),([6,31,2534,3652,13448,26911],[(1024,1295),(1024,14594),(1024,66727),(1024,66823),(1024,170050),(1024,263183),(1024,407720)]),([6,31,2546,3652,13448,26896],[(1024,1295),(1024,132111),(1024,132494),(1024,269710),(1024,406658)]),([6,31,2546,3679,13448,26896],[(1024,1295),(1024,132494),(1024,269710),(1024,276482),(1024,406658)]),([6,31,3554,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,309511),(1024,407556)]),([6,31,3554,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([6,31,3588,13448,26896,32349],[(1024,1191),(1024,164871),(1024,399364)]),([6,31,3648,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,3679,13448,26640,32285],[(1024,145570)]),([6,31,3652,4070,4095,13448,27122],[(1024,145796),(1024,177282),(1024,178306)]),([6,31,3652,4070,5645,13448],[(1024,132271),(1024,165007),(1024,178178),(1024,178306)])]
def t131 : BT := .nd (blockTree b134) [6,31,2530,3652,26896,32152] (blockTree b135)
def t132 : BT := .nd t130 [6,31,1514,3679,13448,26896] t131
def t133 : BT := .nd t129 [6,31,511,3652,26896,27122,32152] t132
def b136 : List Row := [([6,31,3652,4070,13448,27122],[(1024,132271),(1024,165007),(1024,178178),(1024,178306)]),([6,31,3652,4070,13448,27135],[(1024,1199),(1024,14498),(1024,66727),(1024,164879),(1024,170050),(1024,178178)]),([6,31,3652,4070,13471,13802,26896],[(1024,14504)]),([6,31,3652,4070,13512,26896],[(1024,1295),(1024,66828),(1024,134542),(1024,165007),(1024,273474),(1024,276482)]),([6,31,3652,4070,19319,27122],[(1024,132271),(1024,165007),(1024,178178),(1024,178306)]),([6,31,3652,4095,13448,13802,26896],[(1024,276482)]),([6,31,3652,4095,13448,26896,27122],[(1024,132494)]),([6,31,3652,4095,13448,26896,32285],[(1024,1294),(1024,1295)]),([6,31,3652,5256,5871,32285],[(1024,1198),(1024,1292),(1024,1294),(1024,132270),(1024,165006),(1024,275458)]),([6,31,3652,5256,26896,32285],[(1024,1198),(1024,1292),(1024,1294),(1024,144546),(1024,165006),(1024,275458)]),([6,31,3652,5645,6127,13448],[(1024,132271),(1024,165007),(1024,175234),(1024,177282),(1024,178306)]),([6,31,3652,5645,13448,13802],[(1024,132271),(1024,165007),(1024,175234),(1024,178178),(1024,178180),(1024,178306)]),([6,31,3652,5645,13448,32285],[(1024,1199),(1024,132271),(1024,165007),(1024,178306)])]
def b137 : List Row := [([6,31,3652,5871,8674,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482),(1024,407556)]),([6,31,3652,5871,13448,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,132271),(1024,165007),(1024,276482)]),([6,31,3652,5871,19319,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,132271),(1024,165007),(1024,276482)]),([6,31,3652,5871,32152,32285],[(1024,1292),(1024,1294),(1024,165006),(1024,406660)]),([6,31,3652,5887,13448,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,276482)]),([6,31,3652,6127,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,177282),(1024,178306)]),([6,31,3652,6127,13448,32285],[(1024,132271),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,178306)]),([6,31,3652,8320,13802,26896],[(1024,1295),(1024,165007),(1024,178178),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([6,31,3652,8320,13802,27122],[(1024,3247),(1024,165007),(1024,175108),(1024,178178),(1024,178180),(1024,178306)]),([6,31,3652,8674,8703,13448,26896],[(1024,178178),(1024,276482)]),([6,31,3652,8674,13448,26896],[(1024,1295),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,31,3652,8674,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482),(1024,407556)]),([6,31,3652,8674,13448,27122],[(1024,132271),(1024,165007),(1024,178178),(1024,178306),(1024,407556),(1024,407684)])]
def t134 : BT := .nd (blockTree b136) [6,31,3652,5856,13448,32285] (blockTree b137)
def b138 : List Row := [([6,31,3652,8674,19319,26896],[(1024,1295),(1024,3471),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,31,3652,8682,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407720),(1024,407816)]),([6,31,3652,8682,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482),(1024,407720),(1024,407816)]),([6,31,3652,8690,13448,26896],[(1024,132111),(1024,132172),(1024,132396),(1024,268588),(1024,276482)]),([6,31,3652,9698,13448,26896],[(1024,1295),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482),(1024,407556),(1024,407684)]),([6,31,3652,10240,10722,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,178178),(1024,407556)]),([6,31,3652,10240,13448,32285],[(1024,1199),(1024,164879),(1024,407556)]),([6,31,3652,10722,13448],[(1024,178178),(1024,309415),(1024,407556),(1024,407720)]),([6,31,3652,10722,13448,16076],[(1024,1199),(1024,14498),(1024,164879),(1024,178178),(1024,309415),(1024,407556),(1024,407720)]),([6,31,3652,10722,13448,26896],[(1024,1295),(1024,165007),(1024,178306),(1024,276482),(1024,407556),(1024,407684)]),([6,31,3652,13320,26896,32413],[(1024,1192),(1024,164872),(1024,400388)]),([6,31,3652,13448,13471,26640,32285],[(1024,145570)]),([6,31,3652,13448,13802,13823,27122],[(1024,175234),(1024,178306)])]
def b139 : List Row := [([6,31,3652,13448,13802,27024],[(1024,1295),(1024,165007),(1024,268588),(1024,273410),(1024,276482)]),([6,31,3652,13448,13802,27122],[(1024,132271),(1024,165007),(1024,175234),(1024,178178),(1024,178180),(1024,178306)]),([6,31,3652,13448,13802,27135],[(1024,1199),(1024,164879),(1024,175106),(1024,178178)]),([6,31,3652,13448,13823,26896,27122],[(1024,132396)]),([6,31,3652,13448,13823,26896,32285],[(1024,1292),(1024,1295)]),([6,31,3652,13448,16366,27122],[(1024,14498),(1024,132271),(1024,165007),(1024,178178),(1024,178180),(1024,178306)]),([6,31,3652,13448,18965,27122],[(1024,1199),(1024,3247),(1024,132271),(1024,142498),(1024,145570),(1024,165007),(1024,178306)]),([6,31,3652,13448,24093,26896],[(1024,1199),(1024,1295),(1024,145570),(1024,165007),(1024,268588),(1024,276482)]),([6,31,3652,13448,26640,26655,32285],[(1024,145570)]),([6,31,3652,13448,26640,27122],[(1024,132271),(1024,142498),(1024,144546),(1024,165007),(1024,178306)]),([6,31,3652,13448,26640,32285],[(1024,134542),(1024,142498),(1024,145570),(1024,165007)]),([6,31,3652,13448,26640,32285,32736],[(1024,145570)]),([6,31,3652,13448,26640,32541],[(1024,134542),(1024,142498),(1024,145570),(1024,165007)])]
def t135 : BT := .nd (blockTree b138) [6,31,3652,13448,13802,26896,32256] (blockTree b139)
def t136 : BT := .nd t134 [6,31,3652,8674,13448,32152] t135
def b140 : List Row := [([6,31,3652,13448,26655,26896,32285],[(1024,1295),(1024,145570)]),([6,31,3652,13448,26655,32285],[(1024,14498)]),([6,31,3652,13448,26880,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,276482)]),([6,31,3652,13448,26896,27122,32256],[]),([6,31,3652,13448,26896,30237],[(1024,1199),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,13448,26896,31261],[(1024,1292),(1024,1294),(1024,1295),(1024,142498),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,13448,26896,32256,32285],[(1024,1295)]),([6,31,3652,13448,26896,32269],[(1024,1167),(1024,1292),(1024,1294),(1024,1295),(1024,132396)]),([6,31,3652,13448,26896,32277],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,13448,26896,32281],[(1024,1292),(1024,1294),(1024,1295),(1024,66727),(1024,164935)]),([6,31,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,13448,26898,32285],[(1024,1295),(1024,71951),(1024,132364),(1024,132366),(1024,132367),(1024,145570),(1024,263311),(1024,276610)]),([6,31,3652,13448,26900,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,76962),(1024,164940),(1024,276482)])]
def b141 : List Row := [([6,31,3652,13448,26909,32285],[(1024,1295),(1024,14498),(1024,164879),(1024,276775),(1024,301324),(1024,301327)]),([6,31,3652,13448,26911,32285],[(1024,1292),(1024,1295),(1024,14498),(1024,263183),(1024,276482)]),([6,31,3652,13448,26911,32285,32287],[(1024,1295),(1024,1324),(1024,301314)]),([6,31,3652,13448,26911,32285,32541],[(1024,1295),(1024,14498),(1024,301327)]),([6,31,3652,13448,26960,32285],[(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,13448,27024,32285],[(1024,1292),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,13448,27122,28697],[(1024,1199),(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,31,3652,13448,27122,32285],[(1024,1199),(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,31,3652,13448,27122,32349],[(1024,1199),(1024,132263),(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,31,3652,13448,27122,32413],[(1024,1199),(1024,132264),(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,31,3652,13448,27135,32285],[(1024,1199),(1024,14498),(1024,164879),(1024,178178)]),([6,31,3652,13448,27920,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,142498),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,13450,26896,32285],[(1024,71951),(1024,145796),(1024,276775),(1024,301324),(1024,301326),(1024,301327),(1024,396431)])]
def t137 : BT := .nd (blockTree b140) [6,31,3652,13448,26904,32285] (blockTree b141)
def b142 : List Row := [([6,31,3652,13464,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,134444),(1024,165006)]),([6,31,3652,13471,13802,26896,32285],[(1024,14504),(1024,142504),(1024,301327)]),([6,31,3652,13471,13802,27122],[(1024,3247),(1024,145796),(1024,175108),(1024,178178),(1024,178180),(1024,178251)]),([6,31,3652,13512,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,13704,26896,32285],[(1024,1294),(1024,165007),(1024,269612)]),([6,31,3652,13802,16076,27122],[(1024,132271),(1024,165007),(1024,178178),(1024,178180),(1024,178244),(1024,178251),(1024,178306)]),([6,31,3652,13802,19319,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,178178),(1024,178180),(1024,178306)]),([6,31,3652,15496,26896,32285],[(1024,1199),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,19319,26640,32285],[(1024,142498),(1024,144546),(1024,145570),(1024,165007)]),([6,31,3652,19319,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3652,19319,26911,32285],[(1024,1292),(1024,1295),(1024,14498),(1024,263183),(1024,276482)]),([6,31,3652,19319,27122,32285],[(1024,1199),(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,31,3652,26640,31896,32285],[(1024,134542),(1024,142498),(1024,165006),(1024,406660)])]
def b143 : List Row := [([6,31,3652,26896,31896,32285],[(1024,1294),(1024,134542),(1024,142498),(1024,165006),(1024,406660)]),([6,31,3652,26896,32152,32285],[(1024,1292),(1024,1294),(1024,134542),(1024,165006)]),([6,31,3652,28500,32152,32285],[(1024,1291),(1024,1294),(1024,134539),(1024,134542),(1024,165006)]),([6,31,3654,13448,26896,32285],[(1024,1295),(1024,66828),(1024,66830),(1024,66831),(1024,145796),(1024,276546),(1024,296207),(1024,396431)]),([6,31,3660,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3668,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,142498),(1024,165004),(1024,276482)]),([6,31,3677,13448,26896,32285],[(1024,1295),(1024,142498),(1024,165004),(1024,276775),(1024,301324),(1024,301326),(1024,301327)]),([6,31,3679,4070,13448,13802,26896],[(1024,145570),(1024,276482)]),([6,31,3679,4070,13448,26896,27122],[(1024,178306),(1024,276482),(1024,276610),(1024,276620),(1024,276872)]),([6,31,3679,4070,13448,26896,32285],[(1024,66831),(1024,145570)]),([6,31,3679,4070,13448,27122],[(1024,132271),(1024,145796),(1024,178306),(1024,178311)]),([6,31,3679,4095,13448,13802,26896],[(1024,142504),(1024,276482)]),([6,31,3679,4095,13448,26896,27122],[(1024,132494)])]
def t138 : BT := .nd (blockTree b142) [6,31,3652,26896,27511,32285] (blockTree b143)
def t139 : BT := .nd t137 [6,31,3652,13452,26896,32285] t138
def t140 : BT := .nd t136 [6,31,3652,13448,26653,32285] t139
def t141 : BT := .nd t133 [6,31,3652,4070,13448,26960] t140
def b144 : List Row := [([6,31,3679,5871,13448,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,132271),(1024,276482),(1024,296207)]),([6,31,3679,8674,13448,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,31,3679,13448,13802,26896,27122],[(1024,178306),(1024,276482),(1024,276484)]),([6,31,3679,13448,13802,26896,32285],[(1024,1295),(1024,142504),(1024,400652)]),([6,31,3679,13448,13802,27122],[(1024,132271),(1024,178178),(1024,178180),(1024,178306)]),([6,31,3679,13448,26640,26896,32285],[(1024,1295),(1024,134542)]),([6,31,3679,13448,26640,32285],[(1024,134542)]),([6,31,3679,13448,26896,27122,32285],[(1024,1295),(1024,6415),(1024,132271)]),([6,31,3679,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,276482),(1024,296207)]),([6,31,3679,13448,26896,32285,32285],[(1024,1295),(1024,296207)]),([6,31,3679,13448,26896,32285,32287],[(1024,1295)]),([6,31,3679,13448,26896,32285,32349],[(1024,1295),(1024,296207),(1024,301327),(1024,400551)]),([6,31,3679,13448,26896,32285,32351],[(1024,1295),(1024,400551)])]
def b145 : List Row := [([6,31,3679,13448,26896,32285,32541],[(1024,1295),(1024,296207)]),([6,31,3679,13448,26911,32285],[(1024,1292),(1024,1295),(1024,276482),(1024,301327)]),([6,31,3679,13448,27122,32285],[(1024,1199),(1024,132271),(1024,178306)]),([6,31,3679,19319,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,276482),(1024,296207)]),([6,31,3679,26896,32152,32285],[(1024,1292),(1024,1294),(1024,134542),(1024,296206)]),([6,31,3780,13448,13802,26896],[(1024,1295),(1024,165007),(1024,268588),(1024,273410),(1024,276482)]),([6,31,3780,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,3908,13448,26896,32285],[(1024,1292),(1024,165007),(1024,268588)]),([6,31,4070,13448,16076,27122],[(1024,66727),(1024,68738),(1024,132271),(1024,165007),(1024,178178),(1024,178306)]),([6,31,4070,13448,27122,29115],[(1024,132271),(1024,145570),(1024,165007),(1024,170050),(1024,178306)]),([6,31,4070,13802,16076,26896],[(1024,14498),(1024,14594),(1024,66564),(1024,66828),(1024,145570),(1024,165007),(1024,268588),(1024,273474),(1024,276482),(1024,276775),(1024,276871)]),([6,31,4267,13448,26896,32285],[(1024,1292),(1024,165004),(1024,268588)]),([6,31,5871,13448,28500,32285],[(1024,1292),(1024,165004),(1024,306439)])]
def t142 : BT := .nd (blockTree b144) [6,31,3679,13448,26896,32285,32413] (blockTree b145)
def b146 : List Row := [([6,31,8674,11844,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,31,8674,13448,26896,28500],[(1024,165004),(1024,268588),(1024,273410)]),([6,31,8674,13448,26896,29115],[(1024,1295),(1024,165007),(1024,178306),(1024,273410),(1024,276482),(1024,407556),(1024,407684)]),([6,31,9698,13448,26896,28500],[(1024,165004),(1024,268588),(1024,273410)]),([6,31,11844,13448,26896,32285],[(1024,1199),(1024,1292),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,13448,13802,27122,29115],[(1024,132271),(1024,142498),(1024,165007),(1024,178178),(1024,178180),(1024,178306)]),([6,31,13448,26640,28244,32285],[(1024,142498),(1024,165004)]),([6,31,13448,26640,29115,32285],[(1024,134542),(1024,142498),(1024,145570),(1024,165007)]),([6,31,13448,26896,28244,32285],[(1024,1292),(1024,77058),(1024,142498),(1024,165004)]),([6,31,13448,26896,28500,32285],[(1024,1292),(1024,165004),(1024,268588)]),([6,31,13448,26896,28511,32285],[(1024,1292),(1024,268588),(1024,296204)]),([6,31,13448,26896,29088,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,276482),(1024,296207)]),([6,31,13448,26896,29115,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)])]
def b147 : List Row := [([6,31,13448,26896,31163,32285],[(1024,1196),(1024,1292),(1024,142498),(1024,165004),(1024,273410)]),([6,31,13448,26911,28500,32285],[(1024,1292),(1024,268588),(1024,301324)]),([6,31,13448,26911,28511,32285],[(1024,1292),(1024,263180),(1024,268588)]),([6,31,13448,26911,29115,32285],[(1024,1292),(1024,1295),(1024,14498),(1024,263183),(1024,276482)]),([6,31,13448,27122,29115,32285],[(1024,1199),(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,31,13448,28500,32152,32285],[(1024,1291),(1024,1292),(1024,165004),(1024,268292),(1024,268588)]),([6,31,19319,26896,28500,32285],[(1024,1292),(1024,165004),(1024,268588)]),([6,31,19319,26896,29115,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,31,26896,28500,32152,32285],[(1024,1291),(1024,1292),(1024,134311),(1024,165004),(1024,273410)]),([6,31,26896,29115,32152,32285],[(1024,1292),(1024,1294),(1024,134542),(1024,165006)]),([6,31,28500,32152,32285],[(1024,1291),(1024,268292),(1024,268456),(1024,301323),(1024,400651)]),([6,64,482,511,3679,13448,26896],[]),([6,64,482,1055,13448,26896],[(1024,1292),(1024,11522),(1024,134540),(1024,142498),(1024,165004),(1024,273410)])]
def t143 : BT := .nd (blockTree b146) [6,31,13448,26896,29119,32285] (blockTree b147)
def t144 : BT := .nd t142 [6,31,5871,13448,29115,32285] t143
def b148 : List Row := [([6,66,511,3652,13448,26896],[(1024,134542),(1024,142724),(1024,145796),(1024,396431)]),([6,66,511,3679,13448,26896],[(1024,134542),(1024,142728),(1024,400524)]),([6,66,3652,4095,13448,26896],[(1024,134542),(1024,145796),(1024,396431)]),([6,66,3679,4070,13448,26896],[(1024,134542),(1024,142607),(1024,273551),(1024,276620)]),([6,68,482,511,3679,13448,26896],[]),([6,95,482,511,3652,13448,26896],[(1024,145796),(1024,178178),(1024,273410),(1024,276482)]),([6,95,482,511,3679,13448,26896],[(1024,142728),(1024,178178),(1024,273410),(1024,276482)]),([6,95,482,1024,13448,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,273410)]),([6,95,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,273474),(1024,275458),(1024,276482)]),([6,95,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([6,95,482,3652,13448,26911],[(1024,1295),(1024,14594),(1024,71980),(1024,178178),(1024,263183),(1024,273410),(1024,273474),(1024,276482)]),([6,95,482,3652,13448,26960],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([6,95,482,3652,13448,26975],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,273410),(1024,273474),(1024,276482)])]
def b149 : List Row := [([6,95,482,3652,13512,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([6,95,482,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,275458),(1024,276482)]),([6,95,482,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]),([6,95,482,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,273410),(1024,276482)]),([6,95,482,4070,13448,26896],[(1024,66828),(1024,134542),(1024,145570),(1024,165007),(1024,273410),(1024,273474)]),([6,95,482,13448,26896,28500],[(1024,1292),(1024,165004),(1024,273410),(1024,273474),(1024,273543)]),([6,95,482,13448,26896,29115],[(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,95,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,128,482,511,3679,13448,26896],[]),([6,136,482,511,3652,13471,26896],[]),([6,136,482,511,3679,13448,26896],[]),([6,159,482,511,3652,13448,26896],[(1024,178178),(1024,276482)]),([6,159,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)])]
def t145 : BT := .nd (blockTree b148) [6,95,482,3652,13448,27122] (blockTree b149)
def b150 : List Row := [([6,159,482,3652,13448,26911],[(1024,1295),(1024,14504),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,159,482,3652,13448,27024],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,159,482,3652,13448,27039],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([6,159,482,3652,13448,27122],[(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,159,482,3652,13802,26896],[(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,268588)]),([6,159,482,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,159,482,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]),([6,159,482,3679,13448,26896],[(1024,1295),(1024,134542),(1024,142504),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,159,482,3780,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([6,159,482,3807,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([6,159,482,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,159,482,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([6,159,3652,13448,13802,26896],[(1024,1295),(1024,165007),(1024,268588),(1024,273410),(1024,276482)])]
def b151 : List Row := [([6,223,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([6,256,287,482,3652,13448,26911],[(1024,263172),(1024,263335)]),([6,256,287,482,3679,13448,26896],[(1024,263468)]),([6,256,287,482,3935,13448,26896],[(1024,263468)]),([6,256,482,511,3652,13448,26911],[(1024,268450),(1024,269474)]),([6,256,482,511,3679,13448,26896],[(1024,263468),(1024,269612)]),([6,256,482,3652,13448,13471,26911],[(1024,14594),(1024,268588)]),([6,256,482,3652,13448,26880,32736],[(1024,268588),(1024,269612),(1024,276482)]),([6,256,482,3652,13448,26911,32736],[(1024,263183),(1024,268588),(1024,269612)]),([6,256,482,3679,13448,13471,26896],[(1024,268588),(1024,276482)]),([6,256,482,3679,13448,26896,32736],[(1024,268588),(1024,269612),(1024,276482)]),([6,272,287,482,3652,13448,26896],[(1024,132396),(1024,134444),(1024,142498),(1024,263468)]),([6,272,482,511,3652,13448,26911],[(1024,268450)])]
def t146 : BT := .nd (blockTree b150) [6,159,3652,13448,26896,32285] (blockTree b151)
def t147 : BT := .nd t145 [6,159,482,3652,13448,26896] t146
def t148 : BT := .nd t144 [6,66,482,511,3679,13448,26896] t147
def b152 : List Row := [([6,272,482,3652,3679,13448,26896],[(1024,132172),(1024,134220),(1024,145570),(1024,263244)]),([6,272,482,3652,13448,26896,26911],[(1024,132111)]),([6,272,482,3652,13448,26896,32736],[(1024,132396),(1024,165004),(1024,165006),(1024,165007)]),([6,272,482,3679,13448,26896],[(1024,276482)]),([6,287,482,3652,3679,13448,26896],[(1024,263244),(1024,263468),(1024,276482)]),([6,287,482,3652,5871,13448],[(1024,77058),(1024,145570),(1024,165007),(1024,263468),(1024,306434),(1024,406786)]),([6,287,482,3652,13448,13471,26896],[(1024,14594),(1024,263468),(1024,268588),(1024,276482)]),([6,287,482,3652,13448,26896],[(1024,132271),(1024,134542),(1024,142498),(1024,165007),(1024,263244),(1024,263468),(1024,306434)]),([6,287,482,3652,13448,26896,26911],[(1024,263335),(1024,263468)]),([6,287,482,3652,13448,26896,32736],[(1024,263183),(1024,263468),(1024,268588)]),([6,287,482,3652,13704,26896],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,263172)]),([6,287,482,3652,19319,26896],[(1024,132271),(1024,142498),(1024,165007),(1024,263244),(1024,263468),(1024,306434)]),([6,287,482,3652,26896,32152],[(1024,134542),(1024,142498),(1024,144546),(1024,165006),(1024,263172),(1024,406660)])]
def b153 : List Row := [([6,287,482,3908,13448,26896],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,263335),(1024,263468),(1024,268364)]),([6,287,482,3935,13448,26896],[(1024,132271),(1024,134542),(1024,263468),(1024,306434)]),([6,287,482,13448,26896,28500],[(1024,142498),(1024,165004),(1024,263335),(1024,263468)]),([6,287,482,13448,26896,29115],[(1024,132271),(1024,134542),(1024,165007),(1024,263244),(1024,263468),(1024,263566),(1024,306434)]),([6,287,3652,13448,26896,27122],[(1024,132271),(1024,142498),(1024,144546),(1024,165007),(1024,178306)]),([6,287,3652,13448,26896,32285],[(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,263244),(1024,263468),(1024,306434)]),([6,351,482,3652,13448,26896],[(1024,132271),(1024,134542),(1024,165007),(1024,263244),(1024,263468),(1024,268588),(1024,306434)]),([6,351,482,13448,26896,28500],[(1024,142498),(1024,165004),(1024,263468),(1024,268588),(1024,306439)]),([6,415,482,3652,13448,26896],[(1024,132271),(1024,134542),(1024,142498),(1024,165007),(1024,263244),(1024,263468),(1024,306434)]),([6,415,482,3652,26896,32152],[(1024,134542),(1024,142498),(1024,144546),(1024,165006),(1024,406660)]),([6,480,482,3652,13448,26880,32736],[(1024,178178),(1024,276482),(1024,396290)]),([6,480,482,3652,13448,26911,32736],[(1024,164879),(1024,263183),(1024,263463)]),([6,480,482,3679,13448,26896,32736],[(1024,178178),(1024,276482)])]
def t149 : BT := .nd (blockTree b152) [6,287,482,3679,13448,26896] (blockTree b153)
def b154 : List Row := [([6,482,482,511,3679,13448,26896],[]),([6,482,482,3652,13448,26880,32736],[(1024,276482)]),([6,482,482,3679,13448,13471,26896],[(1024,142504),(1024,178306),(1024,276482)]),([6,482,482,3679,13448,26896,32736],[(1024,178306),(1024,276482),(1024,276770)]),([6,482,498,3652,3679,13448,26896],[(1024,132108),(1024,132172),(1024,145570)]),([6,482,498,3652,13448,26896,32736],[(1024,132396),(1024,165007)]),([6,482,498,3679,13448,26896],[(1024,132108),(1024,142728),(1024,263180),(1024,269710),(1024,276872)]),([6,482,511,511,3679,13448,26896],[]),([6,482,511,1024,3679,13448,26896],[(1024,142724),(1024,273410)]),([6,482,511,1032,3679,13448,26896],[(1024,142728),(1024,273410)]),([6,482,511,1055,3652,13448,26896],[(1024,14498),(1024,142498),(1024,145570),(1024,276482)]),([6,482,511,2048,3679,13448,26896],[(1024,14498),(1024,145570)]),([6,482,511,2064,3679,13448,26896],[(1024,132494),(1024,134542),(1024,276482)])]
def b155 : List Row := [([6,482,511,3648,13448,26896,32736],[(1024,164879),(1024,165007)]),([6,482,511,3652,3679,5871,13448],[(1024,145570),(1024,145796),(1024,276482)]),([6,482,511,3652,3679,13448,26896],[(1024,145570),(1024,145796),(1024,276482)]),([6,482,511,3652,3679,13448,26911],[(1024,14728),(1024,276482)]),([6,482,511,3652,3679,13448,27122],[(1024,145570),(1024,145796),(1024,178306)]),([6,482,511,3652,3679,13448,27135],[(1024,178178)]),([6,482,511,3652,3679,19319,26896],[(1024,145570),(1024,145796),(1024,276482)]),([6,482,511,3652,5856,13448,26896],[(1024,263335)]),([6,482,511,3652,5871,13448,13471],[(1024,276482)]),([6,482,511,3652,5871,13448,26911],[(1024,306434)]),([6,482,511,3652,5871,13448,32736],[(1024,165007)]),([6,482,511,3652,8223,13448,26896],[(1024,14498),(1024,145570),(1024,276482)]),([6,482,511,3652,13448,13471,26896],[(1024,14498),(1024,276482)])]
def t150 : BT := .nd (blockTree b154) [6,482,511,2079,3652,13448,26896] (blockTree b155)
def t151 : BT := .nd t149 [6,480,3652,13448,26896,32738] t150
def b156 : List Row := [([6,482,511,3652,13448,13471,27122],[(1024,14498),(1024,145796),(1024,178306)]),([6,482,511,3652,13448,13471,27135],[(1024,14498),(1024,178178)]),([6,482,511,3652,13448,16095,26896],[(1024,145796),(1024,276482)]),([6,482,511,3652,13448,19296,26896],[(1024,164879)]),([6,482,511,3652,13448,26880,32736],[(1024,164879),(1024,276482)]),([6,482,511,3652,13448,26896,26911],[(1024,263335),(1024,263468)]),([6,482,511,3652,13448,26896,29088],[(1024,165007)]),([6,482,511,3652,13448,26896,32736],[(1024,164879),(1024,165007)]),([6,482,511,3652,13448,26896,32740],[(1024,165007)]),([6,482,511,3652,13448,26896,32744],[(1024,164879)]),([6,482,511,3652,13448,26896,32752],[]),([6,482,511,3652,13448,26911,28500],[(1024,66727),(1024,263335)]),([6,482,511,3652,13448,26911,32152],[(1024,263468)])]
def b157 : List Row := [([6,482,511,3652,13448,27122,32736],[(1024,164879),(1024,165007),(1024,165164)]),([6,482,511,3652,13448,27135,32736],[(1024,164879),(1024,165164)]),([6,482,511,3652,13450,26896],[(1024,134542),(1024,145794),(1024,145796),(1024,268588),(1024,396431)]),([6,482,511,3652,13471,13802,26896],[(1024,14498),(1024,145570),(1024,145796)]),([6,482,511,3652,13471,19319,26896],[(1024,14498),(1024,276482)]),([6,482,511,3652,19319,26896,26911],[(1024,263335),(1024,263468)]),([6,482,511,3652,19319,26896,32736],[(1024,164879),(1024,165007)]),([6,482,511,3652,26896,26911,32152],[(1024,132100),(1024,134311),(1024,134542)]),([6,482,511,3654,13448,26896],[(1024,134542),(1024,145796),(1024,263468),(1024,396431)]),([6,482,511,3679,3679,13448,26896],[(1024,142728),(1024,276482)]),([6,482,511,3679,4070,13448,26896],[(1024,145570),(1024,145796),(1024,273474)]),([6,482,511,3679,4095,13448,26896],[(1024,273410)]),([6,482,511,3679,5871,13448],[(1024,142728),(1024,276482)])]
def t152 : BT := .nd (blockTree b156) [6,482,511,3652,13448,26911,32736] (blockTree b157)
def b158 : List Row := [([6,482,511,3679,8192,13448,26896],[]),([6,482,511,3679,13448,13448,26896],[(1024,142728)]),([6,482,511,3679,13448,13471,26896],[(1024,178178),(1024,276482)]),([6,482,511,3679,13448,13802,26896],[(1024,142728)]),([6,482,511,3679,13448,13823,26896],[]),([6,482,511,3679,13448,16076,26896],[(1024,145570),(1024,407556)]),([6,482,511,3679,13448,16095,26896],[(1024,142728),(1024,276482),(1024,407556)]),([6,482,511,3679,13448,19319,26896],[(1024,142728)]),([6,482,511,3679,13448,26896],[(1024,134542),(1024,142728),(1024,263468),(1024,276482)]),([6,482,511,3679,13448,26896,26896],[(1024,134542),(1024,263468)]),([6,482,511,3679,13448,26896,26911],[(1024,263468)]),([6,482,511,3679,13448,26896,27122],[]),([6,482,511,3679,13448,26896,27135],[])]
def b159 : List Row := [([6,482,511,3679,13448,26896,28511],[(1024,142728),(1024,263468),(1024,273410)]),([6,482,511,3679,13448,26896,29088],[(1024,142728),(1024,145570),(1024,276482)]),([6,482,511,3679,13448,26896,29115],[(1024,145570),(1024,145796),(1024,276482)]),([6,482,511,3679,13448,26896,32152],[(1024,132494),(1024,134542),(1024,263468),(1024,269710)]),([6,482,511,3679,13448,26896,32256],[(1024,276770)]),([6,482,511,3679,13448,26896,32285],[(1024,276770)]),([6,482,511,3679,13448,26896,32736],[(1024,178178),(1024,276482),(1024,276770)]),([6,482,511,3679,13448,26911],[(1024,6444),(1024,11656),(1024,276482)]),([6,482,511,3679,13448,27122],[(1024,178306)]),([6,482,511,3679,13448,27135],[(1024,178178)]),([6,482,511,3679,19319,26896],[(1024,142728),(1024,263468),(1024,276482)]),([6,482,511,3679,26896,32152],[(1024,134542),(1024,406660)]),([6,482,511,13448,13471,26896,29115],[(1024,14498),(1024,276482)])]
def t153 : BT := .nd (blockTree b158) [6,482,511,3679,13448,26896,28500] (blockTree b159)
def t154 : BT := .nd t152 [6,482,511,3679,5871,13448,26896] t153
def t155 : BT := .nd t151 [6,482,511,3652,13448,13471,26911] t154
def t156 : BT := .nd t148 [6,272,482,511,3679,13448,26896] t155
def t157 : BT := .nd t141 [6,31,3679,4095,13448,26896,32285] t156
def b160 : List Row := [([6,482,511,13448,26896,26911,28511],[(1024,263468)]),([6,482,511,13448,26896,26911,29115],[(1024,263468)]),([6,482,511,13448,26896,28511],[(1024,263468),(1024,306434)]),([6,482,511,13448,26896,29088],[(1024,134542),(1024,142728),(1024,165007)]),([6,482,511,13448,26896,29115,32736],[(1024,164879),(1024,165007)]),([6,482,511,13448,26911,28500],[(1024,66727),(1024,263335),(1024,268450)]),([6,482,615,3652,3679,26896],[(1024,1294),(1024,134542),(1024,144546),(1024,165006),(1024,406660)]),([6,482,615,3652,26896,32736],[(1024,134542),(1024,165004),(1024,165006)]),([6,482,1032,3679,13471,26896],[(1024,1295),(1024,142504),(1024,170126),(1024,171148)]),([6,482,1032,3679,16076,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,407720)]),([6,482,1055,1535,3652,13448,26896],[(1024,14498),(1024,142498),(1024,144546),(1024,145570)]),([6,482,1055,3652,5871,13448],[(1024,1295),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([6,482,1055,3652,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,268588),(1024,276482)])]
def b161 : List Row := [([6,482,1055,3652,13448,27122],[(1024,14498),(1024,132271),(1024,142498),(1024,145570),(1024,165007),(1024,178306)]),([6,482,1055,3652,13448,27920],[(1024,1295),(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,268588),(1024,276482)]),([6,482,1055,3652,13448,27935],[(1024,1295),(1024,11522),(1024,14498),(1024,14594),(1024,263183),(1024,268588),(1024,276482)]),([6,482,1055,3652,19319,26896],[(1024,1295),(1024,14594),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,268588),(1024,276482)]),([6,482,1055,3652,26896,32152],[(1024,1294),(1024,134540),(1024,134542),(1024,142498),(1024,165006),(1024,406660)]),([6,482,1055,3679,13448,26896],[(1024,1295),(1024,134542),(1024,142724),(1024,178306),(1024,268588),(1024,276482)]),([6,482,1055,13448,16076,26896],[(1024,1295),(1024,14594),(1024,142498),(1024,142724),(1024,145570),(1024,165007),(1024,268588),(1024,309415)]),([6,482,1055,13448,26896,28500],[(1024,1292),(1024,142498),(1024,165004),(1024,268588),(1024,306439)]),([6,482,1055,13448,26896,29115],[(1024,1295),(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,276482)]),([6,482,1088,1119,13448,26896],[(1024,1292),(1024,11522),(1024,134540),(1024,142498),(1024,165004),(1024,273410)]),([6,482,1088,13448,26896,32736],[(1024,165004),(1024,273410)]),([6,482,1119,3652,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,276482)]),([6,482,1119,13448,13802,26896],[(1024,11522),(1024,142498),(1024,165004),(1024,269710),(1024,273410),(1024,273800)])]
def t158 : BT := .nd (blockTree b160) [6,482,1055,3652,13448,26911] (blockTree b161)
def b162 : List Row := [([6,482,1160,3652,3679,4095,26896],[(1024,144546)]),([6,482,1160,3652,3679,26896],[(1024,1294),(1024,144546),(1024,165006)]),([6,482,1183,3652,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,268588),(1024,276482)]),([6,482,1604,1631,5871,13448],[(1024,1292),(1024,11426),(1024,142498),(1024,165004),(1024,273410)]),([6,482,1604,1631,13448,26896],[(1024,1292),(1024,11522),(1024,134540),(1024,142498),(1024,165004),(1024,273410),(1024,404484)]),([6,482,1604,5871,13448,32736],[(1024,164876),(1024,165004),(1024,263180),(1024,273410)]),([6,482,1604,13448,26896,32736],[(1024,164876),(1024,165004),(1024,273410)]),([6,482,1631,3652,5871,13448],[(1024,1295),(1024,14498),(1024,76962),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([6,482,1631,3652,13448,26896],[(1024,1295),(1024,14594),(1024,76962),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,276482),(1024,407556)]),([6,482,1631,5871,13448],[(1024,142498),(1024,142724),(1024,273410)]),([6,482,1631,5871,13448,26896],[(1024,1292),(1024,142498),(1024,165004),(1024,273410)]),([6,482,1631,13448,26896],[(1024,142498),(1024,142724),(1024,273410)]),([6,482,2048,3652,8223,13448],[(1024,1199),(1024,3471),(1024,14498),(1024,164879),(1024,170287),(1024,407556)])]
def b163 : List Row := [([6,482,2048,3679,5871,13448],[(1024,1295),(1024,14498),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([6,482,2048,3679,8192,13448],[(1024,1199),(1024,3471),(1024,14498),(1024,164879),(1024,407556)]),([6,482,2048,3679,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,407556)]),([6,482,2048,3679,13448,26911],[(1024,1295),(1024,14498),(1024,14503),(1024,14594),(1024,169999),(1024,407563)]),([6,482,2048,3679,13448,27122],[(1024,14498),(1024,132271),(1024,145570),(1024,165007),(1024,178306),(1024,407556)]),([6,482,2048,3679,13448,28500],[(1024,1295),(1024,14594),(1024,80034),(1024,164943),(1024,407556)]),([6,482,2048,3679,13448,28511],[(1024,1295),(1024,14498),(1024,14594),(1024,263183),(1024,407720)]),([6,482,2048,3679,15496,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,276482),(1024,407556)]),([6,482,2048,3679,19319,26896],[(1024,1295),(1024,14498),(1024,14594),(1024,144546),(1024,145570),(1024,165007)]),([6,482,2048,3679,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([6,482,2048,13448,26896,29088],[(1024,1295),(1024,145570),(1024,164879),(1024,165006),(1024,165007),(1024,276482)]),([6,482,2052,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007)]),([6,482,2064,3652,3679,13448,27122],[(1024,134542),(1024,145570),(1024,178316)])]
def t159 : BT := .nd (blockTree b162) [6,482,2048,3679,4095,13448,26896] (blockTree b163)
def t160 : BT := .nd t158 [6,482,1119,13448,26896] t159
def b164 : List Row := [([6,482,2079,2559,3652,13448,26896],[(1024,145570)]),([6,482,2079,3652,5871,13448],[(1024,1295),(1024,144546),(1024,145570),(1024,165007)]),([6,482,2079,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007)]),([6,482,2079,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,482,2079,3652,15496,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([6,482,2079,3652,19319,26896],[(1024,1295),(1024,144546),(1024,145570),(1024,165007)]),([6,482,2079,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([6,482,2079,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([6,482,2112,3679,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,407556)]),([6,482,2112,3679,13448,27122],[(1024,14498),(1024,132271),(1024,145570),(1024,165007),(1024,178306),(1024,407556)]),([6,482,2143,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007)]),([6,482,2143,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,482,2304,3679,13448,26896],[(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,407556)])]
def b165 : List Row := [([6,482,2335,3652,13448,26896],[(1024,77058),(1024,132271),(1024,134542),(1024,165007),(1024,263244)]),([6,482,2530,3679,13448,26896],[(1024,14594),(1024,134542),(1024,145570),(1024,145676),(1024,145796),(1024,165007),(1024,407556)]),([6,482,2546,3652,3679,13448,26896],[(1024,132494),(1024,145570)]),([6,482,2628,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007)]),([6,482,2628,3679,19319,26896],[(1024,1295),(1024,144546),(1024,145570),(1024,165007)]),([6,482,2655,3652,13448,26896],[(1024,1295),(1024,69003),(1024,134542),(1024,145570),(1024,165007)]),([6,482,2655,3652,19319,26896],[(1024,1295),(1024,75938),(1024,144546),(1024,145570),(1024,165007)]),([6,482,3072,3679,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,407556)]),([6,482,3072,3679,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([6,482,3103,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007)]),([6,482,3103,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([6,482,3588,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3615,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)])]
def t161 : BT := .nd (blockTree b164) [6,482,2320,3652,3679,13448,26896] (blockTree b165)
def b166 : List Row := [([6,482,3648,5871,13448,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,263183),(1024,276482)]),([6,482,3648,13448,26880,32736],[(1024,1295),(1024,268588),(1024,269710),(1024,276482)]),([6,482,3648,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3648,13448,26896,32740],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3648,13448,26911,32736],[(1024,164879),(1024,263180),(1024,263183),(1024,276482)]),([6,482,3648,13448,27122,32736],[(1024,165007),(1024,178178),(1024,178306)]),([6,482,3648,19319,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3648,26896,32152,32736],[(1024,134542),(1024,165004),(1024,165006)]),([6,482,3652,3679,3935,13448,26896],[(1024,145570),(1024,263244)]),([6,482,3652,3679,4095,5871,13448],[(1024,144546),(1024,145570),(1024,145796)]),([6,482,3652,3679,4095,13448,26896],[(1024,144546),(1024,145570),(1024,145796)]),([6,482,3652,3679,4095,13448,27122],[(1024,144546),(1024,145570),(1024,145796)]),([6,482,3652,3679,4095,19319,26896],[(1024,145570),(1024,145796)])]
def b167 : List Row := [([6,482,3652,3679,5256,26896],[(1024,1294),(1024,134542),(1024,144546),(1024,165006),(1024,406532),(1024,406660)]),([6,482,3652,3679,5645,13448],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,482,3652,3679,5871,13448],[(1024,1295),(1024,144546),(1024,145570),(1024,165007)]),([6,482,3652,3679,5871,19319],[(1024,1295),(1024,145570),(1024,165007),(1024,406660)]),([6,482,3652,3679,5871,32152],[(1024,1294),(1024,134542),(1024,144546),(1024,165006),(1024,406660)]),([6,482,3652,3679,5887,13448],[(1024,1295),(1024,275458),(1024,276482)]),([6,482,3652,3679,6127,13448],[(1024,144546),(1024,145570),(1024,165007)]),([6,482,3652,3679,10240,13448],[(1024,1199),(1024,3471),(1024,14498),(1024,164879),(1024,407556)]),([6,482,3652,3679,10256,13448],[(1024,1199),(1024,3471),(1024,14498),(1024,164879),(1024,407556)]),([6,482,3652,3679,13448,13823,26896],[(1024,145570)]),([6,482,3652,3679,13448,16383,26896],[(1024,145570),(1024,407556)]),([6,482,3652,3679,13448,26640],[(1024,132271),(1024,134542),(1024,145570),(1024,165007)]),([6,482,3652,3679,13448,26880],[(1024,1295),(1024,263183),(1024,269710),(1024,276482)])]
def t162 : BT := .nd (blockTree b166) [6,482,3652,3679,5256,5871] (blockTree b167)
def t163 : BT := .nd t161 [6,482,3648,3679,13448,26896] t162
def t164 : BT := .nd t160 [6,482,2064,3679,4070,13448,26896] t163
def b168 : List Row := [([6,482,3652,3679,13448,26896,28672],[(1024,396431)]),([6,482,3652,3679,13448,26896,32256],[(1024,145570),(1024,396431)]),([6,482,3652,3679,13448,26898],[(1024,71951),(1024,134542),(1024,145570),(1024,145575),(1024,145666),(1024,263311)]),([6,482,3652,3679,13448,26904],[(1024,1295),(1024,145570),(1024,165007)]),([6,482,3652,3679,13448,26960],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3652,3679,13448,26962],[(1024,132367),(1024,134542),(1024,145570),(1024,145666),(1024,263311),(1024,276610)]),([6,482,3652,3679,13448,27024],[(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3652,3679,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,482,3652,3679,13448,27920],[(1024,1295),(1024,134542),(1024,145570),(1024,165007)]),([6,482,3652,3679,13448,27928],[(1024,1295),(1024,145570),(1024,165007)]),([6,482,3652,3679,13450,26896],[(1024,71951),(1024,134542),(1024,145575),(1024,145796),(1024,396431)]),([6,482,3652,3679,13464,26896],[(1024,1295),(1024,76932),(1024,134156),(1024,134220),(1024,134542),(1024,141388),(1024,165006)]),([6,482,3652,3679,13471,13802,26896],[(1024,142504),(1024,145796),(1024,178180)])]
def b169 : List Row := [([6,482,3652,3679,13514,26896],[(1024,134542),(1024,145796),(1024,276872),(1024,396431),(1024,400655)]),([6,482,3652,3679,13704,26896],[(1024,1294),(1024,77064),(1024,134542),(1024,165007),(1024,269388),(1024,269710)]),([6,482,3652,3679,13802,16095,26896],[(1024,145796),(1024,178180)]),([6,482,3652,3679,15496,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,276482),(1024,407556)]),([6,482,3652,3679,15512,26896],[(1024,1295),(1024,134542),(1024,165006),(1024,406660),(1024,407556)]),([6,482,3652,3679,19319,26896],[(1024,1295),(1024,144546),(1024,145570),(1024,165007)]),([6,482,3652,3679,19319,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,482,3652,3679,26896,27511],[(1024,1294),(1024,3470),(1024,144546),(1024,165006)]),([6,482,3652,3679,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([6,482,3652,3679,28500,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,406660)]),([6,482,3652,3807,13448,26896],[(1024,1295),(1024,134542),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3652,3935,13448,26896],[(1024,77058),(1024,132271),(1024,134542),(1024,165007),(1024,263244),(1024,263566)]),([6,482,3652,4070,13448,26880,32736],[(1024,276482)])]
def t165 : BT := .nd (blockTree b168) [6,482,3652,3679,13512,26896] (blockTree b169)
def b170 : List Row := [([6,482,3652,4095,13448,16095,26896],[(1024,145570),(1024,145796)]),([6,482,3652,4095,13448,26896,29088],[(1024,165006),(1024,165007)]),([6,482,3652,4095,13448,26896,32736],[(1024,165006),(1024,165007)]),([6,482,3652,5256,5871,32736],[(1024,164878),(1024,165004),(1024,165006),(1024,263182),(1024,275458)]),([6,482,3652,5256,26896,32736],[(1024,164878),(1024,165004),(1024,165006),(1024,275458)]),([6,482,3652,5645,13448,32736],[(1024,164879),(1024,165007),(1024,178306)]),([6,482,3652,5856,5887,13448],[(1024,1295),(1024,11522),(1024,13570),(1024,14594),(1024,263183)]),([6,482,3652,5856,13448,13471],[(1024,1295),(1024,11522),(1024,14498),(1024,14504),(1024,14594),(1024,263183)]),([6,482,3652,5856,13448,32736],[(1024,164879),(1024,263180),(1024,263183),(1024,276482)]),([6,482,3652,5871,8223,13448],[(1024,1295),(1024,142498),(1024,145570),(1024,165007),(1024,276482),(1024,407556)]),([6,482,3652,5871,13448,29088],[(1024,1295),(1024,145570),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,5871,13448,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,263183),(1024,276482)]),([6,482,3652,5871,13448,32740],[(1024,165004),(1024,165006),(1024,165007),(1024,263183),(1024,276482)])]
def b171 : List Row := [([6,482,3652,5871,32152,32736],[(1024,165004),(1024,165006),(1024,406660)]),([6,482,3652,5887,13448,26911],[(1024,1295),(1024,11522),(1024,13570),(1024,14594),(1024,263183),(1024,276482)]),([6,482,3652,5887,13448,32736],[(1024,1295),(1024,14594),(1024,263183),(1024,273410),(1024,275458),(1024,276482)]),([6,482,3652,6127,13448,32736],[(1024,145570),(1024,165004),(1024,165006),(1024,165007)]),([6,482,3652,8200,13471,26911],[(1024,1295),(1024,10540),(1024,14498),(1024,14504),(1024,76076)]),([6,482,3652,8223,8703,13448,26896],[(1024,14498),(1024,145570)]),([6,482,3652,8223,13448,26896],[(1024,1295),(1024,14594),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,482,3652,8223,13448,26911],[(1024,1295),(1024,14498),(1024,14594),(1024,263183),(1024,268588),(1024,276482),(1024,407556)]),([6,482,3652,8223,13448,27122],[(1024,14498),(1024,132271),(1024,145570),(1024,165007),(1024,178306),(1024,407556),(1024,407684)]),([6,482,3652,8223,13448,32152],[(1024,1295),(1024,134543),(1024,165007),(1024,407556),(1024,407684)]),([6,482,3652,8223,19319,26896],[(1024,1295),(1024,3471),(1024,14594),(1024,145570),(1024,165007),(1024,268588),(1024,276482)]),([6,482,3652,8351,13448,26896],[(1024,1295),(1024,14594),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,482,3652,8351,13448,27122],[(1024,14498),(1024,132271),(1024,145570),(1024,165007),(1024,178306),(1024,407556),(1024,407684)])]
def t166 : BT := .nd (blockTree b170) [6,482,3652,5871,19319,32736] (blockTree b171)
def t167 : BT := .nd t165 [6,482,3652,4095,13448,13471,26896] t166
def b172 : List Row := [([6,482,3652,9247,13448,26896],[(1024,1295),(1024,14594),(1024,142498),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,482,3652,10240,10271,13448],[(1024,1199),(1024,3471),(1024,14498),(1024,164879),(1024,170287),(1024,407556)]),([6,482,3652,10240,13448,32736],[(1024,164879),(1024,407556)]),([6,482,3652,10271,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,407556),(1024,407684)]),([6,482,3652,11871,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,407556),(1024,407684)]),([6,482,3652,13440,26896,32744],[(1024,164868),(1024,396456)]),([6,482,3652,13448,13471,13823,26911],[(1024,11522),(1024,14594),(1024,71980)]),([6,482,3652,13448,13471,26896,32256],[]),([6,482,3652,13448,13471,26904],[(1024,1295),(1024,145570),(1024,165007),(1024,268588)]),([6,482,3652,13448,13471,26911],[(1024,1295),(1024,14498),(1024,14504),(1024,14594),(1024,76076),(1024,263183),(1024,268588)]),([6,482,3652,13448,13471,27135],[(1024,1199),(1024,14498),(1024,76076),(1024,164879),(1024,178178)]),([6,482,3652,13448,13792,26896,32736],[(1024,165004),(1024,165007)]),([6,482,3652,13448,13802,26880,32736],[(1024,273410),(1024,276482)])]
def b173 : List Row := [([6,482,3652,13448,13823,26896,32736],[(1024,165004),(1024,165007)]),([6,482,3652,13448,19296,26911],[(1024,1295),(1024,14594),(1024,76076),(1024,164879),(1024,171023),(1024,263183),(1024,268588),(1024,276482)]),([6,482,3652,13448,24544,26896],[(1024,1295),(1024,145570),(1024,164879),(1024,165007),(1024,268588),(1024,276482)]),([6,482,3652,13448,26640,32736],[(1024,145570),(1024,165004),(1024,165006),(1024,165007)]),([6,482,3652,13448,26880,26911],[(1024,1295),(1024,14594),(1024,263180),(1024,263183),(1024,273410),(1024,275458)]),([6,482,3652,13448,26880,27106,32736],[(1024,276482)]),([6,482,3652,13448,26880,32285,32736],[]),([6,482,3652,13448,26880,32736],[(1024,1295),(1024,268588),(1024,269710),(1024,276482)]),([6,482,3652,13448,26880,32740],[(1024,1295),(1024,268364),(1024,269710),(1024,276482)]),([6,482,3652,13448,26880,32752],[(1024,1295),(1024,268588),(1024,269710),(1024,276482)]),([6,482,3652,13448,26896,26911,32256],[(1024,263335),(1024,263468)]),([6,482,3652,13448,26896,27106,32736],[(1024,165007),(1024,276482)]),([6,482,3652,13448,26896,29088],[(1024,1295),(1024,145570),(1024,165006),(1024,165007),(1024,276482)])]
def t168 : BT := .nd (blockTree b172) [6,482,3652,13448,13823,26896,26911] (blockTree b173)
def b174 : List Row := [([6,482,3652,13448,26896,31712],[(1024,1295),(1024,145570),(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,13448,26896,32256,32736],[(1024,165007)]),([6,482,3652,13448,26896,32480],[(1024,165004),(1024,165006),(1024,165007),(1024,263468)]),([6,482,3652,13448,26896,32608],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,13448,26896,32672],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,13448,26896,32740],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,13448,26898,32736],[(1024,165007),(1024,263308),(1024,263310),(1024,263311),(1024,276482),(1024,276610)]),([6,482,3652,13448,26900,32736],[(1024,164940),(1024,164943),(1024,276482)]),([6,482,3652,13448,26904,32736],[(1024,165004),(1024,165007),(1024,276482)]),([6,482,3652,13448,26911,32736],[(1024,164879),(1024,263180),(1024,263183),(1024,276482)]),([6,482,3652,13448,26911,32744],[(1024,164879),(1024,263172),(1024,263180),(1024,263183),(1024,276482)]),([6,482,3652,13448,26960,32736],[(1024,165006),(1024,165007),(1024,276482)])]
def b175 : List Row := [([6,482,3652,13448,27104,32736],[(1024,1199),(1024,164879),(1024,165164),(1024,178178)]),([6,482,3652,13448,27106,32736],[(1024,178178)]),([6,482,3652,13448,27120,32736],[(1024,165007),(1024,178178),(1024,396431)]),([6,482,3652,13448,27122,29088],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,482,3652,13448,27122,32736],[(1024,165007),(1024,178178),(1024,178306)]),([6,482,3652,13448,27122,32736,32738],[(1024,165007),(1024,165164),(1024,396418)]),([6,482,3652,13448,27122,32736,32752],[(1024,165007),(1024,178178),(1024,396431)]),([6,482,3652,13448,27122,32740],[(1024,165007),(1024,178178),(1024,178306)]),([6,482,3652,13448,27135,32736],[(1024,164879),(1024,178178)]),([6,482,3652,13448,27920,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,13450,26896,32736],[(1024,276775),(1024,394383),(1024,396428),(1024,396430),(1024,396431)]),([6,482,3652,13452,26896,32736],[(1024,68775),(1024,164939)]),([6,482,3652,13464,26896,32736],[(1024,134444),(1024,165006)])]
def t169 : BT := .nd (blockTree b174) [6,482,3652,13448,27024,32736] (blockTree b175)
def t170 : BT := .nd t168 [6,482,3652,13448,26896,30688] t169
def t171 : BT := .nd t167 [6,482,3652,8479,13448,26896] t170
def t172 : BT := .nd t164 [6,482,3652,3679,13448,26896] t171
def b176 : List Row := [([6,482,3652,13471,13802,26911],[(1024,11432),(1024,14498),(1024,14504),(1024,76076),(1024,171023),(1024,268588),(1024,276482),(1024,276484),(1024,276775)]),([6,482,3652,13471,16076,26911],[(1024,1295),(1024,14498),(1024,14504),(1024,14594),(1024,76076),(1024,403524)]),([6,482,3652,13471,19319,26911],[(1024,1295),(1024,14498),(1024,14504),(1024,14594),(1024,76076),(1024,263183),(1024,268588),(1024,276482)]),([6,482,3652,13512,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,13704,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,269612)]),([6,482,3652,15496,26896,32736],[(1024,164879),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,19319,26880,32736],[(1024,1295),(1024,268588),(1024,275458),(1024,276482)]),([6,482,3652,19319,26896,29088],[(1024,1295),(1024,145570),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,19319,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,19319,26896,32740],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3652,19319,26911,32736],[(1024,164879),(1024,263180),(1024,263183),(1024,276482)]),([6,482,3652,19319,27122,32736],[(1024,165007),(1024,178178),(1024,178306)]),([6,482,3652,26880,32136,32736],[(1024,1294),(1024,269710),(1024,273410),(1024,406792)])]
def b177 : List Row := [([6,482,3652,26896,29088,32152],[(1024,1294),(1024,134542),(1024,165006)]),([6,482,3652,26896,32136,32736],[(1024,1294),(1024,165006),(1024,269710),(1024,273410),(1024,406792)]),([6,482,3652,26896,32152,32736],[(1024,134542),(1024,165004),(1024,165006)]),([6,482,3652,26896,32152,32740],[(1024,134542),(1024,165004),(1024,165006)]),([6,482,3652,28500,32152,32736],[(1024,134542),(1024,165003),(1024,165006),(1024,268292)]),([6,482,3654,3679,13448,26896],[(1024,66831),(1024,134542),(1024,145570),(1024,145796),(1024,396431)]),([6,482,3654,13448,26896,32736],[(1024,165007),(1024,276546),(1024,396428),(1024,396430),(1024,396431)]),([6,482,3660,3679,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,269710)]),([6,482,3660,13448,13471,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,268588)]),([6,482,3660,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3668,13448,26896,32736],[(1024,165004),(1024,165007),(1024,276482)]),([6,482,3679,3679,4070,13448,26896],[(1024,145570),(1024,145796),(1024,178306),(1024,276620)]),([6,482,3679,3780,13448,26896],[(1024,1295),(1024,134542),(1024,144546),(1024,145570),(1024,165007),(1024,276482)])]
def t173 : BT := .nd (blockTree b176) [6,482,3652,26896,27511,32736] (blockTree b177)
def b178 : List Row := [([6,482,3679,4070,4095,13448,26896],[(1024,144546),(1024,145570),(1024,145796)]),([6,482,3679,4070,5871,13448],[(1024,144546),(1024,145570),(1024,145796),(1024,165007),(1024,276620)]),([6,482,3679,4070,13448,13471,26896],[(1024,145570),(1024,178306),(1024,276482)]),([6,482,3679,4070,13448,16095,26896],[(1024,145570),(1024,145796),(1024,178306),(1024,276620),(1024,407556)]),([6,482,3679,4070,13448,26896],[(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,276620)]),([6,482,3679,4070,13448,26896,28511],[(1024,145570),(1024,145796),(1024,276610)]),([6,482,3679,4070,13448,26896,29088],[(1024,178306),(1024,273551),(1024,276546),(1024,276620),(1024,396431)]),([6,482,3679,4070,13448,26896,32736],[(1024,145575),(1024,178306),(1024,276482),(1024,276546),(1024,396431)]),([6,482,3679,4070,13448,27122],[(1024,145570),(1024,145796),(1024,165007),(1024,178306),(1024,178316)]),([6,482,3679,4070,19319,26896],[(1024,144546),(1024,145570),(1024,145796),(1024,165007),(1024,276620)]),([6,482,3679,4070,26896,32152],[(1024,134542),(1024,165006),(1024,275596),(1024,406660)]),([6,482,3679,4095,13448,13471,26896],[(1024,142504),(1024,144551),(1024,276482)]),([6,482,3679,4095,13448,16076,26896],[(1024,145570),(1024,145796),(1024,407556)])]
def b179 : List Row := [([6,482,3679,4095,13448,26896,32736],[(1024,145575),(1024,275458),(1024,276482)]),([6,482,3679,5871,5887,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([6,482,3679,5871,7919,13448],[(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,276482),(1024,406668)]),([6,482,3679,5871,13448,13471],[(1024,1295),(1024,142504),(1024,144551),(1024,273410),(1024,276482)]),([6,482,3679,5871,13448,16076],[(1024,1295),(1024,14498),(1024,145570),(1024,165007)]),([6,482,3679,5871,13448,29115],[(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3679,5871,13448,32736],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482),(1024,276770)]),([6,482,3679,5887,13448],[(1024,276482),(1024,276872)]),([6,482,3679,5887,13448,26896],[(1024,1295),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]),([6,482,3679,7919,13448,26896],[(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,276482),(1024,406668)]),([6,482,3679,8208,13448,26896],[(1024,1295),(1024,144546),(1024,263180),(1024,269711),(1024,276482),(1024,407556),(1024,407816)]),([6,482,3679,8223,13448,26896],[(1024,1295),(1024,134543),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,482,3679,10240,13448],[(1024,14498),(1024,178178),(1024,407556),(1024,407720)])]
def t174 : BT := .nd (blockTree b178) [6,482,3679,4095,13448,26896,29115] (blockTree b179)
def t175 : BT := .nd t173 [6,482,3679,3908,13448,26896] t174
def b180 : List Row := [([6,482,3679,10240,13448,26896],[(1024,1295),(1024,14594),(1024,134543),(1024,145570),(1024,165007),(1024,276482),(1024,407556),(1024,407684)]),([6,482,3679,11844,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,407556),(1024,407684)]),([6,482,3679,13448,13464,26896],[(1024,1295),(1024,134156),(1024,134542),(1024,142504),(1024,263180),(1024,276482)]),([6,482,3679,13448,13471,13802,26896],[(1024,142504),(1024,178306),(1024,273800),(1024,276482)]),([6,482,3679,13448,13471,13823,26896],[(1024,273410),(1024,276482)]),([6,482,3679,13448,13471,26896],[(1024,1295),(1024,134542),(1024,142504),(1024,178306),(1024,268588),(1024,276482)]),([6,482,3679,13448,13471,26896,27122],[(1024,134542),(1024,178306),(1024,276482),(1024,276484),(1024,276487)]),([6,482,3679,13448,13471,26896,32285],[(1024,132271),(1024,142504),(1024,276770)]),([6,482,3679,13448,13471,26911],[(1024,1295),(1024,10540),(1024,11432),(1024,178178),(1024,268588),(1024,276482)]),([6,482,3679,13448,13471,27122],[(1024,132271),(1024,134542),(1024,142504),(1024,178306)]),([6,482,3679,13448,13802,13823,26896],[(1024,142498)]),([6,482,3679,13448,13802,26896,32736],[(1024,178306),(1024,273800),(1024,276482),(1024,276770)]),([6,482,3679,13448,13823,26896],[(1024,134542),(1024,263468),(1024,276482)])]
def b181 : List Row := [([6,482,3679,13448,16076,26896],[(1024,1295),(1024,14498),(1024,145570),(1024,165007)]),([6,482,3679,13448,16076,27122],[(1024,14498),(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,482,3679,13448,16366,26896],[(1024,14498),(1024,145570),(1024,165007),(1024,269710),(1024,276546),(1024,276620)]),([6,482,3679,13448,16691,26896],[(1024,1295),(1024,14498),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3679,13448,19296,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,171148),(1024,178306),(1024,268588),(1024,276482),(1024,276770)]),([6,482,3679,13448,24848,26896],[(1024,1295),(1024,142734),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3679,13448,26880],[(1024,276482),(1024,276872)]),([6,482,3679,13448,26880,26896],[(1024,1295),(1024,145570),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]),([6,482,3679,13448,26880,32736],[(1024,1295),(1024,268588),(1024,269710),(1024,276482),(1024,276770)]),([6,482,3679,13448,26896,27122,32736],[(1024,178306),(1024,276482),(1024,276610)]),([6,482,3679,13448,26896,28697],[(1024,1295),(1024,134542),(1024,142607),(1024,145570),(1024,165007),(1024,276546)]),([6,482,3679,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3679,13448,26896,29119],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)])]
def t176 : BT := .nd (blockTree b180) [6,482,3679,13448,15496,26896] (blockTree b181)
def b182 : List Row := [([6,482,3679,13448,26896,30139],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3679,13448,26896,30719],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,276482),(1024,407556)]),([6,482,3679,13448,26896,32256],[(1024,134542),(1024,145570),(1024,263468),(1024,276770),(1024,296207),(1024,400524)]),([6,482,3679,13448,26896,32285,32736],[(1024,132271),(1024,296207)]),([6,482,3679,13448,26896,32736],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,276770)]),([6,482,3679,13448,26896,32738],[(1024,134542),(1024,145796),(1024,263468),(1024,276482),(1024,276770),(1024,296207),(1024,396431)]),([6,482,3679,13448,26896,32740],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268364),(1024,276482),(1024,276546)]),([6,482,3679,13448,26896,32744],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482),(1024,276770)]),([6,482,3679,13448,26896,32751],[(1024,1295),(1024,263180),(1024,269710),(1024,276482)]),([6,482,3679,13448,26911,32736],[(1024,1295),(1024,14594),(1024,178178),(1024,263180),(1024,263183),(1024,276482),(1024,276775)]),([6,482,3679,13448,27122,29115],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([6,482,3679,13448,27122,32736],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([6,482,3679,13464,26896],[(1024,134156),(1024,134542),(1024,142340),(1024,144546)])]
def b183 : List Row := [([6,482,3679,13471,19319,26896],[(1024,1295),(1024,142504),(1024,144551),(1024,178306),(1024,268588),(1024,276482)]),([6,482,3679,13471,26896,32152],[(1024,1295),(1024,134444),(1024,134542),(1024,170126),(1024,269711),(1024,406660),(1024,407816)]),([6,482,3679,13802,16076,26896],[(1024,14498),(1024,145570),(1024,165007),(1024,276482),(1024,276548),(1024,276872)]),([6,482,3679,15496,26896],[(1024,145570),(1024,145796),(1024,276482)]),([6,482,3679,16076,19319,26896],[(1024,1295),(1024,14498),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3679,16076,26896,32152],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,269710),(1024,276482),(1024,407684)]),([6,482,3679,19319,26896,29115],[(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3679,19319,26896,32736],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482),(1024,276770)]),([6,482,3679,26896,29115,32152],[(1024,1294),(1024,134542),(1024,144546),(1024,165006),(1024,406660)]),([6,482,3679,26896,32152,32736],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]),([6,482,3780,3807,13448,26896],[(1024,1295),(1024,134542),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([6,482,3780,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,3908,3935,13448,26896],[(1024,1292),(1024,77063),(1024,134542),(1024,145570),(1024,165007),(1024,263244),(1024,268364)])]
def t177 : BT := .nd (blockTree b182) [6,482,3679,13471,13802,26896] (blockTree b183)
def t178 : BT := .nd t176 [6,482,3679,13448,26896,29179] t177
def t179 : BT := .nd t175 [6,482,3679,10240,13448,16076] t178
def b184 : List Row := [([6,482,4070,13448,26896,29088],[(1024,145570),(1024,165006),(1024,165007),(1024,276546),(1024,276620)]),([6,482,4267,13448,26896,32736],[(1024,165004),(1024,268588)]),([6,482,5871,13448,28500,32736],[(1024,165004),(1024,306439)]),([6,482,5871,13448,29115,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,263183),(1024,276482)]),([6,482,8223,11844,13448,26896],[(1024,1295),(1024,14594),(1024,134543),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,482,8223,11871,13448,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([6,482,8223,13448,26896,28500],[(1024,1292),(1024,142498),(1024,268588)]),([6,482,8223,13448,26896,29115],[(1024,1295),(1024,14594),(1024,142498),(1024,145570),(1024,165007),(1024,407556),(1024,407684)]),([6,482,9247,13448,26896,28500],[(1024,1292),(1024,142498),(1024,268588)]),([6,482,11844,11871,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,407556),(1024,407684)]),([6,482,11844,13448,26896,32736],[(1024,164879),(1024,165004),(1024,165007),(1024,276482)]),([6,482,13448,13471,26896,28511],[(1024,1292),(1024,263180),(1024,263468),(1024,268588),(1024,306439)]),([6,482,13448,13471,26896,29088],[(1024,1295),(1024,142504),(1024,165007),(1024,170126),(1024,178306),(1024,273410),(1024,276482)])]
def b185 : List Row := [([6,482,13448,13471,26911,28511],[(1024,1292),(1024,10540),(1024,11522),(1024,268588)]),([6,482,13448,13471,26911,29115],[(1024,1295),(1024,11522),(1024,14498),(1024,14504),(1024,14594),(1024,76076),(1024,263183)]),([6,482,13448,16076,26896,29088],[(1024,1295),(1024,145570),(1024,164879),(1024,165007),(1024,276482)]),([6,482,13448,26880,28484,32736],[(1024,1292),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]),([6,482,13448,26880,28500,32736],[(1024,1292),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]),([6,482,13448,26880,29115,32736],[(1024,1295),(1024,269710),(1024,273410),(1024,276482)]),([6,482,13448,26896,28480,32736],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([6,482,13448,26896,28484,32736],[(1024,1292),(1024,165004),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]),([6,482,13448,26896,28496,32736],[(1024,165004),(1024,268588)]),([6,482,13448,26896,28500,32736],[(1024,165004),(1024,268588)]),([6,482,13448,26896,28500,32740],[(1024,165004),(1024,268364)]),([6,482,13448,26896,28511,32736],[(1024,1292),(1024,263468),(1024,268588),(1024,273410),(1024,306439)]),([6,482,13448,26896,29088,29115],[(1024,1295),(1024,145570),(1024,165006),(1024,165007)])]
def t180 : BT := .nd (blockTree b184) [6,482,13448,13471,26911,28500] (blockTree b185)
def b186 : List Row := [([6,482,13448,26896,29088,32736],[(1024,1295),(1024,134542),(1024,178306),(1024,273410),(1024,276482),(1024,276770)]),([6,482,13448,26896,29088,32740],[(1024,1295),(1024,134542),(1024,178306),(1024,273410),(1024,276482),(1024,276546)]),([6,482,13448,26896,29115,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,13448,26896,29115,32740],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,13448,26896,29119,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,482,13448,26896,31163,32736],[(1024,164876),(1024,165004),(1024,273410)]),([6,482,13448,26911,28500,32736],[(1024,1292),(1024,164940),(1024,263180),(1024,263335),(1024,268450),(1024,268588),(1024,273410),(1024,306439),(1024,396364)]),([6,482,13448,26911,28511,32736],[(1024,263180),(1024,268588)]),([6,482,13448,26911,29115,32736],[(1024,164879),(1024,263180),(1024,263183),(1024,276482)]),([6,482,13448,27122,29115,32736],[(1024,165007),(1024,178178),(1024,178306)]),([6,482,13448,28500,32152,32736],[(1024,165003),(1024,165004),(1024,268456),(1024,268588)]),([6,482,19319,26896,28500,32736],[(1024,165004),(1024,268588)]),([6,482,19319,26896,29115,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)])]
def b187 : List Row := [([6,482,26896,29115,32152,32736],[(1024,134542),(1024,165004),(1024,165006)]),([6,482,28500,32152,32736],[(1024,134311),(1024,165003),(1024,268292),(1024,396427)]),([6,486,3652,13448,26896,32736],[(1024,66727),(1024,164935)]),([6,490,3652,3679,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,269710)]),([6,490,3652,13448,13471,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,268588)]),([6,490,3652,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([6,498,3652,3679,13448,26896],[(1024,1295),(1024,76930),(1024,132108),(1024,132111),(1024,132172),(1024,132494),(1024,137292),(1024,269710)]),([6,498,3652,13448,26896,26911],[(1024,1167),(1024,14466),(1024,132108),(1024,132111),(1024,142338),(1024,144386)]),([6,498,3652,13448,26896,32736],[(1024,1295),(1024,132172),(1024,132396),(1024,145410),(1024,268588),(1024,269710),(1024,306306)]),([6,498,3679,13448,26896],[(1024,132108),(1024,142338)]),([6,511,3652,3679,13448,13802,26896],[(1024,142728),(1024,145570),(1024,145800)]),([6,511,3652,3679,13448,26896,27122],[(1024,132172),(1024,132494)]),([6,511,3652,3679,13448,26896,32285],[(1024,1295)])]
def t181 : BT := .nd (blockTree b186) [6,482,26896,28500,32152,32736] (blockTree b187)
def t182 : BT := .nd t180 [6,482,13448,26896,29088,29119] t181
def b188 : List Row := [([6,511,3652,13448,13471,26896,32285],[(1024,1199),(1024,1295)]),([6,511,3652,13448,13802,26896,32736],[(1024,164879),(1024,165007)]),([6,511,3652,13448,26896,26911,27122],[(1024,132100),(1024,132111),(1024,132263),(1024,132271)]),([6,511,3652,13448,26896,26911,32285],[(1024,263335),(1024,263468)]),([6,511,3652,13448,26896,27122,32736],[(1024,132396)]),([6,511,3652,13448,26896,32285,32736],[(1024,164879)]),([6,511,3652,13471,13802,26896],[(1024,71842),(1024,132494),(1024,145570),(1024,145794),(1024,263566),(1024,268588),(1024,276482),(1024,276775)]),([6,511,3679,13448,13802,26896],[(1024,132494),(1024,142728),(1024,263468),(1024,269710),(1024,400524)]),([6,511,3679,13448,26896,27122],[(1024,132396),(1024,132494)]),([6,511,3679,13448,26896,32285],[(1024,1295),(1024,134542),(1024,142728),(1024,263468),(1024,276770),(1024,296207)]),([6,1055,1506,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([6,1055,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,142498),(1024,145570)]),([6,1506,3652,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007)])]
def b189 : List Row := [([6,1514,3652,3679,13448,26896],[(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,269710),(1024,276482)]),([6,2048,2530,3679,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,276482),(1024,407556)]),([6,2048,3679,13448,26896,32285],[(1024,1199),(1024,1294),(1024,1295),(1024,145570)]),([6,2079,2530,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([6,2079,3652,13448,26896,32285],[(1024,1294),(1024,1295),(1024,145570)]),([6,2530,3652,3679,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,276482),(1024,407556)]),([6,2530,3652,13448,26896,32736],[(1024,164879),(1024,165006),(1024,165007),(1024,276482)]),([6,2530,3679,13448,26896],[(1024,145570),(1024,145676),(1024,145796),(1024,276482)]),([6,2546,3652,3679,13448,26896],[(1024,1295),(1024,132111),(1024,132494),(1024,269710),(1024,406658)]),([6,3588,3679,13448,26896,32285],[(1024,1294),(1024,1295),(1024,145570)]),([6,3615,3652,13448,26896,32285],[(1024,1294),(1024,1295),(1024,145570)]),([6,3648,13448,26896,32285,32736],[(1024,1295),(1024,165004),(1024,165006),(1024,165007)]),([6,3652,3679,4070,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)])]
def t183 : BT := .nd (blockTree b188) [6,1506,3652,13448,26896,32736] (blockTree b189)
def b190 : List Row := [([6,3652,3679,4095,13448,26896,27122],[(1024,132494)]),([6,3652,3679,4095,13448,26896,32285],[(1024,1294),(1024,1295)]),([6,3652,3679,5871,13448,32285],[(1024,1294),(1024,1295),(1024,132271),(1024,145570)]),([6,3652,3679,8674,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,407556),(1024,407684)]),([6,3652,3679,13448,13802,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178180),(1024,178251),(1024,178306)]),([6,3652,3679,13448,26640,32285],[(1024,134542),(1024,145570),(1024,165007)]),([6,3652,3679,13448,26896,32285],[(1024,1294),(1024,1295),(1024,145570)]),([6,3652,3679,13448,27122,32285],[(1024,132271),(1024,145570)]),([6,3652,3679,19319,26896,32285],[(1024,1294),(1024,1295),(1024,145570)]),([6,3652,3679,26896,32152,32285],[(1024,1294),(1024,134542)]),([6,3652,4070,13448,27122,32736],[(1024,165007),(1024,178178),(1024,178306)]),([6,3652,5871,13448,32285,32736],[(1024,1295),(1024,165004),(1024,165006),(1024,165007),(1024,263183)]),([6,3652,8223,8674,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)])]
def b191 : List Row := [([6,3652,8674,13448,26896,32736],[(1024,164879),(1024,165004),(1024,165007),(1024,276482)]),([6,3652,13448,13471,26911,32285],[(1024,1292),(1024,1295),(1024,14498),(1024,14594)]),([6,3652,13448,13802,27122,32736],[(1024,165004),(1024,165007),(1024,178178),(1024,178306)]),([6,3652,13448,26640,32285,32736],[(1024,145570),(1024,165004),(1024,165006),(1024,165007)]),([6,3652,13448,26880,32285,32736],[(1024,1292),(1024,1294),(1024,1295),(1024,276482)]),([6,3652,13448,26896,29088,32285],[(1024,1294),(1024,1295),(1024,165007)]),([6,3652,13448,26896,32256,32285,32736],[(1024,165007)]),([6,3652,13448,26896,32285,32736],[(1024,1295),(1024,165004),(1024,165006),(1024,165007)]),([6,3652,13448,26896,32285,32740],[(1024,1295),(1024,165004),(1024,165006),(1024,165007)]),([6,3652,13448,26911,32285,32736],[(1024,1295),(1024,164879),(1024,263180),(1024,263183)]),([6,3652,13448,27122,32285,32736],[(1024,1199),(1024,132271),(1024,165007)]),([6,3652,19319,26896,32285,32736],[(1024,1295),(1024,165004),(1024,165006),(1024,165007)]),([6,3652,26896,32152,32285,32736],[(1024,1294),(1024,165004),(1024,165006)])]
def t184 : BT := .nd (blockTree b190) [6,3652,8223,13448,26896,32285] (blockTree b191)
def t185 : BT := .nd t183 [6,3652,3679,4095,13448,13802,26896] t184
def t186 : BT := .nd t182 [6,511,3652,13448,13471,13802,26896] t185
def t187 : BT := .nd t179 [6,482,3908,13448,26896,32736] t186
def t188 : BT := .nd t172 [6,482,3652,13471,13802,26896,32736] t187
def t189 : BT := .nd t157 [6,482,511,13448,26896,26911,28500] t188
def b192 : List Row := [([6,3679,4070,13448,26896,27122],[(1024,132271),(1024,142607),(1024,145570),(1024,165007),(1024,178306),(1024,178316),(1024,275596),(1024,276610),(1024,276620)]),([6,3679,4070,13448,26896,32285],[(1024,1295),(1024,66831),(1024,134542),(1024,145570),(1024,165007),(1024,276482),(1024,276620)]),([6,3679,4070,13448,27122],[(1024,145570),(1024,145796),(1024,178306)]),([6,3679,13448,13471,26896,32285],[(1024,1292),(1024,1295),(1024,276482),(1024,296207)]),([6,3679,13448,16076,26896,32285],[(1024,1199),(1024,1295),(1024,145570)]),([6,3679,13448,26896,29115,32285],[(1024,1294),(1024,1295),(1024,145570)]),([6,3679,13448,26896,32285,32736],[(1024,1292),(1024,1294),(1024,1295),(1024,165007),(1024,276482)]),([6,13448,26896,28500,32285,32736],[(1024,1292),(1024,165004)]),([6,13448,26896,29115,32285,32736],[(1024,1295),(1024,165004),(1024,165006),(1024,165007)]),([7,0,31,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,0,31,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,0,31,482,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([7,0,31,482,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)])]
def b193 : List Row := [([7,0,482,3652,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([7,2,31,482,511,3652,13448,26896],[(1024,145796),(1024,276775)]),([7,2,31,482,3652,5871,13448],[(1024,145570),(1024,145796),(1024,273703),(1024,275751),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,2,31,482,3652,13448,26896],[(1024,134542),(1024,145570),(1024,145796),(1024,268588),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,2,31,482,3652,13448,26898],[(1024,134542),(1024,145666),(1024,145796),(1024,268588),(1024,276610),(1024,276775),(1024,301327),(1024,396431)]),([7,2,31,482,3652,13448,26911],[(1024,14594),(1024,268588),(1024,276482),(1024,276775),(1024,301327)]),([7,2,31,482,3652,13448,27122],[(1024,145570),(1024,145796),(1024,178306),(1024,396431)]),([7,2,31,482,3652,13450,26896],[(1024,134542),(1024,145796),(1024,268588),(1024,276775),(1024,301327),(1024,396431)]),([7,2,31,482,3652,19319,26896],[(1024,145570),(1024,145796),(1024,268588),(1024,275751),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,2,31,482,3652,26896,32152],[(1024,134542),(1024,273703),(1024,275751),(1024,301326),(1024,396430),(1024,406660)]),([7,2,31,482,3654,13448,26896],[(1024,134542),(1024,145796),(1024,268588),(1024,276546),(1024,276775),(1024,301327),(1024,396431)]),([7,2,31,482,3679,13448,26896],[(1024,134542),(1024,268588),(1024,276482),(1024,276487),(1024,276775),(1024,301327)]),([7,2,31,482,13448,26896,28500],[(1024,268588),(1024,273703),(1024,301324),(1024,306439),(1024,396428)])]
def t190 : BT := .nd (blockTree b192) [7,0,31,3652,13448,26896,32285] (blockTree b193)
def b194 : List Row := [([7,2,31,511,3652,13448,26896],[(1024,134542),(1024,145703),(1024,268588),(1024,276775),(1024,301327)]),([7,2,31,3652,13448,26896,32285],[(1024,1295),(1024,71951),(1024,145796),(1024,276775),(1024,301324),(1024,301326),(1024,301327),(1024,396431)]),([7,2,482,511,3652,13448,26896],[(1024,134542),(1024,145796),(1024,268588),(1024,396431)]),([7,2,482,3652,3679,13448,26896],[(1024,71951),(1024,134542),(1024,145570),(1024,145575),(1024,145796),(1024,276482),(1024,396431)]),([7,2,482,3652,13448,26896,32736],[(1024,165007),(1024,276775),(1024,396428),(1024,396430),(1024,396431)]),([7,4,31,482,511,3652,13448,26896],[(1024,66727),(1024,68775),(1024,145703),(1024,178178),(1024,276482)]),([7,4,31,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,4,31,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,4,31,482,3652,13448,26900],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,4,31,482,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([7,4,31,482,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([7,4,31,482,3652,13452,26896],[(1024,1295),(1024,68775),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,4,31,482,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)])]
def b195 : List Row := [([7,4,31,482,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,276482)]),([7,4,31,482,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,4,31,482,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([7,4,31,486,3652,13448,26896],[(1024,1295),(1024,66727),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,4,31,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,4,482,3652,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([7,4,482,3652,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([7,6,31,482,3652,13448,26896],[(1024,66727),(1024,134542),(1024,145570),(1024,145796),(1024,268588),(1024,276482),(1024,276546),(1024,276775),(1024,301327),(1024,396431)]),([7,8,31,482,511,3652,13448,26896],[(1024,178178),(1024,276482)]),([7,8,31,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,8,31,482,3652,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,8,31,482,3652,13448,26904],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,8,31,482,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,269710),(1024,276482)])]
def t191 : BT := .nd (blockTree b194) [7,4,31,482,3652,26896,32152] (blockTree b195)
def t192 : BT := .nd t190 [7,2,31,482,13448,26896,29115] t191
def b196 : List Row := [([7,8,31,482,3652,13471,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,8,31,482,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([7,8,31,482,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,269710),(1024,273410),(1024,275458),(1024,406792)]),([7,8,31,482,3660,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,8,31,482,3679,13448,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,8,31,482,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,8,31,482,13448,26896,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,269710),(1024,273410),(1024,276482)]),([7,8,31,490,3652,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,8,31,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,8,482,3652,3679,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,269710),(1024,276482)]),([7,8,482,3652,13448,13471,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,268588)]),([7,8,482,3652,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([7,10,31,482,3652,13448,13802,26896],[(1024,145570),(1024,145576),(1024,145666),(1024,145796),(1024,145800),(1024,273800),(1024,276775)])]
def b197 : List Row := [([7,12,31,482,3652,13448,26896],[(1024,1295),(1024,68775),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,15,31,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,273410),(1024,275458),(1024,276482),(1024,276775)]),([7,15,31,482,3652,13448,26896],[(1024,1295),(1024,145570),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,16,31,256,482,3652,13448,26896],[(1024,132396),(1024,134444),(1024,142498),(1024,145570),(1024,263468),(1024,268588),(1024,269612),(1024,276482)]),([7,16,31,482,482,3652,13448,26896],[(1024,134444),(1024,142498),(1024,145570),(1024,276482)]),([7,16,31,482,498,3652,13448,26896],[(1024,132396),(1024,276482)]),([7,16,31,482,511,3652,13448,26896],[(1024,132396),(1024,134444),(1024,178178),(1024,276482)]),([7,16,31,482,3652,4070,13448,26896],[(1024,134444),(1024,145570),(1024,276482)]),([7,16,31,482,3652,5871,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([7,16,31,482,3652,13448,13802,26896],[(1024,142498),(1024,145570),(1024,273410),(1024,276482),(1024,276551)]),([7,16,31,482,3652,13448,26896],[(1024,1295),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]),([7,16,31,482,3652,13448,26896,27122],[(1024,142498),(1024,144546),(1024,145570),(1024,276482)]),([7,16,31,482,3652,13448,26896,32285],[(1024,1295),(1024,134444),(1024,142498),(1024,145570),(1024,276482)])]
def t193 : BT := .nd (blockTree b196) [7,10,31,482,3652,13448,26896] (blockTree b197)
def b198 : List Row := [([7,16,31,482,3652,13448,27122],[(1024,178178),(1024,178306)]),([7,16,31,482,3652,13464,26896],[(1024,1295),(1024,134444),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]),([7,16,31,482,3652,19319,26896],[(1024,1295),(1024,263183),(1024,268588),(1024,275458),(1024,276482)]),([7,16,31,482,3652,26896,32152],[(1024,1294),(1024,134542),(1024,269710),(1024,273410),(1024,275458),(1024,406792)]),([7,16,31,482,3668,13448,26896],[(1024,1295),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]),([7,16,31,482,3679,13448,26896],[(1024,1295),(1024,268588),(1024,269710),(1024,276482),(1024,276487)]),([7,16,31,482,13448,26896,28500],[(1024,1292),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]),([7,16,31,482,13448,26896,29115],[(1024,1295),(1024,263183),(1024,269710),(1024,273410),(1024,276482)]),([7,16,31,498,3652,13448,26896],[(1024,1295),(1024,132396),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]),([7,16,31,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,276482)]),([7,16,482,3652,3679,13448,26896],[(1024,1295),(1024,145570),(1024,263183),(1024,269710),(1024,276482)]),([7,16,482,3652,13448,26896,26911],[(1024,1295),(1024,14594),(1024,263180),(1024,263183),(1024,273410),(1024,275458)]),([7,16,482,3652,13448,26896,32736],[(1024,1295),(1024,165007),(1024,268588),(1024,269710),(1024,276482)])]
def b199 : List Row := [([7,18,31,482,3652,13448,26896],[(1024,132396),(1024,178306),(1024,268588),(1024,269710),(1024,276482),(1024,276551),(1024,276610),(1024,276775),(1024,301327)]),([7,18,31,482,3652,13448,26896,27122],[(1024,142724),(1024,144772),(1024,145570),(1024,178306),(1024,276551),(1024,276610),(1024,276775),(1024,276868)]),([7,18,31,482,3652,13448,27122],[(1024,132271),(1024,145796),(1024,178306)]),([7,20,31,482,3652,13448,26896],[(1024,1295),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]),([7,20,31,482,13448,26896,28500],[(1024,1292),(1024,268588),(1024,273410),(1024,306439)]),([7,23,31,482,3652,13448,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,23,31,482,3652,19319,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,275458),(1024,276482),(1024,276775)]),([7,24,31,482,3652,13448,26896],[(1024,1295),(1024,134444),(1024,134542),(1024,263183),(1024,268588),(1024,276482),(1024,276551)]),([7,24,31,482,3652,26896,32152],[(1024,1294),(1024,134542),(1024,269710),(1024,273410),(1024,275458),(1024,406660)]),([7,27,31,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,276482),(1024,276551),(1024,276775)]),([7,27,31,482,13448,26896,29115],[(1024,1295),(1024,134542),(1024,178306),(1024,273410),(1024,276482),(1024,276551),(1024,276775)]),([7,27,482,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276551)]),([7,27,482,3652,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)])]
def t194 : BT := .nd (blockTree b198) [7,16,482,3679,13448,26896] (blockTree b199)
def t195 : BT := .nd t193 [7,16,31,482,3652,13448,26911] t194
def t196 : BT := .nd t192 [7,8,31,482,3652,13448,27122] t195
def b200 : List Row := [([7,29,31,482,3652,13448,26896],[(1024,134542),(1024,268588),(1024,276482),(1024,276775),(1024,301327)]),([7,29,31,482,3652,13448,26896,32285],[(1024,1295),(1024,14498),(1024,142498),(1024,145570),(1024,145796),(1024,276775),(1024,301327)]),([7,29,31,3652,13448,26896,32285],[(1024,1295),(1024,145570),(1024,145796),(1024,276775),(1024,301324),(1024,301326),(1024,301327)]),([7,31,31,256,482,3652,13448,26896],[(1024,145570),(1024,268588),(1024,269612),(1024,276482)]),([7,31,31,482,482,3652,13448,26896],[(1024,14594),(1024,145570),(1024,178306),(1024,276482),(1024,276775)]),([7,31,31,482,511,3652,13448,26896],[(1024,178178),(1024,276482),(1024,276775)]),([7,31,31,482,3652,4070,13448,26896],[(1024,14594),(1024,66727),(1024,145570),(1024,178306),(1024,276482),(1024,276775)]),([7,31,31,482,3652,5871,13448],[(1024,1295),(1024,273410),(1024,275458),(1024,276482),(1024,276775)]),([7,31,31,482,3652,13448,13802,26896],[(1024,14594),(1024,145570),(1024,178306),(1024,273410),(1024,276482),(1024,276775)]),([7,31,31,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,276482),(1024,276775)]),([7,31,31,482,3652,13448,26896,27122],[(1024,145570),(1024,178306),(1024,276482),(1024,276610),(1024,276775)]),([7,31,31,482,3652,13448,26896,32285],[(1024,14594),(1024,132271),(1024,145570),(1024,145796),(1024,276775),(1024,301327)]),([7,31,31,482,3652,13448,26911],[(1024,1295),(1024,178178),(1024,268588),(1024,276482),(1024,276775)])]
def b201 : List Row := [([7,31,31,482,3652,19319,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,275458),(1024,276482),(1024,276775)]),([7,31,31,482,3652,26896,32152],[(1024,1294),(1024,134542),(1024,269710),(1024,273410),(1024,275458),(1024,406660)]),([7,31,31,482,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,276482),(1024,276775)]),([7,31,31,482,13448,26896,28500],[(1024,1292),(1024,268588),(1024,273410),(1024,306439)]),([7,31,31,482,13448,26896,29115],[(1024,1295),(1024,134542),(1024,178306),(1024,273410),(1024,276482),(1024,276775)]),([7,31,31,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145796),(1024,276482),(1024,301327)]),([7,31,64,482,511,3652,13448,26896],[(1024,145796),(1024,178178),(1024,273410),(1024,276482)]),([7,31,64,482,1024,13448,26896],[(1024,1292),(1024,134540),(1024,142498),(1024,165004),(1024,175234),(1024,273410)]),([7,31,64,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,273474),(1024,275458),(1024,276482)]),([7,31,64,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([7,31,64,482,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,273410),(1024,273474),(1024,276482)]),([7,31,64,482,3652,13448,26960],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([7,31,64,482,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,178178),(1024,178306)])]
def t197 : BT := .nd (blockTree b200) [7,31,31,482,3652,13448,27122] (blockTree b201)
def b202 : List Row := [([7,31,64,482,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,275458),(1024,276482)]),([7,31,64,482,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]),([7,31,64,482,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,273410),(1024,276482)]),([7,31,64,482,4070,13448,26896],[(1024,66828),(1024,134542),(1024,145570),(1024,165007),(1024,273410),(1024,273474)]),([7,31,64,482,13448,26896,28500],[(1024,1292),(1024,142498),(1024,165004),(1024,268588),(1024,273410),(1024,273474)]),([7,31,64,482,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([7,31,64,3652,4070,13448,26896],[(1024,1295),(1024,66828),(1024,134542),(1024,165007),(1024,273474),(1024,276482)]),([7,31,64,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,66,482,3652,13448,26896],[(1024,134542),(1024,145570),(1024,145796),(1024,273800),(1024,276482),(1024,276775),(1024,276872),(1024,396431),(1024,400655)]),([7,31,66,482,3679,13448,26896],[(1024,134542),(1024,273800),(1024,276482),(1024,276775),(1024,276872),(1024,400655)]),([7,31,68,482,511,3652,13448,26896],[(1024,66727),(1024,69003),(1024,178178),(1024,273410),(1024,276482)]),([7,31,68,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([7,31,95,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,273410),(1024,273474),(1024,276482),(1024,276551),(1024,276872)])]
def b203 : List Row := [([7,31,128,482,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,128,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,128,482,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([7,31,128,482,3652,13448,27024],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,128,482,3652,13448,27122],[(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([7,31,128,482,3652,13802,26896],[(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,268588)]),([7,31,128,482,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([7,31,128,482,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]),([7,31,128,482,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([7,31,128,482,3780,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,128,482,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,31,128,482,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([7,31,128,3652,13448,13802,26896],[(1024,1295),(1024,165007),(1024,268588),(1024,273410),(1024,276482)])]
def t198 : BT := .nd (blockTree b202) [7,31,128,482,511,3652,13448,26896] (blockTree b203)
def t199 : BT := .nd t197 [7,31,64,482,3652,13512,26896] t198
def b204 : List Row := [([7,31,130,482,3652,13448,26896],[(1024,134542),(1024,145570),(1024,145796),(1024,268588),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,31,136,482,511,3652,13448,26896],[(1024,178178),(1024,275458),(1024,276482)]),([7,31,136,482,3652,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([7,31,159,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,276482),(1024,276775)]),([7,31,192,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([7,31,226,482,3652,5871,13448],[(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,276482),(1024,276775),(1024,276872)]),([7,31,226,482,3652,13448,26896],[(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,276482),(1024,276775),(1024,276872)]),([7,31,256,287,482,3652,13448,26896],[(1024,145570),(1024,263468)]),([7,31,256,482,511,3652,13448,26896],[(1024,145570),(1024,178178),(1024,263468),(1024,268588),(1024,269612)]),([7,31,256,482,3652,3679,13448,26896],[(1024,145570),(1024,269612),(1024,276482)]),([7,31,256,482,3652,5871,13448],[(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([7,31,256,482,3652,13448,13471,26896],[(1024,145570),(1024,268588),(1024,276482)]),([7,31,256,482,3652,13448,26896],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,276482)])]
def b205 : List Row := [([7,31,256,482,3652,13448,26896,32736],[(1024,145570),(1024,165007),(1024,268588),(1024,269612),(1024,276482)]),([7,31,256,482,3652,13448,26911],[(1024,14594),(1024,178178),(1024,276482)]),([7,31,256,482,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([7,31,256,482,3652,13704,26896],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,269612),(1024,275458)]),([7,31,256,482,3652,19319,26896],[(1024,132271),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,256,482,3652,26896,32152],[(1024,134542),(1024,142498),(1024,144546),(1024,165006),(1024,275458),(1024,406660)]),([7,31,256,482,3679,13448,26896],[(1024,132271),(1024,134542),(1024,178306),(1024,276482)]),([7,31,256,482,3908,13448,26896],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410)]),([7,31,256,482,13448,26896,28500],[(1024,142498),(1024,165004),(1024,268588),(1024,273410)]),([7,31,256,482,13448,26896,29115],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,256,3652,13448,26896,27122],[(1024,132271),(1024,142498),(1024,144546),(1024,165007),(1024,178306)]),([7,31,256,3652,13448,26896,32285],[(1024,1295),(1024,134542),(1024,142498),(1024,145570),(1024,165007)]),([7,31,258,482,3652,13448,26896],[(1024,14594),(1024,134542),(1024,142724),(1024,145570),(1024,145666),(1024,145796),(1024,263468),(1024,276482),(1024,276775),(1024,396431)])]
def t200 : BT := .nd (blockTree b204) [7,31,256,482,3652,13448,26896,26911] (blockTree b205)
def b206 : List Row := [([7,31,258,482,3652,13448,26911],[(1024,11522),(1024,14594),(1024,263183),(1024,276482),(1024,276775)]),([7,31,272,482,511,3652,13448,26896],[(1024,132396),(1024,134444),(1024,178178),(1024,263468),(1024,268588)]),([7,31,272,482,3652,13448,26896],[(1024,145570),(1024,276482)]),([7,31,287,482,3652,13448,26896],[(1024,132271),(1024,134542),(1024,145796),(1024,178306),(1024,263468),(1024,276482)]),([7,31,320,482,3652,13448,26896],[(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,320,482,13448,26896,28500],[(1024,142498),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,31,354,482,3652,13448,26896],[(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,276775),(1024,276872)]),([7,31,354,482,3652,19319,26896],[(1024,14594),(1024,144546),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,276775),(1024,276872)]),([7,31,384,482,3652,13448,26896],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,269612),(1024,276482)]),([7,31,384,482,3652,26896,32152],[(1024,134542),(1024,142498),(1024,144546),(1024,165006),(1024,275458),(1024,406660)]),([7,31,418,482,3652,13448,26896],[(1024,14594),(1024,71842),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,276482),(1024,276775)]),([7,31,418,482,13448,26896,29115],[(1024,14594),(1024,71842),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,276482),(1024,276775)]),([7,31,480,482,3652,13448,26896],[(1024,66727),(1024,134542),(1024,145570),(1024,145796),(1024,268588),(1024,276482),(1024,276775),(1024,396431)])]
def b207 : List Row := [([7,31,482,482,511,3652,13448,26896],[(1024,14498),(1024,145570),(1024,145796)]),([7,31,482,482,3652,3679,13448,26896],[(1024,145570),(1024,145796),(1024,178306),(1024,276482),(1024,276872)]),([7,31,482,482,3652,5871,13448],[(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,276482),(1024,276775)]),([7,31,482,482,3652,13448,13471,26896],[(1024,14594),(1024,145570),(1024,178306),(1024,276482),(1024,276775)]),([7,31,482,482,3652,13448,26896],[(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,482,3652,13448,26896,26911],[(1024,14594),(1024,145570),(1024,145796),(1024,268588),(1024,276482),(1024,276610)]),([7,31,482,482,3652,13448,26896,32736],[(1024,145570),(1024,145796),(1024,178306),(1024,263183),(1024,276482),(1024,276775),(1024,396431)]),([7,31,482,482,3652,13448,26911],[(1024,14498),(1024,14594),(1024,263183),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,482,3652,13448,27122],[(1024,14498),(1024,145570),(1024,145796),(1024,165007),(1024,178306)]),([7,31,482,482,3652,19319,26896],[(1024,14594),(1024,144546),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,482,3652,26896,32152],[(1024,134542),(1024,142498),(1024,144546),(1024,165006),(1024,406660)]),([7,31,482,482,3679,13448,26896],[(1024,134542),(1024,268588),(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,482,13448,26896,28500],[(1024,142498),(1024,165004),(1024,268588),(1024,306439)])]
def t201 : BT := .nd (blockTree b206) [7,31,480,482,3652,13448,26896,32736] (blockTree b207)
def t202 : BT := .nd t200 [7,31,258,482,3652,13448,26896,26911] t201
def t203 : BT := .nd t199 [7,31,128,3652,13448,26896,32285] t202
def t204 : BT := .nd t196 [7,27,482,13448,26896,29115] t203
def b208 : List Row := [([7,31,482,486,3652,13448,26896],[(1024,14594),(1024,66727),(1024,66955),(1024,134542),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,490,3652,13448,26896],[(1024,14594),(1024,145570),(1024,165007),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,31,482,498,3652,13448,26896],[(1024,14594),(1024,132396),(1024,145570),(1024,263183),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,31,482,511,511,3652,13448,26896],[]),([7,31,482,511,1024,3652,13448,26896],[(1024,178178),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,511,2048,3652,13448,26896],[(1024,178178),(1024,276482)]),([7,31,482,511,3652,3652,13448,26896],[(1024,66727),(1024,178178),(1024,276482)]),([7,31,482,511,3652,3679,13448,26896],[(1024,178178),(1024,276482),(1024,276872)]),([7,31,482,511,3652,4070,13448,26896],[(1024,14498),(1024,66727),(1024,145570),(1024,145796)]),([7,31,482,511,3652,4095,13448,26896],[(1024,76962),(1024,273410)]),([7,31,482,511,3652,5871,13448],[(1024,66727),(1024,145570),(1024,145796),(1024,276482),(1024,276775)]),([7,31,482,511,3652,5871,13448,26896],[(1024,276482),(1024,306439),(1024,406660)]),([7,31,482,511,3652,8192,13448,26896],[(1024,178178),(1024,276482)])]
def b209 : List Row := [([7,31,482,511,3652,13448,13471,26896],[(1024,178178),(1024,276482),(1024,276775)]),([7,31,482,511,3652,13448,13802,26896],[(1024,14498),(1024,145570),(1024,145796)]),([7,31,482,511,3652,13448,13823,26896],[(1024,275458)]),([7,31,482,511,3652,13448,16076,26896],[(1024,66727),(1024,69003),(1024,178178),(1024,276482),(1024,407556)]),([7,31,482,511,3652,13448,19319,26896],[(1024,178178),(1024,276482)]),([7,31,482,511,3652,13448,26896],[(1024,66727),(1024,134542),(1024,145570),(1024,145796),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,511,3652,13448,26896,26896],[(1024,134542),(1024,268588),(1024,276482)]),([7,31,482,511,3652,13448,26896,26911],[(1024,145703),(1024,268588),(1024,276482)]),([7,31,482,511,3652,13448,26896,27122],[(1024,145570),(1024,145796),(1024,178306),(1024,276482)]),([7,31,482,511,3652,13448,26896,27135],[(1024,178178),(1024,276482)]),([7,31,482,511,3652,13448,26896,28500],[(1024,66727),(1024,132396),(1024,134542),(1024,263468),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,511,3652,13448,26896,29115],[(1024,71842),(1024,170050),(1024,178178),(1024,276482)]),([7,31,482,511,3652,13448,26896,32152],[(1024,132494),(1024,134542),(1024,263566),(1024,268588),(1024,269710),(1024,275458),(1024,276482)])]
def t205 : BT := .nd (blockTree b208) [7,31,482,511,3652,13448,13448,26896] (blockTree b209)
def b210 : List Row := [([7,31,482,511,3652,13448,26896,32285],[(1024,14498),(1024,145570),(1024,145796),(1024,276482),(1024,276775)]),([7,31,482,511,3652,13448,26896,32736],[(1024,145796),(1024,178178),(1024,276482),(1024,276775)]),([7,31,482,511,3652,13448,26911],[(1024,14594),(1024,66727),(1024,77058),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,511,3652,13448,27122],[(1024,145570),(1024,145796),(1024,178306)]),([7,31,482,511,3652,13448,27135],[(1024,14498),(1024,66727),(1024,76962),(1024,178178)]),([7,31,482,511,3652,19319,26896],[(1024,66727),(1024,145570),(1024,145796),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,511,3652,26896,32152],[(1024,134542),(1024,275458),(1024,406660)]),([7,31,482,511,3679,13448,26896],[(1024,134542),(1024,268588),(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,511,13448,26896,28500],[(1024,66727),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,511,13448,26896,29115],[(1024,71842),(1024,134542),(1024,145570),(1024,145796),(1024,276482),(1024,276775)]),([7,31,482,615,3652,13448,26896],[(1024,1295),(1024,134542),(1024,134543),(1024,145570),(1024,165007),(1024,269710),(1024,273410),(1024,276482),(1024,276872),(1024,407684)]),([7,31,482,615,3652,26896],[(1024,134542),(1024,144546),(1024,269710),(1024,275458)]),([7,31,482,615,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)])]
def b211 : List Row := [([7,31,482,1024,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,1024,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,1024,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,178178),(1024,178306)]),([7,31,482,1024,3652,13448,27920],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,1024,3652,16076,26896],[(1024,1295),(1024,134444),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,407556)]),([7,31,482,1024,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,1024,3652,26896,32152],[(1024,1294),(1024,134444),(1024,134540),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]),([7,31,482,1024,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,273800),(1024,276482)]),([7,31,482,1024,13448,16076,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482),(1024,309415)]),([7,31,482,1024,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,1024,13448,26896,29115],[(1024,1295),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([7,31,482,1028,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,1032,3652,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,273410),(1024,275458),(1024,276482)])]
def t206 : BT := .nd (blockTree b210) [7,31,482,1024,3652,5871,13448] (blockTree b211)
def t207 : BT := .nd t205 [7,31,482,511,3652,13448,26896,32256] t206
def b212 : List Row := [([7,31,482,1055,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,178306),(1024,268588),(1024,273410),(1024,276482),(1024,276775)]),([7,31,482,1088,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([7,31,482,1088,13448,13802,26896],[(1024,11522),(1024,142498),(1024,165004),(1024,269710),(1024,273410),(1024,273800)]),([7,31,482,1088,13448,26896],[(1024,142498),(1024,273410),(1024,273800)]),([7,31,482,1152,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,1506,3652,13448,26896],[(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,1604,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,178178),(1024,273410),(1024,273703),(1024,275458),(1024,276482)]),([7,31,482,1604,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273703),(1024,276482),(1024,407556)]),([7,31,482,1604,5871,13448],[(1024,142498),(1024,273410),(1024,273703)]),([7,31,482,1604,5871,13448,26896],[(1024,1292),(1024,142498),(1024,165004),(1024,273410)]),([7,31,482,1604,13448,26896],[(1024,142498),(1024,273410),(1024,273703)]),([7,31,482,2048,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482),(1024,309415)]),([7,31,482,2048,3652,8192,13448],[(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,309415),(1024,407556)])]
def b213 : List Row := [([7,31,482,2048,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268591),(1024,276482),(1024,309511),(1024,407720)]),([7,31,482,2048,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,309415),(1024,407556)]),([7,31,482,2048,3652,13448,28500],[(1024,1295),(1024,145570),(1024,165007),(1024,268591),(1024,309415),(1024,309511),(1024,407556)]),([7,31,482,2048,3652,15496,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([7,31,482,2048,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,275458),(1024,276482),(1024,309415),(1024,309511)]),([7,31,482,2048,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,275458),(1024,406660)]),([7,31,482,2048,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,145575),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([7,31,482,2048,13448,26896,28500],[(1024,1295),(1024,165007),(1024,268588),(1024,268591),(1024,273410),(1024,275458),(1024,309511)]),([7,31,482,2048,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,170287),(1024,178306),(1024,276482)]),([7,31,482,2052,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([7,31,482,2052,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268591),(1024,276482),(1024,309511),(1024,407720)]),([7,31,482,2064,3652,13448,26896],[(1024,1295),(1024,263183),(1024,268591),(1024,269710),(1024,276482),(1024,309511),(1024,407556)]),([7,31,482,2064,3679,13448,26896],[(1024,1295),(1024,268591),(1024,269710),(1024,276482),(1024,309511),(1024,407556)])]
def t208 : BT := .nd (blockTree b212) [7,31,482,2048,3652,13448,26896] (blockTree b213)
def b214 : List Row := [([7,31,482,2112,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,407556)]),([7,31,482,2112,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,407556)]),([7,31,482,2304,3652,13448,26896],[(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482),(1024,407556)]),([7,31,482,2530,3652,13448,26896],[(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,268591),(1024,276482),(1024,276775),(1024,309511),(1024,407556)]),([7,31,482,2628,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,482,2628,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,275458),(1024,276482)]),([7,31,482,3072,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([7,31,482,3072,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,275458),(1024,406660)]),([7,31,482,3588,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3648,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,482,3648,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,3648,13448,26896,32736],[(1024,1295),(1024,134542),(1024,145796),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,276775),(1024,396431)]),([7,31,482,3652,3652,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482)])]
def b215 : List Row := [([7,31,482,3652,3652,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,276482)]),([7,31,482,3652,3652,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([7,31,482,3652,3652,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,275458),(1024,276482)]),([7,31,482,3652,3652,26896,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,275458),(1024,406660)]),([7,31,482,3652,3654,13448,26896],[(1024,134542),(1024,145570),(1024,145796),(1024,276482),(1024,276546),(1024,276775),(1024,276872),(1024,301327),(1024,396431)]),([7,31,482,3652,3660,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,269710),(1024,276482)]),([7,31,482,3652,3668,13448,26896],[(1024,1295),(1024,263183),(1024,269710),(1024,276482)]),([7,31,482,3652,3679,4070,13448,26896],[(1024,145570),(1024,145796),(1024,178306),(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3652,3679,4095,13448,26896],[(1024,275458),(1024,276482),(1024,276872)]),([7,31,482,3652,3679,5871,13448],[(1024,1295),(1024,145570),(1024,145796),(1024,275458),(1024,276482),(1024,276872)]),([7,31,482,3652,3679,13448,13802,26896],[(1024,145570),(1024,178306),(1024,276482),(1024,276551),(1024,276872)]),([7,31,482,3652,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,178306),(1024,276482),(1024,276872)]),([7,31,482,3652,3679,13448,26896,27122],[(1024,145570),(1024,145666),(1024,178306),(1024,276482),(1024,276546),(1024,276551),(1024,276610),(1024,276872)])]
def t209 : BT := .nd (blockTree b214) [7,31,482,3652,3652,13448,26896] (blockTree b215)
def t210 : BT := .nd t208 [7,31,482,2079,3652,13448,26896] t209
def t211 : BT := .nd t207 [7,31,482,1032,3679,13448,26896] t210
def b216 : List Row := [([7,31,482,3652,3679,13448,26911],[(1024,1295),(1024,14594),(1024,77058),(1024,178178),(1024,276482),(1024,276872)]),([7,31,482,3652,3679,13448,27122],[(1024,132271),(1024,145570),(1024,145796),(1024,178178),(1024,178306)]),([7,31,482,3652,3679,19319,26896],[(1024,1295),(1024,145570),(1024,145796),(1024,178306),(1024,275458),(1024,276482),(1024,276872)]),([7,31,482,3652,3679,26896,32152],[(1024,1294),(1024,134542),(1024,269710),(1024,275458),(1024,406660)]),([7,31,482,3652,3780,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,482,3652,3908,13448,26896],[(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,268686),(1024,273410),(1024,276482)]),([7,31,482,3652,4070,4095,13448,26896],[(1024,144546),(1024,145570),(1024,145796)]),([7,31,482,3652,4070,5871,13448],[(1024,66727),(1024,144546),(1024,145570),(1024,165007),(1024,273474),(1024,273703),(1024,276482),(1024,276775)]),([7,31,482,3652,4070,13448,13471,26896],[(1024,14594),(1024,66727),(1024,68775),(1024,69003),(1024,71842),(1024,145570),(1024,178306),(1024,276482),(1024,276775)]),([7,31,482,3652,4070,13448,26896],[(1024,14594),(1024,66727),(1024,134542),(1024,145570),(1024,165007),(1024,268588),(1024,273474),(1024,276482),(1024,276775)]),([7,31,482,3652,4070,13448,26896,26911],[(1024,14594),(1024,71842),(1024,145570),(1024,145575),(1024,145796),(1024,263244),(1024,268588),(1024,276482),(1024,276610)]),([7,31,482,3652,4070,13448,26896,32736],[(1024,66727),(1024,145570),(1024,145796),(1024,164935),(1024,178306),(1024,263183),(1024,276482),(1024,276775),(1024,396431)]),([7,31,482,3652,4070,13448,26911],[(1024,14498),(1024,14594),(1024,66727),(1024,77058),(1024,263183),(1024,268588),(1024,273474),(1024,276482),(1024,276775)])]
def b217 : List Row := [([7,31,482,3652,4070,19319,26896],[(1024,14594),(1024,66727),(1024,144546),(1024,145570),(1024,165007),(1024,268588),(1024,273474),(1024,276482),(1024,276775)]),([7,31,482,3652,4070,26896,32152],[(1024,134542),(1024,144546),(1024,165006),(1024,273703),(1024,275751),(1024,406660)]),([7,31,482,3652,4095,13448,26896],[(1024,77058),(1024,134542),(1024,145570),(1024,145796),(1024,263244),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,3652,4267,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,268588),(1024,268591),(1024,273410),(1024,275458),(1024,276482),(1024,276775),(1024,309511)]),([7,31,482,3652,5256,5871],[(1024,144546),(1024,275458),(1024,275751)]),([7,31,482,3652,5256,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,178178),(1024,273410),(1024,275458),(1024,275848),(1024,276482)]),([7,31,482,3652,5256,5871,26896],[(1024,1294),(1024,144546),(1024,165006),(1024,273410),(1024,275458)]),([7,31,482,3652,5256,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,275848),(1024,276482),(1024,309415)]),([7,31,482,3652,5256,26896],[(1024,144546),(1024,275458),(1024,275751)]),([7,31,482,3652,5645,13448],[(1024,145570),(1024,145796),(1024,178306)]),([7,31,482,3652,5645,13448,26896],[(1024,132271),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,276610),(1024,276775),(1024,276872)]),([7,31,482,3652,5645,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([7,31,482,3652,5856,13448],[(1024,14594),(1024,276482),(1024,276775)])]
def t212 : BT := .nd (blockTree b216) [7,31,482,3652,4070,13448,27122] (blockTree b217)
def b218 : List Row := [([7,31,482,3652,5856,13448,26911],[(1024,1295),(1024,14594),(1024,263183),(1024,273410),(1024,276482)]),([7,31,482,3652,5871,5871,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,5871,5887,13448],[(1024,1295),(1024,145570),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,5871,6127,13448],[(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([7,31,482,3652,5871,7919,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482)]),([7,31,482,3652,5871,8192,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482),(1024,407556)]),([7,31,482,3652,5871,13448],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,3652,5871,13448,13448],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482)]),([7,31,482,3652,5871,13448,13471],[(1024,1295),(1024,69003),(1024,145570),(1024,273410),(1024,276482),(1024,276775)]),([7,31,482,3652,5871,13448,13802],[(1024,142498),(1024,145570),(1024,165007),(1024,275848),(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3652,5871,13448,14063],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482)]),([7,31,482,3652,5871,13448,16076],[(1024,1295),(1024,69003),(1024,145570),(1024,165007),(1024,178178),(1024,276482)]),([7,31,482,3652,5871,13448,19319],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482)])]
def b219 : List Row := [([7,31,482,3652,5871,13448,26911],[(1024,1295),(1024,145666),(1024,145796),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,5871,13448,27122],[(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,276610),(1024,276775),(1024,276872)]),([7,31,482,3652,5871,13448,28500],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482),(1024,276775),(1024,306439)]),([7,31,482,3652,5871,13448,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482)]),([7,31,482,3652,5871,13448,32152],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482),(1024,276872),(1024,406660),(1024,406792)]),([7,31,482,3652,5871,13448,32285],[(1024,1295),(1024,142498),(1024,144546),(1024,145570),(1024,145796),(1024,165007),(1024,276482),(1024,276775),(1024,301327)]),([7,31,482,3652,5871,13448,32736],[(1024,1295),(1024,145796),(1024,165007),(1024,273410),(1024,275458),(1024,276482),(1024,276775),(1024,396431)]),([7,31,482,3652,5871,13448,32767],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,5871,19319],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,3652,5871,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,5871,26896,32152],[(1024,1294),(1024,134542),(1024,144546),(1024,165006),(1024,269710),(1024,273410),(1024,275458),(1024,406660),(1024,406792)]),([7,31,482,3652,5871,32152],[(1024,144546),(1024,275458),(1024,406660),(1024,406792)]),([7,31,482,3652,5887,13448],[(1024,276482),(1024,276775)])]
def t213 : BT := .nd (blockTree b218) [7,31,482,3652,5871,13448,26896] (blockTree b219)
def t214 : BT := .nd t212 [7,31,482,3652,5856,13448,26896] t213
def b220 : List Row := [([7,31,482,3652,6127,13448],[(1024,145570),(1024,145796)]),([7,31,482,3652,6127,13448,26896],[(1024,142498),(1024,144546),(1024,145570),(1024,145666),(1024,165007),(1024,276482)]),([7,31,482,3652,7919,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482)]),([7,31,482,3652,8192,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([7,31,482,3652,8192,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482),(1024,407556)]),([7,31,482,3652,8192,13448,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,407556),(1024,407684)]),([7,31,482,3652,8192,13448,32152],[(1024,1295),(1024,134543),(1024,165007),(1024,407556),(1024,407684)]),([7,31,482,3652,8192,19319,26896],[(1024,1295),(1024,3471),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,8192,26896,32152],[(1024,1295),(1024,134542),(1024,134543),(1024,165007),(1024,273410),(1024,275458),(1024,407684)]),([7,31,482,3652,8200,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269711),(1024,276482),(1024,407720),(1024,407816)]),([7,31,482,3652,8200,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,269711),(1024,276482),(1024,407720),(1024,407816)]),([7,31,482,3652,8208,13448,26896],[(1024,1295),(1024,263183),(1024,268588),(1024,269711),(1024,276482),(1024,407556),(1024,407816)]),([7,31,482,3652,8223,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,145796),(1024,178306),(1024,268588),(1024,276482),(1024,276775),(1024,407556),(1024,407684)])]
def b221 : List Row := [([7,31,482,3652,8320,13448,27122],[(1024,132271),(1024,134543),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,407556),(1024,407684)]),([7,31,482,3652,8448,13448,26896],[(1024,132271),(1024,134543),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,275458),(1024,276482),(1024,407556),(1024,407684)]),([7,31,482,3652,8674,13448,26896],[(1024,14594),(1024,134543),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,276775),(1024,407556),(1024,407684)]),([7,31,482,3652,9216,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482),(1024,407556),(1024,407684)]),([7,31,482,3652,10240,13448],[(1024,178178),(1024,309415),(1024,407556),(1024,407720)]),([7,31,482,3652,10240,13448,16076],[(1024,1199),(1024,14498),(1024,69003),(1024,164879),(1024,178178),(1024,309415),(1024,407556),(1024,407720)]),([7,31,482,3652,10240,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556),(1024,407684)]),([7,31,482,3652,11844,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,407556),(1024,407684)]),([7,31,482,3652,12424,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,3652,13320,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,31,482,3652,13440,13448,26896],[(1024,1295),(1024,69003),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,13448,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)])]
def t215 : BT := .nd (blockTree b220) [7,31,482,3652,8320,13448,26896] (blockTree b221)
def b222 : List Row := [([7,31,482,3652,13448,13450,26896],[(1024,145570),(1024,145796),(1024,268588),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,31,482,3652,13448,13452,26896],[(1024,1295),(1024,68775),(1024,69003),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,13464,26896],[(1024,1295),(1024,134444),(1024,134542),(1024,263183),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,13471,13802,26896],[(1024,14594),(1024,145570),(1024,178306),(1024,273410),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,13471,13823,26896],[(1024,273410),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,13471,26896],[(1024,1295),(1024,69003),(1024,134542),(1024,145570),(1024,178306),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,13471,26896,27122],[(1024,134542),(1024,145570),(1024,145666),(1024,178306),(1024,276482),(1024,276484),(1024,276610),(1024,276775),(1024,276868)]),([7,31,482,3652,13448,13471,26896,32285],[(1024,14594),(1024,132271),(1024,145570),(1024,145796),(1024,276482),(1024,276775),(1024,301327)]),([7,31,482,3652,13448,13471,26911],[(1024,1295),(1024,14594),(1024,69003),(1024,178178),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,13471,27122],[(1024,69003),(1024,132271),(1024,134542),(1024,145570),(1024,145796),(1024,178178),(1024,178306)]),([7,31,482,3652,13448,13512,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([7,31,482,3652,13448,13704,26896],[(1024,132271),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,269612),(1024,269710),(1024,275458),(1024,276482)]),([7,31,482,3652,13448,13802,13823,26896],[(1024,142498),(1024,145570)])]
def b223 : List Row := [([7,31,482,3652,13448,13802,26896,26911],[(1024,14594),(1024,145570),(1024,145576),(1024,145800),(1024,268588),(1024,269710),(1024,273410),(1024,276482),(1024,276610)]),([7,31,482,3652,13448,13802,26896,32736],[(1024,145570),(1024,145796),(1024,178306),(1024,263183),(1024,273410),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,13802,26911],[(1024,11522),(1024,14498),(1024,14594),(1024,263183),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,13802,27122],[(1024,14498),(1024,142498),(1024,145570),(1024,145796),(1024,165007),(1024,178306)]),([7,31,482,3652,13448,13823,26896],[(1024,66727),(1024,69003),(1024,134542),(1024,145570),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,14063,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482)]),([7,31,482,3652,13448,15496,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309415),(1024,309511)]),([7,31,482,3652,13448,16076,26896],[(1024,1295),(1024,69003),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,276482)]),([7,31,482,3652,13448,16076,26911],[(1024,1295),(1024,14594),(1024,69003),(1024,178178),(1024,263183),(1024,276482)]),([7,31,482,3652,13448,16076,27122],[(1024,69003),(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([7,31,482,3652,13448,16095,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,178178),(1024,178306),(1024,276482)]),([7,31,482,3652,13448,16366,26896],[(1024,14498),(1024,14594),(1024,66727),(1024,68775),(1024,145570),(1024,165007),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,16691,26896],[(1024,1295),(1024,69003),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,276482)])]
def t216 : BT := .nd (blockTree b222) [7,31,482,3652,13448,13802,26896] (blockTree b223)
def t217 : BT := .nd t215 [7,31,482,3652,13448,13448,27122] t216
def t218 : BT := .nd t214 [7,31,482,3652,5887,13448,26896] t217
def t219 : BT := .nd t211 [7,31,482,3652,3679,13448,26896,32285] t218
def t220 : BT := .nd t204 [7,31,482,482,13448,26896,29115] t219
def b224 : List Row := [([7,31,482,3652,13448,18965,26896],[(1024,1295),(1024,14594),(1024,142498),(1024,145570),(1024,165007),(1024,268588),(1024,269710),(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3652,13448,19296,26896],[(1024,1295),(1024,69003),(1024,134542),(1024,145796),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,19319,26911],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,19319,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([7,31,482,3652,13448,19327,26896],[(1024,1295),(1024,69003),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,19447,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,31,482,3652,13448,20343,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,3652,13448,24575,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([7,31,482,3652,13448,24848,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482)]),([7,31,482,3652,13448,26640],[(1024,145570),(1024,145796)]),([7,31,482,3652,13448,26640,26896],[(1024,142498),(1024,144546),(1024,145570),(1024,145666),(1024,165007),(1024,276482)]),([7,31,482,3652,13448,26640,32285],[(1024,134542),(1024,142498),(1024,145570),(1024,145796),(1024,165007)])]
def b225 : List Row := [([7,31,482,3652,13448,26880,26896],[(1024,1295),(1024,145570),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]),([7,31,482,3652,13448,26880,32736],[(1024,1295),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26896,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,13448,26896,26898],[(1024,145570),(1024,145796),(1024,273703),(1024,275751),(1024,276482),(1024,276610),(1024,276775),(1024,301327),(1024,396431)]),([7,31,482,3652,13448,26896,26900],[(1024,1295),(1024,76962),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,13448,26896,26904],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,13448,26896,26911],[(1024,1295),(1024,145796),(1024,263183),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]),([7,31,482,3652,13448,26896,26911,27122],[(1024,145570),(1024,145796),(1024,276482),(1024,276610),(1024,276775)]),([7,31,482,3652,13448,26896,26911,32285],[(1024,1295),(1024,14594),(1024,132367),(1024,145570),(1024,145666),(1024,145796),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26896,26960],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,273474),(1024,275458),(1024,276482)]),([7,31,482,3652,13448,26896,27024],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,13448,26896,27122],[(1024,132271),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,276610),(1024,276775),(1024,276872)])]
def t221 : BT := .nd (blockTree b224) [7,31,482,3652,13448,26880] (blockTree b225)
def b226 : List Row := [([7,31,482,3652,13448,26896,27135],[(1024,1295),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,13448,26896,27511],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,275848),(1024,276482),(1024,309415)]),([7,31,482,3652,13448,26896,27920],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,13448,26896,28500],[(1024,1295),(1024,145570),(1024,165007),(1024,268588),(1024,268591),(1024,273410),(1024,275458),(1024,276482),(1024,276775),(1024,309511)]),([7,31,482,3652,13448,26896,28511],[(1024,1295),(1024,145796),(1024,263183),(1024,263468),(1024,268588),(1024,268591),(1024,273410),(1024,275458),(1024,276482),(1024,276610),(1024,309511)]),([7,31,482,3652,13448,26896,28662],[(1024,132396),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273474),(1024,275751),(1024,276482),(1024,276546),(1024,276610),(1024,276775),(1024,301327),(1024,309415)]),([7,31,482,3652,13448,26896,28697],[(1024,1295),(1024,14594),(1024,66727),(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,268588),(1024,273474),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26896,29088],[(1024,1295),(1024,134542),(1024,145796),(1024,165007),(1024,178306),(1024,276482),(1024,276872),(1024,396431)]),([7,31,482,3652,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,482,3652,13448,26896,29119],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,482,3652,13448,26896,29179],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,26896,30139],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,482,3652,13448,26896,30719],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)])]
def b227 : List Row := [([7,31,482,3652,13448,26896,31743],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,3652,13448,26896,32152],[(1024,1295),(1024,134542),(1024,134543),(1024,145570),(1024,165007),(1024,269710),(1024,273410),(1024,276482),(1024,276872),(1024,407684)]),([7,31,482,3652,13448,26896,32159],[(1024,1295),(1024,69003),(1024,134542),(1024,145796),(1024,263566),(1024,269710),(1024,273410),(1024,276482),(1024,276610),(1024,396431),(1024,407556)]),([7,31,482,3652,13448,26896,32250],[(1024,132494),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273800),(1024,276482),(1024,276610),(1024,276775),(1024,276872),(1024,400655),(1024,407684)]),([7,31,482,3652,13448,26896,32256],[(1024,66727),(1024,134542),(1024,145796),(1024,268588),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,31,482,3652,13448,26896,32285],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,268588),(1024,276482),(1024,276775),(1024,301327)]),([7,31,482,3652,13448,26896,32285,32736],[(1024,132271),(1024,145570),(1024,145796),(1024,263183),(1024,276775),(1024,301327),(1024,396431)]),([7,31,482,3652,13448,26896,32287],[(1024,66727),(1024,134542),(1024,145570),(1024,145796),(1024,268588),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,31,482,3652,13448,26896,32349],[(1024,1295),(1024,14594),(1024,71842),(1024,134542),(1024,142498),(1024,145570),(1024,145796),(1024,165007),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26896,32413],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,268588),(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3652,13448,26896,32511],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,482,3652,13448,26896,32541],[(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3652,13448,26896,32639],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)])]
def t222 : BT := .nd (blockTree b226) [7,31,482,3652,13448,26896,31163] (blockTree b227)
def t223 : BT := .nd t221 [7,31,482,3652,13448,26896,27122,32736] t222
def b228 : List Row := [([7,31,482,3652,13448,26896,32732],[(1024,1295),(1024,134444),(1024,134542),(1024,145570),(1024,165007),(1024,268588),(1024,269612),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26896,32736],[(1024,1295),(1024,134542),(1024,145796),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,276775),(1024,396431)]),([7,31,482,3652,13448,26896,32738],[(1024,134542),(1024,145570),(1024,268588),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,31,482,3652,13448,26896,32740],[(1024,1295),(1024,134542),(1024,145796),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,276775),(1024,396431)]),([7,31,482,3652,13448,26896,32744],[(1024,1295),(1024,145796),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26896,32751],[(1024,1295),(1024,145570),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]),([7,31,482,3652,13448,26896,32752],[(1024,1295),(1024,145796),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26896,32759],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482)]),([7,31,482,3652,13448,26896,32763],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,26896,32765],[(1024,134542),(1024,145796),(1024,268588),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,31,482,3652,13448,26896,32767],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,13448,26898],[(1024,145666),(1024,276610),(1024,276775)]),([7,31,482,3652,13448,26900],[(1024,76962),(1024,276482),(1024,276775)])]
def b229 : List Row := [([7,31,482,3652,13448,26911],[(1024,14594),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26911,26911],[(1024,1295),(1024,14594),(1024,263183),(1024,273410),(1024,276482)]),([7,31,482,3652,13448,26911,27122],[(1024,14594),(1024,132367),(1024,145666),(1024,178306),(1024,263311),(1024,273538),(1024,276482),(1024,276610)]),([7,31,482,3652,13448,26911,27135],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,273410),(1024,276482)]),([7,31,482,3652,13448,26911,28500],[(1024,1295),(1024,263183),(1024,268588),(1024,268591),(1024,273410),(1024,276482),(1024,276610),(1024,309511)]),([7,31,482,3652,13448,26911,28511],[(1024,1295),(1024,14594),(1024,263183),(1024,268588),(1024,268591),(1024,273410),(1024,276482),(1024,309511)]),([7,31,482,3652,13448,26911,29115],[(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,276482)]),([7,31,482,3652,13448,26911,32152],[(1024,1295),(1024,263183),(1024,269710),(1024,269711),(1024,273410),(1024,276482),(1024,276610),(1024,407816)]),([7,31,482,3652,13448,26911,32159],[(1024,1295),(1024,14594),(1024,69003),(1024,263183),(1024,269710),(1024,269711),(1024,273410),(1024,276482),(1024,407816)]),([7,31,482,3652,13448,26911,32285],[(1024,1295),(1024,14498),(1024,14594),(1024,263183),(1024,268588),(1024,276482),(1024,276775),(1024,301327)]),([7,31,482,3652,13448,26911,32736],[(1024,1295),(1024,178178),(1024,263183),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,26960],[(1024,145570),(1024,276482),(1024,276872)]),([7,31,482,3652,13448,27024],[(1024,145570),(1024,276482),(1024,276775)])]
def t224 : BT := .nd (blockTree b228) [7,31,482,3652,13448,26904] (blockTree b229)
def b230 : List Row := [([7,31,482,3652,13448,27122,27122],[(1024,132271),(1024,145570),(1024,165007),(1024,178306)]),([7,31,482,3652,13448,27122,27135],[(1024,14498),(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([7,31,482,3652,13448,27122,28500],[(1024,132271),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,276610),(1024,276872)]),([7,31,482,3652,13448,27122,28662],[(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,178306)]),([7,31,482,3652,13448,27122,29115],[(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]),([7,31,482,3652,13448,27122,32152],[(1024,132271),(1024,134542),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,276610),(1024,276775),(1024,407684)]),([7,31,482,3652,13448,27122,32250],[(1024,132271),(1024,134542),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,407684)]),([7,31,482,3652,13448,27122,32285],[(1024,14498),(1024,132271),(1024,145570),(1024,145796),(1024,165007),(1024,178306)]),([7,31,482,3652,13448,27122,32736],[(1024,132271),(1024,145796),(1024,165007),(1024,178178),(1024,178306),(1024,396431)]),([7,31,482,3652,13448,27135],[(1024,14498),(1024,178178)]),([7,31,482,3652,13448,27920],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,3652,13448,28500,32152],[(1024,1295),(1024,134542),(1024,134543),(1024,145570),(1024,165007),(1024,268588),(1024,268591),(1024,269710),(1024,273410),(1024,276482),(1024,276775),(1024,276872),(1024,309511),(1024,407684)]),([7,31,482,3652,13450,26896],[(1024,145796),(1024,276775),(1024,276872)])]
def b231 : List Row := [([7,31,482,3652,13464,26896],[(1024,134444),(1024,134542),(1024,144546),(1024,276482)]),([7,31,482,3652,13471,13802,26896],[(1024,68775),(1024,134542),(1024,145576),(1024,145796),(1024,268588),(1024,269710),(1024,276484),(1024,276775)]),([7,31,482,3652,13471,16076,26896],[(1024,1295),(1024,68775),(1024,69003),(1024,76164),(1024,134444),(1024,145570),(1024,276482),(1024,396363),(1024,403524)]),([7,31,482,3652,13471,19319,26896],[(1024,1295),(1024,145570),(1024,178306),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,3652,13471,26896,32152],[(1024,1295),(1024,134444),(1024,134542),(1024,269711),(1024,273410),(1024,396430),(1024,406660),(1024,407816)]),([7,31,482,3652,13512,26896],[(1024,145570),(1024,276482),(1024,276872)]),([7,31,482,3652,13704,26896],[(1024,145570),(1024,269612),(1024,269710),(1024,275458)]),([7,31,482,3652,13802,16076,26896],[(1024,14498),(1024,14594),(1024,69003),(1024,145570),(1024,165007),(1024,269612),(1024,276482),(1024,276779),(1024,276872)]),([7,31,482,3652,13802,19319,26896],[(1024,14594),(1024,142498),(1024,145570),(1024,165007),(1024,268588),(1024,275848),(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3652,13802,26896,32152],[(1024,134542),(1024,134543),(1024,165007),(1024,269612),(1024,269710),(1024,275848),(1024,400654),(1024,406792),(1024,407684)]),([7,31,482,3652,15496,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,3652,16076,19319,26896],[(1024,1295),(1024,69003),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,276482)]),([7,31,482,3652,16076,26896,32152],[(1024,1295),(1024,69003),(1024,134542),(1024,134543),(1024,145570),(1024,165007),(1024,269710),(1024,276482),(1024,276872),(1024,407684)])]
def t225 : BT := .nd (blockTree b230) [7,31,482,3652,13452,26896] (blockTree b231)
def t226 : BT := .nd t224 [7,31,482,3652,13448,27122] t225
def t227 : BT := .nd t223 [7,31,482,3652,13448,26896,32703] t226
def b232 : List Row := [([7,31,482,3652,19319,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,19319,19327,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,19319,19447,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3652,19319,20343,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([7,31,482,3652,19319,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,3652,19319,26896,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3652,19319,26896,26911],[(1024,1295),(1024,145796),(1024,263183),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]),([7,31,482,3652,19319,26896,27122],[(1024,132271),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,276610),(1024,276775),(1024,276872)]),([7,31,482,3652,19319,26896,27511],[(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482),(1024,309415)]),([7,31,482,3652,19319,26896,28500],[(1024,1295),(1024,145570),(1024,165007),(1024,268588),(1024,268591),(1024,273410),(1024,275458),(1024,276482),(1024,276775),(1024,309511)]),([7,31,482,3652,19319,26896,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,275458),(1024,276482)]),([7,31,482,3652,19319,26896,32152],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,269710),(1024,273410),(1024,275458),(1024,276482),(1024,276872)]),([7,31,482,3652,19319,26896,32285],[(1024,1295),(1024,14594),(1024,144546),(1024,145570),(1024,145796),(1024,165007),(1024,268588),(1024,276482),(1024,276775),(1024,301327)])]
def b233 : List Row := [([7,31,482,3652,19319,26896,32767],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482)]),([7,31,482,3652,19319,26911],[(1024,14594),(1024,276482),(1024,276775)]),([7,31,482,3652,19319,27122],[(1024,145570),(1024,145796),(1024,178306)]),([7,31,482,3652,26896,26896,32152],[(1024,1294),(1024,134542),(1024,144546),(1024,165006),(1024,269710),(1024,273410),(1024,275458)]),([7,31,482,3652,26896,26911,32152],[(1024,1294),(1024,134542),(1024,269710),(1024,273410),(1024,275458)]),([7,31,482,3652,26896,27122,32152],[(1024,134542),(1024,142498),(1024,144546),(1024,165006),(1024,269710),(1024,275458),(1024,275751)]),([7,31,482,3652,26896,27511],[(1024,144546),(1024,275458),(1024,275751)]),([7,31,482,3652,26896,28500,32152],[(1024,1294),(1024,134542),(1024,144546),(1024,165006),(1024,269710),(1024,273410),(1024,273703),(1024,275458),(1024,275751)]),([7,31,482,3652,26896,29115,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,275458),(1024,406660)]),([7,31,482,3652,26896,32152],[(1024,134542),(1024,144546),(1024,269710),(1024,275458)]),([7,31,482,3652,26896,32152,32152],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]),([7,31,482,3652,26896,32152,32159],[(1024,1294),(1024,134542),(1024,273410),(1024,275458),(1024,396430),(1024,406660)]),([7,31,482,3652,26896,32152,32250],[(1024,134542),(1024,165006),(1024,273800),(1024,275458),(1024,400654),(1024,406660)])]
def t228 : BT := .nd (blockTree b232) [7,31,482,3652,19319,26896,32736] (blockTree b233)
def b234 : List Row := [([7,31,482,3652,26896,32152,32732],[(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]),([7,31,482,3652,26896,32152,32736],[(1024,1294),(1024,134542),(1024,165006),(1024,269710),(1024,273410),(1024,275458),(1024,396430),(1024,406660)]),([7,31,482,3652,28500,32152],[(1024,134542),(1024,269710),(1024,275458),(1024,275751)]),([7,31,482,3654,13448,26896],[(1024,145796),(1024,276546),(1024,276775),(1024,276872)]),([7,31,482,3660,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,3668,13448,26896],[(1024,142498),(1024,276482),(1024,276775)]),([7,31,482,3679,3679,13448,26896],[(1024,1295),(1024,134542),(1024,178306),(1024,276482),(1024,276872)]),([7,31,482,3679,4070,13448,26896],[(1024,134542),(1024,145570),(1024,145575),(1024,145796),(1024,268588),(1024,276482),(1024,276546),(1024,276872)]),([7,31,482,3679,4095,13448,26896],[(1024,134542),(1024,268588),(1024,276482),(1024,276872)]),([7,31,482,3679,5871,13448],[(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3679,5871,13448,26896],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3679,8192,13448,26896],[(1024,1295),(1024,134543),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([7,31,482,3679,13448,13448,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,276482)])]
def b235 : List Row := [([7,31,482,3679,13448,13802,26896],[(1024,268588),(1024,269710),(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3679,13448,16076,26896],[(1024,1295),(1024,145570),(1024,145796),(1024,145803),(1024,178178),(1024,178306),(1024,276482)]),([7,31,482,3679,13448,16095,26896],[(1024,1295),(1024,134542),(1024,178178),(1024,178306),(1024,276482)]),([7,31,482,3679,13448,19319,26896],[(1024,1295),(1024,178306),(1024,268588),(1024,276482)]),([7,31,482,3679,13448,26896],[(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3679,13448,26896,26896],[(1024,1295),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,3679,13448,26896,26911],[(1024,1295),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]),([7,31,482,3679,13448,26896,27122],[(1024,132271),(1024,178306),(1024,276482),(1024,276610),(1024,276775),(1024,276872)]),([7,31,482,3679,13448,26896,28500],[(1024,1295),(1024,268588),(1024,268591),(1024,273800),(1024,275458),(1024,276482),(1024,276546),(1024,309511)]),([7,31,482,3679,13448,26896,28511],[(1024,1295),(1024,268588),(1024,268591),(1024,273800),(1024,275458),(1024,276482),(1024,276610),(1024,309511)]),([7,31,482,3679,13448,26896,29088],[(1024,1295),(1024,134542),(1024,178306),(1024,276482),(1024,276872)]),([7,31,482,3679,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,178306),(1024,276482),(1024,276872)]),([7,31,482,3679,13448,26896,32152],[(1024,1295),(1024,134542),(1024,134543),(1024,269710),(1024,273410),(1024,276482),(1024,276872),(1024,407684)])]
def t229 : BT := .nd (blockTree b234) [7,31,482,3679,13448,13471,26896] (blockTree b235)
def t230 : BT := .nd t228 [7,31,482,3652,26896,32152,32285] t229
def b236 : List Row := [([7,31,482,3679,13448,26896,32736],[(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,276482),(1024,276775)]),([7,31,482,3679,13448,26911],[(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3679,13448,27122],[(1024,178306)]),([7,31,482,3679,19319,26896],[(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,3679,26896,32152],[(1024,134542),(1024,269710),(1024,275458)]),([7,31,482,3780,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,3908,13448,26896],[(1024,145570),(1024,268588),(1024,273410)]),([7,31,482,4070,13448,16076,26896],[(1024,14498),(1024,14594),(1024,66727),(1024,66828),(1024,69003),(1024,145570),(1024,165007),(1024,268588),(1024,273474),(1024,276482),(1024,276775),(1024,276875)]),([7,31,482,4070,13448,26896,28500],[(1024,66727),(1024,165007),(1024,268588),(1024,273410),(1024,273703),(1024,301324),(1024,306439)]),([7,31,482,4070,13448,26896,29115],[(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,170050),(1024,273703),(1024,276482),(1024,276775)]),([7,31,482,4267,13448,26896],[(1024,142498),(1024,268588),(1024,273410)]),([7,31,482,4267,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,5871,13448,26896,28500],[(1024,1292),(1024,142498),(1024,165004),(1024,268588),(1024,273410),(1024,306439)])]
def b237 : List Row := [([7,31,482,5871,13448,28500],[(1024,142498),(1024,273410),(1024,306439)]),([7,31,482,5871,13448,29115],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,8192,11844,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([7,31,482,8192,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,8192,13448,26896,29115],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482),(1024,407556),(1024,407684)]),([7,31,482,9216,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,11844,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,12424,13448,26896,29115],[(1024,1295),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([7,31,482,13448,13448,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,13448,13448,26896,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([7,31,482,13448,13471,26896,28500],[(1024,1292),(1024,69003),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,13448,13471,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,178306),(1024,273410),(1024,276482),(1024,276775)]),([7,31,482,13448,13802,26896,28500],[(1024,142498),(1024,165004),(1024,268588),(1024,273800),(1024,275848),(1024,306439)])]
def t231 : BT := .nd (blockTree b236) [7,31,482,5871,13448,26896,29115] (blockTree b237)
def b238 : List Row := [([7,31,482,13448,16076,26896,28500],[(1024,1295),(1024,69003),(1024,145570),(1024,165007),(1024,268588),(1024,268591),(1024,273410),(1024,276482),(1024,276775),(1024,309511)]),([7,31,482,13448,16076,26896,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,178178),(1024,178306),(1024,276482),(1024,403524)]),([7,31,482,13448,19319,26896,28500],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,13448,19319,26896,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([7,31,482,13448,24848,26896,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,275458),(1024,276482)]),([7,31,482,13448,26896,26896,28500],[(1024,1292),(1024,142498),(1024,165004),(1024,268588),(1024,273410)]),([7,31,482,13448,26896,26896,29115],[(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]),([7,31,482,13448,26896,26911,28500],[(1024,1292),(1024,142724),(1024,268588),(1024,273410)]),([7,31,482,13448,26896,26911,28511],[(1024,1292),(1024,263180),(1024,268588),(1024,273410),(1024,273538)]),([7,31,482,13448,26896,26911,29115],[(1024,1295),(1024,145796),(1024,263183),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]),([7,31,482,13448,26896,27122,28500],[(1024,142498),(1024,165004),(1024,268588),(1024,273410),(1024,273800)]),([7,31,482,13448,26896,27122,29115],[(1024,132271),(1024,142498),(1024,144546),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,276610),(1024,276775),(1024,276872)]),([7,31,482,13448,26896,28500],[(1024,142498),(1024,268588),(1024,273410)])]
def b239 : List Row := [([7,31,482,13448,26896,28500,28511],[(1024,1292),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,13448,26896,28500,28662],[(1024,66727),(1024,165004),(1024,268588),(1024,273410),(1024,273703),(1024,301324),(1024,306439)]),([7,31,482,13448,26896,28500,29115],[(1024,1295),(1024,142498),(1024,145570),(1024,165007),(1024,268588),(1024,273410),(1024,275458),(1024,276482),(1024,276775)]),([7,31,482,13448,26896,28500,32152],[(1024,1292),(1024,142498),(1024,165004),(1024,268588),(1024,273410),(1024,273800),(1024,275848)]),([7,31,482,13448,26896,28500,32285],[(1024,1292),(1024,142498),(1024,165004),(1024,268588),(1024,301324),(1024,306439)]),([7,31,482,13448,26896,28500,32732],[(1024,1292),(1024,69003),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]),([7,31,482,13448,26896,28500,32736],[(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439),(1024,396428)]),([7,31,482,13448,26896,28511],[(1024,268588),(1024,273410)]),([7,31,482,13448,26896,29088],[(1024,276482),(1024,276775),(1024,276872)]),([7,31,482,13448,26896,29115],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,13448,26896,29115,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,482,13448,26896,29115,29119],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]),([7,31,482,13448,26896,29115,29179],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)])]
def t232 : BT := .nd (blockTree b238) [7,31,482,13448,26896,28500,28500] (blockTree b239)
def t233 : BT := .nd t231 [7,31,482,13448,13802,26896,29115] t232
def t234 : BT := .nd t230 [7,31,482,3679,13448,26896,32285] t233
def t235 : BT := .nd t227 [7,31,482,3652,18704,19319,26896] t234
def b240 : List Row := [([7,31,482,13448,26896,29115,31163],[(1024,1295),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482),(1024,407556)]),([7,31,482,13448,26896,29115,32152],[(1024,1295),(1024,134542),(1024,134543),(1024,145570),(1024,165007),(1024,269710),(1024,273410),(1024,276482),(1024,276872),(1024,407684)]),([7,31,482,13448,26896,29115,32285],[(1024,1295),(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,145796),(1024,165007),(1024,276482),(1024,276775),(1024,301327)]),([7,31,482,13448,26896,29115,32736],[(1024,1295),(1024,134542),(1024,145796),(1024,165007),(1024,178306),(1024,273410),(1024,276482),(1024,276775),(1024,396431)]),([7,31,482,13448,26896,29115,32767],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]),([7,31,482,13448,26896,29119],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,482,13448,26896,31163],[(1024,142498),(1024,273410),(1024,273703)]),([7,31,482,13448,26911,28500],[(1024,268588),(1024,273410)]),([7,31,482,13448,26911,28511],[(1024,11522),(1024,268588),(1024,273410)]),([7,31,482,13448,26911,29115],[(1024,14594),(1024,276482),(1024,276775)]),([7,31,482,13448,27122,29115],[(1024,145570),(1024,145796),(1024,178306)]),([7,31,482,13448,28500,32152],[(1024,142498),(1024,268588),(1024,273410),(1024,273800)]),([7,31,482,19319,26896,28500],[(1024,142498),(1024,268588),(1024,273410)])]
def b241 : List Row := [([7,31,482,26896,28500,32152],[(1024,142498),(1024,273410),(1024,273703),(1024,273800)]),([7,31,482,26896,29115,32152],[(1024,134542),(1024,144546),(1024,269710),(1024,275458)]),([7,31,482,28500,32152],[]),([7,31,486,3652,13448,26896],[(1024,66727),(1024,276482)]),([7,31,490,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,498,3652,13448,26896],[(1024,132396),(1024,132494),(1024,276482)]),([7,31,511,3652,4070,13448,26896],[(1024,66727),(1024,71842),(1024,132396),(1024,134542),(1024,164935),(1024,170050),(1024,276482)]),([7,31,511,3652,13448,13802,26896],[(1024,66727),(1024,132494),(1024,145570),(1024,145800),(1024,268588),(1024,269710),(1024,276482),(1024,276775)]),([7,31,511,3652,13448,26896,27122],[(1024,132396),(1024,132494),(1024,276868)]),([7,31,511,3652,13448,26896,32285],[(1024,1295),(1024,71842),(1024,134542),(1024,145796),(1024,268588),(1024,276775),(1024,301327)]),([7,31,1024,1506,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]),([7,31,1024,3652,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,142498),(1024,145570),(1024,165007),(1024,276482)]),([7,31,1506,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)])]
def t236 : BT := .nd (blockTree b240) [7,31,482,19319,26896,29115] (blockTree b241)
def b242 : List Row := [([7,31,2048,3652,13448,26896,32285],[(1024,1199),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,2530,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,31,3588,3652,13448,26896,32285],[(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,3652,13448,26896,32285],[(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,3679,13448,26896,32285],[(1024,1294),(1024,1295),(1024,145796),(1024,276482),(1024,301327),(1024,400655)]),([7,31,3652,4070,13448,13802,26896],[(1024,14594),(1024,66727),(1024,145570),(1024,165007),(1024,268588),(1024,269710),(1024,273474),(1024,276482),(1024,276775),(1024,276872)]),([7,31,3652,4070,13448,26896,27122],[(1024,132271),(1024,144546),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,276610),(1024,276872),(1024,276875)]),([7,31,3652,4070,13448,26896,32285],[(1024,1295),(1024,14594),(1024,66727),(1024,134542),(1024,145570),(1024,165007),(1024,276482),(1024,301324),(1024,301327)]),([7,31,3652,4070,13448,27122],[(1024,145570),(1024,145796),(1024,178306)]),([7,31,3652,5871,13448,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,5871,13448,32285],[(1024,1295),(1024,145570),(1024,145796),(1024,301327)]),([7,31,3652,8192,8674,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]),([7,31,3652,8192,13448,26896,32285],[(1024,1199),(1024,1292),(1024,1295),(1024,145570),(1024,165007),(1024,276482)])]
def b243 : List Row := [([7,31,3652,13320,13448,26896,32285],[(1024,1292),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,13448,13448,26896,32285],[(1024,1292),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,13448,13471,26896,32285],[(1024,1292),(1024,1295),(1024,145796),(1024,276482),(1024,301327)]),([7,31,3652,13448,13802,26896,27122],[(1024,132271),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,276482),(1024,276484),(1024,276610),(1024,276775),(1024,276779)]),([7,31,3652,13448,13802,26896,32285],[(1024,1295),(1024,14594),(1024,142498),(1024,145570),(1024,145796),(1024,165007),(1024,268588),(1024,276482),(1024,301327),(1024,400654),(1024,400655)]),([7,31,3652,13448,13802,27122],[(1024,145570),(1024,178306)]),([7,31,3652,13448,16076,26896,32285],[(1024,1199),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,13448,19319,26896,32285],[(1024,1292),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,13448,26640,26896,32285],[(1024,1295),(1024,142498),(1024,144546),(1024,145570),(1024,145666),(1024,165007)]),([7,31,3652,13448,26640,32285],[(1024,145570),(1024,145796)]),([7,31,3652,13448,26896,26896,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,13448,26896,26911,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,145666),(1024,276482),(1024,301327)]),([7,31,3652,13448,26896,27122,32285],[(1024,1295),(1024,132271),(1024,132367),(1024,142498),(1024,144546),(1024,145570),(1024,145796),(1024,165007),(1024,301327),(1024,400655)])]
def t237 : BT := .nd (blockTree b242) [7,31,3652,8674,13448,26896] (blockTree b243)
def t238 : BT := .nd t236 [7,31,2048,2530,3652,13448,26896] t237
def b244 : List Row := [([7,31,3652,13448,26896,29115,32285],[(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,13448,26896,32152,32285],[(1024,1292),(1024,1294),(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482),(1024,400655)]),([7,31,3652,13448,26896,32285],[(1024,1295),(1024,145570),(1024,145796),(1024,301327)]),([7,31,3652,13448,26896,32285,32285],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,268588),(1024,301327)]),([7,31,3652,13448,26896,32285,32287],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,268588),(1024,301327),(1024,396431)]),([7,31,3652,13448,26896,32285,32349],[(1024,1295),(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,145796),(1024,165007),(1024,301327)]),([7,31,3652,13448,26896,32285,32413],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,268588),(1024,301327),(1024,400655)]),([7,31,3652,13448,26896,32285,32541],[(1024,1295),(1024,134542),(1024,142498),(1024,145570),(1024,145796),(1024,165007),(1024,301327),(1024,400655)]),([7,31,3652,13448,26896,32285,32736],[(1024,1292),(1024,1294),(1024,1295),(1024,165007),(1024,276482),(1024,301327),(1024,396431)]),([7,31,3652,13448,26896,32285,32767],[(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,31,3652,13448,26911,32285],[(1024,1295),(1024,14594),(1024,301327)]),([7,31,3652,13448,27122,32285],[(1024,132271),(1024,145570),(1024,145796)]),([7,31,3652,19319,26896,32285],[(1024,1295),(1024,145570),(1024,145796),(1024,301327)])]
def b245 : List Row := [([7,31,3679,13448,26896,32285],[(1024,1295),(1024,301327),(1024,400655)]),([7,31,13448,26896,28500,32285],[(1024,1292),(1024,142498),(1024,268588),(1024,301324)]),([7,31,13448,26896,29115,32285],[(1024,1295),(1024,145570),(1024,145796),(1024,301327)]),([7,64,95,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]),([7,64,482,3652,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([7,64,482,3652,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([7,66,482,3652,3679,13448,26896],[(1024,134542),(1024,145570),(1024,145796),(1024,276482),(1024,276872),(1024,396431),(1024,400655)]),([7,95,482,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276872)]),([7,128,159,482,3652,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]),([7,128,482,3652,3679,13448,26896],[(1024,1295),(1024,134542),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([7,128,482,3652,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([7,159,482,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([7,256,287,482,3652,13448,26896],[(1024,132271),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,178306),(1024,263468)])]
def t239 : BT := .nd (blockTree b244) [7,31,3652,26896,32152,32285] (blockTree b245)
def b246 : List Row := [([7,256,482,3652,13448,26896,32736],[(1024,145570),(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([7,287,482,3652,13448,26896],[(1024,145570),(1024,263468),(1024,263566)]),([7,480,482,3652,13448,26896,32736],[(1024,145796),(1024,165007),(1024,276482),(1024,276775),(1024,396428),(1024,396430),(1024,396431)]),([7,482,482,3652,3679,13448,26896],[(1024,134542),(1024,145570),(1024,145796),(1024,165007)]),([7,482,482,3652,13448,26896,32736],[(1024,145570),(1024,165004),(1024,165006),(1024,165007),(1024,276775),(1024,396431)]),([7,482,511,3652,3679,13448,26896],[(1024,134542),(1024,145570),(1024,145796),(1024,263468),(1024,276482),(1024,276872)]),([7,482,511,3652,13448,13471,26896],[(1024,69003),(1024,71842),(1024,134542),(1024,145570),(1024,145796),(1024,263566),(1024,268588),(1024,276482),(1024,276775),(1024,276868)]),([7,482,511,3652,13448,26896,26911],[(1024,71842),(1024,145703),(1024,145800),(1024,263244),(1024,263468),(1024,263566)]),([7,482,511,3652,13448,26896,32736],[(1024,134542),(1024,145796),(1024,164935),(1024,165007),(1024,268588),(1024,276775),(1024,396431)]),([7,482,511,3679,13448,26896],[]),([7,482,1024,1055,3652,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,268588),(1024,276482)]),([7,482,1024,3652,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([7,482,1024,3652,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)])]
def b247 : List Row := [([7,482,1055,3652,13448,26896],[(1024,145570),(1024,145796),(1024,276482)]),([7,482,2048,2079,3652,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]),([7,482,2048,3652,3679,13448,26896],[(1024,1295),(1024,14594),(1024,134542),(1024,145570),(1024,165007),(1024,276482),(1024,407556)]),([7,482,2048,3652,13448,26896,32736],[(1024,164879),(1024,165006),(1024,165007),(1024,276482)]),([7,482,2048,3679,13448,26896],[(1024,145570),(1024,145796),(1024,276482)]),([7,482,2064,3652,3679,13448,26896],[(1024,1295),(1024,14594),(1024,145570),(1024,263183),(1024,269710),(1024,276482),(1024,407556)]),([7,482,2079,3652,13448,26896],[(1024,145570),(1024,145796),(1024,276482)]),([7,482,3648,3652,13448,26896,32736],[(1024,165006),(1024,165007),(1024,276482)]),([7,482,3648,13448,26896,32736],[(1024,165007),(1024,276482),(1024,276775),(1024,396431)]),([7,482,3652,3652,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([7,482,3652,3652,13448,26896,32736],[(1024,165006),(1024,165007),(1024,276482)]),([7,482,3652,3679,3679,13448,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,178306),(1024,276482)]),([7,482,3652,3679,4070,13448,26896],[(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,276482),(1024,276872)])]
def t240 : BT := .nd (blockTree b246) [7,482,1032,3652,3679,13448,26896] (blockTree b247)
def t241 : BT := .nd t239 [7,256,482,3652,3679,13448,26896] t240
def t242 : BT := .nd t238 [7,31,3652,13448,26896,28500,32285] t241
def b248 : List Row := [([7,482,3652,3679,5871,13448],[(1024,145570),(1024,145796),(1024,276482)]),([7,482,3652,3679,5871,13448,26896],[(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([7,482,3652,3679,8192,13448,26896],[(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,276482),(1024,407556),(1024,407684)]),([7,482,3652,3679,13448,13448,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,482,3652,3679,13448,13471,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,178306),(1024,276482)]),([7,482,3652,3679,13448,13802,26896],[(1024,145570),(1024,165007),(1024,269710),(1024,276482),(1024,276872)]),([7,482,3652,3679,13448,16076,26896],[(1024,1295),(1024,14498),(1024,145570),(1024,165007),(1024,276482)]),([7,482,3652,3679,13448,16095,26896],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,178178),(1024,178306),(1024,276482)]),([7,482,3652,3679,13448,19319,26896],[(1024,1295),(1024,145570),(1024,165007),(1024,276482)]),([7,482,3652,3679,13448,26896],[(1024,145570),(1024,145796),(1024,276482)]),([7,482,3652,3679,13448,26896,26896],[(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]),([7,482,3652,3679,13448,26896,26911],[(1024,1295),(1024,14594),(1024,145570),(1024,145575),(1024,145666),(1024,145796),(1024,145803),(1024,263183),(1024,263244),(1024,275458),(1024,276482)]),([7,482,3652,3679,13448,26896,27122],[(1024,132271),(1024,144546),(1024,145570),(1024,145666),(1024,165007),(1024,276872)])]
def b249 : List Row := [([7,482,3652,3679,13448,26896,28511],[(1024,1295),(1024,14594),(1024,145570),(1024,145666),(1024,145796),(1024,263183),(1024,263244),(1024,275458),(1024,276482)]),([7,482,3652,3679,13448,26896,29088],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,178306),(1024,276482),(1024,276872),(1024,396431)]),([7,482,3652,3679,13448,26896,29115],[(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]),([7,482,3652,3679,13448,26896,32152],[(1024,1295),(1024,134542),(1024,134543),(1024,145570),(1024,145796),(1024,165007),(1024,269710),(1024,276482),(1024,407684)]),([7,482,3652,3679,13448,26896,32285],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,276872),(1024,400655)]),([7,482,3652,3679,13448,26896,32736],[(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,165007),(1024,178306),(1024,276482),(1024,276775),(1024,396431)]),([7,482,3652,3679,13448,27122],[(1024,145570),(1024,145796),(1024,178306)]),([7,482,3652,3679,19319,26896],[(1024,145570),(1024,145796),(1024,276482)]),([7,482,3652,3679,26896,32152],[(1024,134542),(1024,144546),(1024,269710),(1024,275458)]),([7,482,3652,4070,13448,26896,32736],[(1024,145570),(1024,165006),(1024,165007),(1024,276775),(1024,396431)]),([7,482,3652,5871,13448,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([7,482,3652,5871,13448,32736],[(1024,165007),(1024,276482),(1024,276775),(1024,396431)]),([7,482,3652,8192,8223,13448,26896],[(1024,1295),(1024,14594),(1024,134543),(1024,145570),(1024,165007),(1024,268588),(1024,276482),(1024,407556),(1024,407684)])]
def t243 : BT := .nd (blockTree b248) [7,482,3652,3679,13448,26896,28500] (blockTree b249)
def b250 : List Row := [([7,482,3652,8223,13448,26896],[(1024,145570),(1024,145796),(1024,276482)]),([7,482,3652,13440,13448,26896,32736],[(1024,165004),(1024,165007),(1024,276482)]),([7,482,3652,13448,13448,26896,32736],[(1024,165004),(1024,165007),(1024,276482)]),([7,482,3652,13448,13471,26896,26911],[(1024,1295),(1024,14594),(1024,76164),(1024,145570),(1024,145576),(1024,145666),(1024,263183),(1024,273410),(1024,276482)]),([7,482,3652,13448,13471,26896,32736],[(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,276775),(1024,396363),(1024,396430),(1024,396431)]),([7,482,3652,13448,13471,26911],[(1024,14594),(1024,276482),(1024,276775)]),([7,482,3652,13448,13802,26896,32736],[(1024,145570),(1024,165004),(1024,165007),(1024,276775),(1024,396431)]),([7,482,3652,13448,16076,26896,32736],[(1024,164879),(1024,165007),(1024,276482)]),([7,482,3652,13448,19319,26896,32736],[(1024,165004),(1024,165007),(1024,276482)]),([7,482,3652,13448,26880,26896,32736],[(1024,1295),(1024,165007),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]),([7,482,3652,13448,26880,32736],[(1024,276482),(1024,276775)]),([7,482,3652,13448,26896,26896,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([7,482,3652,13448,26896,26911,32736],[(1024,1295),(1024,165007),(1024,263183),(1024,263311),(1024,273410),(1024,275458),(1024,276482),(1024,276775),(1024,396431)])]
def b251 : List Row := [([7,482,3652,13448,26896,28500,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,268588),(1024,276482)]),([7,482,3652,13448,26896,29088],[(1024,165007),(1024,276482),(1024,276872),(1024,396431)]),([7,482,3652,13448,26896,29115,32736],[(1024,165006),(1024,165007),(1024,276482)]),([7,482,3652,13448,26896,32152,32736],[(1024,165004),(1024,165006),(1024,165007),(1024,269710),(1024,276482),(1024,396431)]),([7,482,3652,13448,26896,32285,32736],[(1024,145570),(1024,165004),(1024,165006),(1024,165007),(1024,301327),(1024,396431)]),([7,482,3652,13448,26896,32736],[(1024,165007),(1024,276482),(1024,276775),(1024,396431)]),([7,482,3652,13448,26896,32736,32736],[(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,276775),(1024,396431)]),([7,482,3652,13448,26896,32736,32738],[(1024,134542),(1024,165007),(1024,268588),(1024,276482),(1024,276775),(1024,301327),(1024,396431)]),([7,482,3652,13448,26896,32736,32740],[(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,276775),(1024,396431)]),([7,482,3652,13448,26896,32736,32744],[(1024,1295),(1024,165007),(1024,178306),(1024,268588),(1024,269710),(1024,276482),(1024,276775),(1024,396431)]),([7,482,3652,13448,26896,32736,32752],[(1024,1295),(1024,165007),(1024,268588),(1024,269710),(1024,276482),(1024,276775),(1024,396431)]),([7,482,3652,13448,26896,32736,32767],[(1024,165004),(1024,165006),(1024,165007),(1024,276482)]),([7,482,3652,13448,26896,32740],[(1024,165007),(1024,276482),(1024,276551),(1024,396431)])]
def t244 : BT := .nd (blockTree b250) [7,482,3652,13448,26896,27122,32736] (blockTree b251)
def t245 : BT := .nd t243 [7,482,3652,8192,13448,26896,32736] t244
def b252 : List Row := [([7,482,3652,13448,27122,32736],[(1024,165007),(1024,178306),(1024,396431)]),([7,482,3652,19319,26896,32736],[(1024,165007),(1024,276482),(1024,276775),(1024,396431)]),([7,482,3652,26896,32152,32736],[(1024,134542),(1024,165006),(1024,269710),(1024,275458),(1024,396430)]),([7,482,3679,4070,13448,26896],[(1024,145570),(1024,145796)]),([7,482,3679,13448,13471,26896],[(1024,276482),(1024,276775),(1024,276872)]),([7,482,3679,13448,16076,26896],[(1024,145570),(1024,145796),(1024,276482)]),([7,482,3679,13448,26896,29115],[(1024,145570),(1024,145796),(1024,276482)]),([7,482,3679,13448,26896,32736],[(1024,276482),(1024,276775),(1024,276872)]),([7,482,13448,26896,28500,32736],[(1024,165004),(1024,268588),(1024,273410),(1024,396428)]),([7,482,13448,26896,29115,32736],[(1024,165007),(1024,276482),(1024,276775),(1024,396431)]),([7,3652,3679,13448,26896,32285],[(1024,1295),(1024,145570),(1024,145796),(1024,400655)]),([7,3652,13448,26896,32285,32736],[(1024,1295),(1024,165007),(1024,396431)]),([8,2,31,482,3652,13448,26896],[(1024,145796),(1024,276775),(1024,276872)])]
def b253 : List Row := [([8,8,31,482,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,16,31,482,3652,13448,26896],[(1024,276482),(1024,276775)]),([8,31,31,482,3652,13448,26896],[(1024,276482),(1024,276775)]),([8,31,64,482,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276872)]),([8,31,128,482,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,256,482,3652,13448,26896],[(1024,145570),(1024,145796)]),([8,31,482,482,3652,13448,26896],[(1024,145570),(1024,145796)]),([8,31,482,511,3652,13448,26896],[]),([8,31,482,1024,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,2048,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,3652,3652,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,3652,3679,13448,26896],[(1024,276482),(1024,276775),(1024,276872)]),([8,31,482,3652,4070,13448,26896],[(1024,145570),(1024,145796)])]
def t246 : BT := .nd (blockTree b252) [8,4,31,482,3652,13448,26896] (blockTree b253)
def b254 : List Row := [([8,31,482,3652,5871,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,3652,8192,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,3652,13448,13448,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,3652,13448,13471,26896],[(1024,276482),(1024,276775)]),([8,31,482,3652,13448,13802,26896],[(1024,145570),(1024,145796)]),([8,31,482,3652,13448,16076,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,3652,13448,19319,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,3652,13448,26896],[]),([8,31,482,3652,13448,26896,26896],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,3652,13448,26896,26911],[(1024,276482),(1024,276775)]),([8,31,482,3652,13448,26896,27122],[(1024,145570),(1024,145796)]),([8,31,482,3652,13448,26896,28500],[(1024,145570),(1024,276482),(1024,276775)]),([8,31,482,3652,13448,26896,29115],[(1024,145570),(1024,276482),(1024,276775)])]
def b255 : List Row := [([8,31,482,3652,13448,26896,32285],[(1024,145570),(1024,145796)]),([8,31,482,3652,13448,26896,32736],[(1024,276482),(1024,276775)]),([8,31,482,3652,13448,26911],[]),([8,31,482,3652,13448,27122],[]),([8,31,482,3652,19319,26896],[]),([8,31,482,3652,26896,32152],[]),([8,31,482,3679,13448,26896],[]),([8,31,482,13448,26896,28500],[]),([8,31,482,13448,26896,29115],[]),([8,31,3652,13448,26896,32285],[]),([8,482,3652,3679,13448,26896],[]),([8,482,3652,13448,26896,32736],[]),([9,31,482,3652,13448,26896],[])]
def t247 : BT := .nd (blockTree b254) [8,31,482,3652,13448,26896,32152] (blockTree b255)
def t248 : BT := .nd t246 [8,31,482,3652,5871,13448] t247
def t249 : BT := .nd t245 [7,482,3652,13448,26911,32736] t248
def t250 : BT := .nd t242 [7,482,3652,3679,4095,13448,26896] t249
def t251 : BT := .nd t235 [7,31,482,13448,26896,29115,30139] t250
def t252 : BT := .nd t220 [7,31,482,3652,13448,18704,26896] t251
def t253 : BT := .nd t189 [6,3679,4070,13448,13802,26896] t252
def t254 : BT := .nd t126 [6,31,490,3652,13448,27122] t253
def T_cert : BT := t254
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
theorem cb128 : Covered mP (blockTree b128) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb129 : Covered mP (blockTree b129) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb130 : Covered mP (blockTree b130) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb131 : Covered mP (blockTree b131) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb132 : Covered mP (blockTree b132) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb133 : Covered mP (blockTree b133) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb134 : Covered mP (blockTree b134) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb135 : Covered mP (blockTree b135) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb136 : Covered mP (blockTree b136) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb137 : Covered mP (blockTree b137) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb138 : Covered mP (blockTree b138) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb139 : Covered mP (blockTree b139) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb140 : Covered mP (blockTree b140) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb141 : Covered mP (blockTree b141) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb142 : Covered mP (blockTree b142) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb143 : Covered mP (blockTree b143) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb144 : Covered mP (blockTree b144) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb145 : Covered mP (blockTree b145) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb146 : Covered mP (blockTree b146) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb147 : Covered mP (blockTree b147) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb148 : Covered mP (blockTree b148) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb149 : Covered mP (blockTree b149) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb150 : Covered mP (blockTree b150) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb151 : Covered mP (blockTree b151) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb152 : Covered mP (blockTree b152) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb153 : Covered mP (blockTree b153) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb154 : Covered mP (blockTree b154) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb155 : Covered mP (blockTree b155) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb156 : Covered mP (blockTree b156) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb157 : Covered mP (blockTree b157) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb158 : Covered mP (blockTree b158) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb159 : Covered mP (blockTree b159) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb160 : Covered mP (blockTree b160) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb161 : Covered mP (blockTree b161) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb162 : Covered mP (blockTree b162) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb163 : Covered mP (blockTree b163) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb164 : Covered mP (blockTree b164) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb165 : Covered mP (blockTree b165) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb166 : Covered mP (blockTree b166) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb167 : Covered mP (blockTree b167) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb168 : Covered mP (blockTree b168) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb169 : Covered mP (blockTree b169) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb170 : Covered mP (blockTree b170) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb171 : Covered mP (blockTree b171) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb172 : Covered mP (blockTree b172) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb173 : Covered mP (blockTree b173) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb174 : Covered mP (blockTree b174) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb175 : Covered mP (blockTree b175) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb176 : Covered mP (blockTree b176) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb177 : Covered mP (blockTree b177) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb178 : Covered mP (blockTree b178) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb179 : Covered mP (blockTree b179) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb180 : Covered mP (blockTree b180) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb181 : Covered mP (blockTree b181) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb182 : Covered mP (blockTree b182) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb183 : Covered mP (blockTree b183) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb184 : Covered mP (blockTree b184) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb185 : Covered mP (blockTree b185) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb186 : Covered mP (blockTree b186) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb187 : Covered mP (blockTree b187) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb188 : Covered mP (blockTree b188) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb189 : Covered mP (blockTree b189) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb190 : Covered mP (blockTree b190) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb191 : Covered mP (blockTree b191) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb192 : Covered mP (blockTree b192) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb193 : Covered mP (blockTree b193) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb194 : Covered mP (blockTree b194) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb195 : Covered mP (blockTree b195) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb196 : Covered mP (blockTree b196) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb197 : Covered mP (blockTree b197) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb198 : Covered mP (blockTree b198) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb199 : Covered mP (blockTree b199) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb200 : Covered mP (blockTree b200) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb201 : Covered mP (blockTree b201) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb202 : Covered mP (blockTree b202) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb203 : Covered mP (blockTree b203) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb204 : Covered mP (blockTree b204) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb205 : Covered mP (blockTree b205) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb206 : Covered mP (blockTree b206) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb207 : Covered mP (blockTree b207) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb208 : Covered mP (blockTree b208) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb209 : Covered mP (blockTree b209) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb210 : Covered mP (blockTree b210) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb211 : Covered mP (blockTree b211) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb212 : Covered mP (blockTree b212) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb213 : Covered mP (blockTree b213) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb214 : Covered mP (blockTree b214) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb215 : Covered mP (blockTree b215) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb216 : Covered mP (blockTree b216) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb217 : Covered mP (blockTree b217) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb218 : Covered mP (blockTree b218) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb219 : Covered mP (blockTree b219) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb220 : Covered mP (blockTree b220) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb221 : Covered mP (blockTree b221) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb222 : Covered mP (blockTree b222) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb223 : Covered mP (blockTree b223) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb224 : Covered mP (blockTree b224) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb225 : Covered mP (blockTree b225) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb226 : Covered mP (blockTree b226) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb227 : Covered mP (blockTree b227) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb228 : Covered mP (blockTree b228) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb229 : Covered mP (blockTree b229) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb230 : Covered mP (blockTree b230) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb231 : Covered mP (blockTree b231) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb232 : Covered mP (blockTree b232) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb233 : Covered mP (blockTree b233) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb234 : Covered mP (blockTree b234) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb235 : Covered mP (blockTree b235) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb236 : Covered mP (blockTree b236) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb237 : Covered mP (blockTree b237) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb238 : Covered mP (blockTree b238) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb239 : Covered mP (blockTree b239) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb240 : Covered mP (blockTree b240) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb241 : Covered mP (blockTree b241) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb242 : Covered mP (blockTree b242) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb243 : Covered mP (blockTree b243) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb244 : Covered mP (blockTree b244) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb245 : Covered mP (blockTree b245) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb246 : Covered mP (blockTree b246) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb247 : Covered mP (blockTree b247) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb248 : Covered mP (blockTree b248) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb249 : Covered mP (blockTree b249) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb250 : Covered mP (blockTree b250) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb251 : Covered mP (blockTree b251) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb252 : Covered mP (blockTree b252) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb253 : Covered mP (blockTree b253) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb254 : Covered mP (blockTree b254) := coveredBlock _ (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cb255 : Covered mP (blockTree b255) := coveredBlock _ (by decide +kernel) (by decide +kernel)
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
theorem ct4 : Covered mP t4 := coveredNode cb6 cb7 (h := [(1024,132100),(1024,134156)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct5 : Covered mP t5 := coveredNode ct3 ct4 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct6 : Covered mP t6 := coveredNode ct2 ct5 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct7 : Covered mP t7 := coveredNode cb8 cb9 (h := [(1024,132100)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct8 : Covered mP t8 := coveredNode cb10 cb11 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct9 : Covered mP t9 := coveredNode ct7 ct8 (h := [(1024,1196),(1024,3468),(1024,170284),(1024,306343),(1024,404484),(1024,404491)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct10 : Covered mP t10 := coveredNode cb12 cb13 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct11 : Covered mP t11 := coveredNode cb14 cb15 (h := [(1024,1196),(1024,3468),(1024,164876),(1024,170060),(1024,170284)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct12 : Covered mP t12 := coveredNode ct10 ct11 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct13 : Covered mP t13 := coveredNode ct9 ct12 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct14 : Covered mP t14 := coveredNode ct6 ct13 (h := [(1024,71947),(1024,134311),(1024,165003),(1024,268363)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct15 : Covered mP t15 := coveredNode cb16 cb17 (h := [(1024,1196),(1024,164876),(1024,404484)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct16 : Covered mP t16 := coveredNode cb18 cb19 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct17 : Covered mP t17 := coveredNode ct15 ct16 (h := [(1024,1199),(1024,14498),(1024,164879),(1024,170050),(1024,171407),(1024,407720)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct18 : Covered mP t18 := coveredNode cb20 cb21 (h := [(1024,1291),(1024,165003),(1024,268292)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct19 : Covered mP t19 := coveredNode cb22 cb23 (h := [(1024,132108),(1024,134156)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct20 : Covered mP t20 := coveredNode ct18 ct19 (h := [(1024,142728)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct21 : Covered mP t21 := coveredNode ct17 ct20 (h := [(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct22 : Covered mP t22 := coveredNode cb24 cb25 (h := [(1024,134311),(1024,165003),(1024,170116)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct23 : Covered mP t23 := coveredNode cb26 cb27 (h := [(1024,11426),(1024,142498)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct24 : Covered mP t24 := coveredNode ct22 ct23 (h := [(1024,132108)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct25 : Covered mP t25 := coveredNode cb28 cb29 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct26 : Covered mP t26 := coveredNode cb30 cb31 (h := [(1024,134311),(1024,165003)]) (by decide +kernel)
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
theorem ct30 : Covered mP t30 := coveredNode ct14 ct29 (h := [(1024,1291),(1024,66727),(1024,164935),(1024,268292)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct31 : Covered mP t31 := coveredNode cb32 cb33 (h := [(1024,1292),(1024,11426),(1024,11431),(1024,169996),(1024,273410)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct32 : Covered mP t32 := coveredNode cb34 cb35 (h := [(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct33 : Covered mP t33 := coveredNode ct31 ct32 (h := [(1024,1292),(1024,134540),(1024,165004),(1024,404612)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct34 : Covered mP t34 := coveredNode cb36 cb37 (h := [(1024,1295),(1024,14498),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct35 : Covered mP t35 := coveredNode cb38 cb39 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct36 : Covered mP t36 := coveredNode ct34 ct35 (h := [(1024,134156)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct37 : Covered mP t37 := coveredNode ct33 ct36 (h := [(1024,1284),(1024,263172),(1024,269474)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct38 : Covered mP t38 := coveredNode cb40 cb41 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct39 : Covered mP t39 := coveredNode cb42 cb43 (h := [(1024,1292),(1024,165127),(1024,263180),(1024,268450)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct40 : Covered mP t40 := coveredNode ct38 ct39 (h := [(1024,1295),(1024,14498),(1024,14594),(1024,263183),(1024,407720)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct41 : Covered mP t41 := coveredNode cb44 cb45 (h := [(1024,1164),(1024,11394),(1024,132108),(1024,142338)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct42 : Covered mP t42 := coveredNode cb46 cb47 (h := [(1024,71980),(1024,178178)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct43 : Covered mP t43 := coveredNode ct41 ct42 (h := [(1024,142498),(1024,142728),(1024,175106)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct44 : Covered mP t44 := coveredNode ct40 ct43 (h := [(1024,1292),(1024,142498),(1024,165004),(1024,273410)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct45 : Covered mP t45 := coveredNode ct37 ct44 (h := [(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct46 : Covered mP t46 := coveredNode cb48 cb49 (h := [(1024,132100),(1024,269710)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct47 : Covered mP t47 := coveredNode cb50 cb51 (h := [(1024,1295),(1024,14498),(1024,14594),(1024,144546),(1024,145570),(1024,165007)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct48 : Covered mP t48 := coveredNode ct46 ct47 (h := [(1024,1196),(1024,1292),(1024,142498)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct49 : Covered mP t49 := coveredNode cb52 cb53 (h := [(1024,134542),(1024,142607),(1024,273551),(1024,276620)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct50 : Covered mP t50 := coveredNode cb54 cb55 (h := [(1024,165007),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct51 : Covered mP t51 := coveredNode ct49 ct50 (h := [(1024,132108)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct52 : Covered mP t52 := coveredNode ct48 ct51 (h := [(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct53 : Covered mP t53 := coveredNode cb56 cb57 (h := [(1024,142498),(1024,145570),(1024,306306),(1024,306308)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct54 : Covered mP t54 := coveredNode cb58 cb59 (h := [(1024,134156),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct55 : Covered mP t55 := coveredNode ct53 ct54 (h := [(1024,132271),(1024,134444),(1024,142498)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct56 : Covered mP t56 := coveredNode cb60 cb61 (h := [(1024,1295),(1024,134156),(1024,134542),(1024,263180),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct57 : Covered mP t57 := coveredNode cb62 cb63 (h := [(1024,142498),(1024,178178),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct58 : Covered mP t58 := coveredNode ct56 ct57 (h := [(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct59 : Covered mP t59 := coveredNode ct55 ct58 (h := [(1024,134444),(1024,142498),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct60 : Covered mP t60 := coveredNode ct52 ct59 (h := [(1024,1095),(1024,6210),(1024,66567),(1024,71682),(1024,134542),(1024,301199)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct61 : Covered mP t61 := coveredNode ct45 ct60 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct62 : Covered mP t62 := coveredNode ct30 ct61 (h := [(1024,1292),(1024,11522),(1024,142498),(1024,165004)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct63 : Covered mP t63 := coveredNode cb64 cb65 (h := [(1024,142498),(1024,144546),(1024,145570),(1024,165007)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct64 : Covered mP t64 := coveredNode cb66 cb67 (h := [(1024,269612)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct65 : Covered mP t65 := coveredNode ct63 ct64 (h := [(1024,263468),(1024,268588),(1024,275458)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct66 : Covered mP t66 := coveredNode cb68 cb69 (h := [(1024,268588),(1024,269612),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct67 : Covered mP t67 := coveredNode cb70 cb71 (h := [(1024,1191),(1024,164871),(1024,399364),(1024,403527),(1024,403751)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct68 : Covered mP t68 := coveredNode ct66 ct67 (h := [(1024,178178),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct69 : Covered mP t69 := coveredNode ct65 ct68 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct70 : Covered mP t70 := coveredNode cb72 cb73 (h := [(1024,132396),(1024,178306),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct71 : Covered mP t71 := coveredNode cb74 cb75 (h := [(1024,71980),(1024,178178),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct72 : Covered mP t72 := coveredNode ct70 ct71 (h := [(1024,177154),(1024,275458)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct73 : Covered mP t73 := coveredNode cb76 cb77 (h := [(1024,178178),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct74 : Covered mP t74 := coveredNode cb78 cb79 (h := [(1024,1292),(1024,142498),(1024,165004),(1024,273410)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct75 : Covered mP t75 := coveredNode ct73 ct74 (h := [(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct76 : Covered mP t76 := coveredNode ct72 ct75 (h := [(1024,71980),(1024,178178),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct77 : Covered mP t77 := coveredNode ct69 ct76 (h := [(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct78 : Covered mP t78 := coveredNode cb80 cb81 (h := [(1024,1292),(1024,142498),(1024,165004),(1024,273410),(1024,306343),(1024,404484)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct79 : Covered mP t79 := coveredNode cb82 cb83 (h := [(1024,132494),(1024,134542),(1024,263244),(1024,268588),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct80 : Covered mP t80 := coveredNode ct78 ct79 (h := [(1024,1292),(1024,142498),(1024,165004),(1024,175234),(1024,268588),(1024,273410),(1024,306343),(1024,306439)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct81 : Covered mP t81 := coveredNode cb84 cb85 (h := [(1024,275458),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct82 : Covered mP t82 := coveredNode cb86 cb87 (h := [(1024,273410),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct83 : Covered mP t83 := coveredNode ct81 ct82 (h := [(1024,1199),(1024,14498),(1024,164879),(1024,178178)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct84 : Covered mP t84 := coveredNode ct80 ct83 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct85 : Covered mP t85 := coveredNode cb88 cb89 (h := [(1024,134444),(1024,142498),(1024,145570),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct86 : Covered mP t86 := coveredNode cb90 cb91 (h := [(1024,276482),(1024,407556)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct87 : Covered mP t87 := coveredNode ct85 ct86 (h := [(1024,1199),(1024,3471),(1024,164879),(1024,170287),(1024,407556)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct88 : Covered mP t88 := coveredNode cb92 cb93 (h := [(1024,132367),(1024,134542),(1024,178306),(1024,263244),(1024,268588),(1024,276482),(1024,276546),(1024,276610)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct89 : Covered mP t89 := coveredNode cb94 cb95 (h := [(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct90 : Covered mP t90 := coveredNode ct88 ct89 (h := [(1024,132367),(1024,134542),(1024,145666),(1024,178306),(1024,263311),(1024,276482),(1024,276610)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct91 : Covered mP t91 := coveredNode ct87 ct90 (h := [(1024,1295),(1024,263183),(1024,268588),(1024,269710),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct92 : Covered mP t92 := coveredNode ct84 ct91 (h := [(1024,1295),(1024,273410),(1024,275458),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct93 : Covered mP t93 := coveredNode ct77 ct92 (h := [(1024,11431),(1024,142498),(1024,142503),(1024,175234),(1024,273410),(1024,273800)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct94 : Covered mP t94 := coveredNode cb96 cb97 (h := [(1024,132396),(1024,134159),(1024,134220),(1024,134444),(1024,134542),(1024,268588),(1024,301327),(1024,306308),(1024,396430)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct95 : Covered mP t95 := coveredNode cb98 cb99 (h := [(1024,1295),(1024,68775),(1024,68871),(1024,170052),(1024,263183),(1024,407720)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct96 : Covered mP t96 := coveredNode ct94 ct95 (h := [(1024,1294),(1024,134542),(1024,165007),(1024,269388),(1024,269612),(1024,275458),(1024,306440)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct97 : Covered mP t97 := coveredNode cb100 cb101 (h := [(1024,1294),(1024,134542),(1024,165006),(1024,275458),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct98 : Covered mP t98 := coveredNode cb102 cb103 (h := [(1024,134542),(1024,145796),(1024,268588),(1024,276775),(1024,301327),(1024,396431)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct99 : Covered mP t99 := coveredNode ct97 ct98 (h := [(1024,1294),(1024,69006),(1024,134542),(1024,164940),(1024,273410),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct100 : Covered mP t100 := coveredNode ct96 ct99 (h := [(1024,1295),(1024,263183),(1024,268588),(1024,275458),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct101 : Covered mP t101 := coveredNode cb104 cb105 (h := [(1024,1191),(1024,134542),(1024,142498),(1024,165004),(1024,268588),(1024,276482),(1024,276775),(1024,301327)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct102 : Covered mP t102 := coveredNode cb106 cb107 (h := [(1024,268588),(1024,269612),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct103 : Covered mP t103 := coveredNode ct101 ct102 (h := [(1024,1294),(1024,134542),(1024,177282),(1024,268588),(1024,275458),(1024,406532),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct104 : Covered mP t104 := coveredNode cb108 cb109 (h := [(1024,132367),(1024,134542),(1024,178306),(1024,268588),(1024,276482),(1024,276487),(1024,276610)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct105 : Covered mP t105 := coveredNode cb110 cb111 (h := [(1024,132271),(1024,276770)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct106 : Covered mP t106 := coveredNode ct104 ct105 (h := [(1024,1295),(1024,178306),(1024,268588),(1024,273800),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct107 : Covered mP t107 := coveredNode ct103 ct106 (h := [(1024,132271)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct108 : Covered mP t108 := coveredNode ct100 ct107 (h := [(1024,145570),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct109 : Covered mP t109 := coveredNode cb112 cb113 (h := [(1024,1292),(1024,134542),(1024,165007),(1024,268364),(1024,268588),(1024,306439)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct110 : Covered mP t110 := coveredNode cb114 cb115 (h := [(1024,1292),(1024,11522),(1024,263180),(1024,268588),(1024,273410),(1024,306439)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct111 : Covered mP t111 := coveredNode ct109 ct110 (h := [(1024,1292),(1024,268450),(1024,268588),(1024,273410),(1024,306439)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct112 : Covered mP t112 := coveredNode cb116 cb117 (h := [(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,269711),(1024,276482),(1024,407620),(1024,407816)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct113 : Covered mP t113 := coveredNode cb118 cb119 (h := [(1024,1292),(1024,268364),(1024,268588),(1024,273410),(1024,306439)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct114 : Covered mP t114 := coveredNode ct112 ct113 (h := [(1024,1191),(1024,3239),(1024,11522),(1024,142498),(1024,165004),(1024,268588),(1024,269710)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct115 : Covered mP t115 := coveredNode ct111 ct114 (h := [(1024,1295),(1024,275458),(1024,276482),(1024,306439)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct116 : Covered mP t116 := coveredNode cb120 cb121 (h := [(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct117 : Covered mP t117 := coveredNode cb122 cb123 (h := [(1024,134542),(1024,145796),(1024,273703),(1024,276551),(1024,276775),(1024,301327),(1024,396431)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct118 : Covered mP t118 := coveredNode ct116 ct117 (h := [(1024,132271),(1024,165007),(1024,170284),(1024,175234),(1024,178178),(1024,178247),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct119 : Covered mP t119 := coveredNode cb124 cb125 (h := [(1024,132271),(1024,165007),(1024,178178),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct120 : Covered mP t120 := coveredNode cb126 cb127 (h := [(1024,1295),(1024,66727),(1024,66860),(1024,71980),(1024,134542),(1024,165007),(1024,268588),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct121 : Covered mP t121 := coveredNode ct119 ct120 (h := [(1024,1291),(1024,134311),(1024,134539),(1024,165003),(1024,268292),(1024,268587),(1024,272386)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct122 : Covered mP t122 := coveredNode ct118 ct121 (h := [(1024,1295),(1024,165007),(1024,268591),(1024,273410),(1024,309511)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct123 : Covered mP t123 := coveredNode ct115 ct122 (h := [(1024,1295),(1024,134542),(1024,165007),(1024,178306),(1024,273410),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct124 : Covered mP t124 := coveredNode ct108 ct123 (h := [(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct125 : Covered mP t125 := coveredNode ct93 ct124 (h := [(1024,1295),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct126 : Covered mP t126 := coveredNode ct62 ct125 (h := [(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct127 : Covered mP t127 := coveredNode cb128 cb129 (h := [(1024,132271),(1024,132396)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct128 : Covered mP t128 := coveredNode cb130 cb131 (h := [(1024,1199),(1024,1295)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct129 : Covered mP t129 := coveredNode ct127 ct128 (h := [(1024,178178),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct130 : Covered mP t130 := coveredNode cb132 cb133 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,273410),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct131 : Covered mP t131 := coveredNode cb134 cb135 (h := [(1024,1294),(1024,134542),(1024,165006),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct132 : Covered mP t132 := coveredNode ct130 ct131 (h := [(1024,1295),(1024,178306),(1024,268588),(1024,269710),(1024,273800),(1024,275458),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct133 : Covered mP t133 := coveredNode ct129 ct132 (h := [(1024,132100),(1024,268292),(1024,269710)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct134 : Covered mP t134 := coveredNode cb136 cb137 (h := [(1024,1199),(1024,1292),(1024,1295),(1024,263183),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct135 : Covered mP t135 := coveredNode cb138 cb139 (h := [(1024,400524)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct136 : Covered mP t136 := coveredNode ct134 ct135 (h := [(1024,1295),(1024,134543),(1024,165007),(1024,407556),(1024,407684)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct137 : Covered mP t137 := coveredNode cb140 cb141 (h := [(1024,1292),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct138 : Covered mP t138 := coveredNode cb142 cb143 (h := [(1024,1198),(1024,1292),(1024,1294),(1024,144546),(1024,165006),(1024,275458)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct139 : Covered mP t139 := coveredNode ct137 ct138 (h := [(1024,1292),(1024,1294),(1024,1295),(1024,68775),(1024,164939)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct140 : Covered mP t140 := coveredNode ct136 ct139 (h := [(1024,1324),(1024,11426),(1024,14498),(1024,164879)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct141 : Covered mP t141 := coveredNode ct133 ct140 (h := [(1024,1295),(1024,66823),(1024,134542),(1024,165007),(1024,268354),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct142 : Covered mP t142 := coveredNode cb144 cb145 (h := [(1024,1192),(1024,1295),(1024,296207)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct143 : Covered mP t143 := coveredNode cb146 cb147 (h := [(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct144 : Covered mP t144 := coveredNode ct142 ct143 (h := [(1024,1292),(1024,1294),(1024,1295),(1024,132271),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct145 : Covered mP t145 := coveredNode cb148 cb149 (h := [(1024,132271),(1024,145570),(1024,165007),(1024,175234),(1024,178178),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct146 : Covered mP t146 := coveredNode cb150 cb151 (h := [(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct147 : Covered mP t147 := coveredNode ct145 ct146 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct148 : Covered mP t148 := coveredNode ct144 ct147 (h := [(1024,142728)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct149 : Covered mP t149 := coveredNode cb152 cb153 (h := [(1024,132271),(1024,134542),(1024,178306),(1024,263468),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct150 : Covered mP t150 := coveredNode cb154 cb155 (h := [(1024,145570),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct151 : Covered mP t151 := coveredNode ct149 ct150 (h := [(1024,394244),(1024,396290)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct152 : Covered mP t152 := coveredNode cb156 cb157 (h := [(1024,164879),(1024,263183)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct153 : Covered mP t153 := coveredNode cb158 cb159 (h := [(1024,134542),(1024,142724),(1024,263468),(1024,273410)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct154 : Covered mP t154 := coveredNode ct152 ct153 (h := [(1024,306434),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct155 : Covered mP t155 := coveredNode ct151 ct154 (h := [(1024,14498),(1024,14594),(1024,71980),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct156 : Covered mP t156 := coveredNode ct148 ct155 (h := [(1024,132396),(1024,134444),(1024,263468)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct157 : Covered mP t157 := coveredNode ct141 ct156 (h := [(1024,1294),(1024,1295)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct158 : Covered mP t158 := coveredNode cb160 cb161 (h := [(1024,1295),(1024,11522),(1024,14498),(1024,14594),(1024,76076),(1024,263183),(1024,268588),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct159 : Covered mP t159 := coveredNode cb162 cb163 (h := [(1024,14498),(1024,144546),(1024,145570),(1024,145796)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct160 : Covered mP t160 := coveredNode ct158 ct159 (h := [(1024,142498),(1024,142724),(1024,273410)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct161 : Covered mP t161 := coveredNode cb164 cb165 (h := [(1024,132494),(1024,134542),(1024,145570),(1024,263244)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct162 : Covered mP t162 := coveredNode cb166 cb167 (h := [(1024,1294),(1024,144546),(1024,165006),(1024,406532)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct163 : Covered mP t163 := coveredNode ct161 ct162 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct164 : Covered mP t164 := coveredNode ct160 ct163 (h := [(1024,134542),(1024,145570),(1024,178316)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct165 : Covered mP t165 := coveredNode cb168 cb169 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct166 : Covered mP t166 := coveredNode cb170 cb171 (h := [(1024,165004),(1024,165006),(1024,165007),(1024,263183),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct167 : Covered mP t167 := coveredNode ct165 ct166 (h := [(1024,145570)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct168 : Covered mP t168 := coveredNode cb172 cb173 (h := [(1024,263335),(1024,263468)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct169 : Covered mP t169 := coveredNode cb174 cb175 (h := [(1024,165004),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct170 : Covered mP t170 := coveredNode ct168 ct169 (h := [(1024,1295),(1024,145570),(1024,165006),(1024,165007)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct171 : Covered mP t171 := coveredNode ct167 ct170 (h := [(1024,132271),(1024,142498),(1024,145570),(1024,263244),(1024,263468)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct172 : Covered mP t172 := coveredNode ct164 ct171 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct173 : Covered mP t173 := coveredNode cb176 cb177 (h := [(1024,164878),(1024,165004),(1024,165006),(1024,275458)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct174 : Covered mP t174 := coveredNode cb178 cb179 (h := [(1024,144546),(1024,145570),(1024,145796)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct175 : Covered mP t175 := coveredNode ct173 ct174 (h := [(1024,132271),(1024,134542),(1024,145570),(1024,165007),(1024,268364)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct176 : Covered mP t176 := coveredNode cb180 cb181 (h := [(1024,1295),(1024,14498),(1024,14594),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct177 : Covered mP t177 := coveredNode cb182 cb183 (h := [(1024,134542),(1024,142504),(1024,171148),(1024,268588),(1024,276484),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct178 : Covered mP t178 := coveredNode ct176 ct177 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct179 : Covered mP t179 := coveredNode ct175 ct178 (h := [(1024,1199),(1024,14498),(1024,164879),(1024,178178),(1024,407556),(1024,407620),(1024,407720)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct180 : Covered mP t180 := coveredNode cb184 cb185 (h := [(1024,1292),(1024,76076),(1024,263180),(1024,263335),(1024,268588),(1024,306439)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct181 : Covered mP t181 := coveredNode cb186 cb187 (h := [(1024,165003),(1024,165004),(1024,268292),(1024,273410)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct182 : Covered mP t182 := coveredNode ct180 ct181 (h := [(1024,1295),(1024,145570),(1024,165006),(1024,165007)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct183 : Covered mP t183 := coveredNode cb188 cb189 (h := [(1024,165004),(1024,165006),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct184 : Covered mP t184 := coveredNode cb190 cb191 (h := [(1024,1199),(1024,1292),(1024,1295),(1024,145570)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct185 : Covered mP t185 := coveredNode ct183 ct184 (h := [(1024,145570),(1024,145800)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct186 : Covered mP t186 := coveredNode ct182 ct185 (h := [(1024,145570),(1024,178178),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct187 : Covered mP t187 := coveredNode ct179 ct186 (h := [(1024,165004),(1024,165006),(1024,165007),(1024,268588)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct188 : Covered mP t188 := coveredNode ct172 ct187 (h := [(1024,178180),(1024,396431)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct189 : Covered mP t189 := coveredNode ct157 ct188 (h := [(1024,132263),(1024,134311),(1024,142498),(1024,263335),(1024,263468)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct190 : Covered mP t190 := coveredNode cb192 cb193 (h := [(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct191 : Covered mP t191 := coveredNode cb194 cb195 (h := [(1024,1294),(1024,134542),(1024,165006),(1024,273410),(1024,275458),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct192 : Covered mP t192 := coveredNode ct190 ct191 (h := [(1024,134542),(1024,145570),(1024,145796),(1024,273703),(1024,276482),(1024,276551),(1024,276775),(1024,301327),(1024,396431)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct193 : Covered mP t193 := coveredNode cb196 cb197 (h := [(1024,145570),(1024,268588),(1024,269710),(1024,276482),(1024,276551),(1024,276775),(1024,301327)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct194 : Covered mP t194 := coveredNode cb198 cb199 (h := [(1024,276482),(1024,276872)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct195 : Covered mP t195 := coveredNode ct193 ct194 (h := [(1024,1295),(1024,14594),(1024,178178),(1024,263183),(1024,268588),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct196 : Covered mP t196 := coveredNode ct192 ct195 (h := [(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct197 : Covered mP t197 := coveredNode cb200 cb201 (h := [(1024,132271),(1024,145796),(1024,178178),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct198 : Covered mP t198 := coveredNode cb202 cb203 (h := [(1024,178178),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct199 : Covered mP t199 := coveredNode ct197 ct198 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct200 : Covered mP t200 := coveredNode cb204 cb205 (h := [(1024,145570),(1024,273410),(1024,275458),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct201 : Covered mP t201 := coveredNode cb206 cb207 (h := [(1024,145796),(1024,165007),(1024,178178),(1024,276482),(1024,276775),(1024,396431)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct202 : Covered mP t202 := coveredNode ct200 ct201 (h := [(1024,14594),(1024,145703),(1024,145796),(1024,273474),(1024,275751),(1024,276482),(1024,276610)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct203 : Covered mP t203 := coveredNode ct199 ct202 (h := [(1024,1292),(1024,1294),(1024,1295),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct204 : Covered mP t204 := coveredNode ct196 ct203 (h := [(1024,145570),(1024,276482),(1024,276551)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct205 : Covered mP t205 := coveredNode cb208 cb209 (h := [(1024,178178),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct206 : Covered mP t206 := coveredNode cb210 cb211 (h := [(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct207 : Covered mP t207 := coveredNode ct205 ct206 (h := [(1024,145796),(1024,276482),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct208 : Covered mP t208 := coveredNode cb212 cb213 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct209 : Covered mP t209 := coveredNode cb214 cb215 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct210 : Covered mP t210 := coveredNode ct208 ct209 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,145796),(1024,178306),(1024,268591),(1024,276482),(1024,276775),(1024,309511),(1024,407556)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct211 : Covered mP t211 := coveredNode ct207 ct210 (h := [(1024,1295),(1024,178306),(1024,268588),(1024,269710),(1024,273800),(1024,275458),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct212 : Covered mP t212 := coveredNode cb216 cb217 (h := [(1024,14498),(1024,145570),(1024,145796),(1024,165007),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct213 : Covered mP t213 := coveredNode cb218 cb219 (h := [(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct214 : Covered mP t214 := coveredNode ct212 ct213 (h := [(1024,1295),(1024,145570),(1024,263183),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct215 : Covered mP t215 := coveredNode cb220 cb221 (h := [(1024,1295),(1024,134543),(1024,145570),(1024,165007),(1024,178306),(1024,268588),(1024,276482),(1024,407556),(1024,407684)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct216 : Covered mP t216 := coveredNode cb222 cb223 (h := [(1024,14594),(1024,142498),(1024,145570),(1024,165007),(1024,268588),(1024,269710),(1024,276482),(1024,276775),(1024,276872)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct217 : Covered mP t217 := coveredNode ct215 ct216 (h := [(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct218 : Covered mP t218 := coveredNode ct214 ct217 (h := [(1024,1295),(1024,145570),(1024,273410),(1024,275458),(1024,276482),(1024,276610)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct219 : Covered mP t219 := coveredNode ct211 ct218 (h := [(1024,1295),(1024,71951),(1024,132271),(1024,145570),(1024,145796),(1024,276482),(1024,276775),(1024,276872),(1024,400655)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct220 : Covered mP t220 := coveredNode ct204 ct219 (h := [(1024,14594),(1024,134542),(1024,142498),(1024,145570),(1024,165007),(1024,276482),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct221 : Covered mP t221 := coveredNode cb224 cb225 (h := [(1024,276482),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct222 : Covered mP t222 := coveredNode cb226 cb227 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273703),(1024,276482),(1024,407556)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct223 : Covered mP t223 := coveredNode ct221 ct222 (h := [(1024,145570),(1024,145796),(1024,165007),(1024,178306),(1024,263311),(1024,276482),(1024,276610),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct224 : Covered mP t224 := coveredNode cb228 cb229 (h := [(1024,145570),(1024,276482),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct225 : Covered mP t225 := coveredNode cb230 cb231 (h := [(1024,68775),(1024,69003),(1024,75938),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct226 : Covered mP t226 := coveredNode ct224 ct225 (h := [(1024,145570),(1024,145796),(1024,178306)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct227 : Covered mP t227 := coveredNode ct223 ct226 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,273410),(1024,273474),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct228 : Covered mP t228 := coveredNode cb232 cb233 (h := [(1024,1295),(1024,145796),(1024,165007),(1024,178306),(1024,268588),(1024,275458),(1024,276482),(1024,276775),(1024,396431)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct229 : Covered mP t229 := coveredNode cb234 cb235 (h := [(1024,1295),(1024,134542),(1024,178306),(1024,268588),(1024,276482),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct230 : Covered mP t230 := coveredNode ct228 ct229 (h := [(1024,1294),(1024,134542),(1024,142498),(1024,144546),(1024,165006),(1024,301326),(1024,400654),(1024,406660)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct231 : Covered mP t231 := coveredNode cb236 cb237 (h := [(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,275458),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct232 : Covered mP t232 := coveredNode cb238 cb239 (h := [(1024,1292),(1024,165004),(1024,268588),(1024,273410),(1024,306439)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct233 : Covered mP t233 := coveredNode ct231 ct232 (h := [(1024,14594),(1024,142498),(1024,145570),(1024,165007),(1024,269710),(1024,276482),(1024,276775),(1024,276872)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct234 : Covered mP t234 := coveredNode ct230 ct233 (h := [(1024,1295),(1024,134542),(1024,268588),(1024,276482),(1024,276775),(1024,276872),(1024,301327),(1024,400655)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct235 : Covered mP t235 := coveredNode ct227 ct234 (h := [(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct236 : Covered mP t236 := coveredNode cb240 cb241 (h := [(1024,145570),(1024,276482),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct237 : Covered mP t237 := coveredNode cb242 cb243 (h := [(1024,145570),(1024,276482),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct238 : Covered mP t238 := coveredNode ct236 ct237 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,268591),(1024,276482),(1024,309511),(1024,407556)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct239 : Covered mP t239 := coveredNode cb244 cb245 (h := [(1024,1294),(1024,134542),(1024,144546),(1024,301326),(1024,400654)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct240 : Covered mP t240 := coveredNode cb246 cb247 (h := [(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,269710),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct241 : Covered mP t241 := coveredNode ct239 ct240 (h := [(1024,132271),(1024,134542),(1024,145570),(1024,165007)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct242 : Covered mP t242 := coveredNode ct238 ct241 (h := [(1024,1292),(1024,1294),(1024,1295),(1024,142498),(1024,145570),(1024,165007),(1024,276482),(1024,301327)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct243 : Covered mP t243 := coveredNode cb248 cb249 (h := [(1024,1295),(1024,144546),(1024,145570),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct244 : Covered mP t244 := coveredNode cb250 cb251 (h := [(1024,145570),(1024,165004),(1024,165006),(1024,165007),(1024,276482),(1024,276610),(1024,396431)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct245 : Covered mP t245 := coveredNode ct243 ct244 (h := [(1024,164879),(1024,165004),(1024,165007),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct246 : Covered mP t246 := coveredNode cb252 cb253 (h := [(1024,145570),(1024,276482),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct247 : Covered mP t247 := coveredNode cb254 cb255 (h := [(1024,145570),(1024,276482),(1024,276775),(1024,276872)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct248 : Covered mP t248 := coveredNode ct246 ct247 (h := []) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct249 : Covered mP t249 := coveredNode ct245 ct248 (h := [(1024,263183),(1024,276482),(1024,276775)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct250 : Covered mP t250 := coveredNode ct242 ct249 (h := [(1024,134542),(1024,145570),(1024,145796),(1024,263244),(1024,276482),(1024,276872)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct251 : Covered mP t251 := coveredNode ct235 ct250 (h := [(1024,1295),(1024,134542),(1024,145570),(1024,165007),(1024,178306),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct252 : Covered mP t252 := coveredNode ct220 ct251 (h := [(1024,1295),(1024,145570),(1024,165007),(1024,273410),(1024,276482)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct253 : Covered mP t253 := coveredNode ct189 ct252 (h := [(1024,145570),(1024,165007),(1024,269710),(1024,275596),(1024,276620)]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct254 : Covered mP t254 := coveredNode ct126 ct253 (h := [(1024,132271),(1024,145570),(1024,165007),(1024,178178),(1024,178180),(1024,178306)]) (by decide +kernel)
theorem hT_cert : Covered mP T_cert := ct254
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266837 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by

  rintro ⟨C,hfan,hsize,hr⟩
  let f : BFn 5 := fun x => C.eval (List.ofFn x)
  have he (p : Fin 5 × Fin 5) : f (pt 5 (pairCode p)) = reference (pt 5 (pairCode p)) := by
    obtain ⟨i,j⟩ := p
    change C.eval (List.ofFn (pt 5 (pairCode (i,j)))) = _
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
  have nc : ∃ x y : Fin 5 → Bool, f x ≠ f y := by
    refine ⟨pt 5 (pairCode (0,0)),pt 5 (pairCode (0,1)),?_⟩
    rw [he (0,0),he (0,1)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 9 10 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 9 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end PEqualNP.Outside.L_meta_24070.Lower

theorem PEqualNP.Outside.L_meta_24070 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266837 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := PEqualNP.Outside.L_meta_24070.Lower.lower
