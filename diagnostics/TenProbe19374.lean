import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19374.Probes

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
def probeRoots : List (List Nat × Nat) := [([7,9,24,32,98,192,512],102465),([7,9,24,32,132,192,512],102433),([7,24,32,98,132,192,272],271461),([7,9,24,32,98,512,768],102465),([7,9,24,32,132,512,768],102433),([7,24,32,98,132,272,768],271461),([7,9,24,98,192,512,768],102465),([7,9,24,132,192,512,768],102433),([7,24,98,132,192,272,768],271461),([7,9,32,98,192,512,768],102465),([7,9,32,132,192,512,768],102433),([7,32,98,132,192,272,768],266346),([7,9,32,98,132,272,768],72801),([7,9,32,98,272,512,768],105537),([7,9,32,98,132,512,768],72801),([7,9,32,132,272,512,768],72801),([7,32,98,132,272,512,768],65640),([7,9,98,132,192,272,768],37985),([7,9,98,192,272,512,768],37985),([7,9,98,132,192,512,768],37985),([7,9,132,192,272,512,768],103457),([7,98,132,192,272,512,768],32870),([9,24,32,98,192,512,768],98373),([9,24,32,132,192,512,768],98341),([24,32,98,132,192,272,768],271461),([9,24,32,98,132,192,272],98565),([9,24,32,98,192,272,512],98565),([9,24,32,98,132,192,512],98565),([9,24,32,132,192,272,512],98565),([24,32,98,132,192,272,512],262245)]
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
def samplePairs : List (Fin 5 × Fin 5) := [(0, 0), (0, 1), (0, 3), (1, 0), (1, 2), (2, 1), (3, 1), (3, 3), (4, 2), (4, 4)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) = (7571262 : ℕ).testBit (5 * p.1.val + p.2.val)
def M_ : ℕ := 1023

def Y_ : ℕ := 334

def XS_ : List ℕ := [7, 24, 32, 192, 768, 9, 98, 272, 132, 512]

def PD_ : List (ℕ × ℕ) := [(1, 489), (2, 29), (3, 103), (4, 26), (5, 4), (6, 11), (7, 4), (8, 3)]

def PM_ : List (ℕ × ℕ) := [(0, 334), (4, 334), (5, 334), (7, 334), (9, 334)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,15,378,964] BT.lf) [2,15,476,866] (BT.nd BT.lf [2,98,476,783] BT.lf)) [2,196,378,783] (BT.nd (BT.nd BT.lf [3,7,8,370,964] BT.lf) [3,7,8,468,866] BT.lf)) [3,7,9,378,964] (BT.nd (BT.nd (BT.nd BT.lf [3,7,9,476,866] BT.lf) [3,7,98,196,264] (BT.nd BT.lf [3,7,98,476,777] BT.lf)) [3,7,132,378,969] (BT.nd (BT.nd BT.lf [3,7,196,378,777] BT.lf) [3,7,201,378,900] BT.lf))) [3,7,329] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,8,98,279,964] BT.lf) [3,8,98,468,775] (BT.nd BT.lf [3,8,196,279,866] BT.lf)) [3,8,196,370,775] (BT.nd (BT.nd BT.lf [3,9,24,343] BT.lf) [3,9,24,680] BT.lf)) [3,9,56,375] (BT.nd (BT.nd (BT.nd BT.lf [3,9,56,648] BT.lf) [3,9,98,476,775] BT.lf) [3,9,152,471] (BT.nd (BT.nd BT.lf [3,9,196,378,775] BT.lf) [3,9,327] BT.lf)))) [3,9,343,999] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,9,375,967] BT.lf) [3,9,471,871] (BT.nd BT.lf [3,9,696] BT.lf)) [3,15,24,370,964] (BT.nd (BT.nd BT.lf [3,15,24,468,866] BT.lf) [3,15,98,220,256] BT.lf)) [3,15,98,280,964] (BT.nd (BT.nd (BT.nd BT.lf [3,15,98,476,768] BT.lf) [3,15,122,196,256] BT.lf) [3,15,122,272,964] (BT.nd (BT.nd BT.lf [3,15,132,378,960] BT.lf) [3,15,132,472,866] BT.lf))) [3,15,156,370,960] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,15,156,464,866] BT.lf) [3,15,192,378,900] (BT.nd BT.lf [3,15,192,412,866] BT.lf)) [3,15,196,280,866] (BT.nd (BT.nd BT.lf [3,15,196,378,768] BT.lf) [3,15,216,404,866] BT.lf)) [3,15,220,272,866] (BT.nd (BT.nd (BT.nd BT.lf [3,24,41,375] BT.lf) [3,24,41,648] BT.lf) [3,24,98,468,783] (BT.nd (BT.nd BT.lf [3,24,137,471] BT.lf) [3,24,196,370,783] BT.lf))))) [3,24,272,937] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,24,343,1014] BT.lf) [3,24,375,982] (BT.nd BT.lf [3,24,681] BT.lf)) [3,25,343] (BT.nd (BT.nd BT.lf [3,41,359] BT.lf) [3,41,375,999] BT.lf)) [3,41,664] (BT.nd (BT.nd (BT.nd BT.lf [3,56,374] BT.lf) [3,56,375,1014] (BT.nd BT.lf [3,56,649] BT.lf)) [3,57,375] (BT.nd (BT.nd BT.lf [3,60,370] BT.lf) [3,71,265] BT.lf))) [3,73,88,279] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,73,263] BT.lf) [3,89,279] (BT.nd BT.lf [3,98,132,472,783] BT.lf)) [3,98,156,464,783] (BT.nd (BT.nd BT.lf [3,98,192,412,783] BT.lf) [3,98,196,280,783] BT.lf)) [3,98,216,404,783] (BT.nd (BT.nd (BT.nd BT.lf [3,98,220,272,783] BT.lf) [3,103,297] BT.lf) [3,122,192,404,783] (BT.nd (BT.nd BT.lf [3,122,196,272,783] BT.lf) [3,122,201,404,775] BT.lf)))) [3,122,308] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,126,304] BT.lf) [3,132,192,378,783] (BT.nd BT.lf [3,132,201,378,775] BT.lf)) [3,135,457] (BT.nd (BT.nd BT.lf [3,137,568] BT.lf) [3,152,553] BT.lf)) [3,156,192,370,783] (BT.nd (BT.nd (BT.nd BT.lf [3,156,466] BT.lf) [3,158,464] BT.lf) [3,169,536] (BT.nd (BT.nd BT.lf [3,184,521] BT.lf) [3,188,498] BT.lf))) [3,201,391] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,216,406] BT.lf) [3,217,407] (BT.nd BT.lf [3,218,404] BT.lf)) [3,250,436] (BT.nd (BT.nd BT.lf [3,519,841] BT.lf) [3,521,839] BT.lf)) [3,553,871] (BT.nd (BT.nd (BT.nd BT.lf [3,583,777] BT.lf) [3,585,775] BT.lf) [3,615,809] (BT.nd (BT.nd BT.lf [3,647,969] BT.lf) [3,713,903] BT.lf)))))) [4,2,156,464] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2,216,404] BT.lf) [4,4,56,370] (BT.nd BT.lf [4,4,122,304] BT.lf)) [4,7,8,98,196,256] (BT.nd (BT.nd BT.lf [4,7,8,98,272,964] BT.lf) [4,7,8,98,468,768] BT.lf)) [4,7,8,132,370,960] (BT.nd (BT.nd (BT.nd BT.lf [4,7,8,132,464,866] BT.lf) [4,7,8,192,370,900] (BT.nd BT.lf [4,7,8,192,404,866] BT.lf)) [4,7,8,196,272,866] (BT.nd (BT.nd BT.lf [4,7,8,196,370,768] BT.lf) [4,7,9,24,336] BT.lf))) [4,7,9,24,338] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,9,24,343] BT.lf) [4,7,9,24,345] (BT.nd BT.lf [4,7,9,24,370,964] BT.lf)) [4,7,9,24,468,866] (BT.nd (BT.nd BT.lf [4,7,9,24,685] BT.lf) [4,7,9,24,687] BT.lf)) [4,7,9,31,336] (BT.nd (BT.nd (BT.nd BT.lf [4,7,9,41,668] BT.lf) [4,7,9,56,370] BT.lf) [4,7,9,56,375] (BT.nd (BT.nd BT.lf [4,7,9,56,653] BT.lf) [4,7,9,98,220,256] BT.lf)))) [4,7,9,98,280,964] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,9,98,476,768] BT.lf) [4,7,9,98,700] (BT.nd BT.lf [4,7,9,122,196,256] BT.lf)) [4,7,9,122,272,964] (BT.nd (BT.nd BT.lf [4,7,9,132,378,960] BT.lf) [4,7,9,132,472,866] BT.lf)) [4,7,9,141,568] (BT.nd (BT.nd (BT.nd BT.lf [4,7,9,152,464] BT.lf) [4,7,9,156,370,960] BT.lf) [4,7,9,156,464] (BT.nd (BT.nd BT.lf [4,7,9,156,464,866] BT.lf) [4,7,9,156,468] BT.lf))) [4,7,9,156,471] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,9,156,473] BT.lf) [4,7,9,156,553] (BT.nd BT.lf [4,7,9,156,559] BT.lf)) [4,7,9,159,464] (BT.nd (BT.nd BT.lf [4,7,9,173,536] BT.lf) [4,7,9,188,370] BT.lf)) [4,7,9,188,521] (BT.nd (BT.nd (BT.nd BT.lf [4,7,9,192,378,900] BT.lf) [4,7,9,192,412,866] BT.lf) [4,7,9,196,280,866] (BT.nd (BT.nd BT.lf [4,7,9,196,378,768] BT.lf) [4,7,9,216,404,866] BT.lf))))) [4,7,9,220,272,866] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,9,320] BT.lf) [4,7,9,336,999] (BT.nd BT.lf [4,7,9,370,967] BT.lf)) [4,7,9,375,960] (BT.nd (BT.nd BT.lf [4,7,9,464,867] BT.lf) [4,7,9,464,871] BT.lf)) [4,7,9,471,866] (BT.nd (BT.nd (BT.nd BT.lf [4,7,9,700] BT.lf) [4,7,24,41,370] BT.lf) [4,7,24,41,375] (BT.nd (BT.nd BT.lf [4,7,24,41,653] BT.lf) [4,7,24,73,281] BT.lf))) [4,7,24,73,336] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,24,98,468,777] BT.lf) [4,7,24,132,370,969] (BT.nd BT.lf [4,7,24,137,464] BT.lf)) [4,7,24,141,468] (BT.nd (BT.nd BT.lf [4,7,24,141,553] BT.lf) [4,7,24,173,521] BT.lf)) [4,7,24,196,370,777] (BT.nd (BT.nd (BT.nd BT.lf [4,7,24,201,370,900] BT.lf) [4,7,24,201,404,866] BT.lf) [4,7,24,336,345] (BT.nd (BT.nd BT.lf [4,7,24,336,1014] BT.lf) [4,7,24,370,982] BT.lf)))) [4,7,25,336] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,41,141,536] BT.lf) [4,7,41,156,521] (BT.nd BT.lf [4,7,41,354] BT.lf)) [4,7,41,370,999] (BT.nd (BT.nd BT.lf [4,7,41,668] BT.lf) [4,7,56,141,521] BT.lf)) [4,7,56,370,1014] (BT.nd (BT.nd (BT.nd BT.lf [4,7,57,370] BT.lf) [4,7,64,265] BT.lf) [4,7,73,88,272] (BT.nd (BT.nd BT.lf [4,7,73,256] BT.lf) [4,7,89,272] BT.lf))) [4,7,98,132,192,264] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,98,132,280,969] BT.lf) [4,7,98,132,472,777] (BT.nd BT.lf [4,7,98,156,464,777] BT.lf)) [4,7,98,192,412,777] (BT.nd (BT.nd BT.lf [4,7,98,196,280,777] BT.lf) [4,7,98,201,280,900] BT.lf)) [4,7,98,216,404,777] (BT.nd (BT.nd (BT.nd BT.lf [4,7,98,220,272,777] BT.lf) [4,7,98,297] BT.lf) [4,7,122,132,201,256] (BT.nd (BT.nd BT.lf [4,7,122,132,272,969] BT.lf) [4,7,122,192,404,777] BT.lf))))))) [4,7,122,196,272,777] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,122,201,272,900] BT.lf) [4,7,122,201,404,768] (BT.nd BT.lf [4,7,122,201,644] BT.lf)) [4,7,122,713] (BT.nd (BT.nd BT.lf [4,7,132,192,378,777] BT.lf) [4,7,132,201,280,866] BT.lf)) [4,7,132,201,378,768] (BT.nd (BT.nd (BT.nd BT.lf [4,7,132,201,634] BT.lf) [4,7,132,457] (BT.nd BT.lf [4,7,156,192,370,777] BT.lf)) [4,7,156,201,281] (BT.nd (BT.nd BT.lf [4,7,156,464,473] BT.lf) [4,7,156,464,1014] BT.lf))) [4,7,156,553] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,188,521] BT.lf) [4,7,201,388] (BT.nd BT.lf [4,7,201,634] BT.lf)) [4,7,217,404] (BT.nd (BT.nd BT.lf [4,7,370,964] BT.lf) [4,7,468,866] BT.lf)) [4,7,512,841] (BT.nd (BT.nd (BT.nd BT.lf [4,7,521,832] BT.lf) [4,7,553,866] BT.lf) [4,7,576,777] (BT.nd (BT.nd BT.lf [4,7,585,768] BT.lf) [4,7,610,809] BT.lf)))) [4,7,644,969] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,713,900] BT.lf) [4,8,98,132,279,960] (BT.nd BT.lf [4,8,98,132,464,775] BT.lf)) [4,8,98,192,279,900] (BT.nd (BT.nd BT.lf [4,8,98,192,404,775] BT.lf) [4,8,98,196,272,775] BT.lf)) [4,8,98,196,279,768] (BT.nd (BT.nd (BT.nd BT.lf [4,8,132,192,279,866] BT.lf) [4,8,132,192,370,775] BT.lf) [4,9,24,31,336] (BT.nd (BT.nd BT.lf [4,9,24,32,343] BT.lf) [4,9,24,32,375] BT.lf))) [4,9,24,32,648] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,24,41,375] BT.lf) [4,9,24,56,375] (BT.nd BT.lf [4,9,24,64,279] BT.lf)) [4,9,24,64,343] (BT.nd (BT.nd BT.lf [4,9,24,64,744] BT.lf) [4,9,24,66,279] BT.lf)) [4,9,24,71,272] (BT.nd (BT.nd (BT.nd BT.lf [4,9,24,71,279] BT.lf) [4,9,24,71,281] BT.lf) [4,9,24,71,336] (BT.nd (BT.nd BT.lf [4,9,24,71,343] BT.lf) [4,9,24,71,751] BT.lf))))) [4,9,24,73,279] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,24,88,279] BT.lf) [4,9,24,95,272] (BT.nd BT.lf [4,9,24,98,279,964] BT.lf)) [4,9,24,98,343] (BT.nd (BT.nd BT.lf [4,9,24,98,468,775] BT.lf) [4,9,24,128,471] BT.lf)) [4,9,24,132,343] (BT.nd (BT.nd (BT.nd BT.lf [4,9,24,192,343] BT.lf) [4,9,24,196,279,866] (BT.nd BT.lf [4,9,24,196,370,775] BT.lf)) [4,9,24,272,343] (BT.nd (BT.nd BT.lf [4,9,24,272,928] BT.lf) [4,9,24,272,952] BT.lf))) [4,9,24,279,336] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,24,279,343] BT.lf) [4,9,24,279,676] (BT.nd BT.lf [4,9,24,279,932] BT.lf)) [4,9,24,279,957] (BT.nd (BT.nd BT.lf [4,9,24,279,959] BT.lf) [4,9,24,336,343] BT.lf)) [4,9,24,336,1016] (BT.nd (BT.nd (BT.nd BT.lf [4,9,24,343] BT.lf) [4,9,24,343,512] BT.lf) [4,9,24,343,768] (BT.nd (BT.nd BT.lf [4,9,24,375,471] BT.lf) [4,9,24,375,544] BT.lf)))) [4,9,24,375,991] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,24,672] BT.lf) [4,9,31,88,272] (BT.nd BT.lf [4,9,31,135,464] BT.lf)) [4,9,32,56,375] (BT.nd (BT.nd BT.lf [4,9,32,359] BT.lf) [4,9,32,375,999] BT.lf)) [4,9,32,664] (BT.nd (BT.nd (BT.nd BT.lf [4,9,39,56,370] BT.lf) [4,9,56,98,279] BT.lf) [4,9,56,98,311] (BT.nd (BT.nd BT.lf [4,9,56,98,375] BT.lf) [4,9,56,98,744] BT.lf))) [4,9,56,103,272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,56,103,279] BT.lf) [4,9,56,103,281] (BT.nd BT.lf [4,9,56,103,304] BT.lf)) [4,9,56,103,370] (BT.nd (BT.nd BT.lf [4,9,56,103,375] BT.lf) [4,9,56,103,751] BT.lf)) [4,9,56,132,375] (BT.nd (BT.nd (BT.nd BT.lf [4,9,56,192,375] BT.lf) [4,9,56,272,375] BT.lf) [4,9,56,272,920] (BT.nd (BT.nd BT.lf [4,9,56,279,370] BT.lf) [4,9,56,279,375] BT.lf)))))) [4,9,56,279,925] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,56,370,375] BT.lf) [4,9,56,370,1016] (BT.nd BT.lf [4,9,56,375] BT.lf)) [4,9,56,375,512] (BT.nd (BT.nd BT.lf [4,9,56,375,768] BT.lf) [4,9,56,640] BT.lf)) [4,9,64,88,279] (BT.nd (BT.nd (BT.nd BT.lf [4,9,64,263] BT.lf) [4,9,64,279,999] (BT.nd BT.lf [4,9,71,88,272] BT.lf)) [4,9,71,95,272] (BT.nd (BT.nd BT.lf [4,9,71,256] BT.lf) [4,9,71,272,999] BT.lf))) [4,9,88,279] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,98,132,472,775] BT.lf) [4,9,98,156,464,775] (BT.nd BT.lf [4,9,98,192,412,775] BT.lf)) [4,9,98,196,280,775] (BT.nd (BT.nd BT.lf [4,9,98,216,279,900] BT.lf) [4,9,98,216,404,775] BT.lf)) [4,9,98,216,471] (BT.nd (BT.nd (BT.nd BT.lf [4,9,98,220,272,775] BT.lf) [4,9,98,279,967] BT.lf) [4,9,98,471,775] (BT.nd (BT.nd BT.lf [4,9,103,272,967] BT.lf) [4,9,103,279,960] BT.lf)))) [4,9,103,288] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,103,464,775] BT.lf) [4,9,103,471,768] (BT.nd BT.lf [4,9,122,192,404,775] BT.lf)) [4,9,122,196,272,775] (BT.nd (BT.nd BT.lf [4,9,128,568] BT.lf) [4,9,132,192,378,775] BT.lf)) [4,9,132,216,279,866] (BT.nd (BT.nd (BT.nd BT.lf [4,9,135,448] BT.lf) [4,9,152,192,279] BT.lf) [4,9,152,199,272] (BT.nd (BT.nd BT.lf [4,9,152,544] BT.lf) [4,9,156,192,370,775] BT.lf))) [4,9,156,196,279] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,156,199,279] BT.lf) [4,9,156,464,471] (BT.nd BT.lf [4,9,156,464,1016] BT.lf)) [4,9,160,536] (BT.nd (BT.nd BT.lf [4,9,184,512] BT.lf) [4,9,192,279,871] BT.lf)) [4,9,192,375,775] (BT.nd (BT.nd (BT.nd BT.lf [4,9,192,391] BT.lf) [4,9,199,272,871] BT.lf) [4,9,199,279,866] (BT.nd (BT.nd BT.lf [4,9,199,370,775] BT.lf) [4,9,199,375,768] BT.lf))))) [4,9,216,407] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,512,839] BT.lf) [4,9,519,832] (BT.nd BT.lf [4,9,544,871] BT.lf)) [4,9,576,775] (BT.nd (BT.nd BT.lf [4,9,583,768] BT.lf) [4,9,615,800] BT.lf)) [4,9,647,960] (BT.nd (BT.nd (BT.nd BT.lf [4,9,704,903] BT.lf) [4,15,24,98,196,256] BT.lf) [4,15,24,98,272,964] (BT.nd (BT.nd BT.lf [4,15,24,98,468,768] BT.lf) [4,15,24,132,370,960] BT.lf))) [4,15,24,132,464,866] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,15,24,192,370,900] BT.lf) [4,15,24,192,404,866] (BT.nd BT.lf [4,15,24,196,272,866] BT.lf)) [4,15,24,196,370,768] (BT.nd (BT.nd BT.lf [4,15,98,132,216,256] BT.lf) [4,15,98,132,280,960] BT.lf)) [4,15,98,132,472,768] (BT.nd (BT.nd (BT.nd BT.lf [4,15,98,156,192,256] BT.lf) [4,15,98,156,272,960] BT.lf) [4,15,98,156,464,768] (BT.nd (BT.nd BT.lf [4,15,98,192,280,900] BT.lf) [4,15,98,192,412,768] BT.lf)))) [4,15,98,196,280,768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,15,98,216,272,900] BT.lf) [4,15,98,216,404,768] (BT.nd BT.lf [4,15,98,220,272,768] BT.lf)) [4,15,122,132,192,256] (BT.nd (BT.nd BT.lf [4,15,122,132,272,960] BT.lf) [4,15,122,192,272,900] BT.lf)) [4,15,122,192,404,768] (BT.nd (BT.nd (BT.nd BT.lf [4,15,122,196,272,768] BT.lf) [4,15,132,192,280,866] BT.lf) [4,15,132,192,378,768] (BT.nd (BT.nd BT.lf [4,15,132,216,272,866] BT.lf) [4,15,156,192,272,866] BT.lf))) [4,15,156,192,370,768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,24,32,41,375] BT.lf) [4,24,32,272,905] (BT.nd BT.lf [4,24,32,374] BT.lf)) [4,24,32,375,1014] (BT.nd (BT.nd BT.lf [4,24,32,649] BT.lf) [4,24,36,370] BT.lf)) [4,24,39,41,370] (BT.nd (BT.nd (BT.nd BT.lf [4,24,41,98,279] BT.lf) [4,24,41,98,311] BT.lf) [4,24,41,98,375] (BT.nd (BT.nd BT.lf [4,24,41,98,744] BT.lf) [4,24,41,103,272] BT.lf)))))))) [4,24,41,103,279] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,24,41,103,304] BT.lf) [4,24,41,103,313] (BT.nd BT.lf [4,24,41,103,370] BT.lf)) [4,24,41,103,375] (BT.nd (BT.nd BT.lf [4,24,41,103,751] BT.lf) [4,24,41,127,272] BT.lf)) [4,24,41,132,375] (BT.nd (BT.nd (BT.nd BT.lf [4,24,41,192,375] BT.lf) [4,24,41,272,375] (BT.nd BT.lf [4,24,41,272,896] BT.lf)) [4,24,41,272,920] (BT.nd (BT.nd BT.lf [4,24,41,279,370] BT.lf) [4,24,41,279,375] BT.lf))) [4,24,41,279,925] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,24,41,370,375] BT.lf) [4,24,41,370,1016] (BT.nd BT.lf [4,24,41,375] BT.lf)) [4,24,41,375,512] (BT.nd (BT.nd BT.lf [4,24,41,375,768] BT.lf) [4,24,41,640] BT.lf)) [4,24,64,73,279] (BT.nd (BT.nd (BT.nd BT.lf [4,24,64,279,1014] BT.lf) [4,24,71,272,281] BT.lf) [4,24,71,272,777] (BT.nd (BT.nd BT.lf [4,24,71,272,1014] BT.lf) [4,24,73,279] BT.lf)))) [4,24,98,132,464,783] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,24,98,192,404,783] BT.lf) [4,24,98,196,272,783] (BT.nd BT.lf [4,24,98,201,279,900] BT.lf)) [4,24,98,201,404,775] (BT.nd (BT.nd BT.lf [4,24,98,201,471] BT.lf) [4,24,98,279,982] BT.lf)) [4,24,98,308] (BT.nd (BT.nd (BT.nd BT.lf [4,24,102,304] BT.lf) [4,24,103,272,313] BT.lf) [4,24,103,272,809] (BT.nd (BT.nd BT.lf [4,24,103,272,982] BT.lf) [4,24,103,281,304] BT.lf))) [4,24,128,272,809] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,24,128,553] BT.lf) [4,24,132,192,370,783] (BT.nd BT.lf [4,24,132,201,279,866] BT.lf)) [4,24,132,201,370,775] (BT.nd (BT.nd BT.lf [4,24,132,466] BT.lf) [4,24,134,464] BT.lf)) [4,24,137,192,279] (BT.nd (BT.nd (BT.nd BT.lf [4,24,137,199,272] BT.lf) [4,24,137,272,800] BT.lf) [4,24,137,544] (BT.nd (BT.nd BT.lf [4,24,141,196,279] BT.lf) [4,24,160,272,777] BT.lf))))) [4,24,160,521] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,24,164,498] BT.lf) [4,24,169,272,768] (BT.nd BT.lf [4,24,169,512] BT.lf)) [4,24,192,406] (BT.nd (BT.nd BT.lf [4,24,194,404] BT.lf) [4,24,201,407] BT.lf)) [4,24,226,436] (BT.nd (BT.nd (BT.nd BT.lf [4,25,32,375] BT.lf) [4,25,64,279] (BT.nd BT.lf [4,25,71,272] BT.lf)) [4,25,103,304] (BT.nd (BT.nd BT.lf [4,25,135,464] BT.lf) [4,25,192,407] BT.lf))) [4,26,132,464] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,26,192,404] BT.lf) [4,28,32,370] (BT.nd BT.lf [4,28,98,304] BT.lf)) [4,32,103,265] (BT.nd (BT.nd BT.lf [4,32,122,276] BT.lf) [4,32,126,272] BT.lf)) [4,32,137,536] (BT.nd (BT.nd (BT.nd BT.lf [4,32,152,521] BT.lf) [4,32,156,498] BT.lf) [4,32,250,404] (BT.nd (BT.nd BT.lf [4,32,521,871] BT.lf) [4,32,615,777] BT.lf)))) [4,36,122,272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,41,98,263] BT.lf) [4,41,98,279,999] (BT.nd BT.lf [4,41,98,728] BT.lf)) [4,41,103,127,272] (BT.nd (BT.nd BT.lf [4,41,103,256] BT.lf) [4,41,103,272,999] BT.lf)) [4,41,128,536] (BT.nd (BT.nd (BT.nd BT.lf [4,41,152,512] BT.lf) [4,41,512,871] BT.lf) [4,41,615,768] (BT.nd (BT.nd BT.lf [4,56,98,276] BT.lf) [4,56,98,279,1014] BT.lf))) [4,56,98,713] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,56,102,272] BT.lf) [4,56,103,272,281] (BT.nd BT.lf [4,56,103,272,1014] BT.lf)) [4,56,128,521] (BT.nd (BT.nd BT.lf [4,56,132,498] BT.lf) [4,56,137,512] BT.lf)) [4,56,226,404] (BT.nd (BT.nd (BT.nd BT.lf [4,57,98,279] BT.lf) [4,57,103,272] BT.lf) [4,60,98,272] (BT.nd (BT.nd BT.lf [4,64,519,777] BT.lf) [4,64,521,775] BT.lf)))))) [4,71,512,777] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,71,521,768] BT.lf) [4,73,512,775] (BT.nd BT.lf [4,73,519,768] BT.lf)) [4,98,132,192,280,783] (BT.nd (BT.nd BT.lf [4,98,132,201,280,775] BT.lf) [4,98,132,216,272,783] BT.lf)) [4,98,156,192,272,783] (BT.nd (BT.nd (BT.nd BT.lf [4,98,188,464] BT.lf) [4,98,201,568] (BT.nd BT.lf [4,98,216,436] BT.lf)) [4,98,216,553] (BT.nd (BT.nd BT.lf [4,98,279,932] BT.lf) [4,98,279,964] BT.lf))) [4,98,436,775] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,98,468,775] BT.lf) [4,98,519,809] (BT.nd BT.lf [4,98,553,775] BT.lf)) [4,103,512,809] (BT.nd (BT.nd BT.lf [4,103,521,800] BT.lf) [4,103,544,777] BT.lf)) [4,103,553,768] (BT.nd (BT.nd (BT.nd BT.lf [4,122,132,192,272,783] BT.lf) [4,122,132,201,272,775] BT.lf) [4,122,192,436] (BT.nd (BT.nd BT.lf [4,132,201,216,279] BT.lf) [4,132,201,263] BT.lf)))) [4,132,216,274] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,132,217,279] BT.lf) [4,132,218,272] (BT.nd BT.lf [4,132,250,304] BT.lf)) [4,132,519,969] (BT.nd (BT.nd BT.lf [4,132,713,775] BT.lf) [4,134,216,272] BT.lf)) [4,135,192,265] (BT.nd (BT.nd (BT.nd BT.lf [4,135,201,256] BT.lf) [4,135,201,272,800] BT.lf) [4,135,201,304,768] (BT.nd (BT.nd BT.lf [4,135,217,272] BT.lf) [4,135,512,969] BT.lf))) [4,135,521,960] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,135,704,777] BT.lf) [4,135,713,768] (BT.nd BT.lf [4,156,192,274] BT.lf)) [4,156,194,272] (BT.nd (BT.nd BT.lf [4,156,226,304] BT.lf) [4,158,192,272] BT.lf)) [4,164,250,272] (BT.nd (BT.nd (BT.nd BT.lf [4,188,192,370] BT.lf) [4,188,226,272] BT.lf) [4,192,521,903] (BT.nd (BT.nd BT.lf [4,192,647,777] BT.lf) [4,196,279,866] BT.lf))))) [4,196,370,775] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,201,512,903] BT.lf) [4,201,647,768] (BT.nd BT.lf [5,2,24,132,464] BT.lf)) [5,2,24,192,404] (BT.nd (BT.nd BT.lf [5,2,132,216,272] BT.lf) [5,2,156,192,272] BT.lf)) [5,4,24,32,370] (BT.nd (BT.nd (BT.nd BT.lf [5,4,24,98,304] BT.lf) [5,4,32,122,272] BT.lf) [5,4,56,98,272] (BT.nd (BT.nd BT.lf [5,7,8,98,132,192,256] BT.lf) [5,7,8,98,132,272,960] BT.lf))) [5,7,8,98,132,464,768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,8,98,192,272,900] BT.lf) [5,7,8,98,192,404,768] (BT.nd BT.lf [5,7,8,98,196,272,768] BT.lf)) [5,7,8,132,192,272,866] (BT.nd (BT.nd BT.lf [5,7,8,132,192,370,768] BT.lf) [5,7,9,24,32,336] BT.lf)) [5,7,9,24,32,370] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,24,32,375] BT.lf) [5,7,9,24,32,653] BT.lf) [5,7,9,24,39,370] (BT.nd (BT.nd BT.lf [5,7,9,24,41,370] BT.lf) [5,7,9,24,41,644] BT.lf)))) [5,7,9,24,56,370] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,24,64,272] BT.lf) [5,7,9,24,64,279] (BT.nd BT.lf [5,7,9,24,64,281] BT.lf)) [5,7,9,24,64,336] (BT.nd (BT.nd BT.lf [5,7,9,24,64,751] BT.lf) [5,7,9,24,66,272] BT.lf)) [5,7,9,24,71,272] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,24,73,272] BT.lf) [5,7,9,24,88,272] BT.lf) [5,7,9,24,98,196,256] (BT.nd (BT.nd BT.lf [5,7,9,24,98,272,964] BT.lf) [5,7,9,24,98,336] BT.lf))) [5,7,9,24,98,468,768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,24,98,676] BT.lf) [5,7,9,24,128,464] (BT.nd BT.lf [5,7,9,24,132,336] BT.lf)) [5,7,9,24,132,370,960] (BT.nd (BT.nd BT.lf [5,7,9,24,132,464] BT.lf) [5,7,9,24,132,464,866] BT.lf)) [5,7,9,24,132,468] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,24,132,471] BT.lf) [5,7,9,24,132,473] BT.lf) [5,7,9,24,132,553] (BT.nd (BT.nd BT.lf [5,7,9,24,132,559] BT.lf) [5,7,9,24,135,464] BT.lf))))))) [5,7,9,24,141,464] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,24,141,544] BT.lf) [5,7,9,24,156,464] (BT.nd BT.lf [5,7,9,24,164,370] BT.lf)) [5,7,9,24,164,464] (BT.nd (BT.nd BT.lf [5,7,9,24,164,521] BT.lf) [5,7,9,24,173,512] BT.lf)) [5,7,9,24,192,336] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,24,192,370,900] BT.lf) [5,7,9,24,192,404,866] (BT.nd BT.lf [5,7,9,24,196,272,866] BT.lf)) [5,7,9,24,196,370,768] (BT.nd (BT.nd BT.lf [5,7,9,24,272,336] BT.lf) [5,7,9,24,272,676] BT.lf))) [5,7,9,24,272,932] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,24,272,957] BT.lf) [5,7,9,24,272,959] (BT.nd BT.lf [5,7,9,24,336] BT.lf)) [5,7,9,24,336,512] (BT.nd (BT.nd BT.lf [5,7,9,24,336,768] BT.lf) [5,7,9,24,370,464] BT.lf)) [5,7,9,24,370,544] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,24,370,960] BT.lf) [5,7,9,24,370,991] BT.lf) [5,7,9,24,464,644] (BT.nd (BT.nd BT.lf [5,7,9,24,464,866] BT.lf) [5,7,9,24,464,891] BT.lf)))) [5,7,9,24,676] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,31,64,272] BT.lf) [5,7,9,31,132,464] (BT.nd BT.lf [5,7,9,32,56,370] BT.lf)) [5,7,9,32,98,668] (BT.nd (BT.nd BT.lf [5,7,9,32,141,536] BT.lf) [5,7,9,32,156,370] BT.lf)) [5,7,9,32,156,464] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,32,156,521] BT.lf) [5,7,9,32,354] BT.lf) [5,7,9,32,370,999] (BT.nd (BT.nd BT.lf [5,7,9,32,668] BT.lf) [5,7,9,41,132,536] BT.lf))) [5,7,9,41,156,512] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,56,98,272] BT.lf) [5,7,9,56,98,279] (BT.nd BT.lf [5,7,9,56,98,281] BT.lf)) [5,7,9,56,98,304] (BT.nd (BT.nd BT.lf [5,7,9,56,98,370] BT.lf) [5,7,9,56,98,644] BT.lf)) [5,7,9,56,98,751] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,56,103,272] BT.lf) [5,7,9,56,132,370] BT.lf) [5,7,9,56,132,521] (BT.nd (BT.nd BT.lf [5,7,9,56,141,512] BT.lf) [5,7,9,56,192,370] BT.lf))))) [5,7,9,56,272,370] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,56,272,925] BT.lf) [5,7,9,56,370] (BT.nd BT.lf [5,7,9,56,370,512] BT.lf)) [5,7,9,56,370,768] (BT.nd (BT.nd BT.lf [5,7,9,56,644] BT.lf) [5,7,9,64,88,272] BT.lf)) [5,7,9,64,256] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,64,272,999] BT.lf) [5,7,9,88,272] BT.lf) [5,7,9,98,132,216,256] (BT.nd (BT.nd BT.lf [5,7,9,98,132,280,960] BT.lf) [5,7,9,98,132,472,768] BT.lf))) [5,7,9,98,132,568] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,98,156,192,256] BT.lf) [5,7,9,98,156,272,960] (BT.nd BT.lf [5,7,9,98,156,464] BT.lf)) [5,7,9,98,156,464,768] (BT.nd (BT.nd BT.lf [5,7,9,98,156,544] BT.lf) [5,7,9,98,164,536] BT.lf)) [5,7,9,98,188,272] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,98,188,512] BT.lf) [5,7,9,98,192,280,900] BT.lf) [5,7,9,98,192,412,768] (BT.nd (BT.nd BT.lf [5,7,9,98,192,668] BT.lf) [5,7,9,98,196,280,768] BT.lf)))) [5,7,9,98,216,272,900] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,98,216,404,768] BT.lf) [5,7,9,98,216,464] (BT.nd BT.lf [5,7,9,98,220,272,768] BT.lf)) [5,7,9,98,272,967] (BT.nd (BT.nd BT.lf [5,7,9,98,279,960] BT.lf) [5,7,9,98,288] BT.lf)) [5,7,9,98,304,960] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,98,464,775] BT.lf) [5,7,9,98,464,800] BT.lf) [5,7,9,98,471,768] (BT.nd (BT.nd BT.lf [5,7,9,98,728] BT.lf) [5,7,9,103,272,960] BT.lf))) [5,7,9,103,464,768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,122,132,192,256] BT.lf) [5,7,9,122,132,272,960] (BT.nd BT.lf [5,7,9,122,192,272,900] BT.lf)) [5,7,9,122,192,370] (BT.nd (BT.nd BT.lf [5,7,9,122,192,404,768] BT.lf) [5,7,9,122,192,644] BT.lf)) [5,7,9,122,196,272,768] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,122,304] BT.lf) [5,7,9,122,704] BT.lf) [5,7,9,132,156,464] (BT.nd (BT.nd BT.lf [5,7,9,132,192,280,866] BT.lf) [5,7,9,132,192,378,768] BT.lf)))))) [5,7,9,132,192,634] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,132,216,272,866] BT.lf) [5,7,9,132,448] (BT.nd BT.lf [5,7,9,132,464,999] BT.lf)) [5,7,9,132,568] (BT.nd (BT.nd BT.lf [5,7,9,152,192,272] BT.lf) [5,7,9,156,192,272] BT.lf)) [5,7,9,156,192,272,866] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,156,192,279] BT.lf) [5,7,9,156,192,281] (BT.nd BT.lf [5,7,9,156,192,370,768] BT.lf)) [5,7,9,156,192,404] (BT.nd (BT.nd BT.lf [5,7,9,156,192,464] BT.lf) [5,7,9,156,192,610] BT.lf))) [5,7,9,156,192,751] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,156,196,272] BT.lf) [5,7,9,156,199,272] (BT.nd BT.lf [5,7,9,156,201,272] BT.lf)) [5,7,9,156,272,464] (BT.nd (BT.nd BT.lf [5,7,9,156,272,831] BT.lf) [5,7,9,156,464] BT.lf)) [5,7,9,156,464,512] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,156,464,768] BT.lf) [5,7,9,156,544] BT.lf) [5,7,9,159,192,272] (BT.nd (BT.nd BT.lf [5,7,9,164,536] BT.lf) [5,7,9,188,512] BT.lf)))) [5,7,9,192,272,867] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,192,272,871] BT.lf) [5,7,9,192,279,866] (BT.nd BT.lf [5,7,9,192,370,775] BT.lf)) [5,7,9,192,375,768] (BT.nd (BT.nd BT.lf [5,7,9,192,388] BT.lf) [5,7,9,192,634] BT.lf)) [5,7,9,199,272,866] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,199,370,768] BT.lf) [5,7,9,216,404] BT.lf) [5,7,9,216,610] (BT.nd (BT.nd BT.lf [5,7,9,272,932] BT.lf) [5,7,9,304,900] BT.lf))) [5,7,9,370,960] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,404,800] BT.lf) [5,7,9,436,768] (BT.nd BT.lf [5,7,9,464,866] BT.lf)) [5,7,9,512,832] (BT.nd (BT.nd BT.lf [5,7,9,544,866] BT.lf) [5,7,9,576,768] BT.lf)) [5,7,9,610,800] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,644,960] BT.lf) [5,7,9,704,900] BT.lf) [5,7,24,32,41,370] (BT.nd (BT.nd BT.lf [5,7,24,32,107,370] BT.lf) [5,7,24,32,141,521] BT.lf))))) [5,7,24,32,370,1014] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,41,98,272] BT.lf) [5,7,24,41,98,279] (BT.nd BT.lf [5,7,24,41,98,304] BT.lf)) [5,7,24,41,98,313] (BT.nd (BT.nd BT.lf [5,7,24,41,98,370] BT.lf) [5,7,24,41,98,751] BT.lf)) [5,7,24,41,103,272] (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,41,122,272] BT.lf) [5,7,24,41,132,370] BT.lf) [5,7,24,41,132,521] (BT.nd (BT.nd BT.lf [5,7,24,41,141,512] BT.lf) [5,7,24,41,192,370] BT.lf))) [5,7,24,41,272,370] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,41,272,900] BT.lf) [5,7,24,41,272,925] (BT.nd BT.lf [5,7,24,41,370] BT.lf)) [5,7,24,41,370,512] (BT.nd (BT.nd BT.lf [5,7,24,41,370,768] BT.lf) [5,7,24,41,644] BT.lf)) [5,7,24,64,73,272] (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,64,272,281] BT.lf) [5,7,24,64,272,777] BT.lf) [5,7,24,64,272,1014] (BT.nd (BT.nd BT.lf [5,7,24,73,272] BT.lf) [5,7,24,98,132,201,256] BT.lf)))) [5,7,24,98,132,272,969] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,98,132,464,777] BT.lf) [5,7,24,98,192,404,777] (BT.nd BT.lf [5,7,24,98,196,272,777] BT.lf)) [5,7,24,98,201,272,900] (BT.nd (BT.nd BT.lf [5,7,24,98,201,281] BT.lf) [5,7,24,98,201,404,768] BT.lf)) [5,7,24,98,201,464] (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,98,201,644] BT.lf) [5,7,24,98,272,313] BT.lf) [5,7,24,98,272,708] (BT.nd (BT.nd BT.lf [5,7,24,98,272,809] BT.lf) [5,7,24,98,272,982] BT.lf))) [5,7,24,98,281,304] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,98,713] BT.lf) [5,7,24,107,192,370] (BT.nd BT.lf [5,7,24,132,141,464] BT.lf)) [5,7,24,132,192,370,777] (BT.nd (BT.nd BT.lf [5,7,24,132,201,272,866] BT.lf) [5,7,24,132,201,281] BT.lf)) [5,7,24,132,201,370,768] (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,132,201,464] BT.lf) [5,7,24,132,201,610] BT.lf) [5,7,24,132,272,809] (BT.nd (BT.nd BT.lf [5,7,24,132,464,473] BT.lf) [5,7,24,132,464,1014] BT.lf))))))))) [5,7,24,132,553] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,137,192,272] BT.lf) [5,7,24,141,192,404] (BT.nd BT.lf [5,7,24,141,196,272] BT.lf)) [5,7,24,164,272,777] (BT.nd (BT.nd BT.lf [5,7,24,164,370] BT.lf) [5,7,24,164,521] BT.lf)) [5,7,24,192,281,404] (BT.nd (BT.nd (BT.nd BT.lf [5,7,24,196,272,610] BT.lf) [5,7,24,201,404] (BT.nd BT.lf [5,7,24,201,610] BT.lf)) [5,7,25,32,370] (BT.nd (BT.nd BT.lf [5,7,25,64,272] BT.lf) [5,7,25,98,304] BT.lf))) [5,7,25,132,464] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,25,192,404] BT.lf) [5,7,31,41,98,272] (BT.nd BT.lf [5,7,32,98,265] BT.lf)) [5,7,32,156,521] (BT.nd (BT.nd BT.lf [5,7,32,521,866] BT.lf) [5,7,32,610,777] BT.lf)) [5,7,41,98,122,272] (BT.nd (BT.nd (BT.nd BT.lf [5,7,41,98,256] BT.lf) [5,7,41,98,272,999] BT.lf) [5,7,41,132,536] (BT.nd (BT.nd BT.lf [5,7,41,156,512] BT.lf) [5,7,41,512,866] BT.lf)))) [5,7,41,610,768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,56,98,272,281] BT.lf) [5,7,56,98,272,1014] (BT.nd BT.lf [5,7,56,132,370] BT.lf)) [5,7,56,132,521] (BT.nd (BT.nd BT.lf [5,7,57,98,272] BT.lf) [5,7,64,512,777] BT.lf)) [5,7,64,521,768] (BT.nd (BT.nd (BT.nd BT.lf [5,7,73,272,768] BT.lf) [5,7,73,512,768] BT.lf) [5,7,98,132,192,280,777] (BT.nd (BT.nd BT.lf [5,7,98,132,201,280,768] BT.lf) [5,7,98,132,201,536] BT.lf))) [5,7,98,132,216,272,777] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,98,156,192,272,777] BT.lf) [5,7,98,156,464] (BT.nd BT.lf [5,7,98,192,265] BT.lf)) [5,7,98,201,536] (BT.nd (BT.nd BT.lf [5,7,98,216,404] BT.lf) [5,7,98,216,521] BT.lf)) [5,7,98,272,932] (BT.nd (BT.nd (BT.nd BT.lf [5,7,98,272,964] BT.lf) [5,7,98,304,900] BT.lf) [5,7,98,404,800] (BT.nd (BT.nd BT.lf [5,7,98,436,768] BT.lf) [5,7,98,468,768] BT.lf))))) [5,7,98,512,809] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,98,521,800] BT.lf) [5,7,98,544,777] (BT.nd BT.lf [5,7,98,553,768] BT.lf)) [5,7,98,704,777] (BT.nd (BT.nd BT.lf [5,7,122,132,192,272,777] BT.lf) [5,7,122,132,201,272] BT.lf)) [5,7,122,132,201,272,768] (BT.nd (BT.nd (BT.nd BT.lf [5,7,122,132,201,512] BT.lf) [5,7,122,132,304] (BT.nd BT.lf [5,7,122,164,272] BT.lf)) [5,7,122,192,521] (BT.nd (BT.nd BT.lf [5,7,122,201,272] BT.lf) [5,7,122,201,512] BT.lf))) [5,7,132,192,265] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,132,201,216,272] BT.lf) [5,7,132,201,256] (BT.nd BT.lf [5,7,132,201,272,800] BT.lf)) [5,7,132,201,304,768] (BT.nd (BT.nd BT.lf [5,7,132,217,272] BT.lf) [5,7,132,370,960] BT.lf)) [5,7,132,464,866] (BT.nd (BT.nd (BT.nd BT.lf [5,7,132,512,969] BT.lf) [5,7,132,521,960] BT.lf) [5,7,132,704,777] (BT.nd (BT.nd BT.lf [5,7,132,713,768] BT.lf) [5,7,156,192,201,272] BT.lf)))) [5,7,156,192,272,281] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,156,192,272,1014] BT.lf) [5,7,192,370,900] (BT.nd BT.lf [5,7,192,404,866] BT.lf)) [5,7,192,521,900] (BT.nd (BT.nd BT.lf [5,7,192,610,777] BT.lf) [5,7,192,644,777] BT.lf)) [5,7,196,272,866] (BT.nd (BT.nd (BT.nd BT.lf [5,7,196,370,768] BT.lf) [5,7,201,272,900] BT.lf) [5,7,201,404,768] (BT.nd (BT.nd BT.lf [5,7,201,512,900] BT.lf) [5,7,201,644,768] BT.lf))) [5,8,98,132,192,272,775] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,8,98,132,192,279,768] BT.lf) [5,9,24,31,64,272] (BT.nd BT.lf [5,9,24,31,132,464] BT.lf)) [5,9,24,32,39,370] (BT.nd (BT.nd BT.lf [5,9,24,32,64,279] BT.lf) [5,9,24,32,71,272] BT.lf)) [5,9,24,32,98,279] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,32,98,311] BT.lf) [5,9,24,32,98,375] BT.lf) [5,9,24,32,98,744] (BT.nd (BT.nd BT.lf [5,9,24,32,103,272] BT.lf) [5,9,24,32,103,279] BT.lf)))))) [5,9,24,32,103,281] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,32,103,304] BT.lf) [5,9,24,32,103,370] (BT.nd BT.lf [5,9,24,32,103,375] BT.lf)) [5,9,24,32,103,751] (BT.nd (BT.nd BT.lf [5,9,24,32,107,279] BT.lf) [5,9,24,32,122,279] BT.lf)) [5,9,24,32,127,272] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,32,132,375] BT.lf) [5,9,24,32,192,375] (BT.nd BT.lf [5,9,24,32,272,375] BT.lf)) [5,9,24,32,272,896] (BT.nd (BT.nd BT.lf [5,9,24,32,272,920] BT.lf) [5,9,24,32,279,370] BT.lf))) [5,9,24,32,279,375] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,32,279,644] BT.lf) [5,9,24,32,279,900] (BT.nd BT.lf [5,9,24,32,279,925] BT.lf)) [5,9,24,32,370,375] (BT.nd (BT.nd BT.lf [5,9,24,32,370,1016] BT.lf) [5,9,24,32,375] BT.lf)) [5,9,24,32,375,512] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,32,375,768] BT.lf) [5,9,24,32,640] BT.lf) [5,9,24,39,98,279] (BT.nd (BT.nd BT.lf [5,9,24,41,98,279] BT.lf) [5,9,24,41,103,272] BT.lf)))) [5,9,24,56,98,279] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,56,103,272] BT.lf) [5,9,24,64,71,272] (BT.nd BT.lf [5,9,24,64,98,279] BT.lf)) [5,9,24,64,132,279] (BT.nd (BT.nd BT.lf [5,9,24,64,192,279] BT.lf) [5,9,24,64,272,279] BT.lf)) [5,9,24,64,272,1016] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,64,279] BT.lf) [5,9,24,64,279,512] BT.lf) [5,9,24,64,279,768] (BT.nd (BT.nd BT.lf [5,9,24,71,98,272] BT.lf) [5,9,24,71,132,272] BT.lf))) [5,9,24,71,192,272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,71,272] BT.lf) [5,9,24,71,272,512] (BT.nd BT.lf [5,9,24,71,272,768] BT.lf)) [5,9,24,98,132,279,960] (BT.nd (BT.nd BT.lf [5,9,24,98,132,464,775] BT.lf) [5,9,24,98,164,279] BT.lf)) [5,9,24,98,192,279] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,98,192,279,900] BT.lf) [5,9,24,98,192,404,775] BT.lf) [5,9,24,98,192,471] (BT.nd (BT.nd BT.lf [5,9,24,98,192,744] BT.lf) [5,9,24,98,196,272,775] BT.lf))))) [5,9,24,98,196,279] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,98,196,279,768] BT.lf) [5,9,24,98,199,279] (BT.nd BT.lf [5,9,24,98,201,279] BT.lf)) [5,9,24,98,216,279] (BT.nd (BT.nd BT.lf [5,9,24,98,279,304] BT.lf) [5,9,24,98,279,311] BT.lf)) [5,9,24,98,279,464] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,98,279,471] BT.lf) [5,9,24,98,279,544] BT.lf) [5,9,24,98,279,704] (BT.nd (BT.nd BT.lf [5,9,24,98,279,800] BT.lf) [5,9,24,98,279,831] BT.lf))) [5,9,24,98,279,960] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,98,279,991] BT.lf) [5,9,24,103,192,279] (BT.nd BT.lf [5,9,24,103,199,272] BT.lf)) [5,9,24,103,272,304] (BT.nd (BT.nd BT.lf [5,9,24,103,272,544] BT.lf) [5,9,24,103,272,800] BT.lf)) [5,9,24,103,272,991] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,103,304] BT.lf) [5,9,24,107,192,279] BT.lf) [5,9,24,122,192,279] (BT.nd (BT.nd BT.lf [5,9,24,128,192,279] BT.lf) [5,9,24,128,199,272] BT.lf)))) [5,9,24,128,272,800] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,128,544] BT.lf) [5,9,24,132,192,279] (BT.nd BT.lf [5,9,24,132,192,279,866] BT.lf)) [5,9,24,132,192,370,775] (BT.nd (BT.nd BT.lf [5,9,24,132,192,471] BT.lf) [5,9,24,132,192,744] BT.lf)) [5,9,24,132,196,279] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,132,199,279] BT.lf) [5,9,24,132,201,279] BT.lf) [5,9,24,132,216,279] (BT.nd (BT.nd BT.lf [5,9,24,132,279,464] BT.lf) [5,9,24,132,279,471] BT.lf))) [5,9,24,132,279,544] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,132,279,800] BT.lf) [5,9,24,132,279,831] (BT.nd BT.lf [5,9,24,132,464,471] BT.lf)) [5,9,24,132,464,1016] (BT.nd (BT.nd BT.lf [5,9,24,135,192,279] BT.lf) [5,9,24,135,464] BT.lf)) [5,9,24,141,192,279] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,156,192,279] BT.lf) [5,9,24,160,272,768] BT.lf) [5,9,24,160,512] (BT.nd (BT.nd BT.lf [5,9,24,164,192,279] BT.lf) [5,9,24,164,279,512] BT.lf))))))) [5,9,24,164,279,768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,192,279,370] BT.lf) [5,9,24,192,279,375] (BT.nd BT.lf [5,9,24,192,279,404] BT.lf)) [5,9,24,192,279,407] (BT.nd (BT.nd BT.lf [5,9,24,192,279,610] BT.lf) [5,9,24,192,279,644] BT.lf)) [5,9,24,192,279,866] (BT.nd (BT.nd (BT.nd BT.lf [5,9,24,192,279,891] BT.lf) [5,9,24,192,279,900] (BT.nd BT.lf [5,9,24,192,279,925] BT.lf)) [5,9,24,192,407] (BT.nd (BT.nd BT.lf [5,9,31,98,216,272] BT.lf) [5,9,31,132,216,272] BT.lf))) [5,9,31,135,192,272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,32,56,98,279] BT.lf) [5,9,32,56,103,272] (BT.nd BT.lf [5,9,32,98,122,279] BT.lf)) [5,9,32,98,263] (BT.nd (BT.nd BT.lf [5,9,32,98,279,999] BT.lf) [5,9,32,98,728] BT.lf)) [5,9,32,103,122,272] (BT.nd (BT.nd (BT.nd BT.lf [5,9,32,103,127,272] BT.lf) [5,9,32,103,256] BT.lf) [5,9,32,103,272,999] (BT.nd (BT.nd BT.lf [5,9,32,128,536] BT.lf) [5,9,32,152,512] BT.lf)))) [5,9,32,512,871] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,32,615,768] BT.lf) [5,9,39,56,98,272] (BT.nd BT.lf [5,9,56,98,103,272] BT.lf)) [5,9,56,98,132,279] (BT.nd (BT.nd BT.lf [5,9,56,98,192,279] BT.lf) [5,9,56,98,272,279] BT.lf)) [5,9,56,98,272,1016] (BT.nd (BT.nd (BT.nd BT.lf [5,9,56,98,279] BT.lf) [5,9,56,98,279,512] BT.lf) [5,9,56,98,279,768] (BT.nd (BT.nd BT.lf [5,9,56,98,704] BT.lf) [5,9,56,103,132,272] BT.lf))) [5,9,56,103,192,272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,56,103,272] BT.lf) [5,9,56,103,272,512] (BT.nd BT.lf [5,9,56,103,272,768] BT.lf)) [5,9,56,128,512] (BT.nd (BT.nd BT.lf [5,9,64,512,775] BT.lf) [5,9,64,519,768] BT.lf)) [5,9,71,272,768] (BT.nd (BT.nd (BT.nd BT.lf [5,9,71,512,768] BT.lf) [5,9,98,122,192,279] BT.lf) [5,9,98,132,192,280,775] (BT.nd (BT.nd BT.lf [5,9,98,132,216,272,775] BT.lf) [5,9,98,132,216,279,768] BT.lf))))) [5,9,98,156,192,272,775] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,98,192,216,279] BT.lf) [5,9,98,192,263] (BT.nd BT.lf [5,9,98,192,279,775] BT.lf)) [5,9,98,192,279,999] (BT.nd (BT.nd BT.lf [5,9,98,192,568] BT.lf) [5,9,98,199,216,272] BT.lf)) [5,9,98,199,272,775] (BT.nd (BT.nd (BT.nd BT.lf [5,9,98,199,279,768] BT.lf) [5,9,98,216,279] BT.lf) [5,9,98,216,544] (BT.nd (BT.nd BT.lf [5,9,98,519,800] BT.lf) [5,9,98,544,775] BT.lf))) [5,9,98,704,775] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,103,192,272,775] BT.lf) [5,9,103,192,279,768] (BT.nd BT.lf [5,9,103,199,272,768] BT.lf)) [5,9,103,272,800] (BT.nd (BT.nd BT.lf [5,9,103,304,768] BT.lf) [5,9,103,512,800] BT.lf)) [5,9,103,544,768] (BT.nd (BT.nd (BT.nd BT.lf [5,9,122,132,192,272,775] BT.lf) [5,9,132,156,192,279] BT.lf) [5,9,132,192,216,279] (BT.nd (BT.nd BT.lf [5,9,132,192,263] BT.lf) [5,9,132,192,279,999] BT.lf)))) [5,9,132,192,568] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,132,199,216,272] BT.lf) [5,9,132,216,279] (BT.nd BT.lf [5,9,132,519,960] BT.lf)) [5,9,132,704,775] (BT.nd (BT.nd BT.lf [5,9,135,192,256] BT.lf) [5,9,135,192,272,800] BT.lf)) [5,9,135,192,304,768] (BT.nd (BT.nd (BT.nd BT.lf [5,9,135,216,272] BT.lf) [5,9,135,512,960] BT.lf) [5,9,135,704,768] (BT.nd (BT.nd BT.lf [5,9,156,192,199,272] BT.lf) [5,9,156,192,272,279] BT.lf))) [5,9,156,192,272,1016] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,192,512,903] BT.lf) [5,9,192,647,768] (BT.nd BT.lf [5,15,24,98,132,192,256] BT.lf)) [5,15,24,98,132,272,960] (BT.nd (BT.nd BT.lf [5,15,24,98,132,464,768] BT.lf) [5,15,24,98,192,272,900] BT.lf)) [5,15,24,98,192,404,768] (BT.nd (BT.nd (BT.nd BT.lf [5,15,24,98,196,272,768] BT.lf) [5,15,24,132,192,272,866] BT.lf) [5,15,24,132,192,370,768] (BT.nd (BT.nd BT.lf [5,15,98,132,192,280,768] BT.lf) [5,15,98,132,216,272,768] BT.lf)))))) [5,15,98,156,192,272,768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,122,132,192,272,768] BT.lf) [5,24,31,41,98,272] (BT.nd BT.lf [5,24,32,41,98,279] BT.lf)) [5,24,32,41,103,272] (BT.nd (BT.nd BT.lf [5,24,32,98,107,279] BT.lf) [5,24,32,98,272,969] BT.lf)) [5,24,32,98,276] (BT.nd (BT.nd (BT.nd BT.lf [5,24,32,98,279,1014] BT.lf) [5,24,32,98,713] (BT.nd BT.lf [5,24,32,102,272] BT.lf)) [5,24,32,103,272,281] (BT.nd (BT.nd BT.lf [5,24,32,103,272,777] BT.lf) [5,24,32,103,272,1014] BT.lf))) [5,24,32,128,272,777] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,24,32,128,521] BT.lf) [5,24,32,132,498] (BT.nd BT.lf [5,24,32,137,272,768] BT.lf)) [5,24,32,137,512] (BT.nd (BT.nd BT.lf [5,24,32,226,404] BT.lf) [5,24,36,98,272] BT.lf)) [5,24,39,41,98,272] (BT.nd (BT.nd (BT.nd BT.lf [5,24,41,98,103,272] BT.lf) [5,24,41,98,132,279] BT.lf) [5,24,41,98,192,279] (BT.nd (BT.nd BT.lf [5,24,41,98,272,279] BT.lf) [5,24,41,98,272,960] BT.lf)))) [5,24,41,98,272,1016] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,24,41,98,279] BT.lf) [5,24,41,98,279,512] (BT.nd BT.lf [5,24,41,98,279,768] BT.lf)) [5,24,41,98,704] (BT.nd (BT.nd BT.lf [5,24,41,103,132,272] BT.lf) [5,24,41,103,192,272] BT.lf)) [5,24,41,103,272] (BT.nd (BT.nd (BT.nd BT.lf [5,24,41,103,272,512] BT.lf) [5,24,41,103,272,768] BT.lf) [5,24,41,128,272,768] (BT.nd (BT.nd BT.lf [5,24,41,128,512] BT.lf) [5,24,98,107,192,279] BT.lf))) [5,24,98,132,192,272,783] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,24,98,132,201,272,775] BT.lf) [5,24,98,132,201,279,768] (BT.nd BT.lf [5,24,98,164,464] BT.lf)) [5,24,98,192,201,279] (BT.nd (BT.nd BT.lf [5,24,98,192,272,809] BT.lf) [5,24,98,192,279,1014] BT.lf)) [5,24,98,192,436] (BT.nd (BT.nd (BT.nd BT.lf [5,24,98,192,553] BT.lf) [5,24,98,196,272,519] BT.lf) [5,24,98,199,201,272] (BT.nd (BT.nd BT.lf [5,24,98,201,272,800] BT.lf) [5,24,98,201,279] BT.lf))))) [5,24,98,201,544] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,24,132,141,192,279] BT.lf) [5,24,132,192,201,279] (BT.nd BT.lf [5,24,132,192,272,809] BT.lf)) [5,24,132,192,274] (BT.nd (BT.nd BT.lf [5,24,132,192,279,1014] BT.lf) [5,24,132,192,553] BT.lf)) [5,24,132,194,272] (BT.nd (BT.nd (BT.nd BT.lf [5,24,132,201,279] BT.lf) [5,24,132,226,304] BT.lf) [5,24,134,192,272] (BT.nd (BT.nd BT.lf [5,24,135,201,272] BT.lf) [5,24,164,192,370] BT.lf))) [5,24,164,226,272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,25,32,98,279] BT.lf) [5,25,32,103,272] (BT.nd BT.lf [5,25,98,192,279] BT.lf)) [5,25,132,192,279] (BT.nd (BT.nd BT.lf [5,25,135,192,272] BT.lf) [5,26,132,192,272] BT.lf)) [5,28,32,98,272] (BT.nd (BT.nd (BT.nd BT.lf [5,32,98,156,464] BT.lf) [5,32,98,201,536] BT.lf) [5,32,98,216,404] (BT.nd (BT.nd BT.lf [5,32,98,216,521] BT.lf) [5,32,98,279,900] BT.lf)))) [5,32,98,404,775] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,32,98,519,777] BT.lf) [5,32,98,521,775] (BT.nd BT.lf [5,32,103,512,777] BT.lf)) [5,32,103,521,768] (BT.nd (BT.nd BT.lf [5,32,122,192,404] BT.lf) [5,32,132,250,272] BT.lf)) [5,32,135,201,272,768] (BT.nd (BT.nd (BT.nd BT.lf [5,32,156,192,370] BT.lf) [5,32,156,226,272] BT.lf) [5,41,98,192,536] (BT.nd (BT.nd BT.lf [5,41,98,216,512] BT.lf) [5,41,98,512,775] BT.lf))) [5,41,98,519,768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,41,103,272,768] BT.lf) [5,41,103,512,768] (BT.nd BT.lf [5,41,132,192,536] BT.lf)) [5,56,98,132,464] (BT.nd (BT.nd BT.lf [5,56,98,192,404] BT.lf) [5,56,98,192,521] BT.lf)) [5,56,98,201,512] (BT.nd (BT.nd (BT.nd BT.lf [5,56,132,192,370] BT.lf) [5,56,132,192,521] BT.lf) [5,56,132,226,272] (BT.nd (BT.nd BT.lf [5,98,132,216,304] BT.lf) [5,98,132,279,800] BT.lf)))))))) [5,98,132,279,960] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,98,132,304,775] BT.lf) [5,98,132,464,775] (BT.nd BT.lf [5,98,156,192,304] BT.lf)) [5,98,164,216,272] (BT.nd (BT.nd BT.lf [5,98,164,272,775] BT.lf) [5,98,164,279,768] BT.lf)) [5,98,188,192,272] (BT.nd (BT.nd (BT.nd BT.lf [5,98,192,279,900] BT.lf) [5,98,192,404,775] (BT.nd BT.lf [5,98,192,519,777] BT.lf)) [5,98,192,521,775] (BT.nd (BT.nd BT.lf [5,98,196,272,775] BT.lf) [5,98,196,279,768] BT.lf))) [5,122,132,192,304] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,122,164,192,272] BT.lf) [5,132,192,279,866] (BT.nd BT.lf [5,132,192,370,775] BT.lf)) [5,132,192,519,777] (BT.nd (BT.nd BT.lf [5,132,192,521,775] BT.lf) [5,132,201,512,775] BT.lf)) [5,132,201,519,768] (BT.nd (BT.nd (BT.nd BT.lf [5,135,192,512,777] BT.lf) [5,135,192,521,768] BT.lf) [5,135,201,272,768] (BT.nd (BT.nd BT.lf [5,135,201,512,768] BT.lf) [6,2,24,132,192,272] BT.lf)))) [6,4,24,32,98,272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,8,98,132,192,272,768] BT.lf) [6,7,9,24,32,64,272] (BT.nd BT.lf [6,7,9,24,32,98,272] BT.lf)) [6,7,9,24,32,98,279] (BT.nd (BT.nd BT.lf [6,7,9,24,32,98,281] BT.lf) [6,7,9,24,32,98,304] BT.lf)) [6,7,9,24,32,98,370] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,32,98,644] BT.lf) [6,7,9,24,32,98,751] BT.lf) [6,7,9,24,32,103,272] (BT.nd (BT.nd BT.lf [6,7,9,24,32,107,272] BT.lf) [6,7,9,24,32,122,272] BT.lf))) [6,7,9,24,32,132,370] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,32,132,464] BT.lf) [6,7,9,24,32,132,521] (BT.nd BT.lf [6,7,9,24,32,141,512] BT.lf)) [6,7,9,24,32,192,370] (BT.nd (BT.nd BT.lf [6,7,9,24,32,272,370] BT.lf) [6,7,9,24,32,272,644] BT.lf)) [6,7,9,24,32,272,900] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,32,272,925] BT.lf) [6,7,9,24,32,370] BT.lf) [6,7,9,24,32,370,512] (BT.nd (BT.nd BT.lf [6,7,9,24,32,370,768] BT.lf) [6,7,9,24,32,644] BT.lf))))) [6,7,9,24,39,98,272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,41,98,272] BT.lf) [6,7,9,24,41,132,512] (BT.nd BT.lf [6,7,9,24,56,98,272] BT.lf)) [6,7,9,24,64,98,272] (BT.nd (BT.nd BT.lf [6,7,9,24,64,132,272] BT.lf) [6,7,9,24,64,192,272] BT.lf)) [6,7,9,24,64,272] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,64,272,512] BT.lf) [6,7,9,24,64,272,768] (BT.nd BT.lf [6,7,9,24,98,132,192,256] BT.lf)) [6,7,9,24,98,132,272,960] (BT.nd (BT.nd BT.lf [6,7,9,24,98,132,464] BT.lf) [6,7,9,24,98,132,464,768] BT.lf))) [6,7,9,24,98,132,544] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,98,164,272] BT.lf) [6,7,9,24,98,164,512] (BT.nd BT.lf [6,7,9,24,98,192,272] BT.lf)) [6,7,9,24,98,192,272,900] (BT.nd (BT.nd BT.lf [6,7,9,24,98,192,279] BT.lf) [6,7,9,24,98,192,281] BT.lf)) [6,7,9,24,98,192,370] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,98,192,404,768] BT.lf) [6,7,9,24,98,192,464] BT.lf) [6,7,9,24,98,192,644] (BT.nd (BT.nd BT.lf [6,7,9,24,98,192,751] BT.lf) [6,7,9,24,98,196,272] BT.lf)))) [6,7,9,24,98,196,272,768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,98,199,272] BT.lf) [6,7,9,24,98,201,272] (BT.nd BT.lf [6,7,9,24,98,216,272] BT.lf)) [6,7,9,24,98,272,304] (BT.nd (BT.nd BT.lf [6,7,9,24,98,272,464] BT.lf) [6,7,9,24,98,272,544] BT.lf)) [6,7,9,24,98,272,704] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,98,272,800] BT.lf) [6,7,9,24,98,272,831] BT.lf) [6,7,9,24,98,272,960] (BT.nd (BT.nd BT.lf [6,7,9,24,98,272,991] BT.lf) [6,7,9,24,98,304] BT.lf))) [6,7,9,24,98,464,768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,98,704] BT.lf) [6,7,9,24,103,192,272] (BT.nd BT.lf [6,7,9,24,107,192,272] BT.lf)) [6,7,9,24,122,192,272] (BT.nd (BT.nd BT.lf [6,7,9,24,128,192,272] BT.lf) [6,7,9,24,132,192,272] BT.lf)) [6,7,9,24,132,192,272,866] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,132,192,279] BT.lf) [6,7,9,24,132,192,281] BT.lf) [6,7,9,24,132,192,370,768] (BT.nd (BT.nd BT.lf [6,7,9,24,132,192,404] BT.lf) [6,7,9,24,132,192,464] BT.lf)))))) [6,7,9,24,132,192,610] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,132,192,751] BT.lf) [6,7,9,24,132,196,272] (BT.nd BT.lf [6,7,9,24,132,199,272] BT.lf)) [6,7,9,24,132,201,272] (BT.nd (BT.nd BT.lf [6,7,9,24,132,216,272] BT.lf) [6,7,9,24,132,272,464] BT.lf)) [6,7,9,24,132,272,544] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,132,272,800] BT.lf) [6,7,9,24,132,272,831] (BT.nd BT.lf [6,7,9,24,132,464] BT.lf)) [6,7,9,24,132,464,512] (BT.nd (BT.nd BT.lf [6,7,9,24,132,464,768] BT.lf) [6,7,9,24,132,544] BT.lf))) [6,7,9,24,135,192,272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,141,192,272] BT.lf) [6,7,9,24,156,192,272] (BT.nd BT.lf [6,7,9,24,164,192,272] BT.lf)) [6,7,9,24,164,272,512] (BT.nd (BT.nd BT.lf [6,7,9,24,164,272,768] BT.lf) [6,7,9,24,164,512] BT.lf)) [6,7,9,24,192,272,370] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,192,272,404] BT.lf) [6,7,9,24,192,272,610] BT.lf) [6,7,9,24,192,272,644] (BT.nd (BT.nd BT.lf [6,7,9,24,192,272,866] BT.lf) [6,7,9,24,192,272,891] BT.lf)))) [6,7,9,24,192,272,900] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,24,192,272,925] BT.lf) [6,7,9,24,192,370,768] (BT.nd BT.lf [6,7,9,24,192,404] BT.lf)) [6,7,9,24,192,610] (BT.nd (BT.nd BT.lf [6,7,9,31,32,98,272] BT.lf) [6,7,9,31,98,192,272] BT.lf)) [6,7,9,31,132,192,272] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,32,56,98,272] BT.lf) [6,7,9,32,98,122,272] BT.lf) [6,7,9,32,98,132,536] (BT.nd (BT.nd BT.lf [6,7,9,32,98,156,272] BT.lf) [6,7,9,32,98,156,512] BT.lf))) [6,7,9,32,98,256] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,32,98,272,960] BT.lf) [6,7,9,32,98,272,999] (BT.nd BT.lf [6,7,9,32,98,464,768] BT.lf)) [6,7,9,32,122,272] (BT.nd (BT.nd BT.lf [6,7,9,32,132,536] BT.lf) [6,7,9,32,156,192,272] BT.lf)) [6,7,9,32,156,512] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,32,272,900] BT.lf) [6,7,9,32,404,768] BT.lf) [6,7,9,32,512,866] (BT.nd (BT.nd BT.lf [6,7,9,32,610,768] BT.lf) [6,7,9,56,98,132,272] BT.lf))))) [6,7,9,56,98,132,512] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,56,98,192,272] BT.lf) [6,7,9,56,98,272] (BT.nd BT.lf [6,7,9,56,98,272,512] BT.lf)) [6,7,9,56,98,272,768] (BT.nd (BT.nd BT.lf [6,7,9,56,132,512] BT.lf) [6,7,9,64,272,768] BT.lf)) [6,7,9,64,512,768] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,98,122,192,272] BT.lf) [6,7,9,98,132,192,280,768] BT.lf) [6,7,9,98,132,192,536] (BT.nd (BT.nd BT.lf [6,7,9,98,132,216,272,768] BT.lf) [6,7,9,98,156,192,272] BT.lf))) [6,7,9,98,156,192,272,768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,98,156,192,512] BT.lf) [6,7,9,98,192,216,272] (BT.nd BT.lf [6,7,9,98,192,256] BT.lf)) [6,7,9,98,192,272,775] (BT.nd (BT.nd BT.lf [6,7,9,98,192,272,800] BT.lf) [6,7,9,98,192,272,999] BT.lf)) [6,7,9,98,192,279,768] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,98,192,304,768] BT.lf) [6,7,9,98,192,536] BT.lf) [6,7,9,98,199,272,768] (BT.nd (BT.nd BT.lf [6,7,9,98,216,272] BT.lf) [6,7,9,98,216,512] BT.lf)))) [6,7,9,98,272,800] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,98,272,960] BT.lf) [6,7,9,98,304,768] (BT.nd BT.lf [6,7,9,98,464,768] BT.lf)) [6,7,9,98,512,800] (BT.nd (BT.nd BT.lf [6,7,9,98,544,768] BT.lf) [6,7,9,98,704,768] BT.lf)) [6,7,9,103,192,272,768] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,122,132,192,272] BT.lf) [6,7,9,122,132,192,272,768] BT.lf) [6,7,9,122,132,192,512] (BT.nd (BT.nd BT.lf [6,7,9,122,192,272] BT.lf) [6,7,9,122,192,512] BT.lf))) [6,7,9,132,156,192,272] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,132,192,216,272] BT.lf) [6,7,9,132,192,256] (BT.nd BT.lf [6,7,9,132,192,272,800] BT.lf)) [6,7,9,132,192,272,999] (BT.nd (BT.nd BT.lf [6,7,9,132,192,304,768] BT.lf) [6,7,9,132,216,272] BT.lf)) [6,7,9,132,272,800] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,132,304,768] BT.lf) [6,7,9,132,512,960] BT.lf) [6,7,9,132,704,768] (BT.nd (BT.nd BT.lf [6,7,9,156,192,272] BT.lf) [6,7,9,156,192,272,512] BT.lf))))))) [6,7,9,156,192,272,768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,164,272,768] BT.lf) [6,7,9,192,272,866] (BT.nd BT.lf [6,7,9,192,272,900] BT.lf)) [6,7,9,192,370,768] (BT.nd (BT.nd BT.lf [6,7,9,192,404,768] BT.lf) [6,7,9,192,512,900] BT.lf)) [6,7,9,192,610,768] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,192,644,768] BT.lf) [6,7,24,32,41,98,272] (BT.nd BT.lf [6,7,24,32,98,107,272] BT.lf)) [6,7,24,32,98,272,281] (BT.nd (BT.nd BT.lf [6,7,24,32,98,272,644] BT.lf) [6,7,24,32,98,272,777] BT.lf))) [6,7,24,32,98,272,1014] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,24,32,132,272,777] BT.lf) [6,7,24,32,132,370] (BT.nd BT.lf [6,7,24,32,132,521] BT.lf)) [6,7,24,41,98,132,272] (BT.nd (BT.nd BT.lf [6,7,24,41,98,192,272] BT.lf) [6,7,24,41,98,272] BT.lf)) [6,7,24,41,98,272,512] (BT.nd (BT.nd (BT.nd BT.lf [6,7,24,41,98,272,768] BT.lf) [6,7,24,41,132,272,768] BT.lf) [6,7,24,41,132,512] (BT.nd (BT.nd BT.lf [6,7,24,98,107,192,272] BT.lf) [6,7,24,98,132,192,272,777] BT.lf)))) [6,7,24,98,132,201,272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,24,98,132,201,272,768] BT.lf) [6,7,24,98,132,201,512] (BT.nd BT.lf [6,7,24,98,132,272,544] BT.lf)) [6,7,24,98,132,272,704] (BT.nd (BT.nd BT.lf [6,7,24,98,132,304] BT.lf) [6,7,24,98,132,464] BT.lf)) [6,7,24,98,164,272] (BT.nd (BT.nd (BT.nd BT.lf [6,7,24,98,192,201,272] BT.lf) [6,7,24,98,192,272,281] BT.lf) [6,7,24,98,192,272,644] (BT.nd (BT.nd BT.lf [6,7,24,98,192,272,777] BT.lf) [6,7,24,98,192,272,1014] BT.lf))) [6,7,24,98,192,404] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,24,98,192,521] BT.lf) [6,7,24,98,196,272] (BT.nd BT.lf [6,7,24,98,196,272,512] BT.lf)) [6,7,24,98,201,272] (BT.nd (BT.nd BT.lf [6,7,24,98,201,512] BT.lf) [6,7,24,132,141,192,272] BT.lf)) [6,7,24,132,192,201,272] (BT.nd (BT.nd (BT.nd BT.lf [6,7,24,132,192,272,281] BT.lf) [6,7,24,132,192,272,610] BT.lf) [6,7,24,132,192,272,777] (BT.nd (BT.nd BT.lf [6,7,24,132,192,272,1014] BT.lf) [6,7,24,132,201,272] BT.lf))))) [6,7,25,32,98,272] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,25,98,192,272] BT.lf) [6,7,25,132,192,272] (BT.nd BT.lf [6,7,32,98,272,900] BT.lf)) [6,7,32,98,404,768] (BT.nd (BT.nd BT.lf [6,7,32,98,512,777] BT.lf) [6,7,32,98,521,768] BT.lf)) [6,7,32,122,132,272] (BT.nd (BT.nd (BT.nd BT.lf [6,7,32,132,201,272,768] BT.lf) [6,7,41,98,272,768] BT.lf) [6,7,41,98,512,768] (BT.nd (BT.nd BT.lf [6,7,56,98,132,272] BT.lf) [6,7,98,132,216,272] BT.lf))) [6,7,98,132,272,800] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,98,132,272,960] BT.lf) [6,7,98,132,304,768] (BT.nd BT.lf [6,7,98,132,464,768] BT.lf)) [6,7,98,156,192,272] (BT.nd (BT.nd BT.lf [6,7,98,164,272,768] BT.lf) [6,7,98,192,272,900] BT.lf)) [6,7,98,192,404,768] (BT.nd (BT.nd (BT.nd BT.lf [6,7,98,192,512,777] BT.lf) [6,7,98,192,521,768] BT.lf) [6,7,98,196,272,768] (BT.nd (BT.nd BT.lf [6,7,132,192,272,866] BT.lf) [6,7,132,192,370,768] BT.lf)))) [6,7,132,192,512,777] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,132,192,521,768] BT.lf) [6,7,132,201,272,768] (BT.nd BT.lf [6,7,132,201,512,768] BT.lf)) [6,9,24,31,32,98,272] (BT.nd (BT.nd BT.lf [6,9,24,31,98,192,272] BT.lf) [6,9,24,31,132,192,272] BT.lf)) [6,9,24,32,39,98,272] (BT.nd (BT.nd (BT.nd BT.lf [6,9,24,32,98,103,272] BT.lf) [6,9,24,32,98,132,279] BT.lf) [6,9,24,32,98,192,279] (BT.nd (BT.nd BT.lf [6,9,24,32,98,272,279] BT.lf) [6,9,24,32,98,272,960] BT.lf))) [6,9,24,32,98,272,1016] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,9,24,32,98,279] BT.lf) [6,9,24,32,98,279,512] (BT.nd BT.lf [6,9,24,32,98,279,768] BT.lf)) [6,9,24,32,98,704] (BT.nd (BT.nd BT.lf [6,9,24,32,103,132,272] BT.lf) [6,9,24,32,103,192,272] BT.lf)) [6,9,24,32,103,272] (BT.nd (BT.nd (BT.nd BT.lf [6,9,24,32,103,272,512] BT.lf) [6,9,24,32,103,272,768] BT.lf) [6,9,24,32,128,272,768] (BT.nd (BT.nd BT.lf [6,9,24,32,128,512] BT.lf) [6,9,24,32,132,192,279] BT.lf)))))) [6,9,24,32,132,279,512] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,9,24,32,132,279,768] BT.lf) [6,9,24,98,132,192,272,775] (BT.nd BT.lf [6,9,24,98,132,192,279] BT.lf)) [6,9,24,98,132,192,279,768] (BT.nd (BT.nd BT.lf [6,9,24,98,192,199,272] BT.lf) [6,9,24,98,192,272,279] BT.lf)) [6,9,24,98,192,272,800] (BT.nd (BT.nd (BT.nd BT.lf [6,9,24,98,192,272,1016] BT.lf) [6,9,24,98,192,279] (BT.nd BT.lf [6,9,24,98,192,279,512] BT.lf)) [6,9,24,98,192,279,768] (BT.nd (BT.nd BT.lf [6,9,24,98,192,544] BT.lf) [6,9,24,132,192,199,272] BT.lf))) [6,9,24,132,192,272,279] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,9,24,132,192,272,800] BT.lf) [6,9,24,132,192,272,1016] (BT.nd BT.lf [6,9,24,132,192,279] BT.lf)) [6,9,24,132,192,279,512] (BT.nd (BT.nd BT.lf [6,9,24,132,192,279,768] BT.lf) [6,9,24,132,192,544] BT.lf)) [6,9,24,135,192,272] (BT.nd (BT.nd (BT.nd BT.lf [6,9,32,98,192,536] BT.lf) [6,9,32,98,216,512] BT.lf) [6,9,32,98,512,775] (BT.nd (BT.nd BT.lf [6,9,32,98,519,768] BT.lf) [6,9,32,103,272,768] BT.lf)))) [6,9,32,103,512,768] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,9,32,132,192,536] BT.lf) [6,9,32,135,192,272,768] (BT.nd BT.lf [6,9,56,98,192,512] BT.lf)) [6,9,56,132,192,512] (BT.nd (BT.nd BT.lf [6,9,98,192,512,775] BT.lf) [6,9,98,192,519,768] BT.lf)) [6,9,132,192,512,775] (BT.nd (BT.nd (BT.nd BT.lf [6,9,132,192,519,768] BT.lf) [6,9,135,192,272,768] BT.lf) [6,9,135,192,512,768] (BT.nd (BT.nd BT.lf [6,15,24,98,132,192,272,768] BT.lf) [6,24,32,98,132,272,519] BT.lf))) [6,24,32,98,132,464] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,24,32,98,192,272,777] BT.lf) [6,24,32,98,192,404] (BT.nd BT.lf [6,24,32,98,192,521] BT.lf)) [6,24,32,98,201,272,768] (BT.nd (BT.nd BT.lf [6,24,32,98,201,512] BT.lf) [6,24,32,132,192,272,777] BT.lf)) [6,24,32,132,192,370] (BT.nd (BT.nd (BT.nd BT.lf [6,24,32,132,192,521] BT.lf) [6,24,32,132,226,272] BT.lf) [6,24,41,98,192,272,768] (BT.nd (BT.nd BT.lf [6,24,41,98,192,512] BT.lf) [6,24,41,132,192,272,768] BT.lf))))) [6,24,41,132,192,512] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,24,98,132,192,272,519] BT.lf) [6,24,98,132,192,304] (BT.nd BT.lf [6,24,98,164,192,272] BT.lf)) [6,32,98,132,216,272] (BT.nd (BT.nd BT.lf [6,32,98,132,272,775] BT.lf) [6,32,98,132,279,768] BT.lf)) [6,32,98,156,192,272] (BT.nd (BT.nd (BT.nd BT.lf [6,32,122,132,192,272] BT.lf) [6,56,98,132,192,272] BT.lf) [6,98,132,192,272,775] (BT.nd (BT.nd BT.lf [6,98,132,192,279,768] BT.lf) [7,7,9,24,32,98,132,272] BT.lf))) [7,7,9,24,32,98,132,512] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,7,9,24,32,98,192,272] BT.lf) [7,7,9,24,32,98,272] (BT.nd BT.lf [7,7,9,24,32,98,272,512] BT.lf)) [7,7,9,24,32,98,272,768] (BT.nd (BT.nd BT.lf [7,7,9,24,32,132,192,272] BT.lf) [7,7,9,24,32,132,272,512] BT.lf)) [7,7,9,24,32,132,272,768] (BT.nd (BT.nd (BT.nd BT.lf [7,7,9,24,32,132,512] BT.lf) [7,7,9,24,98,132,192,272] BT.lf) [7,7,9,24,98,132,192,272,768] (BT.nd (BT.nd BT.lf [7,7,9,24,98,132,192,512] BT.lf) [7,7,9,24,98,192,272] BT.lf)))) [7,7,9,24,98,192,272,512] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,7,9,24,98,192,272,768] BT.lf) [7,7,9,24,98,192,512] (BT.nd BT.lf [7,7,9,24,132,192,272] BT.lf)) [7,7,9,24,132,192,272,512] (BT.nd (BT.nd BT.lf [7,7,9,24,132,192,272,768] BT.lf) [7,7,9,32,98,192,272,768] BT.lf)) [7,7,9,32,98,272,768] (BT.nd (BT.nd (BT.nd BT.lf [7,7,9,32,98,512,768] BT.lf) [7,7,9,32,132,192,272,768] BT.lf) [7,7,9,32,132,272,768] (BT.nd (BT.nd BT.lf [7,7,9,98,192,272,768] BT.lf) [7,7,9,98,192,512,768] BT.lf))) [7,7,9,132,192,272,768] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,7,9,132,192,512,768] BT.lf) [7,7,24,32,98,132,272] (BT.nd BT.lf [7,7,24,32,98,132,272,512] BT.lf)) [7,7,24,98,132,192,272] (BT.nd (BT.nd BT.lf [7,7,24,98,132,192,272,512] BT.lf) [7,7,32,98,132,272,768] BT.lf)) [7,7,98,132,192,272,768] (BT.nd (BT.nd (BT.nd BT.lf [7,9,24,32,98,192,272,768] BT.lf) [7,9,24,32,98,192,512] BT.lf) [7,9,24,32,132,192,272,768] (BT.nd (BT.nd BT.lf [7,9,24,32,132,192,512] BT.lf) [7,24,32,98,132,192,272] BT.lf))))))))))

def hintValues : Array Nat := #[32837,32838,32840,32869,32870,32872,32966,32968,33029,33030,36929,36961,36966,37057,37062,37121,37130,37953,37985,37989,37992,38081,38085,38088,38090,38145,38149,38152,38154,40001,40033,40037,40038,40129,40133,40134,40198,42081,42177,42181,42184,65573,65574,65576,65637,65638,65640,65642,65733,65734,65736,65797,65800,65802,69665,69729,69736,69825,69830,69889,69898,70689,70753,72737,72801,72805,72806,72897,72961,72970,74849,98341,98342,98344,98373,98374,98376,98501,98502,98504,98565,102433,102438,102440,102442,102465,102598,102600,102602,102657,102662,102664,102666,103457,103461,103489,103493,103621,103624,103685,103688,105505,105509,105510,105537,105541,105670,105674,105733,105738,107553,107557,107558,107585,107589,107717,107718,107720,107781,196645,196646,196648,196677,196678,196680,196709,196870,200737,200742,200744,200746,200769,200774,200776,200801,200806,200808,200810,200966,200968,200970,201761,201765,201768,201793,201797,201800,201802,201825,201829,201832,201834,201985,201989,201992,201994,203809,203813,203814,203841,203846,203873,203877,203878,203882,204037,204038,204042,205857,205864,205925,262181,262182,262213,262216,262245,262246,262250,262341,262344,266273,266278,266280,266282,266305,266312,266314,266337,266342,266344,266346,266438,266440,266442,267297,267301,267304,267306,267329,267333,267336,267365,267368,267461,267464,267466,269345,269349,269350,269354,269377,269381,269386,269413,269414,269509,269510,269514,271393,271397,271398,271425,271429,271432,271461,271464,271557,271558,271560]
def decodeHints (xs : List Nat) : List (Nat × Nat) := xs.map fun w => (w / 256, hintValues[w % 256]?.getD 0)
noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([2,15,378,964],[]),([2,15,476,866],[]),([2,98,476,783],[]),([2,196,378,783],[]),([3,7,8,370,964],[]),([3,7,8,468,866],[]),([3,7,9,378,964],[]),([3,7,9,476,866],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([3,7,98,196,264],[]),([3,7,98,476,777],[]),([3,7,132,378,969],[]),([3,7,196,378,777],[]),([3,7,201,378,900],[]),([3,7,329],(decodeHints [81,583,1105,1539])),([3,8,98,279,964],[]),([3,8,98,468,775],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([3,8,196,279,866],[]),([3,8,196,370,775],[]),([3,9,24,343],(decodeHints [14354])),([3,9,24,680],(decodeHints [14408,18513,20551])),([3,9,56,375],(decodeHints [14366])),([3,9,56,648],(decodeHints [14409,18513,20551])),([3,9,98,476,775],[]),([3,9,152,471],(decodeHints [14354]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([3,9,196,378,775],[]),([3,9,327],(decodeHints [11,515,1035,1607])),([3,9,343,999],(decodeHints [21515])),([3,9,375,967],(decodeHints [21515])),([3,9,471,871],(decodeHints [21515])),([3,9,696],(decodeHints [71,515,1095,1547])),([3,15,24,370,964],[]),([3,15,24,468,866],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([3,15,98,220,256],[]),([3,15,98,280,964],[]),([3,15,98,476,768],[]),([3,15,122,196,256],[]),([3,15,122,272,964],[]),([3,15,132,378,960],[]),([3,15,132,472,866],[]),([3,15,156,370,960],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([3,15,156,464,866],[]),([3,15,192,378,900],[]),([3,15,192,412,866],[]),([3,15,196,280,866],[]),([3,15,196,378,768],[]),([3,15,216,404,866],[]),([3,15,220,272,866],[]),([3,24,41,375],(decodeHints [14366]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([3,24,41,648],(decodeHints [14409,18503,20561])),([3,24,98,468,783],[]),([3,24,137,471],(decodeHints [14354])),([3,24,196,370,783],[]),([3,24,272,937],(decodeHints [14417])),([3,24,343,1014],(decodeHints [21507])),([3,24,375,982],(decodeHints [21507])),([3,24,681],(decodeHints [81,523,1105,1539]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([3,25,343],(decodeHints [18,516,1042,1608])),([3,41,359],(decodeHints [11,515,1035,1607])),([3,41,375,999],(decodeHints [21515])),([3,41,664],(decodeHints [71,515,1095,1547])),([3,56,374],(decodeHints [3,523,1027,1617])),([3,56,375,1014],(decodeHints [21507])),([3,56,649],(decodeHints [81,523,1105,1539])),([3,57,375],(decodeHints [30,517,1054,1609]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([3,60,370],(decodeHints [0,522,1024,1590])),([3,71,265],(decodeHints [81,583,1105,1539])),([3,73,88,279],(decodeHints [14354])),([3,73,263],(decodeHints [11,515,1035,1607])),([3,89,279],(decodeHints [18,516,1042,1608])),([3,98,132,472,783],[]),([3,98,156,464,783],[]),([3,98,192,412,783],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([3,98,196,280,783],[]),([3,98,216,404,783],[]),([3,98,220,272,783],[]),([3,103,297],(decodeHints [81,583,1105,1539])),([3,122,192,404,783],[]),([3,122,196,272,783],[]),([3,122,201,404,775],[]),([3,122,308],(decodeHints [41,566,1065,1546]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([3,126,304],(decodeHints [171,692,1195,1551])),([3,132,192,378,783],[]),([3,132,201,378,775],[]),([3,135,457],(decodeHints [81,583,1105,1539])),([3,137,568],(decodeHints [71,515,1095,1547])),([3,152,553],(decodeHints [81,523,1105,1539])),([3,156,192,370,783],[]),([3,156,466],(decodeHints [0,522,1024,1590]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([3,158,464],(decodeHints [119,639,1143,1549])),([3,169,536],(decodeHints [71,515,1095,1547])),([3,184,521],(decodeHints [81,523,1105,1539])),([3,188,498],(decodeHints [0,522,1024,1590])),([3,201,391],(decodeHints [11,515,1035,1607])),([3,216,406],(decodeHints [3,523,1027,1617])),([3,217,407],(decodeHints [18,516,1042,1608])),([3,218,404],(decodeHints [41,566,1065,1546]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([3,250,436],(decodeHints [41,566,1065,1546])),([3,519,841],(decodeHints [81,593,1105,1547])),([3,521,839],(decodeHints [11,523,1035,1617])),([3,553,871],(decodeHints [11,523,1035,1617])),([3,583,777],(decodeHints [81,593,1105,1547])),([3,585,775],(decodeHints [11,523,1035,1617])),([3,615,809],(decodeHints [81,593,1105,1547])),([3,647,969],(decodeHints [81,593,1105,1547]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([3,713,903],(decodeHints [11,523,1035,1617])),([4,2,156,464],(decodeHints [122,634,1146,1667,2170,2617,14714,14970,18736,19066])),([4,2,216,404],(decodeHints [44,556,1068,1591,2092,2645,14636,14892,18762,18988])),([4,4,56,370],(decodeHints [3,515,1027,1547,2051,2641,14595,14851,18759,18947])),([4,4,122,304],(decodeHints [171,683,1195,1716,2219,2575,14763,15019,18696,19115])),([4,7,8,98,196,256],[]),([4,7,8,98,272,964],[]),([4,7,8,98,468,768],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,8,132,370,960],[]),([4,7,8,132,464,866],[]),([4,7,8,192,370,900],[]),([4,7,8,192,404,866],[]),([4,7,8,196,272,866],[]),([4,7,8,196,370,768],[]),([4,7,9,24,336],(decodeHints [20629])),([4,7,9,24,338],(decodeHints [20629]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,9,24,343],(decodeHints [15379,20629])),([4,7,9,24,345],(decodeHints [14477,24647])),([4,7,9,24,370,964],[]),([4,7,9,24,468,866],[]),([4,7,9,24,685],(decodeHints [20566,28757])),([4,7,9,24,687],(decodeHints [20566,28753])),([4,7,9,31,336],(decodeHints [15502])),([4,7,9,41,668],(decodeHints [14413,20577,26721,28757]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,9,56,370],(decodeHints [20642])),([4,7,9,56,375],(decodeHints [15391,20642])),([4,7,9,56,653],(decodeHints [20567,28757])),([4,7,9,98,220,256],[]),([4,7,9,98,280,964],[]),([4,7,9,98,476,768],[]),([4,7,9,98,700],(decodeHints [14385])),([4,7,9,122,196,256],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,9,122,272,964],[]),([4,7,9,132,378,960],[]),([4,7,9,132,472,866],[]),([4,7,9,141,568],(decodeHints [26728,28757])),([4,7,9,152,464],(decodeHints [20629])),([4,7,9,156,370,960],[]),([4,7,9,156,464],[]),([4,7,9,156,464,866],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,9,156,468],(decodeHints [20524])),([4,7,9,156,471],[]),([4,7,9,156,473],(decodeHints [14477])),([4,7,9,156,553],(decodeHints [14413,20565,26705,28757])),([4,7,9,156,559],(decodeHints [28753])),([4,7,9,159,464],(decodeHints [15502])),([4,7,9,173,536],(decodeHints [26719,28757])),([4,7,9,188,370],(decodeHints [14384]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,9,188,521],(decodeHints [14413,20565,26705,28757])),([4,7,9,192,378,900],[]),([4,7,9,192,412,866],[]),([4,7,9,196,280,866],[]),([4,7,9,196,378,768],[]),([4,7,9,216,404,866],[]),([4,7,9,220,272,866],[]),([4,7,9,320],(decodeHints [81,583,1105,1539,2129,2641,18699,19025,20817,21003]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,9,336,999],(decodeHints [29777])),([4,7,9,370,967],(decodeHints [29781])),([4,7,9,375,960],(decodeHints [29777])),([4,7,9,464,867],(decodeHints [29777])),([4,7,9,464,871],(decodeHints [29777])),([4,7,9,471,866],(decodeHints [29781])),([4,7,9,700],(decodeHints [81,593,1105,1539,2129,2641,14669,19025,19783,21077])),([4,7,24,41,370],(decodeHints [20642]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,24,41,375],(decodeHints [20642])),([4,7,24,41,653],(decodeHints [20567,26721])),([4,7,24,73,281],(decodeHints [18626,24597])),([4,7,24,73,336],[]),([4,7,24,98,468,777],[]),([4,7,24,132,370,969],[]),([4,7,24,137,464],(decodeHints [20629])),([4,7,24,141,468],(decodeHints [20524]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,24,141,553],(decodeHints [20565,26728])),([4,7,24,173,521],(decodeHints [20565,26719])),([4,7,24,196,370,777],[]),([4,7,24,201,370,900],[]),([4,7,24,201,404,866],[]),([4,7,24,336,345],(decodeHints [21597])),([4,7,24,336,1014],(decodeHints [25725])),([4,7,24,370,982],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,25,336],(decodeHints [149,584,1173,1540,2197,2646,18706,19093])),([4,7,41,141,536],(decodeHints [26728,28769])),([4,7,41,156,521],(decodeHints [20565,26705,28769])),([4,7,41,354],(decodeHints [135,586,1159,1580,2183,2657,18743,19079])),([4,7,41,370,999],(decodeHints [29831])),([4,7,41,668],(decodeHints [97,609,1121,1539,2145,2695,14669,19041,19783])),([4,7,56,141,521],(decodeHints [20565,26728])),([4,7,56,370,1014],(decodeHints [25725]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,57,370],(decodeHints [162,588,1186,1582,2210,2647,18752,19106])),([4,7,64,265],(decodeHints [81,583,1105,1617,2129,2563,14673,14929,20747,21073])),([4,7,73,88,272],(decodeHints [20681])),([4,7,73,256],(decodeHints [81,583,1105,1539,2129,2641,18699,19025,20817,21003])),([4,7,89,272],(decodeHints [201,584,1225,1540,2249,2650,18706,19145])),([4,7,98,132,192,264],[]),([4,7,98,132,280,969],[]),([4,7,98,132,472,777],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,98,156,464,777],[]),([4,7,98,192,412,777],[]),([4,7,98,196,280,777],[]),([4,7,98,201,280,900],[]),([4,7,98,216,404,777],[]),([4,7,98,220,272,777],[]),([4,7,98,297],(decodeHints [85,586,1109,1633,2133,2604,14674,14929])),([4,7,122,132,201,256],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,122,132,272,969],[]),([4,7,122,192,404,777],[]),([4,7,122,196,272,777],[]),([4,7,122,201,272,900],[]),([4,7,122,201,404,768],[]),([4,7,122,201,644],[]),([4,7,122,713],(decodeHints [85,597,1109,1725,2133,2604,14929,15701,18768])),([4,7,132,192,378,777],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,132,201,280,866],[]),([4,7,132,201,378,768],[]),([4,7,132,201,634],(decodeHints [14421])),([4,7,132,457],(decodeHints [81,583,1105,1617,2129,2563,14673,14929,21073,21841])),([4,7,156,192,370,777],[]),([4,7,156,201,281],[]),([4,7,156,464,473],(decodeHints [21597])),([4,7,156,464,1014],(decodeHints [25725]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,156,553],(decodeHints [81,593,1105,1671,2129,2563,14929,15697,18765])),([4,7,188,521],(decodeHints [81,593,1105,1673,2129,2563,14929,15697,18765])),([4,7,201,388],(decodeHints [189,583,1213,1539,2237,2668,18699,19133])),([4,7,201,634],(decodeHints [108,620,1132,1580,2156,2749,14672,19052,19786])),([4,7,217,404],(decodeHints [201,584,1225,1540,2249,2650,18706,19145])),([4,7,370,964],(decodeHints [46,583,1070,1582,2094,2563])),([4,7,468,866],(decodeHints [4,584,1028,1540,2052,2604])),([4,7,512,841],(decodeHints [81,583,1105,1617,2129,2563,14673,14929,21073,21841]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,521,832],(decodeHints [137,583,1161,1673,2185,2641,18699,19081])),([4,7,553,866],(decodeHints [135,586,1159,1671,2183,2645,18743,19079])),([4,7,576,777],(decodeHints [81,583,1105,1617,2129,2697,14673,14929])),([4,7,585,768],(decodeHints [190,583,1214,1726,2238,2641,18699,19134])),([4,7,610,809],(decodeHints [85,586,1109,1621,2133,2695,14674,14929])),([4,7,644,969],(decodeHints [81,583,1105,1617,2129,2563,14673,14929,21073,21841])),([4,7,713,900],(decodeHints [189,583,1213,1725,2237,2641,18699,19133])),([4,8,98,132,279,960],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([4,8,98,132,464,775],[]),([4,8,98,192,279,900],[]),([4,8,98,192,404,775],[]),([4,8,98,196,272,775],[]),([4,8,98,196,279,768],[]),([4,8,132,192,279,866],[]),([4,8,132,192,370,775],[]),([4,9,24,31,336],(decodeHints [26695,28743]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,24,32,343],(decodeHints [14366,18526,20573])),([4,9,24,32,375],(decodeHints [14366])),([4,9,24,32,648],(decodeHints [14409,24657,26695])),([4,9,24,41,375],(decodeHints [14366,20510,24657])),([4,9,24,56,375],(decodeHints [14367,18463,26695])),([4,9,24,64,279],(decodeHints [14354,18453,20502])),([4,9,24,64,343],(decodeHints [14354])),([4,9,24,64,744],(decodeHints [14408,18552,20608,24657,26695]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,24,66,279],(decodeHints [14398])),([4,9,24,71,272],(decodeHints [14537])),([4,9,24,71,279],(decodeHints [14537])),([4,9,24,71,281],(decodeHints [18626,28743])),([4,9,24,71,336],(decodeHints [14537])),([4,9,24,71,343],(decodeHints [14537,19475])),([4,9,24,71,751],(decodeHints [14426,26635])),([4,9,24,73,279],(decodeHints [14354,18453,20498,24597,28743]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,24,88,279],(decodeHints [14355,18451,20502,26646,28743])),([4,9,24,95,272],(decodeHints [26695,28743])),([4,9,24,98,279,964],[]),([4,9,24,98,343],(decodeHints [14354])),([4,9,24,98,468,775],[]),([4,9,24,128,471],(decodeHints [14354])),([4,9,24,132,343],(decodeHints [14354])),([4,9,24,192,343],(decodeHints [14354]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,24,196,279,866],[]),([4,9,24,196,370,775],[]),([4,9,24,272,343],(decodeHints [14354,21522])),([4,9,24,272,928],(decodeHints [20661])),([4,9,24,272,952],(decodeHints [14408,24751])),([4,9,24,279,336],(decodeHints [14354])),([4,9,24,279,343],(decodeHints [14429,19475,21522])),([4,9,24,279,676],(decodeHints [14398]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,24,279,932],(decodeHints [14398])),([4,9,24,279,957],(decodeHints [14398])),([4,9,24,279,959],(decodeHints [14354])),([4,9,24,336,343],(decodeHints [14354,21522])),([4,9,24,336,1016],(decodeHints [14408,24701])),([4,9,24,343],(decodeHints [14611,14866,19015,19731,21063,21778])),([4,9,24,343,512],(decodeHints [14354,24687,26734])),([4,9,24,343,768],(decodeHints [14354]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,24,375,471],(decodeHints [14446])),([4,9,24,375,544],(decodeHints [14366,24687,26734])),([4,9,24,375,991],(decodeHints [14366])),([4,9,24,672],(decodeHints [71,515,1095,1547,2119,2631,18769,19015,20807,21073])),([4,9,31,88,272],(decodeHints [26646,28743])),([4,9,31,135,464],[]),([4,9,32,56,375],(decodeHints [14368,18462])),([4,9,32,359],(decodeHints [11,515,1035,1547,2059,2631,14603,14859,21003,21771]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,32,375,999],(decodeHints [29707])),([4,9,32,664],(decodeHints [71,515,1095,1607,2119,2571,14663,14919,20817,21063])),([4,9,39,56,370],(decodeHints [18594])),([4,9,56,98,279],(decodeHints [14400])),([4,9,56,98,311],(decodeHints [14400])),([4,9,56,98,375],(decodeHints [14400])),([4,9,56,98,744],(decodeHints [14412,24661])),([4,9,56,103,272],(decodeHints [14549]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,56,103,279],(decodeHints [14549])),([4,9,56,103,281],(decodeHints [18525,28743])),([4,9,56,103,304],(decodeHints [14549])),([4,9,56,103,370],(decodeHints [14549])),([4,9,56,103,375],(decodeHints [14549,19487])),([4,9,56,103,751],(decodeHints [14427])),([4,9,56,132,375],(decodeHints [14373])),([4,9,56,192,375],(decodeHints [14373]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,56,272,375],(decodeHints [14366])),([4,9,56,272,920],(decodeHints [14409,24669])),([4,9,56,279,370],(decodeHints [14499])),([4,9,56,279,375],(decodeHints [14499,19487])),([4,9,56,279,925],(decodeHints [14434])),([4,9,56,370,375],(decodeHints [14400,21534])),([4,9,56,370,1016],(decodeHints [14412,24701])),([4,9,56,375],(decodeHints [14623,14878,19015,19743,21063,21790]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,56,375,512],(decodeHints [14366,24687,26734])),([4,9,56,375,768],(decodeHints [14366])),([4,9,56,640],(decodeHints [71,515,1095,1547,2119,2631,18769,19015,20807,21073])),([4,9,64,88,279],(decodeHints [18450,20502])),([4,9,64,263],(decodeHints [11,515,1035,1547,2059,2631,14603,14859,20817,21003])),([4,9,64,279,999],(decodeHints [14357,29707])),([4,9,71,88,272],[]),([4,9,71,95,272],(decodeHints [15555]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,71,256],(decodeHints [11,515,1035,1607,2059,2571,18769,18955,20747,21073])),([4,9,71,272,999],(decodeHints [29707])),([4,9,88,279],(decodeHints [22,534,1046,1550,2070,2688,14611,14866,18966,19731])),([4,9,98,132,472,775],[]),([4,9,98,156,464,775],[]),([4,9,98,192,412,775],[]),([4,9,98,196,280,775],[]),([4,9,98,216,279,900],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,98,216,404,775],[]),([4,9,98,216,471],(decodeHints [18450])),([4,9,98,220,272,775],[]),([4,9,98,279,967],[]),([4,9,98,471,775],[]),([4,9,103,272,967],[]),([4,9,103,279,960],[]),([4,9,103,288],(decodeHints [181,515,1205,1607,2229,2586,18769,19125]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,103,464,775],[]),([4,9,103,471,768],[]),([4,9,122,192,404,775],[]),([4,9,122,196,272,775],[]),([4,9,128,568],(decodeHints [71,515,1095,1607,2119,2571,14663,14919,20817,21063])),([4,9,132,192,378,775],[]),([4,9,132,216,279,866],[]),([4,9,135,448],(decodeHints [129,515,1153,1607,2177,2594,18769,19073]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,152,192,279],(decodeHints [14354])),([4,9,152,199,272],(decodeHints [14537])),([4,9,152,544],(decodeHints [71,515,1095,1547,2119,2631,18769,19015,20807,21073])),([4,9,156,192,370,775],[]),([4,9,156,196,279],(decodeHints [14354])),([4,9,156,199,279],[]),([4,9,156,464,471],(decodeHints [21522])),([4,9,156,464,1016],(decodeHints [24701]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,160,536],(decodeHints [71,515,1095,1607,2119,2571,14663,14919,20817,21063])),([4,9,184,512],(decodeHints [71,515,1095,1547,2119,2631,18769,19015,20807,21073])),([4,9,192,279,871],[]),([4,9,192,375,775],[]),([4,9,192,391],(decodeHints [11,515,1035,1570,2059,2631,14603,14859])),([4,9,199,272,871],[]),([4,9,199,279,866],[]),([4,9,199,370,775],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,199,375,768],[]),([4,9,216,407],(decodeHints [22,534,1046,1550,2070,2688,14611,14866,18966,19731])),([4,9,512,839],(decodeHints [11,515,1035,1547,2059,2631,14603,14859,21003,21771])),([4,9,519,832],(decodeHints [130,515,1154,1666,2178,2571,18769,19074])),([4,9,544,871],(decodeHints [11,515,1035,1547,2059,2631,14603,14859,21003,21771])),([4,9,576,775],(decodeHints [11,515,1035,1547,2059,2690,14603,14859])),([4,9,583,768],(decodeHints [183,515,1207,1719,2231,2571,18769,19127])),([4,9,615,800],(decodeHints [181,515,1205,1717,2229,2571,18769,19125]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,647,960],(decodeHints [129,515,1153,1665,2177,2571,18769,19073])),([4,9,704,903],(decodeHints [11,515,1035,1547,2059,2689,14603,14859])),([4,15,24,98,196,256],[]),([4,15,24,98,272,964],[]),([4,15,24,98,468,768],[]),([4,15,24,132,370,960],[]),([4,15,24,132,464,866],[]),([4,15,24,192,370,900],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,24,192,404,866],[]),([4,15,24,196,272,866],[]),([4,15,24,196,370,768],[]),([4,15,98,132,216,256],[]),([4,15,98,132,280,960],[]),([4,15,98,132,472,768],[]),([4,15,98,156,192,256],[]),([4,15,98,156,272,960],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,98,156,464,768],[]),([4,15,98,192,280,900],[]),([4,15,98,192,412,768],[]),([4,15,98,196,280,768],[]),([4,15,98,216,272,900],[]),([4,15,98,216,404,768],[]),([4,15,98,220,272,768],[]),([4,15,122,132,192,256],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,122,132,272,960],[]),([4,15,122,192,272,900],[]),([4,15,122,192,404,768],[]),([4,15,122,196,272,768],[]),([4,15,132,192,280,866],[]),([4,15,132,192,378,768],[]),([4,15,132,216,272,866],[]),([4,15,156,192,272,866],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,156,192,370,768],[]),([4,24,32,41,375],(decodeHints [14368,18462])),([4,24,32,272,905],(decodeHints [14429,18513,20674])),([4,24,32,374],(decodeHints [3,523,1027,1539,2051,2641,14595,14851,20995,21763])),([4,24,32,375,1014],(decodeHints [29699])),([4,24,32,649],(decodeHints [81,523,1105,1617,2129,2563,14673,14929,20807,21073])),([4,24,36,370],(decodeHints [1,523,1025,1553,2049,2621,14593,14849])),([4,24,39,41,370],(decodeHints [18594]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([4,24,41,98,279],(decodeHints [14400])),([4,24,41,98,311],(decodeHints [14400])),([4,24,41,98,375],(decodeHints [14400])),([4,24,41,98,744],(decodeHints [14412,24650])),([4,24,41,103,272],(decodeHints [14549])),([4,24,41,103,279],(decodeHints [14549])),([4,24,41,103,304],(decodeHints [14549])),([4,24,41,103,313],(decodeHints [20686,28753]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([4,24,41,103,370],(decodeHints [14549])),([4,24,41,103,375],(decodeHints [14549,21535])),([4,24,41,103,751],(decodeHints [14427,24587])),([4,24,41,127,272],(decodeHints [24647,28753])),([4,24,41,132,375],(decodeHints [14373])),([4,24,41,192,375],(decodeHints [14373])),([4,24,41,272,375],(decodeHints [14366,19486])),([4,24,41,272,896],(decodeHints [18614]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_54 : List (List ℕ × List (ℕ × ℕ)) := [([4,24,41,272,920],(decodeHints [14409,26799])),([4,24,41,279,370],(decodeHints [14499])),([4,24,41,279,375],(decodeHints [14499,19486])),([4,24,41,279,925],(decodeHints [14434])),([4,24,41,370,375],(decodeHints [14400,19486])),([4,24,41,370,1016],(decodeHints [14412])),([4,24,41,375],(decodeHints [14622,14879,19025,19742,21073,21791])),([4,24,41,375,512],(decodeHints [14366,24686,26735]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_54 : K_54.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_55 : List (List ℕ × List (ℕ × ℕ)) := [([4,24,41,375,768],(decodeHints [14366])),([4,24,41,640],(decodeHints [81,523,1105,1539,2129,2641,18759,19025,20817,21063])),([4,24,64,73,279],(decodeHints [18450,20501])),([4,24,64,279,1014],(decodeHints [14358,29699])),([4,24,71,272,281],(decodeHints [19549])),([4,24,71,272,777],(decodeHints [18513])),([4,24,71,272,1014],(decodeHints [27823])),([4,24,73,279],(decodeHints [21,533,1045,1542,2069,2680,14610,14867,18965,19730]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_55 : K_55.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_56 : List (List ℕ × List (ℕ × ℕ)) := [([4,24,98,132,464,783],[]),([4,24,98,192,404,783],[]),([4,24,98,196,272,783],[]),([4,24,98,201,279,900],[]),([4,24,98,201,404,775],[]),([4,24,98,201,471],(decodeHints [18450])),([4,24,98,279,982],[]),([4,24,98,308],(decodeHints [42,567,1066,1597,2090,2577,14634,14890]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_56 : K_56.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_57 : List (List ℕ × List (ℕ × ℕ)) := [([4,24,102,304],(decodeHints [172,699,1196,1730,2220,2585,14764,15020])),([4,24,103,272,313],(decodeHints [19557])),([4,24,103,272,809],(decodeHints [18513])),([4,24,103,272,982],(decodeHints [27823])),([4,24,103,281,304],[]),([4,24,128,272,809],(decodeHints [14437,18513,20686])),([4,24,128,553],(decodeHints [81,523,1105,1617,2129,2563,14673,14929,20807,21073])),([4,24,132,192,370,783],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_57 : K_57.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_58 : List (List ℕ × List (ℕ × ℕ)) := [([4,24,132,201,279,866],[]),([4,24,132,201,370,775],[]),([4,24,132,466],(decodeHints [2,523,1026,1565,2050,2623,14594,14850])),([4,24,134,464],(decodeHints [121,646,1145,1692,2169,2593,14713,14969])),([4,24,137,192,279],(decodeHints [14354])),([4,24,137,199,272],(decodeHints [14537])),([4,24,137,272,800],(decodeHints [18613])),([4,24,137,544],(decodeHints [81,523,1105,1539,2129,2641,18759,19025,20817,21063]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_58 : K_58.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_59 : List (List ℕ × List (ℕ × ℕ)) := [([4,24,141,196,279],(decodeHints [14354])),([4,24,160,272,777],(decodeHints [14429,18513,20674])),([4,24,160,521],(decodeHints [81,523,1105,1617,2129,2563,14673,14929,20807,21073])),([4,24,164,498],(decodeHints [1,523,1025,1553,2049,2621,14593,14849])),([4,24,169,272,768],(decodeHints [18615])),([4,24,169,512],(decodeHints [81,523,1105,1539,2129,2641,18759,19025,20817,21063])),([4,24,192,406],(decodeHints [3,523,1027,1569,2051,2641,14595,14851])),([4,24,194,404],(decodeHints [43,567,1067,1599,2091,2589,14635,14891]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_59 : K_59.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_60 : List (List ℕ × List (ℕ × ℕ)) := [([4,24,201,407],(decodeHints [21,533,1045,1542,2069,2680,14610,14867,18965,19730])),([4,24,226,436],(decodeHints [42,567,1066,1597,2090,2577,14634,14890])),([4,25,32,375],(decodeHints [30,517,1054,1566,2078,2633,14622,14878,21022,21790])),([4,25,64,279],(decodeHints [18,516,1042,1554,2066,2632,14610,14866,20829,21010])),([4,25,71,272],(decodeHints [201,516,1225,1608,2249,2650,20754,21193])),([4,25,103,304],(decodeHints [208,517,1232,1609,2256,2587])),([4,25,135,464],(decodeHints [143,516,1167,1608,2191,2595])),([4,25,192,407],(decodeHints [18,516,1042,1571,2066,2632,14610,14866]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_60 : K_60.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_61 : List (List ℕ × List (ℕ × ℕ)) := [([4,26,132,464],(decodeHints [119,639,1143,1695,2167,2573,14711,14967])),([4,26,192,404],(decodeHints [41,566,1065,1603,2089,2570,14633,14889])),([4,28,32,370],(decodeHints [0,522,1024,1536,2048,2614,14592,14848,20992,21760])),([4,28,98,304],(decodeHints [172,696,1196,1730,2220,2585,14764,15020])),([4,32,103,265],(decodeHints [81,593,1105,1607,2129,2563,14929,15697,18699,19025])),([4,32,122,276],(decodeHints [41,553,1065,1590,2089,2570,14889,15657,18688,18985])),([4,32,126,272],(decodeHints [171,683,1195,1716,2219,2575,15019,15787,18696,19115])),([4,32,137,536],(decodeHints [71,583,1095,1539,2119,2571,14663,14919,18769,19015]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_61 : K_61.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_62 : List (List ℕ × List (ℕ × ℕ)) := [([4,32,152,521],(decodeHints [81,593,1105,1547,2129,2563,14673,14929,18759,19025])),([4,32,156,498],(decodeHints [0,512,1024,1546,2048,2614,14592,14848,18944,19712])),([4,32,250,404],(decodeHints [41,553,1065,1590,2089,2570,14889,15657,18688,18985])),([4,32,521,871],(decodeHints [11,523,1035,1547,2059,2641,14603,14859,18955,19723])),([4,32,615,777],(decodeHints [81,593,1105,1617,2129,2571,14929,15697,18699,19025])),([4,36,122,272],(decodeHints [171,529,1195,1597,2219,2575,18730,19115])),([4,41,98,263],(decodeHints [55,556,1079,1633,2103,2634,20871,21047])),([4,41,98,279,999],(decodeHints [29751]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_62 : K_62.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_63 : List (List ℕ × List (ℕ × ℕ)) := [([4,41,98,728],(decodeHints [74,531,1098,1610,2122,2615,14922,21066,21831])),([4,41,103,127,272],(decodeHints [15567])),([4,41,103,256],(decodeHints [11,515,1035,1607,2059,2571,18769,18955,20747,21073])),([4,41,103,272,999],(decodeHints [29707])),([4,41,128,536],(decodeHints [71,515,1095,1607,2119,2571,14663,14919,20817,21063])),([4,41,152,512],(decodeHints [71,515,1095,1547,2119,2631,18769,19015,20807,21073])),([4,41,512,871],(decodeHints [11,515,1035,1547,2059,2631,14603,14859,21003,21771])),([4,41,615,768],(decodeHints [183,515,1207,1719,2231,2571,18769,19127]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_63 : K_63.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_64 : List (List ℕ × List (ℕ × ℕ)) := [([4,56,98,276],(decodeHints [44,530,1068,1629,2092,2645,20740,21036])),([4,56,98,279,1014],(decodeHints [29740])),([4,56,98,713],(decodeHints [85,530,1109,1621,2133,2604,14933,21077,21841])),([4,56,102,272],(decodeHints [175,530,1199,1629,2223,2649,20740,21167])),([4,56,103,272,281],[]),([4,56,103,272,1014],(decodeHints [27823])),([4,56,128,521],(decodeHints [81,523,1105,1617,2129,2563,14673,14929,20807,21073])),([4,56,132,498],(decodeHints [2,523,1026,1565,2050,2623,14594,14850]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_64 : K_64.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_65 : List (List ℕ × List (ℕ × ℕ)) := [([4,56,137,512],(decodeHints [81,523,1105,1539,2129,2641,18759,19025,20817,21063])),([4,56,226,404],(decodeHints [43,530,1067,1599,2091,2589])),([4,57,98,279],(decodeHints [64,558,1088,1634,2112,2636,20899,21056])),([4,57,103,272],(decodeHints [213,517,1237,1609,2261,2651,20766,21205])),([4,60,98,272],(decodeHints [173,529,1197,1597,2221,2619,20737,21165])),([4,64,519,777],(decodeHints [81,593,1105,1617,2129,2571,14673,14929,18699,19025])),([4,64,521,775],(decodeHints [11,523,1035,1547,2059,2641,14603,14859,18769,18955])),([4,71,512,777],(decodeHints [81,583,1105,1617,2129,2563,14673,14929,21073,21841]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_65 : K_65.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_66 : List (List ℕ × List (ℕ × ℕ)) := [([4,71,521,768],(decodeHints [190,583,1214,1726,2238,2641,18699,19134])),([4,73,512,775],(decodeHints [11,515,1035,1547,2059,2631,14603,14859,21003,21771])),([4,73,519,768],(decodeHints [183,515,1207,1719,2231,2571,18769,19127])),([4,98,132,192,280,783],[]),([4,98,132,201,280,775],[]),([4,98,132,216,272,783],[]),([4,98,156,192,272,783],[]),([4,98,188,464],(decodeHints [173,573,1197,1553,2221,2619,18689,19117]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_66 : K_66.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_67 : List (List ℕ × List (ℕ × ℕ)) := [([4,98,201,568],(decodeHints [72,584,1096,1580,2120,2578,14920,15687,18773])),([4,98,216,436],(decodeHints [42,573,1066,1591,2090,2577,14634,14890])),([4,98,216,553],(decodeHints [82,594,1106,1591,2130,2579,14930,15697,18762])),([4,98,279,932],(decodeHints [46,558,1070,1582,2094,2624,14890,15661,18750])),([4,98,279,964],(decodeHints [46,558,1070,1582,2094,2578])),([4,98,436,775],(decodeHints [55,567,1079,1591,2103,2604,14647,18999,19767])),([4,98,468,775],(decodeHints [18,605,1042,1554,2066,2604])),([4,98,519,809],(decodeHints [85,609,1109,1621,2133,2615,14673,14930]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_67 : K_67.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_68 : List (List ℕ × List (ℕ × ℕ)) := [([4,98,553,775],(decodeHints [55,609,1079,1591,2103,2645,18823,18999])),([4,103,512,809],(decodeHints [81,583,1105,1617,2129,2563,14673,14929,21073,21841])),([4,103,521,800],(decodeHints [181,583,1205,1717,2229,2641])),([4,103,544,777],(decodeHints [81,583,1105,1617,2129,2563,14673,21073])),([4,103,553,768],(decodeHints [190,583,1214,1726,2238,2641,18699,19134])),([4,122,132,192,272,783],[]),([4,122,132,201,272,775],[]),([4,122,192,436],(decodeHints [41,566,1065,1577,2089,2570,14633,14889,21033,21801]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_68 : K_68.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_69 : List (List ℕ × List (ℕ × ℕ)) := [([4,132,201,216,279],(decodeHints [20498,24596])),([4,132,201,263],(decodeHints [11,523,1035,1539,2059,2631,14859,15627,18769,18955])),([4,132,216,274],(decodeHints [3,616,1027,1547,2051,2641,18734,18947])),([4,132,217,279],(decodeHints [18,530,1042,1540,2066,2632,14866,15634,18781,18962])),([4,132,218,272],(decodeHints [171,541,1195,1599,2219,2575,18731,19115])),([4,132,250,304],(decodeHints [171,541,1195,1599,2219,2575,18731,19115])),([4,132,519,969],(decodeHints [81,593,1105,1617,2129,2571,14673,14929,19025,19793])),([4,132,713,775],(decodeHints [11,523,1035,1547,2059,2641,14859,15627,18769,18955]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_69 : K_69.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_70 : List (List ℕ × List (ℕ × ℕ)) := [([4,134,216,272],(decodeHints [175,613,1199,1566,2223,2649,18693,19119])),([4,135,192,265],(decodeHints [81,583,1105,1570,2129,2563,20865,21073])),([4,135,201,256],(decodeHints [81,583,1105,1539,2129,2641,18699,19025,20817,21003])),([4,135,201,272,800],(decodeHints [15541,29777])),([4,135,201,304,768],(decodeHints [15543,29777])),([4,135,217,272],(decodeHints [201,584,1225,1540,2249,2650,18706,19145])),([4,135,512,969],(decodeHints [81,593,1105,1617,2129,2571,14673,14929,21073,21841])),([4,135,521,960],(decodeHints [129,641,1153,1665,2177,2641]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_70 : K_70.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_71 : List (List ℕ × List (ℕ × ℕ)) := [([4,135,704,777],(decodeHints [81,583,1105,1617,2129,2689])),([4,135,713,768],(decodeHints [190,583,1214,1726,2238,2641,18699,19134])),([4,156,192,274],(decodeHints [0,522,1024,1603,2048,2614,20860,20992])),([4,156,194,272],(decodeHints [173,541,1197,1599,2221,2619,20738,21165])),([4,156,226,304],(decodeHints [172,541,1196,1599,2220,2585])),([4,158,192,272],(decodeHints [171,668,1195,1569,2219,2575,20857,21163])),([4,164,250,272],(decodeHints [171,529,1195,1597,2219,2575,18730,19115])),([4,188,192,370],(decodeHints [0,522,1024,1536,2048,2614,14592,15872,20777,20992]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_71 : K_71.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_72 : List (List ℕ × List (ℕ × ℕ)) := [([4,188,226,272],(decodeHints [173,529,1197,1597,2221,2619,20737,21165])),([4,192,521,903],(decodeHints [11,523,1035,1547,2059,2641,14603,14859])),([4,192,647,777],(decodeHints [81,546,1105,1617,2129,2571,18817,19025])),([4,196,279,866],(decodeHints [4,516,1028,1540,2052,2578])),([4,196,370,775],(decodeHints [11,616,1035,1547,2059,2563])),([4,201,512,903],(decodeHints [11,523,1035,1547,2059,2641,14603,14859,21003,21771])),([4,201,647,768],(decodeHints [183,515,1207,1719,2231,2571,18769,19127])),([5,2,24,132,464],(decodeHints [124,636,1148,1670,2172,2719,3196,3651,14716,14972,18812,19068,20860,21116,24882,25212]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_72 : K_72.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_73 : List (List ℕ × List (ℕ × ℕ)) := [([5,2,24,192,404],(decodeHints [44,556,1068,1591,2092,2627,3116,3669,14636,14892,18732,18988,20780,21036,24956,25132])),([5,2,132,216,272],(decodeHints [175,687,1199,1640,2223,2624,3247,3673,14767,15023,18863,19119,24908,25263,26926,27311])),([5,2,156,192,272],(decodeHints [173,685,1197,1695,2221,2627,3245,3643,14765,15021,18861,19117,24956,25261,29052,29357])),([5,4,24,32,370],(decodeHints [3,515,1027,1547,2051,2563,3075,3665,14595,14851,18691,18947,20739,20995,24903,25091,29187,29955])),([5,4,24,98,304],(decodeHints [172,684,1196,1723,2220,2754,3244,3609,14764,15020,18860,19116,20908,21164,24841,25260])),([5,4,32,122,272],(decodeHints [171,683,1195,1707,2219,2740,3243,3599,14763,15019,18859,19115,21163,21931,24840,25259,26888,27307])),([5,4,56,98,272],(decodeHints [175,687,1199,1554,2223,2653,3247,3673,14767,15023,18863,19119,24836,25263,28932,29359])),([5,7,8,98,132,192,256],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_73 : K_73.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_74 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,8,98,132,272,960],[]),([5,7,8,98,132,464,768],[]),([5,7,8,98,192,272,900],[]),([5,7,8,98,192,404,768],[]),([5,7,8,98,196,272,768],[]),([5,7,8,132,192,272,866],[]),([5,7,8,132,192,370,768],[]),([5,7,9,24,32,336],(decodeHints [20642,26721,28765]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_74 : K_74.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_75 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,24,32,370],(decodeHints [20642])),([5,7,9,24,32,375],(decodeHints [15391,20642])),([5,7,9,24,32,653],(decodeHints [20567,36949])),([5,7,9,24,39,370],(decodeHints [18443,20642,28683])),([5,7,9,24,41,370],(decodeHints [14413,20544,28736,34897])),([5,7,9,24,41,644],(decodeHints [14413,20566,26705,28736])),([5,7,9,24,56,370],(decodeHints [18503,20642,26786,36949])),([5,7,9,24,64,272],(decodeHints [20681,26765,28875]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_75 : K_75.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_76 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,24,64,279],(decodeHints [15379,20681,26765,28875])),([5,7,9,24,64,281],(decodeHints [14530,28875,32839])),([5,7,9,24,64,336],(decodeHints [20681])),([5,7,9,24,64,751],(decodeHints [20570,26765,28810,36945])),([5,7,9,24,66,272],(decodeHints [20681,28875])),([5,7,9,24,71,272],(decodeHints [15561,18580,20681,28875])),([5,7,9,24,73,272],(decodeHints [14477,20498,24656,26765,28875])),([5,7,9,24,88,272],(decodeHints [20681,26825,28875,37067,38993]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_76 : K_76.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_77 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,24,98,196,256],[]),([5,7,9,24,98,272,964],[]),([5,7,9,24,98,336],(decodeHints [20629])),([5,7,9,24,98,468,768],[]),([5,7,9,24,98,676],(decodeHints [14385])),([5,7,9,24,128,464],(decodeHints [20629,24719])),([5,7,9,24,132,336],(decodeHints [20629,28773])),([5,7,9,24,132,370,960],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_77 : K_77.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_78 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,24,132,464],(decodeHints [20629,24719])),([5,7,9,24,132,464,866],[]),([5,7,9,24,132,468],(decodeHints [20629])),([5,7,9,24,132,471],(decodeHints [20629])),([5,7,9,24,132,473],(decodeHints [14477,24719,26768])),([5,7,9,24,132,553],(decodeHints [14413,20566,34897,36928])),([5,7,9,24,132,559],(decodeHints [20566,24611,36945])),([5,7,9,24,135,464],(decodeHints [15503,20629,24719]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_78 : K_78.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_79 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,24,141,464],(decodeHints [20498,24719,28690,34960])),([5,7,9,24,141,544],(decodeHints [20567,28757])),([5,7,9,24,156,464],(decodeHints [18577,20629,24719,36945])),([5,7,9,24,164,370],(decodeHints [14385,20650])),([5,7,9,24,164,464],(decodeHints [20650,28765])),([5,7,9,24,164,521],(decodeHints [14413,20568,34897,36926])),([5,7,9,24,173,512],(decodeHints [20566,28757])),([5,7,9,24,192,336],(decodeHints [20642,26732]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_79 : K_79.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_80 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,24,192,370,900],[]),([5,7,9,24,192,404,866],[]),([5,7,9,24,196,272,866],[]),([5,7,9,24,196,370,768],[]),([5,7,9,24,272,336],(decodeHints [20573,26773,29789,34957])),([5,7,9,24,272,676],(decodeHints [20542,29758,36957])),([5,7,9,24,272,932],(decodeHints [20681,28863])),([5,7,9,24,272,957],(decodeHints [20681]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_80 : K_80.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_81 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,24,272,959],(decodeHints [20681])),([5,7,9,24,336],(decodeHints [14669,16021,20885,21010,29265,30045])),([5,7,9,24,336,512],(decodeHints [20629,34931,36974])),([5,7,9,24,336,768],(decodeHints [20629,34931])),([5,7,9,24,370,464],(decodeHints [20593,34960])),([5,7,9,24,370,544],(decodeHints [20642,34931,36977])),([5,7,9,24,370,960],(decodeHints [20642,28757,34960,40017])),([5,7,9,24,370,991],(decodeHints [20642]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_81 : K_81.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_82 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,24,464,644],(decodeHints [20629,36974])),([5,7,9,24,464,866],(decodeHints [20629,28757,40017])),([5,7,9,24,464,891],(decodeHints [20629])),([5,7,9,24,676],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,14669,18759,19025,21054,25169,25927,26961,29009,29265])),([5,7,9,31,64,272],(decodeHints [15555,24724,26765,28875])),([5,7,9,31,132,464],(decodeHints [15502])),([5,7,9,32,56,370],(decodeHints [20643,26786])),([5,7,9,32,98,668],(decodeHints [14387,20566,24657,29777]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_82 : K_82.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_83 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,32,141,536],(decodeHints [34920,38997])),([5,7,9,32,156,370],(decodeHints [14384,20586])),([5,7,9,32,156,464],(decodeHints [20577,28765])),([5,7,9,32,156,521],(decodeHints [14413,26709,34897,38997])),([5,7,9,32,354],(decodeHints [85,586,1109,1580,2133,2645,3157,3669,18743,19029,20821,21047,24887,25169,26965,27191,29269,30037])),([5,7,9,32,370,999],(decodeHints [40021])),([5,7,9,32,668],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,14669,18769,19025,20817,25169,25927,27221,29009,29265])),([5,7,9,41,132,536],(decodeHints [14413,20577,34913,36928]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_83 : K_83.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_84 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,41,156,512],(decodeHints [14413,20577,26721,28757])),([5,7,9,56,98,272],(decodeHints [20693])),([5,7,9,56,98,279],(decodeHints [15425,20693])),([5,7,9,56,98,281],(decodeHints [14546,26717,32842,38993])),([5,7,9,56,98,304],(decodeHints [20693,28887])),([5,7,9,56,98,370],(decodeHints [20693,26628])),([5,7,9,56,98,644],(decodeHints [14388,24657])),([5,7,9,56,98,751],(decodeHints [20571]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_84 : K_84.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_85 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,56,103,272],(decodeHints [15573,20693])),([5,7,9,56,132,370],(decodeHints [14413,20650,25671])),([5,7,9,56,132,521],(decodeHints [14413,20568,34897,36928])),([5,7,9,56,141,512],(decodeHints [20567,28757])),([5,7,9,56,192,370],(decodeHints [20642,26732])),([5,7,9,56,272,370],(decodeHints [20643,26786])),([5,7,9,56,272,925],(decodeHints [20578])),([5,7,9,56,370],(decodeHints [14669,16034,18759,18955,20898,21056,26883,27217,29269,30056]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_85 : K_85.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_86 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,56,370,512],(decodeHints [20642,34931,36977])),([5,7,9,56,370,768],(decodeHints [20642,34931])),([5,7,9,56,644],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,14669,18759,19025,21056,25169,25927,26961,29009,29265])),([5,7,9,64,88,272],(decodeHints [26825,28875])),([5,7,9,64,256],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,18699,19025,20817,21003,24843,25169,26961,27147,29009,29265])),([5,7,9,64,272,999],(decodeHints [20621,40017])),([5,7,9,88,272],(decodeHints [203,715,1227,1739,2251,2751,3275,3722,14795,16073,18891,19147,20937,21195,24985,25291,27033,27339])),([5,7,9,98,132,216,256],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_86 : K_86.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_87 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,98,132,280,960],[]),([5,7,9,98,132,472,768],[]),([5,7,9,98,132,568],(decodeHints [14414,18513])),([5,7,9,98,156,192,256],[]),([5,7,9,98,156,272,960],[]),([5,7,9,98,156,464],(decodeHints [14387,19601])),([5,7,9,98,156,464,768],[]),([5,7,9,98,156,544],(decodeHints [14387,18513,34902]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_87 : K_87.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_88 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,98,164,536],(decodeHints [14416])),([5,7,9,98,188,272],(decodeHints [14385])),([5,7,9,98,188,512],(decodeHints [14385,32828,34908])),([5,7,9,98,192,280,900],[]),([5,7,9,98,192,412,768],[]),([5,7,9,98,192,668],(decodeHints [14387,39065])),([5,7,9,98,196,280,768],[]),([5,7,9,98,216,272,900],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_88 : K_88.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_89 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,98,216,404,768],[]),([5,7,9,98,216,464],(decodeHints [26848])),([5,7,9,98,220,272,768],[]),([5,7,9,98,272,967],[]),([5,7,9,98,279,960],[]),([5,7,9,98,288],(decodeHints [191,586,1215,1580,2239,2763,3263,3737,18869,19135,20927,21183,24887,25279,26965,27327])),([5,7,9,98,304,960],(decodeHints [15545,18640,28683])),([5,7,9,98,464,775],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_89 : K_89.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_90 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,98,464,800],(decodeHints [15541,18613,36882])),([5,7,9,98,471,768],[]),([5,7,9,98,728],(decodeHints [153,665,1177,1580,2201,2763,3225,3775,14672,19097,19786,20889,21145,24906,25241,27289])),([5,7,9,103,272,960],[]),([5,7,9,103,464,768],[]),([5,7,9,122,132,192,256],[]),([5,7,9,122,132,272,960],[]),([5,7,9,122,192,272,900],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_90 : K_90.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_91 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,122,192,370],(decodeHints [20483,26755])),([5,7,9,122,192,404,768],[]),([5,7,9,122,192,644],(decodeHints [14389,39051])),([5,7,9,122,196,272,768],[]),([5,7,9,122,304],(decodeHints [215,727,1239,1751,2263,2752,3287,3723,14807,16085,18895,19159,20949,21207,24997,25303,27045,27351])),([5,7,9,122,704],(decodeHints [139,651,1163,1580,2187,2752,3211,3799,14731,19083,19845,21131,24997,25227,26965,27275])),([5,7,9,132,156,464],(decodeHints [18578,20630,26773])),([5,7,9,132,192,280,866],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_91 : K_91.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_92 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,132,192,378,768],[]),([5,7,9,132,192,634],(decodeHints [14344,18565,28837])),([5,7,9,132,216,272,866],[]),([5,7,9,132,448],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,18821,19025,20817,21003,24843,25169,26961,27147,29265,30033])),([5,7,9,132,464,999],(decodeHints [18575,40017])),([5,7,9,132,568],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,14669,19025,19783,20817,24903,25169,27200,29009,29265])),([5,7,9,152,192,272],(decodeHints [20681])),([5,7,9,156,192,272],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_92 : K_92.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_93 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,156,192,272,866],[]),([5,7,9,156,192,279],[]),([5,7,9,156,192,281],(decodeHints [14530])),([5,7,9,156,192,370,768],[]),([5,7,9,156,192,404],(decodeHints [20524,26826,28875])),([5,7,9,156,192,464],(decodeHints [24776,26826])),([5,7,9,156,192,610],(decodeHints [14345,28810])),([5,7,9,156,192,751],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_93 : K_93.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_94 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,156,196,272],(decodeHints [20681])),([5,7,9,156,199,272],[]),([5,7,9,156,201,272],(decodeHints [14477])),([5,7,9,156,272,464],(decodeHints [24721,26773])),([5,7,9,156,272,831],[]),([5,7,9,156,464],(decodeHints [14669,16021,18833,20885,21010,29265,30045])),([5,7,9,156,464,512],(decodeHints [34931,36974])),([5,7,9,156,464,768],(decodeHints [34931]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_94 : K_94.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_95 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,156,544],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,14669,19025,19783,21077,24913,25169,26961,29009,29265])),([5,7,9,159,192,272],(decodeHints [15555])),([5,7,9,164,536],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,14669,19025,19783,20817,24903,25169,27198,29009,29265])),([5,7,9,188,512],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,14669,19025,19783,21077,24913,25169,26961,29009,29265])),([5,7,9,192,272,867],[]),([5,7,9,192,272,871],[]),([5,7,9,192,279,866],[]),([5,7,9,192,370,775],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_95 : K_95.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_96 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,192,375,768],[]),([5,7,9,192,388],(decodeHints [192,583,1216,1539,2240,2775,3264,3749,18880,19136,20928,21184,24843,25280,26961,27328])),([5,7,9,192,634],(decodeHints [165,677,1189,1580,2213,2775,3237,3776,14672,18853,19109,20901,21157,25253,25930,27301])),([5,7,9,199,272,866],[]),([5,7,9,199,370,768],[]),([5,7,9,216,404],(decodeHints [203,715,1227,1739,2251,2751,3275,3722,14795,16073,18891,19147,20937,21195,24977,25291,26924,27339])),([5,7,9,216,610],(decodeHints [138,650,1162,1580,2186,2751,3210,3787,14730,18826,19082,21130,25226,25988,26965,27274])),([5,7,9,272,932],(decodeHints [191,587,1215,1727,2239,2751,3263,3787,16060,18879,19135,20927,21183,25279,26925,27327]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_96 : K_96.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_97 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,304,900],(decodeHints [192,588,1216,1728,2240,2752,3264,3799,16061,18880,19136,20928,21184,25280,26926,27328])),([5,7,9,370,960],(decodeHints [11,583,1035,1547,2059,2571,3083,3595,16008,20739,21073,24843,26891,27147,30033,30312])),([5,7,9,404,800],(decodeHints [191,586,1215,1727,2239,2751,3263,3787,16060,19135,20927,21183,24887,25279,27083,27327])),([5,7,9,436,768],(decodeHints [193,586,1217,1729,2241,2753,3265,3810,16062,19137,20929,21185,24887,25281,27106,27329])),([5,7,9,464,866],(decodeHints [18,584,1042,1554,2066,2578,3090,3602,16007,18706,20754,21010,26884,27229,30037,30301])),([5,7,9,512,832],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,18699,19025,20817,21003,24843,25169,26961,27147,29265,30033])),([5,7,9,544,866],(decodeHints [85,586,1109,1580,2133,2645,3157,3669,18743,19029,20821,21047,24887,25169,26965,27191,29269,30037])),([5,7,9,576,768],(decodeHints [193,583,1217,1539,2241,2753,3265,3724,18881,19137,20929,21185,24843,25281,26961,27329]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_97 : K_97.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_98 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,610,800],(decodeHints [191,586,1215,1580,2239,2751,3263,3722,18869,19135,20927,21183,24887,25279,26965,27327])),([5,7,9,644,960],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,18821,19025,20817,21003,24843,25169,26961,27147,29265,30033])),([5,7,9,704,900],(decodeHints [192,583,1216,1539,2240,2752,3264,3723,18880,19136,20928,21184,24843,25280,26961,27328])),([5,7,24,32,41,370],(decodeHints [20643,26786])),([5,7,24,32,107,370],(decodeHints [20484])),([5,7,24,32,141,521],(decodeHints [26709,34920])),([5,7,24,32,370,1014],(decodeHints [33917])),([5,7,24,41,98,272],(decodeHints [20693]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_98 : K_98.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_99 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,24,41,98,279],(decodeHints [20693])),([5,7,24,41,98,304],(decodeHints [20693,26838])),([5,7,24,41,98,313],(decodeHints [18640,28878,32850,38993])),([5,7,24,41,98,370],(decodeHints [20693])),([5,7,24,41,98,751],(decodeHints [20571,34951])),([5,7,24,41,103,272],(decodeHints [14497,20693])),([5,7,24,41,122,272],(decodeHints [14543,32862,34913,38997])),([5,7,24,41,132,370],(decodeHints [20650,25671,26730]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_99 : K_99.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_100 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,24,41,132,521],(decodeHints [20568,34913,36945])),([5,7,24,41,141,512],(decodeHints [20567,26721])),([5,7,24,41,192,370],(decodeHints [20642])),([5,7,24,41,272,370],(decodeHints [20643,27811])),([5,7,24,41,272,900],(decodeHints [24670,26816])),([5,7,24,41,272,925],(decodeHints [20578])),([5,7,24,41,370],(decodeHints [14663,14859,18765,20899,21154,27221,28067,29265])),([5,7,24,41,370,512],(decodeHints [20642,34929,36979]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_100 : K_100.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_101 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,24,41,370,768],(decodeHints [20642])),([5,7,24,41,644],(decodeHints [81,593,1105,1671,2129,2563,3153,3665,14673,14929,18765,25169,25937,26977,27217,29009,29281])),([5,7,24,64,73,272],(decodeHints [26825,28813])),([5,7,24,64,272,281],(decodeHints [20633,27741,28821,37005])),([5,7,24,64,272,777],(decodeHints [20706,26705,28787])),([5,7,24,64,272,1014],(decodeHints [20683,33967])),([5,7,24,73,272],(decodeHints [141,632,1165,1677,2189,2566,3213,3725,14733,14989,20754,21193,24853,25229,27217,27997,29069,29205])),([5,7,24,98,132,201,256],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_101 : K_101.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_102 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,24,98,132,272,969],[]),([5,7,24,98,132,464,777],[]),([5,7,24,98,192,404,777],[]),([5,7,24,98,196,272,777],[]),([5,7,24,98,201,272,900],[]),([5,7,24,98,201,281],(decodeHints [20645,32853])),([5,7,24,98,201,404,768],[]),([5,7,24,98,201,464],(decodeHints [20575,26848]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_102 : K_102.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_103 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,24,98,201,644],[]),([5,7,24,98,272,313],(decodeHints [27752])),([5,7,24,98,272,708],(decodeHints [27694])),([5,7,24,98,272,809],(decodeHints [26709])),([5,7,24,98,272,982],[]),([5,7,24,98,281,304],(decodeHints [20645])),([5,7,24,98,713],(decodeHints [85,597,1109,1725,2133,2764,3157,3628,14677,14933,19025,19797,20821,21077,24958])),([5,7,24,107,192,370],(decodeHints [20483,26777]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_103 : K_103.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_104 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,24,132,141,464],(decodeHints [20630,26773])),([5,7,24,132,192,370,777],[]),([5,7,24,132,201,272,866],[]),([5,7,24,132,201,281],(decodeHints [18515,32789,37068])),([5,7,24,132,201,370,768],[]),([5,7,24,132,201,464],(decodeHints [18455,20682])),([5,7,24,132,201,610],(decodeHints [18517])),([5,7,24,132,272,809],(decodeHints [20581,26705,28878]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_104 : K_104.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_105 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,24,132,464,473],(decodeHints [18455,27741])),([5,7,24,132,464,1014],(decodeHints [18575,33917])),([5,7,24,132,553],(decodeHints [81,593,1105,1671,2129,2641,3153,3587,14673,14929,19025,19793,20817,21073,24909,29025,29265])),([5,7,24,137,192,272],(decodeHints [20681])),([5,7,24,141,192,404],(decodeHints [20524,26670,28722])),([5,7,24,141,196,272],(decodeHints [20681])),([5,7,24,164,272,777],(decodeHints [20573,26705,28866])),([5,7,24,164,370],(decodeHints [3,515,1027,1673,2051,2704,3075,3665,14595,14851,19715,20739,20995,24833,29187]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_105 : K_105.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_106 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,24,164,521],(decodeHints [81,593,1105,1673,2129,2641,3153,3587,14673,14929,19025,19793,20817,21073,24909,29043,29265])),([5,7,24,192,281,404],(decodeHints [20633])),([5,7,24,196,272,610],(decodeHints [27652])),([5,7,24,201,404],(decodeHints [204,632,1228,1740,2252,2566,3276,3750,14796,15052,20938,21193,24853,25292,27340,28106])),([5,7,24,201,610],(decodeHints [166,678,1190,1725,2214,2604,3238,3788,14758,15014,18814,25254,25979,26988,27302])),([5,7,25,32,370],(decodeHints [162,588,1186,1582,2210,2722,3234,3671,18850,19106,20898,21154,24896,25250,29346,30114])),([5,7,25,64,272],(decodeHints [201,584,1225,1540,2249,2761,3273,3674,18889,19145,20937,21193,24850,25289,29021,29385])),([5,7,25,98,304],(decodeHints [213,588,1237,1582,2261,2764,3285,3675,18896,19157,20949,21205,24896,25301]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_106 : K_106.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_107 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,25,132,464],(decodeHints [149,584,1173,1540,2197,2709,3221,3670,18834,19093,20885,21141,24850,25237,29333,30101])),([5,7,25,192,404],(decodeHints [201,584,1225,1540,2249,2776,3273,3674,18889,19145,20937,21193,24850,25289])),([5,7,31,41,98,272],(decodeHints [24737,38923])),([5,7,32,98,265],(decodeHints [85,586,1109,1621,2133,2645,3157,3628,14677,14933,18773,19025,21077,21845,26935,27221,28983,29269])),([5,7,32,156,521],(decodeHints [81,593,1105,1617,2129,2697,3153,3587,14673,14929,19025,19793,20817,21073,24909,26995,27217])),([5,7,32,521,866],(decodeHints [137,586,1161,1673,2185,2697,3209,3669,14729,14985,20873,21129,24887,25225,27273,28041])),([5,7,32,610,777],(decodeHints [85,586,1109,1621,2133,2645,3157,3721,14677,14933,18772,19025,21077,21845,27017,27221])),([5,7,41,98,122,272],(decodeHints [18498,32780]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_107 : K_107.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_108 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,41,98,256],(decodeHints [135,586,1159,1580,2183,2657,3207,3719,18743,19079,24887,25223,26965,27271,29063,29269])),([5,7,41,98,272,999],(decodeHints [40071])),([5,7,41,132,536],(decodeHints [97,609,1121,1539,2145,2657,3169,3719,14669,19041,19783,20833,21089,24903,25185,29009,29281])),([5,7,41,156,512],(decodeHints [97,609,1121,1539,2145,2695,3169,3681,14669,19041,19783,24929,25185,26961,27233,29025,29265])),([5,7,41,512,866],(decodeHints [135,586,1159,1580,2183,2695,3207,3681,18823,19079,20871,21127,24887,25223,29319,30087])),([5,7,41,610,768],(decodeHints [193,586,1217,1580,2241,2753,3265,3719,18871,19137,24887,25281,26965,27329])),([5,7,56,98,272,281],(decodeHints [28834])),([5,7,56,98,272,1014],(decodeHints [33967]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_108 : K_108.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_109 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,56,132,370],(decodeHints [3,515,1027,1673,2051,2563,3075,3665,14595,14851,19715,19971,20739,20995,24943,29043,29187])),([5,7,56,132,521],(decodeHints [81,593,1105,1673,2129,2641,3153,3587,14673,14929,19025,19793,20817,21073,24909,29043,29265])),([5,7,57,98,272],(decodeHints [213,588,1237,1582,2261,2658,3285,3675,18901,19157,24896,25301,29091,29397])),([5,7,64,512,777],(decodeHints [81,583,1105,1617,2129,2641,3153,3587,14673,14929,18769,19025,20817,21073,26891,27217,29265,30033])),([5,7,64,521,768],(decodeHints [190,583,1214,1726,2238,2750,3262,3665,14782,15038,20926,21182,24843,25278,26961,27326])),([5,7,73,272,768],(decodeHints [93,584,1117,1540,2141,2653,3165,3677,18706,19037,20829,21010,24850,25181,26973,27154,30033,30301])),([5,7,73,512,768],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,18699,19025,20817,21003,24843,25169,26961,27147,29265,30033])),([5,7,98,132,192,280,777],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_109 : K_109.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_110 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,98,132,201,280,768],[]),([5,7,98,132,201,536],(decodeHints [18517])),([5,7,98,132,216,272,777],[]),([5,7,98,156,192,272,777],[]),([5,7,98,156,464],(decodeHints [149,661,1173,1685,2197,2744,3221,3670,15761,16021,18833,20885,21141,25005,25237,26928])),([5,7,98,192,265],(decodeHints [85,584,1109,1621,2133,2645,3157,3628,14929,18773,19029,21841,22101,26973,27221,28946,29269])),([5,7,98,201,536],(decodeHints [108,620,1132,1740,2156,2604,3180,3773,14956,15690,18768,24906,25196,27046,27244])),([5,7,98,216,404],(decodeHints [44,556,1068,1580,2092,2750,3116,3669,15660,15916,18732,18988,20780,24946,27083,27180]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_110 : K_110.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_111 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,98,216,521],(decodeHints [85,597,1109,1739,2133,2750,3157,3628,14929,15701,18773,19029,24912,27018,27221])),([5,7,98,272,932],(decodeHints [46,588,1070,1582,2094,2606,3118,3797,14634,15917,18734,18990,20782,21038,27081])),([5,7,98,272,964],(decodeHints [46,584,1070,1582,2094,2606,3118,3797,18734,18990,20782,21038])),([5,7,98,304,900],(decodeHints [46,588,1070,1582,2094,2606,3118,3797,14638,15918,18734,18990,20782,27084,27182])),([5,7,98,404,800],(decodeHints [190,586,1214,1726,2238,2750,3262,3628,14773,16060,20926,21182,24887,25278,26924])),([5,7,98,436,768],(decodeHints [190,586,1214,1726,2238,2750,3262,3628,14782,16062,20926,24887,25278,27085,27326])),([5,7,98,468,768],(decodeHints [190,584,1214,1629,2238,2750,3262,3628,24850,25278,26884,27326])),([5,7,98,512,809],(decodeHints [85,586,1109,1633,2133,2645,3157,3628,14674,14929,18773,19029,20821,21077,29269,30037]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_111 : K_111.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_112 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,98,521,800],(decodeHints [190,586,1214,1739,2238,2750,3262,3669,14773,15038,20926,21182,24887,25278])),([5,7,98,544,777],(decodeHints [85,586,1109,1621,2133,2645,3157,3628,14677,14929,18773,19029,20821,26935,27221,29269])),([5,7,98,553,768],(decodeHints [190,586,1214,1633,2238,2750,3262,3669,14782,15038,24887,25278,27015,27326])),([5,7,98,704,777],(decodeHints [85,584,1109,1621,2133,2645,3157,3735,14929,18773,19029,21841,26973,27221,29269])),([5,7,122,132,192,272,777],[]),([5,7,122,132,201,272],(decodeHints [18527,36964])),([5,7,122,132,201,272,768],[]),([5,7,122,132,201,512],(decodeHints [18517,32784,39004]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_112 : K_112.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_113 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,122,132,304],(decodeHints [224,736,1248,1716,2272,2784,3296,3676,14811,19883,20181,20960,21216,25003,25312,28936,29408])),([5,7,122,164,272],(decodeHints [224,736,1248,1716,2272,2655,3296,3676,14811,19883,20960,25003,25312,28973,29408])),([5,7,122,192,521],(decodeHints [85,597,1109,1726,2133,2775,3157,3628,14929,15701,18773,19029,24971,29067,29269])),([5,7,122,201,272],(decodeHints [95,607,1119,1725,2143,2605,3167,3679,14941,18768,24927,25183,27221,29023,29275])),([5,7,122,201,512],(decodeHints [85,597,1109,1725,2133,2604,3157,3669,14929,15701,18768,24917,25173,26988,27221,29013,29292])),([5,7,132,192,265],(decodeHints [81,583,1105,1617,2129,2641,3153,3587,14673,14929,18769,19025,21073,21841,26891,27217,28939,29265])),([5,7,132,201,216,272],(decodeHints [14356,28873,35018])),([5,7,132,201,256],(decodeHints [81,583,1105,1617,2129,2563,3153,3665,14673,14929,21073,21841,24843,25169,26961,27217,29009,29195]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_113 : K_113.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_114 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,132,201,272,800],(decodeHints [26826,35005,40017])),([5,7,132,201,304,768],(decodeHints [26849,35005,40017])),([5,7,132,217,272],(decodeHints [201,584,1225,1737,2249,2564,3273,3674,14793,15049,21193,21961,24850,25289,26973,27337])),([5,7,132,370,960],(decodeHints [137,583,1161,1673,2185,2697,3209,3587,14725,16008,20873,21129,24843,25225,26883,27273])),([5,7,132,464,866],(decodeHints [4,584,1028,1540,2052,2564,3076,3733,14596,15876,18692,18948,20740,20996,27029,27140])),([5,7,132,512,969],(decodeHints [81,583,1105,1617,2129,2641,3153,3587,14673,14929,18769,19025,20817,21073,27217,27985,29265,30033])),([5,7,132,521,960],(decodeHints [137,583,1161,1673,2185,2697,3209,3665,14725,14985,20873,21129,24843,25225,27273,28041])),([5,7,132,704,777],(decodeHints [81,583,1105,1617,2129,2641,3153,3721,14673,14929,18769,19025,21073,21841,27017,27217]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_114 : K_114.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_115 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,132,713,768],(decodeHints [190,583,1214,1726,2238,2750,3262,3665,14782,15038,21182,21950,24843,25278,26961,27326])),([5,7,156,192,201,272],(decodeHints [37066])),([5,7,156,192,272,281],(decodeHints [28821])),([5,7,156,192,272,1014],(decodeHints [33967])),([5,7,192,370,900],(decodeHints [47,583,1071,1583,2095,2607,3119,3587,14639,14895,21039,21806,26883,27183])),([5,7,192,404,866],(decodeHints [4,584,1028,1540,2052,2564,3076,3628,14596,14852,20740,20996,27140,27908])),([5,7,192,521,900],(decodeHints [190,583,1214,1726,2238,2750,3262,3665,14782,15038,20926,21182,24843,25278])),([5,7,192,610,777],(decodeHints [85,584,1109,1621,2133,2645,3157,3748,14677,14933,19025,21845,26987,27221,29269]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_115 : K_115.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_116 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,192,644,777],(decodeHints [81,583,1105,1617,2129,2641,3153,3587,14673,14929,18769,19025,20817,26891,27217,29265])),([5,7,196,272,866],(decodeHints [4,584,1028,1540,2052,2564,3076,3785,18692,18948,20740,20996])),([5,7,196,370,768],(decodeHints [190,583,1214,1640,2238,2750,3262,3587,24843,25278,26926,27326])),([5,7,201,272,900],(decodeHints [189,584,1213,1725,2237,2749,3261,3677,18877,19133,20925,21181,25277,26973,30033])),([5,7,201,404,768],(decodeHints [225,584,1249,1540,2273,2669,3297,3809,19169,20829,24850,25313,26973,27361,30301])),([5,7,201,512,900],(decodeHints [189,583,1213,1725,2237,2749,3261,3665,18877,19133,20925,21181,24843,25277,29373,30141])),([5,7,201,644,768],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,18874,19025,20817,24843,25169,26961,27147,29265])),([5,8,98,132,192,272,775],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_116 : K_116.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_117 : List (List ℕ × List (ℕ × ℕ)) := [([5,8,98,132,192,279,768],[]),([5,9,24,31,64,272],(decodeHints [24717,34887,36935])),([5,9,24,31,132,464],(decodeHints [26769,28815,34887])),([5,9,24,32,39,370],(decodeHints [14498])),([5,9,24,32,64,279],(decodeHints [14366,18526,20573,24609,26658])),([5,9,24,32,71,272],(decodeHints [14549,18531,20573])),([5,9,24,32,98,279],(decodeHints [14400])),([5,9,24,32,98,311],(decodeHints [14400]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_117 : K_117.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_118 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,32,98,375],(decodeHints [14400])),([5,9,24,32,98,744],(decodeHints [14412,32853,34890])),([5,9,24,32,103,272],(decodeHints [14549,37072])),([5,9,24,32,103,279],(decodeHints [14549])),([5,9,24,32,103,281],(decodeHints [18514,24782,37072,38983])),([5,9,24,32,103,304],(decodeHints [14549,28880,37072])),([5,9,24,32,103,370],(decodeHints [14549])),([5,9,24,32,103,375],(decodeHints [14549,25631]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_118 : K_118.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_119 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,32,103,751],(decodeHints [14427,34827])),([5,9,24,32,107,279],(decodeHints [14400,18528,20573,38983])),([5,9,24,32,122,279],(decodeHints [14401,18526,20575,38983])),([5,9,24,32,127,272],(decodeHints [20552,34887,37072,38983])),([5,9,24,32,132,375],(decodeHints [14373])),([5,9,24,32,192,375],(decodeHints [14373])),([5,9,24,32,272,375],(decodeHints [14366,27678])),([5,9,24,32,272,896],(decodeHints [20552,26806,28868]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_119 : K_119.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_120 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,32,272,920],(decodeHints [14409,28868,32943])),([5,9,24,32,279,370],(decodeHints [14400])),([5,9,24,32,279,375],(decodeHints [14437,25631,27678])),([5,9,24,32,279,644],(decodeHints [14400,18526,20573])),([5,9,24,32,279,900],(decodeHints [14400,18526,20573])),([5,9,24,32,279,925],(decodeHints [14400])),([5,9,24,32,370,375],(decodeHints [14400,27678])),([5,9,24,32,370,1016],(decodeHints [14412,32893]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_120 : K_120.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_121 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,32,375],(decodeHints [14623,14878,25159,25887,27207,27934])),([5,9,24,32,375,512],(decodeHints [14366,32879,34926])),([5,9,24,32,375,768],(decodeHints [14366])),([5,9,24,32,640],(decodeHints [71,515,1095,1547,2119,2631,3143,3655,18769,19015,20807,21073,24913,25159,26951,27217,28999,29255])),([5,9,24,39,98,279],(decodeHints [14355,26646])),([5,9,24,41,98,279],(decodeHints [14400,20544,24672,32853])),([5,9,24,41,103,272],(decodeHints [14366,20510,24656,32850,37072])),([5,9,24,56,98,279],(decodeHints [14401,18497,26719,34890]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_121 : K_121.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_122 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,56,103,272],(decodeHints [14549,18645,26696,34897,37072])),([5,9,24,64,71,272],(decodeHints [14537])),([5,9,24,64,98,279],(decodeHints [14354,18576,20625])),([5,9,24,64,132,279],(decodeHints [14354,18453,20502])),([5,9,24,64,192,279],(decodeHints [14354,18588,20637,24678,26725])),([5,9,24,64,272,279],(decodeHints [14354,18453,20633,27666])),([5,9,24,64,272,1016],(decodeHints [14408,18552,20683,32943])),([5,9,24,64,279],(decodeHints [14611,14866,25159,25875,27207,27922]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_122 : K_122.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_123 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,64,279,512],(decodeHints [14354,18453,20502,32879,34926])),([5,9,24,64,279,768],(decodeHints [14354,18453,20502])),([5,9,24,71,98,272],(decodeHints [14549,26719])),([5,9,24,71,132,272],(decodeHints [14537,26725])),([5,9,24,71,192,272],(decodeHints [14537,26725])),([5,9,24,71,272],(decodeHints [14793,14866,19024,19913,27217,27922])),([5,9,24,71,272,512],(decodeHints [14537,32886,34926])),([5,9,24,71,272,768],(decodeHints [14560,26705,40017]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_123 : K_123.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_124 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,98,132,279,960],[]),([5,9,24,98,132,464,775],[]),([5,9,24,98,164,279],(decodeHints [14400])),([5,9,24,98,192,279],(decodeHints [14354,24720,26769])),([5,9,24,98,192,279,900],[]),([5,9,24,98,192,404,775],[]),([5,9,24,98,192,471],(decodeHints [14354])),([5,9,24,98,192,744],(decodeHints [14408,24720,26769,32850,34888]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_124 : K_124.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_125 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,98,196,272,775],[]),([5,9,24,98,196,279],(decodeHints [14354])),([5,9,24,98,196,279,768],[]),([5,9,24,98,199,279],(decodeHints [14401,20645])),([5,9,24,98,201,279],(decodeHints [14354,18453,24720,26642,32853])),([5,9,24,98,216,279],(decodeHints [14355,20502,24595,26769,34890])),([5,9,24,98,279,304],(decodeHints [14400,20645])),([5,9,24,98,279,311],(decodeHints [14440]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_125 : K_125.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_126 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,98,279,464],(decodeHints [14354,20622])),([5,9,24,98,279,471],(decodeHints [14449])),([5,9,24,98,279,544],(decodeHints [14400,32882,34929])),([5,9,24,98,279,704],(decodeHints [14354,32912,34961])),([5,9,24,98,279,800],(decodeHints [14400])),([5,9,24,98,279,831],(decodeHints [14354])),([5,9,24,98,279,960],(decodeHints [14354])),([5,9,24,98,279,991],(decodeHints [14400]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_126 : K_126.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_127 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,103,192,279],(decodeHints [14355,24597,26777])),([5,9,24,103,199,272],(decodeHints [14560,20498,26650])),([5,9,24,103,272,304],(decodeHints [14366,27856,39120])),([5,9,24,103,272,544],(decodeHints [14549,32886,34926])),([5,9,24,103,272,800],(decodeHints [14560,26805])),([5,9,24,103,272,991],(decodeHints [14549])),([5,9,24,103,304],(decodeHints [208,720,1232,1744,2256,2756,3280,3611,14800,15056,19152,19920,20944,21200,24868,25296,27344,28112])),([5,9,24,107,192,279],(decodeHints [14354,24597,26769]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_127 : K_127.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_128 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,122,192,279],(decodeHints [14355,24720,26646])),([5,9,24,128,192,279],(decodeHints [14354,24597,26646,36887])),([5,9,24,128,199,272],(decodeHints [14537,37060])),([5,9,24,128,272,800],(decodeHints [20553,26805,28880])),([5,9,24,128,544],(decodeHints [71,515,1095,1547,2119,2631,3143,3655,18769,19015,20807,21073,24913,25159,26951,27217,28999,29255])),([5,9,24,132,192,279],(decodeHints [14354,24597,26646,36887])),([5,9,24,132,192,279,866],[]),([5,9,24,132,192,370,775],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_128 : K_128.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_129 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,132,192,471],(decodeHints [14354])),([5,9,24,132,192,744],(decodeHints [14408,24696,26752,32849,34887])),([5,9,24,132,196,279],(decodeHints [14354,24597,26646])),([5,9,24,132,199,279],(decodeHints [14401])),([5,9,24,132,201,279],(decodeHints [14354,18576,24597,26642,32789,36887])),([5,9,24,132,216,279],(decodeHints [14355,20625,24595,26646,34838,36887])),([5,9,24,132,279,464],(decodeHints [14354,20625])),([5,9,24,132,279,471],(decodeHints [14429]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_129 : K_129.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_130 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,132,279,544],(decodeHints [14400,32862,34909])),([5,9,24,132,279,800],(decodeHints [14400])),([5,9,24,132,279,831],(decodeHints [14354,28707])),([5,9,24,132,464,471],(decodeHints [14354])),([5,9,24,132,464,1016],(decodeHints [14408,32893])),([5,9,24,135,192,279],(decodeHints [14537,24717,26827,36887])),([5,9,24,135,464],(decodeHints [143,655,1167,1679,2191,2718,3215,3619,14735,14991,19087,19855,20879,21135,24855,25231,27279,28047])),([5,9,24,141,192,279],(decodeHints [14354,24720,26646,36887]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_130 : K_130.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_131 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,156,192,279],(decodeHints [14355,24597,26769,36887])),([5,9,24,160,272,768],(decodeHints [20552,26807,28869])),([5,9,24,160,512],(decodeHints [71,515,1095,1547,2119,2631,3143,3655,18769,19015,20807,21073,24913,25159,26951,27217,28999,29255])),([5,9,24,164,192,279],(decodeHints [14373,24614,26663])),([5,9,24,164,279,512],(decodeHints [14398,32879,34926])),([5,9,24,164,279,768],(decodeHints [14398])),([5,9,24,192,279,370],(decodeHints [14354,18576,20502])),([5,9,24,192,279,375],(decodeHints [14446,18453,20502]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_131 : K_131.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_132 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,192,279,404],(decodeHints [14354,18453,20625,38935])),([5,9,24,192,279,407],(decodeHints [14429,18573,20622,25619,27666,38935])),([5,9,24,192,279,610],(decodeHints [14354,18576,20625])),([5,9,24,192,279,644],(decodeHints [14354,18453,20502])),([5,9,24,192,279,866],(decodeHints [14354,18576,20625])),([5,9,24,192,279,891],(decodeHints [14354,18453,20502])),([5,9,24,192,279,900],(decodeHints [14354,18453,20502])),([5,9,24,192,279,925],(decodeHints [14354,18576,20625]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_132 : K_132.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_133 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,24,192,407],(decodeHints [23,535,1047,1559,2071,2595,3095,3742,14611,14866,18711,18967,20759,21015,25111,25875,27159,27922])),([5,9,31,98,216,272],(decodeHints [34890])),([5,9,31,132,216,272],(decodeHints [20553,34838,37068,38983])),([5,9,31,135,192,272],(decodeHints [24717])),([5,9,32,56,98,279],(decodeHints [14499,18496])),([5,9,32,56,103,272],(decodeHints [14368,18645])),([5,9,32,98,122,279],(decodeHints [14348,18432,24640])),([5,9,32,98,263],(decodeHints [55,556,1079,1591,2103,2615,3127,3658,14647,14903,18743,18999,21047,21815,26965,27191,29009,29239]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_133 : K_133.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_134 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,32,98,279,999],(decodeHints [39991])),([5,9,32,98,728],(decodeHints [74,556,1098,1610,2122,2634,3146,3639,14666,14922,18762,19018,21066,21834,26965,27210,29258,30023])),([5,9,32,103,122,272],(decodeHints [14402,35024])),([5,9,32,103,127,272],(decodeHints [19663,35024])),([5,9,32,103,256],(decodeHints [11,515,1035,1547,2059,2631,3083,3595,14603,14859,21003,21771,24913,25099,26891,27147,28939,29265])),([5,9,32,103,272,999],(decodeHints [26832,39947])),([5,9,32,128,536],(decodeHints [71,515,1095,1607,2119,2631,3143,3595,14663,14919,18759,19015,20807,21063,26961,27207,29009,29255])),([5,9,32,152,512],(decodeHints [71,515,1095,1607,2119,2571,3143,3655,14663,14919,20817,21063,24913,25159,26951,27207,28999,29265]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_134 : K_134.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_135 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,32,512,871],(decodeHints [11,515,1035,1547,2059,2571,3083,3655,14603,14859,18699,18955,20747,21003,27147,27915,29195,29963])),([5,9,32,615,768],(decodeHints [183,515,1207,1719,2231,2743,3255,3595,14775,15031,21175,21943,24913,25271,26891,27319])),([5,9,39,56,98,272],(decodeHints [18645])),([5,9,56,98,103,272],(decodeHints [14549])),([5,9,56,98,132,279],(decodeHints [14400])),([5,9,56,98,192,279],(decodeHints [14406,24681,29789])),([5,9,56,98,272,279],(decodeHints [14400])),([5,9,56,98,272,1016],(decodeHints [14412,32943]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_135 : K_135.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_136 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,56,98,279],(decodeHints [14657,14912,18692,19037,21087,25162,25921,27208])),([5,9,56,98,279,512],(decodeHints [14400,32882,34929])),([5,9,56,98,279,768],(decodeHints [14400])),([5,9,56,98,704],(decodeHints [72,556,1096,1554,2120,2632,3144,3656,18773,19016,21077,24917,25160,26952,27221,29256,30023])),([5,9,56,103,132,272],(decodeHints [14560])),([5,9,56,103,192,272],(decodeHints [14560])),([5,9,56,103,272],(decodeHints [14805,14878,19016,19925,21064,27217])),([5,9,56,103,272,512],(decodeHints [14549,32880,34926]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_136 : K_136.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_137 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,56,103,272,768],(decodeHints [14560,26844,32880,40017])),([5,9,56,128,512],(decodeHints [71,515,1095,1547,2119,2631,3143,3655,18769,19015,20807,21073,24913,25159,26951,27217,28999,29255])),([5,9,64,512,775],(decodeHints [11,515,1035,1547,2059,2571,3083,3655,14603,14859,18699,18955,20747,21003,26961,27147,29195,29963])),([5,9,64,519,768],(decodeHints [183,515,1207,1719,2231,2743,3255,3595,14775,15031,20919,21175,24913,25271,26891,27319])),([5,9,71,272,768],(decodeHints [18,516,1042,1608,2066,2578,3090,3602,18781,18962,20754,21085,24925,25106,26898,27229,29963,30226])),([5,9,71,512,768],(decodeHints [11,515,1035,1607,2059,2571,3083,3595,18769,18955,20747,21073,24913,25099,26891,27217,29195,29963])),([5,9,98,122,192,279],(decodeHints [18450,24720])),([5,9,98,132,192,280,775],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_137 : K_137.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_138 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,98,132,216,272,775],[]),([5,9,98,132,216,279,768],[]),([5,9,98,156,192,272,775],[]),([5,9,98,192,216,279],(decodeHints [21605,24594,28817])),([5,9,98,192,263],(decodeHints [18,556,1042,1554,2066,2578,3090,3656,14610,14866,18706,18962,21771,22034,26961,29013,29202])),([5,9,98,192,279,775],(decodeHints [21597,39954])),([5,9,98,192,279,999],(decodeHints [18488,39954])),([5,9,98,192,568],(decodeHints [72,556,1096,1608,2120,2632,3144,3602,14664,14920,18760,19016,21064,21831,26965,29013,29256]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_138 : K_138.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_139 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,98,199,216,272],(decodeHints [24800])),([5,9,98,199,272,775],[]),([5,9,98,199,279,768],[]),([5,9,98,216,279],(decodeHints [145,558,1169,1681,2193,2618,3217,3729,14737,14993,18962,21861,25162,26902,29258])),([5,9,98,216,544],(decodeHints [74,556,1098,1610,2122,2615,3146,3658,14666,14922,21066,21831,24917,25162,26954,29002,29269])),([5,9,98,519,800],(decodeHints [186,556,1210,1739,2234,2746,3258,3639,14778,15034,20919,21173,24917,25274])),([5,9,98,544,775],(decodeHints [55,556,1079,1591,2103,2615,3127,3658,14647,14903,18743,18999,20791,26961,27191,29239])),([5,9,98,704,775],(decodeHints [18,556,1042,1554,2066,2578,3090,3731,14610,14866,18706,18962,21771,26904,29202]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_139 : K_139.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_140 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,103,192,272,775],[]),([5,9,103,192,279,768],[]),([5,9,103,199,272,768],(decodeHints [21522,40017])),([5,9,103,272,800],(decodeHints [181,517,1205,1609,2229,2741,3253,3610,18869,19125,20917,21173,24933,25269,26910,29963])),([5,9,103,304,768],(decodeHints [220,517,1244,1609,2268,2588,3292,3804,18789,19164,20766,24933,25308,26910,27356,30238])),([5,9,103,512,800],(decodeHints [181,515,1205,1607,2229,2741,3253,3610,18869,19125,20917,21173,24913,25269,29365,30133])),([5,9,103,544,768],(decodeHints [11,515,1035,1607,2059,2571,3083,3595,18769,18955,20747,24913,25099,26891,27217,29195])),([5,9,122,132,192,272,775],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_140 : K_140.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_141 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,132,156,192,279],(decodeHints [14486,18450,24597,28694])),([5,9,132,192,216,279],(decodeHints [21526,24594,28694,34839])),([5,9,132,192,263],(decodeHints [11,515,1035,1547,2059,2571,3083,3655,14603,14859,18699,18955,21003,21771,26961,27147,29009,29195])),([5,9,132,192,279,999],(decodeHints [18453,26647,39947])),([5,9,132,192,568],(decodeHints [71,515,1095,1607,2119,2631,3143,3595,14663,14919,18759,19015,21831,22087,26961,27207,29009,29255])),([5,9,132,199,216,272],(decodeHints [35020])),([5,9,132,216,279],(decodeHints [22,534,1046,1558,2070,2574,3094,3712,14614,14870,18707,18962,21014,21782,25110,25875,27022,27158])),([5,9,132,519,960],(decodeHints [130,515,1154,1666,2178,2690,3202,3595,14722,14978,20866,21122,24913,25218,27266,28034]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_141 : K_141.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_142 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,132,704,775],(decodeHints [11,515,1035,1547,2059,2571,3083,3714,14603,14859,18699,18955,21003,21771,27010,27147])),([5,9,135,192,256],(decodeHints [129,515,1153,1607,2177,2594,3201,3713,18769,19073,24913,25217,26891,27265,29057,29195])),([5,9,135,192,272,800],(decodeHints [40065])),([5,9,135,192,304,768],(decodeHints [40065])),([5,9,135,216,272],(decodeHints [203,715,1227,1694,2251,2595,3275,3722,15051,15817,18889,19147,24975,25291,26903,27339])),([5,9,135,512,960],(decodeHints [129,515,1153,1665,2177,2689,3201,3595,18817,19073,20865,21121,24913,25217,29313,30081])),([5,9,135,704,768],(decodeHints [193,515,1217,1607,2241,2753,3265,3713,18881,19137,24913,25281,26891,27329])),([5,9,156,192,199,272],(decodeHints [37064]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_142 : K_142.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_143 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,156,192,272,279],(decodeHints [28817])),([5,9,156,192,272,1016],(decodeHints [32943])),([5,9,192,512,903],(decodeHints [11,515,1035,1547,2059,2571,3083,3713,14603,14859,18699,18955,20747,21003,29195,29963])),([5,9,192,647,768],(decodeHints [183,515,1207,1570,2231,2743,3255,3595,14775,15031,24913,25271,27009,27319])),([5,15,24,98,132,192,256],[]),([5,15,24,98,132,272,960],[]),([5,15,24,98,132,464,768],[]),([5,15,24,98,192,272,900],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_143 : K_143.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_144 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,24,98,192,404,768],[]),([5,15,24,98,196,272,768],[]),([5,15,24,132,192,272,866],[]),([5,15,24,132,192,370,768],[]),([5,15,98,132,192,280,768],[]),([5,15,98,132,216,272,768],[]),([5,15,98,156,192,272,768],[]),([5,15,122,132,192,272,768],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_144 : K_144.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_145 : List (List ℕ × List (ℕ × ℕ)) := [([5,24,31,41,98,272],(decodeHints [24783,32842,34901,38983])),([5,24,32,41,98,279],(decodeHints [14499,18496])),([5,24,32,41,103,272],(decodeHints [14368,18645])),([5,24,32,98,107,279],(decodeHints [14340,18432,24640])),([5,24,32,98,272,969],(decodeHints [14408,18603,24661,26796,28743])),([5,24,32,98,276],(decodeHints [44,567,1068,1580,2092,2604,3116,3669,14636,14892,18732,18988,21036,21804,26954,27180,29002,29228])),([5,24,32,98,279,1014],(decodeHints [39980])),([5,24,32,98,713],(decodeHints [85,567,1109,1621,2133,2645,3157,3628,14677,14933,18773,19029,21077,21845,26954,27221,29269,30033]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_145 : K_145.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_146 : List (List ℕ × List (ℕ × ℕ)) := [([5,24,32,102,272],(decodeHints [175,699,1199,1711,2223,2735,3247,3673,14767,15023,18863,19119,21167,21935,26960,27311,29008,29359])),([5,24,32,103,272,281],(decodeHints [25701])),([5,24,32,103,272,777],(decodeHints [14448,24657,26844])),([5,24,32,103,272,1014],(decodeHints [26832,38063])),([5,24,32,128,272,777],(decodeHints [14429,18533,24657,26818,28878])),([5,24,32,128,521],(decodeHints [81,523,1105,1617,2129,2641,3153,3587,14673,14929,18769,19025,20817,21073,26951,27217,28999,29265])),([5,24,32,132,498],(decodeHints [2,523,1026,1538,2050,2589,3074,3647,14594,14850,18690,18946,20738,20994,27138,27906])),([5,24,32,137,272,768],(decodeHints [14429,24759,26821]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_146 : K_146.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_147 : List (List ℕ × List (ℕ × ℕ)) := [([5,24,32,137,512],(decodeHints [81,523,1105,1617,2129,2563,3153,3665,14673,14929,20807,21073,24903,25169,26961,27217,29009,29255])),([5,24,32,226,404],(decodeHints [43,567,1067,1579,2091,2623,3115,3613,14635,14891,18731,18987,21035,21803,26882,27179])),([5,24,36,98,272],(decodeHints [175,699,1199,1553,2223,2621,3247,3673,14767,15023,18863,19119,26922,27311,28929,29359])),([5,24,39,41,98,272],(decodeHints [18645,24791])),([5,24,41,98,103,272],(decodeHints [14549,18498])),([5,24,41,98,132,279],(decodeHints [14400])),([5,24,41,98,192,279],(decodeHints [14406,24680,29790])),([5,24,41,98,272,279],(decodeHints [14400,25664]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_147 : K_147.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_148 : List (List ℕ × List (ℕ × ℕ)) := [([5,24,41,98,272,960],(decodeHints [24761,28743])),([5,24,41,98,272,1016],(decodeHints [14412])),([5,24,41,98,279],(decodeHints [14656,14913,18700,19038,21088,25173,25920,27218])),([5,24,41,98,279,512],(decodeHints [14400,32881,34930])),([5,24,41,98,279,768],(decodeHints [14400])),([5,24,41,98,704],(decodeHints [82,567,1106,1555,2130,2642,3154,3666,18762,19026,21066,24906,25170,26962,27210,29266,30033])),([5,24,41,103,132,272],(decodeHints [14560,24677])),([5,24,41,103,192,272],(decodeHints [14560,24677]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_148 : K_148.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_149 : List (List ℕ × List (ℕ × ℕ)) := [([5,24,41,103,272],(decodeHints [14622,15061,21072,21973,25169,25886])),([5,24,41,103,272,512],(decodeHints [14549,32878,34934])),([5,24,41,103,272,768],(decodeHints [14560,24657,40017])),([5,24,41,128,272,768],(decodeHints [18505,24759,28881])),([5,24,41,128,512],(decodeHints [81,523,1105,1539,2129,2641,3153,3665,18759,19025,20817,21063,24903,25169,26961,27207,29009,29265])),([5,24,98,107,192,279],(decodeHints [18450,24721])),([5,24,98,132,192,272,783],[]),([5,24,98,132,201,272,775],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_149 : K_149.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_150 : List (List ℕ × List (ℕ × ℕ)) := [([5,24,98,132,201,279,768],[]),([5,24,98,164,464],(decodeHints [174,699,1198,1597,2222,2577,3246,3652,14766,15022,18862,19118,26881,27310])),([5,24,98,192,201,279],(decodeHints [21606,24594,28816])),([5,24,98,192,272,809],(decodeHints [18535,24658,28880])),([5,24,98,192,279,1014],(decodeHints [18478,39955])),([5,24,98,192,436],(decodeHints [42,567,1066,1597,2090,2602,3114,3601,14634,14890,18730,18986,20778,21034,29226,29994])),([5,24,98,192,553],(decodeHints [82,567,1106,1618,2130,2642,3154,3603,14674,14930,18770,19026,21074,21841,26954,29002,29266])),([5,24,98,196,272,519],(decodeHints [25618]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_150 : K_150.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_151 : List (List ℕ × List (ℕ × ℕ)) := [([5,24,98,199,201,272],(decodeHints [14431,24800])),([5,24,98,201,272,800],(decodeHints [14555,24757])),([5,24,98,201,279],(decodeHints [144,568,1168,1680,2192,2609,3216,3728,14736,14992,18963,21862,25173,26901,29269])),([5,24,98,201,544],(decodeHints [85,567,1109,1621,2133,2604,3157,3669,14677,14933,21077,21841,24906,25173,26965,29013,29258])),([5,24,132,141,192,279],(decodeHints [14486,18450,24598,28693])),([5,24,132,192,201,279],(decodeHints [21525,24594,28693,34839])),([5,24,132,192,272,809],(decodeHints [14509,18610,24657,26803,28846])),([5,24,132,192,274],(decodeHints [3,523,1027,1695,2051,2627,3075,3665,14595,14851,18691,18947,26930,27139,29052,29187]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_151 : K_151.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_152 : List (List ℕ × List (ℕ × ℕ)) := [([5,24,132,192,279,1014],(decodeHints [18454,26647,39939])),([5,24,132,192,553],(decodeHints [81,523,1105,1617,2129,2641,3153,3587,14673,14929,18769,19025,21841,22097,26951,27217,28999,29265])),([5,24,132,194,272],(decodeHints [175,699,1199,1565,2223,2623,3247,3673,14767,15023,18863,19119,26923,27311,28930,29359])),([5,24,132,201,279],(decodeHints [21,533,1045,1557,2069,2566,3093,3704,14613,14869,18706,18963,21013,21781,25109,25874,27021,27157])),([5,24,132,226,304],(decodeHints [172,699,1196,1565,2220,2623,3244,3609,14764,15020,18860,19116,26923,27308])),([5,24,134,192,272],(decodeHints [175,699,1199,1692,2223,2593,3247,3673,14767,15023,18863,19119,26887,27311,29049,29359])),([5,24,135,201,272],(decodeHints [141,653,1165,1656,2189,2566,3213,3725,14733,14989,18706,19145,25169,25949,26901,27277,29069,29205])),([5,24,164,192,370],(decodeHints [1,523,1025,1553,2049,2561,3073,3645,14593,14849,18689,18945,20737,22017,28970,29185]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_152 : K_152.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_153 : List (List ℕ × List (ℕ × ℕ)) := [([5,24,164,226,272],(decodeHints [175,699,1199,1553,2223,2621,3247,3673,14767,15023,18863,19119,26922,27311,28929,29359])),([5,25,32,98,279],(decodeHints [64,558,1088,1600,2112,2624,3136,3660,14656,14912,18752,19008,21056,21824,26984,27200,29029,29248])),([5,25,32,103,272],(decodeHints [213,517,1237,1749,2261,2633,3285,3675,14805,15061,21205,21973,26910,27349,28958,29397])),([5,25,98,192,279],(decodeHints [18,559,1042,1554,2066,2578,3090,3656,14610,14866,18706,18962,21778,22034,26990,29041,29202])),([5,25,132,192,279],(decodeHints [18,516,1042,1554,2066,2578,3090,3656,14610,14866,18706,18962,21010,21778,26973,27154,29021,29202])),([5,25,135,192,272],(decodeHints [201,516,1225,1608,2249,2595,3273,3674,18889,19145,26898,27337,29071,29385])),([5,26,132,192,272],(decodeHints [171,692,1195,1695,2219,2627,3243,3599,14763,15019,18859,19115,26930,27307,29052,29355])),([5,28,32,98,272],(decodeHints [173,696,1197,1709,2221,2733,3245,3643,14765,15021,18861,19117,21165,21933,26931,27309,28979,29357]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_153 : K_153.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_154 : List (List ℕ × List (ℕ × ℕ)) := [([5,32,98,156,464],(decodeHints [173,685,1197,1709,2221,2744,3245,3643,15021,15789,18861,19117,20909,21165,24883,25261,26928,27309])),([5,32,98,201,536],(decodeHints [74,586,1098,1610,2122,2604,3146,3639,14922,15690,18762,19018,21066,21831,24917,25162,26965,27210])),([5,32,98,216,404],(decodeHints [44,556,1068,1580,2092,2615,3116,3669,14892,15660,18732,18988,20780,21036,24906,25132,26954,27180])),([5,32,98,216,521],(decodeHints [85,597,1109,1621,2133,2615,3157,3628,14933,15701,18773,19029,21077,21841,24906,25173,26954,27221])),([5,32,98,279,900],(decodeHints [46,558,1070,1582,2094,2606,3118,3648,14894,15662,18734,18990,21038,21806,24896,25134,26944,27182])),([5,32,98,404,775],(decodeHints [55,567,1079,1591,2103,2615,3127,3628,14903,15671,18743,18999,20791,21047,24876,25143,27191,27959])),([5,32,98,519,777],(decodeHints [85,597,1109,1621,2133,2645,3157,3639,14933,15701,18773,19029,20817,21077,24887,25173,26935,27221])),([5,32,98,521,775],(decodeHints [55,567,1079,1591,2103,2615,3127,3669,14903,15671,18743,18999,20791,21047,24917,25143,26961,27191]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_154 : K_154.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_155 : List (List ℕ × List (ℕ × ℕ)) := [([5,32,103,512,777],(decodeHints [81,593,1105,1607,2129,2641,3153,3587,14929,15697,18769,19025,20817,21073,24843,25169,29265,30033])),([5,32,103,521,768],(decodeHints [190,702,1214,1607,2238,2750,3262,3665,15038,15806,18878,19134,24913,25278,26891,27326])),([5,32,122,192,404],(decodeHints [41,553,1065,1590,2089,2601,3113,3594,14889,15657,18729,18985,20777,21033,24832,25129,29225,29993])),([5,32,132,250,272],(decodeHints [171,683,1195,1565,2219,2623,3243,3599,14763,15019,19115,19883,24834,25259,26923,27307])),([5,32,135,201,272,768],(decodeHints [21687,40017])),([5,32,156,192,370],(decodeHints [0,512,1024,1546,2048,2560,3072,3638,14592,14848,18688,18944,20736,22016,25088,25856,28969,29184])),([5,32,156,226,272],(decodeHints [173,685,1197,1565,2221,2623,3245,3643,14765,15021,19117,19885,24834,25261,28930,29357])),([5,41,98,192,536],(decodeHints [74,531,1098,1610,2122,2634,3146,3639,14922,18762,19018,21066,21831,26974,27210,29010,29258]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_155 : K_155.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_156 : List (List ℕ × List (ℕ × ℕ)) := [([5,41,98,216,512],(decodeHints [74,531,1098,1610,2122,2615,3146,3658,14922,21066,21831,24914,25162,26954,27210,29002,29266])),([5,41,98,512,775],(decodeHints [55,556,1079,1633,2103,2615,3127,3658,18743,18999,20791,21047,27015,27191,29239,30007])),([5,41,98,519,768],(decodeHints [186,556,1210,1633,2234,2746,3258,3639,20919,21178,24917,25274,27015,27322])),([5,41,103,272,768],(decodeHints [30,517,1054,1609,2078,2590,3102,3614,18789,18974,20766,21093,24933,25118,26910,27237,29963,30238])),([5,41,103,512,768],(decodeHints [11,515,1035,1607,2059,2571,3083,3595,18769,18955,20747,21073,24913,25099,26891,27217,29195,29963])),([5,41,132,192,536],(decodeHints [71,515,1095,1607,2119,2631,3143,3595,14663,14919,18759,19015,21831,22087,26961,27207,29009,29255])),([5,56,98,132,464],(decodeHints [174,530,1198,1629,2222,2770,3246,3652,18862,19118,20910,21166,26884,27310])),([5,56,98,192,404],(decodeHints [44,530,1068,1629,2092,2604,3116,3669,18732,18988,20780,21036,26884,27180,29228,29996]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_156 : K_156.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_157 : List (List ℕ × List (ℕ × ℕ)) := [([5,56,98,192,521],(decodeHints [85,530,1109,1621,2133,2645,3157,3628,14933,18773,19029,21077,21841,26973,27221,29000,29269])),([5,56,98,201,512],(decodeHints [85,530,1109,1621,2133,2604,3157,3669,14933,21077,21841,24904,25173,26965,27221,29013,29256])),([5,56,132,192,370],(decodeHints [3,523,1027,1539,2051,2563,3075,3665,14595,14851,18691,18947,20739,22019,26951,27139,28999,29187])),([5,56,132,192,521],(decodeHints [81,523,1105,1617,2129,2641,3153,3587,14673,14929,18769,19025,21841,22097,26951,27217,28999,29265])),([5,56,132,226,272],(decodeHints [175,530,1199,1565,2223,2623,3247,3673,14767,15023,26923,27311,28930,29359])),([5,98,132,216,304],(decodeHints [172,706,1196,1640,2220,2624,3244,3609,14764,15020,18860,19116,26926,27308])),([5,98,132,279,800],(decodeHints [177,689,1201,1640,2225,2737,3249,3648,14769,15025,19116,19888,24896,26926,27313])),([5,98,132,279,960],(decodeHints [151,663,1175,1687,2199,2711,3223,3602,14743,14999,21138,21910,26898,27287]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_157 : K_157.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_158 : List (List ℕ × List (ℕ × ℕ)) := [([5,98,132,304,775],(decodeHints [64,576,1088,1640,2112,2624,3136,3759,14656,14912,18752,20800,21056,25152,25920])),([5,98,132,464,775],(decodeHints [18,605,1042,1554,2066,2578,3090,3733,14610,14866,20754,21010,27154,27922])),([5,98,156,192,304],(decodeHints [172,706,1196,1720,2220,2732,3244,3609,14764,15020,18860,19116,20908,22188,28979,29356])),([5,98,164,216,272],(decodeHints [175,573,1199,1553,2223,2624,3247,3673,18863,19119,24833,25263,26922,27311])),([5,98,164,272,775],(decodeHints [64,576,1088,1640,2112,2624,3136,3759,14654,18752,19008,20800,21056,25152,25918])),([5,98,164,279,768],(decodeHints [177,689,1201,1640,2225,2737,3249,3648,14769,19121,19889,24896,25265,26926,27313])),([5,98,188,192,272],(decodeHints [173,573,1197,1553,2221,2733,3245,3643,18861,19117,20909,22189,24833,25261,28970,29357])),([5,98,192,279,900],(decodeHints [47,605,1071,1583,2095,2607,3119,3602,14639,15918,20783,21039,24836,25135,26898,27183]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_158 : K_158.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_159 : List (List ℕ × List (ℕ × ℕ)) := [([5,98,192,404,775],(decodeHints [18,605,1042,1554,2066,2578,3090,3628,14610,15890,18706,18962,20754,21010,26924,27154])),([5,98,192,519,777],(decodeHints [85,597,1109,1621,2133,2645,3157,3602,15697,15957,18769,20821,21077,24925,25173,26898,27221])),([5,98,192,521,775],(decodeHints [18,530,1042,1554,2066,2578,3090,3669,15627,15890,18706,18962,20754,21010,24913,26965,27154])),([5,98,196,272,775],(decodeHints [18,605,1042,1640,2066,2578,3090,3759,18706,18962,20754,21010])),([5,98,196,279,768],(decodeHints [177,605,1201,1640,2225,2737,3249,3602,24836,25265,26926,27313])),([5,122,132,192,304],(decodeHints [171,692,1195,1707,2219,2731,3243,3599,14763,15019,18859,19115,20907,22187,26888,27307,28936,29355])),([5,122,164,192,272],(decodeHints [171,573,1195,1553,2219,2731,3243,3599,18859,19115,20907,22187,26922,27307,28970,29355])),([5,132,192,279,866],(decodeHints [4,516,1028,1540,2052,2564,3076,3602,14596,14852,18948,19716,20740,20996,24850,25092,27140,27908]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_159 : K_159.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_160 : List (List ℕ × List (ℕ × ℕ)) := [([5,132,192,370,775],(decodeHints [11,523,1035,1547,2059,2571,3083,3587,14603,14859,18699,18955,21003,21771,25099,25867,26883,27147])),([5,132,192,519,777],(decodeHints [81,593,1105,1617,2129,2641,3153,3595,14929,15697,18769,19025,20817,21073,24843,25169,26891,27217])),([5,132,192,521,775],(decodeHints [11,523,1035,1547,2059,2571,3083,3665,14859,15627,18699,18955,20747,21003,24913,25099,26961,27147])),([5,132,201,512,775],(decodeHints [11,523,1035,1539,2059,2571,3083,3655,14859,15627,18699,18955,20747,21003,24913,25099,29195,29963])),([5,132,201,519,768],(decodeHints [183,695,1207,1539,2231,2743,3255,3595,15031,15799,18871,19127,24843,25271,26961,27319])),([5,135,192,512,777],(decodeHints [81,583,1105,1570,2129,2641,3153,3587,18769,19025,20817,21073,27009,27217,29265,30033])),([5,135,192,521,768],(decodeHints [190,583,1214,1570,2238,2750,3262,3665,20926,21182,24843,25278,27009,27326])),([5,135,201,272,768],(decodeHints [93,584,1117,1540,2141,2653,3165,3677,18706,19037,20829,21010,24850,25181,26973,27154,30033,30301]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_160 : K_160.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_161 : List (List ℕ × List (ℕ × ℕ)) := [([5,135,201,512,768],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,18699,19025,20817,21003,24843,25169,26961,27147,29265,30033])),([6,2,24,132,192,272],(decodeHints [175,687,1199,1723,2223,2719,3247,3651,4271,4697,14767,15023,18863,19119,20911,21167,25007,25263,27055,27311,33148,33455,37170,37551,39292,39599])),([6,4,24,32,98,272],(decodeHints [175,687,1199,1723,2223,2735,3247,3759,4271,4697,14767,15023,18863,19119,20911,21167,25007,25263,27055,27311,29359,30127,33104,33455,37200,37551,39248,39599])),([6,7,8,98,132,192,272,768],[]),([6,7,9,24,32,64,272],(decodeHints [20693,26723,28765,34972,37079])),([6,7,9,24,32,98,272],(decodeHints [20693,37079,49368])),([6,7,9,24,32,98,279],(decodeHints [15425,20693,37079,49368])),([6,7,9,24,32,98,281],(decodeHints [14546,26710,35022,37079,43082,49368,51281]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_161 : K_161.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_162 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,32,98,304],(decodeHints [20693,24784,37079,39128,49368])),([6,7,9,24,32,98,370],(decodeHints [20693])),([6,7,9,24,32,98,644],(decodeHints [14388,26710,32849,40017])),([6,7,9,24,32,98,751],(decodeHints [20571,37003,47189])),([6,7,9,24,32,103,272],(decodeHints [15573,18593,20693,37079,49368])),([6,7,9,24,32,107,272],(decodeHints [20544,26723,28765,32848,37079,45262,49368,51281])),([6,7,9,24,32,122,272],(decodeHints [18639,20693,28767,37079,47319,49368,51285])),([6,7,9,24,32,132,370],(decodeHints [14413,20650,33863]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_162 : K_162.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_163 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,32,132,464],(decodeHints [20650,26721,28765,32937])),([6,7,9,24,32,132,521],(decodeHints [14413,20568,45137,47168])),([6,7,9,24,32,141,512],(decodeHints [20567,36949])),([6,7,9,24,32,192,370],(decodeHints [20642,34924])),([6,7,9,24,32,272,370],(decodeHints [20584,34978,37992])),([6,7,9,24,32,272,644],(decodeHints [20544,26723,28765,37952,47205])),([6,7,9,24,32,272,900],(decodeHints [20693,28765,37056,39116])),([6,7,9,24,32,272,925],(decodeHints [20693,39116]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_163 : K_163.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_164 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,32,370],(decodeHints [14669,16034,18759,18955,20898,21056,35075,35409,37461,38248])),([6,7,9,24,32,370,512],(decodeHints [20642,45171,47217])),([6,7,9,24,32,370,768],(decodeHints [20642,45171])),([6,7,9,24,32,644],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,4177,4689,14669,18759,19025,21056,24913,25169,26961,29009,29265,33361,34119,35153,37201,37457,39249,39505])),([6,7,9,24,39,98,272],(decodeHints [18458,20693,28690,37079,49368])),([6,7,9,24,41,98,272],(decodeHints [14416,20544,28736,34915,37079,45142,49368])),([6,7,9,24,41,132,512],(decodeHints [14413,20566,26705,28736])),([6,7,9,24,56,98,272],(decodeHints [18510,20693,26837,36959,47189,49368]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_164 : K_164.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_165 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,64,98,272],(decodeHints [20693,26768,28825,36959])),([6,7,9,24,64,132,272],(decodeHints [20681,26765,28875,36965])),([6,7,9,24,64,192,272],(decodeHints [20681,26780,28837,34924,36965])),([6,7,9,24,64,272],(decodeHints [14672,16073,20937,21010,37457,38237])),([6,7,9,24,64,272,512],(decodeHints [20681,26765,28875,45174,47214])),([6,7,9,24,64,272,768],(decodeHints [20704,26765,28898,36945,52305])),([6,7,9,24,98,132,192,256],[]),([6,7,9,24,98,132,272,960],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_165 : K_165.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_166 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,98,132,464],(decodeHints [14388,20629,25746,32914])),([6,7,9,24,98,132,464,768],[]),([6,7,9,24,98,132,544],(decodeHints [14388,24657,45142])),([6,7,9,24,98,164,272],(decodeHints [14385,20704,28898])),([6,7,9,24,98,164,512],(decodeHints [14385,43077,45148])),([6,7,9,24,98,192,272],(decodeHints [20704,28837,34960,37017])),([6,7,9,24,98,192,272,900],[]),([6,7,9,24,98,192,279],(decodeHints [15379,20704,28837,34960,37017]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_166 : K_166.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_167 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,98,192,281],(decodeHints [14557,26842,28837,37017,43082])),([6,7,9,24,98,192,370],(decodeHints [20704,34960,37017])),([6,7,9,24,98,192,404,768],[]),([6,7,9,24,98,192,464],(decodeHints [20704,28811,32991])),([6,7,9,24,98,192,644],(decodeHints [14389,37017,51354])),([6,7,9,24,98,192,751],(decodeHints [20572,28837,34960,37017,47189])),([6,7,9,24,98,196,272],(decodeHints [14416,20704,28837,37017])),([6,7,9,24,98,196,272,768],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_167 : K_167.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_168 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,98,199,272],(decodeHints [18580,20704,28837,37017])),([6,7,9,24,98,201,272],(decodeHints [14480,20588,26765,28837,34960,37017])),([6,7,9,24,98,216,272],(decodeHints [20704,28898,35040,37017,47257])),([6,7,9,24,98,272,304],(decodeHints [20584,28837,38104,51416])),([6,7,9,24,98,272,464],(decodeHints [20593,28887,34965,45200])),([6,7,9,24,98,272,544],(decodeHints [20693,28887,45174,47217])),([6,7,9,24,98,272,704],(decodeHints [20498,28837,38042,45200,47257])),([6,7,9,24,98,272,800],(decodeHints [20704,28898,37055]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_168 : K_168.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_169 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,98,272,831],(decodeHints [20704,28837])),([6,7,9,24,98,272,960],(decodeHints [20693,28767,36949,45200])),([6,7,9,24,98,272,991],(decodeHints [20693,28887])),([6,7,9,24,98,304],(decodeHints [216,728,1240,1752,2264,2776,3288,3788,4312,4762,14808,16085,18904,19160,20949,21208,25040,25304,27096,27352,29144,29400,33190,33496,35238,35544,37592,38360])),([6,7,9,24,98,464,768],(decodeHints [20629,36949,45266])),([6,7,9,24,98,704],(decodeHints [154,666,1178,1580,2202,2714,3226,3788,4250,4824,14746,18842,19098,21146,25242,26002,27034,27290,29082,29338,33190,33434,35157,35482,37286,37530])),([6,7,9,24,103,192,272],(decodeHints [18593,20704,28837,34957,37017])),([6,7,9,24,107,192,272],(decodeHints [20573,28837,34957,37017,45274]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_169 : K_169.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_170 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,122,192,272],(decodeHints [18651,20704,28837,34960,37090,47269])),([6,7,9,24,128,192,272],(decodeHints [20681,24719,34957,37067,49356])),([6,7,9,24,132,192,272],(decodeHints [20681,24719,34957,37067,49356])),([6,7,9,24,132,192,272,866],[]),([6,7,9,24,132,192,279],(decodeHints [15379,20681,34957,37067,49356])),([6,7,9,24,132,192,281],(decodeHints [14530,24719,26822,37067,43079,49356])),([6,7,9,24,132,192,370,768],[]),([6,7,9,24,132,192,404],(decodeHints [20681,24722,34957,37067,39116,43154,49356]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_170 : K_170.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_171 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,132,192,464],(decodeHints [20681,24599,32968])),([6,7,9,24,132,192,610],(decodeHints [14345,24722,37002,39078])),([6,7,9,24,132,192,751],(decodeHints [20570,24719,34957,37002,47185])),([6,7,9,24,132,196,272],(decodeHints [20681,34957,37067,49356])),([6,7,9,24,132,199,272],(decodeHints [18580,20681,37067,49356])),([6,7,9,24,132,201,272],(decodeHints [14477,20498,24719,26768,34957,37067,49356])),([6,7,9,24,132,216,272],(decodeHints [20681,24719,28773,35017,37067,47307,49356,51281])),([6,7,9,24,132,272,464],(decodeHints [20573,24719,34965,37981,45197]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_171 : K_171.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_172 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,132,272,544],(decodeHints [20544,28773,37952,45155,47197])),([6,7,9,24,132,272,800],(decodeHints [20681,28773,37055,39128])),([6,7,9,24,132,272,831],(decodeHints [20681,24611,39128])),([6,7,9,24,132,464],(decodeHints [14669,16021,20885,21010,24978,37457,38237])),([6,7,9,24,132,464,512],(decodeHints [20629,24719,45171,47214])),([6,7,9,24,132,464,768],(decodeHints [20629,24719,45171])),([6,7,9,24,132,544],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,4177,4689,14669,18759,19025,21056,25169,25927,26961,29009,29265,33105,33361,35153,37201,37457,39249,39505])),([6,7,9,24,135,192,272],(decodeHints [15561,20681,24719,34957,37067,49356]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_172 : K_172.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_173 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,141,192,272],(decodeHints [20498,24719,28690,34960,37067,45254,49356])),([6,7,9,24,156,192,272],(decodeHints [18631,20681,24719,34957,36965,47185,49356])),([6,7,9,24,164,192,272],(decodeHints [20704,28765,34984,37090])),([6,7,9,24,164,272,512],(decodeHints [20542,28765,37950,45174,47214])),([6,7,9,24,164,272,768],(decodeHints [20704,28765,37057,39117])),([6,7,9,24,164,512],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,4177,4689,14669,18759,19025,21054,25169,25927,26961,29009,29265,33105,33361,35153,37201,37457,39249,39505])),([6,7,9,24,192,272,370],(decodeHints [20593,26768,28875,34978])),([6,7,9,24,192,272,404],(decodeHints [20573,26765,28825,38092,43031,51404]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_173 : K_173.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_174 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,192,272,610],(decodeHints [20498,26768,28825,38054,47269])),([6,7,9,24,192,272,644],(decodeHints [20681,26765,28875,47214])),([6,7,9,24,192,272,866],(decodeHints [20681,26768,28776,36949])),([6,7,9,24,192,272,891],(decodeHints [20681,26765,28875])),([6,7,9,24,192,272,900],(decodeHints [20704,26765,28898,37056])),([6,7,9,24,192,272,925],(decodeHints [20704,26768,28825])),([6,7,9,24,192,370,768],(decodeHints [20642,26768,36949,45254])),([6,7,9,24,192,404],(decodeHints [204,716,1228,1740,2252,2764,3276,3800,4300,4774,14796,16073,18892,19148,20937,21196,25036,25292,27084,27340,29132,29388,33170,33484,35116,35532,37580,38348]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_174 : K_174.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_175 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,24,192,610],(decodeHints [166,678,1190,1580,2214,2726,3238,3800,4262,4812,14758,18854,19110,21158,24998,25254,27046,27302,29094,29350,33446,34208,35157,35494,37274,37542])),([6,7,9,31,32,98,272],(decodeHints [15571,24602,28690,32929,37079,49368,51211])),([6,7,9,31,98,192,272],(decodeHints [15582,24737,28837,32916,34960,37017])),([6,7,9,31,132,192,272],(decodeHints [15555,32916,34957,37067,49356])),([6,7,9,32,56,98,272],(decodeHints [20643,26837,39127])),([6,7,9,32,98,122,272],(decodeHints [26632,29911,35029,39127,47320])),([6,7,9,32,98,132,536],(decodeHints [14416,20566,24657,29777])),([6,7,9,32,98,156,272],(decodeHints [14387,20586,24677,47331]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_175 : K_175.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_176 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,32,98,156,512],(decodeHints [14387,20566,24657,29777,43068,45148])),([6,7,9,32,98,256],(decodeHints [85,586,1109,1580,2133,2645,3157,3669,4181,4693,18743,19029,20821,21047,24887,25169,26965,27191,29269,30037,33079,33365,35157,35383,37205,37461,39253,39509])),([6,7,9,32,98,272,960],(decodeHints [15545,20643,24737,28690,38923,52309])),([6,7,9,32,98,272,999],(decodeHints [37080,52309])),([6,7,9,32,98,464,768],(decodeHints [15546,20615,24710,28690,49189,52309])),([6,7,9,32,122,272],(decodeHints [215,727,1239,1751,2263,2775,3287,3776,4311,4747,14807,16085,18903,19159,20951,21207,25039,25303,27093,27351,29399,30167,33189,33495,35237,35543,37285,37591])),([6,7,9,32,132,536],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,4177,4689,14669,18769,19025,20817,25169,25927,26961,29009,29265,33095,33361,35392,37201,37457,39249,39505])),([6,7,9,32,156,192,272],(decodeHints [20578,28765]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_176 : K_176.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_177 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,32,156,512],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,4177,4689,14669,18769,19025,20817,25169,25927,27221,29009,29265,33105,33361,35153,37201,37457,39249,39505])),([6,7,9,32,272,900],(decodeHints [192,588,1216,1728,2240,2752,3264,3776,4288,4823,16061,18880,19136,20928,21184,25024,25280,27072,27328,29120,29376,33472,35118,35520,37335,37568])),([6,7,9,32,404,768],(decodeHints [193,586,1217,1729,2241,2753,3265,3777,4289,4834,16062,18881,19137,20929,21185,25281,27073,27329,29121,29377,33079,33473,35298,35521,37346,37569])),([6,7,9,32,512,866],(decodeHints [85,586,1109,1580,2133,2645,3157,3669,4181,4693,18743,19029,20821,21047,24887,25173,26965,27191,29013,29269,33079,33361,35157,35383,37461,38229,39509,40277])),([6,7,9,32,610,768],(decodeHints [193,586,1217,1580,2241,2753,3265,3777,4289,4748,18881,19137,20929,21185,25015,25281,27073,27329,29377,30145,33079,33473,35157,35521,37260,37569])),([6,7,9,56,98,132,272],(decodeHints [14414,20704,33864])),([6,7,9,56,98,132,512],(decodeHints [14388,24657,43077,45148])),([6,7,9,56,98,192,272],(decodeHints [20704,28837,34924,40029]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_177 : K_177.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_178 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,56,98,272],(decodeHints [14670,16085,18760,18962,20949,21056,26884,27229,29279,37461])),([6,7,9,56,98,272,512],(decodeHints [20693,45172,47217])),([6,7,9,56,98,272,768],(decodeHints [20704,37091,45172,52309])),([6,7,9,56,132,512],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,4177,4689,14669,18759,19025,21056,25169,25927,26961,29009,29265,33105,33361,35153,37201,37457,39249,39505])),([6,7,9,64,272,768],(decodeHints [93,584,1117,1540,2141,2653,3165,3677,4189,4701,18706,19037,20829,21010,24850,25181,26973,27154,29021,29277,33042,33373,35165,35346,37213,37469,40273,40541])),([6,7,9,64,512,768],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,4177,4689,18699,19025,20817,21003,24843,25169,26961,27147,29009,29265,33035,33361,35153,35339,37201,37457,39505,40273])),([6,7,9,98,122,192,272],(decodeHints [26848,28837,34960,37983])),([6,7,9,98,132,192,280,768],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_178 : K_178.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_179 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,98,132,192,536],(decodeHints [14416,24722,39066,51353])),([6,7,9,98,132,216,272,768],[]),([6,7,9,98,156,192,272],(decodeHints [14387,19655,37989,39065])),([6,7,9,98,156,192,272,768],[]),([6,7,9,98,156,192,512],(decodeHints [14387,39065,43036,45148,51355])),([6,7,9,98,192,216,272],(decodeHints [29797,35040,39065])),([6,7,9,98,192,256],(decodeHints [85,584,1109,1580,2133,2645,3157,3669,4181,4693,19025,20821,21085,24850,25173,26965,27154,30033,30293,33042,33365,35157,35346,37205,37461,39253,39509])),([6,7,9,98,192,272,775],(decodeHints [29789,52309]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_179 : K_179.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_180 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,98,192,272,800],(decodeHints [15541,18613,29797,47122,52309])),([6,7,9,98,192,272,999],(decodeHints [26813,52309])),([6,7,9,98,192,279,768],(decodeHints [29789,52309])),([6,7,9,98,192,304,768],(decodeHints [15546,18652,29797,36875,52309])),([6,7,9,98,192,536],(decodeHints [154,666,1178,1580,2202,2764,3226,3800,4250,4762,14672,19098,19786,20890,21146,24998,25242,26965,27290,33098,33434,35482,37286,37530,39322,39590])),([6,7,9,98,199,272,768],(decodeHints [29791,52309])),([6,7,9,98,216,272],(decodeHints [153,665,1177,1582,2201,2713,3225,3775,4249,4761,14672,19097,20889,21145,24908,25241,27289,30053,33177,33433,35176,35481,37323,37529,39509])),([6,7,9,98,216,512],(decodeHints [153,665,1177,1580,2201,2763,3225,3775,4249,4761,14672,19097,19786,20889,21145,24906,25241,27289,33177,33433,35157,35481,37258,37529,39321,39562]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_180 : K_180.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_181 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,98,272,800],(decodeHints [191,588,1215,1582,2239,2751,3263,3775,4287,4761,18869,19135,20927,21183,25023,25279,27071,27327,29119,29375,33088,33471,35176,35519,37224,40277])),([6,7,9,98,272,960],(decodeHints [18,584,1042,1554,2066,2578,3090,3602,4114,4626,16022,20740,21085,24850,26898,27154,28946,29202,33042,35090,35346,38237,40277])),([6,7,9,98,304,768],(decodeHints [227,588,1251,1582,2275,2787,3299,3739,4323,4835,18908,19171,20963,21219,24896,25315,26984,27363,29032,33088,33507,35176,35555,37325,37603,40552])),([6,7,9,98,464,768],(decodeHints [18,584,1042,1554,2066,2578,3090,3602,4114,4626,16062,20740,21085,24850,26898,27154,30045,33042,35090,35346,37138,37394,40561])),([6,7,9,98,512,800],(decodeHints [191,586,1215,1580,2239,2763,3263,3775,4287,4761,18869,19135,20927,21183,25023,25279,27071,27327,29119,29375,33079,33471,35157,35519,39615,40383])),([6,7,9,98,544,768],(decodeHints [85,586,1109,1580,2133,2645,3157,3669,4181,4693,18743,19025,20821,21047,24887,25173,26965,27191,29013,33079,33365,35157,35383,37205,37461,39509])),([6,7,9,98,704,768],(decodeHints [155,584,1179,1580,2203,2715,3227,3811,4251,4763,19099,20891,21147,24850,25243,26965,27291,30033,33042,33435,35157,35483,37325,37531,39509])),([6,7,9,103,192,272,768],(decodeHints [29789,52305]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_181 : K_181.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_182 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,122,132,192,272],(decodeHints [14344,24722,39077,49306])),([6,7,9,122,132,192,272,768],[]),([6,7,9,122,132,192,512],(decodeHints [14344,24709,39051,43024,45148,51340])),([6,7,9,122,192,272],(decodeHints [165,677,1189,1581,2213,2752,3237,3749,4261,4773,14672,19109,21157,24997,25253,26975,27301,30303,33189,33445,35167,35493,37461,39383,39563])),([6,7,9,122,192,512],(decodeHints [139,651,1163,1580,2187,2752,3211,3799,4235,4747,14731,19083,19845,21131,24997,25227,26965,27275,33163,33419,35157,35467,37285,37515,39307,39589])),([6,7,9,132,156,192,272],(decodeHints [18578,20630,26825,34957,39115])),([6,7,9,132,192,216,272],(decodeHints [18455,29899,35017,39115,47308])),([6,7,9,132,192,256],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,4177,4689,18821,19025,20817,21003,24843,25169,26961,27147,29265,30033,33035,33361,35153,35339,37201,37457,39249,39505]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_182 : K_182.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_183 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,132,192,272,800],(decodeHints [15541,29887,37068,47296,52305])),([6,7,9,132,192,272,999],(decodeHints [18575,26765,37068,52305])),([6,7,9,132,192,304,768],(decodeHints [15543,29889,37092,47296,52305])),([6,7,9,132,216,272],(decodeHints [203,715,1227,1739,2251,2763,3275,3775,4299,4746,14795,16073,18891,19147,20939,21195,25035,25291,27081,27339,29387,30155,33177,33483,35225,35531,37273,37579])),([6,7,9,132,272,800],(decodeHints [191,588,1215,1727,2239,2751,3263,3775,4287,4811,16060,19135,20927,21183,25023,25279,27071,27327,29119,29375,33088,33471,35275,35519,37323,37567])),([6,7,9,132,304,768],(decodeHints [193,588,1217,1729,2241,2753,3265,3777,4289,4834,16062,19137,20929,21185,25025,25281,27073,27329,29121,29377,33088,33473,35298,35521,37346,37569])),([6,7,9,132,512,960],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,4177,4689,18821,19025,20817,21003,24843,25169,26961,27147,29009,29265,33035,33361,35153,35339,37457,38225,39505,40273])),([6,7,9,132,704,768],(decodeHints [193,583,1217,1539,2241,2753,3265,3777,4289,4748,18881,19137,20929,21185,25025,25281,27073,27329,29377,30145,33035,33473,35153,35521,37260,37569]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_183 : K_183.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_184 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,156,192,272],(decodeHints [14671,16073,18887,20937,21010,29285,37457])),([6,7,9,156,192,272,512],(decodeHints [45173,47214])),([6,7,9,156,192,272,768],(decodeHints [37092,45173,52305])),([6,7,9,164,272,768],(decodeHints [193,587,1217,1729,2241,2753,3265,3777,4289,4834,16062,19137,20929,21185,25025,25281,27073,27329,29121,29377,33086,33473,35298,35521,37346,37569])),([6,7,9,192,272,866],(decodeHints [18,584,1042,1554,2066,2578,3090,3602,4114,4626,16035,18706,20754,21010,24850,26898,27154,28946,29202,35076,35421,38248,40277])),([6,7,9,192,272,900],(decodeHints [192,584,1216,1540,2240,2752,3264,3776,4288,4773,18880,19136,20928,21184,25024,25280,27072,27328,29120,29376,33472,35165,35520,37213,40273])),([6,7,9,192,370,768],(decodeHints [11,583,1035,1547,2059,2571,3083,3595,4107,4619,16062,18699,20747,21003,26883,27217,30056,33035,35083,35339,37131,37387,40561])),([6,7,9,192,404,768],(decodeHints [228,584,1252,1540,2276,2788,3300,3751,4324,4836,18916,19172,20964,21220,25316,26973,27364,29021,33042,33508,35165,35556,37337,37604,40541]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_184 : K_184.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_185 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,192,512,900],(decodeHints [192,583,1216,1539,2240,2752,3264,3776,4288,4747,18880,19136,20928,21184,25024,25280,27072,27328,29120,29376,33035,33472,35153,35520,39616,40384])),([6,7,9,192,610,768],(decodeHints [167,584,1191,1580,2215,2727,3239,3812,4263,4775,18855,19111,20903,21159,25255,26965,27303,30037,33042,33447,35157,35495,37337,37543,39509])),([6,7,9,192,644,768],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,4177,4689,18699,19025,20817,21003,25018,25169,26961,27147,29009,33035,33361,35153,35339,37201,37457,39505])),([6,7,24,32,41,98,272],(decodeHints [20643,26837,35031])),([6,7,24,32,98,107,272],(decodeHints [20484,26632,35029,47320])),([6,7,24,32,98,272,281],(decodeHints [26789,35944,39074])),([6,7,24,32,98,272,644],(decodeHints [20484,26632,35886,36873,38915,44207,47153])),([6,7,24,32,98,272,777],(decodeHints [20596,26850,34901,37091,39027]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_185 : K_185.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_186 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,24,32,98,272,1014],(decodeHints [26839,37080,44207])),([6,7,24,32,132,272,777],(decodeHints [20573,26725,34897,37058,39118])),([6,7,24,32,132,370],(decodeHints [3,515,1027,1673,2051,2563,3075,3587,4099,4689,14595,14851,18691,18947,20739,20995,25859,26115,26883,27139,28931,29187,33135,37379,38147,39283,39427])),([6,7,24,32,132,521],(decodeHints [81,593,1105,1673,2129,2641,3153,3665,4177,4611,14673,14929,18769,19025,20817,21073,25169,25937,26961,27217,29009,29265,33101,37235,37457,39283,39505])),([6,7,24,41,98,132,272],(decodeHints [20704,33872,34922])),([6,7,24,41,98,192,272],(decodeHints [20704,34920,40035])),([6,7,24,41,98,272],(decodeHints [18768,20899,21205,29283,35413,36259])),([6,7,24,41,98,272,512],(decodeHints [20693,45169,47222]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_186 : K_186.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_187 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,24,41,98,272,768],(decodeHints [20704,34901,52309])),([6,7,24,41,132,272,768],(decodeHints [26722,32862,35009,39129])),([6,7,24,41,132,512],(decodeHints [81,593,1105,1671,2129,2563,3153,3665,4177,4689,14673,14929,18765,25169,25937,26977,27217,29009,29281,33105,33361,35169,35409,37201,37473,39249,39505])),([6,7,24,98,107,192,272],(decodeHints [26848,34969])),([6,7,24,98,132,192,272,777],[]),([6,7,24,98,132,201,272],(decodeHints [24720,35040,43160,49306])),([6,7,24,98,132,201,272,768],[]),([6,7,24,98,132,201,512],(decodeHints [24661,43036,51292]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_187 : K_187.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_188 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,24,98,132,272,544],(decodeHints [20488,25775,35886,36867,49201])),([6,7,24,98,132,272,704],(decodeHints [26774,35991,39066])),([6,7,24,98,132,304],(decodeHints [224,736,1248,1726,2272,2754,3296,3808,4320,4700,14816,15072,18908,20960,21216,26028,26325,27104,27360,29152,29408,33196,33504,39177,39648])),([6,7,24,98,132,464],(decodeHints [149,661,1173,1726,2197,2709,3221,3794,4245,4694,14741,14997,19858,20117,20885,21141,24978,27029,27285,29077,29333,33198,33429,37170,39573])),([6,7,24,98,164,272],(decodeHints [224,736,1248,1726,2272,2784,3296,3728,4320,4700,14816,15072,18912,20960,21216,26031,27104,27360,29152,33073,33504,37169,37600,39217,39648])),([6,7,24,98,192,201,272],(decodeHints [20575,29804,35040,39056])),([6,7,24,98,192,272,281],(decodeHints [20575,26728,35953,37026,39061,49296])),([6,7,24,98,192,272,644],(decodeHints [26670,35887,38964]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_188 : K_188.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_189 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,24,98,192,272,777],(decodeHints [20575,26728,34901,37062,39122,49296])),([6,7,24,98,192,272,1014],(decodeHints [20525,26670,44207])),([6,7,24,98,192,404],(decodeHints [44,556,1068,1726,2092,2604,3116,3800,4140,4693,14636,14892,19756,20012,20780,21036,24876,25132,26924,27180,28972,33170,37324,37420,39468])),([6,7,24,98,192,521],(decodeHints [85,597,1109,1726,2133,2764,3157,3800,4181,4652,14677,14933,19025,19797,20821,21077,24917,25173,26965,27221,33178,37286,37461,39322,39509])),([6,7,24,98,196,272],(decodeHints [224,736,1248,1726,2272,2784,3296,3808,4320,4700,14816,15072,20960,21216,27104,27360,33142,33504,37238,37600,39286,39648])),([6,7,24,98,196,272,512],(decodeHints [35886])),([6,7,24,98,201,272],(decodeHints [144,656,1168,1725,2192,2704,3216,3633,4240,4752,14736,14992,19085,20880,21136,24912,27360,30060,33168,33424,35413,37264,37520,39312,39515])),([6,7,24,98,201,512],(decodeHints [85,597,1109,1725,2133,2764,3157,3628,4181,4693,14677,14933,19025,19797,20821,21077,24958,33109,33365,35180,35413,37286,37461,39253,39590]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_189 : K_189.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_190 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,24,132,141,192,272],(decodeHints [20630,26825,35019,39053])),([6,7,24,132,192,201,272],(decodeHints [18455,29837,35017,39053,47308])),([6,7,24,132,192,272,281],(decodeHints [18575,26777,35933,39061,49293])),([6,7,24,132,192,272,610],(decodeHints [20630,26777,35844,36908,39061,44207])),([6,7,24,132,192,272,777],(decodeHints [18575,20597,26850,34897,37092,39027])),([6,7,24,132,192,272,1014],(decodeHints [18575,26827,37068,44207])),([6,7,24,132,201,272],(decodeHints [141,632,1165,1677,2189,2701,3213,3590,4237,4749,14733,14989,18829,19085,20877,21133,26898,27337,29325,30093,33045,33421,35409,36189,37261,37517,39309,39445])),([6,7,25,32,98,272],(decodeHints [213,588,1237,1582,2261,2773,3285,3797,4309,4699,18901,19157,20949,21205,25045,25301,27093,27349,29397,30165,33088,33493,37224,37589,39272,39637]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_190 : K_190.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_191 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,25,98,192,272],(decodeHints [224,584,1248,1583,2272,2784,3296,3808,4320,4700,19168,20960,21216,25056,25312,27104,27360,30153,30421,33042,33504,37233,37600,39281,39648])),([6,7,25,132,192,272],(decodeHints [201,584,1225,1540,2249,2761,3273,3785,4297,4698,18889,19145,20937,21193,25033,25289,27081,27337,29385,30153,33042,33481,37213,37577,39261,39625])),([6,7,32,98,272,900],(decodeHints [46,588,1070,1582,2094,2606,3118,3630,4142,4821,14638,14894,18734,20014,21038,21806,24878,25134,26926,27182,28974,29230,35285,35374,37333,37422])),([6,7,32,98,404,768],(decodeHints [190,586,1214,1726,2238,2750,3262,3774,4286,4652,14782,15038,18878,20158,21182,21950,27070,27326,29118,29374,33079,33470,35116,35518,37164,37566])),([6,7,32,98,512,777],(decodeHints [85,586,1109,1621,2133,2645,3157,3669,4181,4652,14677,14933,18773,19025,21077,21845,24917,25173,26965,27221,29013,29269,35127,35413,37175,37461,39509,40277])),([6,7,32,98,521,768],(decodeHints [190,586,1214,1726,2238,2750,3262,3774,4286,4693,14782,15038,18878,19134,21182,21950,27070,27326,29118,29374,33079,33470,35157,35518,37205,37566])),([6,7,32,122,132,272],(decodeHints [224,736,1248,1760,2272,2740,3296,3808,4320,4700,14816,15072,18907,21216,21984,26027,26325,27104,27360,29152,29408,33195,33504,35080,35552,39176,39648])),([6,7,32,132,201,272,768],(decodeHints [20542,37089,47293,52305]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_191 : K_191.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_192 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,41,98,272,768],(decodeHints [163,588,1187,1582,2211,2658,3235,3747,4259,4771,18752,19107,24896,25251,26984,27299,29091,29288,33088,33443,35176,35491,37283,37480,40327,40611])),([6,7,41,98,512,768],(decodeHints [135,586,1159,1580,2183,2657,3207,3719,4231,4743,18743,19079,24887,25223,26965,27271,29063,29269,33079,33415,35157,35463,37255,37461,39559,40327])),([6,7,56,98,132,272],(decodeHints [224,736,1248,1687,2272,2653,3296,3808,4320,4700,14816,15072,18912,26031,26325,27104,27360,29152,29408,33028,33504,37124,37600,39172,39648])),([6,7,98,132,216,272],(decodeHints [224,736,1248,1760,2272,2664,3296,3774,4320,4700,15791,16073,18912,20960,21216,25056,25312,27104,29408,33142,33504,35275,35552,37166,37600])),([6,7,98,132,272,800],(decodeHints [190,588,1214,1726,2238,2664,3262,3774,4286,4832,14773,16060,20926,21182,25022,25278,27070,27326,29118,29374,33088,33470,35273,37166,37566])),([6,7,98,132,272,960],(decodeHints [151,584,1175,1687,2199,2711,3223,3735,4247,4832,18834,20118,20887,21143,24983,25239,27031,27287,29079,29335,33042,33431,37333,37527])),([6,7,98,132,304,768],(decodeHints [190,588,1214,1726,2238,2664,3262,3774,4286,4832,14782,16062,20926,21182,25022,25278,27070,29118,29374,33088,33470,35277,35518,37166,37566])),([6,7,98,132,464,768],(decodeHints [190,584,1214,1629,2238,2750,3262,3774,4286,4757,18878,20158,20926,21182,25022,25278,29118,29374,33042,33470,35076,35518,37269,37566]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_192 : K_192.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_193 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,98,156,192,272],(decodeHints [224,736,1248,1760,2272,2744,3296,3690,4320,4700,15789,16073,18910,20960,21216,25056,25312,27104,29152,33197,33504,35222,35552,39318,39648])),([6,7,98,164,272,768],(decodeHints [190,588,1214,1726,2238,2664,3262,3774,4286,4832,14782,16062,20926,25022,25278,27070,27326,29118,29374,33088,33470,35296,35518,37166,37566])),([6,7,98,192,272,900],(decodeHints [47,584,1071,1629,2095,2607,3119,3631,4143,4832,18735,18991,20783,22062,24879,25135,26927,27183,28975,29231,35076,35375,37333,37423])),([6,7,98,192,404,768],(decodeHints [190,584,1214,1629,2238,2750,3262,3774,4286,4652,18878,19134,20926,22206,27070,27326,29118,29374,33042,33470,35076,35518,37164,37566])),([6,7,98,192,512,777],(decodeHints [85,584,1109,1621,2133,2645,3157,3669,4181,4652,14929,18773,19029,21841,22101,24917,25173,26965,27221,29013,29269,35165,35413,37138,37461,39509,40277])),([6,7,98,192,521,768],(decodeHints [190,584,1214,1726,2238,2750,3262,3774,4286,4693,15038,18878,19134,21950,22206,27070,27326,29118,29374,33042,33470,35157,35518,37205,37566])),([6,7,98,196,272,768],(decodeHints [190,584,1214,1629,2238,2664,3262,3774,4286,4832,25022,25278,27070,27326,29118,29374,33042,33470,35076,35518,37166,37566])),([6,7,132,192,272,866],(decodeHints [4,584,1028,1540,2052,2564,3076,3588,4100,4809,14596,15876,18692,18948,20740,20996,24836,25092,26884,27140,28932,29188,35273,35332,37380,38148]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_193 : K_193.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_194 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,132,192,370,768],(decodeHints [190,583,1214,1726,2238,2750,3262,3774,4286,4611,14782,16062,18878,19134,20926,21182,27070,27326,29374,30142,33035,33470,35075,35518,37123,37566])),([6,7,132,192,512,777],(decodeHints [81,583,1105,1617,2129,2641,3153,3665,4177,4611,14673,14929,18769,19025,21073,21841,24913,25169,26961,27217,29009,29265,35083,35409,37131,37457,39505,40273])),([6,7,132,192,521,768],(decodeHints [190,583,1214,1726,2238,2750,3262,3774,4286,4689,14782,15038,18878,19134,21182,21950,27070,27326,29118,29374,33035,33470,35153,35518,37201,37566])),([6,7,132,201,272,768],(decodeHints [93,584,1117,1629,2141,2564,3165,3677,4189,4701,14685,14941,21085,21853,24850,25181,26973,27229,29021,29202,33042,33373,35165,35421,37213,37394,40273,40541])),([6,7,132,201,512,768],(decodeHints [81,583,1105,1617,2129,2563,3153,3665,4177,4689,14673,14929,21073,21841,24843,25169,26961,27217,29009,29195,33035,33361,35153,35409,37201,37387,39505,40273])),([6,9,24,31,32,98,272],(decodeHints [26702,35023,45130,47178,49368,51271])),([6,9,24,31,98,192,272],(decodeHints [26843,32912,45130,47178])),([6,9,24,31,132,192,272],(decodeHints [26823,28815,32909,45127,47175,49356]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_194 : K_194.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_195 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,24,32,39,98,272],(decodeHints [14549,35031,47312])),([6,9,24,32,98,103,272],(decodeHints [14549,47312])),([6,9,24,32,98,132,279],(decodeHints [14400])),([6,9,24,32,98,192,279],(decodeHints [14406,32873,34920])),([6,9,24,32,98,272,279],(decodeHints [14400,26789,35904])),([6,9,24,32,98,272,960],(decodeHints [20552,26831,35001,37072,38983])),([6,9,24,32,98,272,1016],(decodeHints [14412,26839,37080,43183])),([6,9,24,32,98,279],(decodeHints [14657,14912,33354,34113,35402,36160]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_195 : K_195.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_196 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,24,32,98,279,512],(decodeHints [14400,43122,45169])),([6,9,24,32,98,279,768],(decodeHints [14400])),([6,9,24,32,98,704],(decodeHints [74,556,1098,1591,2122,2634,3146,3658,4170,4682,18773,19018,20810,21077,24917,25162,26954,27221,29258,30026,33109,33354,35146,35413,37194,37450,39498,40263])),([6,9,24,32,103,132,272],(decodeHints [14560,34917,47324])),([6,9,24,32,103,192,272],(decodeHints [14560,34917,47324])),([6,9,24,32,103,272],(decodeHints [14805,14878,25168,26069,35409,36126])),([6,9,24,32,103,272,512],(decodeHints [14549,37072,43126,45166])),([6,9,24,32,103,272,768],(decodeHints [14560,34897,37084,52305]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_196 : K_196.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_197 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,24,32,128,272,768],(decodeHints [20552,26697,34999,37061,39121])),([6,9,24,32,128,512],(decodeHints [71,515,1095,1547,2119,2631,3143,3655,4167,4679,18769,19015,20807,21073,24913,25159,26951,27217,28999,29255,33105,33351,35143,35409,37191,37447,39239,39495])),([6,9,24,32,132,192,279],(decodeHints [14373,18526,20573,32806,34855,49192])),([6,9,24,32,132,279,512],(decodeHints [14400,18526,20573,43119,45166])),([6,9,24,32,132,279,768],(decodeHints [14400,18526,20573])),([6,9,24,98,132,192,272,775],[]),([6,9,24,98,132,192,279],(decodeHints [14354,32920,34969,49298])),([6,9,24,98,132,192,279,768],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_197 : K_197.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_198 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,24,98,192,199,272],(decodeHints [14560,20645,49375])),([6,9,24,98,192,272,279],(decodeHints [14354,20645,24720,26777,35858])),([6,9,24,98,192,272,800],(decodeHints [20699,26700,34997,39120])),([6,9,24,98,192,272,1016],(decodeHints [14408,20645,24720,26777,43183])),([6,9,24,98,192,279],(decodeHints [14611,14866,33354,34067,35402,36114])),([6,9,24,98,192,279,512],(decodeHints [14354,24720,26769,43122,45169])),([6,9,24,98,192,279,768],(decodeHints [14354,24720,26769])),([6,9,24,98,192,544],(decodeHints [74,556,1098,1591,2122,2634,3146,3658,4170,4682,18773,19018,20810,21077,24917,25162,26954,27221,29258,30023,33109,33354,35146,35413,37194,39242,39498]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_198 : K_198.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_199 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,24,132,192,199,272],(decodeHints [14537,47308,49352])),([6,9,24,132,192,272,279],(decodeHints [14354,24597,26777,35858,47127])),([6,9,24,132,192,272,800],(decodeHints [20679,26827,34997,37068,39112])),([6,9,24,132,192,272,1016],(decodeHints [14408,24696,26827,37068,43183])),([6,9,24,132,192,279],(decodeHints [14611,14866,33351,34067,35399,36114,37522])),([6,9,24,132,192,279,512],(decodeHints [14354,24597,26646,36887,43119,45166])),([6,9,24,132,192,279,768],(decodeHints [14354,24597,26646,36887])),([6,9,24,132,192,544],(decodeHints [71,515,1095,1547,2119,2631,3143,3655,4167,4679,18769,19015,20807,21073,24913,25159,26951,27217,30023,30279,33105,33351,35143,35409,37191,37447,39239,39495]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_199 : K_199.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_200 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,24,135,192,272],(decodeHints [143,655,1167,1679,2191,2718,3215,3619,4239,4751,14793,14991,19087,19913,20879,21135,24855,25231,26903,27279,33167,33423,35471,36239,37143,37519,39311,39447])),([6,9,32,98,192,536],(decodeHints [74,556,1098,1610,2122,2634,3146,3658,4170,4663,14666,14922,18762,19018,21066,21834,24906,25162,26954,27210,29258,30023,35157,35402,37205,37450,39253,39498])),([6,9,32,98,216,512],(decodeHints [74,556,1098,1610,2122,2634,3146,3639,4170,4682,14666,14922,18762,19018,21066,21834,26965,27210,29258,30023,33109,33354,35146,35402,37194,37450,39242,39509])),([6,9,32,98,512,775],(decodeHints [55,556,1079,1591,2103,2615,3127,3639,4151,4682,14647,14903,18743,18999,21047,21815,24887,25143,26935,27191,28983,29239,35157,35383,37201,37431,39479,40247])),([6,9,32,98,519,768],(decodeHints [186,556,1210,1722,2234,2746,3258,3770,4282,4663,14778,15034,18874,19130,21178,21946,27066,27322,29111,29370,33109,33466,35127,35514,37175,37562])),([6,9,32,103,272,768],(decodeHints [30,517,1054,1566,2078,2633,3102,3614,4126,4638,14622,14878,21022,21790,24933,25118,26910,27166,28958,29285,33125,33310,35102,35358,37150,37477,40203,40478])),([6,9,32,103,512,768],(decodeHints [11,515,1035,1547,2059,2631,3083,3595,4107,4619,14603,14859,21003,21771,24913,25099,26891,27147,28939,29265,33105,33291,35083,35339,37131,37457,39435,40203])),([6,9,32,132,192,536],(decodeHints [71,515,1095,1607,2119,2631,3143,3655,4167,4619,14663,14919,18759,19015,20807,21063,24903,25159,26951,27207,30023,30279,35153,35399,37201,37447,39249,39495]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_200 : K_200.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_201 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,32,135,192,272,768],(decodeHints [52353])),([6,9,56,98,192,512],(decodeHints [72,556,1096,1554,2120,2632,3144,3656,4168,4680,18773,19016,21077,24917,25160,26952,27221,29256,30023,33109,33352,35144,35413,37192,37448,39240,39496])),([6,9,56,132,192,512],(decodeHints [71,515,1095,1547,2119,2631,3143,3655,4167,4679,18769,19015,20807,21073,24913,25159,26951,27217,30023,30279,33105,33351,35143,35409,37191,37447,39239,39495])),([6,9,98,192,512,775],(decodeHints [18,556,1042,1554,2066,2578,3090,3602,4114,4680,14610,14866,18706,18962,21771,22034,24850,25106,26898,27154,28946,29202,35153,37205,37394,39442,40210])),([6,9,98,192,519,768],(decodeHints [186,556,1210,1722,2234,2746,3258,3770,4282,4626,14778,15034,18874,19130,21943,22202,27063,29114,29370,33109,33466,35269,35514,37138,37562])),([6,9,132,192,512,775],(decodeHints [11,515,1035,1547,2059,2571,3083,3595,4107,4679,14603,14859,18699,18955,21003,21771,24843,25099,26891,27147,28939,29195,35153,35339,37201,37387,39435,40203])),([6,9,132,192,519,768],(decodeHints [183,515,1207,1719,2231,2743,3255,3767,4279,4619,14775,15031,18871,19127,21175,21943,27063,27319,29111,29367,33105,33463,35083,35511,37131,37559])),([6,9,135,192,272,768],(decodeHints [143,516,1167,1608,2191,2595,3215,3727,4239,4751,18781,19087,24925,25231,26898,27279,29071,29202,33117,33423,35090,35471,37263,37394,40321,40591]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_201 : K_201.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_202 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,135,192,512,768],(decodeHints [129,515,1153,1607,2177,2594,3201,3713,4225,4737,18769,19073,24913,25217,26891,27265,29057,29195,33105,33409,35083,35457,37249,37387,39553,40321])),([6,15,24,98,132,192,272,768],[]),([6,24,32,98,132,272,519],(decodeHints [14340,18440,26673,33856,34825,36867,50351])),([6,24,32,98,132,464],(decodeHints [174,699,1198,1710,2222,2734,3246,3794,4270,4676,14766,15022,18862,19118,21166,21934,25006,25262,27054,27310,29102,29358,35124,35502,37170,37550])),([6,24,32,98,192,272,777],(decodeHints [14408,18603,24680,32853,34988,36935,39122])),([6,24,32,98,192,404],(decodeHints [44,567,1068,1580,2092,2604,3116,3628,4140,4693,14636,14892,18732,18988,21036,21804,24876,25132,26924,27180,28972,29228,35146,35372,37194,37420,39468,40236])),([6,24,32,98,192,521],(decodeHints [85,567,1109,1621,2133,2645,3157,3669,4181,4652,14677,14933,18773,19029,21077,21845,24917,25173,26965,27221,29269,30033,35146,35413,37194,37461,39242,39509])),([6,24,32,98,201,272,768],(decodeHints [14408,18651,32954,35036,36935]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_202 : K_202.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_203 : List (List ℕ × List (ℕ × ℕ)) := [([6,24,32,98,201,512],(decodeHints [85,567,1109,1621,2133,2645,3157,3628,4181,4693,14677,14933,18773,19029,21077,21845,26954,27221,29269,30033,33098,33365,35157,35413,37205,37461,39253,39498])),([6,24,32,132,192,272,777],(decodeHints [14429,18605,24754,32849,35010,37043,39086])),([6,24,32,132,192,370],(decodeHints [3,523,1027,1539,2051,2563,3075,3587,4099,4689,14595,14851,18691,18947,20739,20995,24835,25091,26883,27139,28931,30211,35331,36099,37191,37379,39239,39427])),([6,24,32,132,192,521],(decodeHints [81,523,1105,1617,2129,2641,3153,3665,4177,4611,14673,14929,18769,19025,20817,21073,24913,25169,26961,27217,30033,30289,35143,35409,37191,37457,39239,39505])),([6,24,32,132,226,272],(decodeHints [175,699,1199,1711,2223,2589,3247,3647,4271,4697,14767,15023,18863,19119,20911,21167,25007,25263,27311,28079,35074,35503,37163,37551,39170,39599])),([6,24,41,98,192,272,768],(decodeHints [24652,32954,36935,39124])),([6,24,41,98,192,512],(decodeHints [82,567,1106,1555,2130,2642,3154,3666,4178,4690,18762,19026,21066,24906,25170,26962,27210,29266,30033,33098,33362,35154,35402,37202,37458,39250,39506])),([6,24,41,132,192,272,768],(decodeHints [18654,24802,32951,37092,39135]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_203 : K_203.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_204 : List (List ℕ × List (ℕ × ℕ)) := [([6,24,41,132,192,512],(decodeHints [81,523,1105,1539,2129,2641,3153,3665,4177,4689,18759,19025,20817,21063,24903,25169,26961,27207,30033,30289,33095,33361,35153,35399,37201,37457,39249,39505])),([6,24,98,132,192,272,519],(decodeHints [18582,24729,33810,36908,39061,46255])),([6,24,98,132,192,304],(decodeHints [172,699,1196,1730,2220,2732,3244,3756,4268,4633,14764,15020,18860,19116,20908,21164,25004,25260,27052,27308,29100,30380,37129,37548,39177,39596])),([6,24,98,164,192,272],(decodeHints [175,699,1199,1597,2223,2577,3247,3759,4271,4697,14767,15023,18863,19119,25007,25263,27055,27311,29103,30383,35073,35503,37162,37551,39210,39599])),([6,32,98,132,216,272],(decodeHints [175,687,1199,1711,2223,2664,3247,3648,4271,4697,15023,15791,18863,19119,20911,21167,25007,25263,27055,27311,33100,33455,35148,35503,37166,37551])),([6,32,98,132,272,775],(decodeHints [64,576,1088,1600,2112,2664,3136,3648,4160,4783,14912,15680,18752,19008,20800,21056,24896,25152,26944,27200,28992,29248,33199,33344,35392,36160])),([6,32,98,132,279,768],(decodeHints [177,689,1201,1713,2225,2664,3249,3761,4273,4672,15025,15793,18865,19121,20913,21169,25009,25265,27313,28081,33088,33457,35136,35505,37166,37553])),([6,32,98,156,192,272],(decodeHints [173,685,1197,1709,2221,2744,3245,3757,4269,4667,15021,15789,18861,19117,20909,21165,25005,25261,27053,27309,29101,30381,33075,33453,35123,35501,39219,39597]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_204 : K_204.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_205 : List (List ℕ × List (ℕ × ℕ)) := [([6,32,122,132,192,272],(decodeHints [171,683,1195,1716,2219,2731,3243,3755,4267,4623,15019,15787,18859,19115,20907,21163,25003,25259,27051,27307,29099,30379,33032,33451,37128,37547,39176,39595])),([6,56,98,132,192,272],(decodeHints [175,530,1199,1629,2223,2735,3247,3759,4271,4697,18863,19119,20911,21167,25007,25263,27055,27311,29103,30383,35076,35503,37124,37551,39172,39599])),([6,98,132,192,272,775],(decodeHints [18,605,1042,1554,2066,2578,3090,3602,4114,4783,14610,14866,18706,19986,20754,21010,24850,25106,26898,27154,28946,29202,35346,36114,37295,37394])),([6,98,132,192,279,768],(decodeHints [177,605,1201,1713,2225,2737,3249,3761,4273,4626,14769,15025,18865,20145,20913,21169,27313,28081,29105,29361,33028,33457,35090,35505,37138,37553])),([7,7,9,24,32,98,132,272],(decodeHints [14416,20704,37090,44112,61667])),([7,7,9,24,32,98,132,512],(decodeHints [14388,26710,32849,40017,55365,57436])),([7,7,9,24,32,98,192,272],(decodeHints [20704,37029,45164,47208,61606])),([7,7,9,24,32,98,272],(decodeHints [14672,16085,20949,21056,47701,48488]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_205 : K_205.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_206 : List (List ℕ × List (ℕ × ℕ)) := [([7,7,9,24,32,98,272,512],(decodeHints [20693,37079,49368,57462,59505])),([7,7,9,24,32,98,272,768],(decodeHints [20704,37090,47189,49379,66645])),([7,7,9,24,32,132,192,272],(decodeHints [20704,26723,28765,32937,45224,47330,63716])),([7,7,9,24,32,132,272,512],(decodeHints [20544,26723,28765,36965,48192,57462,59502])),([7,7,9,24,32,132,272,768],(decodeHints [20704,28765,36965,47297,49357,51417])),([7,7,9,24,32,132,512],(decodeHints [81,593,1105,1539,2129,2641,3153,3665,4177,4689,5201,5713,14669,18759,19025,21056,24913,25169,26961,29009,29265,33361,34119,35153,37201,37457,39249,39505,43345,43601,45393,47441,47697,49489,49745,51537,51793])),([7,7,9,24,98,132,192,272],(decodeHints [14416,20704,25746,32914,47257,63642])),([7,7,9,24,98,132,192,272,768],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_206 : K_206.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_207 : List (List ℕ × List (ℕ × ℕ)) := [([7,7,9,24,98,132,192,512],(decodeHints [14345,32914,47257,51354,55324,57436,65691])),([7,7,9,24,98,192,272],(decodeHints [14672,16096,20960,21010,47701,48497])),([7,7,9,24,98,192,272,512],(decodeHints [20498,28837,34960,37017,48282,57462,59505])),([7,7,9,24,98,192,272,768],(decodeHints [20704,28767,34960,36968,47189,66645])),([7,7,9,24,98,192,512],(decodeHints [154,666,1178,1580,2202,2714,3226,3788,4250,4824,5274,5786,14746,18842,19098,21146,25242,26002,27034,27290,29082,29338,33190,33434,35157,35482,37286,37530,43418,43674,45397,45722,47514,47770,49574,49818,51610,51878])),([7,7,9,24,132,192,272],(decodeHints [14672,16073,20937,21010,24978,47697,48477])),([7,7,9,24,132,192,272,512],(decodeHints [20681,24719,34957,37067,49356,57462,59502])),([7,7,9,24,132,192,272,768],(decodeHints [20704,24719,34957,37090,47185,49380,66641]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_207 : K_207.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_208 : List (List ℕ × List (ℕ × ℕ)) := [([7,7,9,32,98,192,272,768],(decodeHints [15546,20643,24737,28690,40037,49163,61477,66645])),([7,7,9,32,98,272,768],(decodeHints [104,588,1128,1582,2152,2664,3176,3688,4200,4712,5224,5736,18752,19048,20840,21056,24896,25189,26984,27200,29288,30056,33088,33384,35176,35392,37224,37480,39272,39528,43328,43624,45416,45632,47464,47720,49512,49768,52565,52840])),([7,7,9,32,98,512,768],(decodeHints [85,586,1109,1580,2133,2645,3157,3669,4181,4693,5205,5717,18743,19029,20821,21047,24887,25169,26965,27191,29269,30037,33079,33365,35157,35383,37205,37461,39253,39509,43319,43605,45397,45623,47445,47701,49493,49749,51797,52565])),([7,7,9,32,132,192,272,768],(decodeHints [15543,28734,40129,49380,61632,66641])),([7,7,9,32,132,272,768],(decodeHints [193,588,1217,1729,2241,2753,3265,3777,4289,4801,5313,5858,16062,18881,19137,20929,21185,25281,27073,27329,29121,29377,33217,33473,35265,35521,37313,37569,39361,39617,43328,43713,45538,45761,47586,47809,49634,49857])),([7,7,9,98,192,272,768],(decodeHints [18,584,1042,1554,2066,2578,3090,3602,4114,4626,5138,5650,16062,20740,21085,24850,26898,27154,30045,30312,33042,35090,35346,37138,37394,39186,39442,43282,45330,45586,47378,47634,49426,49682,52565,52849])),([7,7,9,98,192,512,768],(decodeHints [85,584,1109,1580,2133,2645,3157,3669,4181,4693,5205,5717,19025,20821,21085,24850,25173,26965,27154,30033,30293,33042,33365,35157,35346,37205,37461,39253,39509,43282,43605,45397,45586,47445,47701,49493,49749,51797,52565])),([7,7,9,132,192,272,768],(decodeHints [93,584,1117,1540,2141,2653,3165,3677,4189,4701,5213,5725,18834,19037,20829,21010,24850,25181,26973,27154,29277,30045,33042,33373,35165,35346,37213,37469,39261,39517,43282,43613,45405,45586,47453,47709,49501,49757,52561,52829]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_208 : K_208.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_209 : List (List ℕ × List (ℕ × ℕ)) := [([7,7,9,132,192,512,768],(decodeHints [81,583,1105,1539,2129,2641,3153,3665,4177,4689,5201,5713,18821,19025,20817,21003,24843,25169,26961,27147,29265,30033,33035,33361,35153,35339,37201,37457,39249,39505,43275,43601,45393,45579,47441,47697,49489,49745,51793,52561])),([7,7,24,32,98,132,272],(decodeHints [224,736,1248,1726,2272,2784,3296,3808,4320,4832,5344,5724,14816,15072,18912,19168,20960,21216,25056,27104,27360,29408,30176,34223,34517,35296,35552,37344,37600,39392,39648,43382,43744,47478,47840,49526,49888,51574,51936])),([7,7,24,32,98,132,272,512],(decodeHints [20484,26632,33967,36913,46126,47113,49155])),([7,7,24,98,132,192,272],(decodeHints [224,736,1248,1726,2272,2784,3296,3808,4320,4832,5344,5724,14816,15072,19887,20169,20960,21216,25056,26336,27104,27360,29152,29408,33248,33504,35296,35552,37344,38624,39392,39648,43382,43744,47478,47840,49526,49888,51574,51936])),([7,7,24,98,132,192,272,512],(decodeHints [19631,26774,34969,46084,49196,51349])),([7,7,32,98,132,272,768],(decodeHints [190,588,1214,1726,2238,2750,3262,3688,4286,4798,5310,5856,14782,15038,18878,20158,21182,21950,27070,27326,29118,29374,33214,33470,35262,35518,37310,37566,39358,39614,43328,43710,45536,45758,47584,47806,49454,49854])),([7,7,98,132,192,272,768],(decodeHints [190,584,1214,1629,2238,2750,3262,3774,4286,4798,5310,5856,18878,20158,20926,21182,25022,25278,27070,28350,29118,29374,33214,33470,35262,35518,37310,37566,39358,39614,43282,43710,45316,45758,47584,47806,49632,49854])),([7,9,24,32,98,192,272,768],(decodeHints [20552,26843,34892,45242,47324,49223,51412]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_209 : K_209.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_210 : List (List ℕ × List (ℕ × ℕ)) := [([7,9,24,32,98,192,512],(decodeHints [74,556,1098,1591,2122,2634,3146,3658,4170,4682,5194,5706,18773,19018,20810,21077,24917,25162,26954,27221,29258,30026,33109,33354,35146,35413,37194,37450,39498,40263,43349,43594,45386,45653,47434,47690,49482,49738,51530,51786])),([7,9,24,32,132,192,272,768],(decodeHints [20552,26846,35042,45239,47301,49380,51423])),([7,9,24,32,132,192,512],(decodeHints [71,515,1095,1547,2119,2631,3143,3655,4167,4679,5191,5703,18769,19015,20807,21073,24913,25159,26951,27217,28999,29255,33105,33351,35143,35409,37191,37447,40263,40519,43345,43591,45383,45649,47431,47687,49479,49735,51527,51783])),([7,24,32,98,132,192,272],(decodeHints [175,699,1199,1711,2223,2735,3247,3759,4271,4783,5295,5721,14767,15023,18863,19119,21167,21935,25007,25263,27055,27311,29103,29359,33199,33455,35247,35503,37295,37551,39343,40623,45392,45743,47440,47791,49488,49839,51536,51887]))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_210 : K_210.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((((((((K_0 ++ (K_1 ++ K_2)) ++ (K_3 ++ (K_4 ++ K_5))) ++ ((K_6 ++ (K_7 ++ K_8)) ++ ((K_9 ++ K_10) ++ (K_11 ++ K_12)))) ++ (((K_13 ++ (K_14 ++ K_15)) ++ (K_16 ++ (K_17 ++ K_18))) ++ ((K_19 ++ (K_20 ++ K_21)) ++ ((K_22 ++ K_23) ++ (K_24 ++ K_25))))) ++ ((((K_26 ++ (K_27 ++ K_28)) ++ (K_29 ++ (K_30 ++ K_31))) ++ ((K_32 ++ (K_33 ++ K_34)) ++ ((K_35 ++ K_36) ++ (K_37 ++ K_38)))) ++ (((K_39 ++ (K_40 ++ K_41)) ++ (K_42 ++ (K_43 ++ K_44))) ++ ((K_45 ++ (K_46 ++ K_47)) ++ ((K_48 ++ K_49) ++ (K_50 ++ K_51)))))) ++ (((((K_52 ++ (K_53 ++ K_54)) ++ (K_55 ++ (K_56 ++ K_57))) ++ ((K_58 ++ (K_59 ++ K_60)) ++ ((K_61 ++ K_62) ++ (K_63 ++ K_64)))) ++ (((K_65 ++ (K_66 ++ K_67)) ++ (K_68 ++ (K_69 ++ K_70))) ++ ((K_71 ++ (K_72 ++ K_73)) ++ ((K_74 ++ K_75) ++ (K_76 ++ K_77))))) ++ ((((K_78 ++ (K_79 ++ K_80)) ++ (K_81 ++ (K_82 ++ K_83))) ++ ((K_84 ++ (K_85 ++ K_86)) ++ ((K_87 ++ K_88) ++ (K_89 ++ K_90)))) ++ (((K_91 ++ (K_92 ++ K_93)) ++ ((K_94 ++ K_95) ++ (K_96 ++ K_97))) ++ ((K_98 ++ (K_99 ++ K_100)) ++ ((K_101 ++ K_102) ++ (K_103 ++ K_104))))))) ++ ((((((K_105 ++ (K_106 ++ K_107)) ++ (K_108 ++ (K_109 ++ K_110))) ++ ((K_111 ++ (K_112 ++ K_113)) ++ ((K_114 ++ K_115) ++ (K_116 ++ K_117)))) ++ (((K_118 ++ (K_119 ++ K_120)) ++ (K_121 ++ (K_122 ++ K_123))) ++ ((K_124 ++ (K_125 ++ K_126)) ++ ((K_127 ++ K_128) ++ (K_129 ++ K_130))))) ++ ((((K_131 ++ (K_132 ++ K_133)) ++ (K_134 ++ (K_135 ++ K_136))) ++ ((K_137 ++ (K_138 ++ K_139)) ++ ((K_140 ++ K_141) ++ (K_142 ++ K_143)))) ++ (((K_144 ++ (K_145 ++ K_146)) ++ ((K_147 ++ K_148) ++ (K_149 ++ K_150))) ++ ((K_151 ++ (K_152 ++ K_153)) ++ ((K_154 ++ K_155) ++ (K_156 ++ K_157)))))) ++ (((((K_158 ++ (K_159 ++ K_160)) ++ (K_161 ++ (K_162 ++ K_163))) ++ ((K_164 ++ (K_165 ++ K_166)) ++ ((K_167 ++ K_168) ++ (K_169 ++ K_170)))) ++ (((K_171 ++ (K_172 ++ K_173)) ++ (K_174 ++ (K_175 ++ K_176))) ++ ((K_177 ++ (K_178 ++ K_179)) ++ ((K_180 ++ K_181) ++ (K_182 ++ K_183))))) ++ ((((K_184 ++ (K_185 ++ K_186)) ++ (K_187 ++ (K_188 ++ K_189))) ++ ((K_190 ++ (K_191 ++ K_192)) ++ ((K_193 ++ K_194) ++ (K_195 ++ K_196)))) ++ (((K_197 ++ (K_198 ++ K_199)) ++ ((K_200 ++ K_201) ++ (K_202 ++ K_203))) ++ ((K_204 ++ (K_205 ++ K_206)) ++ ((K_207 ++ K_208) ++ (K_209 ++ K_210))))))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app (all_app (all_app c_0 (all_app c_1 c_2)) (all_app c_3 (all_app c_4 c_5))) (all_app (all_app c_6 (all_app c_7 c_8)) (all_app (all_app c_9 c_10) (all_app c_11 c_12)))) (all_app (all_app (all_app c_13 (all_app c_14 c_15)) (all_app c_16 (all_app c_17 c_18))) (all_app (all_app c_19 (all_app c_20 c_21)) (all_app (all_app c_22 c_23) (all_app c_24 c_25))))) (all_app (all_app (all_app (all_app c_26 (all_app c_27 c_28)) (all_app c_29 (all_app c_30 c_31))) (all_app (all_app c_32 (all_app c_33 c_34)) (all_app (all_app c_35 c_36) (all_app c_37 c_38)))) (all_app (all_app (all_app c_39 (all_app c_40 c_41)) (all_app c_42 (all_app c_43 c_44))) (all_app (all_app c_45 (all_app c_46 c_47)) (all_app (all_app c_48 c_49) (all_app c_50 c_51)))))) (all_app (all_app (all_app (all_app (all_app c_52 (all_app c_53 c_54)) (all_app c_55 (all_app c_56 c_57))) (all_app (all_app c_58 (all_app c_59 c_60)) (all_app (all_app c_61 c_62) (all_app c_63 c_64)))) (all_app (all_app (all_app c_65 (all_app c_66 c_67)) (all_app c_68 (all_app c_69 c_70))) (all_app (all_app c_71 (all_app c_72 c_73)) (all_app (all_app c_74 c_75) (all_app c_76 c_77))))) (all_app (all_app (all_app (all_app c_78 (all_app c_79 c_80)) (all_app c_81 (all_app c_82 c_83))) (all_app (all_app c_84 (all_app c_85 c_86)) (all_app (all_app c_87 c_88) (all_app c_89 c_90)))) (all_app (all_app (all_app c_91 (all_app c_92 c_93)) (all_app (all_app c_94 c_95) (all_app c_96 c_97))) (all_app (all_app c_98 (all_app c_99 c_100)) (all_app (all_app c_101 c_102) (all_app c_103 c_104))))))) (all_app (all_app (all_app (all_app (all_app (all_app c_105 (all_app c_106 c_107)) (all_app c_108 (all_app c_109 c_110))) (all_app (all_app c_111 (all_app c_112 c_113)) (all_app (all_app c_114 c_115) (all_app c_116 c_117)))) (all_app (all_app (all_app c_118 (all_app c_119 c_120)) (all_app c_121 (all_app c_122 c_123))) (all_app (all_app c_124 (all_app c_125 c_126)) (all_app (all_app c_127 c_128) (all_app c_129 c_130))))) (all_app (all_app (all_app (all_app c_131 (all_app c_132 c_133)) (all_app c_134 (all_app c_135 c_136))) (all_app (all_app c_137 (all_app c_138 c_139)) (all_app (all_app c_140 c_141) (all_app c_142 c_143)))) (all_app (all_app (all_app c_144 (all_app c_145 c_146)) (all_app (all_app c_147 c_148) (all_app c_149 c_150))) (all_app (all_app c_151 (all_app c_152 c_153)) (all_app (all_app c_154 c_155) (all_app c_156 c_157)))))) (all_app (all_app (all_app (all_app (all_app c_158 (all_app c_159 c_160)) (all_app c_161 (all_app c_162 c_163))) (all_app (all_app c_164 (all_app c_165 c_166)) (all_app (all_app c_167 c_168) (all_app c_169 c_170)))) (all_app (all_app (all_app c_171 (all_app c_172 c_173)) (all_app c_174 (all_app c_175 c_176))) (all_app (all_app c_177 (all_app c_178 c_179)) (all_app (all_app c_180 c_181) (all_app c_182 c_183))))) (all_app (all_app (all_app (all_app c_184 (all_app c_185 c_186)) (all_app c_187 (all_app c_188 c_189))) (all_app (all_app c_190 (all_app c_191 c_192)) (all_app (all_app c_193 c_194) (all_app c_195 c_196)))) (all_app (all_app (all_app c_197 (all_app c_198 c_199)) (all_app (all_app c_200 c_201) (all_app c_202 c_203))) (all_app (all_app c_204 (all_app c_205 c_206)) (all_app (all_app c_207 c_208) (all_app c_209 c_210))))))))

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
    refine ⟨pt 10 (pairCode (0,0)),pt 10 (pairCode (0,3)),?_⟩
    rw [he (0,0) (by decide +kernel),he (0,3) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 7 8 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 7 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end PEqualNP.Outside.L_meta_19374.Probes

open PEqualNP.Outside.L_meta_19374.Probes in
theorem PEqualNP.Outside.L_meta_19374 (C : PEqualNP.CircuitLowerBounds.Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ 7) : ¬ Matches C := coreLower C hfan hsize
