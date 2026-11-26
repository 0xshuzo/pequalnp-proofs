import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19367.Probes

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
def probeRoots : List (List Nat × Nat) := [([7,9,120,324,384,528,1536],201961),([7,9,120,324,384,1058,1536],200937),([7,120,324,384,528,1058,1536],32870),([0,7,9,120,324,384,528],201961),([0,7,9,120,324,384,1058],200937),([0,7,120,324,384,528,1058],32870),([7,9,120,128,324,384,528],103457),([7,120,128,324,384,528,1058],32870),([0,7,9,120,324,528,1536],201961),([0,7,9,120,324,1058,1536],200937),([0,7,120,324,528,1058,1536],32870),([7,9,120,128,324,528,1536],103457),([7,120,128,324,528,1058,1536],32870),([0,7,9,120,128,528,1058],303301),([0,7,9,120,128,324,528],205093),([0,7,9,120,324,528,1058],205093),([0,7,9,120,128,324,1058],201001),([0,7,120,128,324,528,1058],32870),([7,9,120,128,324,528,1058],205093),([0,7,9,324,384,528,1536],234697),([0,7,9,324,384,1058,1536],233673),([0,7,324,384,528,1058,1536],32870),([7,9,128,384,528,1058,1536],37985),([7,9,128,324,384,528,1536],103457),([7,9,324,384,528,1058,1536],37985),([7,9,128,324,384,1058,1536],37985),([7,128,324,384,528,1058,1536],32870),([0,9,120,324,384,528,1536],201961),([0,9,120,324,384,1058,1536],200937),([0,120,324,384,528,1058,1536],32870),([9,120,128,384,528,1058,1536],98342),([9,120,128,324,384,528,1536],98342),([9,120,324,384,528,1058,1536],98342),([9,120,128,324,384,1058,1536],98342),([120,128,324,384,528,1058,1536],32870)]
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
def samplePairs : List (Fin 5 × Fin 5) := [(0, 0), (0, 3), (0, 4), (1, 0), (1, 1), (1, 3), (1, 4), (2, 2), (2, 4), (3, 1), (3, 3)]
def points := samplePairs.map pairCode
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) = (7577150 : ℕ).testBit (5 * p.1.val + p.2.val)
def M_ : ℕ := 2047

def Y_ : ℕ := 718

def XS_ : List ℕ := [7, 120, 384, 1536, 0, 9, 528, 128, 1058, 324]

def PD_ : List (ℕ × ℕ) := [(1, 937), (2, 125), (3, 151), (4, 98), (5, 24), (6, 5), (7, 11), (8, 4), (9, 3)]

def PM_ : List (ℕ × ℕ) := [(0, 718), (4, 718), (5, 718), (8, 718), (10, 718)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,7,73,1406] BT.lf) [3,9,71,1406] BT.lf) [3,15,324,640,1146] (BT.nd (BT.nd BT.lf [3,87,1382] BT.lf) [3,327,905] BT.lf)) [3,393,839] (BT.nd (BT.nd (BT.nd BT.lf [4,7,9,64,1406] BT.lf) [4,7,9,324,640,1146] BT.lf) [4,7,73,120,1382] (BT.nd (BT.nd BT.lf [4,7,73,324,1146] BT.lf) [4,7,73,380,1058] BT.lf))) [4,7,80,1382] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7,265,324,1146] BT.lf) [4,7,324,393,1274] BT.lf) [4,7,324,905] (BT.nd (BT.nd BT.lf [4,7,324,909] BT.lf) [4,7,324,1138] BT.lf)) [4,7,332,1146] (BT.nd (BT.nd (BT.nd BT.lf [4,7,333,1146,1406] BT.lf) [4,7,333,1147] BT.lf) [4,7,393,836] (BT.nd (BT.nd BT.lf [4,9,71,120,1382] BT.lf) [4,9,71,324,1146] BT.lf)))) [4,9,71,380,1058] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,327,384,1406] BT.lf) [4,9,327,896] BT.lf) [4,9,327,1151] (BT.nd (BT.nd BT.lf [4,9,384,839] BT.lf) [4,15,120,324,640,1058] BT.lf)) [4,15,128,324,512,1146] (BT.nd (BT.nd (BT.nd BT.lf [4,15,128,632,1058,1860] BT.lf) [4,15,324,901] BT.lf) [4,15,324,1146] (BT.nd (BT.nd BT.lf [4,15,1146,1723] BT.lf) [4,87,324,1058] BT.lf))) [4,121,663,1058] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,249,535,1058] BT.lf) [4,324,393,519] BT.lf) [4,324,1146,2032] (BT.nd (BT.nd BT.lf [4,327,384,521] BT.lf) [4,327,393,512] BT.lf)) [4,327,393,1146] (BT.nd (BT.nd (BT.nd BT.lf [4,327,1058,1929] BT.lf) [4,380,1058,1936] BT.lf) [4,380,1442,1552] (BT.nd (BT.nd BT.lf [5,0,15,324,1146] BT.lf) [5,7,8,324,1146] BT.lf))))) [5,7,9,64,120,1382] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,64,324,1146] BT.lf) [5,7,9,64,380,1058] BT.lf) [5,7,9,120,324,640,1058] (BT.nd (BT.nd BT.lf [5,7,9,120,324,1074] BT.lf) [5,7,9,120,324,1314] BT.lf)) [5,7,9,120,324,1406] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,120,528,1314] BT.lf) [5,7,9,120,1348] BT.lf) [5,7,9,128,324,512,1146] (BT.nd (BT.nd BT.lf [5,7,9,128,632,1058,1860] BT.lf) [5,7,9,256,324,1146] BT.lf))) [5,7,9,324,384,1274] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,324,384,1406] BT.lf) [5,7,9,324,896] BT.lf) [5,7,9,324,901] (BT.nd (BT.nd BT.lf [5,7,9,324,1144] BT.lf) [5,7,9,324,1146] BT.lf)) [5,7,9,324,1146,1406] (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,324,1147] BT.lf) [5,7,9,324,1151] BT.lf) [5,7,9,327,1146] (BT.nd (BT.nd BT.lf [5,7,9,333,1146] BT.lf) [5,7,9,380,912,1058] BT.lf)))) [5,7,9,384,836] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,9,632,1860] BT.lf) [5,7,9,1146,1723] BT.lf) [5,7,15,324,1146] (BT.nd (BT.nd BT.lf [5,7,73,120,324,1058] BT.lf) [5,7,80,324,1058] BT.lf)) [5,7,112,324,1058] (BT.nd (BT.nd (BT.nd BT.lf [5,7,120,137,324,1442] BT.lf) [5,7,120,265,324,1058] BT.lf) [5,7,120,324,333,1146] (BT.nd (BT.nd BT.lf [5,7,120,324,393,1186] BT.lf) [5,7,120,324,1033] BT.lf))) [5,7,120,324,1074] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,120,332,1058] BT.lf) [5,7,120,333,380,1058] BT.lf) [5,7,120,333,1067] (BT.nd (BT.nd BT.lf [5,7,120,333,1382] BT.lf) [5,7,120,852,1382] BT.lf)) [5,7,120,852,1586] (BT.nd (BT.nd (BT.nd BT.lf [5,7,120,1067,1382] BT.lf) [5,7,120,1382,1586] BT.lf) [5,7,121,333,1058] (BT.nd BT.lf [5,7,121,380,528,1058] BT.lf)))))) [5,7,121,656,1058] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,128,324,393,1146] BT.lf) [5,7,128,324,632,1058,1545] BT.lf) [5,7,137,324,384,1146] (BT.nd (BT.nd BT.lf [5,7,137,324,1146] BT.lf) [5,7,248,324,393,1058] BT.lf)) [5,7,248,528,1058,1545] (BT.nd (BT.nd (BT.nd BT.lf [5,7,249,528,1058] BT.lf) [5,7,324,333,384,1146] BT.lf) [5,7,324,333,1146] (BT.nd (BT.nd BT.lf [5,7,324,384,521] BT.lf) [5,7,324,384,1074] BT.lf))) [5,7,324,393,512] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,324,393,1146] BT.lf) [5,7,324,632,1545] BT.lf) [5,7,324,1058,1929] (BT.nd (BT.nd BT.lf [5,7,324,1058,1935] BT.lf) [5,7,324,1146,1586] BT.lf)) [5,7,324,1146,2038] (BT.nd (BT.nd (BT.nd BT.lf [5,7,380,912,1058] BT.lf) [5,7,393,1058,1860] BT.lf) [5,9,15,324,1146] (BT.nd (BT.nd BT.lf [5,9,23,120,324,1058] BT.lf) [5,9,71,120,324,1058] BT.lf)))) [5,9,120,128,324,535,1570] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,120,128,535,1058,1860] BT.lf) [5,9,120,135,324,1442] BT.lf) [5,9,120,135,528,1442] (BT.nd (BT.nd BT.lf [5,9,120,324,535,1570] BT.lf) [5,9,120,324,663] BT.lf)) [5,9,120,327,384,1382] (BT.nd (BT.nd (BT.nd BT.lf [5,9,120,327,912] BT.lf) [5,9,120,327,1063] BT.lf) [5,9,120,535,1058,1860] (BT.nd (BT.nd BT.lf [5,9,120,535,1860] BT.lf) [5,9,120,663,1058] BT.lf))) [5,9,120,1442,1860] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,127,327,1058] BT.lf) [5,9,135,324,384,1146] BT.lf) [5,9,135,324,1146] (BT.nd (BT.nd BT.lf [5,9,248,535,1058] BT.lf) [5,9,324,327,384,1146] BT.lf)) [5,9,324,384,519] (BT.nd (BT.nd (BT.nd BT.lf [5,9,324,384,1144] BT.lf) [5,9,324,1146,2040] BT.lf) [5,9,327,380,384,1058] (BT.nd (BT.nd BT.lf [5,9,327,384,512] BT.lf) [5,9,327,384,1146] BT.lf))))) [5,9,327,1058,1920] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,120,128,324,512,1058] BT.lf) [5,15,120,128,324,528,1570] BT.lf) [5,15,120,128,528,1058,1860] (BT.nd (BT.nd BT.lf [5,15,120,324,989] BT.lf) [5,15,120,324,1058] BT.lf)) [5,15,120,324,1146] (BT.nd (BT.nd (BT.nd BT.lf [5,15,120,324,1382] BT.lf) [5,15,120,1058,1382] BT.lf) [5,15,120,1058,1723] (BT.nd (BT.nd BT.lf [5,15,128,324,528,1146,1536] BT.lf) [5,15,128,324,632,1058,1536] BT.lf))) [5,15,128,324,1146] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,324,384,1146] BT.lf) [5,15,324,528,1146] BT.lf) [5,15,324,1058,1146] (BT.nd (BT.nd BT.lf [5,15,324,1058,1927] BT.lf) [5,15,324,1146] BT.lf)) [5,15,324,1146,1536] (BT.nd (BT.nd (BT.nd BT.lf [5,23,120,324,1058] BT.lf) [5,23,324,384,1058] BT.lf) [5,120,135,528,1058,1545] (BT.nd (BT.nd BT.lf [5,120,137,324,535] BT.lf) [5,120,137,535,1058] BT.lf)))) [5,120,324,384,1033] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,120,324,393,535] BT.lf) [5,120,324,535,1570] BT.lf) [5,120,324,535,1586] (BT.nd (BT.nd BT.lf [5,120,324,912,1545] BT.lf) [5,120,324,1058,1936] BT.lf)) [5,120,324,1058,2032] (BT.nd (BT.nd (BT.nd BT.lf [5,120,324,1063,1545] BT.lf) [5,120,324,1442,1552] BT.lf) [5,120,327,393,528] (BT.nd (BT.nd BT.lf [5,120,327,393,1058] BT.lf) [5,120,528,1442,1860] BT.lf))) [5,120,535,852,1058] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,120,535,1058,1860] BT.lf) [5,121,128,535,1058] BT.lf) [5,121,135,528,1058] (BT.nd (BT.nd BT.lf [5,121,324,535,1058] BT.lf) [5,127,324,535,1058] BT.lf)) [5,127,380,528,1058] (BT.nd (BT.nd (BT.nd BT.lf [5,324,384,535,1570] BT.lf) [5,324,384,632,1545] BT.lf) [5,324,535,1058,1920] (BT.nd BT.lf [5,327,384,1058,1545] BT.lf))))))) [5,327,393,528,1536] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,327,393,1058,1536] BT.lf) [5,380,384,1058,1552] BT.lf) [5,380,528,1058,1920] (BT.nd (BT.nd BT.lf [5,380,528,1442,1536] BT.lf) [5,380,912,1058,1536] BT.lf)) [5,384,535,1058,1860] (BT.nd (BT.nd (BT.nd BT.lf [6,0,7,9,324,1146] BT.lf) [6,0,15,120,324,1058] BT.lf) [6,7,8,120,324,1058] (BT.nd (BT.nd BT.lf [6,7,9,16,120,324,1058] BT.lf) [6,7,9,64,120,324,1058] BT.lf))) [6,7,9,120,128,324,512,1058] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,120,128,324,528,1570] BT.lf) [6,7,9,120,128,324,1442] BT.lf) [6,7,9,120,128,528,1058,1860] (BT.nd (BT.nd BT.lf [6,7,9,120,128,528,1442] BT.lf) [6,7,9,120,256,324,1058] BT.lf)) [6,7,9,120,256,528,1058] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,120,324,380,1058] BT.lf) [6,7,9,120,324,384,1186] BT.lf) [6,7,9,120,324,384,1382] (BT.nd (BT.nd BT.lf [6,7,9,120,324,528,1570] BT.lf) [6,7,9,120,324,656] BT.lf)))) [6,7,9,120,324,912] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,120,324,912,1058] BT.lf) [6,7,9,120,324,989] BT.lf) [6,7,9,120,324,1024] (BT.nd (BT.nd BT.lf [6,7,9,120,324,1058] BT.lf) [6,7,9,120,324,1058,1664] BT.lf)) [6,7,9,120,324,1063] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,120,324,1067] BT.lf) [6,7,9,120,324,1146] BT.lf) [6,7,9,120,324,1382] (BT.nd (BT.nd BT.lf [6,7,9,120,327,1058] BT.lf) [6,7,9,120,333,1058] BT.lf))) [6,7,9,120,380,528,1058] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,120,528,1058,1664] BT.lf) [6,7,9,120,528,1058,1860] BT.lf) [6,7,9,120,528,1860] (BT.nd (BT.nd BT.lf [6,7,9,120,656,1058] BT.lf) [6,7,9,120,1058,1382] BT.lf)) [6,7,9,120,1058,1723] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,121,324,1058] BT.lf) [6,7,9,127,324,1058] BT.lf) [6,7,9,128,324,384,1146] (BT.nd (BT.nd BT.lf [6,7,9,128,324,528,1146,1536] BT.lf) [6,7,9,128,324,632,1058,1536] BT.lf))))) [6,7,9,128,324,1146] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,248,324,384,1058] BT.lf) [6,7,9,248,528,1058] BT.lf) [6,7,9,248,528,1058,1536] (BT.nd (BT.nd BT.lf [6,7,9,324,380,384,1058] BT.lf) [6,7,9,324,384,512] BT.lf)) [6,7,9,324,384,1146] (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,324,528,1146] BT.lf) [6,7,9,324,632,1536] BT.lf) [6,7,9,324,1058,1146] (BT.nd (BT.nd BT.lf [6,7,9,324,1058,1920] BT.lf) [6,7,9,324,1058,1927] BT.lf))) [6,7,9,324,1146] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,9,324,1146,1536] BT.lf) [6,7,9,380,384,528,1058] BT.lf) [6,7,9,384,1058,1860] (BT.nd (BT.nd BT.lf [6,7,15,120,324,1058] BT.lf) [6,7,16,120,324,1058] BT.lf)) [6,7,16,324,384,1058] (BT.nd (BT.nd (BT.nd BT.lf [6,7,120,121,324,528,1058] BT.lf) [6,7,120,128,324,393,1058] BT.lf) [6,7,120,128,324,528,1058,1545] (BT.nd (BT.nd BT.lf [6,7,120,128,528,1058,1545] BT.lf) [6,7,120,137,324,384,1058] BT.lf)))) [6,7,120,137,324,528] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,120,137,324,1058] BT.lf) [6,7,120,137,528,1058] BT.lf) [6,7,120,324,333,384,1058] (BT.nd (BT.nd BT.lf [6,7,120,324,333,1058] BT.lf) [6,7,120,324,393,528] BT.lf)) [6,7,120,324,393,1058] (BT.nd (BT.nd (BT.nd BT.lf [6,7,120,324,528,989] BT.lf) [6,7,120,324,528,1058] BT.lf) [6,7,120,324,528,1058,1545] (BT.nd (BT.nd BT.lf [6,7,120,324,528,1382] BT.lf) [6,7,120,324,528,1545] BT.lf))) [6,7,120,324,528,1570] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,120,324,528,1586] BT.lf) [6,7,120,324,535,1058] BT.lf) [6,7,120,324,656,1058] (BT.nd (BT.nd BT.lf [6,7,120,324,852,1058] BT.lf) [6,7,120,324,912,1058] BT.lf)) [6,7,120,324,1058,1067] (BT.nd (BT.nd (BT.nd BT.lf [6,7,120,324,1058,1519] BT.lf) [6,7,120,324,1058,1545] BT.lf) [6,7,120,324,1058,1552] (BT.nd BT.lf [6,7,120,324,1058,1586] BT.lf)))))) [6,7,120,324,1058,2038] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,120,380,528,1058] BT.lf) [6,7,120,528,852,1058] BT.lf) [6,7,120,528,1058,1382] (BT.nd (BT.nd BT.lf [6,7,120,528,1058,1723] BT.lf) [6,7,120,528,1058,1860] BT.lf)) [6,7,121,128,528,1058] (BT.nd (BT.nd (BT.nd BT.lf [6,7,121,324,528,1058] BT.lf) [6,7,127,324,528,1058] BT.lf) [6,7,248,324,528,1058] (BT.nd (BT.nd BT.lf [6,7,324,384,528,1570] BT.lf) [6,7,324,384,1058,1545] BT.lf))) [6,7,324,393,528,1536] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,324,393,1058,1536] BT.lf) [6,7,324,528,1058,1146] BT.lf) [6,7,324,528,1058,1920] (BT.nd (BT.nd BT.lf [6,7,324,528,1058,1927] BT.lf) [6,7,380,384,528,1058] BT.lf)) [6,7,384,528,1058,1860] (BT.nd (BT.nd (BT.nd BT.lf [6,9,15,120,324,1058] BT.lf) [6,9,120,127,324,1058] BT.lf) [6,9,120,128,324,535] (BT.nd (BT.nd BT.lf [6,9,120,128,324,535,1058,1536] BT.lf) [6,9,120,128,535,1058] BT.lf)))) [6,9,120,135,324,384,1058] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,9,120,135,324,528] BT.lf) [6,9,120,135,324,1058] BT.lf) [6,9,120,135,384,528,1058] (BT.nd (BT.nd BT.lf [6,9,120,135,528,1058] BT.lf) [6,9,120,135,528,1058,1536] BT.lf)) [6,9,120,324,327,384,1058] (BT.nd (BT.nd (BT.nd BT.lf [6,9,120,324,384,535] BT.lf) [6,9,120,324,384,535,1058] BT.lf) [6,9,120,324,384,1024] (BT.nd (BT.nd BT.lf [6,9,120,324,535,1058] BT.lf) [6,9,120,324,535,1058,1536] BT.lf))) [6,9,120,324,535,1536] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,9,120,324,912,1536] BT.lf) [6,9,120,324,1058,1920] BT.lf) [6,9,120,324,1058,2040] (BT.nd (BT.nd BT.lf [6,9,120,324,1063,1536] BT.lf) [6,9,120,324,1442,1536] BT.lf)) [6,9,120,327,384,528] (BT.nd (BT.nd (BT.nd BT.lf [6,9,120,327,384,1058] BT.lf) [6,9,120,384,1058,1860] BT.lf) [6,9,324,384,632,1536] (BT.nd BT.lf [6,9,327,384,528,1536] BT.lf))))) [6,9,327,384,1058,1536] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,120,128,324,528,1058,1536] BT.lf) [6,15,120,128,324,1058] BT.lf) [6,15,120,324,384,1058] (BT.nd (BT.nd BT.lf [6,15,120,324,528,1058] BT.lf) [6,15,120,324,1058] BT.lf)) [6,15,120,324,1058,1536] (BT.nd (BT.nd (BT.nd BT.lf [6,120,127,324,528,1058] BT.lf) [6,120,324,384,528,1545] BT.lf) [6,120,324,384,1058,1552] (BT.nd (BT.nd BT.lf [6,120,324,528,535,1058] BT.lf) [6,120,324,528,1058,1920] BT.lf))) [6,120,324,528,1058,2040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,120,324,528,1442,1536] BT.lf) [6,120,324,535,1058,1536] BT.lf) [6,120,324,912,1058,1536] (BT.nd (BT.nd BT.lf [6,120,384,528,1058,1860] BT.lf) [6,324,384,535,1058,1536] BT.lf)) [6,380,384,528,1058,1536] (BT.nd (BT.nd (BT.nd BT.lf [7,0,7,9,120,324,1058] BT.lf) [7,0,7,120,324,528,1058] BT.lf) [7,7,9,120,128,324,384,1058] (BT.nd (BT.nd BT.lf [7,7,9,120,128,324,528] BT.lf) [7,7,9,120,128,324,528,1058,1536] BT.lf)))) [7,7,9,120,128,324,1058] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,7,9,120,128,324,1058,1536] BT.lf) [7,7,9,120,128,384,528,1058] BT.lf) [7,7,9,120,128,528,1058] (BT.nd (BT.nd BT.lf [7,7,9,120,128,528,1058,1536] BT.lf) [7,7,9,120,324,384,528] BT.lf)) [7,7,9,120,324,384,528,1058] (BT.nd (BT.nd (BT.nd BT.lf [7,7,9,120,324,384,1058] BT.lf) [7,7,9,120,324,528,1058] BT.lf) [7,7,9,120,324,528,1058,1536] (BT.nd (BT.nd BT.lf [7,7,9,120,324,528,1536] BT.lf) [7,7,9,120,324,1058] BT.lf))) [7,7,9,120,324,1058,1536] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,7,9,324,384,528,1536] BT.lf) [7,7,9,324,384,1058,1536] BT.lf) [7,7,120,128,324,528,1058] (BT.nd (BT.nd BT.lf [7,7,120,324,384,528,1058] BT.lf) [7,7,120,324,528,1058] BT.lf)) [7,7,120,324,528,1058,1536] (BT.nd (BT.nd (BT.nd BT.lf [7,7,324,384,528,1058,1536] BT.lf) [7,9,120,324,384,528,1536] BT.lf) [7,9,120,324,384,1058,1536] (BT.nd BT.lf [7,120,324,384,528,1058,1536] BT.lf))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,7,73,1406],[(56,32997)]),([3,9,71,1406],[(56,32997)]),([3,15,324,640,1146],[]),([3,87,1382],[(0,32870),(2,98342),(4,32870),(6,103457)]),([3,327,905],[(0,102433),(2,98341),(4,102433),(6,32869)]),([3,393,839],[(0,36961),(2,32869),(4,36961),(6,98341)]),([4,7,9,64,1406],[(56,32997)]),([4,7,9,324,640,1146],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,73,120,1382],[(56,33001)]),([4,7,73,324,1146],[(56,32997)]),([4,7,73,380,1058],[(56,33003)]),([4,7,80,1382],[(0,32870),(2,98342),(4,32870),(6,102598),(8,32870),(10,103457),(57,32870),(58,32870)]),([4,7,265,324,1146],[(72,102465)]),([4,7,324,393,1274],[(56,102465)]),([4,7,324,905],[(0,102433),(2,98341),(4,102433),(6,106693),(8,102433),(10,32869),(57,102433),(58,102433)]),([4,7,324,909],[(0,102433),(2,98341),(4,102433),(6,106561),(8,102433),(10,32869)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([4,7,324,1138],[(0,32869),(2,98341),(4,32869),(6,106561),(8,32869),(10,102433)]),([4,7,332,1146],[(0,32997),(2,229413),(4,32997),(6,237633),(8,32997),(10,233505)]),([4,7,333,1146,1406],[(84,32997),(100,98533),(108,32997)]),([4,7,333,1147],[(0,106561),(2,98341),(4,106561),(6,32869),(8,106561),(10,65641)]),([4,7,393,836],[(0,200809),(2,98341),(4,200809),(6,32869),(8,200809),(10,106693),(73,36961),(74,200809)]),([4,9,71,120,1382],[(56,33001)]),([4,9,71,324,1146],[(56,32997)]),([4,9,71,380,1058],[(56,33003)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,327,384,1406],[(56,33061),(72,102441)]),([4,9,327,896],[(0,233513),(2,32869),(4,233513),(6,98341),(8,233513),(10,41189),(73,102433),(74,233513)]),([4,9,327,1151],[(0,41189),(2,32869),(4,41189),(6,98341),(8,41189),(10,233513),(74,41189),(77,41189)]),([4,9,384,839],[(0,36961),(2,32869),(4,36961),(6,41189),(8,36961),(10,98341),(57,36961),(58,36961)]),([4,15,120,324,640,1058],[]),([4,15,128,324,512,1146],[]),([4,15,128,632,1058,1860],[]),([4,15,324,901],[(0,233505),(2,229413),(4,233505),(6,237633),(8,233505),(10,32997)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,324,1146],[(0,32997),(2,229413),(4,32997),(6,237633),(8,32997),(10,233505)]),([4,15,1146,1723],[(0,237633),(2,229413),(4,237633),(6,237633),(8,237633),(10,32997)]),([4,87,324,1058],[(0,32870),(2,98342),(4,32870),(6,106561),(8,32870),(10,103457),(81,65641),(82,32870)]),([4,121,663,1058],[(0,43105),(2,65641),(4,43105),(6,98347),(8,43105),(10,43105),(73,106561),(78,41057),(82,106529)]),([4,249,535,1058],[(0,43105),(2,65641),(4,43105),(6,98347),(8,43105),(10,43105),(73,106561),(78,41057),(82,106529)]),([4,324,393,519],[(0,36961),(2,106693),(4,36961),(6,32869),(8,36961),(10,98341),(73,200809),(74,36961)]),([4,324,1146,2032],[(0,229413),(2,229413),(4,229413),(6,229413),(8,229413),(10,32997)]),([4,327,384,521],[(0,102433),(2,98341),(4,102433),(6,41189),(8,102433),(10,32869),(81,233513),(82,102433)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([4,327,393,512],[(0,102433),(2,98341),(4,102433),(6,32869),(8,102433),(10,102433),(73,36961),(74,102433),(81,102433),(82,36961)]),([4,327,393,1146],[(0,102465),(2,229413),(4,102465),(6,65637),(8,102465),(10,102465),(74,102433),(82,102433)]),([4,327,1058,1929],[(0,102465),(2,102465),(4,102465),(6,102465),(8,102465),(10,37985),(58,102433),(82,102465),(85,102433)]),([4,380,1058,1936],[(0,229419),(2,229419),(4,229419),(6,229419),(8,229419),(10,32838)]),([4,380,1442,1552],[(0,294955),(2,37953),(4,294955),(6,294955),(8,294955),(10,32838)]),([5,0,15,324,1146],[(0,32997),(2,32997),(4,32997),(6,229413),(8,32997),(10,237633),(12,32997),(14,233505),(57,32997),(58,32997),(61,32997),(73,32997),(74,32997),(77,32997),(97,65769),(98,32997),(101,32997)]),([5,7,8,324,1146],[(0,32997),(2,229413),(4,32997),(6,32997),(8,32997),(10,237633),(12,32997),(14,233505),(57,32997),(58,32997),(81,32997),(82,32997),(106,32997),(109,32997)]),([5,7,9,64,120,1382],[(56,33001)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,64,324,1146],[(56,32997),(112,205029),(144,205029)]),([5,7,9,64,380,1058],[(56,33003)]),([5,7,9,120,324,640,1058],[]),([5,7,9,120,324,1074],[(56,33003),(80,43105),(144,205029)]),([5,7,9,120,324,1314],[(56,33003)]),([5,7,9,120,324,1406],[(56,33003),(104,65771)]),([5,7,9,120,528,1314],[(80,41057),(96,41157),(116,37985)]),([5,7,9,120,1348],[(0,200937),(2,200937),(4,200937),(6,32869),(8,200937),(10,233673),(12,200937),(14,237765),(57,200937),(73,200937),(74,200937),(82,200937),(98,200937),(101,200745),(105,102433),(106,200937)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,128,324,512,1146],[]),([5,7,9,128,632,1058,1860],[]),([5,7,9,256,324,1146],[(56,32997),(96,102465),(112,205029)]),([5,7,9,324,384,1274],[(56,33061),(72,233545),(112,205093)]),([5,7,9,324,384,1406],[(56,33061),(80,65829),(104,102601)]),([5,7,9,324,896],[(0,233673),(2,98341),(4,233673),(6,32869),(8,233673),(10,237765),(12,233673),(14,205029),(73,233545),(74,233673),(81,233673),(82,233673),(97,36961),(98,233673),(105,102433),(106,233673)]),([5,7,9,324,901],[(0,233673),(2,233673),(4,233673),(6,233673),(8,233673),(10,237765),(12,233673),(14,205029),(57,233569),(58,233505),(74,233673),(81,233673),(82,233673),(98,233673),(105,65769),(106,233673)]),([5,7,9,324,1144],[(0,205029),(2,205029),(4,205029),(6,32869),(8,205029),(10,237765),(12,205029),(14,233673),(57,98533),(74,205029),(77,98341),(81,205029),(82,205029),(97,98341),(98,205029),(106,205029)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,324,1146],[(0,205029),(2,205029),(4,205029),(6,205029),(8,205029),(10,237765),(12,205029),(14,233673),(57,98533),(58,32997),(74,205029),(81,205029),(82,205029),(98,205029),(106,205029),(109,32997)]),([5,7,9,324,1146,1406],[(56,37089),(132,98533),(140,32997),(148,205029),(156,205029)]),([5,7,9,324,1147],[(0,205029),(2,98341),(4,205029),(6,32869),(8,205029),(10,237765),(12,205029),(14,233673),(74,205029),(81,205029),(82,205029),(98,205029),(106,205029),(109,205029)]),([5,7,9,324,1151],[(0,205029),(2,98341),(4,205029),(6,32869),(8,205029),(10,237765),(12,205029),(14,233673),(73,73957),(74,205029),(81,205029),(82,205029),(98,205029),(101,205029),(106,205029),(109,205029)]),([5,7,9,327,1146],[(0,205029),(2,205029),(4,205029),(6,65637),(8,205029),(10,237765),(12,205029),(14,233673),(57,205029),(74,205029),(77,205029),(82,205029),(97,37097),(98,205029),(106,205029)]),([5,7,9,333,1146],[(0,205029),(2,205029),(4,205029),(6,205029),(8,205029),(10,237765),(12,205029),(14,233673),(57,98533),(62,106725),(74,205029),(82,205029),(85,205029),(98,205029),(105,102633),(106,205029)]),([5,7,9,380,912,1058],[(56,32966),(116,37985)]),([5,7,9,384,836],[(0,200937),(2,98341),(4,200937),(6,32869),(8,200937),(10,205029),(12,200937),(14,237765),(73,200937),(74,200937),(81,200937),(82,200937),(97,36961),(98,200937),(105,102433),(106,200937)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,9,632,1860],[(0,200937),(2,200937),(4,200937),(6,32869),(8,200937),(10,200937),(12,200937),(14,205029),(57,200937),(73,200937),(74,200937),(82,200937),(98,200937),(101,200745),(105,102433),(106,200937)]),([5,7,9,1146,1723],[(0,237765),(2,237765),(4,237765),(6,237765),(8,237765),(10,237765),(12,237765),(14,205029),(57,237765),(58,237633),(74,237765),(82,237765),(85,237633),(98,237765),(106,237765),(109,237765)]),([5,7,15,324,1146],[(0,32997),(2,32997),(4,32997),(6,32997),(8,32997),(10,237633),(12,32997),(14,233505),(57,32997),(58,32997),(61,32997),(73,32997),(77,32997),(81,32997),(97,65769),(101,98533),(109,205029)]),([5,7,73,120,324,1058],[(56,33003)]),([5,7,80,324,1058],[(0,32870),(2,98342),(4,32870),(6,102601),(8,32870),(10,106561),(12,32870),(14,103457),(57,32870),(58,32870),(105,204901),(106,32870),(113,65641),(114,32870)]),([5,7,112,324,1058],[(0,32875),(2,98347),(4,32875),(6,102601),(8,32875),(10,106561),(12,32875),(14,108577),(57,32875),(58,32875),(105,204901),(106,32875),(113,65641),(114,32875)]),([5,7,120,137,324,1442],[(72,33067)]),([5,7,120,265,324,1058],[(96,102465)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,120,324,333,1146],[(80,106731),(108,32997),(136,205029),(144,65771)]),([5,7,120,324,393,1186],[(72,102465)]),([5,7,120,324,1033],[(0,102433),(2,102433),(4,102433),(6,233579),(8,102433),(10,237765),(12,102433),(14,32869),(57,102433),(58,102433),(74,102433),(77,102433),(97,200937),(113,200937),(114,102433)]),([5,7,120,324,1074],[(0,32869),(2,229419),(4,32869),(6,32869),(8,32869),(10,237633),(12,32869),(14,102433),(57,32869),(58,32869),(82,32869),(85,32869),(105,65769),(113,65769),(114,32869)]),([5,7,120,332,1058],[(0,33003),(2,229419),(4,33003),(6,233577),(8,33003),(10,237633),(12,33003),(14,239649),(57,33003),(58,33003),(105,106725),(106,33003),(113,65769),(114,33003)]),([5,7,120,333,380,1058],[(56,65574),(84,33003),(116,33003),(136,106731),(152,65771)]),([5,7,120,333,1067],[(0,103457),(2,103457),(4,103457),(6,233673),(8,103457),(10,32870),(12,103457),(14,103457),(57,103457),(58,103457),(105,205029),(106,102433)]),([5,7,120,333,1382],[(0,65771),(2,65771),(4,65771),(6,233673),(8,65771),(10,65771),(12,65771),(14,239681),(57,65771),(58,65771),(74,33003),(86,33001),(101,102625),(106,65771)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,120,852,1382],[(0,32870),(2,229419),(4,32870),(6,299209),(8,32870),(10,32870),(12,32870),(14,201829),(57,32870),(58,32870),(74,32870),(85,32870),(86,32870)]),([5,7,120,852,1586],[(0,32870),(2,229419),(4,32870),(6,299209),(8,32870),(10,32870),(12,32870),(14,65769),(57,32870),(58,32870),(82,32869),(85,32870)]),([5,7,120,1067,1382],[(0,32870),(2,32870),(4,32870),(6,233673),(8,32870),(10,32870),(12,32870),(14,102598),(57,32870),(58,32870),(74,32870),(81,32870),(86,32870),(101,200806)]),([5,7,120,1382,1586],[(0,65769),(2,229419),(4,65769),(6,299209),(8,65769),(10,237633),(12,65769),(14,65769),(57,65769),(58,65769),(82,65769),(98,33001),(110,33001)]),([5,7,121,333,1058],[(0,102633),(2,98347),(4,102633),(6,65641),(8,102633),(10,237669),(12,102633),(14,102633),(74,102633),(98,102633),(105,106561),(106,102633),(113,102633),(114,106561)]),([5,7,121,380,528,1058],[(56,32838),(96,43109)]),([5,7,121,656,1058],[(0,237669),(2,98347),(4,237669),(6,65641),(8,237669),(10,102633),(12,237669),(14,237669),(73,43105),(74,237669),(98,237669),(105,106561),(110,237669),(113,237669),(114,106561)]),([5,7,128,324,393,1146],[(72,102465),(104,200937)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,128,324,632,1058,1545],[]),([5,7,137,324,384,1146],[(56,33061),(72,102465),(104,200937),(112,205093)]),([5,7,137,324,1146],[(0,205093),(2,229413),(4,205093),(6,205093),(8,205093),(10,303301),(12,205093),(14,299209),(58,33061),(74,205093),(81,205093),(82,205093),(98,205093),(106,205093),(109,32997)]),([5,7,248,324,393,1058],[(72,102465)]),([5,7,248,528,1058,1545],[(96,41158)]),([5,7,249,528,1058],[(0,303205),(2,98347),(4,303205),(6,65641),(8,303205),(10,102697),(12,303205),(14,303205),(73,43105),(74,303205),(98,303205),(105,106561),(110,303205),(113,303205),(114,106561)]),([5,7,324,333,384,1146],[(72,33061),(104,205093),(112,205093),(136,65829)]),([5,7,324,333,1146],[(0,205029),(2,205029),(4,205029),(6,205029),(8,205029),(10,205029),(12,205029),(14,233673),(62,106725),(74,32997),(82,205029),(85,205029),(98,205029),(117,32997)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,324,384,521],[(0,102433),(2,98341),(4,102433),(6,237765),(8,102433),(10,205029),(12,102433),(14,32869),(57,102433),(58,102433),(73,102433),(74,102433),(105,200937),(106,102433),(113,233673),(114,102433)]),([5,7,324,384,1074],[(0,32869),(2,98341),(4,32869),(6,237633),(8,32869),(10,32869),(12,32869),(14,102433),(57,32869),(73,32869),(74,32869),(86,32869),(105,65769),(106,32869),(113,65769),(114,32869)]),([5,7,324,393,512],[(0,102433),(2,98341),(4,102433),(6,106693),(8,102433),(10,32869),(12,102433),(14,102433),(57,102433),(58,102433),(97,36961),(98,102433),(105,200809),(106,102433),(113,102433),(114,200809)]),([5,7,324,393,1146],[(0,200937),(2,229413),(4,200937),(6,237765),(8,200937),(10,200937),(12,200937),(14,200937),(57,102473),(58,102465),(74,33061),(82,205093),(98,102433),(106,102601),(114,102433),(117,32997)]),([5,7,324,632,1545],[(0,102433),(2,102433),(4,102433),(6,237765),(8,102433),(10,102433),(12,102433),(14,108773),(58,102433),(61,102433),(73,102433),(74,102433),(97,98533),(105,200937),(106,102433)]),([5,7,324,1058,1929],[(0,102601),(2,98342),(4,102601),(6,102601),(8,102601),(10,102601),(12,102601),(14,200809),(57,102473),(58,102465),(74,102433),(81,102601),(82,102601),(98,102601),(114,102601),(117,102433)]),([5,7,324,1058,1935],[(0,102601),(2,98347),(4,102601),(6,102601),(8,102601),(10,102601),(12,102601),(14,32875),(81,102601),(82,102601),(98,102601),(101,102601),(114,102601),(117,102601)]),([5,7,324,1146,1586],[(0,205093),(2,229413),(4,205093),(6,237633),(8,205093),(10,299209),(12,205093),(14,205093),(74,32869),(81,65769),(98,33061),(105,65769),(106,205093),(118,65769)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,324,1146,2038],[(0,205029),(2,205029),(4,205029),(6,237765),(8,205029),(10,233673),(12,205029),(14,205029),(58,65637),(74,32869),(98,32997),(101,229477),(106,205029),(109,205029),(117,205029),(118,65769)]),([5,7,380,912,1058],[(0,32870),(2,32870),(4,32870),(6,233537),(8,32870),(10,32870),(12,32870),(14,103457),(57,32838),(73,32870),(74,32870),(86,32870),(101,229445),(105,65765),(113,65765),(114,32870)]),([5,7,393,1058,1860],[(0,200809),(2,98342),(4,200809),(6,200809),(8,200809),(10,200809),(12,200809),(14,102601),(58,65641),(74,200809),(81,200809),(82,200809),(97,37985),(98,200809),(114,200809),(117,200809)]),([5,9,15,324,1146],[(0,98533),(2,98533),(4,98533),(6,98533),(8,98533),(10,237765),(12,98533),(14,233569),(57,32997),(58,98533),(61,98533),(73,98533),(74,98533),(77,32997),(82,98533),(97,200937),(101,32997)]),([5,9,23,120,324,1058],[(72,43105)]),([5,9,71,120,324,1058],[(56,33003)]),([5,9,120,128,324,535,1570],[]),([5,9,120,128,535,1058,1860],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,120,135,324,1442],[(72,33067)]),([5,9,120,135,528,1442],[(56,41057),(108,37985),(112,41157)]),([5,9,120,324,535,1570],[(56,43105)]),([5,9,120,324,663],[(0,204837),(2,32870),(4,204837),(6,37065),(8,204837),(10,204837),(12,204837),(14,204837),(58,43105),(73,103457),(74,204837),(86,103457),(98,98341),(106,98341),(113,41157)]),([5,9,120,327,384,1382],[(72,33067),(96,102441)]),([5,9,120,327,912],[(0,239657),(2,32870),(4,239657),(6,239657),(8,239657),(10,237611),(12,239657),(14,41195),(58,239657),(74,239657),(81,239657),(97,103457),(98,239657),(106,239657),(109,234537)]),([5,9,120,327,1063],[(0,41195),(2,32869),(4,41195),(6,233673),(8,41195),(10,237611),(12,41195),(14,239657),(58,41195),(74,41195),(98,41195),(105,205029),(106,41195)]),([5,9,120,535,1058,1860],[(56,73825)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,120,535,1860],[(0,201961),(2,32870),(4,201961),(6,37065),(8,201961),(10,201961),(12,201961),(14,237766),(58,201961),(74,201961),(82,200937),(97,103457),(98,201961),(114,201961),(117,200745)]),([5,9,120,663,1058],[(0,43205),(2,43205),(4,43205),(6,69833),(8,43205),(10,200747),(12,43205),(14,43205),(57,43109),(58,43105),(74,43205),(77,43109),(97,32870),(98,43205),(105,204869),(110,41157),(114,204837)]),([5,9,120,1442,1860],[(0,200745),(2,200745),(4,200745),(6,37985),(8,200745),(10,200745),(12,200745),(14,41157),(61,65577),(73,200745),(74,200745),(82,200745),(97,98342),(98,200745),(105,98342),(117,98341)]),([5,9,127,327,1058],[(0,37985),(2,65637),(4,37985),(6,233545),(8,37985),(10,98342),(12,37985),(14,37985),(58,37985),(61,37985),(97,102465),(98,37985),(105,73957),(106,36961),(114,41189)]),([5,9,135,324,384,1146],[(56,33061),(112,205093)]),([5,9,135,324,1146],[(0,205093),(2,229477),(4,205093),(6,205093),(8,205093),(10,303301),(12,205093),(14,299209),(58,98597),(73,205093),(74,205093),(82,205093),(98,205093),(106,205093)]),([5,9,248,535,1058],[(0,43205),(2,43205),(4,43205),(6,69833),(8,43205),(10,200747),(12,43205),(14,43205),(57,43109),(58,43105),(74,43205),(77,43109),(97,32870),(98,43205),(105,204869),(110,41157),(114,204837)]),([5,9,324,327,384,1146],[(72,33061),(80,37097),(96,102473),(108,102465)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,324,384,519],[(0,36961),(2,32869),(4,36961),(6,237765),(8,36961),(10,205029),(12,36961),(14,98341),(57,36961),(58,36961),(73,36961),(74,36961),(105,200937),(106,36961),(113,233673),(114,36961)]),([5,9,324,384,1144],[(0,98341),(2,32869),(4,98341),(6,237765),(8,98341),(10,98341),(12,98341),(14,36961),(57,98341),(58,98341),(73,98341),(74,98341),(86,98341),(106,98341),(113,205029),(114,98341)]),([5,9,324,1146,2040],[(0,205029),(2,205029),(4,205029),(6,237765),(8,205029),(10,233673),(12,205029),(14,205029),(57,205029),(58,205029),(74,98341),(77,229413),(98,98533),(101,229413),(109,205029),(117,205029)]),([5,9,327,380,384,1058],[(56,33067),(96,102473)]),([5,9,327,384,512],[(0,233513),(2,32869),(4,233513),(6,98341),(8,233513),(10,41189),(12,233513),(14,233513),(73,102433),(74,233513),(97,102433),(98,233513),(105,36961),(106,233513),(113,233513),(114,36961)]),([5,9,327,384,1146],[(0,37097),(2,65637),(4,37097),(6,237605),(8,37097),(10,37097),(12,37097),(14,37097),(58,98597),(73,102465),(74,37097),(86,102465),(98,36961),(106,36961),(113,41189),(114,233513)]),([5,9,327,1058,1920],[(0,233545),(2,65637),(4,233545),(6,233545),(8,233545),(10,233545),(12,233545),(14,37985),(73,233545),(74,233545),(82,233513),(97,102465),(98,233545),(114,233545),(117,233513)]),([5,15,120,128,324,512,1058],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,120,128,324,528,1570],[]),([5,15,120,128,528,1058,1860],[]),([5,15,120,324,989],[(0,239649),(2,229419),(4,239649),(6,233569),(8,239649),(10,237633),(12,239649),(14,33003),(106,239649),(109,234529),(114,239649),(117,239649)]),([5,15,120,324,1058],[(0,33003),(2,229419),(4,33003),(6,233569),(8,33003),(10,237633),(12,33003),(14,239649),(105,98533),(106,33003),(113,65769),(114,33003)]),([5,15,120,324,1146],[(0,33003),(2,229419),(4,33003),(6,33003),(8,33003),(10,237633),(12,33003),(14,239649),(58,33003),(62,32997),(81,33003),(85,32997),(105,65769),(106,33003),(109,33003),(114,33003)]),([5,15,120,324,1382],[(0,33003),(2,229419),(4,33003),(6,233569),(8,33003),(10,33003),(12,33003),(14,239649),(74,33003),(86,33001),(106,33003),(114,33003),(117,33003)]),([5,15,120,1058,1382],[(0,65769),(2,229419),(4,65769),(6,233569),(8,65769),(10,65769),(12,65769),(14,237633),(74,33001),(81,65769),(86,33001),(114,65769),(117,65769)]),([5,15,120,1058,1723],[(0,237633),(2,229419),(4,237633),(6,233569),(8,237633),(10,237633),(12,237633),(14,33003),(81,237633),(82,237633),(114,237633),(117,237633)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,128,324,528,1146,1536],[]),([5,15,128,324,632,1058,1536],[]),([5,15,128,324,1146],[(0,33061),(2,294949),(4,33061),(6,33061),(8,33061),(10,303169),(12,33061),(14,299041),(57,33061),(58,33061),(62,32997),(81,33061),(82,33061),(85,32997),(105,65833),(106,33061),(109,32997)]),([5,15,324,384,1146],[(0,33061),(2,294949),(4,33061),(6,237633),(8,33061),(10,33061),(12,33061),(14,299041),(57,33061),(73,33061),(74,33061),(78,32997),(82,33061),(86,32997),(106,33061),(113,205029),(114,33061),(117,32997)]),([5,15,324,528,1146],[(0,32998),(2,229414),(4,32998),(6,237633),(8,32998),(10,32998),(12,32998),(14,234529),(73,32998),(74,32998),(78,32997),(81,32998),(82,32998),(86,32997),(113,65769),(117,32998)]),([5,15,324,1058,1146],[(0,98533),(2,229414),(4,98533),(6,237633),(8,98533),(10,98533),(12,98533),(14,233569),(74,32997),(78,98533),(81,65769),(82,98533),(86,32997),(113,65769),(114,98533),(117,98533)]),([5,15,324,1058,1927],[(0,233569),(2,229419),(4,233569),(6,233569),(8,233569),(10,233569),(12,233569),(14,33003),(81,233569),(82,233569),(114,233569),(117,233569)]),([5,15,324,1146],[(1,32997),(3,32997),(5,32997),(7,32997),(9,65769),(11,65769),(59,32997),(63,32997),(75,65769),(79,205029),(83,37089),(87,32997)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,324,1146,1536],[(0,32997),(2,229413),(4,32997),(6,237633),(8,32997),(10,233505),(12,32997),(14,32997),(97,37089),(98,32997),(102,32997),(105,65769),(106,32997),(110,32997),(114,65769),(118,32997)]),([5,23,120,324,1058],[(0,32870),(2,102443),(4,32870),(6,32870),(8,32870),(10,237633),(12,32870),(14,103457),(58,32870),(82,32870),(85,32870),(105,36966),(113,65769),(114,32870)]),([5,23,324,384,1058],[(0,32870),(2,98342),(4,32870),(6,237633),(8,32870),(10,32870),(12,32870),(14,103457),(57,32870),(73,32870),(74,32870),(86,32870),(105,65769),(106,32870),(113,65769),(114,32870)]),([5,120,135,528,1058,1545],[(104,41158)]),([5,120,137,324,535],[(0,43233),(2,37065),(4,43233),(6,32870),(8,43233),(10,43233),(12,43233),(14,229419),(57,43105),(78,41185),(81,43233),(82,43233),(98,43233),(113,41157)]),([5,120,137,535,1058],[(0,43205),(2,69833),(4,43205),(6,65769),(8,43205),(10,200747),(12,43205),(14,43205),(57,43105),(58,43109),(97,204869),(102,41157),(105,237633),(106,43205),(114,237601)]),([5,120,324,384,1033],[(0,102433),(2,36961),(4,102433),(6,237765),(8,102433),(10,102433),(12,102433),(14,32869),(57,102433),(73,102433),(74,102433),(86,102433),(105,200937),(106,102433),(113,200937),(114,102433)]),([5,120,324,393,535],[(0,43233),(2,43233),(4,43233),(6,237766),(8,43233),(10,32870),(12,43233),(14,229419),(57,43233),(73,43105),(82,43233),(98,43233),(101,37985),(105,201961),(106,43233)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,120,324,535,1570],[(0,32870),(2,32870),(4,32870),(6,237633),(8,32870),(10,32870),(12,32870),(14,43109),(58,32870),(61,32870),(73,32870),(97,36966),(105,65769),(106,32870)]),([5,120,324,535,1586],[(0,32870),(2,37065),(4,32870),(6,237633),(8,32870),(10,32870),(12,32870),(14,43233),(58,32870),(74,32869),(105,65769),(106,32870)]),([5,120,324,912,1545],[(0,103457),(2,37985),(4,103457),(6,237766),(8,103457),(10,103457),(12,103457),(14,294985),(57,103457),(74,102433),(105,201961),(106,103457),(114,103457)]),([5,120,324,1058,1936],[(0,229419),(2,229419),(4,229419),(6,229419),(8,229419),(10,229419),(12,229419),(14,32870),(57,229419),(58,229419),(81,229419),(82,229419)]),([5,120,324,1058,2032],[(0,229419),(2,229419),(4,229419),(6,229419),(8,229419),(10,229419),(12,229419),(14,33003),(73,229414),(74,229419),(81,229419),(82,229419)]),([5,120,324,1063,1545],[(0,102433),(2,38089),(4,102433),(6,237765),(8,102433),(10,102433),(12,102433),(14,74017),(74,102433),(81,102433),(97,204838),(105,200937),(106,102433)]),([5,120,324,1442,1552],[(0,294955),(2,37985),(4,294955),(6,41025),(8,294955),(10,294955),(12,294955),(14,32841),(57,294955),(58,294955),(105,65577),(106,294955)]),([5,120,327,393,528],[(0,103457),(2,103457),(4,103457),(6,229419),(8,103457),(10,32870),(12,103457),(14,103457),(57,103457),(73,103617),(98,102433),(101,103457),(105,43233),(106,103457),(113,103457),(114,43233)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,120,327,393,1058],[(0,102465),(2,102465),(4,102465),(6,229419),(8,102465),(10,65637),(12,102465),(14,102465),(57,102465),(73,102593),(97,102465),(98,102465),(106,102433),(113,102465),(114,103457)]),([5,120,528,1442,1860],[(0,65577),(2,37985),(4,65577),(6,65577),(8,65577),(10,65577),(12,65577),(14,32841),(57,65577),(62,65577),(81,65577),(82,32841),(97,98342),(98,65577),(105,32841),(106,65577)]),([5,120,535,852,1058],[(0,32870),(2,69833),(4,32870),(6,200747),(8,32870),(10,237633),(12,32870),(14,103457),(74,32870),(77,32870),(97,204869),(113,65769),(114,32870)]),([5,120,535,1058,1860],[(0,65769),(2,65769),(4,65769),(6,65769),(8,65769),(10,65769),(12,65769),(14,32870),(57,65769),(73,65769),(81,65579),(98,65769),(101,65641),(113,32870),(114,65769)]),([5,121,128,535,1058],[(0,43105),(2,65641),(4,43105),(6,43105),(8,43105),(10,98347),(12,43105),(14,43105),(57,43105),(58,43105),(81,106561),(82,43105),(97,106561),(102,41057),(105,43105),(106,43105),(114,106529)]),([5,121,135,528,1058],[(0,303205),(2,65641),(4,303205),(6,98347),(8,303205),(10,102697),(12,303205),(14,303205),(81,43105),(82,303205),(97,106561),(102,303205),(106,303205),(113,303205),(114,43105)]),([5,121,324,535,1058],[(0,43105),(2,295113),(4,43105),(6,43105),(8,43105),(10,98347),(12,43105),(14,43105),(58,43105),(81,73921),(97,205089),(105,43105),(106,43105),(114,204833)]),([5,127,324,535,1058],[(0,32870),(2,295113),(4,32870),(6,237633),(8,32870),(10,98342),(12,32870),(14,103457),(78,32870),(82,32870),(97,205089),(105,65769),(106,32870)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,127,380,528,1058],[(0,32838),(2,229419),(4,32838),(6,37953),(8,32838),(10,32838),(12,32838),(14,70689),(73,32838),(78,32838),(81,32838),(86,32838),(113,65574),(114,32838)]),([5,324,384,535,1570],[(0,32870),(2,237633),(4,32870),(6,32870),(8,32870),(10,32870),(12,32870),(14,37985),(62,32870),(74,32870),(81,32870),(82,32870),(97,65769),(98,32870),(105,37985),(106,32870)]),([5,324,384,632,1545],[(0,102433),(2,237765),(4,102433),(6,102433),(8,102433),(10,102433),(12,102433),(14,98341),(62,102433),(74,102433),(81,102433),(82,102433),(97,200937),(98,102433),(105,98341),(106,102433)]),([5,324,535,1058,1920],[(0,295113),(2,295113),(4,295113),(6,295113),(8,295113),(10,295113),(12,295113),(14,32870),(58,294985),(73,295113),(74,295113),(105,37985),(114,295113)]),([5,327,384,1058,1545],[(0,102465),(2,98342),(4,102465),(6,73957),(8,102465),(10,102465),(12,102465),(14,65637),(74,102433),(81,102465),(82,102465),(105,233545),(106,102465),(114,102465),(117,102433)]),([5,327,393,528,1536],[(0,103457),(2,98342),(4,103457),(6,32870),(8,103457),(10,103457),(12,103457),(14,103457),(73,37985),(74,103457),(81,103457),(82,37985),(97,37985),(98,103457),(105,103457),(106,37985),(117,102433),(118,103457)]),([5,327,393,1058,1536],[(0,102465),(2,98342),(4,102465),(6,65637),(8,102465),(10,102465),(12,102465),(14,102465),(74,102433),(81,102465),(82,103457),(97,37985),(98,102465),(105,102465),(106,37985),(114,102465),(117,102433)]),([5,380,384,1058,1552],[(0,294955),(2,37953),(4,294955),(6,73953),(8,294955),(10,294955),(12,294955),(14,32838),(81,294955),(82,294955),(105,229449),(106,294955)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,380,528,1058,1920],[(0,229419),(2,229419),(4,229419),(6,229419),(8,229419),(10,229419),(12,229419),(14,32838),(57,229419),(62,229419),(81,229419),(82,229419),(105,32838),(106,229419)]),([5,380,528,1442,1536],[(0,32838),(2,37953),(4,32838),(6,32838),(8,32838),(10,70689),(12,32838),(14,32838),(57,299051),(62,294955),(81,65574),(82,32838),(97,65574),(98,32838),(105,32838),(106,32838),(113,32838),(118,32838)]),([5,380,912,1058,1536],[(0,32838),(2,37953),(4,32838),(6,69857),(8,32838),(10,70689),(12,32838),(14,32838),(81,229445),(82,32838),(97,65574),(98,32838),(105,229445),(106,32838),(113,32838),(118,32838)]),([5,384,535,1058,1860],[(0,65769),(2,65769),(4,65769),(6,65769),(8,65769),(10,65769),(12,65769),(14,32870),(57,65769),(58,65769),(73,65769),(74,65769),(101,32870),(105,37985),(114,65769)]),([6,0,7,9,324,1146],[(0,205029),(2,205029),(4,205029),(6,205029),(8,205029),(10,205029),(12,205029),(14,237765),(16,205029),(18,233673),(57,205029),(58,205029),(61,205029),(73,205029),(74,205029),(77,205029),(81,98533),(82,32997),(97,205029),(98,205029),(101,205029),(106,205029),(113,205029),(114,205029),(129,200937),(130,205029),(133,205029),(138,205029),(146,205029),(149,32997)]),([6,0,15,120,324,1058],[(0,33003),(2,33003),(4,33003),(6,229419),(8,33003),(10,233569),(12,33003),(14,237633),(16,33003),(18,239649),(57,33003),(58,33003),(61,33003),(73,33003),(74,33003),(77,33003),(97,33003),(98,33003),(101,33003),(129,65769),(130,33003),(133,33003),(145,98533),(146,33003),(153,65769),(154,33003)]),([6,7,8,120,324,1058],[(0,33003),(2,229419),(4,33003),(6,33003),(8,33003),(10,233673),(12,33003),(14,237633),(16,33003),(18,239649),(57,33003),(58,33003),(73,33003),(74,33003),(82,33003),(85,33003),(105,33003),(106,33003),(137,65769),(138,33003),(145,205029),(146,33003),(153,65769),(154,33003)]),([6,7,9,16,120,324,1058],[(56,33003),(104,43105),(112,200937),(192,205030)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,64,120,324,1058],[(56,33003),(112,200937),(144,200937),(184,201961)]),([6,7,9,120,128,324,512,1058],[]),([6,7,9,120,128,324,528,1570],[]),([6,7,9,120,128,324,1442],[(56,33067)]),([6,7,9,120,128,528,1058,1860],[]),([6,7,9,120,128,528,1442],[(80,41057),(104,237633),(128,41157),(148,37985),(152,237765)]),([6,7,9,120,256,324,1058],[(56,33003),(128,102465),(152,200937)]),([6,7,9,120,256,528,1058],[(80,43105),(104,106789),(128,43205),(148,37985)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,120,324,380,1058],[(56,33003),(72,98342),(140,33003),(148,200937),(156,200937),(184,205035)]),([6,7,9,120,324,384,1186],[(56,33067),(96,239689),(152,237867)]),([6,7,9,120,324,384,1382],[(56,33067),(104,65835),(136,43233),(152,205093)]),([6,7,9,120,324,528,1570],[(56,33003),(80,305253)]),([6,7,9,120,324,656],[(0,205029),(2,205029),(4,205029),(6,32870),(8,205029),(10,233673),(12,205029),(14,205029),(16,205029),(18,205029),(57,98533),(73,98342),(74,205029),(82,205029),(98,205029),(105,103457),(106,205029),(118,103457),(129,205029),(130,205029),(137,103457),(138,205029),(146,102433),(153,237765),(154,200937)]),([6,7,9,120,324,912],[(0,201961),(2,201961),(4,201961),(6,32870),(8,201961),(10,201961),(12,201961),(14,237766),(16,201961),(18,201961),(57,201961),(73,201961),(74,201961),(82,201961),(97,239689),(98,201961),(105,103457),(106,201961),(113,239817),(129,201961),(130,201961),(137,103457),(138,201961),(146,200937),(149,234697),(154,200937)]),([6,7,9,120,324,912,1058],[(56,65769),(80,43105),(96,43241),(172,239689),(184,201961)]),([6,7,9,120,324,989],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(57,200937),(58,239649),(73,200937),(74,200937),(82,200937),(85,239649),(98,200937),(105,205029),(106,200937),(130,200937),(138,200937),(141,200937),(146,200937),(149,200937),(154,200937),(157,200937)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,120,324,1024],[(0,200937),(2,200937),(4,200937),(6,32869),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(57,200937),(73,200937),(74,200937),(82,200937),(98,200937),(101,200745),(105,102433),(106,200937),(129,200937),(130,200937),(137,102433),(138,200937),(145,205029),(146,200937),(153,200937),(154,205029)]),([6,7,9,120,324,1058],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(57,200937),(58,33003),(73,200937),(74,200937),(82,200937),(85,33003),(98,200937),(105,205029),(106,200937),(130,200937),(137,32870),(138,200937),(145,205029),(146,200937),(153,200937),(154,205029)]),([6,7,9,120,324,1058,1664],[(56,33003),(116,102465),(128,73963),(144,205035),(176,73953),(204,200937)]),([6,7,9,120,324,1063],[(0,200937),(2,200937),(4,200937),(6,32869),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(57,200937),(73,200937),(74,200937),(82,200937),(97,73963),(98,200937),(105,102433),(106,200937),(130,200937),(133,200937),(138,200937),(145,205029),(146,200937),(153,200937),(154,205029)]),([6,7,9,120,324,1067],[(0,200937),(2,200937),(4,200937),(6,32870),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(57,200937),(73,200937),(74,200937),(82,200937),(98,200937),(105,103457),(106,200937),(130,200937),(138,200937),(141,200937),(145,205029),(146,200937),(153,200937),(154,205029)]),([6,7,9,120,324,1146],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,200937),(12,200937),(14,237765),(16,200937),(18,200937),(57,200937),(58,33003),(73,200937),(74,200937),(78,205029),(82,200937),(85,33003),(86,205029),(98,200937),(106,200937),(113,205035),(130,200937),(138,200937),(141,33003),(145,200937),(146,200937),(149,200937)]),([6,7,9,120,324,1382],[(0,205029),(2,205029),(4,205029),(6,205029),(8,205029),(10,233673),(12,205029),(14,205029),(16,205029),(18,205029),(57,98533),(58,33003),(73,98342),(74,205029),(82,205029),(85,33003),(98,205029),(105,205029),(106,205029),(130,205029),(133,98533),(137,32870),(138,205029),(154,205029),(157,205029)]),([6,7,9,120,327,1058],[(0,200937),(2,200937),(4,200937),(6,65637),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(57,200937),(73,200937),(74,200937),(82,200937),(98,200937),(101,200937),(106,200937),(129,43241),(130,200937),(137,102465),(138,200937),(145,205029),(146,200937),(153,200937),(154,205029)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,120,333,1058],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(57,200937),(62,102633),(73,200937),(74,200937),(81,102633),(82,200937),(98,200937),(106,200937),(109,200937),(130,200937),(137,200937),(138,200937),(145,205029),(146,200937),(153,200937),(154,205029)]),([6,7,9,120,380,528,1058],[(56,32966),(72,98342),(128,43205)]),([6,7,9,120,528,1058,1664],[(80,106561),(96,73925),(128,237611),(176,237633),(192,237765)]),([6,7,9,120,528,1058,1860],[(56,65769),(80,303205),(112,200937)]),([6,7,9,120,528,1860],[(0,201961),(2,201961),(4,201961),(6,32870),(8,201961),(10,234697),(12,201961),(14,201961),(16,201961),(18,237766),(57,201961),(73,201961),(74,201961),(82,201961),(97,201961),(98,201961),(105,201961),(106,201961),(113,201961),(114,200937),(130,201961),(133,201769),(137,103457),(138,201961),(154,201961),(157,200937)]),([6,7,9,120,656,1058],[(0,237765),(2,237765),(4,237765),(6,237765),(8,237765),(10,233673),(12,237765),(14,200937),(16,237765),(18,237765),(57,237765),(62,237669),(73,237765),(74,237765),(81,237669),(82,237765),(97,205029),(98,237765),(105,205029),(106,237765),(130,237765),(137,32870),(138,237765),(145,205029),(150,237765),(153,237765),(154,205029)]),([6,7,9,120,1058,1382],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,233673),(12,200937),(14,200937),(16,200937),(18,237765),(57,200937),(58,65769),(73,200937),(74,200937),(82,200937),(85,65769),(98,200937),(105,200937),(106,200937),(113,200937),(118,200937),(130,200937),(133,200937),(137,205029),(138,200937),(154,200937),(157,200937)]),([6,7,9,120,1058,1723],[(0,237765),(2,237765),(4,237765),(6,237765),(8,237765),(10,233673),(12,237765),(14,237765),(16,237765),(18,200937),(57,237765),(58,237633),(73,237765),(74,237765),(82,237765),(85,237633),(98,237765),(105,237765),(106,237765),(113,237765),(114,237765),(130,237765),(138,237765),(141,237765),(154,237765),(157,237765)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,121,324,1058],[(0,200937),(2,98347),(4,200937),(6,200937),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(58,200937),(74,200937),(82,200937),(85,200937),(98,200937),(105,205029),(106,200937),(130,200937),(137,200937),(138,200937),(145,205029),(146,200937),(153,200937),(154,205029)]),([6,7,9,127,324,1058],[(0,200937),(2,98342),(4,200937),(6,200937),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(58,33003),(74,200937),(77,200937),(82,200937),(85,200937),(97,37985),(98,200937),(105,205029),(106,200937),(130,200937),(137,32870),(138,200937),(145,205029),(146,200937),(153,200937),(154,205029)]),([6,7,9,128,324,384,1146],[(56,33061),(96,102465),(144,200937),(148,205093),(152,205093)]),([6,7,9,128,324,528,1146,1536],[]),([6,7,9,128,324,632,1058,1536],[]),([6,7,9,128,324,1146],[(0,205093),(2,205093),(4,205093),(6,205093),(8,205093),(10,205093),(12,205093),(14,303301),(16,205093),(18,299209),(57,98597),(58,33061),(73,205093),(74,205093),(78,205029),(81,205093),(82,205093),(86,205029),(98,205093),(105,205093),(106,205093),(113,205093),(114,205093),(117,205029),(130,205093),(138,205093),(141,33061),(145,201001),(146,205093),(149,205029)]),([6,7,9,248,324,384,1058],[(56,33067),(96,233545),(152,201001)]),([6,7,9,248,528,1058],[(0,303301),(2,303301),(4,303301),(6,303301),(8,303301),(10,299209),(12,303301),(14,201001),(16,303301),(18,303301),(57,303301),(62,303205),(73,303301),(74,303301),(81,303205),(82,303301),(97,205093),(98,303301),(105,205093),(106,303301),(130,303301),(137,32870),(138,303301),(145,205093),(150,303301),(153,303301),(154,205093)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,248,528,1058,1536],[(80,106561),(96,73925),(128,41158),(192,303301),(200,305349)]),([6,7,9,324,380,384,1058],[(56,33067),(80,65829),(136,102601)]),([6,7,9,324,384,512],[(0,233673),(2,98341),(4,233673),(6,32869),(8,233673),(10,237765),(12,233673),(14,205029),(16,233673),(18,233673),(73,233545),(74,233673),(81,233673),(82,233673),(97,36961),(98,233673),(105,102433),(106,233673),(129,36961),(130,233673),(137,102433),(138,233673),(145,200937),(146,233673),(153,233673),(154,200937)]),([6,7,9,324,384,1146],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,237765),(12,200937),(14,200937),(16,200937),(18,200937),(57,98597),(58,33061),(74,200937),(82,200937),(97,200937),(98,200937),(102,205029),(105,200937),(106,200937),(110,205029),(114,205093),(130,200937),(133,98597),(138,200937),(141,33061),(153,205029),(154,233673),(157,205029)]),([6,7,9,324,528,1146],[(0,205030),(2,205030),(4,205030),(6,205030),(8,205030),(10,237766),(12,205030),(14,205030),(16,205030),(18,234697),(57,98534),(58,32998),(74,205030),(81,205030),(82,205030),(97,205030),(98,205030),(102,205029),(105,205030),(106,205030),(110,205029),(113,205030),(114,205030),(118,205029),(130,205030),(138,205030),(141,32998),(153,200937),(157,205030)]),([6,7,9,324,632,1536],[(0,299243),(2,299243),(4,299243),(6,32869),(8,299243),(10,237765),(12,299243),(14,299243),(16,299243),(18,205029),(57,299243),(74,299243),(77,299051),(81,299243),(82,299243),(97,299243),(98,299243),(106,299243),(129,205029),(130,299243),(137,102433),(138,299243),(145,200937),(146,299243)]),([6,7,9,324,1058,1146],[(0,205029),(2,205029),(4,205029),(6,205029),(8,205029),(10,237765),(12,205029),(14,205029),(16,205029),(18,233673),(57,98533),(58,205029),(74,205029),(81,205029),(82,205029),(98,205029),(102,205029),(105,205029),(106,205029),(110,205029),(113,200937),(114,205029),(118,205029),(130,205029),(138,205029),(141,205029),(153,200937),(154,205029),(157,205029)]),([6,7,9,324,1058,1920],[(0,233673),(2,98342),(4,233673),(6,233673),(8,233673),(10,233673),(12,233673),(14,233673),(16,233673),(18,200937),(58,233673),(73,233545),(74,233673),(81,233673),(82,233673),(98,233673),(105,233673),(106,233673),(113,233673),(114,233673),(129,37985),(130,233673),(137,200937),(138,233673),(154,233673),(157,233673)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,9,324,1058,1927],[(0,233673),(2,233673),(4,233673),(6,233673),(8,233673),(10,233673),(12,233673),(14,233673),(16,233673),(18,200937),(57,233569),(58,233673),(74,233673),(81,233673),(82,233673),(98,233673),(105,233673),(106,233673),(113,233673),(114,233673),(130,233673),(133,233673),(137,33003),(138,233673),(154,233673),(157,233673)]),([6,7,9,324,1146],[(1,205029),(3,205029),(5,205029),(7,205029),(9,205029),(11,205029),(13,200937),(15,200937),(59,205029),(63,205029),(75,205029),(79,205029),(83,205029),(87,205029),(99,200937),(103,205029),(107,200937),(111,205029)]),([6,7,9,324,1146,1536],[(0,205029),(2,205029),(4,205029),(6,205029),(8,205029),(10,237765),(12,205029),(14,233673),(16,205029),(18,205029),(57,98533),(58,32997),(74,205029),(81,205029),(82,205029),(98,205029),(106,205029),(109,32997),(129,205029),(130,205029),(134,205029),(137,205029),(138,205029),(142,205029),(145,200937),(146,205029),(150,205029),(154,200937),(158,205029)]),([6,7,9,380,384,528,1058],[(56,32966)]),([6,7,9,384,1058,1860],[(0,200937),(2,98342),(4,200937),(6,200937),(8,200937),(10,200937),(12,200937),(14,200937),(16,200937),(18,233673),(58,65769),(73,200937),(74,200937),(81,200937),(82,200937),(98,200937),(105,200937),(106,200937),(113,200937),(114,200937),(129,37985),(130,200937),(137,233673),(138,200937),(154,200937),(157,200937)]),([6,7,15,120,324,1058],[(0,33003),(2,33003),(4,33003),(6,33003),(8,33003),(10,233673),(12,33003),(14,237633),(16,33003),(18,239649),(57,33003),(58,33003),(61,33003),(73,33003),(74,33003),(77,33003),(82,33003),(85,33003),(97,33003),(101,33003),(105,33003),(129,65769),(133,65769),(137,32870),(145,205029),(146,33003),(153,65769),(154,33003)]),([6,7,16,120,324,1058],[(0,32870),(2,229419),(4,32870),(6,32870),(8,32870),(10,32870),(12,32870),(14,237633),(16,32870),(18,103457),(57,32870),(58,32870),(73,32870),(74,32870),(82,32870),(85,32870),(105,32870),(106,32870),(114,32870),(117,32870),(137,65769),(138,32870),(145,65769),(153,65769),(154,32870)]),([6,7,16,324,384,1058],[(0,32870),(2,98342),(4,32870),(6,32870),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(73,32870),(81,32870),(82,32870),(97,32870),(98,32870),(105,32870),(106,32870),(118,32870),(137,65769),(138,32870),(145,65769),(146,32870),(153,65769),(154,32870)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,120,121,324,528,1058],[(72,32870),(80,205093),(84,32870),(128,43109),(140,43105),(148,32870)]),([6,7,120,128,324,393,1058],[(96,102465),(144,200937)]),([6,7,120,128,324,528,1058,1545],[]),([6,7,120,128,528,1058,1545],[(112,237765),(128,41158),(144,237766),(184,237633)]),([6,7,120,137,324,384,1058],[(72,33067),(96,102465),(144,200937),(152,201001)]),([6,7,120,137,324,528],[(0,103457),(2,229419),(4,103457),(6,299209),(8,103457),(10,32870),(12,103457),(14,103457),(16,103457),(18,103457),(57,103457),(58,103457),(81,205093),(98,103457),(110,103457),(113,103457),(114,237633),(129,43233),(130,103457),(138,102433),(145,103457),(146,205093),(153,303301),(154,201001)]),([6,7,120,137,324,1058],[(0,201001),(2,229419),(4,201001),(6,299209),(8,201001),(10,201001),(12,201001),(14,303301),(16,201001),(18,201001),(57,201001),(58,201001),(74,33067),(81,201001),(86,33003),(98,201001),(113,65769),(114,201001),(130,201001),(137,205093),(138,201001),(145,32870),(146,201001),(153,201001),(154,205093)]),([6,7,120,137,528,1058],[(0,303301),(2,229419),(4,303301),(6,299209),(8,303301),(10,65769),(12,303301),(14,201001),(16,303301),(18,303301),(57,303301),(58,303301),(81,303301),(82,303205),(97,43233),(98,303301),(113,237633),(114,303301),(130,303301),(137,205093),(142,303301),(145,237633),(146,303301),(153,303301),(154,237633)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,120,324,333,384,1058],[(80,65829),(96,33067),(144,102633),(152,65769),(184,65835)]),([6,7,120,324,333,1058],[(0,205029),(2,205029),(4,205029),(6,233673),(8,205029),(10,205029),(12,205029),(14,205029),(16,205029),(18,205029),(57,98342),(58,205029),(78,102633),(98,33003),(110,33003),(114,205029),(117,205029),(130,102433),(137,205029),(145,205029),(146,205029),(153,32870),(154,103457)]),([6,7,120,324,393,528],[(0,103457),(2,229419),(4,103457),(6,103457),(8,103457),(10,237766),(12,103457),(14,32870),(16,103457),(18,103457),(57,103457),(58,103457),(73,103457),(74,103457),(81,103457),(105,103625),(114,103457),(129,43233),(130,103457),(138,102433),(141,103457),(145,201961),(146,103457),(153,103457),(154,201961)]),([6,7,120,324,393,1058],[(0,200937),(2,229419),(4,200937),(6,200937),(8,200937),(10,237765),(12,200937),(14,200937),(16,200937),(18,200937),(57,200937),(58,200937),(73,102473),(74,102465),(81,102601),(98,33067),(105,102601),(110,33003),(114,65769),(130,102433),(137,200937),(138,200937),(145,200937),(146,43233),(153,32870),(154,103457)]),([6,7,120,324,528,989],[(0,103457),(2,229419),(4,103457),(6,299209),(8,103457),(10,237633),(12,103457),(14,103457),(16,103457),(18,32870),(57,103457),(58,103457),(82,103457),(97,103457),(98,103457),(110,103457),(113,103457),(114,103457),(141,234529),(146,103457),(149,103457),(154,103457),(157,103457)]),([6,7,120,324,528,1058],[(0,32870),(2,229419),(4,32870),(6,299209),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(82,32870),(97,32870),(98,32870),(110,32870),(113,32870),(114,32870),(137,205093),(145,65769),(146,32870),(153,65769),(154,32870)]),([6,7,120,324,528,1058,1545],[(104,205029),(128,204838)]),([6,7,120,324,528,1382],[(0,32870),(2,229419),(4,32870),(6,299209),(8,32870),(10,32870),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(74,32870),(86,32870),(97,32870),(98,32870),(110,32870),(113,32870),(114,32870),(146,32870),(149,32870),(153,205093),(154,32870)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,120,324,528,1545],[(0,103457),(2,103457),(4,103457),(6,234603),(8,103457),(10,237766),(12,103457),(14,103457),(16,103457),(18,32870),(57,103457),(58,103457),(74,103457),(77,103457),(97,103457),(98,103457),(105,103457),(106,102433),(113,103457),(114,103457),(129,201961),(145,201961),(146,103457),(154,103457),(157,102433)]),([6,7,120,324,528,1570],[(0,32870),(2,229419),(4,32870),(6,32870),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,305253),(57,32870),(58,32870),(82,32870),(85,32870),(97,32870),(98,32870),(105,32870),(113,32870),(114,32870),(137,299110),(145,65769),(146,32870),(154,32870)]),([6,7,120,324,528,1586],[(0,32870),(2,229419),(4,32870),(6,299209),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(82,32870),(97,32870),(98,32870),(106,32869),(113,32870),(114,32870),(145,65769),(146,32870),(154,32870),(157,32870)]),([6,7,120,324,535,1058],[(0,32870),(2,32870),(4,32870),(6,299209),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(73,32870),(82,32870),(98,32870),(101,32870),(110,32870),(114,32870),(129,43109),(137,205093),(145,65769),(146,32870),(153,33067)]),([6,7,120,324,656,1058],[(0,32870),(2,32870),(4,32870),(6,233673),(8,32870),(10,32870),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(78,32870),(82,32870),(97,32870),(98,32870),(110,32870),(113,32870),(114,32870),(137,205029),(145,205029),(146,32870),(153,205029),(154,32870)]),([6,7,120,324,852,1058],[(0,32870),(2,229419),(4,32870),(6,299209),(8,32870),(10,303301),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(74,32870),(98,32870),(109,32870),(110,32870),(114,32870),(117,32870),(137,205093),(145,201001),(146,32870),(153,201001),(154,32870)]),([6,7,120,324,912,1058],[(0,32870),(2,32870),(4,32870),(6,32870),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(73,32870),(81,32870),(82,32870),(97,32870),(98,32870),(109,32870),(110,32870),(114,32870),(133,229449),(137,65769),(145,65769),(146,32870),(153,65769),(154,32870)]),([6,7,120,324,1058,1067],[(0,32870),(2,32870),(4,32870),(6,233673),(8,32870),(10,237765),(12,32870),(14,103457),(16,32870),(18,32870),(57,32870),(58,32870),(74,102465),(105,205029),(113,200937),(114,32870),(130,32870),(137,205029),(142,32870),(145,200937),(146,32870),(154,32870),(157,32870)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,120,324,1058,1519],[(0,32870),(2,229419),(4,32870),(6,299209),(8,32870),(10,237633),(12,32870),(14,103457),(16,32870),(18,32870),(57,32870),(58,32870),(82,32870),(105,205093),(113,65769),(114,32870),(130,32870),(133,32870),(142,32870),(146,32870),(149,32870),(154,32870),(157,32870)]),([6,7,120,324,1058,1545],[(0,200937),(2,294985),(4,200937),(6,233673),(8,200937),(10,237765),(12,200937),(14,200937),(16,200937),(18,200937),(57,200937),(58,200937),(74,102465),(97,102443),(98,102433),(105,205029),(106,200937),(113,200937),(114,205029),(130,33067),(137,205029),(142,33003),(145,200937),(146,65833),(154,32870),(157,102433)]),([6,7,120,324,1058,1552],[(0,32870),(2,229449),(4,32870),(6,299209),(8,32870),(10,237633),(12,32870),(14,103457),(16,32870),(18,32870),(57,32870),(58,32870),(82,32870),(97,73953),(105,205093),(113,65769),(114,32870),(129,73953),(130,32870),(142,32870),(145,65769),(146,32870),(154,65769)]),([6,7,120,324,1058,1586],[(0,65769),(2,229419),(4,65769),(6,299209),(8,65769),(10,237633),(12,65769),(14,65769),(16,65769),(18,65769),(57,65769),(58,65769),(82,65769),(98,32869),(105,205093),(106,65769),(113,65769),(114,205093),(130,33067),(142,33003),(145,65769),(146,201001),(154,65769),(157,65769)]),([6,7,120,324,1058,2038],[(0,200937),(2,200937),(4,200937),(6,233673),(8,200937),(10,237765),(12,200937),(14,200937),(16,200937),(18,200937),(57,200937),(58,200937),(74,65637),(98,32869),(105,205029),(106,200937),(113,200937),(114,205029),(130,33003),(133,229477),(141,200937),(142,33003),(146,200937),(149,200937),(154,200937),(157,200937)]),([6,7,120,380,528,1058],[(0,32870),(2,229419),(4,32870),(6,32870),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(82,32870),(85,32870),(97,32870),(98,32870),(105,32870),(110,32870),(113,32870),(118,32870),(137,65769),(145,65769),(153,65769),(154,32870)]),([6,7,120,528,852,1058],[(0,32870),(2,229419),(4,32870),(6,299209),(8,32870),(10,201001),(12,32870),(14,237633),(16,32870),(18,103457),(57,32870),(58,32870),(73,32870),(74,32870),(106,32870),(109,32870),(114,32870),(117,32870),(137,205093),(145,303301),(146,32870),(153,65769),(154,32870)]),([6,7,120,528,1058,1382],[(0,65769),(2,229419),(4,65769),(6,299209),(8,65769),(10,65769),(12,65769),(14,65769),(16,65769),(18,237633),(57,65769),(58,65769),(73,65769),(74,65769),(86,65769),(98,33001),(105,65769),(110,33001),(113,65769),(114,65769),(138,65769),(145,201001),(146,65769),(154,65769),(157,65769)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,120,528,1058,1723],[(0,237633),(2,229419),(4,237633),(6,299209),(8,237633),(10,237633),(12,237633),(14,237633),(16,237633),(18,32870),(57,237633),(58,237633),(73,237633),(74,237633),(86,237633),(105,237633),(113,237633),(114,237633),(138,237633),(146,237633),(149,237633),(154,237633),(157,237633)]),([6,7,120,528,1058,1860],[(0,65769),(2,229449),(4,65769),(6,65769),(8,65769),(10,65769),(12,65769),(14,65769),(16,65769),(18,32870),(57,65769),(58,65769),(73,65769),(74,65769),(81,65769),(97,65579),(105,65769),(113,65769),(114,65769),(138,65769),(141,65641),(146,65769),(153,32870),(154,65769)]),([6,7,121,128,528,1058],[(0,303205),(2,98347),(4,303205),(6,65641),(8,303205),(10,303205),(12,303205),(14,102697),(16,303205),(18,303205),(73,303205),(74,303205),(81,303205),(82,303205),(97,43105),(98,303205),(113,106561),(114,303205),(130,303205),(137,106561),(142,303205),(145,303205),(146,303205),(153,303205),(154,106561)]),([6,7,121,324,528,1058],[(0,205093),(2,98347),(4,205093),(6,299209),(8,205093),(10,205093),(12,205093),(14,205093),(16,205093),(18,205093),(58,32870),(74,204865),(82,106561),(97,43105),(98,205093),(110,43105),(113,303301),(114,201001),(130,204833),(137,205093),(145,205093),(146,205093),(153,205093),(154,205093)]),([6,7,127,324,528,1058],[(0,32870),(2,98342),(4,32870),(6,299209),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,103457),(58,32870),(61,32870),(73,32870),(97,32870),(98,32870),(110,32870),(113,32870),(114,32870),(137,205093),(145,65769),(146,32870),(153,65769),(154,32870)]),([6,7,248,324,528,1058],[(0,32870),(2,32870),(4,32870),(6,299209),(8,32870),(10,32870),(12,32870),(14,32870),(16,32870),(18,103457),(57,32870),(58,32870),(78,32870),(82,32870),(97,32870),(98,32870),(110,32870),(113,32870),(114,32870),(137,205093),(145,205093),(146,32870),(153,205093),(154,32870)]),([6,7,324,384,528,1570],[(0,32870),(2,98342),(4,32870),(6,237633),(8,32870),(10,32870),(12,32870),(14,32870),(16,32870),(18,300133),(57,32870),(73,32870),(74,32870),(86,32870),(97,32870),(98,32870),(105,32870),(106,32870),(113,32870),(114,32870),(137,65769),(138,32870),(145,300133),(146,32870)]),([6,7,324,384,1058,1545],[(0,233673),(2,98342),(4,233673),(6,237765),(8,233673),(10,205029),(12,233673),(14,233673),(16,233673),(18,233673),(57,233545),(58,102465),(73,37985),(74,233673),(98,102433),(105,200937),(106,233673),(113,233673),(114,200937),(130,32875),(137,200937),(138,233673),(145,233673),(146,200937),(154,32870),(157,102433)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,324,393,528,1536],[(0,103457),(2,98342),(4,103457),(6,106694),(8,103457),(10,32870),(12,103457),(14,103457),(16,103457),(18,103457),(57,103457),(58,103457),(97,37985),(98,103457),(105,201833),(106,103457),(113,103457),(114,201833),(129,37985),(130,103457),(137,201833),(138,103457),(145,103457),(146,201833),(157,102433),(158,103457)]),([6,7,324,393,1058,1536],[(0,102601),(2,98342),(4,102601),(6,106693),(8,102601),(10,204901),(12,102601),(14,102601),(16,102601),(18,102601),(57,102473),(58,102465),(74,33067),(98,102433),(105,200809),(106,102601),(113,102601),(114,103457),(129,37985),(130,102601),(137,200809),(138,102601),(145,102601),(146,200809),(154,102601),(157,102433)]),([6,7,324,528,1058,1146],[(0,205093),(2,229414),(4,205093),(6,237633),(8,205093),(10,205093),(12,205093),(14,205093),(16,205093),(18,299209),(73,205093),(74,205093),(81,205093),(82,205093),(98,33061),(105,65769),(106,205093),(113,205093),(114,205093),(130,205093),(137,65769),(149,65769),(154,205093),(157,205093)]),([6,7,324,528,1058,1920],[(0,299209),(2,98342),(4,299209),(6,299209),(8,299209),(10,299209),(12,299209),(14,299209),(16,299209),(18,32870),(57,299081),(73,299209),(74,299209),(81,299209),(82,299209),(105,299209),(106,299209),(113,299209),(114,299209),(129,37985),(130,299209),(145,32870),(154,299209)]),([6,7,324,528,1058,1927],[(0,299209),(2,229419),(4,299209),(6,299209),(8,299209),(10,299209),(12,299209),(14,299209),(16,299209),(18,32870),(73,299209),(74,299209),(81,299209),(82,299209),(105,299209),(106,299209),(113,299209),(114,299209),(130,299209),(133,299209),(141,32870),(145,32870),(154,299209)]),([6,7,380,384,528,1058],[(0,32870),(2,32870),(4,32870),(6,237633),(8,32870),(10,32870),(12,32870),(14,32870),(16,32870),(18,103457),(57,32838),(73,32870),(74,32870),(86,32870),(97,32870),(98,32870),(110,32870),(113,32870),(114,32870),(133,294981),(137,65769),(145,65769),(146,32870),(153,65769),(154,32870)]),([6,7,384,528,1058,1860],[(0,65769),(2,98342),(4,65769),(6,65769),(8,65769),(10,65769),(12,65769),(14,65769),(16,65769),(18,32870),(57,65769),(58,65769),(73,65769),(74,65769),(81,65769),(82,65769),(105,65769),(106,65769),(113,65769),(114,65769),(129,37985),(141,32870),(145,32870),(154,65769)]),([6,9,15,120,324,1058],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,233569),(12,200937),(14,237765),(16,200937),(18,200937),(57,33003),(58,200937),(61,200937),(73,200937),(77,33003),(81,200937),(97,98533),(98,200937),(101,33003),(106,200937),(129,200937),(130,200937),(133,33003),(138,200937),(145,98533),(146,200937),(153,200937),(154,98533)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,120,127,324,1058],[(0,200937),(2,200937),(4,200937),(6,37985),(8,200937),(10,200937),(12,200937),(14,237765),(16,200937),(18,200937),(61,33003),(74,200937),(77,200937),(82,200937),(85,200937),(97,98342),(98,200937),(105,98342),(129,32870),(130,200937),(138,200937),(146,200937),(153,200937),(154,98342)]),([6,9,120,128,324,535],[(0,204837),(2,32870),(4,204837),(6,37065),(8,204837),(10,204837),(12,204837),(14,204837),(16,204837),(18,204837),(58,43105),(73,103457),(74,204837),(81,204837),(82,103457),(97,103457),(98,204837),(110,103457),(113,204837),(114,204837),(130,98341),(138,98341),(145,204837),(146,204837),(153,41157)]),([6,9,120,128,324,535,1058,1536],[]),([6,9,120,128,535,1058],[(0,43205),(2,43205),(4,43205),(6,69833),(8,43205),(10,43205),(12,43205),(14,200747),(16,43205),(18,43205),(57,43109),(58,43105),(73,43205),(74,43205),(81,43205),(82,43205),(98,43205),(101,43109),(113,204869),(114,43205),(129,32870),(130,43205),(137,204869),(142,41157),(145,43205),(146,43205),(154,204837)]),([6,9,120,135,324,384,1058],[(72,33067),(152,201001)]),([6,9,120,135,324,528],[(0,205093),(2,32870),(4,205093),(6,299209),(8,205093),(10,205093),(12,205093),(14,205093),(16,205093),(18,205093),(58,43105),(74,98597),(81,205093),(82,98342),(97,103457),(98,205093),(110,103457),(114,205093),(129,103457),(130,205093),(138,102433),(145,205093),(146,205093),(153,303301),(154,201001)]),([6,9,120,135,324,1058],[(0,201001),(2,229477),(4,201001),(6,299209),(8,201001),(10,201001),(12,201001),(14,303301),(16,201001),(18,201001),(58,201001),(74,201001),(81,201001),(82,201001),(97,102625),(98,201001),(114,201001),(129,102625),(130,201001),(137,205093),(138,201001),(146,201001),(153,201001),(154,205093)]),([6,9,120,135,384,528,1058],[(56,43105),(140,37985),(144,43205)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,120,135,528,1058],[(0,303301),(2,303301),(4,303301),(6,299209),(8,303301),(10,303301),(12,303301),(14,201001),(16,303301),(18,303301),(57,303205),(58,303301),(74,303301),(77,303205),(81,303301),(82,303301),(97,205093),(98,303301),(113,205093),(114,303301),(129,32870),(130,303301),(137,205093),(142,303301),(146,303301),(153,303301),(154,205093)]),([6,9,120,135,528,1058,1536],[(56,73825),(112,73925),(144,41158),(192,303301),(200,305349)]),([6,9,120,324,327,384,1058],[(96,33067),(112,43241),(128,102473),(148,102465)]),([6,9,120,324,384,535],[(0,201961),(2,32870),(4,201961),(6,201961),(8,201961),(10,237766),(12,201961),(14,201961),(16,201961),(18,201961),(58,43105),(73,103457),(74,201961),(81,239817),(97,103457),(98,201961),(105,234697),(106,201961),(114,204837),(130,201961),(138,200937),(141,37985),(145,201961),(146,239689),(153,201961),(154,201961)]),([6,9,120,324,384,535,1058],[(56,43105),(96,43233),(116,43205)]),([6,9,120,324,384,1024],[(0,200937),(2,32869),(4,200937),(6,36961),(8,200937),(10,237765),(12,200937),(14,200937),(16,200937),(18,200937),(73,102433),(74,200937),(81,98341),(97,102433),(98,200937),(105,98341),(106,200937),(118,98341),(129,102433),(130,200937),(137,98341),(138,200937),(145,200937),(146,98341),(153,200937),(154,200937)]),([6,9,120,324,535,1058],[(0,205093),(2,205093),(4,205093),(6,299209),(8,205093),(10,205093),(12,205093),(14,205093),(16,205093),(18,205093),(57,43109),(58,43105),(73,205093),(74,205093),(82,43205),(98,98597),(101,43109),(106,200937),(113,73925),(129,32870),(130,205093),(137,205093),(138,201961),(145,205093),(146,205093),(154,204837)]),([6,9,120,324,535,1058,1536],[(56,73825),(204,201961)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,120,324,535,1536],[(0,201961),(2,32870),(4,201961),(6,37065),(8,201961),(10,237766),(12,201961),(14,201961),(16,201961),(18,201961),(58,73825),(73,103457),(74,201961),(98,201961),(106,200937),(113,201961),(129,103457),(130,201961),(137,204837),(138,201961),(145,201961),(146,204837),(154,201961)]),([6,9,120,324,912,1536],[(0,305225),(2,32870),(4,305225),(6,37985),(8,305225),(10,237766),(12,305225),(14,74027),(16,305225),(18,305225),(73,305225),(74,305225),(81,305225),(97,103457),(98,305225),(106,305225),(129,103457),(130,305225),(137,98342),(138,305225),(145,201961),(146,305225),(154,201961)]),([6,9,120,324,1058,1920],[(0,200937),(2,200937),(4,200937),(6,37985),(8,200937),(10,237765),(12,200937),(14,200937),(16,200937),(18,200937),(61,229419),(73,98342),(74,200937),(81,98342),(97,32870),(98,200937),(106,200937),(113,200937),(114,98342),(129,200937),(130,200937),(137,98342),(138,200937),(157,200937)]),([6,9,120,324,1058,2040],[(0,200937),(2,200937),(4,200937),(6,233673),(8,200937),(10,237765),(12,200937),(14,200937),(16,200937),(18,200937),(58,98347),(61,229419),(73,205029),(74,200937),(97,32870),(98,200937),(105,205029),(106,200937),(113,200937),(114,205029),(130,200937),(133,229419),(138,200937),(141,200937),(149,200937),(157,200937)]),([6,9,120,324,1063,1536],[(0,74027),(2,32869),(4,74027),(6,38089),(8,74027),(10,237765),(12,74027),(14,305225),(16,74027),(18,74027),(58,73825),(73,74027),(74,74027),(98,74027),(106,74027),(113,200937),(129,102433),(130,74027),(137,204838),(138,74027),(145,200937),(146,74027),(158,200937)]),([6,9,120,324,1442,1536],[(0,200745),(2,200745),(4,200745),(6,37985),(8,200745),(10,41157),(12,200745),(14,200745),(16,200745),(18,200745),(61,294955),(73,98342),(74,200745),(81,98342),(97,32870),(98,200745),(106,200745),(129,200745),(130,200745),(137,98342),(138,200745),(145,200745),(146,98342),(158,200745)]),([6,9,120,327,384,528],[(0,239657),(2,32870),(4,239657),(6,239657),(8,239657),(10,237611),(12,239657),(14,41195),(16,239657),(18,239657),(58,239657),(74,239657),(81,239657),(97,103457),(98,239657),(105,234697),(106,239657),(129,103457),(130,239657),(138,239657),(141,234537),(145,43241),(146,239657),(153,239657),(154,43241)]),([6,9,120,327,384,1058],[(0,43241),(2,65637),(4,43241),(6,43241),(8,43241),(10,237611),(12,43241),(14,43241),(16,43241),(18,43241),(58,43105),(74,43241),(81,37985),(97,102465),(98,43241),(105,233673),(106,43241),(118,102465),(129,102465),(130,43241),(137,38121),(138,43241),(146,102433),(153,41195),(154,239657)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([6,9,120,384,1058,1860],[(0,200747),(2,200747),(4,200747),(6,37985),(8,200747),(10,200747),(12,200747),(14,200747),(16,200747),(18,43205),(61,65579),(73,200747),(74,200747),(81,200747),(82,200747),(97,200747),(98,200747),(106,200747),(113,200747),(114,200747),(129,98342),(130,200747),(137,98342),(149,200747),(157,200937)]),([6,9,324,384,632,1536],[(0,299051),(2,32869),(4,299051),(6,237765),(8,299051),(10,299051),(12,299051),(14,299051),(16,299051),(18,98341),(57,299051),(58,299051),(73,299051),(74,299051),(86,299051),(106,299051),(113,299051),(114,299051),(129,102433),(130,299051),(137,200937),(138,299051),(145,98341),(146,299051)]),([6,9,327,384,528,1536],[(0,234537),(2,32870),(4,234537),(6,98342),(8,234537),(10,41190),(12,234537),(14,234537),(16,234537),(18,234537),(73,103457),(74,234537),(97,103457),(98,234537),(105,37985),(106,234537),(113,234537),(114,37985),(129,103457),(130,234537),(137,37985),(138,234537),(145,234537),(146,37985),(157,233513),(158,234537)]),([6,9,327,384,1058,1536],[(0,233545),(2,65637),(4,233545),(6,98342),(8,233545),(10,73957),(12,233545),(14,233545),(16,233545),(18,233545),(73,102465),(74,233545),(97,102465),(98,233545),(106,233513),(113,233545),(114,234537),(129,102465),(130,233545),(137,37985),(138,233545),(145,233545),(146,37985),(154,233545),(157,233513)]),([6,15,120,128,324,528,1058,1536],[]),([6,15,120,128,324,1058],[(0,33067),(2,294955),(4,33067),(6,299105),(8,33067),(10,33067),(12,33067),(14,303169),(16,33067),(18,305185),(73,33067),(74,33067),(78,33003),(81,33067),(82,33067),(86,33003),(113,33067),(114,33067),(117,33003),(137,98597),(138,33067),(145,65833),(146,33067),(149,33003),(153,65833),(154,33067)]),([6,15,120,324,384,1058],[(0,33067),(2,294955),(4,33067),(6,299105),(8,33067),(10,237633),(12,33067),(14,33067),(16,33067),(18,305185),(73,33067),(81,33067),(97,33067),(98,33067),(102,33003),(105,33067),(106,33067),(110,33003),(114,33067),(118,33003),(137,98597),(138,33067),(145,65769),(146,33067),(153,65769),(154,33067),(157,33003)]),([6,15,120,324,528,1058],[(0,33003),(2,229419),(4,33003),(6,299105),(8,33003),(10,237633),(12,33003),(14,33003),(16,33003),(18,239649),(57,32870),(82,32966),(97,33003),(98,33003),(102,33003),(106,33003),(110,33003),(113,33003),(114,33003),(118,33003),(137,98597),(138,33003),(145,65769),(146,33003),(153,65769),(154,33003),(157,33003)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,120,324,1058],[(1,33003),(3,33003),(5,33003),(7,33003),(9,33003),(11,33003),(13,65769),(15,65769),(59,33003),(63,33003),(75,33003),(79,33003),(83,33003),(87,33003),(99,65769),(103,65769),(107,65769),(111,33003),(115,98533),(119,33003)]),([6,15,120,324,1058,1536],[(0,33067),(2,229449),(4,33067),(6,233569),(8,33067),(10,237633),(12,33067),(14,305185),(16,33067),(18,33067),(97,73953),(105,98533),(106,33067),(113,65769),(114,33067),(129,73953),(130,33067),(134,33003),(137,98533),(138,33067),(142,33003),(145,65769),(146,33067),(150,33003),(154,65769),(158,65769)]),([6,120,127,324,528,1058],[(0,32870),(2,37985),(4,32870),(6,229419),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,103457),(58,32870),(61,32870),(73,32870),(74,32870),(97,32870),(102,32870),(105,32870),(110,32870),(113,32870),(114,32870),(145,65769),(146,32870),(153,65769),(154,32870)]),([6,120,324,384,528,1545],[(0,103457),(2,37985),(4,103457),(6,237766),(8,103457),(10,103457),(12,103457),(14,103457),(16,103457),(18,32870),(57,103457),(73,103457),(74,103457),(86,103457),(97,103457),(98,102433),(105,103457),(106,103457),(113,103457),(114,103457),(137,201961),(138,103457),(145,201961),(146,103457),(154,103457),(157,102433)]),([6,120,324,384,1058,1552],[(0,294955),(2,37985),(4,294955),(6,237633),(8,294955),(10,73953),(12,294955),(14,294955),(16,294955),(18,32870),(57,294955),(58,294955),(73,294955),(74,294955),(105,294955),(106,294955),(113,294955),(114,294955),(137,65769),(138,294955),(145,229449),(146,294955)]),([6,120,324,528,535,1058],[(0,32870),(2,299209),(4,32870),(6,237633),(8,32870),(10,32870),(12,32870),(14,229419),(16,32870),(18,103457),(58,32870),(74,32870),(81,32870),(82,32870),(98,32870),(114,32870),(117,32870),(129,205093),(137,65769),(138,32870),(145,43233),(146,32870)]),([6,120,324,528,1058,1920],[(0,229419),(2,37985),(4,229419),(6,229419),(8,229419),(10,229419),(12,229419),(14,229419),(16,229419),(18,32870),(57,229419),(58,229419),(73,229419),(78,229419),(81,229419),(82,229419),(105,229419),(106,229419),(113,229419),(114,229419),(129,98342),(130,229419),(145,32870),(146,229419)]),([6,120,324,528,1058,2040],[(0,229419),(2,229419),(4,229419),(6,229419),(8,229419),(10,229419),(12,229419),(14,229419),(16,229419),(18,32870),(58,229419),(78,229419),(81,229419),(82,229419),(97,229414),(105,229419),(106,229419),(113,229419),(114,229419),(130,229419),(133,229419),(146,229419),(149,229419)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([6,120,324,528,1442,1536],[(0,32841),(2,37985),(4,32841),(6,41025),(8,32841),(10,32841),(12,32841),(14,73761),(16,32841),(18,32841),(57,32841),(58,32841),(73,299051),(78,294955),(81,32841),(82,32841),(113,65577),(114,32841),(129,98342),(130,32841),(137,65577),(138,32841),(145,32841),(146,32841),(153,32841),(158,32841)]),([6,120,324,535,1058,1536],[(0,32870),(2,32870),(4,32870),(6,237633),(8,32870),(10,102473),(12,32870),(14,103457),(16,32870),(18,32870),(58,32870),(61,32870),(73,32870),(97,36966),(105,65769),(106,32870),(113,73829),(129,32870),(130,32870),(137,65769),(138,32870),(145,73829),(150,32870),(153,32870),(154,43109)]),([6,120,324,912,1058,1536],[(0,32870),(2,37985),(4,32870),(6,237633),(8,32870),(10,73953),(12,32870),(14,103457),(16,32870),(18,32870),(57,32870),(58,32870),(105,65769),(106,32870),(113,229449),(114,32870),(129,98342),(130,32870),(137,65769),(138,32870),(145,229449),(146,32870),(153,32870),(158,32870)]),([6,120,384,528,1058,1860],[(0,65579),(2,37985),(4,65579),(6,65579),(8,65579),(10,65579),(12,65579),(14,65579),(16,65579),(18,32843),(57,65579),(58,65579),(73,65579),(78,65579),(81,65579),(82,65579),(105,65579),(106,65579),(113,65579),(114,65579),(129,98342),(130,65579),(145,32843),(146,65579)]),([6,324,384,535,1058,1536],[(0,32870),(2,237633),(4,32870),(6,32870),(8,32870),(10,98342),(12,32870),(14,103457),(16,32870),(18,32870),(62,32870),(74,32870),(81,32870),(82,32870),(97,65769),(98,32870),(105,37985),(106,32870),(129,65769),(130,32870),(137,32870),(138,32870),(145,37985),(150,32870),(153,32870),(154,37985)]),([6,380,384,528,1058,1536],[(0,32838),(2,37953),(4,32838),(6,73953),(8,32838),(10,32838),(12,32838),(14,70689),(16,32838),(18,32838),(73,299051),(78,294955),(81,32838),(82,32838),(105,229449),(106,32838),(113,229449),(114,32838),(129,65574),(130,32838),(137,229449),(138,32838),(145,32838),(146,32838),(153,32838),(158,32838)]),([7,0,7,9,120,324,1058],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,200937),(12,200937),(14,233673),(16,200937),(18,237765),(20,200937),(22,200937),(57,200937),(58,200937),(61,200937),(73,200937),(74,200937),(77,200937),(81,200937),(82,33003),(97,200937),(98,200937),(101,200937),(105,200937),(106,200937),(114,200937),(117,33003),(129,205029),(130,200937),(133,200937),(138,200937),(145,205029),(146,200937),(169,200937),(170,200937),(173,200937),(178,200937),(185,32870),(186,200937),(193,205029),(194,200937),(201,200937),(202,205029)]),([7,0,7,120,324,528,1058],[(0,32870),(2,32870),(4,32870),(6,229419),(8,32870),(10,299209),(12,32870),(14,237633),(16,32870),(18,32870),(20,32870),(22,103457),(57,32870),(58,32870),(61,32870),(73,32870),(74,32870),(77,32870),(81,32870),(82,32870),(97,32870),(98,32870),(101,32870),(114,32870),(129,32870),(130,32870),(133,32870),(137,32870),(138,32870),(150,32870),(153,32870),(154,32870),(169,65769),(170,32870),(173,32870),(185,205093),(193,65769),(194,32870),(201,65769),(202,32870)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([7,7,9,120,128,324,384,1058],[(56,33067),(128,102465),(192,200937),(196,201001),(200,201001)]),([7,7,9,120,128,324,528],[(0,205093),(2,205093),(4,205093),(6,32870),(8,205093),(10,299209),(12,205093),(14,205093),(16,205093),(18,205093),(20,205093),(22,205093),(57,98597),(73,98342),(74,205093),(82,205093),(97,205093),(98,205093),(105,103457),(106,205093),(113,205093),(114,103457),(130,205093),(137,103457),(138,205093),(150,103457),(153,205093),(154,205093),(169,205093),(170,205093),(177,103457),(178,205093),(186,102433),(193,205093),(194,205093),(201,303301),(202,201001)]),([7,7,9,120,128,324,528,1058,1536],[]),([7,7,9,120,128,324,1058],[(0,201001),(2,201001),(4,201001),(6,201001),(8,201001),(10,299209),(12,201001),(14,201001),(16,201001),(18,303301),(20,201001),(22,201001),(57,201001),(58,33067),(73,201001),(74,201001),(82,201001),(85,33067),(97,201001),(98,201001),(102,200937),(105,201001),(106,201001),(110,200937),(113,201001),(114,201001),(118,200937),(130,201001),(137,205093),(138,201001),(153,205093),(154,201001),(157,200937),(170,201001),(177,32870),(178,201001),(185,205093),(186,201001),(193,201001),(194,201001),(197,200937),(201,201001),(202,205093)]),([7,7,9,120,128,324,1058,1536],[(56,33067),(96,102625),(104,73953),(148,102465),(168,74027),(184,205099),(192,205030),(224,74017),(244,200937),(260,201001)]),([7,7,9,120,128,384,528,1058],[(80,43105),(104,237633),(112,237861),(136,106789),(156,303301),(168,43205),(188,37985),(192,237765),(240,237766)]),([7,7,9,120,128,528,1058],[(0,303301),(2,303301),(4,303301),(6,303301),(8,303301),(10,299209),(12,303301),(14,303301),(16,303301),(18,201001),(20,303301),(22,303301),(57,303301),(62,303205),(73,303301),(74,303301),(81,303205),(82,303301),(97,303301),(98,303301),(105,303301),(106,303301),(113,303301),(114,303301),(129,205093),(130,303301),(137,205093),(138,303301),(153,205093),(154,303301),(170,303301),(177,32870),(178,303301),(185,205093),(190,303301),(193,303301),(194,303301),(201,303301),(202,205093)]),([7,7,9,120,128,528,1058,1536],[(80,106561),(104,237633),(128,73925),(152,237765),(168,41158),(192,237766),(248,303301),(256,305349)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([7,7,9,120,324,384,528],[(0,201961),(2,201961),(4,201961),(6,32870),(8,201961),(10,201961),(12,201961),(14,237766),(16,201961),(18,201961),(20,201961),(22,201961),(57,201961),(73,201961),(74,201961),(82,201961),(97,239689),(98,201961),(105,103457),(106,201961),(113,239817),(129,201961),(130,201961),(137,103457),(138,201961),(145,234697),(146,201961),(154,205093),(169,201961),(170,201961),(177,103457),(178,201961),(186,200937),(189,234697),(193,201961),(194,103457),(201,201961),(202,201961)]),([7,7,9,120,324,384,528,1058],[(56,65769),(80,43105),(96,43241),(136,43233),(140,32870),(188,37985),(204,200937),(220,239689),(232,201961)]),([7,7,9,120,324,384,1058],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,200937),(12,200937),(14,237765),(16,200937),(18,200937),(20,200937),(22,200937),(57,200937),(58,33067),(73,200937),(74,200937),(82,200937),(85,33067),(98,200937),(106,200937),(129,200937),(130,200937),(134,200937),(137,200937),(138,200937),(142,200937),(145,233673),(146,200937),(150,200937),(154,205093),(170,200937),(173,200937),(177,32870),(178,200937),(185,200937),(186,200937),(193,200937),(201,200937),(202,200937),(205,200937)]),([7,7,9,120,324,528,1058],[(0,205093),(2,205093),(4,205093),(6,205093),(8,205093),(10,299209),(12,205093),(14,205093),(16,205093),(18,205093),(20,205093),(22,205093),(57,98597),(58,33003),(62,205093),(73,98342),(74,205093),(82,205093),(85,33003),(98,205093),(105,205093),(106,205093),(109,32870),(129,205093),(130,205093),(134,200937),(137,205093),(138,205093),(141,32870),(142,200937),(146,200937),(153,303301),(154,201001),(158,200937),(170,205093),(177,32870),(178,205093),(181,32870),(185,205093),(186,201961),(193,205093),(194,205093),(201,205093),(202,205093),(205,200937)]),([7,7,9,120,324,528,1058,1536],[(56,65769),(80,73825),(144,205029),(168,204838),(184,205030),(228,32870),(248,205093),(252,200937),(260,201961)]),([7,7,9,120,324,528,1536],[(0,201961),(2,201961),(4,201961),(6,32870),(8,201961),(10,234697),(12,201961),(14,237766),(16,201961),(18,201961),(20,201961),(22,201961),(57,201961),(73,201961),(74,201961),(82,201961),(98,201961),(101,201769),(105,103457),(106,201961),(129,201961),(130,201961),(137,103457),(138,201961),(145,299243),(146,200937),(153,201961),(154,205030),(169,201961),(170,201961),(177,103457),(178,201961),(185,205030),(186,201961),(193,201961),(194,205030),(202,201961),(205,200937)]),([7,7,9,120,324,1058],[(1,200937),(3,200937),(5,200937),(7,200937),(9,200937),(11,200937),(13,205029),(15,205029),(17,200937),(19,200937),(59,200937),(63,200937),(75,200937),(79,200937),(83,200937),(87,200937),(99,205029),(103,200937),(107,205029),(111,200937),(131,200937),(135,200937),(139,200937),(143,200937),(147,200937),(151,200937),(155,205029),(159,200937)]),([7,7,9,120,324,1058,1536],[(0,200937),(2,200937),(4,200937),(6,200937),(8,200937),(10,233673),(12,200937),(14,237765),(16,200937),(18,200937),(20,200937),(22,200937),(57,200937),(58,33067),(73,200937),(74,200937),(82,200937),(85,33067),(98,200937),(101,200937),(105,205029),(106,200937),(129,200937),(130,200937),(137,32870),(138,200937),(145,205029),(146,200937),(153,200937),(154,205029),(169,200937),(170,200937),(174,200937),(177,200937),(178,200937),(182,200937),(185,205029),(186,200937),(190,200937),(193,200937),(194,205029),(198,200937),(202,200937),(205,200937),(206,200937)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([7,7,9,324,384,528,1536],[(0,234697),(2,98342),(4,234697),(6,32870),(8,234697),(10,237766),(12,234697),(14,205030),(16,234697),(18,234697),(20,234697),(22,234697),(73,234569),(74,234697),(81,234697),(82,234697),(97,37985),(98,234697),(105,103457),(106,234697),(129,37985),(130,234697),(137,103457),(138,234697),(145,201961),(146,234697),(153,234697),(154,201961),(169,37985),(170,234697),(177,103457),(178,234697),(185,201961),(186,234697),(193,234697),(194,201961),(205,233673),(206,234697)]),([7,7,9,324,384,1058,1536],[(0,233673),(2,98342),(4,233673),(6,233673),(8,233673),(10,237765),(12,233673),(14,205029),(16,233673),(18,233673),(20,233673),(22,233673),(58,33067),(73,233545),(74,233673),(81,233673),(82,233673),(97,37985),(98,233673),(105,200937),(106,233673),(130,233673),(137,32870),(138,233673),(145,200937),(146,233673),(153,233673),(154,200937),(169,37985),(170,233673),(177,233673),(178,233673),(185,200937),(186,233673),(193,233673),(194,200937),(202,233673),(205,233673)]),([7,7,120,128,324,528,1058],[(0,32870),(2,32870),(4,32870),(6,299209),(8,32870),(10,32870),(12,32870),(14,32870),(16,32870),(18,32870),(20,32870),(22,103457),(57,32870),(58,32870),(73,32870),(74,32870),(78,32870),(81,32870),(82,32870),(86,32870),(102,32870),(106,32870),(113,32870),(114,32870),(117,32870),(129,32870),(130,32870),(142,32870),(145,32870),(146,32870),(149,32870),(153,32870),(154,32870),(177,205093),(185,205093),(186,32870),(189,32870),(193,205093),(194,32870),(201,205093),(202,32870)]),([7,7,120,324,384,528,1058],[(0,32870),(2,32870),(4,32870),(6,32870),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,32870),(20,32870),(22,103457),(57,32870),(58,32870),(73,32870),(81,32870),(82,32870),(97,32870),(98,32870),(102,32870),(105,32870),(106,32870),(110,32870),(114,32870),(118,32870),(129,32870),(130,32870),(141,32870),(142,32870),(145,32870),(146,32870),(153,32870),(154,32870),(157,32870),(173,295013),(177,65769),(185,65769),(186,32870),(193,65769),(194,32870),(197,32870),(201,65769),(202,32870)]),([7,7,120,324,528,1058],[(1,32870),(3,32870),(5,32870),(7,32870),(9,32870),(11,32870),(13,32870),(15,32870),(17,65769),(19,65769),(59,32870),(63,32870),(75,32870),(79,32870),(83,32870),(87,32870),(99,32870),(103,32870),(107,32870),(111,32870),(115,32870),(119,32870),(131,65769),(135,65769),(139,65769),(143,33003),(147,205093),(151,32870),(155,65769),(159,32870)]),([7,7,120,324,528,1058,1536],[(0,32870),(2,229449),(4,32870),(6,32870),(8,32870),(10,237633),(12,32870),(14,32870),(16,32870),(18,103457),(20,32870),(22,32870),(57,32870),(58,32870),(82,32870),(85,32870),(97,32870),(98,32870),(105,32870),(110,32870),(113,32870),(114,32870),(129,73953),(137,65769),(145,65769),(146,32870),(153,65769),(154,32870),(169,73953),(170,32870),(174,32870),(177,32870),(178,32870),(182,32870),(185,65769),(186,32870),(190,32870),(193,32870),(194,32870),(198,32870),(201,32870),(202,65769),(206,32870)]),([7,7,324,384,528,1058,1536],[(0,32870),(2,98342),(4,32870),(6,237633),(8,32870),(10,32870),(12,32870),(14,32870),(16,32870),(18,103457),(20,32870),(22,32870),(57,32870),(73,32870),(74,32870),(86,32870),(97,32870),(98,32870),(105,32870),(106,32870),(113,32870),(114,32870),(137,65769),(138,32870),(145,65769),(146,32870),(153,65769),(154,32870),(169,37985),(170,32870),(177,65769),(178,32870),(185,32870),(186,32870),(193,32870),(198,32870),(201,32870),(202,65769)]),([7,9,120,324,384,528,1536],[(0,201961),(2,32870),(4,201961),(6,37985),(8,201961),(10,237766),(12,201961),(14,201961),(16,201961),(18,201961),(20,201961),(22,201961),(73,103457),(74,201961),(81,98342),(97,103457),(98,201961),(105,98342),(106,201961),(118,98342),(129,103457),(130,201961),(137,299051),(138,200937),(145,201961),(146,98342),(153,201961),(154,201961),(169,103457),(170,201961),(177,98342),(178,201961),(185,201961),(186,98342),(193,201961),(194,201961),(202,201961),(205,200937)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([7,9,120,324,384,1058,1536],[(0,200937),(2,200937),(4,200937),(6,37985),(8,200937),(10,237765),(12,200937),(14,200937),(16,200937),(18,200937),(20,200937),(22,200937),(61,294955),(73,98342),(74,200937),(81,98342),(97,200937),(98,200937),(105,98342),(106,200937),(118,98342),(129,32870),(130,200937),(138,200937),(145,200937),(146,98342),(153,200937),(154,200937),(169,200937),(170,200937),(177,98342),(178,200937),(185,200937),(186,98342),(193,200937),(194,200937),(205,200937),(206,200937)]),([7,120,324,384,528,1058,1536],[(0,32870),(2,37985),(4,32870),(6,237633),(8,32870),(10,73953),(12,32870),(14,32870),(16,32870),(18,103457),(20,32870),(22,32870),(57,32870),(58,32870),(73,32870),(74,32870),(97,299051),(102,294955),(105,32870),(106,32870),(113,32870),(114,32870),(137,65769),(138,32870),(145,229449),(146,32870),(153,229449),(154,32870),(169,98342),(170,32870),(177,65769),(178,32870),(185,229449),(186,32870),(193,32870),(194,32870),(201,32870),(206,32870)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = ((((((K_0 ++ (K_1 ++ K_2)) ++ (K_3 ++ (K_4 ++ K_5))) ++ ((K_6 ++ (K_7 ++ K_8)) ++ (K_9 ++ (K_10 ++ K_11)))) ++ (((K_12 ++ (K_13 ++ K_14)) ++ (K_15 ++ (K_16 ++ K_17))) ++ ((K_18 ++ (K_19 ++ K_20)) ++ (K_21 ++ (K_22 ++ K_23))))) ++ ((((K_24 ++ (K_25 ++ K_26)) ++ (K_27 ++ (K_28 ++ K_29))) ++ ((K_30 ++ (K_31 ++ K_32)) ++ (K_33 ++ (K_34 ++ K_35)))) ++ (((K_36 ++ (K_37 ++ K_38)) ++ (K_39 ++ (K_40 ++ K_41))) ++ ((K_42 ++ (K_43 ++ K_44)) ++ (K_45 ++ (K_46 ++ K_47))))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app c_0 (all_app c_1 c_2)) (all_app c_3 (all_app c_4 c_5))) (all_app (all_app c_6 (all_app c_7 c_8)) (all_app c_9 (all_app c_10 c_11)))) (all_app (all_app (all_app c_12 (all_app c_13 c_14)) (all_app c_15 (all_app c_16 c_17))) (all_app (all_app c_18 (all_app c_19 c_20)) (all_app c_21 (all_app c_22 c_23))))) (all_app (all_app (all_app (all_app c_24 (all_app c_25 c_26)) (all_app c_27 (all_app c_28 c_29))) (all_app (all_app c_30 (all_app c_31 c_32)) (all_app c_33 (all_app c_34 c_35)))) (all_app (all_app (all_app c_36 (all_app c_37 c_38)) (all_app c_39 (all_app c_40 c_41))) (all_app (all_app c_42 (all_app c_43 c_44)) (all_app c_45 (all_app c_46 c_47))))))

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

end PEqualNP.Outside.L_meta_19367.Probes

open PEqualNP.Outside.L_meta_19367.Probes in
theorem PEqualNP.Outside.L_meta_19367 (C : PEqualNP.CircuitLowerBounds.Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ 7) : ¬ Matches C := coreLower C hfan hsize
