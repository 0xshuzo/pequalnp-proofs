import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19203

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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
def urootHint (ws : List Nat) : Nat := (([([15, 240, 3840, 4369, 8738, 17476, 61440], 306274), ([15, 240, 3840, 4369, 8738, 34952, 61440], 305218), ([15, 240, 3840, 4369, 17476, 34952, 61440], 99628), ([15, 240, 3840, 8738, 17476, 34952, 61440], 98572), ([15, 240, 3840, 4369, 8738, 17476, 34952], 211333), ([15, 240, 4369, 8738, 17476, 34952, 61440], 207109), ([15, 3840, 4369, 8738, 17476, 34952, 61440], 397519), ([240, 3840, 4369, 8738, 17476, 34952, 61440], 393295)] : List (List Nat × Nat)).lookup (isort ws)).getD 0

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

def L_ : List ℕ := [17,33,65,129,18,34,66,130,20,36,68,132,24,40,72,136]
def M_ : ℕ := 65535
def Y_ : ℕ := 5068
def XS_ : List ℕ := [15,240,3840,61440,4369,8738,17476,34952]
def PD_ : List (ℕ × ℕ) := [(1,6698),(2,5951),(3,4533),(4,752),(5,850),(6,899),(7,491),(8,223),(9,69),(10,8),(11,14),(12,13),(13,4)]
def PM_ : List (ℕ × ℕ) := [(0,5068),(1,5068),(4,5068),(5,5068),(10,5068),(11,5068),(13,5068),(14,5068),(15,5068)]

def G_ : List (List ℕ) := [[0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 12, 13, 15, 14], [4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15], [4, 5, 7, 6, 0, 1, 3, 2, 8, 9, 11, 10, 12, 13, 15, 14]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,204,3840,4369,61986] BT.lf) [3,255,4915] BT.lf) [3,255,60620] (BT.nd BT.lf [3,3840,4607,8738,64716] BT.lf)) [3,4369,8959,53196,61440] (BT.nd (BT.nd BT.lf [3,4383,8946,53196,61440] BT.lf) [3,4607,8738,20292,63624] (BT.nd BT.lf [3,4607,8738,53196,61440] BT.lf))) [3,4881,65314] (BT.nd (BT.nd (BT.nd BT.lf [3,4915,65280] BT.lf) [3,7936,62259] (BT.nd BT.lf [3,7953,62242] BT.lf)) [3,7953,62259,65314] (BT.nd (BT.nd BT.lf [3,8447,13107] BT.lf) [3,8447,52428] (BT.nd BT.lf [3,13107,57088] BT.lf)))) [3,52428,57088] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,60620,65280] BT.lf) [4,15,240,4915] (BT.nd BT.lf [4,15,240,60620] BT.lf)) [4,15,3840,4593,8738,64716] (BT.nd (BT.nd BT.lf [4,15,4369,8946,53196,61440] BT.lf) [4,15,4593,8738,20292,63624] (BT.nd BT.lf [4,15,4593,8738,53196,61440] BT.lf))) [4,15,8432,13107] (BT.nd (BT.nd (BT.nd BT.lf [4,15,8432,52428] BT.lf) [4,204,3840,4369,8738,61440] (BT.nd BT.lf [4,255,546,4369] BT.lf)) [4,255,3840,4369,8738,64716] (BT.nd (BT.nd BT.lf [4,255,3840,4369,52428,61986] BT.lf) [4,255,4369,8738,20292,63624] (BT.nd BT.lf [4,255,4369,8738,53196,61440] BT.lf))))) [4,255,4369,64716] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,255,4369,64989] BT.lf) [4,255,4881,8738] (BT.nd BT.lf [4,255,7953,13107] BT.lf)) [4,255,7953,52428] (BT.nd (BT.nd BT.lf [4,255,8192,13107] BT.lf) [4,255,8192,52428] (BT.nd BT.lf [4,255,8738,12561] BT.lf))) [4,255,17476,43144] (BT.nd (BT.nd (BT.nd BT.lf [4,256,7953,61986] BT.lf) [4,512,4369,65314] (BT.nd BT.lf [4,546,4369,65280] BT.lf)) [4,3549,3840,4369] (BT.nd (BT.nd BT.lf [4,3549,3840,61166] BT.lf) [4,3549,4369,61695] (BT.nd BT.lf [4,3840,4095,4915] BT.lf)))) [4,3840,4096,62259] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,3840,4369,8959,52428,61440] BT.lf) [4,3840,4369,61986] (BT.nd BT.lf [4,3840,4369,61986,65331] BT.lf)) [4,3840,4369,62242] (BT.nd (BT.nd BT.lf [4,3840,4369,62259,65314] BT.lf) [4,3840,4383,8946,52428,61440] (BT.nd BT.lf [4,3840,4607,8738,17476,63624] BT.lf))) [4,3840,4607,8738,52428,61440] (BT.nd (BT.nd (BT.nd BT.lf [4,3840,4881,61986] BT.lf) [4,3840,4915,61440] (BT.nd BT.lf [4,3840,7953,61986,62259] BT.lf)) [4,3840,8959,13107] (BT.nd (BT.nd BT.lf [4,3840,8959,52428] BT.lf) [4,3840,12287,13107] (BT.nd BT.lf [4,3840,12287,52428] BT.lf)))))) [4,3840,13107,53248] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,3840,52428,53248] BT.lf) [4,3840,60620,61440] (BT.nd BT.lf [4,3840,61166,61986] BT.lf)) [4,4369,7936,61986] (BT.nd (BT.nd BT.lf [4,4369,7953,61986,65314] BT.lf) [4,4369,8447,8738] (BT.nd BT.lf [4,4369,8738,57088] BT.lf))) [4,4369,8959,17476,36744,61440] (BT.nd (BT.nd (BT.nd BT.lf [4,4369,56797,57088] BT.lf) [4,4369,61695,61986] (BT.nd BT.lf [4,4369,64716,65280] BT.lf)) [4,4369,64989,65280] (BT.nd (BT.nd BT.lf [4,4383,8946,17476,36744,61440] BT.lf) [4,4607,8738,17476,36744,61440] (BT.nd BT.lf [4,4881,8738,65280] BT.lf)))) [4,4881,12066,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,7936,8738,61713] BT.lf) [4,7936,13107,61440] (BT.nd BT.lf [4,7936,52428,61440] BT.lf)) [4,7953,8738,61696] (BT.nd (BT.nd BT.lf [4,7953,8994,61440] BT.lf) [4,7953,13107,65280] (BT.nd BT.lf [4,7953,52428,65280] BT.lf))) [4,8192,13107,65280] (BT.nd (BT.nd (BT.nd BT.lf [4,8192,52428,65280] BT.lf) [4,8447,17476,34952] (BT.nd BT.lf [4,8738,12561,65280] BT.lf)) [4,12032,13107,61440] (BT.nd (BT.nd BT.lf [4,12032,52428,61440] BT.lf) [4,17476,34952,57088] (BT.nd BT.lf [4,17476,43144,65280] BT.lf))))) [4,61166,61695,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,0,3840,4369,61986] BT.lf) [5,1,3840,4369,61986] (BT.nd BT.lf [5,2,3840,4369,61986] BT.lf)) [5,4,3840,4369,61986] (BT.nd (BT.nd BT.lf [5,15,240,546,4369] BT.lf) [5,15,240,3840,4369,8738,64716] (BT.nd BT.lf [5,15,240,3840,4369,52428,61986] BT.lf))) [5,15,240,4369,8738,20292,63624] (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,4369,8738,53196,61440] BT.lf) [5,15,240,4369,64716] (BT.nd BT.lf [5,15,240,4369,64989] BT.lf)) [5,15,240,4881,8738] (BT.nd (BT.nd BT.lf [5,15,240,7953,13107] BT.lf) [5,15,240,7953,52428] (BT.nd BT.lf [5,15,240,8192,13107] BT.lf)))) [5,15,240,8192,52428] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,240,8738,12561] BT.lf) [5,15,240,17476,43144] (BT.nd BT.lf [5,15,3549,3840,4369] BT.lf)) [5,15,3840,4369,8946,52428,61440] (BT.nd (BT.nd BT.lf [5,15,3840,4369,61986] BT.lf) [5,15,3840,4593,8738,17476,63624] (BT.nd BT.lf [5,15,3840,4593,8738,52428,61440] BT.lf))) [5,15,3840,8946,13107] (BT.nd (BT.nd (BT.nd BT.lf [5,15,3840,8946,52428] BT.lf) [5,15,3840,61166,61986] (BT.nd BT.lf [5,15,3855,4369,61986] BT.lf)) [5,15,4369,8432,8738] (BT.nd (BT.nd BT.lf [5,15,4369,8946,17476,36744,61440] BT.lf) [5,15,4369,61680,61986] (BT.nd BT.lf [5,15,4369,61695,61986] BT.lf))))))) [5,15,4593,8738,17476,36744,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,15,8432,17476,34952] BT.lf) [5,255,512,4369,8738] BT.lf) [5,255,3840,4369,8738] (BT.nd BT.lf [5,255,3840,4369,8738,17476,63624] BT.lf)) [5,255,3840,4369,8738,52428,61440] (BT.nd (BT.nd BT.lf [5,255,3840,4369,13107] BT.lf) [5,255,3840,4369,17476,34952,61986] (BT.nd BT.lf [5,255,3840,4369,52428] BT.lf))) [5,255,3840,4369,56797] (BT.nd (BT.nd (BT.nd BT.lf [5,255,3840,4369,61986] BT.lf) [5,255,3840,8738,13107] (BT.nd BT.lf [5,255,3840,8738,52428] BT.lf)) [5,255,3840,8738,61166] (BT.nd (BT.nd BT.lf [5,255,3855,4369,8738] BT.lf) [5,255,4095,4369,8738] (BT.nd BT.lf [5,255,4369,7953,8738] BT.lf)))) [5,255,4369,8192,8738] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,255,4369,8738,17476,36744,61440] BT.lf) [5,255,4369,8738,20292] (BT.nd BT.lf [5,255,4369,8738,61440] BT.lf)) [5,255,4369,8738,61455] (BT.nd (BT.nd BT.lf [5,255,4369,8738,61695] BT.lf) [5,255,4369,8738,61713] (BT.nd BT.lf [5,255,4369,8738,62532] BT.lf))) [5,255,4369,13107,61440] (BT.nd (BT.nd (BT.nd BT.lf [5,255,4369,17476,63624] BT.lf) [5,255,4369,52428,61440] (BT.nd BT.lf [5,255,4369,56797,61440] BT.lf)) [5,255,4369,61440,61986] (BT.nd (BT.nd BT.lf [5,255,7953,17476,34952] BT.lf) [5,255,8192,17476,34952] (BT.nd BT.lf [5,255,8738,13107,61440] BT.lf))))) [5,255,8738,52428,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,255,8738,61166,61440] BT.lf) [5,256,3840,4369,61986] (BT.nd BT.lf [5,256,7953,8738,61440] BT.lf)) [5,512,3840,4369,61986] (BT.nd (BT.nd BT.lf [5,512,4369,8738,65280] BT.lf) [5,512,4369,12066,61440] (BT.nd BT.lf [5,546,3840,4095,4369] BT.lf))) [5,546,3840,4369,61440] (BT.nd (BT.nd (BT.nd BT.lf [5,1024,3840,4369,61986] BT.lf) [5,3549,3840,4369] (BT.nd BT.lf [5,3549,3840,4369,8738] BT.lf)) [5,3549,3840,4369,17476] (BT.nd (BT.nd BT.lf [5,3549,3840,4369,61440] BT.lf) [5,3549,3840,4369,61986] (BT.nd BT.lf [5,3840,3840,4369,61986] BT.lf)))) [5,3840,3855,4369,61986] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4095,4369,8738] BT.lf) [5,3840,4095,4369,13107] (BT.nd BT.lf [5,3840,4095,4369,52428] BT.lf)) [5,3840,4095,4369,56797] (BT.nd (BT.nd BT.lf [5,3840,4095,4369,61986] BT.lf) [5,3840,4095,8738,13107] (BT.nd BT.lf [5,3840,4095,8738,52428] BT.lf))) [5,3840,4095,8738,61166] (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4096,4369,61986] BT.lf) [5,3840,4096,8738,61713] (BT.nd BT.lf [5,3840,4096,13107,61440] BT.lf)) [5,3840,4096,52428,61440] (BT.nd (BT.nd BT.lf [5,3840,4369,4369,61986] BT.lf) [5,3840,4369,4383,61986] (BT.nd BT.lf [5,3840,4369,7953,61986] BT.lf)))))) [5,3840,4369,8192,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4369,8738,8959] BT.lf) [5,3840,4369,8738,12287] (BT.nd BT.lf [5,3840,4369,8738,53248] BT.lf)) [5,3840,4369,8738,61440] (BT.nd (BT.nd BT.lf [5,3840,4369,8738,61442] BT.lf) [5,3840,4369,8738,61696] (BT.nd BT.lf [5,3840,4369,8738,61952] BT.lf))) [5,3840,4369,8738,61986] (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4369,8738,62464] BT.lf) [5,3840,4369,8738,65280] (BT.nd BT.lf [5,3840,4369,8738,65314] BT.lf)) [5,3840,4369,8739,61440] (BT.nd (BT.nd BT.lf [5,3840,4369,8751,8946] BT.lf) [5,3840,4369,8751,61986] (BT.nd BT.lf [5,3840,4369,8959,17476,34952,61440] BT.lf)))) [5,3840,4369,8994,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4369,12066,61986] BT.lf) [5,3840,4369,12834,61440] (BT.nd BT.lf [5,3840,4369,13107,61440] BT.lf)) [5,3840,4369,13107,61986] (BT.nd (BT.nd BT.lf [5,3840,4369,13107,65280] BT.lf) [5,3840,4369,16384,61986] (BT.nd BT.lf [5,3840,4369,17476,61986] BT.lf))) [5,3840,4369,17487,61986] (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4369,20292,61986] BT.lf) [5,3840,4369,21845,61986] (BT.nd BT.lf [5,3840,4369,25122,61440] BT.lf)) [5,3840,4369,26214,61986] (BT.nd (BT.nd BT.lf [5,3840,4369,30583,61986] BT.lf) [5,3840,4369,52428,61440] (BT.nd BT.lf [5,3840,4369,52428,61986] BT.lf))))) [5,3840,4369,52428,65280] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4369,53248,56797] BT.lf) [5,3840,4369,56797,61440] (BT.nd BT.lf [5,3840,4369,56797,61986] BT.lf)) [5,3840,4369,56797,65280] (BT.nd (BT.nd BT.lf [5,3840,4369,61166,61986] BT.lf) [5,3840,4369,61440,61986] (BT.nd BT.lf [5,3840,4369,61440,62259] BT.lf))) [5,3840,4369,61440,64716] (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4369,61440,64989] BT.lf) [5,3840,4369,61455,61986] (BT.nd BT.lf [5,3840,4369,61695,61986] BT.lf)) [5,3840,4369,61713,61986] (BT.nd (BT.nd BT.lf [5,3840,4369,61986] BT.lf) [5,3840,4369,61986,61986] (BT.nd BT.lf [5,3840,4369,61986,61999] BT.lf)))) [5,3840,4369,61986,62259] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4369,61986,62532] BT.lf) [5,3840,4369,61986,63078] (BT.nd BT.lf [5,3840,4369,61986,65280] BT.lf)) [5,3840,4369,61986,65295] (BT.nd (BT.nd BT.lf [5,3840,4369,61986,65314] BT.lf) [5,3840,4369,62532,63624] (BT.nd BT.lf [5,3840,4371,8738,61440] BT.lf))) [5,3840,4383,8946,17476,34952,61440] (BT.nd (BT.nd (BT.nd BT.lf [5,3840,4383,13107,61440] BT.lf) [5,3840,4383,52428,61440] (BT.nd BT.lf [5,3840,4607,8738,17476,34952,61440] BT.lf)) [5,3840,4881,8738,61440] (BT.nd (BT.nd BT.lf [5,3840,7953,13107,61440] BT.lf) [5,3840,7953,52428,61440] (BT.nd BT.lf [5,3840,8192,13107,61440] BT.lf)))))))) [5,3840,8192,52428,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,8738,12561,61440] BT.lf) [5,3840,8738,13107,61440] BT.lf) [5,3840,8738,13107,61986] (BT.nd BT.lf [5,3840,8738,13107,65280] BT.lf)) [5,3840,8738,52428,61440] (BT.nd (BT.nd BT.lf [5,3840,8738,52428,61986] BT.lf) [5,3840,8738,52428,65280] (BT.nd BT.lf [5,3840,8738,61166,61440] BT.lf))) [5,3840,8738,61166,61986] (BT.nd (BT.nd (BT.nd BT.lf [5,3840,8738,61166,65280] BT.lf) [5,3840,8751,13107,61440] (BT.nd BT.lf [5,3840,8751,52428,61440] BT.lf)) [5,3840,8959,17476,34952] (BT.nd (BT.nd BT.lf [5,3840,12066,13107,61440] BT.lf) [5,3840,12066,52428,61440] (BT.nd BT.lf [5,3840,12287,17476,34952] BT.lf)))) [5,3840,13107,21845,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,13107,26214,61440] BT.lf) [5,3840,13107,56797,61440] (BT.nd BT.lf [5,3840,13107,61166,61440] BT.lf)) [5,3840,17476,21845,61986] (BT.nd (BT.nd BT.lf [5,3840,17476,34952,53248] BT.lf) [5,3840,17476,43144,61440] (BT.nd BT.lf [5,3840,17476,43690,61986] BT.lf))) [5,3840,17476,61166,61986] (BT.nd (BT.nd (BT.nd BT.lf [5,3840,21845,26214,61440] BT.lf) [5,3840,21845,39321,61440] (BT.nd BT.lf [5,3840,21845,52428,61440] BT.lf)) [5,3840,26214,43690,61440] (BT.nd (BT.nd BT.lf [5,3840,26214,52428,61440] BT.lf) [5,3840,52428,56797,61440] (BT.nd BT.lf [5,3840,52428,61166,61440] BT.lf))))) [5,3840,56797,61166,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3840,61166,61440,61986] BT.lf) [5,3840,61166,61986] (BT.nd BT.lf [5,3855,4080,4369,8738] BT.lf)) [5,3855,4369,8738,61455] (BT.nd (BT.nd BT.lf [5,3855,4369,8738,65280] BT.lf) [5,4095,4369,8738,61695] (BT.nd BT.lf [5,4095,4369,8738,65280] BT.lf))) [5,4369,7936,8738,61440] (BT.nd (BT.nd (BT.nd BT.lf [5,4369,7953,8738,65280] BT.lf) [5,4369,8192,8738,65280] (BT.nd BT.lf [5,4369,8738,12032,61440] BT.lf)) [5,4369,8738,20224,61440] (BT.nd (BT.nd BT.lf [5,4369,8738,20292,65280] BT.lf) [5,4369,8738,61440,61695] (BT.nd BT.lf [5,4369,8738,61440,65280] BT.lf)))) [5,4369,8738,61455,61680] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,4369,8738,61455,65280] BT.lf) [5,4369,8738,61695,61986] (BT.nd BT.lf [5,4369,8738,61695,65280] BT.lf)) [5,4369,8738,61713,65280] (BT.nd (BT.nd BT.lf [5,4369,8738,62532,65280] BT.lf) [5,4369,13107,61440,61695] (BT.nd BT.lf [5,4369,13107,61440,65280] BT.lf))) [5,4369,17476,61695,61986] (BT.nd (BT.nd (BT.nd BT.lf [5,4369,17476,63624,65280] BT.lf) [5,4369,52428,61440,61695] (BT.nd BT.lf [5,4369,52428,61440,65280] BT.lf)) [5,4369,56797,61440,61695] (BT.nd (BT.nd BT.lf [5,4369,56797,61440,65280] BT.lf) [5,4369,61440,61695,61986] (BT.nd BT.lf [5,4369,61440,61986,65280] BT.lf)))))) [5,4369,61695,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7936,17476,34952,61440] BT.lf) [5,7953,17476,34952,65280] (BT.nd BT.lf [5,8192,17476,34952,65280] BT.lf)) [5,8738,13107,61440,61695] (BT.nd (BT.nd BT.lf [5,8738,13107,61440,65280] BT.lf) [5,8738,52428,61440,61695] (BT.nd BT.lf [5,8738,52428,61440,65280] BT.lf))) [5,8738,61166,61440,61695] (BT.nd (BT.nd (BT.nd BT.lf [5,8738,61166,61440,65280] BT.lf) [5,12032,17476,34952,61440] (BT.nd BT.lf [6,0,3840,4369,8738,61440] BT.lf)) [6,1,3840,4369,8738,61440] (BT.nd (BT.nd BT.lf [6,2,3840,4369,8738,61440] BT.lf) [6,4,3840,4369,8738,61440] (BT.nd BT.lf [6,15,240,512,4369,8738] BT.lf)))) [6,15,240,3840,4369,8738] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,8738,17476,63624] BT.lf) [6,15,240,3840,4369,8738,52428,61440] (BT.nd BT.lf [6,15,240,3840,4369,13107] BT.lf)) [6,15,240,3840,4369,17476,34952,61986] (BT.nd (BT.nd BT.lf [6,15,240,3840,4369,52428] BT.lf) [6,15,240,3840,4369,56797] (BT.nd BT.lf [6,15,240,3840,4369,61986] BT.lf))) [6,15,240,3840,8738,13107] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,3840,8738,52428] BT.lf) [6,15,240,3840,8738,61166] (BT.nd BT.lf [6,15,240,3855,4369,8738] BT.lf)) [6,15,240,4095,4369,8738] (BT.nd (BT.nd BT.lf [6,15,240,4369,7953,8738] BT.lf) [6,15,240,4369,8192,8738] (BT.nd BT.lf [6,15,240,4369,8738,17476,36744,61440] BT.lf))))) [6,15,240,4369,8738,20292] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,61440] BT.lf) [6,15,240,4369,8738,61455] (BT.nd BT.lf [6,15,240,4369,8738,61695] BT.lf)) [6,15,240,4369,8738,61713] (BT.nd (BT.nd BT.lf [6,15,240,4369,8738,62532] BT.lf) [6,15,240,4369,13107,61440] (BT.nd BT.lf [6,15,240,4369,17476,63624] BT.lf))) [6,15,240,4369,52428,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,15,240,4369,56797,61440] BT.lf) [6,15,240,4369,61440,61986] (BT.nd BT.lf [6,15,240,7953,17476,34952] BT.lf)) [6,15,240,8192,17476,34952] (BT.nd (BT.nd BT.lf [6,15,240,8738,13107,61440] BT.lf) [6,15,240,8738,52428,61440] (BT.nd BT.lf [6,15,240,8738,61166,61440] BT.lf)))) [6,15,255,3840,4369,8738] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,255,4369,8738,61440] BT.lf) [6,15,3840,4080,4369,8738] (BT.nd BT.lf [6,15,3840,4095,4369,8738] BT.lf)) [6,15,3840,4369,8738,8946] (BT.nd (BT.nd BT.lf [6,15,3840,4369,8738,61440] BT.lf) [6,15,3840,4369,8738,61455] (BT.nd BT.lf [6,15,3840,4369,8738,61986] BT.lf))) [6,15,3840,4369,8738,65280] (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4369,8738,65295] BT.lf) [6,15,3840,4369,8946,17476,34952,61440] (BT.nd BT.lf [6,15,3840,4369,13107,61440] BT.lf)) [6,15,3840,4369,17476,61986] (BT.nd (BT.nd BT.lf [6,15,3840,4369,52428,61440] BT.lf) [6,15,3840,4369,56797,61440] (BT.nd BT.lf [6,15,3840,4369,61440,61986] BT.lf))))))) [6,15,3840,4369,61986] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,15,3840,4593,8738,17476,34952,61440] BT.lf) [6,15,3840,8738,13107,61440] BT.lf) [6,15,3840,8738,52428,61440] (BT.nd BT.lf [6,15,3840,8738,61166,61440] BT.lf)) [6,15,3840,8946,17476,34952] (BT.nd (BT.nd BT.lf [6,15,3855,4369,8738,61440] BT.lf) [6,15,4369,8738,61440,61680] (BT.nd BT.lf [6,15,4369,8738,61440,61695] BT.lf))) [6,15,4369,8738,61440,65280] (BT.nd (BT.nd (BT.nd BT.lf [6,15,4369,8738,61440,65295] BT.lf) [6,255,3840,4369,8738] (BT.nd BT.lf [6,255,3840,4369,8738,17476] BT.lf)) [6,255,3840,4369,8738,17476,34952,61440] (BT.nd (BT.nd BT.lf [6,255,3840,4369,8738,61440] BT.lf) [6,255,3840,4369,17476,34952] (BT.nd BT.lf [6,255,3840,8738,17476,34952] BT.lf)))) [6,255,4369,8738,17476,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,255,4369,8738,61440] BT.lf) [6,255,4369,17476,34952,61440] (BT.nd BT.lf [6,255,8738,17476,34952,61440] BT.lf)) [6,256,3840,4369,8738,61440] (BT.nd (BT.nd BT.lf [6,512,3840,4369,8738,61440] BT.lf) [6,1024,3840,4369,8738,61440] (BT.nd BT.lf [6,3840,3840,4369,8738,61440] BT.lf))) [6,3840,3855,4369,8738,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4095,4369,8738] BT.lf) [6,3840,4095,4369,8738,17476] (BT.nd BT.lf [6,3840,4095,4369,8738,61440] BT.lf)) [6,3840,4095,4369,17476,34952] (BT.nd (BT.nd BT.lf [6,3840,4095,8738,17476,34952] BT.lf) [6,3840,4096,4369,8738,61440] (BT.nd BT.lf [6,3840,4096,17476,34952,61440] BT.lf))))) [6,3840,4369,4369,8738,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,4383,8738,61440] BT.lf) [6,3840,4369,7953,8738,61440] (BT.nd BT.lf [6,3840,4369,8192,8738,61440] BT.lf)) [6,3840,4369,8738,8738,61440] (BT.nd (BT.nd BT.lf [6,3840,4369,8738,8751,61440] BT.lf) [6,3840,4369,8738,12066,61440] (BT.nd BT.lf [6,3840,4369,8738,13107,61440] BT.lf))) [6,3840,4369,8738,16384,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,8738,17476,61440] BT.lf) [6,3840,4369,8738,17476,61986] (BT.nd BT.lf [6,3840,4369,8738,17476,65280] BT.lf)) [6,3840,4369,8738,17487,61440] (BT.nd (BT.nd BT.lf [6,3840,4369,8738,20292,61440] BT.lf) [6,3840,4369,8738,21845,61440] (BT.nd BT.lf [6,3840,4369,8738,26214,61440] BT.lf)))) [6,3840,4369,8738,30583,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,8738,52428,61440] BT.lf) [6,3840,4369,8738,56797,61440] (BT.nd BT.lf [6,3840,4369,8738,61166,61440] BT.lf)) [6,3840,4369,8738,61440] (BT.nd (BT.nd BT.lf [6,3840,4369,8738,61440,61440] BT.lf) [6,3840,4369,8738,61440,61455] (BT.nd BT.lf [6,3840,4369,8738,61440,61695] BT.lf))) [6,3840,4369,8738,61440,61713] (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,8738,61440,61986] BT.lf) [6,3840,4369,8738,61440,62532] (BT.nd BT.lf [6,3840,4369,8738,61440,65280] BT.lf)) [6,3840,4369,8738,61440,65295] (BT.nd (BT.nd BT.lf [6,3840,4369,8738,61986] BT.lf) [6,3840,4369,8738,65280] (BT.nd BT.lf [6,3840,4369,13107,17476,61440] BT.lf)))))) [6,3840,4369,13107,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,17476,26214,61440] BT.lf) [6,3840,4369,17476,30583,61440] (BT.nd BT.lf [6,3840,4369,17476,34952,61440] BT.lf)) [6,3840,4369,17476,34952,61986] (BT.nd (BT.nd BT.lf [6,3840,4369,17476,34952,65280] BT.lf) [6,3840,4369,17476,39321,61440] (BT.nd BT.lf [6,3840,4369,17476,52428,61440] BT.lf))) [6,3840,4369,17476,56797,61440] (BT.nd (BT.nd (BT.nd BT.lf [6,3840,4369,17476,61440,61986] BT.lf) [6,3840,4369,17476,61440,63624] (BT.nd BT.lf [6,3840,4369,17476,61986] BT.lf)) [6,3840,4369,52428,61440] (BT.nd (BT.nd BT.lf [6,3840,4369,56797,61440] BT.lf) [6,3840,4369,61440,61986] (BT.nd BT.lf [6,3840,4369,61986] BT.lf)))) [6,3840,4383,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,7953,17476,34952,61440] BT.lf) [6,3840,8192,17476,34952,61440] (BT.nd BT.lf [6,3840,8738,13107,17476,61440] BT.lf)) [6,3840,8738,13107,61440] (BT.nd (BT.nd BT.lf [6,3840,8738,17476,21845,61440] BT.lf) [6,3840,8738,17476,30583,61440] (BT.nd BT.lf [6,3840,8738,17476,34952,61440] BT.lf))) [6,3840,8738,17476,34952,61986] (BT.nd (BT.nd (BT.nd BT.lf [6,3840,8738,17476,34952,65280] BT.lf) [6,3840,8738,17476,43690,61440] (BT.nd BT.lf [6,3840,8738,17476,52428,61440] BT.lf)) [6,3840,8738,17476,61166,61440] (BT.nd (BT.nd BT.lf [6,3840,8738,52428,61440] BT.lf) [6,3840,8738,61166,61440] (BT.nd BT.lf [6,3840,8751,17476,34952,61440] BT.lf))))) [6,3840,12066,17476,34952,61440] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3840,17476,21845,34952,61440] BT.lf) [6,3840,17476,26214,34952,61440] (BT.nd BT.lf [6,3840,17476,34952,56797,61440] BT.lf)) [6,3840,17476,34952,61166,61440] (BT.nd (BT.nd BT.lf [6,4369,8738,17476,61440,61695] BT.lf) [6,4369,8738,17476,61440,65280] (BT.nd BT.lf [6,4369,8738,61440,61695] BT.lf))) [6,4369,8738,61440,65280] (BT.nd (BT.nd (BT.nd BT.lf [6,4369,17476,34952,61440,61695] BT.lf) [6,4369,17476,34952,61440,65280] (BT.nd BT.lf [6,8738,17476,34952,61440,61695] BT.lf)) [6,8738,17476,34952,61440,65280] (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,8738] BT.lf) [7,15,240,3840,4369,8738,17476] (BT.nd BT.lf [7,15,240,3840,4369,8738,17476,34952,61440] BT.lf)))) [7,15,240,3840,4369,8738,61440] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,15,240,3840,4369,17476,34952] BT.lf) [7,15,240,3840,8738,17476,34952] (BT.nd BT.lf [7,15,240,4369,8738,17476,61440] BT.lf)) [7,15,240,4369,8738,61440] (BT.nd (BT.nd BT.lf [7,15,240,4369,17476,34952,61440] BT.lf) [7,15,240,8738,17476,34952,61440] (BT.nd BT.lf [7,15,3840,4369,8738,17476,61440] BT.lf))) [7,15,3840,4369,8738,61440] (BT.nd (BT.nd (BT.nd BT.lf [7,15,3840,4369,17476,34952,61440] BT.lf) [7,15,3840,8738,17476,34952,61440] (BT.nd BT.lf [7,3840,4369,8738,17476,34952,61440] BT.lf)) [7,3840,4369,8738,17476,61440] (BT.nd (BT.nd BT.lf [7,3840,4369,8738,61440] BT.lf) [7,3840,4369,17476,34952,61440] (BT.nd BT.lf [7,3840,8738,17476,34952,61440] BT.lf)))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,204,3840,4369,61986],[]),([3,255,4915],[(0,272449),(2,262219),(4,272449),(6,65803)]),([3,255,60620],[(0,65803),(2,262219),(4,65803),(6,272449)]),([3,3840,4607,8738,64716],[]),([3,4369,8959,53196,61440],[]),([3,4383,8946,53196,61440],[]),([3,4607,8738,20292,63624],[]),([3,4607,8738,53196,61440],[])]

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([3,4881,65314],[(0,262210),(2,262210),(4,262210),(6,263233)]),([3,4915,65280],[(0,262219),(2,262219),(4,262219),(6,272449)]),([3,7936,62259],[(0,272449),(2,272449),(4,272449),(6,262219)]),([3,7953,62242],[(0,262210),(2,262210),(4,262210),(6,263233)]),([3,7953,62259,65314],[(60,262210),(76,272449),(84,262210)]),([3,8447,13107],[(0,272449),(2,262219),(4,272449),(6,65803)]),([3,8447,52428],[(0,65803),(2,262219),(4,65803),(6,272449)]),([3,13107,57088],[(0,262219),(2,262219),(4,262219),(6,272449)])]

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([3,52428,57088],[(0,262219),(2,262219),(4,262219),(6,65803)]),([3,60620,65280],[(0,262219),(2,262219),(4,262219),(6,65803)]),([4,15,240,4915],[(0,272449),(2,262219),(4,272449),(6,266443),(8,272449),(10,65803),(57,272449),(58,272449)]),([4,15,240,60620],[(0,65803),(2,262219),(4,65803),(6,266443),(8,65803),(10,272449),(57,65803),(58,65803)]),([4,15,3840,4593,8738,64716],[]),([4,15,4369,8946,53196,61440],[]),([4,15,4593,8738,20292,63624],[]),([4,15,4593,8738,53196,61440],[(72,1)])]

noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,15,8432,13107],[(0,272449),(2,262219),(4,272449),(6,266443),(8,272449),(10,65803),(57,272449),(58,272449)]),([4,15,8432,52428],[(0,65803),(2,262219),(4,65803),(6,266443),(8,65803),(10,272449),(57,65803),(58,65803)]),([4,204,3840,4369,8738,61440],[]),([4,255,546,4369],[(0,272449),(2,262219),(4,272449),(6,66859),(8,272449),(10,65803),(81,305218),(82,272449)]),([4,255,3840,4369,8738,64716],[]),([4,255,3840,4369,52428,61986],[]),([4,255,4369,8738,20292,63624],[]),([4,255,4369,8738,53196,61440],[])]

noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,255,4369,64716],[(0,66859),(2,262219),(4,66859),(6,66859),(8,66859),(10,305218),(58,65835),(82,66859),(85,65803)]),([4,255,4369,64989],[(0,66859),(2,262219),(4,66859),(6,66859),(8,66859),(10,272449),(82,66859),(85,66859)]),([4,255,4881,8738],[(0,272449),(2,262219),(4,272449),(6,65803),(8,272449),(10,272449),(73,76033),(78,272449),(82,76033)]),([4,255,7953,13107],[(0,272450),(2,262223),(4,272450),(6,272450),(8,272450),(10,66827),(58,272449),(85,76033)]),([4,255,7953,52428],[(0,66827),(2,262223),(4,66827),(6,66827),(8,66827),(10,272450),(58,65803),(81,65803)]),([4,255,8192,13107],[(0,272449),(2,262219),(4,272449),(6,272449),(8,272449),(10,65803),(57,272449),(58,272449),(82,272449),(85,272449)]),([4,255,8192,52428],[(0,65803),(2,262219),(4,65803),(6,65803),(8,65803),(10,272449),(57,65803),(58,65803),(81,76033),(82,65803)]),([4,255,8738,12561],[(0,272449),(2,262219),(4,272449),(6,66859),(8,272449),(10,65803)])]

noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([4,255,17476,43144],[(0,98572),(2,262219),(4,98572),(6,272449),(8,98572),(10,273505),(81,65803),(82,98572)]),([4,256,7953,61986],[(0,294978),(2,294978),(4,294978),(6,294978),(8,294978),(10,296001),(58,294978),(61,294978),(73,296001),(74,294978)]),([4,512,4369,65314],[(0,262210),(2,262210),(4,262210),(6,262210),(8,262210),(10,263233),(57,262210),(58,262210),(74,262210),(77,262210)]),([4,546,4369,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,272449),(57,262219),(58,262219)]),([4,3549,3840,4369],[(0,272449),(2,305218),(4,272449),(6,76033),(8,272449),(10,65803)]),([4,3549,3840,61166],[(0,65803),(2,305218),(4,65803),(6,76033),(8,65803),(10,272449)]),([4,3549,4369,61695],[(0,76033),(2,305218),(4,76033),(6,76033),(8,76033),(10,272449)]),([4,3840,4095,4915],[(0,272449),(2,76033),(4,272449),(6,393294),(8,272449),(10,65803),(58,272449),(61,272449)])]

noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([4,3840,4096,62259],[(0,272449),(2,272449),(4,272449),(6,272449),(8,272449),(10,262219),(57,272449),(58,272449),(82,272449),(85,272449)]),([4,3840,4369,8959,52428,61440],[]),([4,3840,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,272449)]),([4,3840,4369,61986,65331],[(100,305218),(108,305218),(116,305218)]),([4,3840,4369,62242],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,394305),(57,262210),(58,272450)]),([4,3840,4369,62259,65314],[(76,393282),(108,305217),(116,305218)]),([4,3840,4383,8946,52428,61440],[]),([4,3840,4607,8738,17476,63624],[])]

noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([4,3840,4607,8738,52428,61440],[]),([4,3840,4881,61986],[(0,393282),(2,393282),(4,393282),(6,393282),(8,393282),(10,272449),(73,262219),(74,393282)]),([4,3840,4915,61440],[(0,393294),(2,76033),(4,393294),(6,393294),(8,393294),(10,272449),(73,262219),(74,393294)]),([4,3840,7953,61986,62259],[(84,272449),(100,393282),(108,393282)]),([4,3840,8959,13107],[(0,272449),(2,272449),(4,272449),(6,393295),(8,272449),(10,65803),(58,272449),(61,272449),(77,403521)]),([4,3840,8959,52428],[(0,65803),(2,65803),(4,65803),(6,393295),(8,65803),(10,272449),(58,65803),(61,65803),(73,76161)]),([4,3840,12287,13107],[(0,272449),(2,76033),(4,272449),(6,393295),(8,272449),(10,65803),(58,272449),(61,272449)]),([4,3840,12287,52428],[(0,65803),(2,76033),(4,65803),(6,393295),(8,65803),(10,272449),(58,65803),(61,65803)])]

noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([4,3840,13107,53248],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,272449),(73,262219),(74,393295)]),([4,3840,52428,53248],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,65803),(73,262219),(74,393295)]),([4,3840,60620,61440],[(0,393294),(2,76033),(4,393294),(6,393294),(8,393294),(10,65803),(73,262219),(74,393294)]),([4,3840,61166,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,65803)]),([4,4369,7936,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,262219),(73,272449),(74,305218)]),([4,4369,7953,61986,65314],[(84,262210),(100,294978),(108,305218)]),([4,4369,8447,8738],[(0,305218),(2,65803),(4,305218),(6,262219),(8,305218),(10,66859),(73,272449),(74,305218)]),([4,4369,8738,57088],[(0,262219),(2,65803),(4,262219),(6,262219),(8,262219),(10,305218),(57,262219),(58,262219)])]

noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([4,4369,8959,17476,36744,61440],[]),([4,4369,56797,57088],[(0,262219),(2,65803),(4,262219),(6,262219),(8,262219),(10,66859),(58,262219),(61,262219)]),([4,4369,61695,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,76033)]),([4,4369,64716,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,66859),(58,262219),(61,262219),(77,294987)]),([4,4369,64989,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,66859),(58,262219),(61,262219)]),([4,4383,8946,17476,36744,61440],[]),([4,4607,8738,17476,36744,61440],[(144,0)]),([4,4881,8738,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,272449),(58,262219),(81,272449),(82,262219)])]

noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([4,4881,12066,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,262210),(81,262210),(82,393295)]),([4,7936,8738,61713],[(0,272449),(2,272449),(4,272449),(6,272449),(8,272449),(10,305218),(81,305218),(82,272449)]),([4,7936,13107,61440],[(0,272449),(2,76033),(4,272449),(6,65803),(8,272449),(10,272449),(74,272449),(81,272449),(82,262219)]),([4,7936,52428,61440],[(0,65803),(2,76033),(4,65803),(6,272449),(8,65803),(10,65803),(74,65803),(81,65803),(86,65803)]),([4,7953,8738,61696],[(0,262223),(2,262223),(4,262223),(6,262223),(8,262223),(10,294978),(81,294978),(82,262223)]),([4,7953,8994,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,262210),(81,262210),(82,393295)]),([4,7953,13107,65280],[(0,262223),(2,262223),(4,262223),(6,262223),(8,262223),(10,272450),(61,262219),(77,272449)]),([4,7953,52428,65280],[(0,262223),(2,262223),(4,262223),(6,262223),(8,262223),(10,66827),(57,262219),(77,65803)])]

noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([4,8192,13107,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,272449),(58,262219),(61,262219),(74,262219),(77,262219)]),([4,8192,52428,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,65803),(57,262219),(58,262219),(74,262219),(77,262219)]),([4,8447,17476,34952],[(0,98572),(2,262219),(4,98572),(6,272449),(8,98572),(10,273505),(81,65803),(82,98572)]),([4,8738,12561,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,272449)]),([4,12032,13107,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,272449)]),([4,12032,52428,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,65803)]),([4,17476,34952,57088],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,98572),(57,262219),(58,262219)]),([4,17476,43144,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,98572),(57,262219),(58,262219)])]

noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([4,61166,61695,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,76033)]),([5,0,3840,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(57,305218),(58,305218),(61,305218),(73,305218),(74,305218),(77,305218),(97,272449),(98,305218),(101,305218)]),([5,1,3840,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272453),(57,305218),(58,305218),(61,305218),(73,305218),(74,305218),(77,305218),(97,272453),(98,305218),(101,305218)]),([5,2,3840,4369,61986],[(0,305222),(2,305222),(4,305222),(6,305222),(8,305222),(10,305222),(12,305222),(14,272449),(57,305222),(58,305222),(61,305218),(73,305222),(74,305222),(77,305218),(97,272449),(98,305222),(101,305222)]),([5,4,3840,4369,61986],[(0,305250),(2,305250),(4,305250),(6,305250),(8,305250),(10,305250),(12,305250),(14,272481),(57,305250),(58,305250),(61,305218),(73,305250),(74,305250),(77,305218),(97,272481),(98,305250),(101,305218)]),([5,15,240,546,4369],[(0,272449),(2,262219),(4,272449),(6,266443),(8,272449),(10,66859),(12,272449),(14,65803),(57,272449),(58,272449),(113,305218),(114,272449)]),([5,15,240,3840,4369,8738,64716],[(96,1)]),([5,15,240,3840,4369,52428,61986],[])]

noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,4369,8738,20292,63624],[(72,1)]),([5,15,240,4369,8738,53196,61440],[(72,1),(96,1)]),([5,15,240,4369,64716],[(0,66859),(2,262219),(4,66859),(6,266443),(8,66859),(10,66859),(12,66859),(14,305218),(57,66859),(58,66859),(74,65835),(82,66859),(114,66859),(117,65803)]),([5,15,240,4369,64989],[(0,66859),(2,262219),(4,66859),(6,266443),(8,66859),(10,66859),(12,66859),(14,272449),(57,66859),(58,66859),(114,66859),(117,66859)]),([5,15,240,4881,8738],[(0,272449),(2,262219),(4,272449),(6,266443),(8,272449),(10,65803),(12,272449),(14,272449),(57,272449),(58,272449),(97,76033),(105,207109),(114,207109)]),([5,15,240,7953,13107],[(0,272450),(2,262223),(4,272450),(6,266447),(8,272450),(10,272450),(12,272450),(14,66827),(57,272450),(58,272450),(74,272449),(82,272450),(117,207109)]),([5,15,240,7953,52428],[(0,66827),(2,262223),(4,66827),(6,266447),(8,66827),(10,66827),(12,66827),(14,272450),(57,66827),(58,66827),(74,65803),(82,66827),(113,65803)]),([5,15,240,8192,13107],[(0,272449),(2,262219),(4,272449),(6,266443),(8,272449),(10,272449),(12,272449),(14,65803),(57,272449),(58,272449),(72,1),(73,272449),(74,272449),(81,272449),(82,272449),(114,272449),(117,272449)])]

noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,240,8192,52428],[(0,65803),(2,262219),(4,65803),(6,266443),(8,65803),(10,65803),(12,65803),(14,272449),(57,65803),(58,65803),(72,1),(73,65803),(74,65803),(81,65803),(82,65803),(113,207109),(114,65803)]),([5,15,240,8738,12561],[(0,272449),(2,262219),(4,272449),(6,266443),(8,272449),(10,66859),(12,272449),(14,65803),(57,272449),(58,272449)]),([5,15,240,17476,43144],[(0,98572),(2,262219),(4,98572),(6,266443),(8,98572),(10,272449),(12,98572),(14,273505),(57,98572),(58,98572),(113,65803),(114,98572)]),([5,15,3549,3840,4369],[(0,272449),(2,272449),(4,272449),(6,305218),(8,272449),(10,207109),(12,272449),(14,65803),(57,272449),(61,272449),(73,272449),(74,272449),(77,272449),(97,394305),(101,272453)]),([5,15,3840,4369,8946,52428,61440],[]),([5,15,3840,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(57,305218),(58,305218),(61,305218),(73,305218),(77,305218),(97,393282),(101,305222)]),([5,15,3840,4593,8738,17476,63624],[]),([5,15,3840,4593,8738,52428,61440],[(96,1)])]

noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,3840,8946,13107],[(0,272449),(2,393295),(4,272449),(6,272449),(8,272449),(10,397519),(12,272449),(14,65803),(57,272449),(58,272449),(73,272449),(74,272449),(82,272449),(85,272449),(109,403521)]),([5,15,3840,8946,52428],[(0,65803),(2,393295),(4,65803),(6,65803),(8,65803),(10,397519),(12,65803),(14,272449),(57,65803),(58,65803),(73,65803),(74,65803),(82,65803),(85,65803),(105,207237)]),([5,15,3840,61166,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,65803),(57,305218),(58,305218),(61,305218),(73,305218),(77,305218),(97,393282),(101,305222)]),([5,15,3855,4369,61986],[(0,305218),(2,262219),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(58,305218),(61,305218)]),([5,15,4369,8432,8738],[(0,305218),(2,262219),(4,305218),(6,65803),(8,305218),(10,266443),(12,305218),(14,66859),(73,305218),(74,305218),(105,272449),(106,305218)]),([5,15,4369,8946,17476,36744,61440],[]),([5,15,4369,61680,61986],[(0,305218),(2,262219),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,207109),(73,305218),(74,305218)]),([5,15,4369,61695,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,207109),(57,305218),(61,305218),(73,305218),(74,305218),(77,305218),(97,393282),(101,305222)])]

noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([5,15,4593,8738,17476,36744,61440],[(72,1),(192,0)]),([5,15,8432,17476,34952],[(0,98572),(2,262219),(4,98572),(6,266443),(8,98572),(10,272449),(12,98572),(14,273505),(57,98572),(58,98572),(113,65803),(114,98572)]),([5,255,512,4369,8738],[(0,272449),(2,262219),(4,272449),(6,272449),(8,272449),(10,65803),(12,272449),(14,272449),(57,272449),(58,272449),(81,76033),(82,272449),(97,76033),(102,272449),(106,272449),(109,272449),(113,272449),(114,76033)]),([5,255,3840,4369,8738],[(0,305218),(2,393295),(4,305218),(6,305218),(8,305218),(10,65803),(12,305218),(14,66859),(57,305218),(58,305218),(81,305218),(97,80257),(109,272449),(113,272449),(114,305218)]),([5,255,3840,4369,8738,17476,63624],[]),([5,255,3840,4369,8738,52428,61440],[]),([5,255,3840,4369,13107],[(0,305218),(2,393295),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,66859),(57,305218),(58,305218),(74,305217),(81,305218),(82,272450),(109,76161),(114,305218),(117,305218)]),([5,255,3840,4369,17476,34952,61986],[])]

noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([5,255,3840,4369,52428],[(0,66859),(2,393295),(4,66859),(6,66859),(8,66859),(10,66859),(12,66859),(14,305218),(57,66859),(58,66859),(74,65835),(81,66859),(82,66827),(105,76161),(113,65803),(114,66859)]),([5,255,3840,4369,56797],[(0,66859),(2,393295),(4,66859),(6,66859),(8,66859),(10,65803),(12,66859),(14,305218),(57,66859),(58,66859),(81,66859),(101,272449),(105,272449),(114,66859),(117,66859)]),([5,255,3840,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(57,305218),(58,305218),(61,305218),(73,305218),(77,305218),(81,305218),(97,393282),(101,305230),(109,272449),(114,305218)]),([5,255,3840,8738,13107],[(0,272449),(2,393295),(4,272449),(6,272449),(8,272449),(10,272449),(12,272449),(14,65803),(57,272449),(58,272449),(73,272449),(74,272449),(82,272449),(85,272449),(109,403521),(114,272449),(117,272449)]),([5,255,3840,8738,52428],[(0,65803),(2,393295),(4,65803),(6,65803),(8,65803),(10,65803),(12,65803),(14,272449),(57,65803),(58,65803),(73,65803),(74,65803),(82,65803),(85,65803),(105,76161),(113,66859),(114,65803)]),([5,255,3840,8738,61166],[(0,65803),(2,393295),(4,65803),(6,65803),(8,65803),(10,65803),(12,65803),(14,305218),(57,65803),(58,65803),(73,65803),(85,65803),(109,65807),(114,65803),(117,65803)]),([5,255,3855,4369,8738],[(0,305218),(2,262219),(4,305218),(6,305218),(8,305218),(10,65803),(12,305218),(14,66859),(58,305218),(81,305218),(109,272449),(113,272449),(114,305218)]),([5,255,4095,4369,8738],[(0,305218),(2,262219),(4,305218),(6,305218),(8,305218),(10,65803),(12,305218),(14,66859),(58,305218),(61,305218),(81,305218),(109,272449),(110,272449),(113,272449),(114,305218)])]

noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([5,255,4369,7953,8738],[(0,305218),(2,262223),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,66859),(58,305218),(74,305218),(82,305218),(85,305218),(97,80129),(105,80129),(106,305218),(117,272449)]),([5,255,4369,8192,8738],[(0,305218),(2,262219),(4,305218),(6,65803),(8,305218),(10,305218),(12,305218),(14,66859),(73,305218),(74,305218),(81,272449),(82,305218),(105,272449),(106,305218),(114,305218),(117,305218)]),([5,255,4369,8738,17476,36744,61440],[(192,0)]),([5,255,4369,8738,20292],[(0,305250),(2,393291),(4,305250),(6,98571),(8,305250),(10,99627),(12,305250),(14,305250),(73,76161),(81,272481),(82,305250),(98,305218),(106,305250),(118,272449)]),([5,255,4369,8738,61440],[(0,305218),(2,262219),(4,305218),(6,65803),(8,305218),(10,66859),(12,305218),(14,305218),(81,272449),(82,305218),(97,76033),(98,305218),(106,305218),(113,305218),(118,305218)]),([5,255,4369,8738,61455],[(0,305218),(2,266319),(4,305218),(6,65803),(8,305218),(10,66859),(12,305218),(14,305218),(81,272449),(82,305218),(98,305218),(106,305218),(118,305222)]),([5,255,4369,8738,61695],[(0,305218),(2,393295),(4,305218),(6,65803),(8,305218),(10,66859),(12,305218),(14,305218),(73,80257),(81,272449),(82,305218),(98,305218),(101,305218),(106,305218),(118,272449)]),([5,255,4369,8738,61713],[(0,305218),(2,262219),(4,305218),(6,305218),(8,305218),(10,66859),(12,305218),(14,305218),(58,305218),(81,76033),(82,305218),(98,305218),(106,305218),(109,305218),(113,305218),(118,305218)])]

noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([5,255,4369,8738,62532],[(0,306274),(2,262219),(4,306274),(6,98572),(8,306274),(10,99628),(12,306274),(14,306274),(81,273505),(82,306274),(98,306242),(106,306274),(113,306274),(118,305218)]),([5,255,4369,13107,61440],[(0,305218),(2,262219),(4,305218),(6,305218),(8,305218),(10,66859),(12,305218),(14,305218),(58,305217),(82,305218),(85,305218),(97,76033),(98,305218),(106,305218),(109,272449),(113,305218),(118,305218)]),([5,255,4369,17476,63624],[(0,99628),(2,262219),(4,99628),(6,99628),(8,99628),(10,99628),(12,99628),(14,66859),(58,98604),(81,99628),(82,99628),(106,99628),(109,98572),(113,66859),(114,99628)]),([5,255,4369,52428,61440],[(0,66859),(2,262219),(4,66859),(6,66859),(8,66859),(10,305218),(12,66859),(14,66859),(58,65835),(81,65803),(82,66859),(97,76033),(98,66859),(106,66859),(109,65803),(113,66859),(114,76033)]),([5,255,4369,56797,61440],[(0,66859),(2,262219),(4,66859),(6,65803),(8,66859),(10,305218),(12,66859),(14,66859),(82,66859),(85,66859),(97,76033),(98,66859),(106,66859),(113,66859),(114,272449)]),([5,255,4369,61440,61986],[(0,305218),(2,262219),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(73,305218),(74,305218),(82,305218),(106,305218),(114,305218),(117,305218)]),([5,255,7953,17476,34952],[(0,99596),(2,262223),(4,99596),(6,99596),(8,99596),(10,272450),(12,99596),(14,273506),(58,98572),(81,99596),(105,98572),(113,66827),(114,99596)]),([5,255,8192,17476,34952],[(0,98572),(2,262219),(4,98572),(6,98572),(8,98572),(10,272449),(12,98572),(14,273505),(57,98572),(58,98572),(80,0),(81,98572),(82,98572),(105,65803),(106,98572),(113,65803),(114,98572)])]

noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,255,8738,13107,61440],[(0,272449),(2,262219),(4,272449),(6,272449),(8,272449),(10,65803),(12,272449),(14,272449),(58,272449),(82,272449),(85,272449),(97,76033),(98,272449),(109,272449),(110,272449),(118,272449)]),([5,255,8738,52428,61440],[(0,65803),(2,262219),(4,65803),(6,65803),(8,65803),(10,272449),(12,65803),(14,65803),(58,65803),(81,66859),(82,65803),(97,76033),(98,65803),(109,65803),(110,65803),(114,76033)]),([5,255,8738,61166,61440],[(0,65803),(2,262219),(4,65803),(6,65803),(8,65803),(10,305218),(12,65803),(14,65803),(82,65803),(85,65803),(97,76033),(98,65803),(105,305218),(110,65803),(118,65803)]),([5,256,3840,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,394305),(57,305218),(58,305218),(61,305218),(73,305218),(74,305218),(77,305218),(81,305218),(82,305218),(97,394305),(98,305218),(101,305218)]),([5,256,7953,8738,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,294978),(58,393295),(61,393295),(73,393295),(74,393295),(97,294978),(98,393295),(113,294978),(114,393295)]),([5,512,3840,4369,61986],[(0,393282),(2,393282),(4,393282),(6,393282),(8,393282),(10,393282),(12,393282),(14,272449),(57,305218),(58,393282),(61,393282),(73,393282),(74,393282),(77,305218),(97,272449),(98,393282),(101,393282),(105,262219),(106,393282)]),([5,512,4369,8738,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,272449),(57,262219),(58,262219),(74,262219),(77,262219),(81,262219),(82,262219),(98,262219),(101,262219),(113,272449),(114,262219)]),([5,512,4369,12066,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,262210),(57,393295),(58,393295),(74,393295),(77,393295),(97,262210),(98,393295),(113,262210),(114,393295)])]

noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,546,3840,4095,4369],[(0,272449),(2,66859),(4,272449),(6,76033),(8,272449),(10,393294),(12,272449),(14,65803),(74,272449),(77,272449),(82,272449),(85,272449),(97,305218),(98,272449)]),([5,546,3840,4369,61440],[(0,393294),(2,66859),(4,393294),(6,76033),(8,393294),(10,393294),(12,393294),(14,272449),(73,393294),(74,393294),(97,305218),(98,393294),(105,262219),(106,393294)]),([5,1024,3840,4369,61986],[(0,306242),(2,306242),(4,306242),(6,306242),(8,306242),(10,306242),(12,306242),(14,273473),(57,305218),(58,306242),(61,306242),(73,306242),(74,306242),(77,305218),(97,273473),(98,306242),(101,305218)]),([5,3549,3840,4369],[(1,272449),(3,272449),(5,272449),(7,272449),(9,262219),(11,262219),(59,272449),(63,272449),(75,272449),(79,262219),(83,66859),(87,394305)]),([5,3549,3840,4369,8738],[(0,272449),(2,393295),(4,272449),(6,76033),(8,272449),(10,65803),(12,272449),(14,272449),(57,272449),(97,80257),(98,272449),(102,272449),(106,272449),(110,272449),(113,272449),(114,262219),(118,272449)]),([5,3549,3840,4369,17476],[(0,273505),(2,306255),(4,273505),(6,76033),(8,273505),(10,98572),(12,273505),(14,273505),(98,272449),(102,273505),(106,272481),(110,273473),(113,273505),(114,272449),(118,272449)]),([5,3549,3840,4369,61440],[(0,272449),(2,305218),(4,272449),(6,76033),(8,272449),(10,65803),(12,272449),(14,272449),(73,66859),(97,66859),(98,272449),(102,272449),(105,262219),(106,272449),(110,272449),(114,262219),(118,272449)]),([5,3549,3840,4369,61986],[(0,272449),(2,272449),(4,272449),(6,76033),(8,272449),(10,65803),(12,272449),(14,272449),(57,272449),(61,393282),(73,272449),(77,305218),(97,305218),(98,272449),(101,305218),(102,272449),(106,272449),(110,272449),(114,262219),(118,272449)])]

noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,3840,4369,61986],[(0,305218),(2,305218),(8,305218),(10,305218),(12,305218),(14,272449),(49,305218),(50,305218),(53,305218),(54,305218),(73,305218),(77,305218),(97,272449),(101,393282)]),([5,3840,3855,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(58,305218),(61,305218),(62,305218),(81,305218),(85,305218),(105,305218),(109,393286)]),([5,3840,4095,4369,8738],[(0,305218),(2,76033),(4,305218),(6,393295),(8,305218),(10,65803),(12,305218),(14,66859),(58,305218),(61,305218),(105,80257),(110,272449),(113,272449),(114,305218)]),([5,3840,4095,4369,13107],[(0,305218),(2,76033),(4,305218),(6,393295),(8,305218),(10,305218),(12,305218),(14,66859),(58,305218),(61,305218),(74,272450),(82,272449),(110,262219),(114,305218),(117,305218)]),([5,3840,4095,4369,52428],[(0,66859),(2,76033),(4,66859),(6,393295),(8,66859),(10,66859),(12,66859),(14,305218),(58,66859),(61,66859),(74,66827),(82,65803),(110,262219),(113,65803),(114,66859)]),([5,3840,4095,4369,56797],[(0,66859),(2,76033),(4,66859),(6,393295),(8,66859),(10,65803),(12,66859),(14,305218),(58,66859),(61,66859),(109,272449),(110,272449),(114,66859),(117,66859)]),([5,3840,4095,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(58,305218),(61,305218),(62,305218),(81,305218),(85,305218),(105,305218),(109,393294),(110,272449),(114,305218)]),([5,3840,4095,8738,13107],[(0,272449),(2,76033),(4,272449),(6,393295),(8,272449),(10,272449),(12,272449),(14,65803),(58,272449),(61,272449),(74,272449),(81,272449),(82,272449),(114,272449),(117,272449)])]

noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4095,8738,52428],[(0,65803),(2,76033),(4,65803),(6,393295),(8,65803),(10,65803),(12,65803),(14,272449),(58,65803),(61,65803),(74,65803),(81,65803),(82,65803),(113,66859),(114,65803)]),([5,3840,4095,8738,61166],[(0,65803),(2,76033),(4,65803),(6,393295),(8,65803),(10,65803),(12,65803),(14,305218),(58,65803),(61,65803),(81,65803),(86,65803),(114,65803),(117,65803)]),([5,3840,4096,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(57,305218),(58,305218),(62,305218),(81,305218),(82,305218),(85,305218),(105,272449),(106,305218),(109,305218),(113,272449),(114,305218)]),([5,3840,4096,8738,61713],[(0,272449),(2,272449),(4,272449),(6,272449),(8,272449),(10,272449),(12,272449),(14,305218),(57,272449),(58,272449),(81,272449),(82,272449),(106,272449),(109,272449),(113,305218),(114,272449)]),([5,3840,4096,13107,61440],[(0,272449),(2,76033),(4,272449),(6,272449),(8,272449),(10,65803),(12,272449),(14,272449),(57,272449),(58,272449),(82,272449),(85,272449),(97,262219),(98,272449),(106,272449),(109,272449),(113,272449),(114,262219)]),([5,3840,4096,52428,61440],[(0,65803),(2,76033),(4,65803),(6,65803),(8,65803),(10,272449),(12,65803),(14,65803),(57,65803),(58,65803),(81,262219),(82,65803),(97,262219),(98,65803),(106,65803),(109,65803),(113,65803),(118,65803)]),([5,3840,4369,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(12,305218),(14,262219),(58,305218),(62,305218),(65,305218),(66,305218),(69,305218),(70,305218),(105,262219),(109,305218)]),([5,3840,4369,4383,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,394305),(58,305218),(74,305218),(78,305218),(82,305218),(85,305218),(86,305218),(113,393282),(117,305222)])]

noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4369,7953,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,66859),(61,305218),(62,305218),(74,305218),(77,305218),(78,305218),(82,305218),(85,305218),(86,305218),(117,272449)]),([5,3840,4369,8192,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(73,305218),(74,305218),(78,305218),(81,305218),(82,305218),(86,305218),(113,272449),(114,305218),(117,305218)]),([5,3840,4369,8738,8959],[(0,80257),(2,80257),(4,80257),(6,65803),(8,80257),(10,80257),(12,80257),(14,393295),(57,80129),(74,80257),(77,76033),(81,272449),(82,80257),(98,80257),(101,76033),(114,80257),(117,80257)]),([5,3840,4369,8738,12287],[(0,80257),(2,76033),(4,80257),(6,65803),(8,80257),(10,66859),(12,80257),(14,393295),(81,272449),(82,305218),(98,80257),(101,80257),(114,80257),(117,80257)]),([5,3840,4369,8738,53248],[(0,393295),(2,76033),(4,393295),(6,65803),(8,393295),(10,66859),(12,393295),(14,80257),(81,393295),(82,393295),(97,262219),(98,393295),(113,305218),(114,393295)]),([5,3840,4369,8738,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(81,393295),(82,393295),(97,262219),(98,393295),(113,305218),(114,393295)]),([5,3840,4369,8738,61442],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305222),(81,393295),(82,393295),(97,262219),(98,393295),(113,305222),(114,393295)]),([5,3840,4369,8738,61696],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(57,262223),(58,272463),(81,393295),(82,393295),(97,296011),(98,393295),(113,305218),(114,393295)])]

noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4369,8738,61952],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(74,305231),(81,393295),(82,393295),(98,393295),(113,272449),(114,393295)]),([5,3840,4369,8738,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(74,305231),(78,393282),(81,393295),(82,393295),(86,305218),(98,393295),(113,272449),(114,393295),(117,393295)]),([5,3840,4369,8738,62464],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,306242),(81,393295),(82,393295),(97,262220),(98,393295),(113,306242),(114,393295)]),([5,3840,4369,8738,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(57,262223),(77,262219),(81,393295),(82,393295),(98,393295),(101,393295),(114,393295)]),([5,3840,4369,8738,65314],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(57,262223),(77,262219),(78,393282),(81,393295),(82,393295),(98,393295),(101,393295),(114,393295),(117,393295)]),([5,3840,4369,8739,61440],[(0,397391),(2,76037),(4,397391),(6,397391),(8,397391),(10,397391),(12,397391),(14,305218),(81,397391),(82,393295),(97,266315),(98,397391),(113,305218),(114,397391)]),([5,3840,4369,8751,8946],[(0,211010),(2,211010),(4,211010),(6,65803),(8,211010),(10,197711),(12,211010),(14,66767),(57,211010),(74,80066),(77,206914),(98,211010),(101,206914)]),([5,3840,4369,8751,61986],[(0,397378),(2,397378),(4,397378),(6,397378),(8,397378),(10,397378),(12,397378),(14,272449),(74,305218),(78,393282),(82,393282),(86,305218),(98,397378),(113,393282),(117,393295)])]

noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4369,8959,17476,34952,61440],[(96,0)]),([5,3840,4369,8994,61440],[(0,393295),(2,76066),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(57,393295),(58,393295),(81,393295),(82,393295),(97,296011),(98,393295),(113,305218),(114,393295)]),([5,3840,4369,12066,61986],[(0,305231),(2,305231),(4,305231),(6,305231),(8,305231),(10,305231),(12,305231),(14,272449),(57,305231),(74,305231),(77,305231),(78,305218),(82,305231),(86,305218),(101,393295),(113,272449),(117,393295)]),([5,3840,4369,12834,61440],[(0,305218),(2,76033),(4,305218),(6,65803),(8,305218),(10,66859),(12,305218),(14,305218),(82,393295),(97,262219),(98,305218),(106,305218),(113,305218),(114,272449)]),([5,3840,4369,13107,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(58,393295),(82,393295),(85,393295),(97,262219),(98,393295),(109,272449),(113,305218)]),([5,3840,4369,13107,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,262219),(58,393295),(74,305231),(78,393282),(82,393295),(85,393295),(86,305218),(98,393295),(109,272449),(113,262219),(117,272449)]),([5,3840,4369,13107,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(57,262223),(58,393295),(77,393291),(82,393295),(85,393295),(98,393295),(101,393295),(109,305217)]),([5,3840,4369,16384,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(73,305218),(74,305218),(78,305218),(81,305218),(82,305218),(86,305218),(113,272449),(114,305218),(117,305218)])]

noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4369,17476,61986],[(0,306255),(2,306255),(4,306255),(6,306255),(8,306255),(10,306255),(12,306255),(14,273505),(74,305231),(78,306242),(81,306255),(82,306255),(86,305218),(113,305218),(117,305218)]),([5,3840,4369,17487,61986],[(0,306242),(2,306242),(4,306242),(6,306242),(8,306242),(10,306242),(12,306242),(14,273473),(74,305218),(78,306242),(82,306242),(86,305218),(113,305218),(117,305222)]),([5,3840,4369,20292,61986],[(0,305231),(2,305231),(4,305231),(6,305231),(8,305231),(10,305231),(12,305231),(14,272481),(57,305231),(74,305231),(77,305231),(78,305218),(82,305231),(86,305218),(113,305218),(117,393282)]),([5,3840,4369,21845,61986],[(0,306255),(2,306255),(4,306255),(6,306255),(8,306255),(10,306255),(12,306255),(14,272449),(74,305231),(78,306242),(82,306255),(85,306255),(86,305218),(113,305218),(117,305218)]),([5,3840,4369,25122,61440],[(0,393296),(2,76033),(4,393296),(6,393296),(8,393296),(10,393296),(12,393296),(14,305218),(81,393296),(82,393296),(97,262219),(98,393296),(113,305218),(114,393296)]),([5,3840,4369,26214,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,273505),(74,305218),(78,305218),(81,305218),(82,305218),(86,305218),(113,305218),(117,393296)]),([5,3840,4369,30583,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(74,305218),(78,305218),(82,305218),(85,305218),(86,305218),(113,305218),(117,272449)]),([5,3840,4369,52428,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,66859),(58,393295),(81,393295),(82,393295),(97,262219),(98,393295),(109,65803),(113,66859)])]

noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4369,52428,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,262219),(58,393295),(74,305231),(78,393282),(81,393295),(82,393295),(86,305218),(98,393295),(109,65803),(113,305218),(117,305218)]),([5,3840,4369,52428,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,66859),(57,262223),(58,393295),(73,393291),(81,393295),(82,393295),(98,393295),(101,393295),(109,65835)]),([5,3840,4369,53248,56797],[(0,66859),(2,76033),(4,66859),(6,65803),(8,66859),(10,66859),(12,66859),(14,393295),(73,262219),(74,393295),(106,66859),(109,66859),(114,66859),(117,66859)]),([5,3840,4369,56797,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,66859),(82,393295),(85,393295),(97,262219),(98,393295),(113,66859),(118,66859)]),([5,3840,4369,56797,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(74,305231),(78,393282),(82,393295),(85,393295),(86,305218),(98,393295),(113,305218),(117,305218),(118,66859)]),([5,3840,4369,56797,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,66859),(57,262223),(73,262219),(82,393295),(85,393295),(98,393295),(101,393295),(118,393295)]),([5,3840,4369,61166,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,262219),(58,305218),(62,305218),(74,305218),(78,305218),(81,305218),(82,305218),(85,305218),(86,305218),(105,262219),(109,305218),(113,305218),(117,272449)]),([5,3840,4369,61440,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(73,262219),(74,305218),(78,305218),(82,305218),(86,305218),(106,305218),(113,272449),(114,305218),(117,305218)])]

noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4369,61440,62259],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,262219),(58,272450),(73,262219),(74,305218),(85,272449),(86,305218),(106,305218),(109,305218),(114,305218),(117,305218)]),([5,3840,4369,61440,64716],[(0,66859),(2,66859),(4,66859),(6,66859),(8,66859),(10,66859),(12,66859),(14,262219),(58,66827),(73,262219),(74,66859),(82,66859),(85,65803),(106,66859),(109,65803),(114,66859),(117,66859)]),([5,3840,4369,61440,64989],[(0,66859),(2,66859),(4,66859),(6,66859),(8,66859),(10,66859),(12,66859),(14,393294),(73,262219),(74,393294),(106,66859),(109,66859),(114,66859),(117,66859)]),([5,3840,4369,61455,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(73,266443),(74,305218),(78,305218),(82,305218),(86,305218),(113,393282),(117,305222)]),([5,3840,4369,61695,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,272449),(57,305218),(61,305218),(73,305218),(74,305218),(77,305218),(78,305218),(82,305218),(86,305218),(97,272449),(101,393282),(113,393282),(117,272449)]),([5,3840,4369,61713,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,262219),(58,305218),(74,305218),(78,305218),(82,305218),(85,305218),(86,305218),(109,305218),(113,262219),(117,305218)]),([5,3840,4369,61986],[(1,305218),(3,305218),(5,305218),(7,305218),(9,272449),(11,272449),(59,305218),(63,305218),(75,272449),(79,393282),(83,262219),(87,305218)]),([5,3840,4369,61986,61986],[(0,272449),(2,76033),(4,272449),(6,65803),(8,272449),(10,272449),(74,272449),(78,393282),(82,262219),(86,305218),(89,272449),(90,272449),(93,272449),(94,272449)])]

noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4369,61986,61999],[(0,393282),(2,393282),(4,393282),(6,393282),(8,393282),(10,272449),(12,393282),(14,393282),(74,393282),(98,305218),(102,393282),(106,393282),(110,305218),(114,393282),(117,393282),(118,272449)]),([5,3840,4369,61986,62259],[(0,262219),(2,76033),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,262219),(85,272449),(86,305218),(102,393282),(106,262219),(109,262219),(110,305218),(114,262219),(117,262219),(118,272449)]),([5,3840,4369,61986,62532],[(0,306254),(2,306254),(4,306254),(6,306254),(8,306254),(10,273505),(12,306254),(14,306254),(82,306254),(98,305230),(102,306242),(106,306254),(110,305218),(114,305218),(118,305218)]),([5,3840,4369,61986,63078],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,273505),(12,305218),(14,305218),(82,305218),(98,305218),(102,305218),(106,305218),(110,305218),(114,305218),(117,305218),(118,272449)]),([5,3840,4369,61986,65280],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,272449),(12,305218),(14,305218),(57,305218),(77,262219),(82,305218),(98,305218),(101,305218),(102,305218),(106,305218),(110,305218),(114,272449),(118,272449)]),([5,3840,4369,61986,65295],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,272449),(12,305218),(14,305218),(98,305218),(101,305218),(102,305218),(106,305218),(110,305218),(114,305218),(118,272449)]),([5,3840,4369,61986,65314],[(0,272449),(2,272449),(4,272449),(6,65803),(8,272449),(10,272449),(12,272449),(14,272449),(77,262219),(78,393282),(98,272449),(101,272449),(102,305218),(110,305218),(114,272449),(117,272449),(118,272449)]),([5,3840,4369,62532,63624],[(0,99406),(2,99406),(4,99406),(6,99406),(8,99406),(10,99406),(12,99406),(14,66670),(58,99406),(82,99406),(85,98382),(106,99406),(109,98382)])]

noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,4371,8738,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305222),(81,393295),(82,393295),(97,262219),(98,393295),(113,305222),(114,393295)]),([5,3840,4383,8946,17476,34952,61440],[(96,0)]),([5,3840,4383,13107,61440],[(0,393423),(2,207105),(4,393423),(6,393423),(8,393423),(10,393423),(12,393423),(14,305217),(58,393423),(85,393295),(97,262347),(98,393423),(109,272449),(113,305217)]),([5,3840,4383,52428,61440],[(0,393423),(2,207105),(4,393423),(6,393423),(8,393423),(10,393423),(12,393423),(14,65835),(58,393423),(81,393295),(97,262347),(98,393423),(109,65803),(113,65835)]),([5,3840,4607,8738,17476,34952,61440],[(96,0),(192,0)]),([5,3840,4881,8738,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(73,393295),(74,393295),(81,393295),(82,393295),(97,262219),(98,393295),(113,272449),(114,393295)]),([5,3840,7953,13107,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272450),(58,393295),(61,393295),(77,393295),(85,393295),(97,272450),(98,393295),(109,272449),(113,272450)]),([5,3840,7953,52428,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,66827),(58,393295),(61,393295),(73,393295),(81,393295),(97,66827),(98,393295),(109,65803),(113,66827)])]

noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,8192,13107,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(57,393295),(58,393295),(82,393295),(85,393295),(97,262219),(98,393295),(106,393295),(109,393295)]),([5,3840,8192,52428,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(57,393295),(58,393295),(81,393295),(82,393295),(97,262219),(98,393295),(106,393295),(109,393295)]),([5,3840,8738,12561,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(82,393295),(97,262219),(98,393295),(106,393295)]),([5,3840,8738,13107,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(58,393295),(82,393295),(85,393295),(97,262219),(98,393295),(106,393295),(109,393295)]),([5,3840,8738,13107,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(58,393295),(82,393295),(85,393295),(98,393295),(106,393295),(109,393295)]),([5,3840,8738,13107,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(58,393295),(61,262219),(77,393291),(82,393295),(85,393295),(98,393295),(101,393295),(106,393295),(109,393295)]),([5,3840,8738,52428,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(58,393295),(81,393295),(82,393295),(97,262219),(98,393295),(106,393295),(109,393295)]),([5,3840,8738,52428,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(58,393295),(81,393295),(82,393295),(98,393295),(106,393295),(109,393295)])]

noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,8738,52428,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(58,393295),(61,262219),(73,393291),(81,393295),(82,393295),(98,393295),(101,393295),(106,393295),(109,393295)]),([5,3840,8738,61166,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(82,393295),(85,393295),(97,262219),(98,393295),(105,305218),(106,393295)]),([5,3840,8738,61166,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(58,305231),(62,393282),(81,305218),(82,393295),(85,393295),(98,393295),(105,65803),(106,393295),(109,393295)]),([5,3840,8738,61166,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(61,262219),(77,262223),(82,393295),(85,393295),(98,393295),(101,393295),(106,393295)]),([5,3840,8751,13107,61440],[(0,397519),(2,207109),(4,397519),(6,397519),(8,397519),(10,397519),(12,397519),(14,272449),(58,397519),(85,397391),(97,266443),(98,397519),(106,397519),(109,393295)]),([5,3840,8751,52428,61440],[(0,397519),(2,207109),(4,397519),(6,397519),(8,397519),(10,397519),(12,397519),(14,65803),(58,397519),(81,397391),(97,266443),(98,397519),(106,397519),(109,393295)]),([5,3840,8959,17476,34952],[(0,98572),(2,98572),(4,98572),(6,393295),(8,98572),(10,272449),(12,98572),(14,273505),(58,98572),(61,98572),(73,98572),(97,65803),(113,65803),(114,98572)]),([5,3840,12066,13107,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(58,393295),(61,393295),(77,393295),(85,393295),(97,272449),(98,393295),(106,393295),(109,393295)])]

noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,12066,52428,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(58,393295),(61,393295),(73,393295),(81,393295),(97,65803),(98,393295),(106,393295),(109,393295)]),([5,3840,12287,17476,34952],[(0,98572),(2,76033),(4,98572),(6,393295),(8,98572),(10,272449),(12,98572),(14,273505),(58,98572),(61,98572),(113,65803),(114,98572)]),([5,3840,13107,21845,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(74,393295),(86,393295),(97,262219),(98,393295),(117,272449)]),([5,3840,13107,26214,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,273474),(74,393295),(86,393295),(97,262219),(98,393295),(117,393296)]),([5,3840,13107,56797,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,272449),(74,393295),(85,393295),(86,393295),(97,262219),(98,393295),(117,272449),(118,393295)]),([5,3840,13107,61166,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(74,393295),(85,393295),(86,393295),(97,262219),(98,393295),(105,305218),(117,272449)]),([5,3840,17476,21845,61986],[(0,306255),(2,306255),(4,306255),(6,306255),(8,306255),(10,306255),(12,306255),(14,273505),(82,306255),(85,306255)]),([5,3840,17476,34952,53248],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,98572),(81,393295),(82,393295),(97,262219),(98,393295)])]

noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,17476,43144,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,98572),(81,393295),(82,393295),(97,262219),(98,393295)]),([5,3840,17476,43690,61986],[(0,306255),(2,306255),(4,306255),(6,306255),(8,306255),(10,306255),(12,306255),(14,98572),(81,306255),(82,306255)]),([5,3840,17476,61166,61986],[(0,306255),(2,306255),(4,306255),(6,306255),(8,306255),(10,306255),(12,306255),(14,98572),(58,305231),(62,306242),(81,305218),(82,306255),(85,306255),(105,305218),(109,305218)]),([5,3840,21845,26214,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65634),(97,262219),(98,393295)]),([5,3840,21845,39321,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,99393),(97,262219),(98,393295)]),([5,3840,21845,52428,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(58,393295),(81,393295),(97,262219),(98,393295),(109,65803)]),([5,3840,26214,43690,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,98370),(97,262219),(98,393295)]),([5,3840,26214,52428,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,66828),(58,393295),(81,393295),(97,262219),(98,393295),(109,393296)])]

noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([5,3840,52428,56797,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(74,393295),(82,393295),(85,393295),(97,262219),(98,393295),(117,65803),(118,393295)]),([5,3840,52428,61166,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,66859),(74,393295),(82,393295),(85,393295),(97,262219),(98,393295),(105,66859),(117,65803)]),([5,3840,56797,61166,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,65803),(85,393295),(86,393295),(97,262219),(98,393295),(105,66859),(110,65803)]),([5,3840,61166,61440,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,65803),(73,262219),(74,305218),(78,305218),(82,305218),(86,305218),(110,65803),(113,65803),(114,305218),(117,305218)]),([5,3840,61166,61986],[(1,305218),(3,305218),(5,305218),(7,305218),(9,65803),(11,65803),(59,305218),(63,305218),(75,65803),(79,393282),(83,305218),(87,65803)]),([5,3855,4080,4369,8738],[(0,305218),(2,206927),(4,305218),(6,75983),(8,305218),(10,65803),(12,305218),(14,66859),(113,272449),(114,305218)]),([5,3855,4369,8738,61455],[(0,75983),(2,206927),(4,75983),(6,75983),(8,75983),(10,75983),(12,75983),(14,305218),(81,75983),(82,75983)]),([5,3855,4369,8738,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,305218),(57,262219),(77,262219),(81,262219),(82,262219),(101,393295)])]

noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([5,4095,4369,8738,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,305218),(73,76033),(78,76033),(81,76033),(82,76033),(101,305218),(102,305218)]),([5,4095,4369,8738,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,305218),(57,262219),(77,262219),(78,262219),(81,262219),(82,262219),(101,393295),(102,305218)]),([5,4369,7936,8738,61440],[(0,305218),(2,65803),(4,305218),(6,76033),(8,305218),(10,66859),(12,305218),(14,305218),(73,272449),(74,305218),(97,272449),(98,305218),(105,262219),(106,305218),(113,305218),(114,262219)]),([5,4369,7953,8738,65280],[(0,262223),(2,262223),(4,262223),(6,262223),(8,262223),(10,262223),(12,262223),(14,305218),(58,262223),(61,262223),(73,262223),(74,262223),(85,262219),(101,305218),(109,305218),(114,262223)]),([5,4369,8192,8738,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,305218),(57,262219),(58,262219),(73,262219),(74,262219),(82,262219),(85,262219),(106,262219),(109,262219)]),([5,4369,8738,12032,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,262219),(57,393295),(58,393295),(105,305218),(113,262219)]),([5,4369,8738,20224,61440],[(0,393296),(2,393296),(4,393296),(6,393296),(8,393296),(10,393296),(12,393296),(14,262219),(57,393296),(58,393296),(105,305218),(106,393296),(113,262219),(114,393296)]),([5,4369,8738,20292,65280],[(0,393291),(2,393291),(4,393291),(6,393291),(8,393291),(10,393291),(12,393291),(14,305250),(57,393291),(58,393291),(74,262219),(86,262219),(106,393291),(117,393296)])]

noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([5,4369,8738,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,393295),(57,76033),(58,76033),(81,305218),(82,393295),(114,76033),(117,76033)]),([5,4369,8738,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,305218),(57,262219),(58,262219),(74,262219),(81,262219),(86,262219),(114,262219),(117,262219)]),([5,4369,8738,61455,61680],[(0,206927),(2,206927),(4,206927),(6,206927),(8,206927),(10,206927),(12,206927),(14,75983),(57,206927),(58,206927)]),([5,4369,8738,61455,65280],[(0,266319),(2,266319),(4,266319),(6,266319),(8,266319),(10,266319),(12,266319),(14,305218),(57,266319),(58,266319),(74,262223),(86,262219),(117,262219)]),([5,4369,8738,61695,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,76033),(57,393295),(58,393295),(62,305218),(81,393282),(85,305231),(105,76033),(106,393295),(109,393295),(118,76033)]),([5,4369,8738,61695,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(57,393295),(58,393295),(74,262223),(86,262219),(106,393295),(117,262219),(118,76033)]),([5,4369,8738,61713,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,305218),(57,262219),(58,262219),(74,262219),(77,262219),(81,262219),(86,262219),(101,296011),(117,296011)]),([5,4369,8738,62532,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,306274),(57,262219),(58,262219),(74,262219),(81,262219),(86,262219),(117,262220)])]

noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([5,4369,13107,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,393295),(58,76033),(61,76033),(77,76033),(81,305218),(101,76034),(114,76033),(117,76033)]),([5,4369,13107,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,305218),(58,262219),(61,262219),(74,262219),(77,262219),(81,262219),(86,262219),(101,294987),(114,262219),(117,262219)]),([5,4369,17476,61695,61986],[(0,306255),(2,306255),(4,306255),(6,306255),(8,306255),(10,306255),(12,306255),(14,76033),(57,306255),(58,306255),(62,305218),(81,306242),(85,305231),(105,305218),(109,305218)]),([5,4369,17476,63624,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,99628),(57,262219),(58,262219),(74,262219),(77,262219),(81,262219),(82,262219),(101,294987)]),([5,4369,52428,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,393295),(57,76033),(58,76033),(77,76033),(81,66859),(101,76034),(114,76033),(117,76033)]),([5,4369,52428,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,66859),(57,262219),(58,262219),(74,262219),(77,262219),(81,262219),(82,262219),(101,294987),(114,262219),(117,262219)]),([5,4369,56797,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,393295),(58,76033),(61,76033),(81,66859),(86,76033),(114,76033),(117,76033)]),([5,4369,56797,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,66859),(58,262219),(61,262219),(74,262219),(81,262219),(82,262219),(114,262219),(117,262219)])]

noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([5,4369,61440,61695,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,76033),(58,305218),(62,305218),(81,305218),(82,305218),(85,305218),(98,305218),(105,76033),(106,305218),(109,305218)]),([5,4369,61440,61986,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,305218),(58,262219),(74,262219),(82,262219),(85,262219),(106,262219),(109,262219)]),([5,4369,61695,61986],[(1,305218),(3,305218),(5,305218),(7,305218),(9,76033),(11,76033),(59,305218),(63,305218),(75,76033),(79,305218),(83,393282),(87,76033)]),([5,7936,17476,34952,61440],[(0,98572),(2,76033),(4,98572),(6,272449),(8,98572),(10,273505),(12,98572),(14,98572),(81,65803),(82,98572),(98,98572),(105,65803),(113,98572)]),([5,7953,17476,34952,65280],[(0,262223),(2,262223),(4,262223),(6,262223),(8,262223),(10,262223),(12,262223),(14,99596),(57,262219),(73,262223),(81,262223),(82,262223),(101,98572)]),([5,8192,17476,34952,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,98572),(56,0),(57,262219),(58,262219),(73,262219),(74,262219),(81,262219),(82,262219),(98,262219),(101,262219)]),([5,8738,13107,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,393295),(58,76033),(61,76033),(74,393295),(77,76033),(101,76033),(114,76033),(117,76033)]),([5,8738,13107,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,272449),(58,262219),(61,262219),(77,262219),(78,262219),(86,262219),(101,262219),(114,262219),(117,262219)])]

noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([5,8738,52428,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,393295),(57,76033),(58,76033),(74,393295),(77,76033),(101,76033),(114,76033),(117,76033)]),([5,8738,52428,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,65803),(57,262219),(58,262219),(77,262219),(78,262219),(82,262219),(101,262219),(114,262219),(117,262219)]),([5,8738,61166,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,393295),(58,76033),(61,76033),(73,305218),(74,393295),(114,76033),(117,76033)]),([5,8738,61166,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,65803),(58,262219),(61,262219),(73,262219),(78,262219),(86,262219),(114,262219),(117,262219)]),([5,12032,17476,34952,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,98572),(81,393295),(82,393295)]),([6,0,3840,4369,8738,61440],[(0,393295),(2,393295),(4,393295),(6,76033),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305218),(57,393295),(58,393295),(61,393295),(73,393295),(74,393295),(77,393295),(97,393295),(98,393295),(101,393295),(113,393295),(114,393295),(129,305218),(130,393295),(133,393295),(137,262219),(138,393295),(153,305218),(154,393295)]),([6,1,3840,4369,8738,61440],[(0,397391),(2,397391),(4,397391),(6,76037),(8,397391),(10,397391),(12,397391),(14,397391),(16,397391),(18,305218),(57,397391),(58,397391),(61,393295),(73,393295),(74,397391),(77,397391),(97,397391),(98,397391),(101,393295),(113,397391),(114,397391),(129,305218),(130,397391),(133,393295),(137,266315),(138,397391),(153,305218),(154,397391)]),([6,2,3840,4369,8738,61440],[(0,393295),(2,393295),(4,393295),(6,76033),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305222),(57,393295),(58,393295),(61,393295),(73,393295),(74,393295),(77,393295),(97,393295),(98,393295),(101,393295),(113,393295),(114,393295),(129,305222),(130,393295),(133,393295),(137,262219),(138,393295),(153,305222),(154,393295)])]

noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([6,4,3840,4369,8738,61440],[(0,393327),(2,393327),(4,393327),(6,108801),(8,393327),(10,393327),(12,393327),(14,393327),(16,393327),(18,305250),(57,393327),(58,393327),(61,393295),(73,393327),(74,393327),(77,393295),(97,393327),(98,393327),(101,393295),(113,393327),(114,393327),(129,305250),(130,393327),(133,393295),(137,262251),(138,393327),(153,305250),(154,393327)]),([6,15,240,512,4369,8738],[(0,272449),(2,262219),(4,272449),(6,266443),(8,272449),(10,272449),(12,272449),(14,65803),(16,272449),(18,272449),(57,272449),(58,272449),(73,272449),(74,272449),(81,272449),(82,272449),(113,207109),(114,272449),(129,76033),(137,207109),(146,272449),(149,272449),(153,272449),(154,207109)]),([6,15,240,3840,4369,8738],[(0,305218),(2,393295),(4,305218),(6,397519),(8,305218),(10,305218),(12,305218),(14,65803),(16,305218),(18,66859),(57,305218),(58,305218),(73,305218),(74,305218),(81,305218),(82,305218),(113,305218),(129,80257),(137,211333),(149,272449),(153,272449),(154,305218)]),([6,15,240,3840,4369,8738,17476,63624],[(96,1)]),([6,15,240,3840,4369,8738,52428,61440],[(96,1),(128,1)]),([6,15,240,3840,4369,13107],[(0,305218),(2,393295),(4,305218),(6,397519),(8,305218),(10,305218),(12,305218),(14,305218),(16,305218),(18,66859),(57,305218),(58,305218),(73,305218),(74,305218),(81,305218),(82,305218),(98,305217),(106,305218),(113,305218),(114,272450),(149,207237),(154,305218),(157,305218)]),([6,15,240,3840,4369,17476,34952,61986],[]),([6,15,240,3840,4369,52428],[(0,66859),(2,393295),(4,66859),(6,397519),(8,66859),(10,66859),(12,66859),(14,66859),(16,66859),(18,305218),(57,66859),(58,66859),(73,66859),(74,66859),(81,66859),(82,66859),(98,65835),(106,66859),(113,66859),(114,66827),(145,207237),(153,65803),(154,66859)])]

noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,3840,4369,56797],[(0,66859),(2,393295),(4,66859),(6,397519),(8,66859),(10,66859),(12,66859),(14,65803),(16,66859),(18,305218),(57,66859),(58,66859),(73,66859),(74,66859),(81,66859),(82,66859),(113,66859),(133,202027),(141,66859),(145,272449),(154,66859),(157,66859)]),([6,15,240,3840,4369,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,305218),(16,305218),(18,272449),(57,305218),(58,305218),(61,305218),(62,305218),(73,305218),(74,305218),(77,305218),(81,305218),(82,305218),(85,305218),(97,305218),(101,305218),(105,305218),(109,305218),(113,305218),(129,393282),(133,305230),(137,397510),(141,305218),(149,272449),(154,305218)]),([6,15,240,3840,8738,13107],[(0,272449),(2,393295),(4,272449),(6,397519),(8,272449),(10,272449),(12,272449),(14,272449),(16,272449),(18,65803),(57,272449),(58,272449),(73,272449),(74,272449),(81,272449),(82,272449),(96,1),(97,272449),(98,272449),(105,272449),(106,272449),(114,272449),(117,272449),(149,403521),(154,272449),(157,272449)]),([6,15,240,3840,8738,52428],[(0,65803),(2,393295),(4,65803),(6,397519),(8,65803),(10,65803),(12,65803),(14,65803),(16,65803),(18,272449),(57,65803),(58,65803),(73,65803),(74,65803),(81,65803),(82,65803),(96,1),(97,65803),(98,65803),(105,65803),(106,65803),(114,65803),(117,65803),(145,207237),(153,66859),(154,65803)]),([6,15,240,3840,8738,61166],[(0,65803),(2,393295),(4,65803),(6,397519),(8,65803),(10,65803),(12,65803),(14,65803),(16,65803),(18,305218),(57,65803),(58,65803),(73,65803),(74,65803),(81,65803),(82,65803),(97,65803),(105,65803),(117,65803),(149,65807),(154,65803),(157,65803)]),([6,15,240,3855,4369,8738],[(0,305218),(2,262219),(4,305218),(6,397519),(8,305218),(10,305218),(12,305218),(14,65803),(16,305218),(18,66859),(57,305218),(58,305218),(74,305218),(77,305218),(81,305218),(82,305218),(113,305218),(137,211333),(149,272449),(153,272449),(154,305218)]),([6,15,240,4095,4369,8738],[(0,305218),(2,262219),(4,305218),(6,266443),(8,305218),(10,305218),(12,305218),(14,65803),(16,305218),(18,66859),(57,305218),(58,305218),(74,305218),(77,305218),(82,305218),(85,305218),(113,305218),(149,272449),(150,272449),(153,272449),(154,305218)]),([6,15,240,4369,7953,8738],[(0,305218),(2,262223),(4,305218),(6,266447),(8,305218),(10,305218),(12,305218),(14,305218),(16,305218),(18,66859),(57,305218),(58,305218),(74,305218),(82,305218),(98,305218),(106,305218),(114,305218),(117,305218),(129,80129),(137,211205),(145,211205),(146,305218),(157,272449)])]

noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,8192,8738],[(0,305218),(2,262219),(4,305218),(6,266443),(8,305218),(10,65803),(12,305218),(14,305218),(16,305218),(18,66859),(57,305218),(58,305218),(96,1),(97,305218),(98,305218),(105,305218),(106,305218),(113,272449),(114,305218),(145,272449),(146,305218),(154,305218),(157,305218)]),([6,15,240,4369,8738,17476,36744,61440],[(72,1),(96,1),(248,0)]),([6,15,240,4369,8738,20292],[(0,305250),(2,393291),(4,305250),(6,397515),(8,305250),(10,98571),(12,305250),(14,99627),(16,305250),(18,305250),(57,305250),(58,305250),(97,76161),(105,207237),(113,272481),(114,305250),(130,305218),(138,305250),(146,305250),(158,272449)]),([6,15,240,4369,8738,61440],[(0,305218),(2,262219),(4,305218),(6,266443),(8,305218),(10,65803),(12,305218),(14,66859),(16,305218),(18,305218),(57,305218),(58,305218),(113,272449),(114,305218),(129,76033),(130,305218),(137,207109),(138,305218),(146,305218),(153,305218),(158,305218)]),([6,15,240,4369,8738,61455],[(0,305218),(2,393295),(4,305218),(6,266443),(8,305218),(10,65803),(12,305218),(14,66859),(16,305218),(18,305218),(57,305218),(58,305218),(97,80257),(113,272449),(114,305218),(130,305218),(133,305218),(137,207109),(138,305218),(146,305218),(158,305350)]),([6,15,240,4369,8738,61695],[(0,305218),(2,393295),(4,305218),(6,397519),(8,305218),(10,65803),(12,305218),(14,66859),(16,305218),(18,305218),(57,305218),(58,305218),(97,80257),(105,211333),(113,272449),(114,305218),(130,305218),(133,305218),(138,305218),(141,305218),(146,305218),(158,272449)]),([6,15,240,4369,8738,61713],[(0,305218),(2,262219),(4,305218),(6,266443),(8,305218),(10,305218),(12,305218),(14,66859),(16,305218),(18,305218),(57,305218),(58,305218),(74,305218),(82,305218),(113,207109),(114,305218),(130,305218),(138,305218),(146,305218),(149,305218),(153,305218),(158,305218)]),([6,15,240,4369,8738,62532],[(0,306274),(2,262219),(4,306274),(6,266443),(8,306274),(10,98572),(12,306274),(14,99628),(16,306274),(18,306274),(57,306274),(58,306274),(113,273505),(114,306274),(130,306242),(138,306274),(146,306274),(153,306274),(158,305218)])]

noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,4369,13107,61440],[(0,305218),(2,262219),(4,305218),(6,266443),(8,305218),(10,305218),(12,305218),(14,66859),(16,305218),(18,305218),(57,305218),(58,305218),(74,305217),(82,305218),(114,305218),(117,305218),(129,76033),(130,305218),(137,207109),(138,305218),(146,305218),(149,272449),(153,305218),(158,305218)]),([6,15,240,4369,17476,63624],[(0,99628),(2,262219),(4,99628),(6,266443),(8,99628),(10,99628),(12,99628),(14,99628),(16,99628),(18,66859),(57,99628),(58,99628),(74,98604),(82,99628),(113,99628),(114,99628),(146,99628),(149,98572),(153,66859),(154,99628)]),([6,15,240,4369,52428,61440],[(0,66859),(2,262219),(4,66859),(6,266443),(8,66859),(10,66859),(12,66859),(14,305218),(16,66859),(18,66859),(57,66859),(58,66859),(74,65835),(82,66859),(113,65803),(114,66859),(129,76033),(130,66859),(137,207109),(138,66859),(146,66859),(149,65803),(153,66859),(154,207109)]),([6,15,240,4369,56797,61440],[(0,66859),(2,262219),(4,66859),(6,266443),(8,66859),(10,65803),(12,66859),(14,305218),(16,66859),(18,66859),(57,66859),(58,66859),(114,66859),(117,66859),(129,76033),(130,66859),(137,207109),(138,66859),(146,66859),(153,66859),(154,272449)]),([6,15,240,4369,61440,61986],[(0,305218),(2,262219),(4,305218),(6,266443),(8,305218),(10,305218),(12,305218),(14,305218),(16,305218),(18,272449),(57,305218),(58,305218),(96,1),(97,305218),(98,305218),(105,305218),(106,305218),(114,305218),(146,305218),(154,305218),(157,305218)]),([6,15,240,7953,17476,34952],[(0,99596),(2,262223),(4,99596),(6,266447),(8,99596),(10,99596),(12,99596),(14,272450),(16,99596),(18,273506),(57,99596),(58,99596),(74,98572),(82,99596),(113,99596),(145,98572),(153,66827),(154,99596)]),([6,15,240,8192,17476,34952],[(0,98572),(2,262219),(4,98572),(6,266443),(8,98572),(10,98572),(12,98572),(14,272449),(16,98572),(18,273505),(57,98572),(58,98572),(72,1),(73,98572),(74,98572),(81,98572),(82,98572),(112,0),(113,98572),(114,98572),(145,65803),(146,98572),(153,65803),(154,98572)]),([6,15,240,8738,13107,61440],[(0,272449),(2,262219),(4,272449),(6,266443),(8,272449),(10,272449),(12,272449),(14,65803),(16,272449),(18,272449),(57,272449),(58,272449),(74,272449),(82,272449),(114,272449),(117,272449),(129,76033),(130,272449),(137,207109),(138,272449),(149,272449),(150,272449),(158,272449)])]

noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,240,8738,52428,61440],[(0,65803),(2,262219),(4,65803),(6,266443),(8,65803),(10,65803),(12,65803),(14,272449),(16,65803),(18,65803),(57,65803),(58,65803),(74,65803),(82,65803),(113,66859),(114,65803),(129,76033),(130,65803),(137,207109),(138,65803),(149,65803),(150,65803),(154,207109)]),([6,15,240,8738,61166,61440],[(0,65803),(2,262219),(4,65803),(6,266443),(8,65803),(10,65803),(12,65803),(14,305218),(16,65803),(18,65803),(57,65803),(58,65803),(114,65803),(117,65803),(129,76033),(130,65803),(137,207109),(138,65803),(145,305218),(150,65803),(158,65803)]),([6,15,255,3840,4369,8738],[(0,305218),(2,305218),(4,305218),(6,397519),(8,305218),(10,305218),(12,305218),(14,65803),(16,305218),(18,66859),(57,305218),(58,305218),(61,305218),(73,305218),(74,305218),(77,305218),(81,305218),(82,305218),(97,305218),(101,305218),(113,305218),(129,272449),(133,305222),(137,211333),(149,272449),(153,272449),(154,305218)]),([6,15,255,4369,8738,61440],[(0,305218),(2,305218),(4,305218),(6,266443),(8,305218),(10,65803),(12,305218),(14,66859),(16,305218),(18,305218),(57,305218),(58,305218),(61,305218),(73,305218),(77,305218),(97,272449),(101,305222),(113,272449),(114,305218),(129,305218),(130,305218),(133,305218),(137,207109),(138,305218),(146,305218),(153,305218),(158,305218)]),([6,15,3840,4080,4369,8738],[(0,305218),(2,393295),(4,305218),(6,207109),(8,305218),(10,397519),(12,305218),(14,65803),(16,305218),(18,66859),(57,305218),(58,305218),(73,305218),(74,305218),(82,305218),(85,305218),(129,80257),(145,211333),(153,272449),(154,305218)]),([6,15,3840,4095,4369,8738],[(0,305218),(2,305218),(4,305218),(6,207109),(8,305218),(10,397519),(12,305218),(14,65803),(16,305218),(18,66859),(57,305218),(58,305218),(61,305218),(73,305218),(74,305218),(77,305218),(82,305218),(85,305218),(97,305218),(101,305218),(129,272449),(133,305222),(145,211333),(150,272449),(153,272449),(154,305218)]),([6,15,3840,4369,8738,8946],[(0,211333),(2,393295),(4,211333),(6,211333),(8,211333),(10,65803),(12,211333),(14,211333),(16,211333),(18,397519),(57,211333),(58,211333),(81,211205),(97,211333),(98,211010),(106,211333),(109,207109),(113,272449),(114,211333),(129,80257),(130,211333),(138,211333),(141,207109),(154,211333),(157,211333)]),([6,15,3840,4369,8738,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,305218),(57,397519),(58,397519),(61,393295),(73,393423),(77,397391),(97,397519),(101,393295),(113,397519),(114,397519),(129,393295),(130,397519),(133,393295),(137,266443),(138,397519),(153,305218),(154,397519)])]

noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,8738,61455],[(0,397519),(2,393295),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,305218),(57,397519),(58,397519),(97,397519),(113,397519),(114,397519),(130,397519),(133,397519),(137,266443),(138,397519),(154,397519)]),([6,15,3840,4369,8738,61986],[(0,397519),(2,397519),(4,397519),(6,397519),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,272449),(57,397519),(58,397519),(61,393295),(73,393423),(77,397391),(97,397519),(98,397378),(101,393295),(102,305350),(106,305359),(110,397378),(113,397519),(114,397519),(118,305218),(129,393295),(130,397519),(133,393295),(138,397519),(153,272449),(154,397519),(157,397519)]),([6,15,3840,4369,8738,65280],[(0,397519),(2,397519),(4,397519),(6,397519),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,305218),(57,397519),(58,397519),(61,393295),(73,393423),(77,397391),(81,266447),(97,397519),(101,393295),(109,266443),(113,397519),(114,397519),(129,393295),(130,397519),(133,393295),(138,397519),(141,397519),(154,397519)]),([6,15,3840,4369,8738,65295],[(0,397519),(2,393295),(4,397519),(6,397519),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,305218),(57,397519),(58,397519),(81,266447),(97,397519),(109,266443),(113,397519),(114,397519),(130,397519),(133,397519),(138,397519),(141,397519),(154,397519)]),([6,15,3840,4369,8946,17476,34952,61440],[(136,0)]),([6,15,3840,4369,13107,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,305218),(57,397519),(58,397519),(61,393295),(73,393423),(74,397519),(77,397391),(82,397519),(97,393423),(101,397391),(114,397519),(117,397519),(129,393295),(130,397519),(133,393295),(137,266443),(138,397519),(149,272449),(153,305218)]),([6,15,3840,4369,17476,61986],[(0,306274),(2,306274),(4,306274),(6,306274),(8,306274),(10,306274),(12,306274),(14,306274),(16,306274),(18,273505),(57,306274),(58,306274),(61,306255),(73,306274),(77,306255),(97,306255),(98,306242),(101,306274),(102,305250),(106,305250),(110,306242),(113,306274),(114,306274),(118,305218),(129,393295),(133,306255),(153,305218),(157,305218)]),([6,15,3840,4369,52428,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,66859),(57,397519),(58,397519),(61,393295),(73,393423),(74,397519),(77,397391),(82,397519),(97,397391),(101,393423),(113,397519),(114,397519),(129,393295),(130,397519),(133,393295),(137,266443),(138,397519),(149,65803),(153,66859)])]

noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3840,4369,56797,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,66859),(57,397519),(58,397519),(61,393295),(73,393423),(77,397391),(97,393295),(101,397519),(114,397519),(117,397519),(129,393295),(130,397519),(133,393295),(137,266443),(138,397519),(153,66859),(158,66859)]),([6,15,3840,4369,61440,61986],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,305218),(16,305218),(18,272449),(57,305218),(58,305218),(61,305218),(73,305218),(77,305218),(97,305218),(98,305218),(101,305218),(102,305218),(105,266443),(106,305218),(110,305218),(114,305218),(118,305218),(129,272449),(133,305222),(146,305218),(153,272449),(154,305218),(157,305218)]),([6,15,3840,4369,61986],[(1,305218),(2,1),(3,305218),(5,305218),(7,305218),(9,305218),(11,305218),(13,272449),(15,272449),(59,305218),(63,305218),(75,305218),(79,305218),(83,305218),(87,305218),(99,272449),(103,305350),(107,272449),(111,397378),(115,266443),(119,305218)]),([6,15,3840,4593,8738,17476,34952,61440],[(96,1),(136,0),(248,0)]),([6,15,3840,8738,13107,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,272449),(57,397519),(58,397519),(61,393295),(73,397519),(74,397519),(77,393295),(82,397519),(97,393423),(101,397391),(114,397519),(117,397519),(129,393295),(130,397519),(133,393295),(137,266443),(138,397519),(146,397519),(149,397519)]),([6,15,3840,8738,52428,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,65803),(57,397519),(58,397519),(61,393295),(73,397519),(74,397519),(77,393295),(82,397519),(97,397391),(101,393423),(113,397519),(114,397519),(129,393295),(130,397519),(133,393295),(137,266443),(138,397519),(146,397519),(149,397519)]),([6,15,3840,8738,61166,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,65803),(57,397519),(58,397519),(61,393295),(73,397519),(77,393295),(97,397391),(101,393423),(114,397519),(117,397519),(129,393295),(130,397519),(133,393295),(137,266443),(138,397519),(145,305218),(146,397519)]),([6,15,3840,8946,17476,34952],[(0,98572),(2,393295),(4,98572),(6,98572),(8,98572),(10,397519),(12,98572),(14,272449),(16,98572),(18,273505),(57,98572),(58,98572),(73,98572),(74,98572),(82,98572),(85,98572),(105,98572),(137,65803),(153,65803),(154,98572)])]

noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([6,15,3855,4369,8738,61440],[(0,397519),(2,262219),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,305218),(58,397519),(61,397519),(113,397519),(114,397519),(129,76033),(130,397519),(137,266443),(138,397519),(153,305218),(154,397519)]),([6,15,4369,8738,61440,61680],[(0,207109),(2,262219),(4,207109),(6,207109),(8,207109),(10,207109),(12,207109),(14,207109),(16,207109),(18,397519),(81,207109),(82,207109),(97,207109),(98,207109),(113,305218),(114,397519),(129,76033),(130,207109),(154,207109),(157,207109)]),([6,15,4369,8738,61440,61695],[(0,207109),(2,207109),(4,207109),(6,207109),(8,207109),(10,207109),(12,207109),(14,207109),(16,207109),(18,397519),(57,207105),(61,76037),(73,207109),(77,76033),(81,207109),(82,207109),(97,207109),(98,207109),(101,76033),(113,305218),(114,397519),(129,393295),(130,207109),(133,207109),(154,207109),(157,207109)]),([6,15,4369,8738,61440,65280],[(0,266443),(2,266443),(4,266443),(6,266443),(8,266443),(10,266443),(12,266443),(14,266443),(16,266443),(18,305218),(57,262347),(61,266315),(73,266443),(77,262219),(81,266443),(82,266443),(97,266443),(98,266443),(101,262219),(106,266443),(113,266443),(118,266443),(129,262219),(130,266443),(133,262219),(154,266443),(157,266443)]),([6,15,4369,8738,61440,65295],[(0,266443),(2,262219),(4,266443),(6,266443),(8,266443),(10,266443),(12,266443),(14,266443),(16,266443),(18,305218),(81,266443),(82,266443),(97,266443),(98,266443),(106,266443),(113,266443),(118,266443),(130,266443),(133,266443),(154,266443),(157,266443)]),([6,255,3840,4369,8738],[(1,305218),(3,305218),(5,305218),(7,305218),(9,305218),(11,305218),(13,272449),(15,272449),(59,305218),(63,305218),(75,305218),(79,305218),(83,305218),(87,305218),(99,272449),(103,272449),(107,272449),(111,272449),(115,80257),(119,305218)]),([6,255,3840,4369,8738,17476],[(0,306274),(2,393295),(4,306274),(6,306274),(8,306274),(10,98572),(12,306274),(14,99628),(16,306274),(18,306274),(57,306274),(58,306274),(81,306274),(97,80257),(109,273505),(113,273505),(114,306274),(130,306242),(134,305250),(137,306274),(138,305250),(142,306242),(145,273505),(146,306274),(150,305218),(153,306274),(154,305218),(158,305218)]),([6,255,3840,4369,8738,17476,34952,61440],[(136,0),(248,0)])]

noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([6,255,3840,4369,8738,61440],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,65803),(12,305218),(14,66859),(16,305218),(18,305218),(57,305218),(58,305218),(61,393295),(62,305218),(73,305218),(77,305218),(81,305218),(85,305218),(97,272449),(101,393295),(105,272449),(109,272449),(113,272449),(114,305218),(129,393295),(130,305218),(133,393295),(134,305218),(137,305218),(138,305218),(141,305218),(142,305218),(146,305218),(150,305218),(153,305218),(154,272449),(158,305218)]),([6,255,3840,4369,17476,34952],[(0,99628),(2,393295),(4,99628),(6,99628),(8,99628),(10,99628),(12,99628),(14,305218),(16,99628),(18,306274),(57,99628),(58,99628),(74,98604),(81,99628),(82,99596),(105,99628),(113,99628),(114,99628),(137,66859),(145,98572),(146,99628),(153,66859),(154,99628)]),([6,255,3840,8738,17476,34952],[(0,98572),(2,393295),(4,98572),(6,98572),(8,98572),(10,98572),(12,98572),(14,272449),(16,98572),(18,273505),(57,98572),(58,98572),(73,98572),(74,98572),(82,98572),(85,98572),(105,98572),(113,98572),(114,98572),(137,65803),(145,99628),(146,98572),(153,65803),(154,98572)]),([6,255,4369,8738,17476,61440],[(0,306274),(2,262219),(4,306274),(6,98572),(8,306274),(10,99628),(12,306274),(14,306274),(16,306274),(18,306274),(81,273505),(82,306274),(98,306242),(102,305250),(105,273505),(106,306274),(110,305218),(113,306274),(114,305218),(118,305218),(129,76033),(130,306274),(138,306274),(145,306274),(150,306274),(153,306274),(154,306274),(157,305218)]),([6,255,4369,8738,61440],[(1,305218),(3,305218),(5,305218),(7,305218),(9,272449),(11,272449),(13,305218),(15,305218),(59,305218),(63,305218),(75,272449),(79,272449),(83,76033),(87,305218),(99,305218),(103,305218),(107,305218),(111,305218),(115,272449),(119,305218)]),([6,255,4369,17476,34952,61440],[(0,99628),(2,262219),(4,99628),(6,99628),(8,99628),(10,305218),(12,99628),(14,306274),(16,99628),(18,99628),(58,98604),(81,99628),(82,99628),(105,98572),(106,99628),(113,66859),(114,99628),(129,76033),(130,99628),(138,99628),(141,98572),(144,0),(145,66859),(146,99628),(153,99628),(154,66859)]),([6,255,8738,17476,34952,61440],[(0,98572),(2,262219),(4,98572),(6,98572),(8,98572),(10,272449),(12,98572),(14,273505),(16,98572),(18,98572),(58,98572),(81,98572),(82,98572),(105,99628),(106,98572),(113,65803),(114,98572),(129,76033),(130,98572),(141,98572),(142,98572),(146,98572),(154,65803)]),([6,256,3840,4369,8738,61440],[(0,393295),(2,393295),(4,393295),(6,76066),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305218),(57,393295),(58,393295),(61,393295),(73,393295),(74,393295),(77,393295),(81,393295),(82,393295),(97,393295),(98,393295),(101,393295),(113,393295),(114,393295),(129,305218),(130,393295),(133,393295),(137,296011),(138,393295),(153,305218),(154,393295)])]

noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([6,512,3840,4369,8738,61440],[(0,393295),(2,393295),(4,393295),(6,76033),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,272449),(57,393295),(58,393295),(61,393295),(73,393295),(74,393295),(77,393295),(97,393295),(98,393295),(101,393295),(105,393295),(106,393295),(113,393295),(114,393295),(129,272449),(130,393295),(133,393295),(137,262219),(138,393295),(153,272449),(154,393295)]),([6,1024,3840,4369,8738,61440],[(0,393295),(2,393295),(4,393295),(6,77057),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,306242),(57,393295),(58,393295),(61,393295),(73,393295),(74,393295),(77,393295),(97,393295),(98,393295),(101,393295),(113,393295),(114,393295),(129,306242),(130,393295),(133,393295),(137,262220),(138,393295),(153,306242),(154,393295)]),([6,3840,3840,4369,8738,61440],[(0,393295),(2,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305218),(49,393295),(50,393295),(53,393295),(54,393295),(73,393295),(77,393295),(97,393295),(101,393295),(113,393295),(114,393295),(129,305218),(130,393295),(133,393295),(153,305218),(154,393295)]),([6,3840,3855,4369,8738,61440],[(0,397519),(2,76033),(4,397519),(6,397519),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,305218),(58,397519),(61,397519),(62,393295),(81,393423),(85,397391),(105,397519),(109,393295),(113,397519),(114,397519),(129,262219),(130,397519),(137,393295),(138,397519),(141,393295),(153,305218),(154,397519)]),([6,3840,4095,4369,8738],[(1,305218),(3,305218),(5,305218),(7,305218),(9,305218),(11,305218),(13,272449),(15,272449),(59,305218),(63,305218),(75,305218),(79,305218),(83,305218),(87,305218),(99,272449),(103,272449),(107,305218),(111,272449),(115,80257),(119,305218)]),([6,3840,4095,4369,8738,17476],[(0,306274),(2,76033),(4,306274),(6,393295),(8,306274),(10,98572),(12,306274),(14,99628),(16,306274),(18,306274),(58,306274),(61,306274),(105,80257),(110,273505),(113,273505),(114,306274),(130,305250),(134,306242),(138,305218),(142,306274),(145,273505),(146,306274),(150,305218),(153,306274),(154,305218),(158,305218)]),([6,3840,4095,4369,8738,61440],[(0,305218),(2,76033),(4,305218),(6,305218),(8,305218),(10,65803),(12,305218),(14,66859),(16,305218),(18,305218),(58,305218),(61,305218),(62,393295),(81,305218),(85,305218),(105,305218),(109,393295),(110,272449),(113,272449),(114,305218),(129,262219),(130,305218),(134,305218),(137,393295),(138,305218),(141,393295),(142,305218),(146,305218),(150,305218),(153,305218),(154,272449),(158,305218)]),([6,3840,4095,4369,17476,34952],[(0,99628),(2,76033),(4,99628),(6,393295),(8,99628),(10,99628),(12,99628),(14,305218),(16,99628),(18,306274),(58,99628),(61,99628),(74,99596),(82,98572),(110,99628),(113,99628),(114,99628),(142,66859),(145,98572),(146,99628),(153,66859),(154,99628)])]

noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4095,8738,17476,34952],[(0,98572),(2,76033),(4,98572),(6,393295),(8,98572),(10,98572),(12,98572),(14,272449),(16,98572),(18,273505),(58,98572),(61,98572),(74,98572),(81,98572),(82,98572),(113,98572),(114,98572),(145,99628),(146,98572),(153,65803),(154,98572)]),([6,3840,4096,4369,8738,61440],[(0,305218),(2,76033),(4,305218),(6,305218),(8,305218),(10,65803),(12,305218),(14,66859),(16,305218),(18,305218),(57,305218),(58,305218),(62,393295),(81,393295),(82,305218),(85,305218),(105,272449),(106,305218),(109,393295),(113,272449),(114,305218),(129,262219),(130,305218),(137,305218),(138,305218),(141,305218),(145,272449),(146,305218),(153,305218),(154,272449)]),([6,3840,4096,17476,34952,61440],[(0,98572),(2,76033),(4,98572),(6,98572),(8,98572),(10,272449),(12,98572),(14,273505),(16,98572),(18,98572),(57,98572),(58,98572),(81,98572),(82,98572),(105,65803),(106,98572),(113,65803),(114,98572),(129,262219),(130,98572),(138,98572),(141,98572),(145,65803),(153,98572)]),([6,3840,4369,4369,8738,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(12,393295),(14,393295),(16,393295),(18,305218),(58,393295),(62,393295),(65,393295),(66,393295),(69,393295),(70,393295),(105,393295),(106,393295),(109,393295),(129,262219),(130,393295),(137,305218),(141,305218),(153,305218),(154,393295)]),([6,3840,4369,4383,8738,61440],[(0,393423),(2,207105),(4,393423),(6,393423),(8,393423),(10,393423),(12,393423),(14,393423),(16,393423),(18,305218),(58,393423),(74,393423),(78,393295),(82,393423),(85,393423),(86,393295),(105,393423),(106,393423),(113,393423),(117,393295),(129,262347),(130,393423),(137,305218),(145,393295),(149,305218),(153,305218),(154,393423)]),([6,3840,4369,7953,8738,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305218),(61,393295),(62,393295),(74,393295),(77,393295),(78,393295),(82,393295),(85,393295),(86,393295),(97,393295),(105,393295),(106,393295),(113,393295),(117,393295),(129,305218),(130,393295),(137,305218),(145,305218),(149,305218),(153,305218),(154,393295)]),([6,3840,4369,8192,8738,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305218),(73,393295),(74,393295),(78,393295),(81,393295),(82,393295),(86,393295),(105,393295),(106,393295),(113,393295),(114,393295),(117,393295),(129,262219),(130,393295),(145,305218),(146,393295),(149,393295),(153,305218),(154,393295)]),([6,3840,4369,8738,8738,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(16,393295),(18,272449),(74,393295),(78,393295),(81,393295),(82,393295),(86,393295),(89,393295),(90,393295),(93,393295),(94,393295),(129,262219),(130,393295),(145,272449),(146,393295),(149,393295)])]

noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,8738,8751,61440],[(0,397519),(2,207109),(4,397519),(6,397519),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,272449),(74,397519),(81,397519),(82,397519),(98,397519),(102,393295),(106,393423),(110,397391),(114,397519),(117,397519),(118,393295),(129,266443),(130,397519),(145,272449),(146,397519),(153,393295),(154,397519),(157,393295)]),([6,3840,4369,8738,12066,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,272449),(57,393295),(77,393295),(78,393295),(81,393295),(82,393295),(98,393295),(101,393295),(102,393295),(106,393295),(110,393295),(114,393295),(117,393295),(118,393295),(129,272449),(130,393295),(145,272449),(146,393295),(153,272449),(154,393295),(157,393295)]),([6,3840,4369,8738,13107,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,80257),(58,393295),(62,393295),(74,393295),(78,393295),(81,393295),(82,393295),(85,393295),(86,393295),(98,393295),(102,393295),(105,393295),(106,393295),(109,393295),(110,393295),(113,393295),(114,393295),(117,393295),(118,393295),(129,262219),(130,393295),(137,262219),(141,272449),(145,262219),(146,393295),(149,393295),(153,262219),(157,305218)]),([6,3840,4369,8738,16384,61440],[(0,393296),(2,76033),(4,393296),(6,393296),(8,393296),(10,393296),(12,393296),(14,393296),(16,393296),(18,305218),(81,393296),(82,393296),(97,393296),(98,393296),(102,393295),(105,393296),(106,393296),(110,393295),(113,393296),(114,393296),(118,393295),(129,262219),(130,393296),(145,305218),(146,393296),(153,305218),(154,393296),(157,393296)]),([6,3840,4369,8738,17476,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,306274),(81,393295),(82,393295),(98,393295),(102,393295),(105,393295),(106,393295),(110,393295),(113,393295),(114,393295),(118,393295),(129,262219),(130,393295),(145,306274),(146,393295),(153,306274),(157,393296)]),([6,3840,4369,8738,17476,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,273505),(74,306255),(78,393295),(81,393295),(82,393295),(86,306255),(98,393295),(102,393295),(105,393295),(106,393295),(110,393295),(113,393295),(114,393295),(117,306255),(118,393295),(130,393295),(145,273505),(146,393295),(149,393295),(153,273505),(157,393296)]),([6,3840,4369,8738,17476,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,306274),(57,262223),(77,262219),(81,393295),(82,393295),(97,393291),(98,393295),(102,393295),(105,393295),(106,393295),(110,393295),(113,393295),(114,393295),(118,393295),(130,393295),(133,393295),(146,393295),(153,305250),(157,393296)]),([6,3840,4369,8738,17487,61440],[(0,397391),(2,76037),(4,397391),(6,397391),(8,397391),(10,397391),(12,397391),(14,397391),(16,397391),(18,306242),(81,397391),(82,397391),(98,397391),(102,393295),(106,393295),(110,397391),(114,397391),(118,393295),(129,266315),(130,397391),(145,306242),(146,397391),(153,393295),(157,393296)])]

noncomputable def K_54 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,8738,20292,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305250),(57,393295),(73,393295),(81,393295),(82,393295),(98,393295),(101,393295),(102,393295),(106,393295),(110,393295),(114,393295),(118,393295),(129,305250),(130,393295),(145,305250),(146,393295),(153,305250),(157,393296)]),([6,3840,4369,8738,21845,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,306274),(81,393295),(82,393295),(98,393295),(102,393295),(106,393295),(109,393295),(110,393295),(113,393295),(114,393295),(118,393295),(129,262219),(130,393295),(145,306274),(146,393295),(153,393295),(157,305218)]),([6,3840,4369,8738,26214,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305218),(81,393295),(82,393295),(98,393295),(102,393295),(105,393295),(106,393295),(110,393295),(114,393295),(117,393295),(118,393295),(129,262219),(130,393295),(145,305218),(146,393295),(153,305218),(157,393296)]),([6,3840,4369,8738,30583,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305218),(81,393295),(82,393295),(98,393295),(102,393295),(106,393295),(109,393295),(110,393295),(114,393295),(117,393295),(118,393295),(129,262219),(130,393295),(145,305218),(146,393295),(153,393295),(157,305218)]),([6,3840,4369,8738,52428,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,80257),(58,393295),(62,393295),(74,393295),(78,393295),(81,393295),(82,393295),(85,393295),(86,393295),(98,393295),(102,393295),(105,393295),(106,393295),(109,393295),(110,393295),(113,393295),(114,393295),(117,393295),(118,393295),(129,262219),(130,393295),(137,262219),(141,65803),(145,262219),(146,393295),(149,393295),(153,262219),(157,305218)]),([6,3840,4369,8738,56797,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,272449),(74,393295),(78,393295),(81,393295),(82,393295),(86,393295),(98,393295),(102,393295),(106,393295),(109,393295),(110,393295),(113,393295),(114,393295),(117,393295),(118,393295),(129,262219),(130,393295),(145,272449),(146,393295),(149,393295),(153,393295),(157,305218),(158,393295)]),([6,3840,4369,8738,61166,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,305218),(58,393295),(62,393295),(81,393295),(82,393295),(85,393295),(98,393295),(102,393295),(105,393295),(106,393295),(109,393295),(110,393295),(114,393295),(117,393295),(118,393295),(129,262219),(130,393295),(137,305218),(141,65803),(145,305218),(146,393295),(153,305218),(157,305218)]),([6,3840,4369,8738,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,305218),(15,305218),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,305218),(103,393295),(107,305218),(111,305218),(115,272449),(119,393295)])]

noncomputable def K_55 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,8738,61440,61440],[(0,305218),(2,76033),(4,305218),(6,65803),(8,305218),(10,66859),(12,305218),(14,305218),(81,272449),(82,305218),(97,262219),(98,305218),(102,393295),(106,305218),(110,305218),(113,305218),(114,272449),(118,393295),(121,305218),(122,305218),(125,305218),(126,305218)]),([6,3840,4369,8738,61440,61455],[(0,393295),(2,207109),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(16,393295),(18,393295),(81,393295),(82,393295),(97,266443),(98,393295),(113,305218),(114,393295),(129,266443),(130,393295),(134,393295),(138,393295),(142,393295),(146,393295),(150,393295),(154,393295),(157,393295),(158,305218)]),([6,3840,4369,8738,61440,61695],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(16,393295),(18,393295),(57,393295),(61,76066),(73,393295),(77,76033),(81,393295),(82,393295),(97,305218),(98,393295),(101,76033),(113,305218),(114,393295),(129,76033),(130,393295),(133,76033),(134,393295),(138,393295),(142,393295),(146,393295),(150,393295),(154,393295),(157,393295),(158,305218)]),([6,3840,4369,8738,61440,61713],[(0,305218),(2,76033),(4,305218),(6,305218),(8,305218),(10,66859),(12,305218),(14,305218),(16,305218),(18,305218),(58,305218),(81,262219),(82,305218),(97,262219),(98,305218),(109,272449),(110,305218),(113,305218),(114,262219),(130,305218),(134,393295),(138,305218),(141,305218),(142,393295),(145,305218),(146,262219),(150,393295),(154,305218),(157,305218),(158,305218)]),([6,3840,4369,8738,61440,61986],[(0,272449),(2,76033),(4,272449),(6,65803),(8,272449),(10,272449),(12,272449),(14,272449),(16,272449),(18,272449),(74,272449),(78,272449),(81,272449),(82,262219),(86,305218),(97,262219),(98,272449),(102,393295),(106,262219),(110,272449),(113,272449),(114,272449),(117,305218),(118,393295),(130,272449),(134,393295),(138,262219),(142,305218),(145,272449),(146,272449),(149,272449),(150,393295),(153,272449),(154,272449),(157,272449),(158,305218)]),([6,3840,4369,8738,61440,62532],[(0,306274),(2,76033),(4,306274),(6,98572),(8,306274),(10,99628),(12,306274),(14,306274),(16,306274),(18,306274),(81,273505),(82,306274),(97,262219),(98,306274),(106,306274),(113,306274),(114,273505),(130,305250),(134,393295),(138,393295),(142,305218),(145,306274),(146,305218),(150,393295),(154,306274),(157,306274),(158,305218)]),([6,3840,4369,8738,61440,65280],[(0,305218),(2,305218),(4,305218),(6,65803),(8,305218),(10,66859),(12,305218),(14,305218),(16,305218),(18,305218),(57,305218),(61,296011),(73,272449),(77,262219),(81,272449),(82,305218),(97,305218),(98,305218),(101,262219),(102,393295),(106,305218),(110,305218),(113,305218),(114,272449),(118,393295),(129,305218),(130,305218),(133,305218),(134,393295),(138,305218),(142,305218),(146,272449),(150,393295),(153,305218),(154,305218),(157,305218),(158,305218)]),([6,3840,4369,8738,61440,65295],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,305218),(16,393295),(18,393295),(81,393295),(82,393295),(97,262219),(98,393295),(113,305218),(114,393295),(130,393295),(133,393295),(134,393295),(138,393295),(142,393295),(146,393295),(150,393295),(154,393295),(157,393295),(158,305218)])]

noncomputable def K_56 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,8738,61986],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,272449),(15,272449),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,272449),(103,393295),(107,262219),(111,272449),(115,272449),(119,393295)]),([6,3840,4369,8738,65280],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,305218),(15,305218),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,305218),(103,393295),(107,305218),(111,305218),(115,272449),(119,393295)]),([6,3840,4369,13107,17476,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,306274),(58,393295),(82,393295),(85,393295),(98,393295),(102,393295),(105,393295),(106,393295),(110,393295),(113,393295),(114,393295),(118,393295),(129,262219),(130,393295),(141,273505),(145,306274),(153,306274),(157,393296)]),([6,3840,4369,13107,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,305218),(15,305218),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,305218),(103,393295),(107,305218),(111,305218),(115,262219),(119,305218)]),([6,3840,4369,17476,26214,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,306274),(81,393295),(82,393295),(105,393295),(106,393295),(114,393295),(117,393295),(129,262219),(130,393295),(145,66859),(153,306274)]),([6,3840,4369,17476,30583,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,306274),(58,393295),(81,393295),(82,393295),(106,393295),(109,393295),(114,393295),(117,393295),(129,262219),(130,393295),(141,273505),(145,66859),(153,306274)]),([6,3840,4369,17476,34952,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,99628),(58,393295),(81,393295),(82,393295),(105,393295),(106,393295),(113,393295),(114,393295),(129,262219),(130,393295),(141,98572),(145,66859),(153,99628)]),([6,3840,4369,17476,34952,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,262219),(58,393295),(74,305231),(78,393282),(81,393295),(82,393295),(86,305218),(98,306255),(102,393295),(105,393295),(106,393295),(110,306255),(113,393295),(114,393295),(117,305218),(118,306255),(130,393295),(141,98572),(145,305218),(149,305218),(153,306274),(157,306255)])]

noncomputable def K_57 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,17476,34952,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,99628),(57,262223),(58,393295),(73,393291),(81,393295),(82,393295),(97,393295),(105,393295),(106,393295),(113,393295),(114,393295),(130,393295),(133,393295),(141,98604)]),([6,3840,4369,17476,39321,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,99628),(81,393295),(82,393295),(106,393295),(109,393295),(113,393295),(114,393295),(129,262219),(130,393295),(145,66859),(153,99628)]),([6,3840,4369,17476,52428,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,99628),(58,393295),(74,393295),(78,393295),(81,393295),(82,393295),(86,393295),(105,393295),(106,393295),(113,393295),(114,393295),(117,393295),(129,262219),(130,393295),(141,98572),(145,99628),(149,393296),(153,99628)]),([6,3840,4369,17476,56797,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,99628),(74,393295),(78,393295),(81,393295),(82,393295),(86,393295),(106,393295),(109,393295),(113,393295),(114,393295),(117,393295),(129,262219),(130,393295),(145,99628),(149,393296),(153,99628),(158,99628)]),([6,3840,4369,17476,61440,61986],[(0,306274),(2,306274),(4,306274),(6,306274),(8,306274),(10,306274),(12,306274),(14,306274),(16,306274),(18,273505),(74,305250),(78,306242),(81,306274),(82,306274),(86,305218),(97,262219),(98,306274),(102,306255),(106,306274),(110,306255),(113,306274),(114,306255),(117,305218),(118,306274),(138,306274),(145,305218),(146,306274),(149,305218),(153,273505),(154,306274),(157,306274)]),([6,3840,4369,17476,61440,63624],[(0,99628),(2,99628),(4,99628),(6,99628),(8,99628),(10,99628),(12,99628),(14,99628),(16,99628),(18,66859),(58,99596),(81,99628),(82,99628),(97,262219),(98,99628),(106,99628),(109,98572),(113,99628),(114,99407),(138,99628),(141,98572),(145,66859),(146,99628),(154,99628),(157,99628)]),([6,3840,4369,17476,61986],[(1,306255),(3,306255),(5,306255),(7,306255),(9,306255),(10,0),(11,306255),(13,273505),(15,273505),(59,306255),(63,306255),(75,306255),(79,306255),(83,306255),(87,306255),(99,273505),(103,393295),(107,262219),(111,306255),(115,273505),(119,306274)]),([6,3840,4369,52428,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,66859),(15,66859),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,66859),(103,393295),(107,66859),(111,66859),(115,262219),(119,66859)])]

noncomputable def K_58 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,4369,56797,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,66859),(15,66859),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,66859),(103,393295),(107,66859),(111,66859),(115,393295),(119,66859)]),([6,3840,4369,61440,61986],[(1,305218),(3,305218),(5,305218),(7,305218),(9,305218),(11,305218),(13,272449),(15,272449),(59,305218),(63,305218),(75,305218),(79,305218),(83,305218),(87,305218),(99,272449),(103,272449),(107,262219),(111,305218),(115,272449),(119,305218)]),([6,3840,4369,61986],[]),([6,3840,4383,17476,34952,61440],[(0,393423),(2,207105),(4,393423),(6,393423),(8,393423),(10,393423),(12,393423),(14,393423),(16,393423),(18,98604),(58,393423),(81,393295),(105,393328),(113,393423),(114,393423),(129,262347),(130,393423),(141,98572),(145,65835),(153,98604)]),([6,3840,7953,17476,34952,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,99596),(58,393295),(61,393295),(73,393295),(81,393295),(97,393295),(105,393295),(113,393295),(114,393295),(129,99596),(130,393295),(141,98572),(145,66827),(153,99596)]),([6,3840,8192,17476,34952,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(57,393295),(58,393295),(80,0),(81,393295),(82,393295),(105,393295),(106,393295),(113,393295),(114,393295),(129,262219),(130,393295),(138,393295),(141,393295)]),([6,3840,8738,13107,17476,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,273505),(58,393295),(82,393295),(85,393295),(98,393295),(102,393295),(105,393295),(106,393295),(110,393295),(113,393295),(114,393295),(118,393295),(129,262219),(130,393295),(138,393295),(141,393295),(153,273505),(157,393296)]),([6,3840,8738,13107,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,272449),(15,272449),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,272449),(103,393295),(107,272449),(111,393295),(115,262219),(119,272449)])]

noncomputable def K_59 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,8738,17476,21845,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,273505),(81,393295),(82,393295),(105,393295),(106,393295),(114,393295),(117,393295),(129,262219),(130,393295),(137,306274),(138,393295)]),([6,3840,8738,17476,30583,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,273505),(58,393295),(81,393295),(82,393295),(106,393295),(109,393295),(114,393295),(117,393295),(129,262219),(130,393295),(138,393295),(141,393295)]),([6,3840,8738,17476,34952,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(58,393295),(81,393295),(82,393295),(105,393295),(106,393295),(113,393295),(114,393295),(129,262219),(130,393295),(138,393295),(141,393295)]),([6,3840,8738,17476,34952,61986],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(58,393295),(80,0),(81,393295),(82,393295),(105,393295),(106,393295),(113,393295),(114,393295),(130,393295),(138,393295),(141,393295)]),([6,3840,8738,17476,34952,65280],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(58,393295),(61,262219),(73,393291),(81,393295),(82,393295),(97,393295),(105,393295),(106,393295),(113,393295),(114,393295),(130,393295),(133,393295),(138,393295),(141,393295)]),([6,3840,8738,17476,43690,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(81,393295),(82,393295),(106,393295),(109,393295),(113,393295),(114,393295),(129,262219),(130,393295),(137,306274),(138,393295)]),([6,3840,8738,17476,52428,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(58,393295),(74,393295),(78,393295),(81,393295),(82,393295),(86,393295),(105,393295),(106,393295),(113,393295),(114,393295),(117,393295),(129,262219),(130,393295),(138,393295),(141,393295),(145,98572),(149,393296)]),([6,3840,8738,17476,61166,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(74,393295),(78,393295),(81,393295),(82,393295),(86,393295),(106,393295),(109,393295),(113,393295),(114,393295),(117,393295),(129,262219),(130,393295),(137,306274),(138,393295),(145,98572),(149,393296)])]

noncomputable def K_60 : List (List ℕ × List (ℕ × ℕ)) := [([6,3840,8738,52428,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,65803),(15,65803),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,65803),(103,393295),(107,65803),(111,393295),(115,262219),(119,65803)]),([6,3840,8738,61166,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,65803),(15,65803),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,65803),(103,393295),(107,65803),(111,393295),(115,305218),(119,65803)]),([6,3840,8751,17476,34952,61440],[(0,397519),(2,207109),(4,397519),(6,397519),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,98572),(58,397519),(81,397391),(105,397424),(113,397519),(114,397519),(129,266443),(130,397519),(138,397519),(141,393295)]),([6,3840,12066,17476,34952,61440],[(0,393295),(2,393295),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(58,393295),(61,393295),(73,393295),(81,393295),(97,393295),(105,393295),(113,393295),(114,393295),(129,98572),(130,393295),(138,393295),(141,393295)]),([6,3840,17476,21845,34952,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,99628),(74,393295),(82,393295),(85,393295),(105,393295),(106,393295),(113,393295),(114,393295),(129,262219),(130,393295),(149,98572),(153,99628)]),([6,3840,17476,26214,34952,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(74,393295),(82,393295),(85,393295),(105,393295),(106,393295),(113,393295),(114,393295),(129,262219),(130,393295),(137,66859),(149,393328)]),([6,3840,17476,34952,56797,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,98572),(81,393295),(82,393295),(98,393295),(106,393295),(109,393295),(114,393295),(117,393295),(129,262219),(130,393295),(157,98572),(158,393295)]),([6,3840,17476,34952,61166,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,99628),(81,393295),(82,393295),(98,393295),(106,393295),(109,393295),(114,393295),(117,393295),(129,262219),(130,393295),(137,66859),(145,99628),(157,98572)])]

noncomputable def K_61 : List (List ℕ × List (ℕ × ℕ)) := [([6,4369,8738,17476,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,76033),(16,76033),(18,393295),(57,76033),(58,76033),(73,76033),(74,76033),(78,76033),(81,76033),(82,76033),(86,76033),(105,306274),(106,393295),(113,76033),(117,76033),(145,393295),(149,108801),(154,76033),(157,76033)]),([6,4369,8738,17476,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,262219),(16,262219),(18,306274),(57,262219),(58,262219),(73,262219),(74,262219),(78,262219),(81,262219),(82,262219),(86,262219),(98,262219),(105,262219),(110,262219),(113,262219),(114,262219),(117,262219),(145,305250),(149,262220),(154,262219),(157,262219)]),([6,4369,8738,61440,61695],[(1,76033),(3,76033),(5,76033),(7,76033),(9,76033),(11,76033),(13,393295),(15,393295),(59,76033),(63,76033),(75,76033),(79,76033),(83,76033),(87,76033),(99,393295),(103,76066),(107,393295),(111,76033),(115,393295),(119,76033)]),([6,4369,8738,61440,65280],[(1,262219),(3,262219),(5,262219),(7,262219),(9,262219),(11,262219),(13,305218),(15,305218),(59,262219),(63,262219),(75,262219),(79,262219),(83,262219),(87,262219),(99,305218),(103,296011),(107,272449),(111,262219),(115,305218),(119,262219)]),([6,4369,17476,34952,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,76033),(16,76033),(18,393295),(57,76033),(58,76033),(73,76033),(74,76033),(81,76033),(82,76033),(101,76033),(105,66859),(113,99628),(133,76034),(154,76033),(157,76033)]),([6,4369,17476,34952,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,262219),(16,262219),(18,99628),(57,262219),(58,262219),(73,262219),(74,262219),(81,262219),(82,262219),(98,262219),(101,262219),(104,0),(105,262219),(106,262219),(113,262219),(114,262219),(133,294987),(154,262219),(157,262219)]),([6,8738,17476,34952,61440,61695],[(0,76033),(2,76033),(4,76033),(6,76033),(8,76033),(10,76033),(12,76033),(14,76033),(16,76033),(18,393295),(57,76033),(58,76033),(73,76033),(74,76033),(81,76033),(82,76033),(98,393295),(101,76033),(133,76033),(154,76033),(157,76033)]),([6,8738,17476,34952,61440,65280],[(0,262219),(2,262219),(4,262219),(6,262219),(8,262219),(10,262219),(12,262219),(14,262219),(16,262219),(18,98572),(57,262219),(58,262219),(73,262219),(74,262219),(81,262219),(82,262219),(101,262219),(102,262219),(106,262219),(114,262219),(133,262219),(154,262219),(157,262219)])]

noncomputable def K_62 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,3840,4369,8738],[(1,305218),(2,1),(3,305218),(5,305218),(7,305218),(9,305218),(11,305218),(13,305218),(15,305218),(17,272449),(19,272449),(57,1),(59,305218),(63,305218),(73,1),(75,305218),(79,305218),(82,1),(83,305218),(87,305218),(99,305218),(103,305218),(107,305218),(111,305218),(115,305218),(119,305218),(129,1),(131,272449),(135,305350),(139,272449),(143,305218),(147,272449),(151,272449),(155,211333),(159,305218)]),([7,15,240,3840,4369,8738,17476],[(0,306274),(2,393295),(4,306274),(6,397519),(8,306274),(10,306274),(12,306274),(14,98572),(16,306274),(18,99628),(20,306274),(22,306274),(57,306274),(58,306274),(73,306274),(74,306274),(81,306274),(82,306274),(113,306274),(129,80257),(137,211333),(149,273505),(153,273505),(154,306274),(170,306242),(174,305250),(178,306274),(182,305218),(185,306274),(186,305250),(190,306242),(193,273505),(194,306274),(198,305218),(201,306274),(202,305218),(206,305218)]),([7,15,240,3840,4369,8738,17476,34952,61440],[(96,1),(128,1),(184,0),(312,0)]),([7,15,240,3840,4369,8738,61440],[(0,305218),(2,305218),(4,305218),(6,305218),(8,305218),(10,305218),(12,305218),(14,65803),(16,305218),(18,66859),(20,305218),(22,305218),(57,305218),(58,305218),(61,393295),(62,397519),(73,305218),(74,305218),(77,393295),(78,305218),(81,305218),(82,305218),(85,397519),(86,305218),(97,305218),(101,305218),(105,305218),(109,305218),(113,305218),(117,305218),(129,272449),(133,393295),(137,272449),(141,397519),(145,272449),(149,272449),(153,272449),(154,305218),(169,393295),(170,305218),(173,393295),(174,305218),(177,397519),(178,305218),(181,397519),(182,305218),(185,305218),(186,305218),(189,305218),(190,305218),(194,305218),(198,305218),(201,305218),(202,272449),(206,305218)]),([7,15,240,3840,4369,17476,34952],[(0,99628),(2,393295),(4,99628),(6,397519),(8,99628),(10,99628),(12,99628),(14,99628),(16,99628),(18,305218),(20,99628),(22,306274),(57,99628),(58,99628),(73,99628),(74,99628),(81,99628),(82,99628),(98,98604),(106,99628),(113,99628),(114,99596),(145,99628),(153,99628),(154,99628),(185,66859),(193,98572),(194,99628),(201,66859),(202,99628)]),([7,15,240,3840,8738,17476,34952],[(0,98572),(2,393295),(4,98572),(6,397519),(8,98572),(10,98572),(12,98572),(14,98572),(16,98572),(18,272449),(20,98572),(22,273505),(57,98572),(58,98572),(73,98572),(74,98572),(81,98572),(82,98572),(96,1),(97,98572),(98,98572),(105,98572),(106,98572),(114,98572),(117,98572),(145,98572),(153,98572),(154,98572),(185,65803),(193,99628),(194,98572),(201,65803),(202,98572)]),([7,15,240,4369,8738,17476,61440],[(0,306274),(2,262219),(4,306274),(6,266443),(8,306274),(10,98572),(12,306274),(14,99628),(16,306274),(18,306274),(20,306274),(22,306274),(57,306274),(58,306274),(113,273505),(114,306274),(130,306242),(134,305250),(138,306274),(142,305218),(145,273505),(146,306274),(150,305218),(153,306274),(154,305218),(158,305218),(169,76033),(170,306274),(177,207109),(178,306274),(186,306274),(193,306274),(198,306274),(201,306274),(202,306274),(205,305218)]),([7,15,240,4369,8738,61440],[(1,305218),(2,1),(3,305218),(5,305218),(7,305218),(9,305218),(11,305218),(13,272449),(15,272449),(17,305218),(19,305218),(57,1),(59,305218),(63,305218),(75,305218),(79,305218),(83,305218),(87,305218),(99,272449),(103,305350),(107,272449),(111,305218),(115,207109),(119,305218),(129,1),(131,305218),(135,305218),(138,1),(139,305218),(143,305218),(147,305218),(151,305218),(155,272449),(159,305218)])]

noncomputable def K_63 : List (List ℕ × List (ℕ × ℕ)) := [([7,15,240,4369,17476,34952,61440],[(0,99628),(2,262219),(4,99628),(6,266443),(8,99628),(10,99628),(12,99628),(14,305218),(16,99628),(18,306274),(20,99628),(22,99628),(57,99628),(58,99628),(74,98604),(82,99628),(113,99628),(114,99628),(145,98572),(146,99628),(153,66859),(154,99628),(169,76033),(170,99628),(177,207109),(178,99628),(186,99628),(189,98572),(192,0),(193,66859),(194,99628),(201,99628),(202,66859)]),([7,15,240,8738,17476,34952,61440],[(0,98572),(2,262219),(4,98572),(6,266443),(8,98572),(10,98572),(12,98572),(14,272449),(16,98572),(18,273505),(20,98572),(22,98572),(57,98572),(58,98572),(74,98572),(82,98572),(113,98572),(114,98572),(145,99628),(146,98572),(153,65803),(154,98572),(169,76033),(170,98572),(177,207109),(178,98572),(189,98572),(190,98572),(194,98572),(202,65803)]),([7,15,3840,4369,8738,17476,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,397519),(20,397519),(22,306274),(57,397519),(58,397519),(61,393295),(73,393423),(77,397391),(97,397519),(101,393295),(113,397519),(114,397519),(129,397391),(130,397519),(133,393328),(134,397519),(138,397519),(142,397519),(145,397519),(146,397519),(150,397519),(153,397519),(154,397519),(158,397519),(169,393295),(170,397519),(173,393295),(177,266443),(178,397519),(193,306274),(194,397519),(201,306274),(205,397520)]),([7,15,3840,4369,8738,61440],[(1,397519),(2,1),(3,397519),(5,397519),(7,397519),(9,397519),(11,397519),(13,397519),(15,397519),(17,305218),(19,305218),(59,397519),(63,397519),(75,397519),(79,397519),(83,397519),(87,397519),(99,397519),(103,397519),(107,397519),(111,397519),(115,397519),(119,397519),(131,305218),(135,397519),(139,305218),(143,397519),(147,305218),(151,305218),(155,272449),(159,397519)]),([7,15,3840,4369,17476,34952,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,397519),(20,397519),(22,99628),(57,397519),(58,397519),(61,393295),(73,393423),(74,397519),(77,397391),(82,397519),(97,397391),(101,393328),(113,397519),(114,397519),(129,397424),(133,393295),(145,397519),(146,397519),(153,397519),(154,397519),(169,393295),(170,397519),(173,393295),(177,266443),(178,397519),(189,98572),(193,66859),(201,99628)]),([7,15,3840,8738,17476,34952,61440],[(0,397519),(2,397519),(4,397519),(6,207109),(8,397519),(10,397519),(12,397519),(14,397519),(16,397519),(18,397519),(20,397519),(22,98572),(57,397519),(58,397519),(61,393295),(73,397519),(74,397519),(77,393295),(82,397519),(97,397391),(101,393328),(113,397519),(114,397519),(129,397424),(133,393295),(145,397519),(146,397519),(153,397519),(154,397519),(169,393295),(170,397519),(173,393295),(177,266443),(178,397519),(186,397519),(189,397519)]),([7,3840,4369,8738,17476,34952,61440],[(0,393295),(2,76033),(4,393295),(6,393295),(8,393295),(10,393295),(12,393295),(14,393295),(16,393295),(18,393295),(20,393295),(22,80257),(58,393295),(62,393295),(74,393295),(78,393295),(81,393295),(82,393295),(85,393295),(86,393295),(98,393295),(102,393295),(105,393295),(106,393295),(109,393295),(110,393295),(113,393295),(114,393295),(117,393295),(118,393295),(130,393295),(134,393295),(137,393295),(138,393295),(141,393295),(142,393295),(145,393295),(146,393295),(149,393295),(150,393295),(153,393295),(154,393295),(157,393295),(158,393295),(169,262219),(170,393295),(177,262219),(181,98572),(185,262219),(186,393295),(189,393295),(193,262219),(197,393328),(201,262219),(205,393295)]),([7,3840,4369,8738,17476,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(11,393295),(13,393295),(14,0),(15,393295),(17,306274),(19,306274),(59,393295),(63,393295),(75,393295),(79,393295),(83,393295),(87,393295),(99,393295),(103,393295),(107,393295),(111,393295),(115,393295),(119,393295),(131,306274),(135,393295),(139,306274),(143,306274),(147,273505),(151,393295),(155,306274),(159,393328)])]

noncomputable def K_64 : List (List ℕ × List (ℕ × ℕ)) := [([7,3840,4369,8738,61440],[]),([7,3840,4369,17476,34952,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(10,0),(11,393295),(13,393295),(15,393295),(17,99628),(19,99628),(59,393295),(63,393295),(75,393295),(79,393295),(82,0),(83,393295),(87,393295),(99,393295),(103,393295),(105,0),(107,393295),(111,393295),(113,0),(115,393295),(119,393295),(131,99628),(135,393295),(139,99628),(143,99628),(145,0),(147,99628),(151,393328),(155,66859),(159,393295)]),([7,3840,8738,17476,34952,61440],[(1,393295),(3,393295),(5,393295),(7,393295),(9,393295),(10,0),(11,393295),(13,393295),(15,393295),(17,98572),(19,98572),(59,393295),(63,393295),(75,393295),(79,393295),(82,0),(83,393295),(87,393295),(99,393295),(103,393295),(105,0),(107,393295),(111,393295),(113,0),(115,393295),(119,393295),(131,98572),(135,393295),(139,98572),(143,393295),(147,98572),(151,393328),(155,65803),(159,393295)])]

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
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_54 : K_54.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_55 : K_55.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_56 : K_56.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_57 : K_57.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_58 : K_58.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_59 : K_59.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_60 : K_60.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_61 : K_61.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_62 : K_62.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_63 : K_63.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_64 : K_64.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = (((((((K_0 ++ K_1) ++ (K_2 ++ K_3)) ++ ((K_4 ++ K_5) ++ (K_6 ++ K_7))) ++ (((K_8 ++ K_9) ++ (K_10 ++ K_11)) ++ ((K_12 ++ K_13) ++ (K_14 ++ K_15)))) ++ ((((K_16 ++ K_17) ++ (K_18 ++ K_19)) ++ ((K_20 ++ K_21) ++ (K_22 ++ K_23))) ++ (((K_24 ++ K_25) ++ (K_26 ++ K_27)) ++ ((K_28 ++ K_29) ++ (K_30 ++ K_31))))) ++ (((((K_32 ++ K_33) ++ (K_34 ++ K_35)) ++ ((K_36 ++ K_37) ++ (K_38 ++ K_39))) ++ (((K_40 ++ K_41) ++ (K_42 ++ K_43)) ++ ((K_44 ++ K_45) ++ (K_46 ++ K_47)))) ++ ((((K_48 ++ K_49) ++ (K_50 ++ K_51)) ++ ((K_52 ++ K_53) ++ (K_54 ++ K_55))) ++ (((K_56 ++ K_57) ++ (K_58 ++ K_59)) ++ ((K_60 ++ K_61) ++ (K_62 ++ (K_63 ++ K_64)))))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app (all_app c_0 c_1) (all_app c_2 c_3)) (all_app (all_app c_4 c_5) (all_app c_6 c_7))) (all_app (all_app (all_app c_8 c_9) (all_app c_10 c_11)) (all_app (all_app c_12 c_13) (all_app c_14 c_15)))) (all_app (all_app (all_app (all_app c_16 c_17) (all_app c_18 c_19)) (all_app (all_app c_20 c_21) (all_app c_22 c_23))) (all_app (all_app (all_app c_24 c_25) (all_app c_26 c_27)) (all_app (all_app c_28 c_29) (all_app c_30 c_31))))) (all_app (all_app (all_app (all_app (all_app c_32 c_33) (all_app c_34 c_35)) (all_app (all_app c_36 c_37) (all_app c_38 c_39))) (all_app (all_app (all_app c_40 c_41) (all_app c_42 c_43)) (all_app (all_app c_44 c_45) (all_app c_46 c_47)))) (all_app (all_app (all_app (all_app c_48 c_49) (all_app c_50 c_51)) (all_app (all_app c_52 c_53) (all_app c_54 c_55))) (all_app (all_app (all_app c_56 c_57) (all_app c_58 c_59)) (all_app (all_app c_60 c_61) (all_app c_62 (all_app c_63 c_64)))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_seven :
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 7 ∧ PEqualNP.Represents.Represents
        (fun u v : Fin 4 => (5068 : ℕ).testBit (4 * u.val + v.val)) C :=
  signed_rep_lb 5068 7 2 0 PD_ PM_ XS_ G_ T_cert (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel)
end PEqualNP.Outside.L_meta_19203

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19203 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5068 : ℕ).testBit (4 * u.val + v.val)) C) := PEqualNP.Outside.L_meta_19203.no_seven
