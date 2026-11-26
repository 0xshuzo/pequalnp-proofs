import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24645.Core

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
  !((x 2 && x 3) || ((x 5 && !(x 0 || (x 1 || x 2))) || (x 4 && (x 1 || x 2))))
def pairInput (i j : Fin 6) := List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)
theorem codeInputs : ∀ p : Fin 6 × Fin 6, List.ofFn (pt 6 (pairCode p)) = pairInput p.1 p.2 := by
  decide +kernel
theorem graphRow : ∀ i j : Fin 6, reference (pt 6 (pairCode (i,j))) =
    (274877375 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel
def samplePairs : List (Fin 6 × Fin 6) := [(0, 5), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (4, 4), (4, 5), (5, 5)]
def points := samplePairs.map pairCode

def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) =
  (274877375 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def M_ : ℕ := 1023

def Y_ : ℕ := 203

def XS_ : List ℕ := [1, 6, 120, 18, 420, 833]

def PD_ : List (ℕ × ℕ) := [(1, 174), (2, 249), (3, 82), (4, 7), (5, 13), (6, 8), (7, 2), (8, 3), (9, 1)]

def PM_ : List (ℕ × ℕ) := [(2, 203), (4, 203), (5, 203), (8, 203), (9, 203)]

def G_ : List (List ℕ) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,6,306,509] BT.lf) [3,18,294,509] (BT.nd BT.lf [3,48,121,837] BT.lf)) [3,48,123,839] (BT.nd (BT.nd BT.lf [3,52,121,833] BT.lf) [3,52,125,833] BT.lf)) [3,52,127,833] (BT.nd (BT.nd (BT.nd BT.lf [3,103,851] BT.lf) [3,115,839] BT.lf) [3,120,179] (BT.nd (BT.nd BT.lf [3,121,178] BT.lf) [3,121,438,893] BT.lf))) [3,125,438,893] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,127,436,895] BT.lf) [3,380,439] BT.lf) [3,381,438] (BT.nd (BT.nd BT.lf [4,1,6,306,508] BT.lf) [4,1,18,294,508] BT.lf)) [4,1,48,120,837] (BT.nd (BT.nd (BT.nd BT.lf [4,1,48,122,839] BT.lf) [4,1,52,120,833] BT.lf) [4,1,52,124,833] (BT.nd (BT.nd BT.lf [4,1,52,126,833] BT.lf) [4,1,102,851] BT.lf)))) [4,1,114,839] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1,120,178] BT.lf) [4,1,120,438,893] (BT.nd BT.lf [4,1,124,438,893] BT.lf)) [4,1,126,436,895] (BT.nd (BT.nd BT.lf [4,1,380,438] BT.lf) [4,4,48,121,833] BT.lf)) [4,4,121,438,889] (BT.nd (BT.nd (BT.nd BT.lf [4,6,18,288,509] BT.lf) [4,6,48,123,833] BT.lf) [4,6,50,121,851] (BT.nd (BT.nd BT.lf [4,6,50,121,883] BT.lf) [4,6,97,851] BT.lf))) [4,6,105,420,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,6,115,833] BT.lf) [4,6,120,306,421] BT.lf) [4,6,121,306,420] (BT.nd (BT.nd BT.lf [4,6,121,436,889] BT.lf) [4,6,123,438,889] BT.lf)) [4,6,420,889,918] (BT.nd (BT.nd (BT.nd BT.lf [4,7,96,851] BT.lf) [4,7,114,833] BT.lf) [4,16,36,121,833] (BT.nd (BT.nd BT.lf [4,16,36,127,833] BT.lf) [4,16,127,420,895] BT.lf))))) [4,18,36,121,889] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,18,36,127,889] BT.lf) [4,18,38,121,851] (BT.nd BT.lf [4,18,48,121,839] BT.lf)) [4,18,50,121,839] (BT.nd (BT.nd BT.lf [4,18,97,839] BT.lf) [4,18,103,833] BT.lf)) [4,18,120,161] (BT.nd (BT.nd (BT.nd BT.lf [4,18,120,294,421] BT.lf) [4,18,121,160] BT.lf) [4,18,121,292,889] (BT.nd (BT.nd BT.lf [4,18,121,294,420] BT.lf) [4,18,121,420,893] BT.lf))) [4,18,121,863] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,18,125,420,893] BT.lf) [4,18,380,421] BT.lf) [4,18,381,420] (BT.nd (BT.nd BT.lf [4,19,48,120,839] BT.lf) [4,19,50,120,839] BT.lf)) [4,19,51,120,839] (BT.nd (BT.nd (BT.nd BT.lf [4,19,96,839] BT.lf) [4,19,102,833] BT.lf) [4,19,120,160] (BT.nd (BT.nd BT.lf [4,19,120,863] BT.lf) [4,19,380,420] BT.lf)))) [4,22,120,135,420] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,22,120,165] BT.lf) [4,22,120,255,420] BT.lf) [4,22,120,420,768] (BT.nd (BT.nd BT.lf [4,22,120,420,888] BT.lf) [4,22,121,134,420] BT.lf)) [4,22,121,164] (BT.nd (BT.nd (BT.nd BT.lf [4,22,121,255,420] BT.lf) [4,22,121,420,768] BT.lf) [4,22,121,420,889] (BT.nd (BT.nd BT.lf [4,22,121,603,889] BT.lf) [4,22,121,859] BT.lf))) [4,22,123,420,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,22,127,420,889] BT.lf) [4,22,376,421] BT.lf) [4,22,377,420] (BT.nd (BT.nd BT.lf [4,22,420,509,889] BT.lf) [4,22,420,768,902] BT.lf)) [4,22,420,889,902] (BT.nd (BT.nd (BT.nd BT.lf [4,23,120,164] BT.lf) [4,23,120,859] BT.lf) [4,23,376,420] (BT.nd (BT.nd BT.lf [4,50,51,120,839] BT.lf) [4,50,121,839] BT.lf)))))) [4,51,120,839] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,111,420,833] BT.lf) [4,120,121,438,837] (BT.nd BT.lf [4,120,123,438,839] BT.lf)) [4,120,123,439,839] (BT.nd (BT.nd BT.lf [4,120,260,439] BT.lf) [4,120,261,438] BT.lf)) [4,120,278,421] (BT.nd (BT.nd (BT.nd BT.lf [4,120,279,420] BT.lf) [4,121,122,438,839] BT.lf) [4,121,123,438,839] (BT.nd (BT.nd BT.lf [4,121,124,438,833] BT.lf) [4,121,125,438,833] BT.lf))) [4,121,126,436,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,121,127,436,833] BT.lf) [4,121,260,438] BT.lf) [4,121,278,420] (BT.nd (BT.nd BT.lf [4,121,420,889,1001] BT.lf) [4,121,434,833] BT.lf)) [4,121,438,837] (BT.nd (BT.nd (BT.nd BT.lf [4,121,855,997] BT.lf) [4,123,438,839] BT.lf) [4,123,439,839] (BT.nd (BT.nd BT.lf [4,124,125,438,833] BT.lf) [4,125,438,833] BT.lf)))) [4,126,127,436,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,127,436,833] BT.lf) [4,127,438,509,833] (BT.nd BT.lf [5,1,4,48,120,833] BT.lf)) [5,1,4,120,438,889] (BT.nd (BT.nd BT.lf [5,1,6,18,288,508] BT.lf) [5,1,6,48,122,833] BT.lf)) [5,1,6,50,120,851] (BT.nd (BT.nd (BT.nd BT.lf [5,1,6,50,120,883] BT.lf) [5,1,6,96,851] BT.lf) [5,1,6,104,420,889] (BT.nd (BT.nd BT.lf [5,1,6,114,833] BT.lf) [5,1,6,120,306,420] BT.lf))) [5,1,6,120,436,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1,6,122,438,889] BT.lf) [5,1,6,420,889,919] BT.lf) [5,1,16,36,120,833] (BT.nd (BT.nd BT.lf [5,1,16,36,126,833] BT.lf) [5,1,16,126,420,895] BT.lf)) [5,1,18,36,120,889] (BT.nd (BT.nd (BT.nd BT.lf [5,1,18,36,126,889] BT.lf) [5,1,18,38,120,851] BT.lf) [5,1,18,48,120,839] (BT.nd (BT.nd BT.lf [5,1,18,50,120,839] BT.lf) [5,1,18,96,839] BT.lf))))) [5,1,18,102,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1,18,120,160] BT.lf) [5,1,18,120,292,889] (BT.nd BT.lf [5,1,18,120,294,420] BT.lf)) [5,1,18,120,420,893] (BT.nd (BT.nd BT.lf [5,1,18,120,863] BT.lf) [5,1,18,124,420,893] BT.lf)) [5,1,18,380,420] (BT.nd (BT.nd (BT.nd BT.lf [5,1,22,120,134,420] BT.lf) [5,1,22,120,164] BT.lf) [5,1,22,120,254,420] (BT.nd (BT.nd BT.lf [5,1,22,120,420,769] BT.lf) [5,1,22,120,420,889] BT.lf))) [5,1,22,120,421,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1,22,120,603,889] BT.lf) [5,1,22,120,859] BT.lf) [5,1,22,121,420,889] (BT.nd (BT.nd BT.lf [5,1,22,122,420,889] BT.lf) [5,1,22,126,420,889] BT.lf)) [5,1,22,376,420] (BT.nd (BT.nd (BT.nd BT.lf [5,1,22,420,508,889] BT.lf) [5,1,22,420,769,903] BT.lf) [5,1,22,420,889,903] (BT.nd (BT.nd BT.lf [5,1,23,120,420,889] BT.lf) [5,1,50,120,839] BT.lf)))) [5,1,110,420,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1,120,122,438,839] BT.lf) [5,1,120,124,438,833] BT.lf) [5,1,120,126,436,833] (BT.nd (BT.nd BT.lf [5,1,120,260,438] BT.lf) [5,1,120,278,420] BT.lf)) [5,1,120,420,889,1001] (BT.nd (BT.nd (BT.nd BT.lf [5,1,120,434,833] BT.lf) [5,1,120,438,837] BT.lf) [5,1,120,855,997] (BT.nd (BT.nd BT.lf [5,1,122,438,839] BT.lf) [5,1,124,438,833] BT.lf))) [5,1,126,436,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1,126,438,508,833] BT.lf) [5,4,18,121,420,889] BT.lf) [5,4,120,121,438,833] (BT.nd (BT.nd BT.lf [5,4,121,438,833] BT.lf) [5,5,120,438,833] BT.lf)) [5,6,16,121,420,889] (BT.nd (BT.nd (BT.nd BT.lf [5,6,18,32,121,851] BT.lf) [5,6,18,36,121,833] BT.lf) [5,6,18,36,127,833] (BT.nd (BT.nd BT.lf [5,6,18,48,121,833] BT.lf) [5,6,18,50,121,833] BT.lf))))))) [5,6,18,97,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,6,18,120,135,420] BT.lf) [5,6,18,120,165] (BT.nd BT.lf [5,6,18,120,255,420] BT.lf)) [5,6,18,120,288,421] (BT.nd (BT.nd BT.lf [5,6,18,120,420,768] BT.lf) [5,6,18,120,420,888] BT.lf)) [5,6,18,121,134,420] (BT.nd (BT.nd (BT.nd BT.lf [5,6,18,121,164] BT.lf) [5,6,18,121,255,420] BT.lf) [5,6,18,121,288,420] (BT.nd (BT.nd BT.lf [5,6,18,121,420,768] BT.lf) [5,6,18,121,420,865] BT.lf))) [5,6,18,121,420,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,6,18,121,420,891] BT.lf) [5,6,18,121,420,895] BT.lf) [5,6,18,121,438,889] (BT.nd (BT.nd BT.lf [5,6,18,121,603,889] BT.lf) [5,6,18,121,859] BT.lf)) [5,6,18,123,420,889] (BT.nd (BT.nd (BT.nd BT.lf [5,6,18,127,420,889] BT.lf) [5,6,18,127,420,895] BT.lf) [5,6,18,376,421] (BT.nd (BT.nd BT.lf [5,6,18,377,420] BT.lf) [5,6,18,420,509,889] BT.lf)))) [5,6,18,420,768,902] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,6,18,420,889,902] BT.lf) [5,6,19,48,120,833] (BT.nd BT.lf [5,6,19,50,120,833] BT.lf)) [5,6,19,51,120,833] (BT.nd (BT.nd BT.lf [5,6,19,96,833] BT.lf) [5,6,19,120,164] BT.lf)) [5,6,19,120,438,889] (BT.nd (BT.nd (BT.nd BT.lf [5,6,19,120,859] BT.lf) [5,6,19,376,420] BT.lf) [5,6,22,121,420,889] (BT.nd (BT.nd BT.lf [5,6,48,121,420,833] BT.lf) [5,6,50,51,120,833] BT.lf))) [5,6,50,121,420,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,6,50,121,833] BT.lf) [5,6,51,120,833] BT.lf) [5,6,105,120,420,833] (BT.nd (BT.nd BT.lf [5,6,105,121,420,833] BT.lf) [5,6,105,420,833] BT.lf)) [5,6,120,121,436,833] (BT.nd (BT.nd (BT.nd BT.lf [5,6,120,123,438,833] BT.lf) [5,6,120,123,439,833] BT.lf) [5,6,120,274,421] (BT.nd (BT.nd BT.lf [5,6,120,275,420] BT.lf) [5,6,120,420,833,918] BT.lf))))) [5,6,121,122,438,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,6,121,123,438,833] BT.lf) [5,6,121,274,420] (BT.nd BT.lf [5,6,121,420,438,889] BT.lf)) [5,6,121,420,833,918] (BT.nd (BT.nd BT.lf [5,6,121,420,889,1005] BT.lf) [5,6,121,436,833] BT.lf)) [5,6,121,438,509,833] (BT.nd (BT.nd (BT.nd BT.lf [5,6,121,438,851] BT.lf) [5,6,121,851,997] BT.lf) [5,6,123,438,833] (BT.nd (BT.nd BT.lf [5,6,123,439,833] BT.lf) [5,6,420,833,902,918] BT.lf))) [5,6,420,833,918] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,18,36,120,833] BT.lf) [5,7,18,36,126,833] BT.lf) [5,7,18,36,127,833] (BT.nd (BT.nd BT.lf [5,7,18,96,833] BT.lf) [5,7,18,120,164] BT.lf)) [5,7,18,120,420,895] (BT.nd (BT.nd (BT.nd BT.lf [5,7,18,120,859] BT.lf) [5,7,18,121,420,889] BT.lf) [5,7,18,126,420,889] (BT.nd (BT.nd BT.lf [5,7,18,126,420,895] BT.lf) [5,7,18,127,420,889] BT.lf)))) [5,7,18,127,420,895] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,7,18,376,420] BT.lf) [5,7,19,120,420,889] BT.lf) [5,7,22,120,420,889] (BT.nd (BT.nd BT.lf [5,7,23,120,420,889] BT.lf) [5,7,50,120,833] BT.lf)) [5,7,104,420,833] (BT.nd (BT.nd (BT.nd BT.lf [5,7,120,274,420] BT.lf) [5,7,120,436,833] BT.lf) [5,7,120,438,851] (BT.nd (BT.nd BT.lf [5,7,120,851,997] BT.lf) [5,7,122,438,833] BT.lf))) [5,7,420,833,919] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16,121,126,420,833] BT.lf) [5,16,121,127,420,833] BT.lf) [5,16,126,127,420,833] (BT.nd (BT.nd BT.lf [5,16,127,420,833] BT.lf) [5,17,126,420,833] BT.lf)) [5,18,19,32,120,839] (BT.nd (BT.nd (BT.nd BT.lf [5,18,19,38,120,833] BT.lf) [5,18,22,121,420,889] BT.lf) [5,18,32,121,839] (BT.nd (BT.nd BT.lf [5,18,33,120,839] BT.lf) [5,18,36,120,121,833] BT.lf)))))) [5,18,36,120,127,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,18,36,121,127,833] BT.lf) [5,18,36,121,833] (BT.nd BT.lf [5,18,37,120,833] BT.lf)) [5,18,38,121,420,833] (BT.nd (BT.nd BT.lf [5,18,38,121,833] BT.lf) [5,18,39,120,833] BT.lf)) [5,18,71,121,420,833] (BT.nd (BT.nd (BT.nd BT.lf [5,18,120,121,420,837] BT.lf) [5,18,120,121,438,839] BT.lf) [5,18,120,123,420,839] (BT.nd (BT.nd BT.lf [5,18,120,126,191,420] BT.lf) [5,18,120,126,420,832] BT.lf))) [5,18,120,127,420,839] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,18,120,127,420,895] BT.lf) [5,18,120,185,420] BT.lf) [5,18,120,260,421] (BT.nd (BT.nd BT.lf [5,18,120,261,420] BT.lf) [5,18,120,262,421] BT.lf)) [5,18,120,263,420] (BT.nd (BT.nd (BT.nd BT.lf [5,18,120,420,838] BT.lf) [5,18,121,122,420,839] BT.lf) [5,18,121,123,420,839] (BT.nd (BT.nd BT.lf [5,18,121,124,420,833] BT.lf) [5,18,121,125,420,833] BT.lf)))) [5,18,121,126,420,839] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,18,121,126,420,889] BT.lf) [5,18,121,127,190,420] BT.lf) [5,18,121,127,420,833] (BT.nd (BT.nd BT.lf [5,18,121,127,420,839] BT.lf) [5,18,121,127,420,851] BT.lf)) [5,18,121,127,420,889] (BT.nd (BT.nd (BT.nd BT.lf [5,18,121,127,420,895] BT.lf) [5,18,121,127,438,833] BT.lf) [5,18,121,127,603,833] (BT.nd (BT.nd BT.lf [5,18,121,184,420] BT.lf) [5,18,121,260,420] BT.lf))) [5,18,121,262,420] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,18,121,416,833] BT.lf) [5,18,121,420,833,896] BT.lf) [5,18,121,420,837] (BT.nd (BT.nd BT.lf [5,18,121,420,839] BT.lf) [5,18,121,420,839,889] BT.lf)) [5,18,121,420,855] (BT.nd (BT.nd (BT.nd BT.lf [5,18,121,420,889,895] BT.lf) [5,18,121,420,889,1017] BT.lf) [5,18,121,420,895] (BT.nd (BT.nd BT.lf [5,18,121,421,839] BT.lf) [5,18,121,422,839] BT.lf))))) [5,18,121,438,839] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,18,121,603,839] BT.lf) [5,18,121,607,833] (BT.nd BT.lf [5,18,121,839,997] BT.lf)) [5,18,121,839,999] (BT.nd (BT.nd BT.lf [5,18,123,420,839] BT.lf) [5,18,124,125,420,833] BT.lf)) [5,18,125,420,833] (BT.nd (BT.nd (BT.nd BT.lf [5,18,126,127,420,889] BT.lf) [5,18,127,420,509,833] BT.lf) [5,18,127,420,833,902] (BT.nd (BT.nd BT.lf [5,18,127,420,839] BT.lf) [5,18,127,420,889] BT.lf))) [5,18,127,422,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,18,127,423,833] BT.lf) [5,18,420,839,902] BT.lf) [5,19,22,120,420,889] (BT.nd (BT.nd BT.lf [5,19,32,120,839] BT.lf) [5,19,36,120,833] BT.lf)) [5,19,38,120,833] (BT.nd (BT.nd (BT.nd BT.lf [5,19,120,123,420,839] BT.lf) [5,19,120,126,438,833] BT.lf) [5,19,120,126,439,833] (BT.nd (BT.nd BT.lf [5,19,120,127,420,833] BT.lf) [5,19,120,184,420] BT.lf)))) [5,19,120,260,420] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,19,120,262,420] BT.lf) [5,19,120,416,833] BT.lf) [5,19,120,420,837] (BT.nd (BT.nd BT.lf [5,19,120,420,839] BT.lf) [5,19,120,420,855] BT.lf)) [5,19,120,420,895] (BT.nd (BT.nd (BT.nd BT.lf [5,19,120,421,839] BT.lf) [5,19,120,422,839] BT.lf) [5,19,120,438,839] (BT.nd (BT.nd BT.lf [5,19,120,439,839] BT.lf) [5,19,120,603,839] BT.lf))) [5,19,120,607,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,19,120,839,997] BT.lf) [5,19,120,839,999] BT.lf) [5,19,121,126,420,833] (BT.nd (BT.nd BT.lf [5,19,121,420,839] BT.lf) [5,19,122,420,839] BT.lf)) [5,19,123,420,839] (BT.nd (BT.nd (BT.nd BT.lf [5,19,124,420,833] BT.lf) [5,19,126,420,839] BT.lf) [5,19,126,420,889] (BT.nd (BT.nd BT.lf [5,19,126,422,833] BT.lf) [5,19,420,839,903] BT.lf)))))))) [5,22,23,120,420,889] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,22,65,120,420,833] BT.lf) [5,22,65,121,420,833] (BT.nd BT.lf [5,22,120,121,190,420] BT.lf)) [5,22,120,121,420,833] (BT.nd (BT.nd BT.lf [5,22,120,121,420,889] BT.lf) [5,22,120,121,421,833] BT.lf)) [5,22,120,121,603,833] (BT.nd (BT.nd (BT.nd BT.lf [5,22,120,123,420,833] BT.lf) [5,22,120,127,420,833] BT.lf) [5,22,120,191,420] (BT.nd (BT.nd BT.lf [5,22,120,256,421] BT.lf) [5,22,120,257,420] BT.lf))) [5,22,120,420,421,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,22,120,420,509,833] BT.lf) [5,22,120,420,832] BT.lf) [5,22,120,420,833,902] (BT.nd (BT.nd BT.lf [5,22,120,420,889,1022] BT.lf) [5,22,121,121,420,833] BT.lf)) [5,22,121,123,420,833] (BT.nd (BT.nd (BT.nd BT.lf [5,22,121,127,420,833] BT.lf) [5,22,121,190,420] BT.lf) [5,22,121,256,420] (BT.nd (BT.nd BT.lf [5,22,121,420,509,833] BT.lf) [5,22,121,420,833] BT.lf)))) [5,22,121,420,833,889] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,22,121,420,833,902] BT.lf) [5,22,121,420,833,903] (BT.nd BT.lf [5,22,121,420,839] BT.lf)) [5,22,121,420,851] (BT.nd (BT.nd BT.lf [5,22,121,420,855] BT.lf) [5,22,121,420,889] BT.lf)) [5,22,121,421,833] (BT.nd (BT.nd (BT.nd BT.lf [5,22,121,603,833] BT.lf) [5,22,121,833,997] BT.lf) [5,22,420,833,902] (BT.nd (BT.nd BT.lf [5,23,120,121,420,833] BT.lf) [5,23,120,123,420,833] BT.lf))) [5,23,120,127,420,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,23,120,190,420] BT.lf) [5,23,120,256,420] BT.lf) [5,23,120,420,833] (BT.nd (BT.nd BT.lf [5,23,120,420,839] BT.lf) [5,23,120,420,851] BT.lf)) [5,23,120,420,855] (BT.nd (BT.nd (BT.nd BT.lf [5,23,120,420,889] BT.lf) [5,23,120,421,833] BT.lf) [5,23,120,603,833] (BT.nd (BT.nd BT.lf [5,23,120,833,997] BT.lf) [5,23,121,420,833] BT.lf))))) [5,23,420,833,903] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,120,121,420,833,1001] BT.lf) [5,120,420,439,839] (BT.nd BT.lf [5,120,420,833,1000] BT.lf)) [5,120,420,839,1004] (BT.nd (BT.nd BT.lf [5,120,421,438,839] BT.lf) [5,121,127,420,438,833] BT.lf)) [5,121,127,420,833,851] (BT.nd (BT.nd (BT.nd BT.lf [5,121,127,420,833,1005] BT.lf) [5,121,420,438,839] BT.lf) [5,121,420,833,855] (BT.nd (BT.nd BT.lf [5,121,420,833,1001] BT.lf) [5,121,420,839,1005] BT.lf))) [6,1,4,18,120,420,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,4,120,438,833] BT.lf) [6,1,6,16,120,420,889] BT.lf) [6,1,6,18,32,120,851] (BT.nd (BT.nd BT.lf [6,1,6,18,36,120,833] BT.lf) [6,1,6,18,36,126,833] BT.lf)) [6,1,6,18,48,120,833] (BT.nd (BT.nd (BT.nd BT.lf [6,1,6,18,50,120,833] BT.lf) [6,1,6,18,96,833] BT.lf) [6,1,6,18,120,134,420] (BT.nd (BT.nd BT.lf [6,1,6,18,120,164] BT.lf) [6,1,6,18,120,254,420] BT.lf)))) [6,1,6,18,120,288,420] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,6,18,120,420,769] BT.lf) [6,1,6,18,120,420,865] BT.lf) [6,1,6,18,120,420,889] (BT.nd (BT.nd BT.lf [6,1,6,18,120,420,891] BT.lf) [6,1,6,18,120,420,895] BT.lf)) [6,1,6,18,120,421,889] (BT.nd (BT.nd (BT.nd BT.lf [6,1,6,18,120,438,889] BT.lf) [6,1,6,18,120,603,889] BT.lf) [6,1,6,18,120,859] (BT.nd (BT.nd BT.lf [6,1,6,18,121,420,889] BT.lf) [6,1,6,18,122,420,889] BT.lf))) [6,1,6,18,126,420,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,6,18,126,420,895] BT.lf) [6,1,6,18,376,420] BT.lf) [6,1,6,18,420,508,889] (BT.nd (BT.nd BT.lf [6,1,6,18,420,769,903] BT.lf) [6,1,6,18,420,889,903] BT.lf)) [6,1,6,19,120,420,889] (BT.nd (BT.nd (BT.nd BT.lf [6,1,6,22,120,420,889] BT.lf) [6,1,6,48,120,420,833] BT.lf) [6,1,6,50,120,420,833] (BT.nd (BT.nd BT.lf [6,1,6,50,120,833] BT.lf) [6,1,6,104,120,420,833] BT.lf)))))) [6,1,6,104,420,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,6,120,122,438,833] BT.lf) [6,1,6,120,274,420] (BT.nd BT.lf [6,1,6,120,420,438,889] BT.lf)) [6,1,6,120,420,833,919] (BT.nd (BT.nd BT.lf [6,1,6,120,420,889,1005] BT.lf) [6,1,6,120,436,833] BT.lf)) [6,1,6,120,438,508,833] (BT.nd (BT.nd (BT.nd BT.lf [6,1,6,120,438,851] BT.lf) [6,1,6,120,851,997] BT.lf) [6,1,6,122,438,833] (BT.nd (BT.nd BT.lf [6,1,6,420,833,903,919] BT.lf) [6,1,6,420,833,919] BT.lf))) [6,1,7,18,120,420,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,16,120,126,420,833] BT.lf) [6,1,16,126,420,833] BT.lf) [6,1,18,22,120,420,889] (BT.nd (BT.nd BT.lf [6,1,18,32,120,839] BT.lf) [6,1,18,36,120,126,833] BT.lf)) [6,1,18,36,120,833] (BT.nd (BT.nd (BT.nd BT.lf [6,1,18,38,120,420,833] BT.lf) [6,1,18,38,120,833] BT.lf) [6,1,18,70,120,420,833] (BT.nd (BT.nd BT.lf [6,1,18,120,122,420,839] BT.lf) [6,1,18,120,124,420,833] BT.lf)))) [6,1,18,120,126,190,420] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,18,120,126,420,833] BT.lf) [6,1,18,120,126,420,839] BT.lf) [6,1,18,120,126,420,851] (BT.nd (BT.nd BT.lf [6,1,18,120,126,420,889] BT.lf) [6,1,18,120,126,420,895] BT.lf)) [6,1,18,120,126,421,833] (BT.nd (BT.nd (BT.nd BT.lf [6,1,18,120,126,438,833] BT.lf) [6,1,18,120,126,603,833] BT.lf) [6,1,18,120,127,420,833] (BT.nd (BT.nd BT.lf [6,1,18,120,184,420] BT.lf) [6,1,18,120,260,420] BT.lf))) [6,1,18,120,262,420] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,18,120,416,833] BT.lf) [6,1,18,120,420,833,897] BT.lf) [6,1,18,120,420,837] (BT.nd (BT.nd BT.lf [6,1,18,120,420,839] BT.lf) [6,1,18,120,420,839,889] BT.lf)) [6,1,18,120,420,855] (BT.nd (BT.nd (BT.nd BT.lf [6,1,18,120,420,889,895] BT.lf) [6,1,18,120,420,889,1017] BT.lf) [6,1,18,120,420,895] (BT.nd (BT.nd BT.lf [6,1,18,120,421,839] BT.lf) [6,1,18,120,422,839] BT.lf))))) [6,1,18,120,438,839] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,18,120,603,839] BT.lf) [6,1,18,120,607,833] (BT.nd BT.lf [6,1,18,120,839,997] BT.lf)) [6,1,18,120,839,999] (BT.nd (BT.nd BT.lf [6,1,18,121,126,420,833] BT.lf) [6,1,18,121,127,420,833] BT.lf)) [6,1,18,121,420,839] (BT.nd (BT.nd (BT.nd BT.lf [6,1,18,122,420,839] BT.lf) [6,1,18,124,420,833] BT.lf) [6,1,18,126,420,508,833] (BT.nd (BT.nd BT.lf [6,1,18,126,420,833,903] BT.lf) [6,1,18,126,420,839] BT.lf))) [6,1,18,126,420,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,18,126,422,833] BT.lf) [6,1,18,420,839,903] BT.lf) [6,1,19,120,126,420,833] (BT.nd (BT.nd BT.lf [6,1,19,120,420,839] BT.lf) [6,1,22,64,120,420,833] BT.lf)) [6,1,22,120,120,420,833] (BT.nd (BT.nd (BT.nd BT.lf [6,1,22,120,121,420,833] BT.lf) [6,1,22,120,122,420,833] BT.lf) [6,1,22,120,126,420,833] (BT.nd (BT.nd BT.lf [6,1,22,120,190,420] BT.lf) [6,1,22,120,256,420] BT.lf)))) [6,1,22,120,420,508,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,22,120,420,833] BT.lf) [6,1,22,120,420,833,889] BT.lf) [6,1,22,120,420,833,903] (BT.nd (BT.nd BT.lf [6,1,22,120,420,839] BT.lf) [6,1,22,120,420,851] BT.lf)) [6,1,22,120,420,855] (BT.nd (BT.nd (BT.nd BT.lf [6,1,22,120,420,889] BT.lf) [6,1,22,120,421,833] BT.lf) [6,1,22,120,603,833] (BT.nd (BT.nd BT.lf [6,1,22,120,833,997] BT.lf) [6,1,22,121,420,833] BT.lf))) [6,1,22,420,833,903] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,23,120,420,833] BT.lf) [6,1,120,126,420,438,833] BT.lf) [6,1,120,126,420,833,851] (BT.nd (BT.nd BT.lf [6,1,120,126,420,833,1005] BT.lf) [6,1,120,420,438,839] BT.lf)) [6,1,120,420,833,855] (BT.nd (BT.nd (BT.nd BT.lf [6,1,120,420,833,1001] BT.lf) [6,1,120,420,839,1005] BT.lf) [6,4,18,120,121,420,833] (BT.nd (BT.nd BT.lf [6,4,18,121,420,833] BT.lf) [6,4,19,120,420,833] BT.lf))))))) [6,5,18,120,420,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,6,7,18,120,420,889] BT.lf) [6,6,16,120,121,420,833] (BT.nd BT.lf [6,6,16,121,420,833] BT.lf)) [6,6,17,120,420,833] (BT.nd (BT.nd BT.lf [6,6,18,19,32,120,833] BT.lf) [6,6,18,19,120,420,889] BT.lf)) [6,6,18,32,121,420,833] (BT.nd (BT.nd (BT.nd BT.lf [6,6,18,32,121,833] BT.lf) [6,6,18,33,120,420,833] BT.lf) [6,6,18,33,120,833] (BT.nd (BT.nd BT.lf [6,6,18,65,120,420,833] BT.lf) [6,6,18,65,121,420,833] BT.lf))) [6,6,18,120,121,190,420] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,6,18,120,121,420,833] BT.lf) [6,6,18,120,121,420,839] BT.lf) [6,6,18,120,121,420,851] (BT.nd (BT.nd BT.lf [6,6,18,120,121,420,889] BT.lf) [6,6,18,120,121,421,833] BT.lf)) [6,6,18,120,121,438,833] (BT.nd (BT.nd (BT.nd BT.lf [6,6,18,120,121,603,833] BT.lf) [6,6,18,120,123,420,833] BT.lf) [6,6,18,120,127,420,833] (BT.nd (BT.nd BT.lf [6,6,18,120,191,420] BT.lf) [6,6,18,120,256,421] BT.lf)))) [6,6,18,120,257,420] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,6,18,120,420,421,889] BT.lf) [6,6,18,120,420,509,833] (BT.nd BT.lf [6,6,18,120,420,832] BT.lf)) [6,6,18,120,420,833,902] (BT.nd (BT.nd BT.lf [6,6,18,120,420,889,1022] BT.lf) [6,6,18,121,121,420,833] BT.lf)) [6,6,18,121,122,420,833] (BT.nd (BT.nd (BT.nd BT.lf [6,6,18,121,123,420,833] BT.lf) [6,6,18,121,126,420,833] BT.lf) [6,6,18,121,127,420,833] (BT.nd (BT.nd BT.lf [6,6,18,121,190,420] BT.lf) [6,6,18,121,256,420] BT.lf))) [6,6,18,121,420,509,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,6,18,121,420,833] BT.lf) [6,6,18,121,420,833,889] BT.lf) [6,6,18,121,420,833,902] (BT.nd (BT.nd BT.lf [6,6,18,121,420,833,903] BT.lf) [6,6,18,121,420,839] BT.lf)) [6,6,18,121,420,851] (BT.nd (BT.nd (BT.nd BT.lf [6,6,18,121,420,889] BT.lf) [6,6,18,121,421,833] BT.lf) [6,6,18,121,422,833] (BT.nd (BT.nd BT.lf [6,6,18,121,438,833] BT.lf) [6,6,18,121,603,833] BT.lf))))) [6,6,18,121,833,997] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,6,18,123,420,833] BT.lf) [6,6,18,126,127,420,833] (BT.nd BT.lf [6,6,18,127,420,833] BT.lf)) [6,6,18,420,833,902] (BT.nd (BT.nd BT.lf [6,6,19,32,120,833] BT.lf) [6,6,19,120,121,420,833] BT.lf)) [6,6,19,120,123,420,833] (BT.nd (BT.nd (BT.nd BT.lf [6,6,19,120,190,420] BT.lf) [6,6,19,120,256,420] BT.lf) [6,6,19,120,420,833] (BT.nd (BT.nd BT.lf [6,6,19,120,420,839] BT.lf) [6,6,19,120,420,851] BT.lf))) [6,6,19,120,420,889] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,6,19,120,421,833] BT.lf) [6,6,19,120,422,833] BT.lf) [6,6,19,120,438,833] (BT.nd (BT.nd BT.lf [6,6,19,120,439,833] BT.lf) [6,6,19,120,603,833] BT.lf)) [6,6,19,120,833,997] (BT.nd (BT.nd (BT.nd BT.lf [6,6,19,121,420,833] BT.lf) [6,6,19,122,420,833] BT.lf) [6,6,19,123,420,833] (BT.nd (BT.nd BT.lf [6,6,19,126,420,833] BT.lf) [6,6,19,420,833,903] BT.lf)))) [6,6,22,120,121,420,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,6,22,121,420,833] BT.lf) [6,6,23,120,420,833] BT.lf) [6,6,120,121,420,438,833] (BT.nd (BT.nd BT.lf [6,6,120,121,420,833,851] BT.lf) [6,6,120,121,420,833,1005] BT.lf)) [6,6,120,420,439,833] (BT.nd (BT.nd (BT.nd BT.lf [6,6,120,420,833,1004] BT.lf) [6,6,120,421,438,833] BT.lf) [6,6,121,420,438,833] (BT.nd (BT.nd BT.lf [6,6,121,420,833,851] BT.lf) [6,6,121,420,833,1005] BT.lf))) [6,7,16,120,420,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,18,32,120,833] BT.lf) [6,7,18,120,121,420,833] BT.lf) [6,7,18,120,126,420,833] (BT.nd (BT.nd BT.lf [6,7,18,120,127,420,833] BT.lf) [6,7,18,120,190,420] BT.lf)) [6,7,18,120,256,420] (BT.nd (BT.nd (BT.nd BT.lf [6,7,18,120,420,833] BT.lf) [6,7,18,120,420,839] BT.lf) [6,7,18,120,420,851] (BT.nd (BT.nd BT.lf [6,7,18,120,420,889] BT.lf) [6,7,18,120,421,833] BT.lf)))))) [6,7,18,120,422,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,18,120,423,833] BT.lf) [6,7,18,120,438,833] (BT.nd BT.lf [6,7,18,120,603,833] BT.lf)) [6,7,18,120,833,997] (BT.nd (BT.nd BT.lf [6,7,18,121,420,833] BT.lf) [6,7,18,122,420,833] BT.lf)) [6,7,18,126,420,833] (BT.nd (BT.nd (BT.nd BT.lf [6,7,18,127,420,833] BT.lf) [6,7,18,420,833,903] BT.lf) [6,7,19,120,420,833] (BT.nd (BT.nd BT.lf [6,7,22,120,420,833] BT.lf) [6,7,23,120,420,833] BT.lf))) [6,7,120,420,438,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,7,120,420,833,851] BT.lf) [6,7,120,420,833,1005] BT.lf) [6,18,19,120,126,420,833] (BT.nd (BT.nd BT.lf [6,18,19,120,420,839] BT.lf) [6,18,22,120,121,420,833] BT.lf)) [6,18,22,121,420,833] (BT.nd (BT.nd (BT.nd BT.lf [6,18,23,120,420,833] BT.lf) [6,18,120,121,126,420,833] BT.lf) [6,18,120,121,127,420,833] (BT.nd (BT.nd BT.lf [6,18,120,121,420,833,839] BT.lf) [6,18,120,121,420,833,1017] BT.lf)))) [6,18,120,121,420,839] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,18,120,126,127,420,833] BT.lf) [6,18,120,126,420,421,833] BT.lf) [6,18,120,126,420,833,1022] (BT.nd (BT.nd BT.lf [6,18,120,127,420,833] BT.lf) [6,18,120,420,421,839] BT.lf)) [6,18,120,420,833,1016] (BT.nd (BT.nd (BT.nd BT.lf [6,18,120,420,839,1022] BT.lf) [6,18,121,126,420,833] BT.lf) [6,18,121,127,420,833] (BT.nd (BT.nd BT.lf [6,18,121,420,833,839] BT.lf) [6,18,121,420,833,1017] BT.lf))) [6,18,121,420,839] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,19,22,120,420,833] BT.lf) [6,19,23,120,420,833] BT.lf) [6,19,120,126,420,833] (BT.nd (BT.nd BT.lf [6,19,120,420,833,839] BT.lf) [6,19,120,420,833,1017] BT.lf)) [6,19,120,420,839] (BT.nd (BT.nd (BT.nd BT.lf [6,22,23,120,420,833] BT.lf) [6,22,120,121,420,833] BT.lf) [6,22,120,420,421,833] (BT.nd (BT.nd BT.lf [6,22,120,420,833,1022] BT.lf) [6,22,121,420,833] BT.lf))))) [6,23,120,420,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,1,4,18,120,420,833] BT.lf) [7,1,6,16,120,420,833] (BT.nd BT.lf [7,1,6,18,32,120,420,833] BT.lf)) [7,1,6,18,32,120,833] (BT.nd (BT.nd BT.lf [7,1,6,18,64,120,420,833] BT.lf) [7,1,6,18,120,120,420,833] BT.lf)) [7,1,6,18,120,121,420,833] (BT.nd (BT.nd (BT.nd BT.lf [7,1,6,18,120,122,420,833] BT.lf) [7,1,6,18,120,126,420,833] BT.lf) [7,1,6,18,120,190,420] (BT.nd (BT.nd BT.lf [7,1,6,18,120,256,420] BT.lf) [7,1,6,18,120,420,508,833] BT.lf))) [7,1,6,18,120,420,833] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,1,6,18,120,420,833,889] BT.lf) [7,1,6,18,120,420,833,903] BT.lf) [7,1,6,18,120,420,839] (BT.nd (BT.nd BT.lf [7,1,6,18,120,420,851] BT.lf) [7,1,6,18,120,420,889] BT.lf)) [7,1,6,18,120,421,833] (BT.nd (BT.nd (BT.nd BT.lf [7,1,6,18,120,422,833] BT.lf) [7,1,6,18,120,438,833] BT.lf) [7,1,6,18,120,603,833] (BT.nd (BT.nd BT.lf [7,1,6,18,120,833,997] BT.lf) [7,1,6,18,121,420,833] BT.lf)))) [7,1,6,18,122,420,833] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,1,6,18,126,420,833] BT.lf) [7,1,6,18,420,833,903] BT.lf) [7,1,6,19,120,420,833] (BT.nd (BT.nd BT.lf [7,1,6,22,120,420,833] BT.lf) [7,1,6,120,420,438,833] BT.lf)) [7,1,6,120,420,833,851] (BT.nd (BT.nd (BT.nd BT.lf [7,1,6,120,420,833,1005] BT.lf) [7,1,7,18,120,420,833] BT.lf) [7,1,18,22,120,420,833] (BT.nd (BT.nd BT.lf [7,1,18,120,126,420,833] BT.lf) [7,1,18,120,420,833,839] BT.lf))) [7,1,18,120,420,833,1017] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,1,18,120,420,839] BT.lf) [7,1,22,120,420,833] BT.lf) [7,6,7,18,120,420,833] (BT.nd (BT.nd BT.lf [7,6,18,19,120,420,833] BT.lf) [7,6,18,120,121,420,833] BT.lf)) [7,6,18,120,420,421,833] (BT.nd (BT.nd (BT.nd BT.lf [7,6,18,120,420,833,1022] BT.lf) [7,6,18,121,420,833] BT.lf) [7,6,19,120,420,833] (BT.nd (BT.nd BT.lf [7,7,18,120,420,833] BT.lf) [8,1,6,18,120,420,833] BT.lf)))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,6,306,509],[(56,9251)]),([3,18,294,509],[(56,9251)]),([3,48,121,837],[]),([3,48,123,839],[]),([3,52,121,833],[]),([3,52,125,833],[]),([3,52,127,833],[]),([3,103,851],[(0,2149),(2,100357),(4,2149),(6,102403)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([3,115,839],[(0,4195),(2,102403),(4,4195),(6,100357)]),([3,120,179],[(0,2149),(2,4195),(4,2149),(6,102403)]),([3,121,178],[(0,34821),(2,36867),(4,34821),(6,4131)]),([3,121,438,893],[]),([3,125,438,893],[]),([3,127,436,895],[]),([3,380,439],[(0,9315),(2,2154),(4,9315),(6,100362)]),([3,381,438],[(0,41987),(2,34826),(4,41987),(6,2090)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([4,1,6,306,508],[(56,107523),(72,107525),(80,107555)]),([4,1,18,294,508],[(56,107525),(72,107523),(80,107555)]),([4,1,48,120,837],[(56,2149)]),([4,1,48,122,839],[(56,2149)]),([4,1,52,120,833],[(56,2089)]),([4,1,52,124,833],[(56,8291)]),([4,1,52,126,833],[(56,8227)]),([4,1,102,851],[(0,34917),(2,34917),(4,34917),(6,100389),(8,34917),(10,102435),(57,34917),(58,34917),(74,34917),(77,34917)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,1,114,839],[(0,36963),(2,36963),(4,36963),(6,102435),(8,36963),(10,100389),(57,36963),(58,36963),(74,36963),(77,36963)]),([4,1,120,178],[(0,34917),(2,34917),(4,34917),(6,36963),(8,34917),(10,102435),(57,34917),(58,34917),(73,100389),(74,34917)]),([4,1,120,438,893],[]),([4,1,124,438,893],[]),([4,1,126,436,895],[]),([4,1,380,438],[(0,42083),(2,42083),(4,42083),(6,34922),(8,42083),(10,100394),(57,42083),(58,42083),(73,107555),(74,42083)]),([4,4,48,121,833],[]),([4,4,121,438,889],[(56,9251)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,6,18,288,509],[(56,9251)]),([4,6,48,123,833],[]),([4,6,50,121,851],[(56,35049),(96,2085)]),([4,6,50,121,883],[(56,35049),(96,2085)]),([4,6,97,851],[(0,5221),(2,100389),(4,5221),(6,103429),(8,5221),(10,102406),(57,5221),(58,5221)]),([4,6,105,420,889],[(56,4323)]),([4,6,115,833],[(0,4201),(2,100389),(4,4201),(6,102409),(8,4201),(10,106501),(73,36963),(74,4201)]),([4,6,120,306,421],[(72,9251)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([4,6,121,306,420],[(72,238627)]),([4,6,121,436,889],[(56,9443)]),([4,6,123,438,889],[]),([4,6,420,889,918],[]),([4,7,96,851],[(0,2149),(2,100357),(4,2149),(6,103621),(8,2149),(10,102403),(57,2149),(58,2149)]),([4,7,114,833],[(0,2153),(2,100361),(4,2153),(6,102435),(8,2153),(10,106499)]),([4,16,36,121,833],[]),([4,16,36,127,833],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([4,16,127,420,895],[]),([4,18,36,121,889],[]),([4,18,36,127,889],[]),([4,18,38,121,851],[(56,35049)]),([4,18,48,121,839],[(56,34917)]),([4,18,50,121,839],[(56,34917),(72,37091),(96,2085)]),([4,18,97,839],[(0,5219),(2,102435),(4,5219),(6,103427),(8,5219),(10,100358),(57,5219),(58,5219)]),([4,18,103,833],[(0,2153),(2,102435),(4,2153),(6,100361),(8,2153),(10,106499),(73,34917),(74,2153)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([4,18,120,161],[(0,2150),(2,102435),(4,2150),(6,5219),(8,2150),(10,103427),(73,34917),(74,2150)]),([4,18,120,294,421],[(72,9251)]),([4,18,121,160],[(0,231430),(2,4131),(4,231430),(6,36867),(8,231430),(10,5347),(73,34821),(74,231430)]),([4,18,121,292,889],[]),([4,18,121,294,420],[(72,238627)]),([4,18,121,420,893],[]),([4,18,121,863],[(0,5347),(2,4131),(4,5347),(6,36867),(8,5347),(10,231430),(74,5347),(77,5347)]),([4,18,125,420,893],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([4,18,380,421],[(0,9315),(2,102442),(4,9315),(6,2154),(8,9315),(10,100362),(73,42085),(74,9315)]),([4,18,381,420],[(0,238595),(2,4138),(4,238595),(6,36874),(8,238595),(10,2282),(73,41989),(74,238595)]),([4,19,48,120,839],[(56,2149)]),([4,19,50,120,839],[(56,2149),(72,37091)]),([4,19,51,120,839],[(56,2149),(72,4323),(96,198661)]),([4,19,96,839],[(0,4195),(2,102403),(4,4195),(6,103619),(8,4195),(10,100357),(57,4195),(58,4195)]),([4,19,102,833],[(0,4201),(2,102409),(4,4201),(6,100389),(8,4201),(10,106501)]),([4,19,120,160],[(0,231526),(2,102403),(4,231526),(6,4195),(8,231526),(10,103651),(73,2149),(74,231526)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([4,19,120,863],[(0,103651),(2,102403),(4,103651),(6,4195),(8,103651),(10,231526),(74,103651),(77,103651)]),([4,19,380,420],[(0,238691),(2,102410),(4,238691),(6,4202),(8,238691),(10,100586),(73,9317),(74,238691)]),([4,22,120,135,420],[]),([4,22,120,165],[(0,8227),(2,2089),(4,8227),(6,5225),(8,8227),(10,34825)]),([4,22,120,255,420],[]),([4,22,120,420,768],[]),([4,22,120,420,888],[]),([4,22,121,134,420],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([4,22,121,164],[(0,237574),(2,4137),(4,237574),(6,36873),(8,237574),(10,5353)]),([4,22,121,255,420],[(116,237574)]),([4,22,121,420,768],[]),([4,22,121,420,889],[]),([4,22,121,603,889],[]),([4,22,121,859],[(0,5353),(2,4137),(4,5353),(6,36873),(8,5353),(10,237574)]),([4,22,123,420,889],[]),([4,22,127,420,889],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([4,22,376,421],[(0,9251),(2,2090),(4,9251),(6,5226),(8,9251),(10,34826)]),([4,22,377,420],[(0,238598),(2,4138),(4,238598),(6,36874),(8,238598),(10,5354)]),([4,22,420,509,889],[(108,9251),(116,238598)]),([4,22,420,768,902],[]),([4,22,420,889,902],[]),([4,23,120,164],[(0,237571),(2,102409),(4,237571),(6,4201),(8,237571),(10,2281)]),([4,23,120,859],[(0,2281),(2,102409),(4,2281),(6,4201),(8,2281),(10,237571)]),([4,23,376,420],[(0,238595),(2,102410),(4,238595),(6,4202),(8,238595),(10,2282)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([4,50,51,120,839],[(56,2149),(72,37091),(80,37091),(96,198661)]),([4,50,121,839],[(0,34917),(2,102435),(4,34917),(6,34917),(8,34917),(10,34917),(58,37091),(74,2085),(82,2085),(85,36963)]),([4,51,120,839],[(0,2149),(2,102403),(4,2149),(6,2149),(8,2149),(10,2149),(58,4323),(74,198661),(82,100357),(85,4195)]),([4,111,420,833],[(0,233507),(2,231434),(4,233507),(6,35045),(8,233507),(10,233507),(74,233475),(81,233507),(86,233475)]),([4,120,121,438,837],[(56,9253)]),([4,120,123,438,839],[(56,37091)]),([4,120,123,439,839],[(56,4323),(84,2149)]),([4,120,260,439],[(0,9317),(2,4202),(4,9317),(6,9317),(8,9317),(10,102410),(57,9317),(58,9317),(82,9317),(85,9317)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([4,120,261,438],[(0,41987),(2,36970),(4,41987),(6,34826),(8,41987),(10,2090),(57,41987),(58,41987)]),([4,120,278,421],[(0,9251),(2,5226),(4,9251),(6,2090),(8,9251),(10,34826)]),([4,120,279,420],[(0,238595),(2,4202),(4,238595),(6,102410),(8,238595),(10,2282)]),([4,121,122,438,839],[(56,37091),(84,34917)]),([4,121,123,438,839],[(56,37091),(84,34917)]),([4,121,124,438,833],[(56,9251)]),([4,121,125,438,833],[(56,9251),(96,9251)]),([4,121,126,436,833],[(56,9443)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([4,121,127,436,833],[(56,9443),(96,9443)]),([4,121,260,438],[(0,41989),(2,36874),(4,41989),(6,41989),(8,41989),(10,4138),(57,41989),(58,41989),(82,41989),(85,41989)]),([4,121,278,420],[(0,238598),(2,36874),(4,238598),(6,4138),(8,238598),(10,5354)]),([4,121,420,889,1001],[]),([4,121,434,833],[(0,34917),(2,36874),(4,34917),(6,102435),(8,34917),(10,34917),(74,34821),(81,34917),(86,34821)]),([4,121,438,837],[(0,9253),(2,36874),(4,9253),(6,9253),(8,9253),(10,9253),(81,4131),(86,41989)]),([4,121,855,997],[(0,4131),(2,4131),(4,4131),(6,4131),(8,4131),(10,5221)]),([4,123,438,839],[(0,37091),(2,233482),(4,37091),(6,37091),(8,37091),(10,231461),(62,37091),(81,4323),(86,238597)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([4,123,439,839],[(0,4323),(2,233475),(4,4323),(6,4323),(8,4323),(10,231429),(62,4323),(81,4323),(86,238693)]),([4,124,125,438,833],[(56,9251)]),([4,125,438,833],[(0,9251),(2,34826),(4,9251),(6,9251),(8,9251),(10,9251),(81,2089),(86,41987)]),([4,126,127,436,833],[(56,9443)]),([4,127,436,833],[(0,9443),(2,231434),(4,9443),(6,9443),(8,9443),(10,9443),(81,2281),(86,238595)]),([4,127,438,509,833],[(76,9251),(84,9443),(96,9251)]),([5,1,4,48,120,833],[(56,2089),(72,8293)]),([5,1,4,120,438,889],[(56,9251),(80,107555)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([5,1,6,18,288,508],[(56,107523),(72,107525),(80,107555),(96,107526)]),([5,1,6,48,122,833],[(56,2281),(72,8293)]),([5,1,6,50,120,851],[(56,2281),(72,204805),(80,35049),(136,198693)]),([5,1,6,50,120,883],[(56,2281),(72,204805),(80,35049),(136,198693)]),([5,1,6,96,851],[(0,34917),(2,34917),(4,34917),(6,100389),(8,34917),(10,103621),(12,34917),(14,102435),(57,34917),(58,34917),(73,34917),(74,34917),(81,34917),(82,34917),(98,34917),(101,34917)]),([5,1,6,104,420,889],[(56,4323),(80,102627)]),([5,1,6,114,833],[(0,200809),(2,200809),(4,200809),(6,100389),(8,200809),(10,102435),(12,200809),(14,106693),(57,200809),(58,200809),(73,200809),(74,200809),(98,200809),(101,200809),(105,36963),(106,200809)]),([5,1,6,120,306,420],[(56,238595),(96,238601),(104,238627)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([5,1,6,120,436,889],[(56,9443),(80,107747)]),([5,1,6,122,438,889],[(56,9443)]),([5,1,6,420,889,919],[(56,4323)]),([5,1,16,36,120,833],[(56,8293),(72,2089)]),([5,1,16,36,126,833],[(56,8229),(72,8227)]),([5,1,16,126,420,895],[(56,41989)]),([5,1,18,36,120,889],[(56,106501),(72,2281)]),([5,1,18,36,126,889],[(56,106501),(72,106502)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([5,1,18,38,120,851],[(56,204805),(72,2281),(80,35049)]),([5,1,18,48,120,839],[(72,2150),(80,34917)]),([5,1,18,50,120,839],[(72,2150),(80,34917),(104,37091),(136,198693)]),([5,1,18,96,839],[(0,36963),(2,36963),(4,36963),(6,102435),(8,36963),(10,103619),(12,36963),(14,100389),(57,36963),(58,36963),(73,36963),(74,36963),(81,36963),(82,36963),(98,36963),(101,36963)]),([5,1,18,102,833],[(0,198761),(2,198761),(4,198761),(6,102435),(8,198761),(10,100389),(12,198761),(14,106691),(57,198761),(58,198761),(73,198761),(74,198761),(98,198761),(101,198761),(105,34917),(106,198761)]),([5,1,18,120,160],[(0,231526),(2,231526),(4,231526),(6,102435),(8,231526),(10,36963),(12,231526),(14,103651),(57,231526),(58,231526),(73,231526),(74,231526),(97,100389),(98,231526),(105,34917),(106,231526)]),([5,1,18,120,292,889],[(56,107525)]),([5,1,18,120,294,420],[(56,107525),(96,238595),(104,238627)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([5,1,18,120,420,893],[(56,107525)]),([5,1,18,120,863],[(0,103651),(2,103651),(4,103651),(6,102435),(8,103651),(10,36963),(12,103651),(14,231526),(57,103651),(58,103651),(73,103651),(74,103651),(98,103651),(101,103651),(106,103651),(109,103651)]),([5,1,18,124,420,893],[(56,107525)]),([5,1,18,380,420],[(0,238691),(2,238691),(4,238691),(6,102442),(8,238691),(10,36970),(12,238691),(14,100586),(57,238691),(58,238691),(73,238691),(74,238691),(97,107557),(98,238691),(105,42085),(106,238691)]),([5,1,22,120,134,420],[(56,107525)]),([5,1,22,120,164],[(0,237603),(2,237603),(4,237603),(6,102441),(8,237603),(10,36969),(12,237603),(14,35049),(57,237603),(58,237603),(73,237603),(74,237603),(97,106533),(98,237603)]),([5,1,22,120,254,420],[(56,9317),(72,9253),(156,237603)]),([5,1,22,120,420,769],[(56,9317),(72,9253)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,1,22,120,420,889],[(56,107525)]),([5,1,22,120,421,889],[(56,2281)]),([5,1,22,120,603,889],[(56,107525)]),([5,1,22,120,859],[(0,35049),(2,35049),(4,35049),(6,102441),(8,35049),(10,36969),(12,35049),(14,237603),(57,35049),(58,35049),(73,35049),(74,35049),(98,35049),(101,35049)]),([5,1,22,121,420,889],[]),([5,1,22,122,420,889],[(56,107525)]),([5,1,22,126,420,889],[(56,107525)]),([5,1,22,376,420],[(0,238627),(2,238627),(4,238627),(6,102442),(8,238627),(10,36970),(12,238627),(14,35050),(57,238627),(58,238627),(73,238627),(74,238627),(97,107557),(98,238627)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,1,22,420,508,889],[(56,107525),(72,107526),(148,107555),(156,238627)]),([5,1,22,420,769,903],[(56,9317)]),([5,1,22,420,889,903],[(56,4202)]),([5,1,23,120,420,889],[(56,107525),(96,2281),(128,107525)]),([5,1,50,120,839],[(0,34917),(2,34917),(4,34917),(6,102435),(8,34917),(10,34917),(12,34917),(14,34917),(58,34917),(73,34917),(74,34917),(82,37091),(98,34917),(101,34917),(106,198693),(114,100389),(117,36963)]),([5,1,110,420,833],[(0,233507),(2,233507),(4,233507),(6,231461),(8,233507),(10,35045),(12,233507),(14,233507),(57,233507),(58,233507),(73,37091),(74,233507),(98,233507),(101,233507),(106,233507),(113,233507),(118,233507)]),([5,1,120,122,438,839],[(80,37091),(116,34917)]),([5,1,120,124,438,833],[(72,9251),(80,205859),(136,107555)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,1,120,126,436,833],[(72,9443),(80,206051),(136,107747)]),([5,1,120,260,438],[(0,42085),(2,42085),(4,42085),(6,36970),(8,42085),(10,42085),(12,42085),(14,102442),(57,42085),(58,42085),(73,42085),(74,42085),(81,42085),(82,42085),(97,107557),(98,42085),(114,42085),(117,42085)]),([5,1,120,278,420],[(0,238627),(2,238627),(4,238627),(6,36970),(8,238627),(10,102442),(12,238627),(14,35050),(57,238627),(58,238627),(73,238627),(74,238627),(97,42085),(98,238627)]),([5,1,120,420,889,1001],[]),([5,1,120,434,833],[(0,34917),(2,34917),(4,34917),(6,36963),(8,34917),(10,102435),(12,34917),(14,34917),(57,34917),(58,34917),(73,100389),(74,34917),(98,34917),(101,34917),(106,34917),(113,34917),(118,34917)]),([5,1,120,438,837],[(0,205861),(2,205861),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(58,205861),(73,205861),(74,205861),(98,205861),(101,205861),(113,200739),(118,42085)]),([5,1,120,855,997],[(0,200739),(2,200739),(4,200739),(6,200739),(8,200739),(10,200739),(12,200739),(14,201829),(57,200739),(58,200739),(74,200739),(77,200739),(98,200739),(101,200739)]),([5,1,122,438,839],[(0,37091),(2,37091),(4,37091),(6,233507),(8,37091),(10,37091),(12,37091),(14,231461),(57,37091),(58,37091),(73,37091),(74,37091),(86,37091),(98,37091),(101,37091),(113,37091),(118,238693)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,1,124,438,833],[(0,205859),(2,205859),(4,205859),(6,35018),(8,205859),(10,205859),(12,205859),(14,205859),(58,205859),(73,205859),(74,205859),(98,205859),(101,205859),(113,198697),(118,42083)]),([5,1,126,436,833],[(0,206051),(2,206051),(4,206051),(6,231626),(8,206051),(10,206051),(12,206051),(14,206051),(58,206051),(73,206051),(74,206051),(98,206051),(101,206051),(113,198889),(118,238627)]),([5,1,126,438,508,833],[(56,9443),(72,9315),(96,9251),(108,205859),(116,206051),(136,107555)]),([5,4,18,121,420,889],[(72,9443)]),([5,4,120,121,438,833],[(72,9251),(80,9253)]),([5,4,121,438,833],[(0,9253),(2,9253),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(58,9253),(74,9253),(77,9253),(97,9253),(98,9253),(113,4137),(118,41989)]),([5,5,120,438,833],[(0,205861),(2,34826),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(57,9251),(58,205861),(74,2089),(86,2089),(98,205861),(106,9251),(113,2089),(118,41987)]),([5,6,16,121,420,889],[(72,9443)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,6,18,32,121,851],[(56,35049),(128,2085)]),([5,6,18,36,121,833],[(56,8229),(72,34917),(128,41061)]),([5,6,18,36,127,833],[(72,36963),(128,37097)]),([5,6,18,48,121,833],[(72,8229),(80,34917),(136,35049)]),([5,6,18,50,121,833],[(56,8229),(72,8229),(80,34917),(104,37091)]),([5,6,18,97,833],[(0,5225),(2,100389),(4,5225),(6,102435),(8,5225),(10,103433),(12,5225),(14,106502),(73,5225),(74,5225),(81,5225),(82,5225),(97,36963),(98,5225),(105,34917),(106,5225)]),([5,6,18,120,135,420],[(72,107747),(104,9317)]),([5,6,18,120,165],[(0,8294),(2,8294),(4,8294),(6,8294),(8,8294),(10,5225),(12,8294),(14,103433),(57,8294),(58,8227),(73,8294),(74,8294),(82,8294),(85,8227),(98,8294),(101,8294),(105,106502),(106,8294)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([5,6,18,120,255,420],[(148,34821)]),([5,6,18,120,288,421],[(56,9251),(112,9318)]),([5,6,18,120,420,768],[(116,34821),(128,42085),(136,42211)]),([5,6,18,120,420,888],[(72,107747),(128,107557)]),([5,6,18,121,134,420],[(72,9443),(104,237573)]),([5,6,18,121,164],[(0,237574),(2,237574),(4,237574),(6,237574),(8,237574),(10,234505),(12,237574),(14,5353),(57,237574),(58,237574),(73,237574),(74,237574),(82,237574),(85,237574),(98,237574),(101,237574),(105,8422),(106,237574)]),([5,6,18,121,255,420],[(148,34821),(156,237574)]),([5,6,18,121,288,420],[(56,238627),(112,238598)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([5,6,18,121,420,768],[(116,34821),(128,41989),(136,42211)]),([5,6,18,121,420,865],[(56,9253),(128,42085)]),([5,6,18,121,420,889],[(72,9443),(128,9253)]),([5,6,18,121,420,891],[(56,9253),(104,35049),(128,9253)]),([5,6,18,121,420,895],[(56,9253),(96,34821),(128,9253)]),([5,6,18,121,438,889],[(72,9443),(128,9253),(136,35049)]),([5,6,18,121,603,889],[(72,9443),(96,5347),(116,34821),(128,9253)]),([5,6,18,121,859],[(0,5353),(2,5353),(4,5353),(6,5353),(8,5353),(10,234505),(12,5353),(14,237574),(57,5353),(58,5353),(73,5353),(74,5353),(82,5353),(85,5353),(97,8229),(98,5353),(106,5353),(109,5353)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([5,6,18,123,420,889],[(72,9443)]),([5,6,18,127,420,889],[(72,9443),(96,9443)]),([5,6,18,127,420,895],[(96,36867)]),([5,6,18,376,421],[(0,9318),(2,9318),(4,9318),(6,9318),(8,9318),(10,5226),(12,9318),(14,103434),(57,9318),(58,9251),(73,9318),(74,9318),(82,9318),(85,9251),(98,9318),(101,9318),(105,107526),(106,9318)]),([5,6,18,377,420],[(0,238598),(2,238598),(4,238598),(6,238598),(8,238598),(10,234506),(12,238598),(14,5354),(57,238598),(58,238598),(73,238598),(74,238598),(82,238598),(85,238598),(98,238598),(101,238598),(105,9446),(106,238598)]),([5,6,18,420,509,889],[(80,9251),(128,9253),(156,238598)]),([5,6,18,420,768,902],[(96,41989),(104,42211),(136,234501)]),([5,6,18,420,889,902],[(96,36874),(144,34821)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([5,6,19,48,120,833],[(72,204837),(80,8293)]),([5,6,19,50,120,833],[(56,2281),(72,204837),(80,8293),(104,37091)]),([5,6,19,51,120,833],[(56,204837),(72,204837),(80,8293),(104,4329),(136,204805)]),([5,6,19,96,833],[(0,4201),(2,100389),(4,4201),(6,102409),(8,4201),(10,103625),(12,4201),(14,106501),(73,4201),(74,4201),(81,4201),(82,4201),(97,36963),(98,4201)]),([5,6,19,120,164],[(0,237670),(2,237670),(4,237670),(6,102409),(8,237670),(10,4201),(12,237670),(14,103657),(57,237670),(58,237603),(73,237670),(74,237670),(98,237670),(101,237670),(105,8293),(106,237670)]),([5,6,19,120,438,889],[(72,107747),(128,107557)]),([5,6,19,120,859],[(0,103657),(2,103657),(4,103657),(6,102409),(8,103657),(10,4201),(12,103657),(14,237670),(57,103657),(58,35049),(73,103657),(74,103657),(97,106501),(98,103657),(106,103657),(109,103657)]),([5,6,19,376,420],[(0,238694),(2,238694),(4,238694),(6,102410),(8,238694),(10,4202),(12,238694),(14,103658),(57,238694),(58,238627),(73,238694),(74,238694),(98,238694),(101,238694),(105,9317),(106,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([5,6,22,121,420,889],[(128,9253)]),([5,6,48,121,420,833],[(56,9253),(72,9443),(104,9445)]),([5,6,50,51,120,833],[(56,204837),(72,2281),(80,8293),(104,8293),(112,37091),(136,204805)]),([5,6,50,121,420,833],[(56,9253),(100,8229),(128,42085)]),([5,6,50,121,833],[(0,34917),(2,34917),(4,34917),(6,102435),(8,34917),(10,34917),(12,34917),(14,34917),(57,8229),(73,100389),(74,34917),(82,37091),(97,34917),(98,34917),(105,34917),(114,34821),(117,34917)]),([5,6,51,120,833],[(0,8293),(2,8293),(4,8293),(6,102409),(8,8293),(10,8293),(12,8293),(14,8293),(57,204837),(73,100389),(74,8293),(82,4329),(97,8293),(98,8293),(106,204805),(114,106501),(117,4201)]),([5,6,105,120,420,833],[(56,9443)]),([5,6,105,121,420,833],[(56,102627),(84,233507),(136,4329)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([5,6,105,420,833],[(0,233507),(2,231461),(4,233507),(6,234506),(8,233507),(10,35045),(12,233507),(14,233507),(57,233507),(58,233507),(97,37091),(98,233507),(106,233478),(113,233507),(118,233478)]),([5,6,120,121,436,833],[(72,9443),(80,9445)]),([5,6,120,123,438,833],[(80,9445)]),([5,6,120,123,439,833],[(80,4329),(116,8293)]),([5,6,120,274,421],[(0,9318),(2,9318),(4,9318),(6,5226),(8,9318),(10,9318),(12,9318),(14,103434),(57,9318),(58,9318),(73,9257),(74,9251),(81,9318),(98,9318),(101,9257),(114,9318)]),([5,6,120,275,420],[(0,238601),(2,238601),(4,238601),(6,4202),(8,238601),(10,102410),(12,238601),(14,8426),(57,238601),(58,238601),(73,238601),(74,238601),(98,238601),(101,238601)]),([5,6,120,420,833,918],[]),([5,6,121,122,438,833],[(80,9445),(116,34917),(144,35049)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([5,6,121,123,438,833],[(80,9445),(116,34917),(144,35049)]),([5,6,121,274,420],[(0,238598),(2,238598),(4,238598),(6,234506),(8,238598),(10,238598),(12,238598),(14,5354),(57,238598),(58,238598),(73,238598),(74,238598),(81,238598),(98,238598),(101,238598),(114,238598)]),([5,6,121,420,438,889],[(56,9443),(80,9251),(128,41989),(156,238627)]),([5,6,121,420,833,918],[]),([5,6,121,420,889,1005],[(56,9443),(96,4138),(156,4329)]),([5,6,121,436,833],[(0,9445),(2,9445),(4,9445),(6,233482),(8,9445),(10,9445),(12,9445),(14,9445),(58,9445),(77,9445),(97,9445),(98,9445),(113,4329),(118,238597)]),([5,6,121,438,509,833],[(100,9253),(116,9445),(128,42085),(136,9251)]),([5,6,121,438,851],[(0,35049),(2,231465),(4,35049),(6,234506),(8,35049),(10,35049),(12,35049),(14,237603),(57,35049),(58,35049),(74,35049),(77,35049),(86,35049),(106,35049),(118,238598)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([5,6,121,851,997],[(0,4198),(2,4198),(4,4198),(6,4198),(8,4198),(10,4198),(12,4198),(14,5221),(57,4198),(58,4198),(73,4137),(74,4131),(98,4198),(101,4137),(109,5221),(110,5221)]),([5,6,123,438,833],[(0,9445),(2,231461),(4,9445),(6,233482),(8,9445),(10,9445),(12,9445),(14,9445),(74,9445),(77,9445),(86,37091),(97,37091),(98,9445),(106,37091),(113,4329),(118,238597)]),([5,6,123,439,833],[(0,4329),(2,231461),(4,4329),(6,233481),(8,4329),(10,4329),(12,4329),(14,237573),(74,4329),(77,4329),(86,4329),(97,37091),(98,4329),(113,4329),(118,238693)]),([5,6,420,833,902,918],[(100,234506),(116,234501),(152,234506)]),([5,6,420,833,918],[(0,234506),(2,231461),(4,234506),(6,234506),(8,234506),(10,234506),(12,234506),(14,233507),(73,234506),(74,234506),(81,233507),(86,234501),(98,234506),(101,234506),(117,234501)]),([5,7,18,36,120,833],[(56,204837),(72,2281)]),([5,7,18,36,126,833],[(72,8291)]),([5,7,18,36,127,833],[(72,2281),(128,37097)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,18,96,833],[(0,2153),(2,100361),(4,2153),(6,102435),(8,2153),(10,103625),(12,2153),(14,106499),(73,2153),(74,2153),(81,2153),(82,2153),(105,34917),(106,2153)]),([5,7,18,120,164],[(0,237571),(2,231433),(4,237571),(6,237571),(8,237571),(10,234601),(12,237571),(14,2281),(57,237571),(58,237571),(73,237571),(74,237571),(82,237571),(85,237571),(105,106726),(106,237571)]),([5,7,18,120,420,895],[(56,107525)]),([5,7,18,120,859],[(0,2281),(2,231433),(4,2281),(6,2281),(8,2281),(10,234601),(12,2281),(14,237571),(57,2281),(58,2281),(73,2281),(74,2281),(82,2281),(85,2281),(106,2281),(109,2281)]),([5,7,18,121,420,889],[(72,9443),(128,9253)]),([5,7,18,126,420,889],[(56,107525),(72,9443)]),([5,7,18,126,420,895],[]),([5,7,18,127,420,889],[(72,9443)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,18,127,420,895],[]),([5,7,18,376,420],[(0,238595),(2,231434),(4,238595),(6,238595),(8,238595),(10,234602),(12,238595),(14,2282),(57,238595),(58,238595),(73,238595),(74,238595),(82,238595),(85,238595),(105,107750),(106,238595)]),([5,7,19,120,420,889],[(56,107525),(128,107525)]),([5,7,22,120,420,889],[(56,107525)]),([5,7,23,120,420,889],[(56,107525),(128,107525)]),([5,7,50,120,833],[(0,2281),(2,231433),(4,2281),(6,102435),(8,2281),(10,2281),(12,2281),(14,237571),(57,2281),(73,2281),(74,2281),(82,2281),(105,34917),(106,2281),(114,2281),(117,2153)]),([5,7,104,420,833],[(0,233507),(2,231434),(4,233507),(6,234597),(8,233507),(10,35045),(12,233507),(14,233507),(57,233507),(58,233507),(98,233475),(106,233507),(113,233507),(118,233475)]),([5,7,120,274,420],[(0,238595),(2,231434),(4,238595),(6,234602),(8,238595),(10,238595),(12,238595),(14,2282),(57,238595),(58,238595),(73,238595),(74,238595),(81,238595),(114,238595)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([5,7,120,436,833],[(0,206053),(2,231434),(4,206053),(6,233674),(8,206053),(10,206053),(12,206053),(14,206053),(57,9443),(58,206053),(98,206053),(106,9443),(113,2281),(118,238595)]),([5,7,120,438,851],[(0,35049),(2,231434),(4,35049),(6,234698),(8,35049),(10,35049),(12,35049),(14,237603),(57,35049),(58,35049),(74,2281),(86,2281),(106,35049),(118,238595)]),([5,7,120,851,997],[(0,200806),(2,231433),(4,200806),(6,200806),(8,200806),(10,200806),(12,200806),(14,2149),(57,200806),(58,200806),(98,200806),(101,200745),(109,2149),(110,2149)]),([5,7,122,438,833],[(0,35045),(2,231434),(4,35045),(6,233507),(8,35045),(10,35045),(12,35045),(14,35045),(74,2281),(86,2281),(98,35045),(106,9443),(113,2281),(118,238595)]),([5,7,420,833,919],[(0,234597),(2,231434),(4,234597),(6,234597),(8,234597),(10,234597),(12,234597),(14,233507),(74,234597),(81,233507),(86,234597),(98,234597),(101,234597),(117,234597)]),([5,16,121,126,420,833],[(80,9443)]),([5,16,121,127,420,833],[(60,9443),(80,9443),(136,9443)]),([5,16,126,127,420,833],[(60,9443),(80,9443)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([5,16,127,420,833],[(0,9443),(2,9443),(4,9443),(6,231434),(8,9443),(10,9443),(12,9443),(14,9443),(58,9443),(61,9443),(73,9443),(74,9443),(97,9443),(98,9443),(113,2281),(118,238595)]),([5,17,126,420,833],[(0,206051),(2,36874),(4,206051),(6,231626),(8,206051),(10,206051),(12,206051),(14,206051),(58,4329),(73,9253),(74,206051),(86,8229),(98,205829),(106,41989),(113,198889),(118,238627)]),([5,18,19,32,120,839],[(56,2149),(80,2150),(96,37091),(104,37091),(128,198661)]),([5,18,19,38,120,833],[(56,8293),(72,204837),(80,2281),(96,36966),(104,36966),(128,204805)]),([5,18,22,121,420,889],[(80,9443),(128,9253),(136,9253)]),([5,18,32,121,839],[(0,34917),(2,102435),(4,34917),(6,34917),(8,34917),(10,34917),(12,34917),(14,34917),(57,34917),(74,37091),(82,34917),(85,34917),(98,2085),(105,34917),(106,34917),(114,2085),(117,36963)]),([5,18,33,120,839],[(0,2150),(2,102435),(4,2150),(6,103427),(8,2150),(10,2150),(12,2150),(14,2150),(57,34917),(58,2150),(74,37091),(82,5347),(98,198693),(106,198662),(114,100358),(117,5219)]),([5,18,36,120,121,833],[(112,8229)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,36,120,127,833],[]),([5,18,36,121,127,833],[(100,8229),(108,8229),(116,8229),(152,8229)]),([5,18,36,121,833],[(0,8229),(2,8229),(4,8229),(6,8229),(8,8229),(10,36873),(12,8229),(14,8229),(57,8229),(58,8229),(82,8229),(97,4137),(98,8229),(105,8229),(106,8229)]),([5,18,37,120,833],[(0,2281),(2,2281),(4,2281),(6,103433),(8,2281),(10,37065),(12,2281),(14,237571),(57,2281),(58,2281),(77,2089),(82,2281),(97,200745),(98,2281),(114,2281)]),([5,18,38,121,420,833],[(56,9253),(108,8229),(136,42085)]),([5,18,38,121,833],[(0,34917),(2,102435),(4,34917),(6,34917),(8,34917),(10,34917),(12,34917),(14,34917),(58,8229),(74,36966),(82,36963),(97,34917),(105,34917),(106,34917),(114,34821),(117,36963)]),([5,18,39,120,833],[(0,2281),(2,102435),(4,2281),(6,103433),(8,2281),(10,2281),(12,2281),(14,237571),(58,2281),(74,2281),(82,2281),(97,34917),(98,2281),(114,2281),(117,2153)]),([5,18,71,121,420,833],[(56,4329),(116,2153),(128,4323),(136,9446)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,120,121,420,837],[(60,9446),(80,9253),(108,2085)]),([5,18,120,121,438,839],[(80,9446),(136,9253)]),([5,18,120,123,420,839],[(60,9446),(80,37091),(108,37091)]),([5,18,120,126,191,420],[(60,206051),(148,204837)]),([5,18,120,126,420,832],[(60,206051),(116,204837),(136,107747),(144,107557)]),([5,18,120,127,420,839],[(60,9446),(80,37097)]),([5,18,120,127,420,895],[]),([5,18,120,185,420],[(0,206054),(2,102442),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,9253),(74,205861),(82,42085),(97,42085),(98,206054),(110,34917),(118,198886)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,120,260,421],[(0,9318),(2,102442),(4,9318),(6,5226),(8,9318),(10,9318),(12,9318),(14,103434),(73,9318),(74,9318),(81,9318),(82,9318),(97,42085),(98,9318),(114,9318),(117,9318)]),([5,18,120,261,420],[(0,238595),(2,102442),(4,238595),(6,36970),(8,238595),(10,231434),(12,238595),(14,2282),(73,238595),(74,238595),(81,238595),(82,238595),(97,42085),(98,238595)]),([5,18,120,262,421],[(0,9318),(2,9318),(4,9318),(6,5226),(8,9318),(10,9318),(12,9318),(14,103434),(58,9318),(61,9251),(73,9251),(74,9318),(81,9318),(82,9318),(97,107526),(98,9318),(114,9318),(117,9318)]),([5,18,120,263,420],[(0,238595),(2,238595),(4,238595),(6,234602),(8,238595),(10,231434),(12,238595),(14,2282),(58,238595),(61,238595),(73,238595),(74,238595),(81,238595),(82,238595),(97,9443),(98,238595)]),([5,18,120,420,838],[(0,206054),(2,102442),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,36874),(73,42085),(74,206054),(86,34917),(98,205861),(106,107557),(113,201955)]),([5,18,121,122,420,839],[(76,9446),(80,37091),(116,34917),(144,9253)]),([5,18,121,123,420,839],[(60,9446),(76,9446),(80,37091),(84,9446),(108,37091),(116,34917),(144,9253)]),([5,18,121,124,420,833],[(80,9253),(116,8229)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,121,125,420,833],[(60,9443),(80,9253),(116,8229),(136,9443)]),([5,18,121,126,420,839],[(76,9446),(80,37097),(116,41061),(144,9253)]),([5,18,121,126,420,889],[(80,9443),(144,9253)]),([5,18,121,127,190,420],[(60,9443),(148,8229),(156,237574)]),([5,18,121,127,420,833],[(60,9443),(116,8229),(136,9443),(144,9253)]),([5,18,121,127,420,839],[(60,9446),(76,9446),(80,37097),(84,9446),(116,41061),(144,9253)]),([5,18,121,127,420,851],[(60,9443),(96,35049),(116,8229),(144,9253)]),([5,18,121,127,420,889],[(60,9443),(80,9443),(108,2085),(136,9443),(144,9253)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,121,127,420,895],[(76,9253),(84,9253),(116,8229),(144,9253)]),([5,18,121,127,438,833],[(116,8229),(128,35049),(136,9443),(144,9253)]),([5,18,121,127,603,833],[(60,9443),(108,100389),(136,9443),(144,9253),(152,5353)]),([5,18,121,184,420],[(0,9446),(2,102442),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(58,231461),(74,9253),(82,41989),(97,42085),(98,9446),(110,34917),(117,9253),(118,2278)]),([5,18,121,260,420],[(0,238598),(2,4138),(4,238598),(6,36874),(8,238598),(10,238598),(12,238598),(14,5354),(73,238598),(74,238598),(81,238598),(82,238598),(97,41989),(98,238598),(114,238598),(117,238598)]),([5,18,121,262,420],[(0,238598),(2,238598),(4,238598),(6,234506),(8,238598),(10,238598),(12,238598),(14,5354),(58,238598),(61,238598),(73,238598),(74,238598),(81,238598),(82,238598),(97,9446),(98,238598),(114,238598),(117,238598)]),([5,18,121,416,833],[(0,231526),(2,102435),(4,231526),(6,36874),(8,231526),(10,103651),(12,231526),(14,231526),(73,34917),(74,231526),(97,34917),(98,231526),(106,231430),(113,231526),(118,231430)]),([5,18,121,420,833,896],[(60,231434),(104,231434),(128,231525)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,121,420,837],[(0,9253),(2,9253),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(61,9446),(73,9253),(74,9253),(86,2085),(97,4138),(98,9253),(113,5347),(118,238598)]),([5,18,121,420,839],[(0,9446),(2,102442),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(58,37091),(73,42085),(74,9446),(86,34917),(98,9253),(106,9253),(113,5347),(118,238598)]),([5,18,121,420,839,889],[(140,9446),(148,34917),(152,9253)]),([5,18,121,420,855],[(0,9253),(2,4138),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(73,41989),(74,9253),(86,2085),(98,9253),(101,9253),(106,9253),(113,5347),(118,238598)]),([5,18,121,420,889,895],[(108,9253),(116,2085),(152,9253)]),([5,18,121,420,889,1017],[(148,231430)]),([5,18,121,420,895],[(0,9253),(2,4138),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(73,41989),(74,9253),(81,9253),(86,2085),(98,9253),(101,9253),(106,9253),(109,9253),(117,9253),(118,9253)]),([5,18,121,421,839],[(0,5347),(2,102442),(4,5347),(6,234499),(8,5347),(10,5347),(12,5347),(14,231430),(58,5347),(73,5347),(74,5347),(86,5347),(98,5347),(113,5347),(118,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,121,422,839],[(0,9446),(2,102435),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(58,9446),(74,9446),(86,34917),(98,9446),(106,34821),(113,5347),(118,238598)]),([5,18,121,438,839],[(0,9446),(2,9446),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(58,37091),(74,9446),(77,9446),(98,9253),(101,9445),(106,9253),(113,5347),(118,238598)]),([5,18,121,603,839],[(0,9446),(2,102442),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(58,37091),(74,9446),(77,9446),(86,34917),(98,9253),(106,9253),(113,2278),(114,9253)]),([5,18,121,607,833],[(0,103651),(2,102435),(4,103651),(6,36874),(8,103651),(10,231526),(12,103651),(14,103651),(74,103651),(77,103651),(97,34917),(98,103651),(106,5347),(113,103651),(114,2085)]),([5,18,121,839,997],[(0,5347),(2,5347),(4,5347),(6,234499),(8,5347),(10,231430),(12,5347),(14,5347),(58,5347),(61,5347),(73,2278),(74,5347),(97,5347),(98,5347),(109,5347),(110,5347),(114,5347),(117,5347)]),([5,18,121,839,999],[(0,5347),(2,102435),(4,5347),(6,234499),(8,5347),(10,231430),(12,5347),(14,5347),(58,5347),(74,5347),(98,5347),(109,5347),(110,5347),(114,5347),(117,5347)]),([5,18,123,420,839],[(0,37091),(2,37091),(4,37091),(6,234506),(8,37091),(10,37091),(12,37091),(14,231461),(58,37091),(61,37091),(73,37091),(74,37091),(86,37091),(97,9446),(113,5347)]),([5,18,124,125,420,833],[(60,9443),(80,9253),(108,8229)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,125,420,833],[(0,9253),(2,9253),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(61,9443),(73,9253),(74,9253),(86,8229),(97,4138),(98,9253),(113,2281),(118,238595)]),([5,18,126,127,420,889],[(60,9443),(80,9443)]),([5,18,127,420,509,833],[(100,9443),(108,9253),(136,9253)]),([5,18,127,420,833,902],[(84,36873),(104,36874),(144,36963)]),([5,18,127,420,839],[(0,37097),(2,37097),(4,37097),(6,234506),(8,37097),(10,37097),(12,37097),(14,237605),(58,37097),(61,37097),(73,37097),(74,37097),(86,37097),(97,9446)]),([5,18,127,420,889],[(0,9443),(2,9443),(4,9443),(6,231434),(8,9443),(10,9443),(12,9443),(14,9443),(58,9443),(61,9443),(73,9443),(74,9443),(101,9443),(117,2085)]),([5,18,127,422,833],[(0,36963),(2,102435),(4,36963),(6,231434),(8,36963),(10,100389),(12,36963),(14,36963),(58,36963),(61,36963),(86,36963),(97,34917),(98,36963),(106,36867),(113,36963),(118,36867)]),([5,18,127,423,833],[(0,2281),(2,102435),(4,2281),(6,231433),(8,2281),(10,2281),(12,2281),(14,36963),(58,2281),(61,2281),(86,2281),(97,34917),(98,2281),(113,36963),(118,36963)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([5,18,420,839,902],[(0,234506),(2,102442),(4,234506),(6,234506),(8,234506),(10,234506),(12,234506),(14,9446),(57,234506),(58,234506),(74,36874),(81,234499),(86,36874),(98,234506),(105,34917),(117,41989)]),([5,19,22,120,420,889],[(56,107525),(80,107525),(136,107525)]),([5,19,32,120,839],[(0,2149),(2,102403),(4,2149),(6,2149),(8,2149),(10,2149),(12,2149),(14,2149),(57,2149),(74,4323),(82,2149),(85,2149),(98,198661),(105,2149),(106,2149),(114,100357),(117,4195)]),([5,19,36,120,833],[(0,204837),(2,102409),(4,204837),(6,204837),(8,204837),(10,37065),(12,204837),(14,204837),(57,204837),(58,204837),(82,204837),(98,204805),(105,204837),(106,204837),(114,106501)]),([5,19,38,120,833],[(0,8293),(2,102409),(4,8293),(6,8293),(8,8293),(10,8293),(12,8293),(14,8293),(58,204837),(74,4329),(82,36963),(98,204805),(105,8293),(106,8293),(114,106501),(117,4201)]),([5,19,120,123,420,839],[(60,9446),(76,206054),(80,4323),(84,206054),(108,4323),(116,2149),(144,107525)]),([5,19,120,126,438,833],[(116,204837),(136,107747),(144,107557)]),([5,19,120,126,439,833],[(116,204837),(136,107525),(144,107525)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([5,19,120,127,420,833],[(60,9443),(116,204837),(144,107525)]),([5,19,120,184,420],[(0,206054),(2,102410),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,231429),(74,205829),(82,9317),(97,9317),(98,206054),(110,2149),(117,107525),(118,198886)]),([5,19,120,260,420],[(0,238694),(2,102410),(4,238694),(6,4202),(8,238694),(10,238694),(12,238694),(14,103658),(73,238694),(74,238694),(81,238694),(82,238694),(97,9317),(98,238694),(114,238694),(117,238694)]),([5,19,120,262,420],[(0,238694),(2,102410),(4,238694),(6,4202),(8,238694),(10,238694),(12,238694),(14,103658),(73,238627),(74,238694),(81,238694),(82,238694),(97,9317),(98,238694),(114,238694),(117,238694)]),([5,19,120,416,833],[(0,231526),(2,102410),(4,231526),(6,36963),(8,231526),(10,103651),(12,231526),(14,231526),(73,9317),(74,231526),(98,231526),(106,231526),(113,231526),(118,231526)]),([5,19,120,420,837],[(0,205861),(2,102410),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(73,9317),(74,205861),(86,198693),(98,205829),(106,107525),(113,201955),(118,238694)]),([5,19,120,420,839],[(0,206054),(2,102410),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,4323),(73,9317),(74,206054),(86,2149),(98,205829),(106,107525),(113,201955),(118,238694)]),([5,19,120,420,855],[(0,205829),(2,200714),(4,205829),(6,4298),(8,205829),(10,205829),(12,205829),(14,205829),(73,9413),(74,205829),(86,198661),(98,205829),(101,205829),(106,107525),(113,201955),(118,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([5,19,120,420,895],[(0,107525),(2,102410),(4,107525),(6,4202),(8,107525),(10,107525),(12,107525),(14,107525),(73,9317),(74,107525),(81,107525),(86,100357),(98,107525),(101,107525),(106,107525),(109,107525),(117,107525),(118,107525)]),([5,19,120,421,839],[(0,206054),(2,102403),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,37091),(74,206054),(86,2149),(98,205861),(106,107557),(113,201955),(118,238694)]),([5,19,120,422,839],[(0,206054),(2,102410),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,4323),(74,206054),(86,2149),(98,205829),(106,107525),(113,201955),(118,238694)]),([5,19,120,438,839],[(0,206054),(2,206054),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,37091),(74,206054),(98,205861),(101,206053),(106,107557),(113,201955),(118,238694)]),([5,19,120,439,839],[(0,206054),(2,206054),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,4323),(74,206054),(77,206054),(98,205829),(101,206053),(106,107525),(113,201955),(118,238694)]),([5,19,120,603,839],[(0,206054),(2,102410),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,4323),(74,206054),(77,206054),(86,2149),(98,205829),(106,107525),(113,198886),(114,107525)]),([5,19,120,607,833],[(0,103651),(2,102410),(4,103651),(6,36963),(8,103651),(10,231526),(12,103651),(14,103651),(74,103651),(77,103651),(98,103651),(106,103651),(113,103651),(114,100357)]),([5,19,120,839,997],[(0,201955),(2,102403),(4,201955),(6,234691),(8,201955),(10,231622),(12,201955),(14,201955),(58,37091),(74,201955),(98,201955),(109,37091),(110,201955),(114,201955),(117,201955)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([5,19,120,839,999],[(0,201955),(2,102403),(4,201955),(6,234691),(8,201955),(10,231622),(12,201955),(14,201955),(58,201955),(74,201955),(98,201955),(109,201955),(110,201955),(114,201955),(117,201955)]),([5,19,121,126,420,833],[(60,206051),(116,4329),(136,107525)]),([5,19,121,420,839],[(0,4323),(2,102442),(4,4323),(6,234698),(8,4323),(10,4323),(12,4323),(14,231429),(58,4323),(73,4323),(74,4323),(86,4323),(113,201955)]),([5,19,122,420,839],[(0,37091),(2,102410),(4,37091),(6,234698),(8,37091),(10,37091),(12,37091),(14,231461),(58,4323),(73,37091),(74,37091),(86,37091),(113,201955)]),([5,19,123,420,839],[(0,4323),(2,4323),(4,4323),(6,234698),(8,4323),(10,4323),(12,4323),(14,231429),(58,4323),(61,4323),(73,4323),(74,4323),(86,4323),(97,9446),(113,201955)]),([5,19,124,420,833],[(0,205861),(2,102410),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(73,9317),(74,205861),(86,204837),(98,205829),(106,107525),(113,198889),(118,238691)]),([5,19,126,420,839],[(0,37097),(2,102410),(4,37097),(6,234698),(8,37097),(10,37097),(12,37097),(14,237605),(58,4329),(73,37097),(74,37097),(86,37097)]),([5,19,126,420,889],[(0,107525),(2,102410),(4,107525),(6,4202),(8,107525),(10,107525),(12,107525),(14,107525),(73,9317),(74,107525),(86,106501),(101,107525),(117,100389)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([5,19,126,422,833],[(0,36963),(2,102410),(4,36963),(6,231626),(8,36963),(10,100389),(12,36963),(14,36963),(58,4329),(86,36963),(98,36963),(106,36963),(113,36963),(118,36963)]),([5,19,420,839,903],[(0,234698),(2,102410),(4,234698),(6,234698),(8,234698),(10,234698),(12,234698),(14,206054),(57,234698),(58,234698),(74,4298),(81,234691),(86,4202),(98,234698),(105,2149),(117,9317)]),([5,22,23,120,420,889],[(56,107525),(72,107525),(128,107525)]),([5,22,65,120,420,833],[(56,200937),(80,9253)]),([5,22,65,121,420,833],[(56,4329),(80,9253),(104,5353),(136,9253)]),([5,22,120,121,190,420],[(80,9253),(104,9253),(156,237603)]),([5,22,120,121,420,833],[(80,9253)]),([5,22,120,121,420,889],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([5,22,120,121,421,833],[(80,5353)]),([5,22,120,121,603,833],[(80,9253),(152,35049)]),([5,22,120,123,420,833],[]),([5,22,120,127,420,833],[(60,9443)]),([5,22,120,191,420],[(0,205861),(2,205861),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(74,205861),(77,205861),(118,204837)]),([5,22,120,256,421],[(0,9251),(2,2090),(4,9251),(6,5226),(8,9251),(10,9251),(12,9251),(14,34826),(73,9251),(74,9251),(81,9251),(82,9251),(114,9251),(117,9251)]),([5,22,120,257,420],[(0,238601),(2,102442),(4,238601),(6,36970),(8,238601),(10,237578),(12,238601),(14,8426),(73,238601),(74,238601),(81,238601),(82,238601)]),([5,22,120,420,421,889],[(80,107526),(148,9251),(156,238601)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([5,22,120,420,509,833],[(156,238601)]),([5,22,120,420,832],[(0,205861),(2,205861),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(97,200746),(98,205861),(113,201961)]),([5,22,120,420,833,902],[]),([5,22,120,420,889,1022],[]),([5,22,121,121,420,833],[(64,9253),(68,9253)]),([5,22,121,123,420,833],[(84,9253),(144,9253)]),([5,22,121,127,420,833],[(60,9443),(76,9253),(84,9253),(116,8229),(144,9253)]),([5,22,121,190,420],[(0,9253),(2,9253),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(74,9253),(77,9253),(117,9253),(118,8229)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([5,22,121,256,420],[(0,238598),(2,4138),(4,238598),(6,36874),(8,238598),(10,238598),(12,238598),(14,5354),(73,238598),(74,238598),(81,238598),(82,238598),(114,238598),(117,238598)]),([5,22,121,420,509,833],[(100,9446),(108,9253),(116,9253),(156,238627)]),([5,22,121,420,833],[(0,9253),(2,9253),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(97,4138),(98,9253),(113,5353),(118,238598)]),([5,22,121,420,833,889],[(140,9253),(156,9253)]),([5,22,121,420,833,902],[]),([5,22,121,420,833,903],[(156,9253)]),([5,22,121,420,839],[(0,9446),(2,102442),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(58,37097),(73,42085),(98,9253),(106,9253),(118,238598)]),([5,22,121,420,851],[(0,9253),(2,4138),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(74,35049),(86,35049),(98,9253),(106,9253),(113,5353),(118,238598)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([5,22,121,420,855],[(0,9253),(2,4138),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(73,41989),(98,9253),(101,9253),(106,9253),(118,238598)]),([5,22,121,420,889],[(98,9253),(118,238627)]),([5,22,121,421,833],[(0,5353),(2,5353),(4,5353),(6,36873),(8,5353),(10,5353),(12,5353),(14,237574),(97,200746),(98,5353),(113,5353),(118,238627)]),([5,22,121,603,833],[(0,9253),(2,9253),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(97,4138),(98,9253),(113,8229),(114,9253)]),([5,22,121,833,997],[(0,5353),(2,5353),(4,5353),(6,36873),(8,5353),(10,237574),(12,5353),(14,5353),(73,8229),(74,5353),(114,5353),(117,5353)]),([5,22,420,833,902],[(0,36874),(2,36874),(4,36874),(6,36874),(8,36874),(10,36874),(12,36874),(14,9253),(73,36874),(74,36874),(81,36873),(86,36874)]),([5,23,120,121,420,833],[(80,4329),(84,205861),(144,107525)]),([5,23,120,123,420,833],[(84,205861),(144,107525)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_54 : List (List ℕ × List (ℕ × ℕ)) := [([5,23,120,127,420,833],[(60,9443),(76,205861),(84,205861),(116,204837),(144,107525)]),([5,23,120,190,420],[(0,205861),(2,102410),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(74,205829),(82,9317),(117,107525),(118,204837)]),([5,23,120,256,420],[(0,238595),(2,102410),(4,238595),(6,4202),(8,238595),(10,238595),(12,238595),(14,2282),(73,238595),(74,238595),(81,238595),(82,238595),(114,238595),(117,238595)]),([5,23,120,420,833],[(0,205861),(2,102410),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(98,205829),(106,107525),(113,2281),(118,238595)]),([5,23,120,420,839],[(0,206054),(2,102410),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(58,4329),(73,9317),(98,205829),(106,107525),(118,238694)]),([5,23,120,420,851],[(0,205829),(2,200714),(4,205829),(6,4298),(8,205829),(10,205829),(12,205829),(14,205829),(74,2281),(86,2281),(98,205829),(106,107525),(113,2281),(118,238595)]),([5,23,120,420,855],[(0,205829),(2,200714),(4,205829),(6,4298),(8,205829),(10,205829),(12,205829),(14,205829),(73,9413),(98,205829),(101,205829),(106,107525),(118,238694)]),([5,23,120,420,889],[(0,107525),(2,102410),(4,107525),(6,4202),(8,107525),(10,107525),(12,107525),(14,107525),(81,107525),(98,107525),(106,107525),(109,107525),(118,238595)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_54 : K_54.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_55 : List (List ℕ × List (ℕ × ℕ)) := [([5,23,120,421,833],[(0,2281),(2,102409),(4,2281),(6,37066),(8,2281),(10,2281),(12,2281),(14,237571),(106,2281),(113,2281),(118,238627)]),([5,23,120,603,833],[(0,205861),(2,102410),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(98,205829),(106,107525),(113,204837),(114,107525)]),([5,23,120,833,997],[(0,2281),(2,102409),(4,2281),(6,37065),(8,2281),(10,237571),(12,2281),(14,2281),(114,2281),(117,2281)]),([5,23,121,420,833],[(0,4329),(2,4329),(4,4329),(6,37066),(8,4329),(10,4329),(12,4329),(14,237573),(97,4138),(113,201961)]),([5,23,420,833,903],[(0,37066),(2,102410),(4,37066),(6,37066),(8,37066),(10,37066),(12,37066),(14,205861),(74,4298),(81,37065),(86,4202),(117,9317)]),([5,120,121,420,833,1001],[(56,9253)]),([5,120,420,439,839],[(0,9317),(2,234698),(4,9317),(6,9317),(8,9317),(10,102410),(12,9317),(14,9317),(58,9317),(82,9317),(85,9317),(98,9317),(109,9317),(110,9317),(118,107750)]),([5,120,420,833,1000],[(0,102410),(2,102410),(4,102410),(6,102410),(8,102410),(10,102410),(12,102410),(14,205861),(74,102410),(81,102409),(86,102410),(117,205829)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_55 : K_55.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_56 : List (List ℕ × List (ℕ × ℕ)) := [([5,120,420,839,1004],[(0,102410),(2,102410),(4,102410),(6,102410),(8,102410),(10,102410),(12,102410),(14,206054),(62,102403),(74,102410),(81,102403),(86,102410),(101,4323),(106,102410),(109,102410),(117,205829)]),([5,120,421,438,839],[(0,41987),(2,234698),(4,41987),(6,34826),(8,41987),(10,2090),(12,41987),(14,41987),(58,9251),(98,41987),(109,41987),(110,41987),(118,9251)]),([5,121,127,420,438,833],[(84,9253),(100,9443),(108,9253),(128,9443),(136,41989)]),([5,121,127,420,833,851],[(84,4137),(112,4198),(132,4329)]),([5,121,127,420,833,1005],[(84,8229),(96,9443),(104,4138),(140,102627)]),([5,121,420,438,839],[(0,42085),(2,234506),(4,42085),(6,42085),(8,42085),(10,102442),(12,42085),(14,42085),(58,42085),(82,42085),(85,42085),(98,41989),(109,42085),(110,41989),(118,9446)]),([5,121,420,833,855],[(0,4138),(2,36874),(4,4138),(6,4138),(8,4138),(10,41989),(12,4138),(14,4138),(81,8229),(82,4138),(114,4138),(117,4138)]),([5,121,420,833,1001],[(0,9253),(2,36874),(4,9253),(6,9253),(8,9253),(10,9253),(12,9253),(14,9253),(81,5353),(86,4138),(114,9253),(117,9253)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_56 : K_56.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_57 : List (List ℕ × List (ℕ × ℕ)) := [([5,121,420,839,1005],[(0,102442),(2,102442),(4,102442),(6,102442),(8,102442),(10,102442),(12,102442),(14,9446),(62,102435),(74,4138),(81,102435),(86,4138),(101,37091),(106,102442),(109,102442),(117,9253)]),([6,1,4,18,120,420,889],[(56,9443),(72,107525),(104,107747)]),([6,1,4,120,438,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(74,205861),(82,205861),(97,205861),(98,205861),(106,205861),(109,205861),(130,205861),(133,205861),(137,205861),(138,205861),(153,200745),(158,42085)]),([6,1,6,16,120,420,889],[(56,9443),(72,107525),(104,107747)]),([6,1,6,18,32,120,851],[(56,2281),(72,204805),(80,35049),(96,8294),(176,198693)]),([6,1,6,18,36,120,833],[(72,8293),(80,204837),(96,8294),(104,34917),(176,41061)]),([6,1,6,18,36,126,833],[(72,8293),(96,8294),(104,36963),(176,37097)]),([6,1,6,18,48,120,833],[(56,2281),(96,8294),(104,204837),(112,34917),(184,35049)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_57 : K_57.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_58 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,6,18,50,120,833],[(56,2281),(80,204837),(96,8294),(104,204837),(112,34917),(144,37091)]),([6,1,6,18,96,833],[(0,201833),(2,201833),(4,201833),(6,100389),(8,201833),(10,102435),(12,201833),(14,103625),(16,201833),(18,106694),(57,201833),(58,201833),(73,201833),(74,201833),(97,201833),(98,201833),(105,201833),(106,201833),(113,201833),(114,201833),(130,201833),(133,201833),(137,36963),(138,201833),(145,34917),(146,201833)]),([6,1,6,18,120,134,420],[(56,9443),(72,107525),(104,107747),(144,237669)]),([6,1,6,18,120,164],[(0,237670),(2,237670),(4,237670),(6,237670),(8,237670),(10,237670),(12,237670),(14,234601),(16,237670),(18,103657),(57,237670),(58,237670),(73,237670),(74,237670),(81,237670),(82,237603),(97,237670),(98,237670),(105,237670),(106,237670),(114,237670),(117,237603),(129,106726),(130,237670),(138,237670),(141,237670),(145,106726),(146,237670)]),([6,1,6,18,120,254,420],[(56,9443),(72,9317),(96,9446),(196,34917),(204,237670)]),([6,1,6,18,120,288,420],[(56,238595),(72,107525),(80,238627),(128,238601),(152,238694)]),([6,1,6,18,120,420,769],[(56,9443),(72,9317),(96,9446),(156,34917),(176,42085),(184,42211)]),([6,1,6,18,120,420,865],[(56,9443),(72,9317),(80,205861),(176,42085)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_58 : K_58.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_59 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,6,18,120,420,889],[(56,9443),(72,107525),(104,107747),(176,107557)]),([6,1,6,18,120,420,891],[(56,9443),(72,107525),(80,107557),(144,35049),(176,107557)]),([6,1,6,18,120,420,895],[(72,107525),(80,107557),(136,34917),(176,107557)]),([6,1,6,18,120,421,889],[(56,2281),(72,8293),(104,107747),(176,107557)]),([6,1,6,18,120,438,889],[(56,9443),(104,107747),(176,107557),(184,35049)]),([6,1,6,18,120,603,889],[(56,9443),(72,107525),(104,107747),(136,103651),(156,34917),(176,107557)]),([6,1,6,18,120,859],[(0,103657),(2,103657),(4,103657),(6,103657),(8,103657),(10,103657),(12,103657),(14,234601),(16,103657),(18,237670),(57,103657),(58,103657),(73,103657),(74,103657),(81,103657),(82,35049),(97,103657),(98,103657),(105,103657),(106,103657),(114,103657),(117,35049),(130,103657),(133,103657),(137,106533),(138,103657),(146,103657),(149,103657)]),([6,1,6,18,121,420,889],[(104,107747),(176,107557)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_59 : K_59.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_60 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,6,18,122,420,889],[(56,9443),(72,107525),(104,107747)]),([6,1,6,18,126,420,889],[(72,107525),(104,107747),(136,107747)]),([6,1,6,18,126,420,895],[(72,107525),(136,36963)]),([6,1,6,18,376,420],[(0,238694),(2,238694),(4,238694),(6,238694),(8,238694),(10,238694),(12,238694),(14,234602),(16,238694),(18,103658),(57,238694),(58,238694),(73,238694),(74,238694),(81,238694),(82,238627),(97,238694),(98,238694),(105,238694),(106,238694),(114,238694),(117,238627),(129,107750),(130,238694),(138,238694),(141,238694),(145,107750),(146,238694)]),([6,1,6,18,420,508,889],[(56,9443),(72,107525),(96,107526),(112,107555),(176,107557),(204,238694)]),([6,1,6,18,420,769,903],[(56,9443),(72,9317),(136,42085),(144,42211),(184,234597)]),([6,1,6,18,420,889,903],[(56,9443),(72,4202),(136,36970),(192,34917)]),([6,1,6,19,120,420,889],[(72,107525),(104,107747),(128,8293),(168,107525),(176,107557)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_60 : K_60.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_61 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,6,22,120,420,889],[(72,107525),(176,107557)]),([6,1,6,48,120,420,833],[(56,9443),(72,9317),(80,205861),(104,206051),(144,206053)]),([6,1,6,50,120,420,833],[(56,9443),(72,9317),(80,205861),(140,204837),(176,42085)]),([6,1,6,50,120,833],[(0,34917),(2,34917),(4,34917),(6,34917),(8,34917),(10,102435),(12,34917),(14,34917),(16,34917),(18,34917),(57,34917),(58,34917),(74,34917),(81,204837),(97,34917),(98,34917),(105,100389),(106,34917),(114,37091),(130,34917),(133,34917),(137,34917),(138,34917),(145,34917),(154,34917),(157,34917)]),([6,1,6,104,120,420,833],[(56,9443),(80,102627),(96,4329),(116,233507),(184,102633)]),([6,1,6,104,420,833],[(0,233507),(2,233507),(4,233507),(6,231461),(8,233507),(10,234597),(12,233507),(14,35045),(16,233507),(18,233507),(57,233507),(58,233507),(73,233507),(74,233507),(81,233507),(82,233507),(97,102630),(98,233507),(130,233507),(133,233507),(137,37091),(138,233507),(146,233507),(153,233507),(158,233507)]),([6,1,6,120,122,438,833],[(56,9443),(112,35045),(156,34917),(192,35049)]),([6,1,6,120,274,420],[(0,238694),(2,238694),(4,238694),(6,238694),(8,238694),(10,234602),(12,238694),(14,238694),(16,238694),(18,103658),(57,238694),(58,238694),(73,238694),(74,238694),(81,238694),(82,238694),(97,238694),(98,238694),(105,238633),(106,238627),(113,238694),(129,107750),(130,238694),(138,238694),(141,238633),(154,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_61 : K_61.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_62 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,6,120,420,438,889],[(56,9443),(80,107747),(96,9251),(112,107555),(128,9317),(176,42085),(204,238627)]),([6,1,6,120,420,833,919],[(56,9443),(72,4329)]),([6,1,6,120,420,889,1005],[(56,9443),(80,107747),(136,102442),(204,102633)]),([6,1,6,120,436,833],[(0,206053),(2,206053),(4,206053),(6,206053),(8,206053),(10,233674),(12,206053),(14,206053),(16,206053),(18,206053),(57,206053),(58,206053),(74,206053),(82,206053),(97,206053),(98,206053),(109,206053),(130,206053),(133,206053),(137,206053),(138,206053),(153,200937),(158,238627)]),([6,1,6,120,438,508,833],[(56,9443),(72,9445),(96,9317),(128,9251),(140,205861),(156,206053),(176,42085),(184,107555)]),([6,1,6,120,438,851],[(0,35049),(2,35049),(4,35049),(6,231465),(8,35049),(10,234698),(12,35049),(14,35049),(16,35049),(18,237603),(57,35049),(58,35049),(73,35049),(74,35049),(81,35049),(82,35049),(97,35049),(98,35049),(106,35049),(109,35049),(118,35049),(130,35049),(133,35049),(146,35049),(158,238694)]),([6,1,6,120,851,997],[(0,200806),(2,200806),(4,200806),(6,200806),(8,200806),(10,200806),(12,200806),(14,200806),(16,200806),(18,201829),(57,200806),(58,200806),(73,200806),(74,200806),(81,200806),(82,200806),(98,200806),(101,200806),(105,200745),(106,200739),(130,200806),(133,200806),(138,200806),(141,200745),(149,201829),(150,34917)]),([6,1,6,122,438,833],[(0,35045),(2,35045),(4,35045),(6,231461),(8,35045),(10,233507),(12,35045),(14,35045),(16,35045),(18,35045),(57,35045),(58,35045),(73,37091),(74,35045),(97,35045),(98,35045),(106,35045),(109,35045),(118,37091),(130,35045),(133,35045),(137,37091),(138,35045),(146,37091),(153,200937),(158,238693)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_62 : K_62.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_63 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,6,420,833,903,919],[(56,9443),(132,234597),(140,234597),(156,234597),(200,234597)]),([6,1,6,420,833,919],[(0,234597),(2,234597),(4,234597),(6,231461),(8,234597),(10,234597),(12,234597),(14,234597),(16,234597),(18,233507),(57,234597),(58,234597),(73,234597),(74,234597),(98,234597),(101,234597),(105,234597),(106,234597),(113,233507),(118,234597),(130,234597),(133,234597),(138,234597),(141,234597),(157,234597)]),([6,1,7,18,120,420,889],[(56,9443),(104,107747),(128,2281),(168,9443),(176,107557)]),([6,1,16,120,126,420,833],[(56,9317),(84,206051),(96,9443),(112,206051),(184,107747)]),([6,1,16,126,420,833],[(0,206051),(2,206051),(4,206051),(6,206051),(8,206051),(10,231626),(12,206051),(14,206051),(16,206051),(18,206051),(57,206051),(58,206051),(74,206051),(82,206051),(85,206051),(97,206051),(98,206051),(105,206051),(106,206051),(130,206051),(133,206051),(137,206051),(138,206051),(153,198889),(158,238627)]),([6,1,18,22,120,420,889],[(72,9443),(112,107747),(176,107557),(184,107557)]),([6,1,18,32,120,839],[(0,34917),(2,34917),(4,34917),(6,102435),(8,34917),(10,34917),(12,34917),(14,34917),(16,34917),(18,34917),(58,34917),(73,34917),(74,34917),(81,34917),(97,34917),(98,34917),(106,37091),(114,34917),(117,34917),(130,34917),(133,34917),(138,198693),(145,34917),(146,34917),(154,100389),(157,36963)]),([6,1,18,36,120,126,833],[(56,8293),(72,8294),(96,8229),(140,204837),(148,204837),(156,204837),(200,106533)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_63 : K_63.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_64 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,18,36,120,833],[(0,204837),(2,204837),(4,204837),(6,204837),(8,204837),(10,204837),(12,204837),(14,37065),(16,204837),(18,204837),(57,204837),(58,204837),(73,204837),(74,204837),(81,204837),(82,204837),(98,204837),(114,204837),(130,204837),(133,204837),(137,200745),(138,204837),(145,204837),(146,204837)]),([6,1,18,38,120,420,833],[(56,9317),(72,9443),(80,205861),(148,204837),(184,42085)]),([6,1,18,38,120,833],[(0,34917),(2,34917),(4,34917),(6,102435),(8,34917),(10,34917),(12,34917),(14,34917),(16,34917),(18,34917),(58,34917),(73,34917),(74,34917),(82,204837),(97,34917),(98,34917),(106,36966),(114,36963),(130,34917),(133,34917),(137,34917),(145,34917),(146,34917),(154,34917),(157,36963)]),([6,1,18,70,120,420,833],[(56,9317),(72,9443),(80,200937),(96,9446),(156,198761),(176,42211),(184,206054)]),([6,1,18,120,122,420,839],[(56,9317),(84,42214),(108,206054),(112,37091),(116,206054),(148,37091),(156,34917),(192,107557)]),([6,1,18,120,124,420,833],[(56,9317),(84,206051),(96,9443),(112,205861),(156,204837),(184,107747)]),([6,1,18,120,126,190,420],[(56,9317),(72,9253),(84,206051),(96,9443),(196,204837),(204,237670)]),([6,1,18,120,126,420,833],[(56,9317),(72,9253),(84,206051),(96,9443),(156,204837),(184,107747),(192,107557)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_64 : K_64.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_65 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,18,120,126,420,839],[(56,9317),(84,42214),(108,206054),(112,37097),(116,206054),(156,41061),(192,107557)]),([6,1,18,120,126,420,851],[(56,9413),(72,9253),(84,42211),(96,9443),(136,35049),(156,204837),(192,107557)]),([6,1,18,120,126,420,889],[(56,9317),(84,107747),(96,9443),(112,107747),(148,100389),(184,107747),(192,107557)]),([6,1,18,120,126,420,895],[(56,9317),(72,9253),(108,107557),(116,107557),(156,106533),(192,107557)]),([6,1,18,120,126,421,833],[(56,8293),(72,8229),(84,206051),(96,2281),(156,204837),(184,107747),(192,107557)]),([6,1,18,120,126,438,833],[(72,9253),(96,9443),(156,204837),(176,35049),(184,107747),(192,107557)]),([6,1,18,120,126,603,833],[(56,9317),(72,9253),(84,206051),(96,9443),(148,100389),(184,107747),(192,107557),(200,103657)]),([6,1,18,120,127,420,833],[(84,206051),(96,9443),(128,2281),(156,204837),(168,9443),(184,107747),(192,107557)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_65 : K_65.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_66 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,18,120,184,420],[(0,206054),(2,206054),(4,206054),(6,102442),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(73,42085),(74,206054),(82,231461),(97,206054),(98,206054),(106,205861),(114,42085),(129,206054),(130,206054),(137,42085),(138,206054),(150,34917),(157,107557),(158,198886)]),([6,1,18,120,260,420],[(0,238694),(2,238694),(4,238694),(6,102442),(8,238694),(10,36970),(12,238694),(14,238694),(16,238694),(18,103658),(57,238694),(58,238694),(73,238694),(74,238694),(97,238694),(98,238694),(105,238694),(106,238694),(113,238694),(114,238694),(129,107557),(130,238694),(137,42085),(138,238694),(154,238694),(157,238694)]),([6,1,18,120,262,420],[(0,238694),(2,238694),(4,238694),(6,238694),(8,238694),(10,234602),(12,238694),(14,238694),(16,238694),(18,103658),(57,238694),(58,238694),(73,238694),(74,238694),(82,238694),(85,238627),(97,238694),(98,238694),(105,238627),(106,238694),(113,238694),(114,238694),(129,107750),(130,238694),(137,107750),(138,238694),(154,238694),(157,238694)]),([6,1,18,120,416,833],[(0,231526),(2,231526),(4,231526),(6,102435),(8,231526),(10,36963),(12,231526),(14,103651),(16,231526),(18,231526),(57,231526),(58,231526),(73,231526),(74,231526),(97,100389),(98,231526),(105,34917),(106,231526),(130,231526),(133,231526),(137,34917),(138,231526),(146,231526),(153,231526),(158,231526)]),([6,1,18,120,420,833,897],[(56,9317),(72,9253),(84,231626),(144,231530),(176,231525)]),([6,1,18,120,420,837],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(74,205861),(85,206054),(97,205861),(98,205861),(105,205861),(106,205861),(118,198693),(130,205861),(133,205861),(137,200746),(138,205861),(153,201955),(158,238694)]),([6,1,18,120,420,839],[(0,206054),(2,206054),(4,206054),(6,102442),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(73,42085),(74,206054),(82,37091),(97,206054),(98,206054),(105,42085),(106,206054),(118,34917),(130,206054),(133,206054),(138,205861),(146,107557),(153,201955),(158,238694)]),([6,1,18,120,420,839,889],[(56,9317),(172,206054),(188,206054),(196,34917),(200,107557)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_66 : K_66.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_67 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,18,120,420,855],[(0,205861),(2,205861),(4,205861),(6,200746),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(73,42181),(74,205861),(97,205861),(98,205861),(105,42181),(106,205861),(118,198693),(130,205861),(133,205861),(138,205861),(141,205861),(146,107557),(153,201955),(158,238694)]),([6,1,18,120,420,889,895],[(56,107525),(132,107557),(148,107557),(156,100389),(200,107557)]),([6,1,18,120,420,889,1017],[(56,107525),(196,231526)]),([6,1,18,120,420,895],[(0,107557),(2,107557),(4,107557),(6,102442),(8,107557),(10,36970),(12,107557),(14,107557),(16,107557),(18,107557),(57,107557),(58,107557),(73,42085),(74,107557),(97,107557),(98,107557),(105,42085),(106,107557),(113,107557),(118,100389),(130,107557),(133,107557),(138,107557),(141,107557),(146,107557),(149,107557),(157,107557),(158,107557)]),([6,1,18,120,421,839],[(0,206054),(2,206054),(4,206054),(6,102442),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(73,42085),(74,206054),(82,37091),(98,206054),(101,206054),(105,42085),(106,206054),(118,34917),(130,206054),(133,206054),(138,205861),(146,107557),(153,201955),(158,238694)]),([6,1,18,120,422,839],[(0,206054),(2,206054),(4,206054),(6,102435),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(73,34917),(74,206054),(82,206054),(97,206054),(98,206054),(106,206054),(118,34917),(130,206054),(133,206054),(138,206054),(146,34917),(153,201955),(158,238694)]),([6,1,18,120,438,839],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(74,206054),(82,37091),(97,206054),(98,206054),(106,206054),(109,206054),(130,206054),(133,206054),(138,205861),(141,206053),(146,107557),(153,201955),(158,238694)]),([6,1,18,120,603,839],[(0,206054),(2,206054),(4,206054),(6,102442),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(73,42085),(74,206054),(82,37091),(98,206054),(101,206054),(106,206054),(109,206054),(118,34917),(130,206054),(133,206054),(138,205861),(146,107557),(153,198886),(154,107557)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_67 : K_67.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_68 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,18,120,607,833],[(0,103651),(2,103651),(4,103651),(6,102435),(8,103651),(10,36963),(12,103651),(14,231526),(16,103651),(18,103651),(57,103651),(58,103651),(73,103651),(74,103651),(98,103651),(101,103651),(106,103651),(109,103651),(130,103651),(133,103651),(137,34917),(138,103651),(146,103651),(153,103651),(154,100389)]),([6,1,18,120,839,997],[(0,201955),(2,201955),(4,201955),(6,201955),(8,201955),(10,234691),(12,201955),(14,231622),(16,201955),(18,201955),(57,201955),(58,201955),(73,201955),(74,201955),(82,37091),(85,201955),(98,201955),(101,201955),(105,198886),(106,201955),(130,201955),(133,201955),(137,201955),(138,201955),(149,37091),(150,201955),(154,201955),(157,201955)]),([6,1,18,120,839,999],[(0,201955),(2,201955),(4,201955),(6,102435),(8,201955),(10,234691),(12,201955),(14,231622),(16,201955),(18,201955),(57,201955),(58,201955),(73,201955),(74,201955),(82,201955),(98,201955),(101,201955),(106,201955),(130,201955),(133,201955),(138,201955),(149,201955),(150,201955),(154,201955),(157,201955)]),([6,1,18,121,126,420,833],[(72,9253),(84,206051),(128,8229),(156,204837),(168,9253),(184,107747),(192,107557)]),([6,1,18,121,127,420,833],[(56,4329),(84,206051),(128,5353),(156,204837),(184,107747),(192,107557)]),([6,1,18,121,420,839],[(0,206054),(2,206054),(4,206054),(6,102442),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(61,9446),(73,42085),(74,206054),(77,206054),(82,37091),(97,206054),(98,206054),(101,9446),(105,42085),(106,206054),(118,34917),(129,9446),(130,206054),(133,206054),(138,205861),(146,107557),(153,201955),(158,238694)]),([6,1,18,122,420,839],[(0,37091),(2,37091),(4,37091),(6,37091),(8,37091),(10,234698),(12,37091),(14,37091),(16,37091),(18,231461),(57,37091),(58,37091),(73,37091),(74,37091),(82,37091),(85,37091),(97,37091),(98,37091),(105,37091),(106,37091),(118,37091),(130,37091),(133,37091),(137,42214),(153,201955)]),([6,1,18,124,420,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(74,205861),(85,206051),(97,205861),(98,205861),(105,205861),(106,205861),(118,204837),(130,205861),(133,205861),(137,200746),(138,205861),(153,198889),(158,238691)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_68 : K_68.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_69 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,18,126,420,508,833],[(56,9317),(72,9443),(96,9315),(128,9253),(140,206051),(148,205861),(184,107557)]),([6,1,18,126,420,833,903],[(56,9317),(72,9443),(116,37065),(144,36970),(192,36963)]),([6,1,18,126,420,839],[(0,37097),(2,37097),(4,37097),(6,37097),(8,37097),(10,234698),(12,37097),(14,37097),(16,37097),(18,237605),(57,37097),(58,37097),(73,37097),(74,37097),(82,37097),(85,37097),(97,37097),(98,37097),(105,37097),(106,37097),(118,37097),(130,37097),(133,37097),(137,42214)]),([6,1,18,126,420,889],[(0,107747),(2,107747),(4,107747),(6,107747),(8,107747),(10,231530),(12,107747),(14,107747),(16,107747),(18,107747),(57,107747),(58,107747),(74,107747),(82,107747),(85,107747),(97,107747),(98,107747),(105,107747),(106,107747),(130,107747),(133,107747),(141,107747),(157,100389)]),([6,1,18,126,422,833],[(0,36963),(2,36963),(4,36963),(6,102435),(8,36963),(10,231626),(12,36963),(14,100389),(16,36963),(18,36963),(57,36963),(58,36963),(73,36963),(74,36963),(82,36963),(85,36963),(97,206051),(98,36963),(118,36963),(130,36963),(133,36963),(137,34917),(138,36963),(146,36963),(153,36963),(158,36963)]),([6,1,18,420,839,903],[(0,234698),(2,234698),(4,234698),(6,102442),(8,234698),(10,234698),(12,234698),(14,234698),(16,234698),(18,206054),(57,234698),(58,234698),(73,234698),(74,234698),(81,234698),(82,234698),(98,234698),(101,234698),(106,37066),(113,234691),(118,36970),(130,234698),(133,234698),(138,234698),(145,34917),(157,42085)]),([6,1,19,120,126,420,833],[(56,9317),(84,206051),(128,8293),(156,204837),(168,9317),(184,107747),(192,107557)]),([6,1,19,120,420,839],[(0,206054),(2,206054),(4,206054),(6,102442),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(61,206054),(73,42085),(74,206054),(77,206054),(82,37091),(97,206054),(98,206054),(101,206054),(105,42085),(106,206054),(118,34917),(129,206054),(130,206054),(133,206054),(138,205861),(146,107557),(153,201955),(158,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_69 : K_69.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_70 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,22,64,120,420,833],[(56,9317),(80,200937),(96,9253),(112,205861),(144,201961),(184,205861)]),([6,1,22,120,120,420,833],[(56,9317),(88,205861),(92,205861)]),([6,1,22,120,121,420,833],[(76,9253),(100,205861),(112,205861),(116,205861)]),([6,1,22,120,122,420,833],[(56,9317),(72,9253),(116,205861),(192,107557)]),([6,1,22,120,126,420,833],[(56,9317),(72,9253),(84,206051),(108,205861),(116,205861),(156,204837),(192,107557)]),([6,1,22,120,190,420],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(74,205861),(97,205861),(98,205861),(106,205861),(109,205861),(129,205861),(130,205861),(157,107557),(158,204837)]),([6,1,22,120,256,420],[(0,238627),(2,238627),(4,238627),(6,102442),(8,238627),(10,36970),(12,238627),(14,238627),(16,238627),(18,35050),(57,238627),(58,238627),(73,238627),(74,238627),(97,238627),(98,238627),(105,238627),(106,238627),(113,238627),(114,238627),(129,107557),(130,238627),(154,238627),(157,238627)]),([6,1,22,120,420,508,833],[(56,9317),(72,9446),(96,9318),(140,206054),(148,205861),(156,205861),(204,238627)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_70 : K_70.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_71 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,22,120,420,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(74,205861),(97,205861),(98,205861),(130,205861),(133,205861),(137,200746),(138,205861),(153,201961),(158,238627)]),([6,1,22,120,420,833,889],[(56,9317),(172,205861),(188,205861),(204,205861)]),([6,1,22,120,420,833,903],[(56,9317),(172,205861)]),([6,1,22,120,420,839],[(0,206054),(2,206054),(4,206054),(6,102442),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(73,42085),(74,206054),(82,37097),(97,206054),(98,206054),(105,42085),(130,206054),(133,206054),(138,205861),(146,107557),(158,238694)]),([6,1,22,120,420,851],[(0,205861),(2,205861),(4,205861),(6,200746),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(73,42181),(74,205861),(97,205861),(98,205861),(106,35049),(118,35049),(130,205861),(133,205861),(138,205861),(146,107557),(153,35049),(158,238627)]),([6,1,22,120,420,855],[(0,205861),(2,205861),(4,205861),(6,200746),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(73,42181),(74,205861),(97,205861),(98,205861),(105,42181),(130,205861),(133,205861),(138,205861),(141,205861),(146,107557),(158,238694)]),([6,1,22,120,420,889],[(138,107557),(158,238627)]),([6,1,22,120,421,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(74,205861),(98,205861),(101,205861),(130,205861),(133,205861),(137,200746),(138,205861),(153,201961),(158,238627)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_71 : K_71.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_72 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,22,120,603,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(74,205861),(98,205861),(101,205861),(130,205861),(133,205861),(137,200746),(138,205861),(153,204837),(154,107557)]),([6,1,22,120,833,997],[(0,201961),(2,201961),(4,201961),(6,201961),(8,201961),(10,37065),(12,201961),(14,237766),(16,201961),(18,201961),(57,201961),(58,201961),(73,201961),(74,201961),(98,201961),(101,201961),(105,204837),(106,201961),(130,201961),(133,201961),(154,201961),(157,201961)]),([6,1,22,121,420,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(61,9253),(74,205861),(77,205861),(97,205861),(98,205861),(101,9253),(129,9253),(130,205861),(133,205861),(137,200746),(138,205861),(153,201961),(158,238627)]),([6,1,22,420,833,903],[(0,37066),(2,37066),(4,37066),(6,37066),(8,37066),(10,37066),(12,37066),(14,37066),(16,37066),(18,205861),(57,37066),(58,37066),(73,37066),(74,37066),(98,37066),(101,37066),(105,37066),(106,37066),(113,37065),(118,36970),(130,37066),(133,37066)]),([6,1,23,120,420,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(61,205861),(74,205861),(77,205861),(97,205861),(98,205861),(101,205861),(129,205861),(130,205861),(133,205861),(137,200746),(138,205861),(153,201961),(158,238627)]),([6,1,120,126,420,438,833],[(56,9253),(72,9443),(96,9251),(116,205861),(128,9317),(140,206051),(148,205861),(176,107747),(184,42085)]),([6,1,120,126,420,833,851],[(56,9253),(72,9443),(116,200745),(152,200806),(180,200937)]),([6,1,120,126,420,833,1005],[(56,9253),(72,9443),(116,204837),(136,107747),(144,102442),(188,102627)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_72 : K_72.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_73 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,120,420,438,839],[(0,42085),(2,42085),(4,42085),(6,234698),(8,42085),(10,42085),(12,42085),(14,102442),(16,42085),(18,42085),(57,42085),(58,42085),(73,42085),(74,42085),(82,42085),(97,206054),(98,42085),(114,42085),(117,42085),(130,42085),(133,42085),(138,42085),(149,42085),(150,42085),(158,107750)]),([6,1,120,420,833,855],[(0,200746),(2,200746),(4,200746),(6,37066),(8,200746),(10,200746),(12,200746),(14,42181),(16,200746),(18,200746),(57,200746),(58,200746),(73,200746),(74,200746),(98,200746),(101,200746),(113,204837),(114,200746),(130,200746),(133,200746),(154,200746),(157,200746)]),([6,1,120,420,833,1001],[(0,205861),(2,205861),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(16,205861),(18,205861),(58,205861),(73,205861),(74,205861),(98,205861),(101,205861),(113,201961),(118,102442),(130,205861),(133,205861),(154,205861),(157,205861)]),([6,1,120,420,839,1005],[(0,102442),(2,102442),(4,102442),(6,102442),(8,102442),(10,102442),(12,102442),(14,102442),(16,102442),(18,206054),(57,102442),(58,102442),(73,102442),(74,102442),(86,102435),(98,102442),(101,102442),(106,102442),(113,102435),(118,102442),(130,102442),(133,102442),(141,37091),(146,102442),(149,102442),(157,205861)]),([6,4,18,120,121,420,833],[(84,9446),(96,9443),(112,9253),(148,8229)]),([6,4,18,121,420,833],[(0,9253),(2,9253),(4,9253),(6,9253),(8,9253),(10,36874),(12,9253),(14,9253),(16,9253),(18,9253),(57,9253),(58,9253),(74,9253),(85,9446),(98,9253),(101,9253),(105,9253),(106,9253),(118,8229),(129,9253),(130,9253),(137,4138),(138,9253),(153,5353),(158,238598)]),([6,4,19,120,420,833],[(0,205861),(2,205861),(4,205861),(6,102410),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(73,9317),(74,205861),(98,205861),(101,205861),(105,9317),(106,205861),(118,204837),(129,205861),(130,205861),(138,205829),(146,107525),(153,201961),(158,238694)]),([6,5,18,120,420,833],[(0,205861),(2,231434),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(73,9443),(74,205861),(85,206054),(98,2281),(105,205861),(106,205861),(118,2281),(130,205861),(137,200746),(138,205861),(146,9443),(153,2281),(158,238595)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_73 : K_73.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_74 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,7,18,120,420,889],[(56,9443),(80,107525),(128,34917)]),([6,6,16,120,121,420,833],[(84,9446),(96,9443),(112,9446)]),([6,6,16,121,420,833],[(0,9446),(2,9446),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(57,9446),(58,9446),(74,9446),(82,9446),(85,9446),(101,9446),(105,9446),(106,9446),(129,9446),(130,9446),(137,9446),(138,9446),(153,5353),(158,238598)]),([6,6,17,120,420,833],[(0,206054),(2,206054),(4,206054),(6,102410),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(73,9317),(74,206054),(82,4329),(101,206054),(105,9317),(106,206054),(129,206054),(130,206054),(138,205829),(146,107525),(153,201961),(158,238627)]),([6,6,18,19,32,120,833],[(56,204837),(72,2281),(80,8293),(112,8294),(136,8293),(144,37091),(176,204805)]),([6,6,18,19,120,420,889],[(72,9443),(80,107525),(96,107747),(104,107525),(168,107557),(176,107525)]),([6,6,18,32,121,420,833],[(56,9253),(112,9446),(132,8229),(144,9446),(148,34917),(168,42085)]),([6,6,18,32,121,833],[(0,34917),(2,34917),(4,34917),(6,102435),(8,34917),(10,34917),(12,34917),(14,34917),(16,34917),(18,34917),(57,8229),(73,34917),(74,34917),(81,34917),(97,100389),(98,34917),(106,37091),(114,34917),(117,34917),(129,34917),(130,34917),(137,34917),(145,34917),(146,34917),(154,34821),(157,34917)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_74 : K_74.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_75 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,18,33,120,420,833],[(56,205861),(72,9443),(80,9317),(112,9446),(132,204837),(168,42085)]),([6,6,18,33,120,833],[(0,8294),(2,8294),(4,8294),(6,102435),(8,8294),(10,103433),(12,8294),(14,8294),(16,8294),(18,8294),(57,204837),(73,34917),(74,8294),(81,34917),(82,8294),(97,100389),(98,8294),(106,8294),(114,5353),(129,8294),(130,8294),(137,34917),(138,8294),(146,204806),(154,106502),(157,5225)]),([6,6,18,65,120,420,833],[(72,9443),(80,200937),(112,9446),(156,34917),(168,42085),(176,42211)]),([6,6,18,65,121,420,833],[(80,4329),(112,9446),(144,5353),(156,34917),(168,42085),(176,42211),(184,9446)]),([6,6,18,120,121,190,420],[(72,9253),(84,9446),(96,9443),(112,9446),(144,9446),(188,34917),(204,237670)]),([6,6,18,120,121,420,833],[(72,9253),(84,9446),(96,9443),(112,9446),(148,34917),(168,42085)]),([6,6,18,120,121,420,839],[(56,42085),(76,9446),(84,9446),(112,9446),(128,34917),(148,34917),(168,42085)]),([6,6,18,120,121,420,851],[(56,42181),(72,9253),(84,9446),(96,9443),(112,9446),(136,35049),(168,42181)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_75 : K_75.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_76 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,18,120,121,420,889],[(96,9443),(148,34821),(168,42085)]),([6,6,18,120,121,421,833],[(72,8229),(84,5353),(96,2281),(112,5353),(148,34917),(156,8294),(168,42085)]),([6,6,18,120,121,438,833],[(72,9253),(96,9443),(112,9446),(176,35049)]),([6,6,18,120,121,603,833],[(72,9253),(84,9446),(96,9443),(112,9446),(128,103651),(148,5353),(156,34917),(168,42085),(200,103657)]),([6,6,18,120,123,420,833],[(84,9446),(96,9443),(112,9446),(148,37091)]),([6,6,18,120,127,420,833],[(84,9446),(96,9443),(112,9446),(128,9443),(148,34917)]),([6,6,18,120,191,420],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(74,206054),(82,206054),(85,206054),(98,206054),(101,206054),(106,206054),(109,206054),(130,206054),(133,205861),(137,206054),(138,206054),(150,34917),(158,205030)]),([6,6,18,120,256,421],[(0,9318),(2,9318),(4,9318),(6,9318),(8,9318),(10,5226),(12,9318),(14,9318),(16,9318),(18,103434),(57,9318),(58,9251),(73,9318),(74,9318),(82,9318),(85,9251),(97,9318),(98,9318),(105,9318),(106,9318),(113,9318),(114,9318),(130,9318),(133,9318),(137,107526),(138,9318),(154,9318),(157,9318)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_76 : K_76.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_77 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,18,120,257,420],[(0,238601),(2,238601),(4,238601),(6,238601),(8,238601),(10,234602),(12,238601),(14,237578),(16,238601),(18,8426),(57,238601),(58,238601),(73,238601),(74,238601),(82,238601),(85,238601),(97,238601),(98,238601),(105,238601),(106,238601),(113,238601),(114,238601),(130,238601),(133,238601),(137,9449),(138,238601)]),([6,6,18,120,420,421,889],[(72,107747),(104,9251),(112,107526),(136,9317),(168,107557),(204,238601)]),([6,6,18,120,420,509,833],[(72,9253),(104,9251),(168,42085),(204,238601)]),([6,6,18,120,420,832],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(74,206054),(82,206054),(85,206054),(98,206054),(101,205861),(105,206054),(106,206054),(118,34917),(129,206054),(130,206054),(137,206054),(138,206054),(153,201961)]),([6,6,18,120,420,833,902],[(72,36874),(84,234506),(116,34917),(128,42085),(192,34917)]),([6,6,18,120,420,889,1022],[(72,107747),(128,107557)]),([6,6,18,121,121,420,833],[(84,9446),(88,9446),(92,9446),(148,34917),(168,42085)]),([6,6,18,121,122,420,833],[(56,9253),(96,9253),(108,9446),(112,9446),(156,34917)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_77 : K_77.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_78 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,18,121,123,420,833],[(84,9446),(108,9446),(112,9446),(116,9446),(148,37091),(156,34917)]),([6,6,18,121,126,420,833],[(56,9253),(96,9253),(100,9446),(108,9446),(112,9446),(128,34917)]),([6,6,18,121,127,420,833],[(84,9446),(100,9446),(108,9446),(112,9446),(116,9446),(128,34917),(148,34917)]),([6,6,18,121,190,420],[(0,9446),(2,9446),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(57,9253),(58,9446),(74,9446),(82,9446),(85,9446),(98,9446),(101,9446),(106,9446),(109,9446),(130,9446),(133,9253),(137,9446),(138,9446),(150,34917),(157,9446),(158,8422)]),([6,6,18,121,256,420],[(0,238598),(2,238598),(4,238598),(6,238598),(8,238598),(10,234506),(12,238598),(14,238598),(16,238598),(18,5354),(57,238598),(58,238598),(73,238598),(74,238598),(82,238598),(85,238598),(97,238598),(98,238598),(105,238598),(106,238598),(113,238598),(114,238598),(130,238598),(133,238598),(137,9446),(138,238598),(154,238598),(157,238598)]),([6,6,18,121,420,509,833],[(132,9253),(140,9446),(148,9446),(156,9446),(168,42085),(204,238694)]),([6,6,18,121,420,833],[(0,9446),(2,9446),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(57,9253),(58,9446),(74,9446),(82,9446),(85,9446),(98,9446),(101,9253),(105,9446),(106,9446),(118,34917),(129,9446),(130,9446),(137,9446),(138,9446),(153,5353),(158,238598)]),([6,6,18,121,420,833,889],[(72,9443),(168,9253),(180,9446),(188,9446),(196,34917),(204,9446)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_78 : K_78.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_79 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,18,121,420,833,902],[(84,234506),(116,34917),(128,42085),(172,9446),(192,34917)]),([6,6,18,121,420,833,903],[(72,9443),(128,42085),(172,9446),(176,4329),(192,5353),(204,9446)]),([6,6,18,121,420,839],[(0,9446),(2,9446),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(57,9446),(58,9446),(61,9446),(74,9446),(77,9446),(82,9446),(85,9446),(97,9446),(98,9446),(101,9446),(105,9446),(106,9446),(118,34917),(129,9446),(130,9446),(133,9446),(137,9446),(138,9446),(153,5353),(158,238598)]),([6,6,18,121,420,851],[(0,9446),(2,9446),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(57,9253),(58,9446),(74,9446),(82,9446),(85,9446),(98,9446),(101,9253),(105,9446),(106,9446),(129,9253),(130,9446),(138,9446),(141,9446),(153,5353),(158,238598)]),([6,6,18,121,420,889],[(98,34821),(118,34821),(157,34821)]),([6,6,18,121,421,833],[(0,5353),(2,5353),(4,5353),(6,5353),(8,5353),(10,234505),(12,5353),(14,5353),(16,5353),(18,237574),(57,5353),(58,5353),(73,5353),(74,5353),(82,5353),(85,5353),(98,5353),(101,5353),(105,5353),(106,5353),(118,5353),(129,8422),(130,5353),(137,8422),(138,5353),(153,5353),(158,238694)]),([6,6,18,121,422,833],[(0,9446),(2,9446),(4,9446),(6,102435),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(57,9446),(73,34917),(74,9446),(82,9446),(98,9446),(101,9446),(106,9446),(118,34917),(129,9446),(130,9446),(137,34917),(138,9446),(146,34821),(153,5353),(158,238598)]),([6,6,18,121,438,833],[(0,9446),(2,9446),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(57,9253),(62,9445),(74,9446),(82,9446),(98,9446),(101,9446),(106,9446),(109,9446),(129,9446),(130,9446),(137,9446),(138,9446),(153,5353),(158,238598)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_79 : K_79.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_80 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,18,121,603,833],[(0,9446),(2,9446),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(57,9253),(58,9446),(74,9446),(82,9446),(85,9446),(97,9253),(98,9446),(106,9446),(109,9446),(118,34917),(129,9446),(130,9446),(137,9446),(138,9446),(153,8422),(154,9446)]),([6,6,18,121,833,997],[(0,5353),(2,5353),(4,5353),(6,5353),(8,5353),(10,234505),(12,5353),(14,237574),(16,5353),(18,5353),(57,5353),(58,5353),(73,5353),(74,5353),(82,5353),(85,5353),(97,8422),(98,5353),(105,8422),(106,5353),(130,5353),(133,5353),(137,5353),(138,5353),(149,5353),(150,5353),(154,5353),(157,5353)]),([6,6,18,123,420,833],[(0,9446),(2,231461),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(58,9446),(74,9446),(82,9446),(85,9446),(98,9446),(105,9446),(106,9446),(118,37091),(129,37091),(130,9446),(137,9446),(138,9446),(146,37091),(153,5353),(158,238598)]),([6,6,18,126,127,420,833],[(76,9446),(84,9446),(112,9446),(128,36963),(168,37097)]),([6,6,18,127,420,833],[(0,9446),(2,9446),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(58,9446),(61,9443),(74,9446),(77,9446),(82,9446),(85,9446),(97,9443),(98,9446),(105,9446),(106,9446),(129,9446),(130,9446),(137,9446),(138,9446),(153,5353),(158,238598)]),([6,6,18,420,833,902],[(0,234506),(2,234506),(4,234506),(6,234506),(8,234506),(10,234506),(12,234506),(14,234506),(16,234506),(18,9446),(57,36874),(58,234506),(74,234506),(77,36874),(81,234506),(82,234506),(97,234506),(98,234506),(105,234506),(106,234506),(113,234505),(118,234506),(130,234506),(133,234506),(138,234506),(145,34917)]),([6,6,19,32,120,833],[(0,8293),(2,8293),(4,8293),(6,102409),(8,8293),(10,8293),(12,8293),(14,8293),(16,8293),(18,8293),(57,204837),(73,8293),(74,8293),(81,8293),(97,100389),(98,8293),(106,4329),(114,8293),(117,8293),(129,8293),(130,8293),(138,204805),(145,8293),(146,8293),(154,106501),(157,4201)]),([6,6,19,120,121,420,833],[(84,9446),(108,206054),(112,4329),(116,206054),(148,4329),(156,8293),(168,42085),(192,107525)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_80 : K_80.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_81 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,19,120,123,420,833],[(84,9446),(108,206054),(112,4329),(116,206054),(148,4329),(156,8293),(192,107525)]),([6,6,19,120,190,420],[(0,206054),(2,206054),(4,206054),(6,102410),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(73,9317),(74,206054),(82,237573),(98,206054),(101,206054),(106,205829),(114,9317),(130,206054),(133,205861),(137,9317),(138,206054),(150,8293),(157,107525),(158,205030)]),([6,6,19,120,256,420],[(0,238694),(2,238694),(4,238694),(6,102410),(8,238694),(10,4202),(12,238694),(14,238694),(16,238694),(18,103658),(57,238694),(58,238627),(73,238694),(74,238694),(97,238694),(98,238694),(105,238694),(106,238694),(113,238694),(114,238694),(130,238694),(133,238694),(137,9317),(138,238694),(154,238694),(157,238694)]),([6,6,19,120,420,833],[(0,206054),(2,206054),(4,206054),(6,102410),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(73,9317),(74,206054),(82,4329),(98,206054),(101,205861),(105,9317),(106,206054),(118,8293),(129,206054),(130,206054),(138,205829),(146,107525),(153,201961),(158,238694)]),([6,6,19,120,420,839],[(0,206054),(2,206054),(4,206054),(6,102410),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(61,206054),(73,9317),(74,206054),(77,206054),(82,4329),(97,206054),(98,206054),(101,206054),(105,9317),(106,206054),(118,8293),(129,206054),(130,206054),(133,206054),(138,205829),(146,107525),(153,201961),(158,238694)]),([6,6,19,120,420,851],[(0,205829),(2,205829),(4,205829),(6,200714),(8,205829),(10,4298),(12,205829),(14,205829),(16,205829),(18,205829),(57,205829),(58,205829),(73,9413),(74,205829),(98,205829),(101,205829),(105,9413),(106,205829),(118,204805),(129,205829),(130,205829),(138,205829),(141,205829),(146,107525),(153,201961),(158,238694)]),([6,6,19,120,420,889],[(0,107525),(2,107525),(4,107525),(6,102410),(8,107525),(10,4202),(12,107525),(14,107525),(16,107525),(18,107525),(57,107525),(58,107525),(73,9317),(74,107525),(98,107525),(101,107525),(105,9317),(106,107525),(113,107525),(118,106501),(129,107525),(130,107525),(138,107525),(141,107525),(146,107525),(149,107525),(157,107525),(158,107525)]),([6,6,19,120,421,833],[(0,206054),(2,206054),(4,206054),(6,102409),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(73,8293),(74,206054),(82,206054),(98,206054),(101,205861),(106,206054),(118,8293),(129,206054),(130,206054),(138,206054),(146,8293),(153,201961),(158,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_81 : K_81.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_82 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,19,120,422,833],[(0,206054),(2,206054),(4,206054),(6,102410),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(73,9317),(74,206054),(82,4329),(98,206054),(101,206054),(106,206054),(118,8293),(129,206054),(130,206054),(138,205829),(146,107525),(153,201961),(158,238694)]),([6,6,19,120,438,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(74,206054),(82,206054),(98,206054),(101,206054),(106,206054),(129,206054),(130,206054),(138,206054),(153,201961),(158,238694)]),([6,6,19,120,439,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(74,206054),(82,4329),(98,206054),(101,206054),(106,206054),(109,206054),(129,206054),(130,206054),(138,205829),(146,107525),(153,201961),(158,238694)]),([6,6,19,120,603,833],[(0,206054),(2,206054),(4,206054),(6,102410),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(73,9317),(74,206054),(82,4329),(97,205861),(98,206054),(106,206054),(109,206054),(118,8293),(129,206054),(130,206054),(138,205829),(146,107525),(153,205030),(154,107525)]),([6,6,19,120,833,997],[(0,201961),(2,201961),(4,201961),(6,102409),(8,201961),(10,234697),(12,201961),(14,237766),(16,201961),(18,201961),(57,201961),(58,201961),(73,201961),(74,201961),(82,201961),(97,205030),(98,201961),(106,201961),(130,201961),(133,201961),(138,201961),(149,201961),(150,201961),(154,201961),(157,201961)]),([6,6,19,121,420,833],[(0,4329),(2,4329),(4,4329),(6,4329),(8,4329),(10,234698),(12,4329),(14,4329),(16,4329),(18,237573),(57,4329),(58,4329),(73,4329),(74,4329),(82,4329),(85,4329),(98,4329),(101,4329),(105,4329),(106,4329),(118,4329),(129,206054),(130,4329),(137,9446),(153,201961)]),([6,6,19,122,420,833],[(0,206054),(2,231461),(4,206054),(6,102410),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(58,206054),(74,206054),(82,4329),(98,206054),(105,9317),(106,206054),(118,8293),(129,37091),(130,206054),(138,205829),(146,107525),(153,201961),(158,238694)]),([6,6,19,123,420,833],[(0,4329),(2,231461),(4,4329),(6,4329),(8,4329),(10,234698),(12,4329),(14,4329),(16,4329),(18,237573),(58,4329),(74,4329),(82,4329),(85,4329),(98,4329),(105,4329),(106,4329),(118,4329),(129,37091),(130,4329),(137,9446),(153,201961)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_82 : K_82.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_83 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,19,126,420,833],[(0,206054),(2,206054),(4,206054),(6,102410),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(58,206054),(61,206051),(74,206054),(77,206054),(82,4329),(97,206051),(98,206054),(105,9317),(106,206054),(118,8293),(129,206054),(130,206054),(138,205829),(146,107525),(153,201961),(158,238694)]),([6,6,19,420,833,903],[(0,234698),(2,234698),(4,234698),(6,102410),(8,234698),(10,234698),(12,234698),(14,234698),(16,234698),(18,206054),(57,37066),(58,234698),(74,234698),(77,37066),(81,234698),(82,234698),(97,234698),(98,234698),(106,4298),(113,234697),(118,4202),(130,234698),(133,234698),(138,234698),(145,8293),(157,9317)]),([6,6,22,120,121,420,833],[(72,9253),(76,9253),(84,9446),(112,9446),(168,42085)]),([6,6,22,121,420,833],[(0,9446),(2,9446),(4,9446),(6,9446),(8,9446),(10,234506),(12,9446),(14,9446),(16,9446),(18,9446),(57,9253),(58,9446),(61,9446),(74,9446),(77,9253),(82,9446),(85,9446),(97,9446),(101,9253),(105,9446),(129,9446),(130,9446),(133,9253),(137,9446),(138,9446),(153,5353),(158,238598)]),([6,6,23,120,420,833],[(0,206054),(2,206054),(4,206054),(6,102410),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(61,206054),(73,9317),(74,206054),(77,205861),(82,4329),(97,206054),(101,205861),(105,9317),(129,206054),(130,206054),(133,205861),(138,205829),(146,107525),(153,201961),(158,238627)]),([6,6,120,121,420,438,833],[(56,9253),(72,9443),(80,9446),(104,9445),(112,9251),(168,42085)]),([6,6,120,121,420,833,851],[(56,9253),(72,9443),(80,9446),(108,34917),(148,42211),(152,200806),(168,200746),(180,200937),(188,200937)]),([6,6,120,121,420,833,1005],[(56,9253),(72,9443),(80,9446),(108,102435),(128,102442),(180,4329)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_83 : K_83.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_84 : List (List ℕ × List (ℕ × ℕ)) := [([6,6,120,420,439,833],[(0,9317),(2,9317),(4,9317),(6,234698),(8,9317),(10,9317),(12,9317),(14,102410),(16,9317),(18,9317),(57,9317),(58,9317),(77,9317),(82,9317),(98,9317),(101,9317),(114,9317),(117,9317),(129,9317),(130,9317),(138,9317),(150,9317),(158,107750)]),([6,6,120,420,833,1004],[(0,102410),(2,102410),(4,102410),(6,102410),(8,102410),(10,102410),(12,102410),(14,102410),(16,102410),(18,206054),(57,102410),(58,102410),(74,102410),(77,102410),(86,102409),(97,102410),(98,102410),(106,102410),(113,102409),(118,102410),(130,102410),(133,102410),(141,4329),(146,102410),(149,102410),(157,205829)]),([6,6,120,421,438,833],[(0,9251),(2,9251),(4,9251),(6,234698),(8,9251),(10,34826),(12,9251),(14,9251),(16,9251),(18,9251),(57,9251),(58,9251),(77,205861),(82,9251),(98,9251),(101,9251),(129,9251),(130,9251),(138,9251),(150,107750),(158,9251)]),([6,6,121,420,438,833],[(0,9446),(2,9446),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(16,9446),(18,9446),(58,9446),(77,9253),(78,9445),(98,9446),(101,9446),(114,9446),(117,9446),(129,9446),(130,9446),(145,9446),(150,9446),(153,4329),(158,9446)]),([6,6,121,420,833,851],[(0,9446),(2,9446),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(16,9446),(18,9446),(58,9446),(74,34917),(77,4138),(86,34917),(97,9446),(98,9446),(110,42211),(113,8422),(114,9446),(129,4138),(130,9446),(142,4329),(145,8422),(146,4329),(154,9446),(157,9446)]),([6,6,121,420,833,1005],[(0,9446),(2,9446),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(16,9446),(18,9446),(58,9446),(74,102435),(77,9253),(86,102435),(97,9446),(98,9446),(113,5353),(118,238598),(130,9446),(133,9253),(141,9446),(146,9446),(149,9446),(154,9446),(157,9446)]),([6,7,16,120,420,833],[(0,206054),(2,231434),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(73,9443),(74,206054),(82,206054),(85,206054),(105,206054),(106,206054),(130,206054),(137,206054),(138,206054),(146,9443),(153,2281),(158,238595)]),([6,7,18,32,120,833],[(0,2281),(2,231433),(4,2281),(6,102435),(8,2281),(10,2281),(12,2281),(14,2281),(16,2281),(18,237571),(57,2281),(73,2281),(74,2281),(81,2281),(82,2281),(97,2281),(98,2281),(106,2281),(114,2281),(117,2281),(137,34917),(138,2281),(145,34917),(146,2281),(154,2281),(157,2153)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_84 : K_84.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_85 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,18,120,121,420,833],[(84,206054),(96,9443),(108,206054),(112,206054),(116,206054),(148,34917),(156,2281),(168,42085),(192,9443)]),([6,7,18,120,126,420,833],[(56,9317),(84,206054),(96,9443),(108,206054),(112,206054),(116,206054),(148,34917)]),([6,7,18,120,127,420,833],[(84,206054),(96,9443),(100,206054),(108,206054),(112,206054),(116,206054),(128,2281),(148,2281)]),([6,7,18,120,190,420],[(0,206054),(2,231434),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(73,9443),(74,206054),(82,206054),(85,206054),(98,206054),(106,206054),(109,206054),(114,9443),(130,237571),(137,206054),(138,206054),(150,237571),(157,107750),(158,205030)]),([6,7,18,120,256,420],[(0,238595),(2,231434),(4,238595),(6,238595),(8,238595),(10,234602),(12,238595),(14,238595),(16,238595),(18,2282),(57,238595),(58,238595),(73,238595),(74,238595),(82,238595),(85,238595),(97,238595),(98,238595),(105,238595),(106,238595),(113,238595),(114,238595),(137,107750),(138,238595),(154,238595),(157,238595)]),([6,7,18,120,420,833],[(0,206054),(2,231434),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(73,9443),(74,206054),(82,206054),(85,206054),(98,2281),(105,206054),(106,206054),(118,2281),(130,206054),(137,206054),(138,206054),(146,9443),(153,2281),(158,238595)]),([6,7,18,120,420,839],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(74,206054),(82,206054),(85,206054),(97,206054),(105,206054),(106,206054),(130,206054),(133,206054),(137,206054),(138,206054),(158,238694)]),([6,7,18,120,420,851],[(0,206054),(2,231434),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(73,9443),(74,206054),(82,206054),(85,206054),(98,2281),(105,206054),(106,206054),(118,2281),(130,206054),(138,206054),(141,206054),(146,9443),(153,2281),(158,238595)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_85 : K_85.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_86 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,18,120,420,889],[(0,9443),(2,231434),(4,9443),(6,9443),(8,9443),(10,9443),(12,9443),(14,9443),(16,9443),(18,9443),(57,9443),(73,9443),(82,9443),(85,9443),(98,2281),(105,9443),(106,9443),(113,9443),(118,2281),(138,9443),(141,9443),(146,9443),(149,9443),(157,2282),(158,238595)]),([6,7,18,120,421,833],[(0,2281),(2,231433),(4,2281),(6,2281),(8,2281),(10,234698),(12,2281),(14,2281),(16,2281),(18,237571),(57,2281),(58,2281),(73,2281),(74,2281),(82,2281),(85,2281),(98,2281),(101,2281),(105,2281),(106,2281),(118,2281),(137,206054),(138,2281),(146,2281),(153,2281),(158,238694)]),([6,7,18,120,422,833],[(0,206054),(2,231434),(4,206054),(6,102435),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(73,9443),(74,206054),(82,206054),(98,2281),(106,206054),(118,2281),(130,206054),(137,34917),(138,206054),(146,34917),(153,2281),(158,238595)]),([6,7,18,120,423,833],[(0,2281),(2,231433),(4,2281),(6,102435),(8,2281),(10,234698),(12,2281),(14,2281),(16,2281),(18,237571),(57,2281),(73,2281),(74,2281),(82,2281),(98,2281),(101,2281),(106,2281),(118,2281),(137,34917),(138,2281),(146,2281),(153,2281),(158,238694)]),([6,7,18,120,438,833],[(0,206054),(2,231434),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(62,206053),(73,9443),(74,206054),(81,9443),(82,206054),(98,2281),(106,206054),(109,206054),(118,2281),(130,206054),(137,206054),(138,206054),(146,9443),(153,2281),(158,238595)]),([6,7,18,120,603,833],[(0,206054),(2,231434),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(73,9443),(74,206054),(82,206054),(85,206054),(98,2281),(106,206054),(109,206054),(118,2281),(130,206054),(137,206054),(138,206054),(146,9443),(153,205030),(154,107750)]),([6,7,18,120,833,997],[(0,2281),(2,231433),(4,2281),(6,2281),(8,2281),(10,234697),(12,2281),(14,237571),(16,2281),(18,2281),(57,2281),(58,2281),(73,2281),(74,2281),(82,2281),(85,2281),(105,205030),(106,2281),(130,2281),(133,2281),(137,2281),(138,2281),(149,2281),(150,2281),(154,2281),(157,2281)]),([6,7,18,121,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(74,206054),(82,206054),(85,206054),(98,206054),(101,9253),(105,206054),(106,206054),(118,34917),(129,9446),(130,206054),(137,206054),(138,206054),(153,201961),(158,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_86 : K_86.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_87 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,18,122,420,833],[(0,206054),(2,231434),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(58,206054),(74,206054),(82,206054),(85,206054),(98,2281),(105,206054),(106,206054),(118,2281),(130,206054),(137,206054),(138,206054),(146,9443),(153,2281),(158,238595)]),([6,7,18,126,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(58,206054),(74,206054),(82,206054),(85,206054),(97,206051),(98,206054),(105,206054),(106,206054),(130,206054),(137,206054),(138,206054),(153,201961),(158,238694)]),([6,7,18,127,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(58,206054),(61,9443),(74,206054),(77,206054),(82,206054),(85,206054),(97,206051),(98,2281),(105,206054),(106,206054),(129,9446),(130,206054),(137,206054),(138,206054),(153,2281),(158,238595)]),([6,7,18,420,833,903],[(0,234698),(2,231434),(4,234698),(6,234698),(8,234698),(10,234698),(12,234698),(14,234698),(16,234698),(18,206054),(57,37066),(58,234698),(74,234698),(81,234698),(82,234698),(98,234698),(105,234698),(106,234698),(113,234697),(118,234602),(130,234698),(133,234698),(137,9443),(138,234698),(145,2281),(157,9443)]),([6,7,19,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(74,206054),(82,206054),(85,206054),(98,206054),(101,205861),(105,206054),(106,206054),(118,34917),(129,206054),(130,206054),(137,206054),(138,206054),(153,201961),(158,238694)]),([6,7,22,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(74,206054),(82,206054),(85,206054),(97,206054),(105,206054),(130,206054),(133,205861),(137,206054),(138,206054),(153,201961),(158,238627)]),([6,7,23,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,205861),(58,206054),(61,206054),(74,206054),(77,205861),(82,206054),(85,206054),(97,206054),(101,205861),(105,206054),(129,206054),(130,206054),(133,205861),(137,206054),(138,206054),(153,2281),(158,238595)]),([6,7,120,420,438,833],[(0,206054),(2,231434),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(16,206054),(18,206054),(57,9443),(58,206054),(78,206053),(82,9443),(98,206054),(110,9443),(114,206054),(117,206054),(130,206054),(138,9443),(145,206054),(150,107750),(153,200937),(158,107750)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_87 : K_87.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_88 : List (List ℕ × List (ℕ × ℕ)) := [([6,7,120,420,833,851],[(0,206054),(2,231434),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(16,206054),(18,206054),(57,9443),(58,206054),(74,34917),(86,34917),(98,206054),(110,9443),(113,205030),(114,206054),(130,206054),(142,200937),(145,205030),(146,200937),(154,206054),(157,206054)]),([6,7,120,420,833,1005],[(0,206054),(2,231434),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(16,206054),(18,206054),(57,9443),(58,206054),(74,102435),(86,102435),(98,206054),(106,9443),(113,2281),(118,238595),(130,206054),(133,205861),(141,206054),(142,9443),(146,206054),(149,206054),(154,206054),(157,206054)]),([6,18,19,120,126,420,833],[(56,9317),(76,206051),(96,9317),(104,9443),(156,204837),(168,9413),(184,107747),(192,107557)]),([6,18,19,120,420,839],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(57,206054),(58,206054),(61,206054),(73,9317),(74,37091),(77,206054),(82,37091),(97,206054),(98,206054),(101,206054),(105,206054),(106,206054),(129,206054),(130,205861),(133,206054),(138,205861),(141,206054),(146,107557),(153,201955),(158,238694)]),([6,18,22,120,121,420,833],[(72,9253),(76,9446),(80,9253),(104,9443),(112,9253),(148,8229),(168,42181),(176,42181)]),([6,18,22,121,420,833],[(0,9253),(2,9253),(4,9253),(6,9253),(8,9253),(10,36874),(12,9253),(14,9253),(16,9253),(18,9253),(57,9253),(58,9253),(61,9253),(77,9446),(97,9253),(98,9253),(101,9253),(106,9253),(109,9253),(118,8229),(129,9253),(130,9253),(133,9253),(137,9253),(138,9253),(153,5353),(158,238598)]),([6,18,23,120,420,833],[(0,205861),(2,205861),(4,205861),(6,231434),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(61,205861),(73,9317),(77,206054),(81,9443),(97,205861),(98,205861),(101,205861),(106,2281),(118,2281),(129,205861),(130,205861),(133,205861),(138,205861),(146,9443),(153,2281),(158,238595)]),([6,18,120,121,126,420,833],[(80,9253),(104,9253),(112,9443),(140,8229),(192,42085)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_88 : K_88.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_89 : List (List ℕ × List (ℕ × ℕ)) := [([6,18,120,121,127,420,833],[(76,9443),(84,9443),(112,9443),(140,100389),(148,2281),(184,9443),(192,42085)]),([6,18,120,121,420,833,839],[(60,9446),(80,9446),(108,34917),(140,9446),(148,42085),(152,201955),(168,200746),(176,9253),(200,42085)]),([6,18,120,121,420,833,1017],[(60,9446),(80,9446),(108,34917),(176,9446),(196,231526)]),([6,18,120,121,420,839],[(0,42085),(2,102442),(4,42085),(6,42085),(8,42085),(10,42085),(12,42085),(14,42085),(16,42085),(18,42085),(62,9446),(81,42085),(82,42085),(85,42085),(97,42085),(105,9446),(109,42085),(110,34917),(113,42085),(118,34917),(130,42181),(137,42085),(138,42085),(141,9446),(146,42085),(149,42085),(153,201955),(158,238694)]),([6,18,120,126,127,420,833],[(76,9443),(84,9443),(112,9443)]),([6,18,120,126,420,421,833],[(60,206051),(96,9251),(104,9315),(128,9317),(136,9253),(176,107747),(184,107557),(196,9318),(204,238601)]),([6,18,120,126,420,833,1022],[(60,206051),(116,204837),(136,107747),(144,107557)]),([6,18,120,127,420,833],[(0,9443),(2,9443),(4,9443),(6,9443),(8,9443),(10,231434),(12,9443),(14,9443),(16,9443),(18,9443),(61,9443),(62,9443),(74,9443),(77,9443),(82,9443),(85,9443),(97,9443),(98,9443),(105,9443),(110,2281),(129,9443),(130,9443),(137,9443),(138,9443),(153,2281),(158,238595)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_89 : K_89.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_90 : List (List ℕ × List (ℕ × ℕ)) := [([6,18,120,420,421,839],[(0,206054),(2,102442),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(16,206054),(18,206054),(58,37091),(73,42085),(74,206054),(82,9318),(97,42085),(98,206054),(106,42085),(114,206054),(117,206054),(130,205861),(138,107557),(149,9318),(150,107557),(157,206054),(158,107557)]),([6,18,120,420,833,1016],[(0,231434),(2,231434),(4,231434),(6,231434),(8,231434),(10,231434),(12,231434),(14,231434),(16,231434),(18,206054),(58,231434),(61,231434),(73,231434),(74,231434),(86,231433),(97,231434),(98,231434),(106,231434),(113,231433),(118,231434),(130,231434),(133,231434),(138,231434),(141,231434),(149,2281),(157,206054)]),([6,18,120,420,839,1022],[(0,206054),(2,102442),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(16,206054),(18,206054),(58,37091),(73,42085),(74,206054),(86,34917),(98,205861),(106,107557),(113,201955),(118,238694),(130,206054),(133,206054),(138,206054),(141,206054),(146,206054),(149,206054),(157,206054),(158,206054)]),([6,18,121,126,420,833],[(0,9253),(2,9253),(4,9253),(6,36874),(8,9253),(10,9253),(12,9253),(14,9253),(16,9253),(18,9253),(74,9253),(77,9253),(97,9253),(98,9253),(105,9253),(110,8229),(117,9253),(118,8229),(129,9253),(130,9253),(145,9253),(146,9253),(153,201961),(158,238694)]),([6,18,121,127,420,833],[(62,9443),(110,100389),(117,9253),(137,9443),(145,9253),(153,5353),(158,238598)]),([6,18,121,420,833,839],[(0,9446),(2,9446),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(16,9446),(18,9446),(58,37091),(61,9446),(73,9446),(74,9446),(86,34917),(97,9446),(98,9446),(102,9446),(110,42085),(113,8422),(114,9446),(118,9446),(129,9446),(130,9253),(138,9253),(145,8422),(150,9253),(153,9446),(154,9446),(157,9446)]),([6,18,121,420,833,1017],[(0,9446),(2,9446),(4,9446),(6,234506),(8,9446),(10,9446),(12,9446),(14,9446),(16,9446),(18,9446),(58,231461),(61,9446),(73,9446),(74,9446),(86,34917),(97,9446),(98,9446),(113,5353),(118,238598),(130,9253),(133,9446),(138,9446),(141,9446),(149,9446),(150,9253),(154,9446),(157,9446)]),([6,18,121,420,839],[(1,9446),(3,9446),(5,42085),(7,42085),(9,9446),(11,9446),(13,9446),(15,9446),(63,9446),(75,9446),(79,9446),(83,42085),(87,42085),(99,9446),(103,9446),(107,42085),(111,42085),(115,9446),(119,9446)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_90 : K_90.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_91 : List (List ℕ × List (ℕ × ℕ)) := [([6,19,22,120,420,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(81,9317),(97,205861),(98,205861),(106,205861),(109,205861),(118,204837),(130,205861),(133,205861),(137,205861),(138,205861),(153,201961),(158,238694)]),([6,19,23,120,420,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(61,205861),(77,206054),(97,205861),(98,205861),(101,205861),(106,205861),(109,205861),(118,204837),(129,205861),(130,205829),(133,205861),(137,205861),(138,205829),(146,107525),(153,201961),(158,238694)]),([6,19,120,126,420,833],[(0,9317),(2,102410),(4,9317),(6,9317),(8,9317),(10,9317),(12,9317),(14,9317),(16,9317),(18,9317),(62,206051),(82,9317),(85,9317),(97,9317),(105,9317),(110,100389),(117,205861),(118,8293),(130,9413),(137,206051),(138,9317),(145,205861),(146,9317),(153,201961),(158,238694)]),([6,19,120,420,833,839],[(0,206054),(2,102410),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(16,206054),(18,206054),(58,37091),(73,9317),(74,206054),(86,8293),(98,206054),(102,206054),(106,9317),(110,9317),(113,205030),(114,206054),(118,206054),(130,205861),(138,205861),(145,205030),(150,205861),(153,206054),(154,206054),(157,206054)]),([6,19,120,420,833,1017],[(0,206054),(2,102410),(4,206054),(6,234698),(8,206054),(10,206054),(12,206054),(14,206054),(16,206054),(18,206054),(58,231461),(73,9317),(74,206054),(86,8293),(98,205829),(106,107525),(113,201961),(118,238694),(130,205861),(133,206054),(138,206054),(141,206054),(149,206054),(150,205861),(154,206054),(157,206054)]),([6,19,120,420,839],[(1,206054),(3,206054),(5,9317),(7,9317),(9,206054),(11,206054),(13,206054),(15,206054),(63,206054),(75,206054),(79,206054),(83,9317),(87,9317),(99,206054),(103,206054),(107,9317),(111,9317),(115,206054),(119,206054)]),([6,22,23,120,420,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,37066),(12,205861),(14,205861),(16,205861),(18,205861),(57,205861),(58,205861),(61,205861),(73,9317),(77,206054),(97,205861),(101,205861),(105,205861),(129,205861),(130,205861),(133,205861),(138,205861),(141,205861),(153,201961),(158,238627)]),([6,22,120,121,420,833],[(58,9253),(62,9446),(105,9446),(109,9253),(129,200746),(130,42181),(141,9253),(153,201961),(158,238627)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_91 : K_91.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_92 : List (List ℕ × List (ℕ × ℕ)) := [([6,22,120,420,421,833],[(0,205861),(2,205861),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(16,205861),(18,205861),(74,9251),(82,9318),(98,205861),(114,205861),(117,205861),(129,200746),(130,205861),(149,9251),(150,107557),(157,205861),(158,107557)]),([6,22,120,420,833,1022],[(0,205861),(2,205861),(4,205861),(6,37066),(8,205861),(10,205861),(12,205861),(14,205861),(16,205861),(18,205861),(97,200746),(98,205861),(113,201961),(118,238627),(130,205861),(133,205861),(138,205861),(141,205861),(146,205861),(149,205861),(157,205861),(158,205861)]),([6,22,121,420,833],[(1,9253),(3,9253),(9,9253),(11,9253),(13,9253),(15,9253),(63,9446),(75,9253),(79,9253),(87,9253),(99,9253),(103,9253),(115,9253),(119,9253)]),([6,23,120,420,833],[(1,205861),(3,205861),(5,9317),(7,9317),(9,205861),(11,205861),(13,205861),(15,205861),(63,206054),(75,205861),(79,205861),(83,9317),(87,205861),(99,205861),(103,205861),(107,9317),(111,9317),(115,205861),(119,205861)]),([7,1,4,18,120,420,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,205861),(12,205861),(14,37066),(16,205861),(18,205861),(20,205861),(22,205861),(57,205861),(58,205861),(73,205861),(74,205861),(81,205861),(82,205861),(98,205861),(106,205861),(117,206054),(129,205861),(130,205861),(138,205861),(141,205861),(145,205861),(146,205861),(158,204837),(170,205861),(173,205861),(177,205861),(178,205861),(185,200746),(186,205861),(201,201961),(206,238694)]),([7,1,6,16,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(81,206054),(82,206054),(98,206054),(106,206054),(114,206054),(117,206054),(129,206054),(130,206054),(141,206054),(145,206054),(146,206054),(170,206054),(173,206054),(177,206054),(178,206054),(185,206054),(186,206054),(201,201961),(206,238627)]),([7,1,6,18,32,120,420,833],[(56,9443),(72,9317),(80,205861),(152,206054),(180,204837),(192,206054),(196,34917),(224,42085)]),([7,1,6,18,32,120,833],[(0,34917),(2,34917),(4,34917),(6,34917),(8,34917),(10,102435),(12,34917),(14,34917),(16,34917),(18,34917),(20,34917),(22,34917),(57,34917),(58,34917),(74,34917),(81,204837),(97,34917),(98,34917),(105,34917),(106,34917),(113,34917),(129,34917),(130,34917),(137,100389),(138,34917),(146,37091),(154,34917),(157,34917),(170,34917),(173,34917),(177,34917),(178,34917),(185,34917),(193,34917),(194,34917),(202,34917),(205,34917)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_92 : K_92.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_93 : List (List ℕ × List (ℕ × ℕ)) := [([7,1,6,18,64,120,420,833],[(56,9443),(72,9317),(112,200937),(128,9446),(152,206054),(192,201961),(204,34917),(224,42085),(232,42211),(240,206054)]),([7,1,6,18,120,120,420,833],[(56,9443),(72,9317),(116,206054),(120,206054),(124,206054),(196,34917),(224,42085)]),([7,1,6,18,120,121,420,833],[(100,9446),(116,206054),(132,206054),(148,206054),(152,206054),(156,206054),(196,34917),(204,34917),(224,42085)]),([7,1,6,18,120,122,420,833],[(56,9443),(72,9317),(116,206054),(148,206054),(152,206054),(156,206054),(196,37091),(204,34917)]),([7,1,6,18,120,126,420,833],[(72,9317),(116,206054),(140,206054),(148,206054),(152,206054),(156,206054),(176,34917),(196,34917)]),([7,1,6,18,120,190,420],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(81,205861),(82,206054),(98,206054),(106,206054),(114,206054),(117,206054),(129,206054),(130,206054),(138,206054),(141,206054),(146,206054),(149,206054),(169,206054),(170,206054),(178,206054),(181,205861),(185,206054),(186,206054),(198,34917),(205,107750),(206,205030)]),([7,1,6,18,120,256,420],[(0,238694),(2,238694),(4,238694),(6,238694),(8,238694),(10,238694),(12,238694),(14,234602),(16,238694),(18,238694),(20,238694),(22,103658),(57,238694),(58,238694),(73,238694),(74,238694),(81,238694),(82,238627),(97,238694),(98,238694),(105,238694),(106,238694),(114,238694),(117,238627),(129,238694),(130,238694),(137,238694),(138,238694),(145,238694),(146,238694),(153,238694),(154,238694),(169,107750),(170,238694),(178,238694),(181,238694),(185,107750),(186,238694),(202,238694),(205,238694)]),([7,1,6,18,120,420,508,833],[(56,9443),(72,9317),(96,9446),(128,9318),(180,205861),(188,206054),(196,206054),(204,206054),(224,42085),(260,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_93 : K_93.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_94 : List (List ℕ × List (ℕ × ℕ)) := [([7,1,6,18,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(81,205861),(82,206054),(98,206054),(106,206054),(114,206054),(117,206054),(129,206054),(130,206054),(138,206054),(141,205861),(145,206054),(146,206054),(158,34917),(170,206054),(173,206054),(177,206054),(178,206054),(185,206054),(186,206054),(201,201961),(206,238694)]),([7,1,6,18,120,420,833,889],[(56,9443),(72,9317),(104,206051),(220,206054),(224,205861),(236,206054),(244,206054),(252,34917),(260,206054)]),([7,1,6,18,120,420,833,903],[(56,9443),(72,9317),(116,234698),(156,34917),(176,42085),(220,206054),(228,206054),(248,34917)]),([7,1,6,18,120,420,839],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(62,206054),(73,206054),(74,206054),(81,206054),(82,206054),(85,206054),(98,206054),(106,206054),(109,206054),(114,206054),(117,206054),(129,206054),(130,206054),(137,206054),(138,206054),(141,206054),(145,206054),(146,206054),(158,34917),(170,206054),(173,206054),(177,206054),(178,206054),(181,206054),(185,206054),(186,206054),(201,201961),(206,238694)]),([7,1,6,18,120,420,851],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(81,205861),(82,206054),(98,206054),(106,206054),(114,206054),(117,206054),(129,206054),(130,206054),(138,206054),(141,205861),(145,206054),(146,206054),(170,206054),(173,206054),(177,205861),(178,206054),(186,206054),(189,206054),(201,201961),(206,238694)]),([7,1,6,18,120,420,889],[(138,34917),(158,34917),(205,34917)]),([7,1,6,18,120,421,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(81,205861),(82,206054),(98,206054),(106,206054),(114,206054),(117,206054),(130,206054),(133,206054),(138,206054),(141,205861),(145,206054),(146,206054),(158,34917),(170,206054),(173,206054),(177,206054),(178,206054),(185,206054),(186,206054),(201,201961),(206,238694)]),([7,1,6,18,120,422,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,102435),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(81,206054),(97,34917),(98,206054),(105,34917),(106,206054),(114,206054),(129,206054),(130,206054),(138,206054),(141,206054),(146,206054),(158,34917),(170,206054),(173,206054),(177,206054),(178,206054),(185,34917),(186,206054),(194,34917),(201,201961),(206,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_94 : K_94.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_95 : List (List ℕ × List (ℕ × ℕ)) := [([7,1,6,18,120,438,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(81,205861),(86,206053),(98,206054),(106,206054),(114,206054),(129,206054),(130,206054),(138,206054),(141,206054),(146,206054),(149,206054),(170,206054),(173,206054),(177,206054),(178,206054),(185,206054),(186,206054),(201,201961),(206,238694)]),([7,1,6,18,120,603,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(81,205861),(82,206054),(98,206054),(106,206054),(114,206054),(117,206054),(130,206054),(133,206054),(137,205861),(138,206054),(146,206054),(149,206054),(158,34917),(170,206054),(173,206054),(177,206054),(178,206054),(185,206054),(186,206054),(201,205030),(202,107750)]),([7,1,6,18,120,833,997],[(0,201961),(2,201961),(4,201961),(6,201961),(8,201961),(10,201961),(12,201961),(14,234697),(16,201961),(18,237766),(20,201961),(22,201961),(57,201961),(58,201961),(73,201961),(74,201961),(81,201961),(82,201961),(97,201961),(98,201961),(105,201961),(106,201961),(114,201961),(117,201961),(130,201961),(133,201961),(137,205030),(138,201961),(145,205030),(146,201961),(170,201961),(173,201961),(178,201961),(181,201961),(185,201961),(186,201961),(197,201961),(198,201961),(202,201961),(205,201961)]),([7,1,6,18,121,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(61,9446),(73,206054),(74,206054),(77,9446),(81,205861),(82,206054),(98,206054),(101,206054),(106,206054),(114,206054),(117,206054),(129,206054),(130,206054),(133,9446),(138,206054),(141,205861),(145,206054),(146,206054),(158,34917),(169,9446),(170,206054),(173,206054),(177,206054),(178,206054),(185,206054),(186,206054),(201,201961),(206,238694)]),([7,1,6,18,122,420,833],[(0,206054),(2,206054),(4,206054),(6,231461),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(82,206054),(97,37091),(98,206054),(106,206054),(114,206054),(117,206054),(129,206054),(130,206054),(138,206054),(145,206054),(146,206054),(158,37091),(170,206054),(173,206054),(177,37091),(178,206054),(185,206054),(186,206054),(194,37091),(201,201961),(206,238694)]),([7,1,6,18,126,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(73,206054),(74,206054),(82,206054),(85,206051),(98,206054),(106,206054),(109,206054),(114,206054),(117,206054),(129,206054),(130,206054),(137,206051),(138,206054),(145,206054),(146,206054),(170,206054),(173,206054),(177,206054),(178,206054),(185,206054),(186,206054),(201,201961),(206,238694)]),([7,1,6,18,420,833,903],[(0,234698),(2,234698),(4,234698),(6,234698),(8,234698),(10,234698),(12,234698),(14,234698),(16,234698),(18,234698),(20,234698),(22,206054),(57,234698),(58,234698),(73,234698),(74,234698),(81,37066),(82,234698),(97,234698),(98,234698),(106,234698),(109,37066),(113,234698),(114,234698),(130,234698),(133,234698),(137,234698),(138,234698),(145,234698),(146,234698),(153,234697),(158,234602),(170,234698),(173,234698),(178,234698),(181,234698),(186,234698),(193,34917)]),([7,1,6,19,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(61,206054),(73,206054),(74,206054),(77,206054),(81,205861),(82,206054),(98,206054),(101,206054),(106,206054),(114,206054),(117,206054),(129,206054),(130,206054),(133,206054),(138,206054),(141,205861),(145,206054),(146,206054),(158,34917),(169,206054),(170,206054),(173,206054),(177,206054),(178,206054),(185,206054),(186,206054),(201,201961),(206,238694)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_95 : K_95.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_96 : List (List ℕ × List (ℕ × ℕ)) := [([7,1,6,22,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(62,205861),(73,206054),(74,206054),(81,205861),(82,206054),(85,206054),(98,206054),(106,206054),(109,205861),(114,206054),(117,206054),(129,206054),(130,206054),(137,206054),(141,205861),(145,206054),(170,206054),(173,206054),(177,206054),(178,206054),(181,205861),(185,206054),(186,206054),(201,201961),(206,238627)]),([7,1,6,120,420,438,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(74,206054),(82,206054),(97,206054),(98,206054),(109,205861),(110,206053),(129,206054),(130,206054),(138,206054),(141,206054),(154,206054),(157,206054),(170,206054),(173,206054),(177,206054),(178,206054),(193,206054),(198,107750),(201,200937),(206,107750)]),([7,1,6,120,420,833,851],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(74,206054),(82,206054),(97,206054),(98,206054),(106,34917),(109,200746),(118,34917),(130,206054),(133,206054),(137,206054),(138,206054),(150,42211),(153,205030),(154,206054),(170,206054),(173,206054),(177,200746),(178,206054),(190,200937),(193,205030),(194,200937),(202,206054),(205,206054)]),([7,1,6,120,420,833,1005],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(74,206054),(82,206054),(97,206054),(98,206054),(106,102435),(109,205861),(118,102435),(130,206054),(133,206054),(137,206054),(138,206054),(153,201961),(158,238694),(170,206054),(173,206054),(178,206054),(181,205861),(189,206054),(194,206054),(197,206054),(202,206054),(205,206054)]),([7,1,7,18,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(61,206054),(73,206054),(74,206054),(77,206054),(81,205861),(82,206054),(98,206054),(101,206054),(106,206054),(114,206054),(117,206054),(129,206054),(130,206054),(133,206054),(138,206054),(141,205861),(145,206054),(146,206054),(158,34917),(169,206054),(170,206054),(173,206054),(177,206054),(178,206054),(185,206054),(186,206054),(201,201961),(206,238694)]),([7,1,18,22,120,420,833],[(0,205861),(2,205861),(4,205861),(6,205861),(8,205861),(10,205861),(12,205861),(14,37066),(16,205861),(18,205861),(20,205861),(22,205861),(57,205861),(58,205861),(62,205861),(73,205861),(74,205861),(81,205861),(82,205861),(85,205861),(98,205861),(109,206054),(129,205861),(130,205861),(137,205861),(138,205861),(141,205861),(146,205861),(149,205861),(158,204837),(170,205861),(173,205861),(177,205861),(178,205861),(181,205861),(185,205861),(186,205861),(201,201961),(206,238694)]),([7,1,18,120,126,420,833],[(86,206051),(150,100389),(157,205861),(185,206051),(193,205861),(201,201961),(206,238694)]),([7,1,18,120,420,833,839],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(74,206054),(82,37091),(85,206054),(97,206054),(98,206054),(105,206054),(106,206054),(118,34917),(130,206054),(133,206054),(134,206054),(137,206054),(138,206054),(142,206054),(150,42085),(153,205030),(154,206054),(158,206054),(170,206054),(173,206054),(177,206054),(178,205861),(186,205861),(193,205030),(198,205861),(201,206054),(202,206054),(205,206054)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_96 : K_96.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_97 : List (List ℕ × List (ℕ × ℕ)) := [([7,1,18,120,420,833,1017],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(74,206054),(82,231461),(85,206054),(97,206054),(98,206054),(105,206054),(106,206054),(118,34917),(130,206054),(133,206054),(137,206054),(138,206054),(153,201961),(158,238694),(170,206054),(173,206054),(178,205861),(181,206054),(186,206054),(189,206054),(197,206054),(198,205861),(202,206054),(205,206054)]),([7,1,18,120,420,839],[(1,206054),(3,206054),(5,206054),(7,206054),(9,42085),(11,42085),(13,206054),(15,206054),(17,206054),(19,206054),(59,206054),(63,206054),(75,42085),(79,206054),(87,206054),(99,206054),(103,206054),(107,206054),(111,206054),(115,42085),(119,42085),(131,206054),(135,206054),(139,206054),(143,206054),(147,42085),(151,42085),(155,206054),(159,206054)]),([7,1,22,120,420,833],[(1,205861),(3,205861),(5,205861),(7,205861),(13,205861),(15,205861),(17,205861),(19,205861),(59,205861),(63,205861),(79,205861),(87,206054),(99,205861),(103,205861),(107,205861),(111,205861),(119,205861),(131,205861),(135,205861),(139,205861),(143,205861),(155,205861),(159,205861)]),([7,6,7,18,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,206054),(58,206054),(61,206054),(73,206054),(74,206054),(77,206054),(81,206054),(82,206054),(98,206054),(101,206054),(106,206054),(114,206054),(117,206054),(129,206054),(130,206054),(133,206054),(137,206054),(138,206054),(145,206054),(146,206054),(158,34917),(169,206054),(170,206054),(173,206054),(178,206054),(181,206054),(185,206054),(186,206054),(201,201961),(206,238694)]),([7,6,18,19,120,420,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,206054),(12,206054),(14,234698),(16,206054),(18,206054),(20,206054),(22,206054),(57,205861),(58,206054),(62,206054),(73,205861),(74,206054),(81,206054),(82,206054),(85,206054),(98,206054),(105,9317),(106,206054),(109,206054),(114,206054),(130,206054),(133,205861),(137,206054),(138,206054),(141,206054),(145,206054),(146,206054),(169,206054),(170,206054),(177,206054),(178,206054),(181,206054),(186,206054),(189,206054),(201,201961),(206,238694)]),([7,6,18,120,121,420,833],[(78,9446),(86,9446),(130,34917),(145,9446),(150,34917),(158,34917),(189,9446),(201,201961),(206,238694)]),([7,6,18,120,420,421,833],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(20,206054),(22,206054),(57,205861),(58,206054),(74,206054),(82,206054),(85,206054),(98,206054),(101,205861),(105,206054),(106,206054),(114,9318),(130,206054),(133,205861),(137,206054),(138,206054),(154,206054),(157,206054),(169,206054),(170,206054),(177,206054),(178,206054),(197,9318),(198,107750),(205,206054),(206,107750)]),([7,6,18,120,420,833,1022],[(0,206054),(2,206054),(4,206054),(6,206054),(8,206054),(10,234698),(12,206054),(14,206054),(16,206054),(18,206054),(20,206054),(22,206054),(57,205861),(58,206054),(74,206054),(82,206054),(85,206054),(98,206054),(101,205861),(105,206054),(106,206054),(118,34917),(129,206054),(130,206054),(137,206054),(138,206054),(153,201961),(158,238694),(170,206054),(173,206054),(178,206054),(181,206054),(186,206054),(189,206054),(194,206054),(197,206054),(205,206054),(206,206054)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_97 : K_97.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_98 : List (List ℕ × List (ℕ × ℕ)) := [([7,6,18,121,420,833],[(1,9446),(3,9446),(5,9446),(7,9446),(13,9446),(15,9446),(17,9446),(19,9446),(59,9446),(63,9446),(79,9446),(87,9446),(99,9446),(103,9446),(107,9446),(111,9446),(131,9446),(135,9446),(139,9446),(143,9446),(155,9446),(159,9446)]),([7,6,19,120,420,833],[(1,206054),(3,206054),(5,206054),(7,206054),(9,9317),(11,9317),(13,206054),(15,206054),(17,206054),(19,206054),(59,206054),(63,206054),(75,9317),(79,206054),(87,206054),(99,206054),(103,206054),(107,206054),(111,206054),(115,9317),(119,9317),(131,206054),(135,206054),(139,206054),(143,206054),(147,9317),(151,9317),(155,206054),(159,206054)]),([7,7,18,120,420,833],[(1,206054),(3,206054),(5,206054),(7,206054),(9,9443),(11,9443),(13,206054),(15,206054),(17,206054),(19,206054),(59,206054),(63,206054),(79,206054),(83,9443),(87,206054),(99,206054),(103,206054),(107,206054),(111,206054),(115,9443),(119,9443),(131,206054),(135,206054),(139,206054),(143,206054),(147,9443),(151,9443),(155,206054),(159,206054)]),([8,1,6,18,120,420,833],[(1,206054),(3,206054),(5,206054),(7,206054),(9,206054),(11,206054),(17,206054),(19,206054),(21,206054),(23,206054),(59,206054),(63,206054),(75,206054),(79,206054),(83,206054),(87,206054),(103,206054),(111,206054),(119,206054),(131,206054),(135,206054),(139,206054),(143,206054),(147,206054),(151,206054),(171,206054),(175,206054),(179,206054),(183,206054),(187,206054),(191,206054),(203,206054),(207,206054)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_98 : K_98.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = (((((((K_0 ++ (K_1 ++ K_2)) ++ (K_3 ++ (K_4 ++ K_5))) ++ ((K_6 ++ (K_7 ++ K_8)) ++ (K_9 ++ (K_10 ++ K_11)))) ++ (((K_12 ++ (K_13 ++ K_14)) ++ (K_15 ++ (K_16 ++ K_17))) ++ ((K_18 ++ (K_19 ++ K_20)) ++ (K_21 ++ (K_22 ++ K_23))))) ++ ((((K_24 ++ (K_25 ++ K_26)) ++ (K_27 ++ (K_28 ++ K_29))) ++ ((K_30 ++ (K_31 ++ K_32)) ++ (K_33 ++ (K_34 ++ K_35)))) ++ (((K_36 ++ (K_37 ++ K_38)) ++ (K_39 ++ (K_40 ++ K_41))) ++ ((K_42 ++ (K_43 ++ K_44)) ++ ((K_45 ++ K_46) ++ (K_47 ++ K_48)))))) ++ (((((K_49 ++ (K_50 ++ K_51)) ++ (K_52 ++ (K_53 ++ K_54))) ++ ((K_55 ++ (K_56 ++ K_57)) ++ (K_58 ++ (K_59 ++ K_60)))) ++ (((K_61 ++ (K_62 ++ K_63)) ++ (K_64 ++ (K_65 ++ K_66))) ++ ((K_67 ++ (K_68 ++ K_69)) ++ ((K_70 ++ K_71) ++ (K_72 ++ K_73))))) ++ ((((K_74 ++ (K_75 ++ K_76)) ++ (K_77 ++ (K_78 ++ K_79))) ++ ((K_80 ++ (K_81 ++ K_82)) ++ (K_83 ++ (K_84 ++ K_85)))) ++ (((K_86 ++ (K_87 ++ K_88)) ++ (K_89 ++ (K_90 ++ K_91))) ++ ((K_92 ++ (K_93 ++ K_94)) ++ ((K_95 ++ K_96) ++ (K_97 ++ K_98)))))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app (all_app c_0 (all_app c_1 c_2)) (all_app c_3 (all_app c_4 c_5))) (all_app (all_app c_6 (all_app c_7 c_8)) (all_app c_9 (all_app c_10 c_11)))) (all_app (all_app (all_app c_12 (all_app c_13 c_14)) (all_app c_15 (all_app c_16 c_17))) (all_app (all_app c_18 (all_app c_19 c_20)) (all_app c_21 (all_app c_22 c_23))))) (all_app (all_app (all_app (all_app c_24 (all_app c_25 c_26)) (all_app c_27 (all_app c_28 c_29))) (all_app (all_app c_30 (all_app c_31 c_32)) (all_app c_33 (all_app c_34 c_35)))) (all_app (all_app (all_app c_36 (all_app c_37 c_38)) (all_app c_39 (all_app c_40 c_41))) (all_app (all_app c_42 (all_app c_43 c_44)) (all_app (all_app c_45 c_46) (all_app c_47 c_48)))))) (all_app (all_app (all_app (all_app (all_app c_49 (all_app c_50 c_51)) (all_app c_52 (all_app c_53 c_54))) (all_app (all_app c_55 (all_app c_56 c_57)) (all_app c_58 (all_app c_59 c_60)))) (all_app (all_app (all_app c_61 (all_app c_62 c_63)) (all_app c_64 (all_app c_65 c_66))) (all_app (all_app c_67 (all_app c_68 c_69)) (all_app (all_app c_70 c_71) (all_app c_72 c_73))))) (all_app (all_app (all_app (all_app c_74 (all_app c_75 c_76)) (all_app c_77 (all_app c_78 c_79))) (all_app (all_app c_80 (all_app c_81 c_82)) (all_app c_83 (all_app c_84 c_85)))) (all_app (all_app (all_app c_86 (all_app c_87 c_88)) (all_app c_89 (all_app c_90 c_91))) (all_app (all_app c_92 (all_app c_93 c_94)) (all_app (all_app c_95 c_96) (all_app c_97 c_98)))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coreLower (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 8) (hr : Matches C) : False := by
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
    refine ⟨pt 6 (pairCode (0,5)),pt 6 (pairCode (1,4)),?_⟩
    rw [he (0,5) (by decide +kernel),he (1,4) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 8 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end PEqualNP.Outside.L_meta_24645.Core

open PEqualNP.Outside.L_meta_24645.Core in
theorem PEqualNP.Outside.L_meta_24645 (C : PEqualNP.CircuitLowerBounds.Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ 8) : ¬ Matches C :=
  coreLower C hfan hsize
