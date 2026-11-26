import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24685.Core

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
  !((x 5 && (x 2 || x 3 || x 4)) || (x 1 && (x 0 || x 2)) || (x 3 && x 4))
def pairInput (i j : Fin 6) := List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)
theorem codeInputs : ∀ p : Fin 6 × Fin 6, List.ofFn (pt 6 (pairCode p)) = pairInput p.1 p.2 := by
  decide +kernel
theorem graphRow : ∀ i j : Fin 6, reference (pt 6 (pairCode (i,j))) =
    (34630389437 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel
def samplePairs : List (Fin 6 × Fin 6) := [(0, 1), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 5), (3, 4), (3, 5), (4, 5), (5, 5)]
def points := samplePairs.map pairCode

def Matches (C : Circuit) : Prop := ∀ p ∈ samplePairs, C.eval (pairInput p.1 p.2) =
  (34630389437 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)
theorem enc_congr_rows {n : Nat} (f g : BFn n) (l : List Nat)
    (h : ∀ v ∈ l, f (pt n v) = g (pt n v)) : encL f l = encL g l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [encL]
    rw [h a (by simp), ih (fun v hv => h v (by simp [hv]))]
def M_ : ℕ := 4095

def Y_ : ℕ := 2166

def XS_ : List ℕ := [3, 61, 200, 784, 1312, 3714]

def PD_ : List (ℕ × ℕ) := [(1, 1101), (2, 619), (3, 376), (4, 241), (5, 53), (6, 23), (7, 6), (8, 14), (9, 2), (11, 1)]

def PM_ : List (ℕ × ℕ) := [(0, 2166), (3, 2166), (7, 2166), (8, 2166), (9, 2166), (10, 2166)]

def G_ : List (List ℕ) := [[0,1,2,3,5,4,6,7,8,10,9,11]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,9,61,1936] BT.lf) [3,9,61,1968] BT.lf) [3,61,137,1840] (BT.nd (BT.nd BT.lf [3,61,203,1981] BT.lf) [3,61,649,1312] BT.lf)) [3,137,189,1840] (BT.nd (BT.nd (BT.nd BT.lf [3,189,203,1981] BT.lf) [3,200,1853,3971] BT.lf) [3,456,1853,3715] (BT.nd (BT.nd BT.lf [3,784,1513,3723] BT.lf) [3,793,1512,3715] BT.lf))) [3,793,1512,3723] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,793,1513,3714] BT.lf) [3,797,1512,3715] BT.lf) [3,829,1480,3715] (BT.nd (BT.nd BT.lf [4,1,61,136,1840] BT.lf) [4,1,784,1512,3722] BT.lf)) [4,1,792,1512,3714] (BT.nd (BT.nd (BT.nd BT.lf [4,3,61,136,1853] BT.lf) [4,3,61,200,1981] BT.lf) [4,3,189,200,1981] (BT.nd (BT.nd BT.lf [4,3,200,1853,3970] BT.lf) [4,3,456,1853,3714] BT.lf)))) [4,3,793,1512,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,3,793,1515,3714] BT.lf) [4,3,797,1512,3714] BT.lf) [4,3,829,1480,3714] (BT.nd (BT.nd BT.lf [4,9,61,128,1840] BT.lf) [4,9,61,640,1312] BT.lf)) [4,9,61,784,1440] (BT.nd (BT.nd (BT.nd BT.lf [4,9,381,784,1512] BT.lf) [4,9,784,1440,3714] BT.lf) [4,9,784,1512,3714] (BT.nd (BT.nd BT.lf [4,9,784,1512,3715] BT.lf) [4,9,784,1512,3723] BT.lf))) [4,9,784,1513,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,9,784,2583,3714] BT.lf) [4,9,793,1512,3714] BT.lf) [4,9,984,2783,3714] (BT.nd (BT.nd BT.lf [4,16,984,1341,3715] BT.lf) [4,29,784,1512,3715] BT.lf)) [4,60,200,1853,3714] (BT.nd (BT.nd (BT.nd BT.lf [4,61,128,203,1853] BT.lf) [4,61,131,200,1853] BT.lf) [4,61,137,784,1312] (BT.nd BT.lf [4,61,189,203,1840] BT.lf))))) [4,61,200,380,1853] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,61,200,1792,3715] BT.lf) [4,61,200,1840,3971] BT.lf) [4,61,200,1853,3715] (BT.nd (BT.nd BT.lf [4,61,200,1916] BT.lf) [4,61,200,2179] BT.lf)) [4,61,200,2242,3715] (BT.nd (BT.nd (BT.nd BT.lf [4,61,200,2303,3715] BT.lf) [4,61,201,1840,3775] BT.lf) [4,61,201,1853,3714] (BT.nd (BT.nd BT.lf [4,61,203,640,1341] BT.lf) [4,61,203,701,1312] BT.lf))) [4,61,203,784,1469] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,61,203,829,1440] BT.lf) [4,61,203,1936] BT.lf) [4,61,203,1968] (BT.nd (BT.nd BT.lf [4,61,456,1840,3715] BT.lf) [4,61,712,1341,3715] BT.lf)) [4,61,784,1440,3787] (BT.nd (BT.nd (BT.nd BT.lf [4,61,784,1480,3715] BT.lf) [4,61,784,1512,3723] BT.lf) [4,61,792,1512,3715] (BT.nd BT.lf [4,61,1736,3715] BT.lf)))) [4,61,1853,3715,3895] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,61,2040,4019] BT.lf) [4,63,200,1853,3715] BT.lf) [4,63,203,1853,3714] (BT.nd (BT.nd BT.lf [4,137,189,784,1312] BT.lf) [4,137,784,1312,3714] BT.lf)) [4,189,203,784,1469] (BT.nd (BT.nd (BT.nd BT.lf [4,189,203,1840] BT.lf) [4,189,784,1312,3787] BT.lf) [4,200,253,1853,3715] (BT.nd (BT.nd BT.lf [4,200,256,1853,3715] BT.lf) [4,200,259,1853,3714] BT.lf))) [4,200,573,1853,3715] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,200,768,1341,3715] BT.lf) [4,200,784,1321,3715] BT.lf) [4,200,784,1321,3723] (BT.nd (BT.nd BT.lf [4,200,784,1325,3715] BT.lf) [4,200,784,1341,3971] BT.lf)) [4,200,793,1321,3714] (BT.nd (BT.nd (BT.nd BT.lf [4,200,797,2783,3715] BT.lf) [4,200,829,2815,3715] BT.lf) [4,200,1597,3715] (BT.nd BT.lf [4,200,1792,3715,4034] BT.lf)))))) [4,200,1853,3714,4035] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,200,1853,3715,3775] BT.lf) [4,200,1853,3715,4034] BT.lf) [4,201,784,1312,3723] (BT.nd (BT.nd BT.lf [4,201,784,1321,3714] BT.lf) [4,203,793,1512,3714] BT.lf)) [4,253,784,1312,3723] (BT.nd (BT.nd (BT.nd BT.lf [4,456,784,1341,3715] BT.lf) [4,784,793,1512,3714] BT.lf) [4,784,1480,3715,4034] (BT.nd (BT.nd BT.lf [4,784,1512,3714,3723] BT.lf) [4,784,1512,3714,4086] BT.lf))) [4,784,1512,3715,4066] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,784,1512,3722,3723] BT.lf) [4,792,1512,3714,3715] BT.lf) [4,829,984,1512,3715] (BT.nd (BT.nd BT.lf [5,1,8,784,1512,3714] BT.lf) [5,1,61,136,784,1312] BT.lf)) [5,1,61,200,1840,3775] (BT.nd (BT.nd (BT.nd BT.lf [5,1,61,200,1853,3714] BT.lf) [5,1,136,784,1312,3714] BT.lf) [5,1,200,784,1312,3722] (BT.nd BT.lf [5,1,200,784,1320,3714] BT.lf)))) [5,3,9,784,1512,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3,9,784,1515,3714] BT.lf) [5,3,16,984,1341,3714] BT.lf) [5,3,29,784,1512,3714] (BT.nd (BT.nd BT.lf [5,3,61,128,200,1853] BT.lf) [5,3,61,136,784,1341] BT.lf)) [5,3,61,136,1840] (BT.nd (BT.nd (BT.nd BT.lf [5,3,61,136,1840,3714] BT.lf) [5,3,61,189,200,1840] BT.lf) [5,3,61,200,381,1853] (BT.nd (BT.nd BT.lf [5,3,61,200,640,1341] BT.lf) [5,3,61,200,701,1312] BT.lf))) [5,3,61,200,784,1469] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3,61,200,829,1440] BT.lf) [5,3,61,200,1792,3714] BT.lf) [5,3,61,200,1808,4002] (BT.nd (BT.nd BT.lf [5,3,61,200,1840,3722] BT.lf) [5,3,61,200,1840,3970] BT.lf)) [5,3,61,200,1848,3714] (BT.nd (BT.nd (BT.nd BT.lf [5,3,61,200,1853,3714] BT.lf) [5,3,61,200,1853,3715] BT.lf) [5,3,61,200,1853,3775] (BT.nd BT.lf [5,3,61,200,1853,3986] BT.lf))))) [5,3,61,200,1853,4018] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3,61,200,1853,4031] BT.lf) [5,3,61,200,1917] BT.lf) [5,3,61,200,1936] (BT.nd (BT.nd BT.lf [5,3,61,200,1968] BT.lf) [5,3,61,200,2178] BT.lf)) [5,3,61,200,2242,3714] (BT.nd (BT.nd (BT.nd BT.lf [5,3,61,200,2303,3714] BT.lf) [5,3,61,203,1853,3714] BT.lf) [5,3,61,456,1840,3714] (BT.nd (BT.nd BT.lf [5,3,61,712,1312,3986] BT.lf) [5,3,61,712,1341,3714] BT.lf))) [5,3,61,784,1440,3786] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3,61,784,1480,3714] BT.lf) [5,3,61,784,1512,3722] BT.lf) [5,3,61,792,1512,3714] (BT.nd (BT.nd BT.lf [5,3,61,1736,3714] BT.lf) [5,3,61,1853,3714,3895] BT.lf)) [5,3,61,2040,4018] (BT.nd (BT.nd (BT.nd BT.lf [5,3,63,200,1853,3714] BT.lf) [5,3,189,200,784,1469] BT.lf) [5,3,189,200,1840] (BT.nd BT.lf [5,3,189,784,1312,3786] BT.lf)))) [5,3,200,253,1853,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3,200,256,1853,3714] BT.lf) [5,3,200,573,1853,3714] BT.lf) [5,3,200,768,1341,3714] (BT.nd (BT.nd BT.lf [5,3,200,784,1321,3714] BT.lf) [5,3,200,784,1325,3714] BT.lf)) [5,3,200,784,1341,3970] (BT.nd (BT.nd (BT.nd BT.lf [5,3,200,797,2783,3714] BT.lf) [5,3,200,829,2815,3714] BT.lf) [5,3,200,1597,3714] (BT.nd (BT.nd BT.lf [5,3,200,1792,3714,4034] BT.lf) [5,3,200,1853,3714,3775] BT.lf))) [5,3,200,1853,3714,4034] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3,203,784,1321,3714] BT.lf) [5,3,253,784,1312,3722] BT.lf) [5,3,456,784,1341,3714] (BT.nd (BT.nd BT.lf [5,3,784,1480,3714,4034] BT.lf) [5,3,784,1512,3714,3722] BT.lf)) [5,3,784,1512,3714,4066] (BT.nd (BT.nd (BT.nd BT.lf [5,3,784,1512,3722] BT.lf) [5,3,792,1512,3714] BT.lf) [5,3,829,984,1512,3714] (BT.nd BT.lf [5,8,61,784,1512,3715] BT.lf))))))) [5,8,253,784,1312,3715] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,8,784,1512,3714,3715] BT.lf) [5,9,61,128,784,1312] BT.lf) [5,9,61,200,1840,3714] (BT.nd (BT.nd BT.lf [5,9,61,784,1512,3714] BT.lf) [5,9,128,784,1312,3714] BT.lf)) [5,9,200,381,784,1312] (BT.nd (BT.nd (BT.nd BT.lf [5,9,200,784,1312,3714] BT.lf) [5,9,200,784,1312,3715] BT.lf) [5,9,200,784,1312,3723] (BT.nd (BT.nd BT.lf [5,9,200,784,1321,3714] BT.lf) [5,9,200,784,1512,3714] BT.lf))) [5,9,200,784,2783,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,9,201,784,1312,3714] BT.lf) [5,9,203,784,1512,3714] BT.lf) [5,9,253,784,1312,3714] (BT.nd (BT.nd BT.lf [5,9,784,984,1312,3714] BT.lf) [5,9,784,1312,3714,3895] BT.lf)) [5,9,784,1512,3714] (BT.nd (BT.nd (BT.nd BT.lf [5,11,61,200,1840,3714] BT.lf) [5,11,61,784,1512,3714] BT.lf) [5,11,253,784,1312,3714] (BT.nd BT.lf [5,11,784,1512,3714] BT.lf)))) [5,16,61,984,1312,3715] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16,200,784,1341,3715] BT.lf) [5,25,784,984,1312,3714] BT.lf) [5,29,200,784,1312,3715] (BT.nd (BT.nd BT.lf [5,29,200,784,2783,3715] BT.lf) [5,48,61,200,1840,3715] BT.lf)) [5,60,61,200,1840,3714] (BT.nd (BT.nd (BT.nd BT.lf [5,60,200,784,1341,3714] BT.lf) [5,60,200,1840,3714] BT.lf) [5,61,61,200,1840,3715] (BT.nd (BT.nd BT.lf [5,61,63,200,1840,3715] BT.lf) [5,61,63,203,1840,3714] BT.lf))) [5,61,128,203,784,1341] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,128,203,1840] BT.lf) [5,61,128,784,1312,3787] BT.lf) [5,61,131,200,784,1341] (BT.nd (BT.nd BT.lf [5,61,131,200,1840] BT.lf) [5,61,136,784,1312,3715] BT.lf)) [5,61,189,203,784,1312] (BT.nd (BT.nd (BT.nd BT.lf [5,61,200,203,1853,3714] BT.lf) [5,61,200,253,1840,3715] BT.lf) [5,61,200,256,1840,3715] (BT.nd BT.lf [5,61,200,259,1840,3714] BT.lf))))) [5,61,200,380,784,1312] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,200,380,784,1341] BT.lf) [5,61,200,380,784,1512] BT.lf) [5,61,200,380,784,2783] (BT.nd (BT.nd BT.lf [5,61,200,380,1840] BT.lf) [5,61,200,512,1341,3715] BT.lf)) [5,61,200,573,1312,3715] (BT.nd (BT.nd (BT.nd BT.lf [5,61,200,768,1312,3715] BT.lf) [5,61,200,784,1312,3715] BT.lf) [5,61,200,784,1312,3723] (BT.nd (BT.nd BT.lf [5,61,200,784,1312,3971] BT.lf) [5,61,200,784,1313,3715] BT.lf))) [5,61,200,784,1320,3715] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,200,784,1341,3715] BT.lf) [5,61,200,784,1404] BT.lf) [5,61,200,784,1440,3715] (BT.nd (BT.nd BT.lf [5,61,200,784,1512,3715] BT.lf) [5,61,200,784,1824,3715] BT.lf)) [5,61,200,784,1853,3715] (BT.nd (BT.nd (BT.nd BT.lf [5,61,200,784,2583,3715] BT.lf) [5,61,200,784,2691] BT.lf) [5,61,200,784,2754,3715] (BT.nd BT.lf [5,61,200,784,2783,3715] BT.lf)))) [5,61,200,784,2815,3715] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,200,785,1313,3714] BT.lf) [5,61,200,829,1341,3715] BT.lf) [5,61,200,829,1512,3715] (BT.nd (BT.nd BT.lf [5,61,200,829,1840,3715] BT.lf) [5,61,200,829,1853,3715] BT.lf)) [5,61,200,829,2783,3715] (BT.nd (BT.nd (BT.nd BT.lf [5,61,200,984,1512,3715] BT.lf) [5,61,200,984,2783,3715] BT.lf) [5,61,200,1536,3715] (BT.nd (BT.nd BT.lf [5,61,200,1808,3715] BT.lf) [5,61,200,1840,1853,3715] BT.lf))) [5,61,200,1840,3714,4035] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,200,1840,3715] BT.lf) [5,61,200,1840,3715,3775] BT.lf) [5,61,200,1840,3715,4034] (BT.nd (BT.nd BT.lf [5,61,200,1840,3987] BT.lf) [5,61,200,1840,4019] BT.lf)) [5,61,200,1853,3714,3715] (BT.nd (BT.nd (BT.nd BT.lf [5,61,200,1853,3714,4092] BT.lf) [5,61,200,1853,3715] BT.lf) [5,61,200,2040,3715] (BT.nd BT.lf [5,61,200,2255,3715] BT.lf)))))) [5,61,200,2783,3311,3715] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,201,381,784,1312] BT.lf) [5,61,201,784,1312,3714] BT.lf) [5,61,201,784,1312,3715] (BT.nd (BT.nd BT.lf [5,61,201,784,1312,3775] BT.lf) [5,61,201,784,1313,3714] BT.lf)) [5,61,201,784,1341,3714] (BT.nd (BT.nd (BT.nd BT.lf [5,61,201,784,1512,3714] BT.lf) [5,61,201,784,1513,3714] BT.lf) [5,61,201,784,2783,3714] (BT.nd (BT.nd BT.lf [5,61,201,1840,3714] BT.lf) [5,61,203,253,1840,3714] BT.lf))) [5,61,203,381,784,1512] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,203,383,784,1312] BT.lf) [5,61,203,640,1312] BT.lf) [5,61,203,784,1312,3712] (BT.nd (BT.nd BT.lf [5,61,203,784,1440] BT.lf) [5,61,203,784,1440,3714] BT.lf)) [5,61,203,784,1512,3714] (BT.nd (BT.nd (BT.nd BT.lf [5,61,203,784,1512,3715] BT.lf) [5,61,203,784,2583,3714] BT.lf) [5,61,203,787,1315,3714] (BT.nd BT.lf [5,61,203,829,1512,3714] BT.lf)))) [5,61,203,984,2783,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,203,1843,3714] BT.lf) [5,61,203,2040,3714] BT.lf) [5,61,380,784,984,1312] (BT.nd (BT.nd BT.lf [5,61,380,784,1312,3895] BT.lf) [5,61,456,784,1312,3715] BT.lf)) [5,61,712,784,1312,3715] (BT.nd (BT.nd (BT.nd BT.lf [5,61,712,1312,3715] BT.lf) [5,61,784,984,1312,3715] BT.lf) [5,61,784,984,1341,3715] (BT.nd (BT.nd BT.lf [5,61,784,984,1512,3715] BT.lf) [5,61,784,984,2783,3715] BT.lf))) [5,61,784,985,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,784,1312,2040,3715] BT.lf) [5,61,784,1312,2583,3715] BT.lf) [5,61,784,1312,3714,3894] (BT.nd (BT.nd BT.lf [5,61,784,1312,3715,3895] BT.lf) [5,61,784,1315,1512,3715] BT.lf)) [5,61,784,1341,3715,3895] (BT.nd (BT.nd (BT.nd BT.lf [5,61,784,1512,1840,3715] BT.lf) [5,61,784,1512,2783,3715] BT.lf) [5,61,784,1512,3714,3787] (BT.nd BT.lf [5,61,784,1512,3714,3892] BT.lf))))) [5,61,784,1512,3715,3786] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61,784,1512,3715,3787] BT.lf) [5,61,784,1512,3715,3895] BT.lf) [5,61,784,1512,3715,4002] (BT.nd (BT.nd BT.lf [5,61,784,1512,3715,4003] BT.lf) [5,61,784,1512,4003] BT.lf)) [5,61,784,2783,3715,3895] (BT.nd (BT.nd (BT.nd BT.lf [5,61,984,1840,3715] BT.lf) [5,61,1840,2040,3715] BT.lf) [5,61,1840,3715,3895] (BT.nd (BT.nd BT.lf [5,61,1843,2040,3714] BT.lf) [5,63,200,784,1341,3715] BT.lf))) [5,63,201,784,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,63,203,784,1341,3714] BT.lf) [5,63,203,1840,3714] BT.lf) [5,136,784,1312,3714,3715] (BT.nd (BT.nd BT.lf [5,189,200,784,1312,3715] BT.lf) [5,189,203,784,1312] BT.lf)) [5,189,203,784,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [5,200,203,784,1321,3714] BT.lf) [5,200,253,784,1341,3715] BT.lf) [5,200,256,784,1341,3715] (BT.nd BT.lf [5,200,259,784,1341,3714] BT.lf)))) [5,200,317,784,1312,3715] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,200,380,784,829,1312] BT.lf) [5,200,380,784,1312,4034] BT.lf) [5,200,573,784,1312,3715] (BT.nd (BT.nd BT.lf [5,200,573,1312,3715] BT.lf) [5,200,768,1312,3715,4034] BT.lf)) [5,200,784,793,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [5,200,784,829,1312,3715] BT.lf) [5,200,784,829,1512,3715] BT.lf) [5,200,784,829,2783,3715] (BT.nd (BT.nd BT.lf [5,200,784,1312,1853,3715] BT.lf) [5,200,784,1312,2754,3715] BT.lf))) [5,200,784,1312,3714,3723] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,200,784,1312,3714,4086] BT.lf) [5,200,784,1312,3715,4034] BT.lf) [5,200,784,1312,3715,4050] (BT.nd (BT.nd BT.lf [5,200,784,1312,3722,3723] BT.lf) [5,200,784,1315,1341,3715] BT.lf)) [5,200,784,1320,3714,3715] (BT.nd (BT.nd (BT.nd BT.lf [5,200,784,1341,1512,3715] BT.lf) [5,200,784,1341,2783,3715] BT.lf) [5,200,784,1341,3714,4035] (BT.nd BT.lf [5,200,784,1341,3715,3775] BT.lf)))))))) [5,200,784,1341,3715,4002] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,200,784,1341,3715,4003] BT.lf) [5,200,784,1341,3715,4034] BT.lf) [5,200,784,1512,3715,4034] (BT.nd (BT.nd BT.lf [5,200,784,2783,3715,4034] BT.lf) [5,200,1840,3714,4034,4035] BT.lf)) [5,200,1840,3714,4035] (BT.nd (BT.nd (BT.nd BT.lf [5,200,1840,3715,4034] BT.lf) [5,201,784,829,1312,3714] BT.lf) [5,201,784,1312,3714,3775] (BT.nd (BT.nd BT.lf [5,201,784,1312,3714,4034] BT.lf) [5,203,784,829,1512,3714] BT.lf))) [5,203,784,1341,1512,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,203,784,1512,3714,4034] BT.lf) [5,784,829,984,1312,3715] BT.lf) [5,784,829,1312,1512,3715] (BT.nd (BT.nd BT.lf [5,784,829,1312,3715,3895] BT.lf) [5,784,984,1312,3715,4034] BT.lf)) [5,784,1312,3715,3895,4034] (BT.nd (BT.nd (BT.nd BT.lf [6,0,61,200,784,1312,3715] BT.lf) [6,1,8,200,784,1312,3714] BT.lf) [6,1,61,200,381,784,1312] (BT.nd (BT.nd BT.lf [6,1,61,200,784,1312,3714] BT.lf) [6,1,61,200,784,1312,3715] BT.lf)))) [6,1,61,200,784,1312,3775] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1,61,200,784,1313,3714] BT.lf) [6,1,61,200,784,1341,3714] BT.lf) [6,1,61,200,784,1512,3714] (BT.nd (BT.nd BT.lf [6,1,61,200,784,2783,3714] BT.lf) [6,1,61,200,1840,3714] BT.lf)) [6,1,61,201,784,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,1,61,784,984,1312,3714] BT.lf) [6,1,61,784,1312,3714,3895] BT.lf) [6,1,63,200,784,1312,3714] (BT.nd (BT.nd BT.lf [6,1,200,784,829,1312,3714] BT.lf) [6,1,200,784,1312,3714,3775] BT.lf))) [6,1,200,784,1312,3714,4034] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2,61,200,784,1312,3715] BT.lf) [6,2,61,203,784,1312,3714] BT.lf) [6,3,8,61,200,1840,3714] (BT.nd (BT.nd BT.lf [6,3,8,61,784,1512,3714] BT.lf) [6,3,8,253,784,1312,3714] BT.lf)) [6,3,8,784,1512,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,3,9,200,784,1312,3714] BT.lf) [6,3,9,203,784,1312,3714] BT.lf) [6,3,16,61,984,1312,3714] (BT.nd BT.lf [6,3,16,200,784,1341,3714] BT.lf))))) [6,3,29,200,784,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,29,200,784,2783,3714] BT.lf) [6,3,48,61,200,1840,3714] BT.lf) [6,3,61,61,200,1840,3714] (BT.nd (BT.nd BT.lf [6,3,61,63,200,1840,3714] BT.lf) [6,3,61,128,200,784,1341] BT.lf)) [6,3,61,128,200,1840] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,128,784,1312,3786] BT.lf) [6,3,61,136,784,1312] BT.lf) [6,3,61,136,784,1312,3714] (BT.nd (BT.nd BT.lf [6,3,61,189,200,784,1312] BT.lf) [6,3,61,200,253,1840,3714] BT.lf))) [6,3,61,200,256,1840,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,380,784,1312] BT.lf) [6,3,61,200,381,784,1312] BT.lf) [6,3,61,200,381,784,1341] (BT.nd (BT.nd BT.lf [6,3,61,200,381,784,1512] BT.lf) [6,3,61,200,381,784,2783] BT.lf)) [6,3,61,200,381,1840] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,383,784,1312] BT.lf) [6,3,61,200,512,1312,3986] BT.lf) [6,3,61,200,512,1341,3714] (BT.nd BT.lf [6,3,61,200,573,1312,3714] BT.lf)))) [6,3,61,200,640,1312] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,768,1312,3714] BT.lf) [6,3,61,200,784,1312,3712] BT.lf) [6,3,61,200,784,1312,3714] (BT.nd (BT.nd BT.lf [6,3,61,200,784,1312,3715] BT.lf) [6,3,61,200,784,1312,3722] BT.lf)) [6,3,61,200,784,1312,3970] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,784,1313,3714] BT.lf) [6,3,61,200,784,1315,3715] BT.lf) [6,3,61,200,784,1320,3714] (BT.nd (BT.nd BT.lf [6,3,61,200,784,1341,3714] BT.lf) [6,3,61,200,784,1341,3715] BT.lf))) [6,3,61,200,784,1341,3775] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,784,1341,3986] BT.lf) [6,3,61,200,784,1341,4002] BT.lf) [6,3,61,200,784,1341,4031] (BT.nd (BT.nd BT.lf [6,3,61,200,784,1405] BT.lf) [6,3,61,200,784,1440] BT.lf)) [6,3,61,200,784,1440,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,784,1512,3714] BT.lf) [6,3,61,200,784,1512,3715] BT.lf) [6,3,61,200,784,1824,3714] (BT.nd BT.lf [6,3,61,200,784,1853,3714] BT.lf)))))) [6,3,61,200,784,2583,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,784,2690] BT.lf) [6,3,61,200,784,2754,3714] BT.lf) [6,3,61,200,784,2783,3714] (BT.nd (BT.nd BT.lf [6,3,61,200,784,2783,3715] BT.lf) [6,3,61,200,784,2815,3714] BT.lf)) [6,3,61,200,787,1315,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,829,1341,3714] BT.lf) [6,3,61,200,829,1512,3714] BT.lf) [6,3,61,200,829,1840,3714] (BT.nd (BT.nd BT.lf [6,3,61,200,829,1853,3714] BT.lf) [6,3,61,200,829,2783,3714] BT.lf))) [6,3,61,200,984,1512,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,984,2783,3714] BT.lf) [6,3,61,200,1536,3714] BT.lf) [6,3,61,200,1808,3714] (BT.nd (BT.nd BT.lf [6,3,61,200,1840,1853,3714] BT.lf) [6,3,61,200,1840,3714] BT.lf)) [6,3,61,200,1840,3714,3775] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,1840,3714,4034] BT.lf) [6,3,61,200,1840,3715] BT.lf) [6,3,61,200,1840,3775] (BT.nd BT.lf [6,3,61,200,1840,3986] BT.lf)))) [6,3,61,200,1840,4018] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,200,1843,3714] BT.lf) [6,3,61,200,1853,3714] BT.lf) [6,3,61,200,2040,3714] (BT.nd (BT.nd BT.lf [6,3,61,200,2255,3714] BT.lf) [6,3,61,200,2783,3311,3714] BT.lf)) [6,3,61,201,784,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,203,381,784,1312] BT.lf) [6,3,61,203,784,1312,3714] BT.lf) [6,3,61,203,784,1312,3715] (BT.nd (BT.nd BT.lf [6,3,61,203,784,1315,3714] BT.lf) [6,3,61,203,784,1341,3714] BT.lf))) [6,3,61,203,784,1512,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,203,784,1515,3714] BT.lf) [6,3,61,203,784,2783,3714] BT.lf) [6,3,61,203,1840,3714] (BT.nd (BT.nd BT.lf [6,3,61,381,784,984,1312] BT.lf) [6,3,61,381,784,1312,3895] BT.lf)) [6,3,61,456,784,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,712,784,1312,3714] BT.lf) [6,3,61,712,1312,3714] BT.lf) [6,3,61,784,984,1312,3714] (BT.nd BT.lf [6,3,61,784,984,1312,3715] BT.lf))))) [6,3,61,784,984,1341,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,784,984,1512,3714] BT.lf) [6,3,61,784,984,2783,3714] BT.lf) [6,3,61,784,987,1312,3714] (BT.nd (BT.nd BT.lf [6,3,61,784,1312,2040,3714] BT.lf) [6,3,61,784,1312,2583,3714] BT.lf)) [6,3,61,784,1312,3714,3892] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,784,1312,3714,3895] BT.lf) [6,3,61,784,1312,3715,3895] BT.lf) [6,3,61,784,1315,1512,3714] (BT.nd (BT.nd BT.lf [6,3,61,784,1341,3714,3895] BT.lf) [6,3,61,784,1512,1840,3714] BT.lf))) [6,3,61,784,1512,2783,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,784,1512,3714,3786] BT.lf) [6,3,61,784,1512,3714,3895] BT.lf) [6,3,61,784,1512,3714,4002] (BT.nd (BT.nd BT.lf [6,3,61,784,1512,4002] BT.lf) [6,3,61,784,2783,3714,3895] BT.lf)) [6,3,61,984,1840,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,3,61,1840,2040,3714] BT.lf) [6,3,61,1840,3714,3895] BT.lf) [6,3,63,200,784,1341,3714] (BT.nd BT.lf [6,3,63,200,1840,3714] BT.lf)))) [6,3,136,784,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,189,200,784,1312] BT.lf) [6,3,189,200,784,1312,3714] BT.lf) [6,3,200,253,784,1341,3714] (BT.nd (BT.nd BT.lf [6,3,200,256,784,1341,3714] BT.lf) [6,3,200,317,784,1312,3714] BT.lf)) [6,3,200,381,784,829,1312] (BT.nd (BT.nd (BT.nd BT.lf [6,3,200,381,784,1312,4034] BT.lf) [6,3,200,573,784,1312,3714] BT.lf) [6,3,200,573,1312,3714] (BT.nd (BT.nd BT.lf [6,3,200,768,1312,3714,4034] BT.lf) [6,3,200,784,829,1312,3714] BT.lf))) [6,3,200,784,829,1312,3715] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,200,784,829,1512,3714] BT.lf) [6,3,200,784,829,2783,3714] BT.lf) [6,3,200,784,1312,1853,3714] (BT.nd (BT.nd BT.lf [6,3,200,784,1312,2754,3714] BT.lf) [6,3,200,784,1312,3714,3722] BT.lf)) [6,3,200,784,1312,3714,4034] (BT.nd (BT.nd (BT.nd BT.lf [6,3,200,784,1312,3714,4050] BT.lf) [6,3,200,784,1312,3715,4034] BT.lf) [6,3,200,784,1312,3722] (BT.nd BT.lf [6,3,200,784,1315,1341,3714] BT.lf))))))) [6,3,200,784,1320,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,200,784,1341,1512,3714] BT.lf) [6,3,200,784,1341,2783,3714] BT.lf) [6,3,200,784,1341,3714,3775] (BT.nd (BT.nd BT.lf [6,3,200,784,1341,3714,4002] BT.lf) [6,3,200,784,1341,3714,4034] BT.lf)) [6,3,200,784,1512,3714,4034] (BT.nd (BT.nd (BT.nd BT.lf [6,3,200,784,2783,3714,4034] BT.lf) [6,3,200,1840,3714,3775] BT.lf) [6,3,200,1840,3714,4034] (BT.nd (BT.nd BT.lf [6,3,203,784,829,1312,3714] BT.lf) [6,3,203,784,1312,3714,4034] BT.lf))) [6,3,784,829,984,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,3,784,829,1312,1512,3714] BT.lf) [6,3,784,829,1312,3714,3895] BT.lf) [6,3,784,984,1312,3714,4034] (BT.nd (BT.nd BT.lf [6,3,784,1312,3714,3895,4034] BT.lf) [6,8,61,200,784,1312,3715] BT.lf)) [6,8,200,784,1312,3714,3715] (BT.nd (BT.nd (BT.nd BT.lf [6,9,61,200,784,1312,3714] BT.lf) [6,9,200,203,784,1312,3714] BT.lf) [6,9,200,784,1312,3714] (BT.nd BT.lf [6,11,61,200,784,1312,3714] BT.lf)))) [6,11,200,784,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,16,61,200,784,1312,3715] BT.lf) [6,60,61,200,784,1312,3714] BT.lf) [6,60,200,784,1312,3714] (BT.nd (BT.nd BT.lf [6,61,61,200,784,1312,3715] BT.lf) [6,61,63,200,784,1312,3715] BT.lf)) [6,61,63,203,784,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,61,128,200,784,1312,3715] BT.lf) [6,61,128,203,784,1312] BT.lf) [6,61,128,203,784,1312,3714] (BT.nd (BT.nd BT.lf [6,61,131,200,784,1312] BT.lf) [6,61,131,200,784,1312,3714] BT.lf))) [6,61,200,200,784,1312,3715] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,201,784,1312,3714] BT.lf) [6,61,200,203,381,784,1312] BT.lf) [6,61,200,203,784,1312,3714] (BT.nd (BT.nd BT.lf [6,61,200,203,784,1312,3715] BT.lf) [6,61,200,203,784,1341,3714] BT.lf)) [6,61,200,203,784,1512,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,203,784,2783,3714] BT.lf) [6,61,200,203,1840,3714] BT.lf) [6,61,200,253,784,1312,3715] (BT.nd BT.lf [6,61,200,256,784,1312,3715] BT.lf))))) [6,61,200,259,784,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,380,784,1312] BT.lf) [6,61,200,380,784,1312,3714] BT.lf) [6,61,200,380,784,1312,3715] (BT.nd (BT.nd BT.lf [6,61,200,381,784,1312,3715] BT.lf) [6,61,200,381,784,1312,4092] BT.lf)) [6,61,200,512,784,1312,3715] (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,512,1312,3715] BT.lf) [6,61,200,515,784,1312,3714] BT.lf) [6,61,200,784,784,1312,3715] (BT.nd (BT.nd BT.lf [6,61,200,784,785,1312,3714] BT.lf) [6,61,200,784,787,1312,3715] BT.lf))) [6,61,200,784,829,1312,3715] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,784,984,1312,3715] BT.lf) [6,61,200,784,1312,1840,3715] BT.lf) [6,61,200,784,1312,2783,3715] (BT.nd (BT.nd BT.lf [6,61,200,784,1312,3712,4092] BT.lf) [6,61,200,784,1312,3714,3715] BT.lf)) [6,61,200,784,1312,3714,3787] (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,784,1312,3714,3892] BT.lf) [6,61,200,784,1312,3714,4035] BT.lf) [6,61,200,784,1312,3714,4092] (BT.nd BT.lf [6,61,200,784,1312,3714,4094] BT.lf)))) [6,61,200,784,1312,3715] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,784,1312,3715,3715] BT.lf) [6,61,200,784,1312,3715,3775] BT.lf) [6,61,200,784,1312,3715,3786] (BT.nd (BT.nd BT.lf [6,61,200,784,1312,3715,3787] BT.lf) [6,61,200,784,1312,3715,3895] BT.lf)) [6,61,200,784,1312,3715,3986] (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,784,1312,3715,3987] BT.lf) [6,61,200,784,1312,3715,4034] BT.lf) [6,61,200,784,1312,3715,4092] (BT.nd (BT.nd BT.lf [6,61,200,784,1312,3987] BT.lf) [6,61,200,784,1341,3714,3715] BT.lf))) [6,61,200,784,1341,3714,4092] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,784,1341,3715] BT.lf) [6,61,200,784,1512,3714,3715] BT.lf) [6,61,200,784,1512,3714,4092] (BT.nd (BT.nd BT.lf [6,61,200,784,1512,3715] BT.lf) [6,61,200,784,1840,3715] BT.lf)) [6,61,200,784,2783,3714,3715] (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,784,2783,3714,4092] BT.lf) [6,61,200,784,2783,3715] BT.lf) [6,61,200,787,1315,3714] (BT.nd BT.lf [6,61,200,787,1840,3714] BT.lf)))))) [6,61,200,1840,1843,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,61,200,1840,3714,3715] BT.lf) [6,61,200,1840,3714,4092] BT.lf) [6,61,200,1840,3715] (BT.nd (BT.nd BT.lf [6,61,201,784,1312,3714] BT.lf) [6,61,203,253,784,1312,3714] BT.lf)) [6,61,203,784,787,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [6,61,203,784,984,1312,3714] BT.lf) [6,61,203,784,1312,3714,3895] BT.lf) [6,61,203,784,1312,3714,4092] (BT.nd (BT.nd BT.lf [6,61,203,784,1315,3714] BT.lf) [6,61,203,784,1512,3714] BT.lf))) [6,61,784,787,984,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,61,784,984,987,1312,3714] BT.lf) [6,61,784,984,1312,3714,3715] BT.lf) [6,61,784,984,1312,3714,4092] (BT.nd (BT.nd BT.lf [6,61,784,984,1312,3715] BT.lf) [6,61,784,1312,3714,3715,3895] BT.lf)) [6,61,784,1312,3714,3895,4092] (BT.nd (BT.nd (BT.nd BT.lf [6,61,784,1312,3715,3895] BT.lf) [6,61,784,1315,1512,3714] BT.lf) [6,63,200,784,1312,3714,3715] (BT.nd BT.lf [6,63,203,784,1312,3714] BT.lf)))) [6,200,203,784,829,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,200,203,784,1312,3714,4034] BT.lf) [6,200,784,787,829,1312,3714] BT.lf) [6,200,784,829,1312,3714,3715] (BT.nd (BT.nd BT.lf [6,200,784,829,1312,3714,4092] BT.lf) [6,200,784,829,1312,3715] BT.lf)) [6,200,784,1312,3714,3715,3775] (BT.nd (BT.nd (BT.nd BT.lf [6,200,784,1312,3714,3715,4034] BT.lf) [6,200,784,1312,3714,4034,4035] BT.lf) [6,200,784,1312,3714,4034,4092] (BT.nd (BT.nd BT.lf [6,200,784,1312,3714,4035] BT.lf) [6,200,784,1312,3715,4034] BT.lf))) [7,0,3,61,200,784,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,1,3,61,200,784,1312,3714] BT.lf) [7,1,61,200,784,1312,3714] BT.lf) [7,2,3,61,200,784,1312,3714] (BT.nd (BT.nd BT.lf [7,3,3,61,200,784,1312,3714] BT.lf) [7,3,8,61,200,784,1312,3714] BT.lf)) [7,3,8,200,784,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [7,3,16,61,200,784,1312,3714] BT.lf) [7,3,61,61,200,784,1312,3714] BT.lf) [7,3,61,63,200,784,1312,3714] (BT.nd BT.lf [7,3,61,128,200,784,1312] BT.lf))))) [7,3,61,128,200,784,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,3,61,200,200,784,1312,3714] BT.lf) [7,3,61,200,203,784,1312,3714] BT.lf) [7,3,61,200,253,784,1312,3714] (BT.nd (BT.nd BT.lf [7,3,61,200,256,784,1312,3714] BT.lf) [7,3,61,200,381,784,1312] BT.lf)) [7,3,61,200,381,784,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [7,3,61,200,512,784,1312,3714] BT.lf) [7,3,61,200,512,1312,3714] BT.lf) [7,3,61,200,784,784,1312,3714] (BT.nd (BT.nd BT.lf [7,3,61,200,784,787,1312,3714] BT.lf) [7,3,61,200,784,829,1312,3714] BT.lf))) [7,3,61,200,784,984,1312,3714] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,3,61,200,784,1312,1840,3714] BT.lf) [7,3,61,200,784,1312,2783,3714] BT.lf) [7,3,61,200,784,1312,3714] (BT.nd (BT.nd BT.lf [7,3,61,200,784,1312,3714,3714] BT.lf) [7,3,61,200,784,1312,3714,3715] BT.lf)) [7,3,61,200,784,1312,3714,3775] (BT.nd (BT.nd (BT.nd BT.lf [7,3,61,200,784,1312,3714,3786] BT.lf) [7,3,61,200,784,1312,3714,3895] BT.lf) [7,3,61,200,784,1312,3714,3986] (BT.nd BT.lf [7,3,61,200,784,1312,3714,4034] BT.lf)))) [7,3,61,200,784,1312,3714,4092] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,3,61,200,784,1312,3715] BT.lf) [7,3,61,200,784,1312,3775] BT.lf) [7,3,61,200,784,1312,3986] (BT.nd (BT.nd BT.lf [7,3,61,200,784,1315,3714] BT.lf) [7,3,61,200,784,1341,3714] BT.lf)) [7,3,61,200,784,1512,3714] (BT.nd (BT.nd (BT.nd BT.lf [7,3,61,200,784,1840,3714] BT.lf) [7,3,61,200,784,2783,3714] BT.lf) [7,3,61,200,1840,3714] (BT.nd (BT.nd BT.lf [7,3,61,203,784,1312,3714] BT.lf) [7,3,61,784,984,1312,3714] BT.lf))) [7,3,61,784,1312,3714,3895] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,3,63,200,784,1312,3714] BT.lf) [7,3,200,784,829,1312,3714] BT.lf) [7,3,200,784,1312,3714,3775] (BT.nd (BT.nd BT.lf [7,3,200,784,1312,3714,4034] BT.lf) [7,61,200,203,784,1312,3714] BT.lf)) [7,61,200,784,787,1312,3714] (BT.nd (BT.nd (BT.nd BT.lf [7,61,200,784,1312,3714,3715] BT.lf) [7,61,200,784,1312,3714,4092] BT.lf) [7,61,200,784,1312,3715] (BT.nd BT.lf [8,3,61,200,784,1312,3714] BT.lf)))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,9,61,1936],[]),([3,9,61,1968],[]),([3,61,137,1840],[]),([3,61,203,1981],[]),([3,61,649,1312],[]),([3,137,189,1840],[]),([3,189,203,1981],[]),([3,200,1853,3971],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([3,456,1853,3715],[]),([3,784,1513,3723],[]),([3,793,1512,3715],[]),([3,793,1512,3723],[]),([3,793,1513,3714],[]),([3,797,1512,3715],[]),([3,829,1480,3715],[]),([4,1,61,136,1840],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([4,1,784,1512,3722],[]),([4,1,792,1512,3714],[]),([4,3,61,136,1853],[]),([4,3,61,200,1981],[]),([4,3,189,200,1981],[]),([4,3,200,1853,3970],[]),([4,3,456,1853,3714],[]),([4,3,793,1512,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,3,793,1515,3714],[(56,32906)]),([4,3,797,1512,3714],[]),([4,3,829,1480,3714],[]),([4,9,61,128,1840],[]),([4,9,61,640,1312],[(112,0)]),([4,9,61,784,1440],[]),([4,9,381,784,1512],[]),([4,9,784,1440,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,9,784,1512,3714],[]),([4,9,784,1512,3715],[]),([4,9,784,1512,3723],[]),([4,9,784,1513,3714],[]),([4,9,784,2583,3714],[]),([4,9,793,1512,3714],[]),([4,9,984,2783,3714],[]),([4,16,984,1341,3715],[(96,134209)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([4,29,784,1512,3715],[]),([4,60,200,1853,3714],[]),([4,61,128,203,1853],[(56,73768)]),([4,61,131,200,1853],[]),([4,61,137,784,1312],[]),([4,61,189,203,1840],[(56,139297),(96,73768)]),([4,61,200,380,1853],[]),([4,61,200,1792,3715],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([4,61,200,1840,3971],[]),([4,61,200,1853,3715],[]),([4,61,200,1916],[(0,65577),(2,32841),(4,65577),(6,40137),(8,65577),(10,41025)]),([4,61,200,2179],[(0,41025),(2,32841),(4,41025),(6,40137),(8,41025),(10,65577)]),([4,61,200,2242,3715],[]),([4,61,200,2303,3715],[(116,41025)]),([4,61,201,1840,3775],[]),([4,61,201,1853,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([4,61,203,640,1341],[(72,75113)]),([4,61,203,701,1312],[(96,75113)]),([4,61,203,784,1469],[]),([4,61,203,829,1440],[]),([4,61,203,1936],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(81,131112)]),([4,61,203,1968],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(81,131112)]),([4,61,456,1840,3715],[]),([4,61,712,1341,3715],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([4,61,784,1440,3787],[(80,139297)]),([4,61,784,1480,3715],[]),([4,61,784,1512,3723],[]),([4,61,792,1512,3715],[]),([4,61,1736,3715],[(0,41025),(2,32841),(4,41025),(6,41025),(8,41025),(10,204840)]),([4,61,1853,3715,3895],[]),([4,61,2040,4019],[(0,134209),(2,32904),(4,134209),(6,134209),(8,134209),(10,131112)]),([4,63,200,1853,3715],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([4,63,203,1853,3714],[]),([4,137,189,784,1312],[]),([4,137,784,1312,3714],[]),([4,189,203,784,1469],[]),([4,189,203,1840],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(81,131113),(82,41089)]),([4,189,784,1312,3787],[(80,139297)]),([4,200,253,1853,3715],[]),([4,200,256,1853,3715],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([4,200,259,1853,3714],[]),([4,200,573,1853,3715],[]),([4,200,768,1341,3715],[(56,0)]),([4,200,784,1321,3715],[(56,0)]),([4,200,784,1321,3723],[(56,0)]),([4,200,784,1325,3715],[(56,0)]),([4,200,784,1341,3971],[]),([4,200,793,1321,3714],[(56,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([4,200,797,2783,3715],[]),([4,200,829,2815,3715],[]),([4,200,1597,3715],[(0,41025),(2,40137),(4,41025),(6,41025),(8,41025),(10,73761)]),([4,200,1792,3715,4034],[]),([4,200,1853,3714,4035],[]),([4,200,1853,3715,3775],[(84,41156),(108,41025)]),([4,200,1853,3715,4034],[]),([4,201,784,1312,3723],[(56,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([4,201,784,1321,3714],[(56,0)]),([4,203,793,1512,3714],[]),([4,253,784,1312,3723],[(80,139297)]),([4,456,784,1341,3715],[]),([4,784,793,1512,3714],[]),([4,784,1480,3715,4034],[]),([4,784,1512,3714,3723],[]),([4,784,1512,3714,4086],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([4,784,1512,3715,4066],[]),([4,784,1512,3722,3723],[]),([4,792,1512,3714,3715],[]),([4,829,984,1512,3715],[]),([5,1,8,784,1512,3714],[]),([5,1,61,136,784,1312],[]),([5,1,61,200,1840,3775],[]),([5,1,61,200,1853,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([5,1,136,784,1312,3714],[]),([5,1,200,784,1312,3722],[(80,0)]),([5,1,200,784,1320,3714],[(80,0)]),([5,3,9,784,1512,3714],[(56,32906)]),([5,3,9,784,1515,3714],[(56,32906),(72,41098)]),([5,3,16,984,1341,3714],[(56,131140),(136,134219)]),([5,3,29,784,1512,3714],[]),([5,3,61,128,200,1853],[(80,73928)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([5,3,61,136,784,1341],[]),([5,3,61,136,1840],[(0,139297),(2,139297),(4,139297),(6,32905),(8,139297),(10,139297),(12,139297),(14,139297),(73,139297),(74,139297),(81,139297),(97,131113),(98,139297),(113,139297),(114,139297)]),([5,3,61,136,1840,3714],[(128,139297)]),([5,3,61,189,200,1840],[(60,139460),(80,139297),(116,139297),(136,73928)]),([5,3,61,200,381,1853],[(152,204137)]),([5,3,61,200,640,1341],[(104,75113)]),([5,3,61,200,701,1312],[(136,75113)]),([5,3,61,200,784,1469],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([5,3,61,200,829,1440],[]),([5,3,61,200,1792,3714],[]),([5,3,61,200,1808,4002],[]),([5,3,61,200,1840,3722],[(80,139620),(128,139297),(148,139297)]),([5,3,61,200,1840,3970],[]),([5,3,61,200,1848,3714],[(128,139297)]),([5,3,61,200,1853,3714],[]),([5,3,61,200,1853,3715],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([5,3,61,200,1853,3775],[]),([5,3,61,200,1853,3986],[]),([5,3,61,200,1853,4018],[]),([5,3,61,200,1853,4031],[]),([5,3,61,200,1917],[(0,204137),(2,204137),(4,204137),(6,199753),(8,204137),(10,68809),(12,204137),(14,368840),(58,203809),(61,203817),(73,204137),(74,204137),(98,204137),(101,203817),(106,204137),(109,204137)]),([5,3,61,200,1936],[(0,139297),(2,139297),(4,139297),(6,32905),(8,139297),(10,139297),(12,139297),(14,139297),(61,139460),(73,139297),(74,139297),(86,138273),(97,131113),(98,139297),(113,134344)]),([5,3,61,200,1968],[(0,139297),(2,139297),(4,139297),(6,32905),(8,139297),(10,139297),(12,139297),(14,139297),(61,139460),(73,139297),(74,139297),(86,138273),(97,131113),(98,139297),(113,134344)]),([5,3,61,200,2178],[(0,368840),(2,368840),(4,368840),(6,199753),(8,368840),(10,68809),(12,368840),(14,204137),(58,32968),(61,41160),(73,368840),(74,368840),(97,204840),(98,368840),(105,73924),(106,368840)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([5,3,61,200,2242,3714],[(96,42049),(156,368840)]),([5,3,61,200,2303,3714],[(156,368840)]),([5,3,61,203,1853,3714],[(96,40298)]),([5,3,61,456,1840,3714],[]),([5,3,61,712,1312,3986],[]),([5,3,61,712,1341,3714],[]),([5,3,61,784,1440,3786],[(112,139460)]),([5,3,61,784,1480,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([5,3,61,784,1512,3722],[(156,139297)]),([5,3,61,792,1512,3714],[]),([5,3,61,1736,3714],[(0,368840),(2,368840),(4,368840),(6,199753),(8,368840),(10,368840),(12,368840),(14,204868),(58,32968),(61,41160),(73,368840),(74,368840),(97,204840),(98,368840),(105,73924),(106,368840)]),([5,3,61,1853,3714,3895],[]),([5,3,61,2040,4018],[(0,134344),(2,134344),(4,134344),(6,199816),(8,134344),(10,134344),(12,134344),(14,203908),(58,32968),(61,134344),(73,134344),(74,134344),(85,32968),(97,138436),(98,134344),(118,134344)]),([5,3,63,200,1853,3714],[]),([5,3,189,200,784,1469],[]),([5,3,189,200,1840],[(0,139297),(2,139297),(4,139297),(6,32905),(8,139297),(10,139297),(12,139297),(14,139297),(61,139460),(73,139297),(74,139297),(86,139297),(97,131113),(98,139297),(113,134345),(114,204932)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,3,189,784,1312,3786],[(112,139460)]),([5,3,200,253,1853,3714],[(56,73768)]),([5,3,200,256,1853,3714],[]),([5,3,200,573,1853,3714],[]),([5,3,200,768,1341,3714],[(80,0)]),([5,3,200,784,1321,3714],[(80,0)]),([5,3,200,784,1325,3714],[(80,0)]),([5,3,200,784,1341,3970],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,3,200,797,2783,3714],[]),([5,3,200,829,2815,3714],[]),([5,3,200,1597,3714],[(0,368714),(2,368714),(4,368714),(6,68809),(8,368714),(10,368714),(12,368714),(14,73924),(57,368714),(58,368714),(74,32842),(77,41034),(97,73770),(98,368714)]),([5,3,200,1792,3714,4034],[(128,199745)]),([5,3,200,1853,3714,3775],[(148,368714)]),([5,3,200,1853,3714,4034],[]),([5,3,203,784,1321,3714],[(72,40105),(80,0),(96,32906)]),([5,3,253,784,1312,3722],[(112,139620)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,3,456,784,1341,3714],[]),([5,3,784,1480,3714,4034],[(128,199745)]),([5,3,784,1512,3714,3722],[(96,32932),(152,32906)]),([5,3,784,1512,3714,4066],[(128,166977)]),([5,3,784,1512,3722],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,140321),(57,32906),(58,32906),(73,32906),(74,32906)]),([5,3,792,1512,3714],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,140321),(57,32906),(58,32906),(73,32906),(74,32906)]),([5,3,829,984,1512,3714],[(84,32906)]),([5,8,61,784,1512,3715],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,8,253,784,1312,3715],[(112,139297)]),([5,8,784,1512,3714,3715],[(96,32932)]),([5,9,61,128,784,1312],[(112,0)]),([5,9,61,200,1840,3714],[(72,139457),(80,139304),(128,139297)]),([5,9,61,784,1512,3714],[(156,0)]),([5,9,128,784,1312,3714],[(80,0)]),([5,9,200,381,784,1312],[(104,0)]),([5,9,200,784,1312,3714],[(80,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,200,784,1312,3715],[(72,0),(80,0)]),([5,9,200,784,1312,3723],[(72,0),(80,0)]),([5,9,200,784,1321,3714],[(80,0)]),([5,9,200,784,1512,3714],[]),([5,9,200,784,2783,3714],[]),([5,9,201,784,1312,3714],[(72,0),(80,0)]),([5,9,203,784,1512,3714],[]),([5,9,253,784,1312,3714],[(112,139304)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([5,9,784,984,1312,3714],[(80,0)]),([5,9,784,1312,3714,3895],[]),([5,9,784,1512,3714],[(6,0)]),([5,11,61,200,1840,3714],[(80,139624),(128,139297),(148,139297)]),([5,11,61,784,1512,3714],[(156,139297)]),([5,11,253,784,1312,3714],[(112,139624)]),([5,11,784,1512,3714],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,140321),(57,32906),(58,32906),(74,32906)]),([5,16,61,984,1312,3715],[(96,134187),(128,134209)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([5,16,200,784,1341,3715],[(56,134186),(128,139329)]),([5,25,784,984,1312,3714],[(104,134187),(112,134313),(136,134315)]),([5,29,200,784,1312,3715],[(72,0)]),([5,29,200,784,2783,3715],[]),([5,48,61,200,1840,3715],[(56,139297),(72,134186),(96,139297),(128,131114)]),([5,60,61,200,1840,3714],[(60,32968),(96,65578),(128,65736)]),([5,60,200,784,1341,3714],[]),([5,60,200,1840,3714],[(0,32968),(2,199745),(4,32968),(6,40129),(8,32968),(10,32968),(12,32968),(14,203809),(74,32968),(81,32968),(82,32968),(97,65732),(98,32968),(114,32968),(117,32968)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,61,200,1840,3715],[(48,139297),(52,139297)]),([5,61,63,200,1840,3715],[(60,139297)]),([5,61,63,203,1840,3714],[(56,32968),(104,40298)]),([5,61,128,203,784,1341],[(56,75816),(104,0)]),([5,61,128,203,1840],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(12,139297),(14,139297),(57,139297),(82,139297),(85,139297),(105,139297),(106,139297),(113,131113),(114,41089)]),([5,61,128,784,1312,3787],[(80,0),(112,139297)]),([5,61,131,200,784,1341],[]),([5,61,131,200,1840],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(12,139297),(14,139297),(105,131113),(106,41089),(113,134345),(114,204932)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,136,784,1312,3715],[(112,139297)]),([5,61,189,203,784,1312],[(56,140321),(96,74792),(104,0),(128,75816)]),([5,61,200,203,1853,3714],[(56,73768),(104,204865)]),([5,61,200,253,1840,3715],[(60,139297),(76,139297),(84,139297),(112,204868),(148,139460)]),([5,61,200,256,1840,3715],[(112,139297)]),([5,61,200,259,1840,3714],[]),([5,61,200,380,784,1312],[(112,65578),(144,65579),(152,139297)]),([5,61,200,380,784,1341],[(112,65578)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,200,380,784,1512],[(112,65578),(152,204932)]),([5,61,200,380,784,2783],[(112,65578)]),([5,61,200,380,1840],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(12,139297),(14,139297),(105,134345),(106,204932),(113,139297),(114,204840)]),([5,61,200,512,1341,3715],[(72,73770)]),([5,61,200,573,1312,3715],[(72,172065),(96,73770)]),([5,61,200,768,1312,3715],[(80,0),(112,172065)]),([5,61,200,784,1312,3715],[(112,139297)]),([5,61,200,784,1312,3723],[(80,0),(112,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,200,784,1312,3971],[(72,0)]),([5,61,200,784,1313,3715],[(112,139460)]),([5,61,200,784,1320,3715],[(80,0),(112,139297)]),([5,61,200,784,1341,3715],[]),([5,61,200,784,1404],[(0,65579),(2,32843),(4,65579),(6,40139),(8,65579),(10,65579),(12,65579),(14,43073),(74,65579),(81,65579),(82,65579),(113,204840),(114,65579)]),([5,61,200,784,1440,3715],[(112,139297)]),([5,61,200,784,1512,3715],[(112,204932)]),([5,61,200,784,1824,3715],[(112,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,200,784,1853,3715],[]),([5,61,200,784,2583,3715],[]),([5,61,200,784,2691],[(0,43073),(2,32843),(4,43073),(6,40139),(8,43073),(10,43073),(12,43073),(14,65579),(74,43073),(81,43073),(82,43073),(114,43073),(117,41025)]),([5,61,200,784,2754,3715],[]),([5,61,200,784,2783,3715],[(156,43073)]),([5,61,200,784,2815,3715],[(156,43073)]),([5,61,200,785,1313,3714],[]),([5,61,200,829,1341,3715],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,200,829,1512,3715],[(112,204868)]),([5,61,200,829,1840,3715],[(76,139297)]),([5,61,200,829,1853,3715],[]),([5,61,200,829,2783,3715],[(156,43073)]),([5,61,200,984,1512,3715],[(112,204932)]),([5,61,200,984,2783,3715],[(156,43073)]),([5,61,200,1536,3715],[(0,41025),(2,32841),(4,41025),(6,40137),(8,41025),(10,41025),(12,41025),(14,65577),(73,41025),(74,41025),(81,41025),(82,41025),(114,41025),(117,41025)]),([5,61,200,1808,3715],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(12,139297),(14,139297),(81,134345),(82,204932),(114,131113),(117,41025)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,200,1840,1853,3715],[(100,139297),(116,139297)]),([5,61,200,1840,3714,4035],[]),([5,61,200,1840,3715],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(12,139297),(14,139297),(81,134345),(82,204932),(114,131113),(117,41025)]),([5,61,200,1840,3715,3775],[(132,139297),(140,139297),(148,41025),(156,139297)]),([5,61,200,1840,3715,4034],[]),([5,61,200,1840,3987],[(0,131113),(2,32905),(4,131113),(6,131113),(8,131113),(10,41089),(12,131113),(14,131113),(81,139297),(82,131113),(114,131113),(117,131113)]),([5,61,200,1840,4019],[(0,131113),(2,32905),(4,131113),(6,131113),(8,131113),(10,41089),(12,131113),(14,131113),(81,139297),(82,131113),(114,131113),(117,131113)]),([5,61,200,1853,3714,3715],[(116,41025),(148,41160)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,200,1853,3714,4092],[(148,65578)]),([5,61,200,1853,3715],[(82,204868),(117,41160)]),([5,61,200,2040,3715],[(0,204932),(2,32905),(4,204932),(6,134345),(8,204932),(10,204932),(12,204932),(14,204932),(74,204868),(82,204932),(85,204932),(105,204932),(117,41025)]),([5,61,200,2255,3715],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(12,139297),(14,139297),(82,139297),(85,139297),(117,204840),(118,139297)]),([5,61,200,2783,3311,3715],[(116,139297),(148,43073),(156,42049)]),([5,61,201,381,784,1312],[(112,203818),(144,203819),(152,139457)]),([5,61,201,784,1312,3714],[(112,139457)]),([5,61,201,784,1312,3715],[(112,139460)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,201,784,1312,3775],[]),([5,61,201,784,1313,3714],[(112,139460)]),([5,61,201,784,1341,3714],[]),([5,61,201,784,1512,3714],[(112,204865),(156,139457)]),([5,61,201,784,1513,3714],[(112,204929),(156,139457)]),([5,61,201,784,2783,3714],[(156,43208)]),([5,61,201,1840,3714],[(0,139457),(2,196745),(4,139457),(6,139457),(8,139457),(10,139457),(12,139457),(14,139457),(81,131273),(82,204929),(97,139457),(110,139457),(114,139457),(117,41160)]),([5,61,203,253,1840,3714],[(60,139304),(84,139457),(96,73768),(112,204865),(128,140321),(148,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,203,381,784,1512],[(84,203841),(112,204138),(152,204865)]),([5,61,203,383,784,1312],[(112,40298),(144,40299),(152,139297)]),([5,61,203,640,1312],[(0,172065),(2,32937),(4,172065),(6,172065),(8,172065),(10,172065),(12,172065),(14,172065),(73,172065),(81,172065),(105,163881),(106,41121),(112,0),(113,172065),(114,172065)]),([5,61,203,784,1312,3712],[(112,139297)]),([5,61,203,784,1440],[(0,140321),(2,32906),(4,140321),(6,140321),(8,140321),(10,140321),(12,140321),(14,140321),(81,131114),(82,42113),(105,163880),(113,140321),(114,139297)]),([5,61,203,784,1440,3714],[(112,139457),(148,172065),(156,139297)]),([5,61,203,784,1512,3714],[(112,204865),(156,139297)]),([5,61,203,784,1512,3715],[(112,204932),(156,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,203,784,2583,3714],[(96,32906)]),([5,61,203,787,1315,3714],[(112,40298)]),([5,61,203,829,1512,3714],[(112,204865),(156,0)]),([5,61,203,984,2783,3714],[(148,172065),(156,370888)]),([5,61,203,1843,3714],[(0,40298),(2,199817),(4,40298),(6,68650),(8,40298),(10,369704),(12,40298),(14,40298),(74,40298),(97,139460),(98,40298),(110,40297),(114,40297),(117,368840)]),([5,61,203,2040,3714],[(0,204865),(2,199817),(4,204865),(6,65737),(8,204865),(10,204865),(12,204865),(14,204865),(74,204865),(77,32968),(97,139460),(98,204865),(105,204865),(110,204865),(117,204865),(118,204865)]),([5,61,380,784,984,1312],[(136,65579),(144,134187)]),([5,61,380,784,1312,3895],[(80,40138),(104,40139),(112,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,456,784,1312,3715],[(72,0)]),([5,61,712,784,1312,3715],[(112,139297)]),([5,61,712,1312,3715],[(0,172065),(2,32937),(4,172065),(6,172065),(8,172065),(10,172065),(12,172065),(14,172065),(81,167113),(82,204964),(114,163881),(117,41025)]),([5,61,784,984,1312,3715],[(104,134187),(136,134209)]),([5,61,784,984,1341,3715],[(136,134209)]),([5,61,784,984,1512,3715],[(136,131114)]),([5,61,784,984,2783,3715],[(136,134209),(156,43073)]),([5,61,784,985,1312,3714],[(104,131115),(136,131272)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,784,1312,2040,3715],[(80,134345),(136,134209),(144,166977)]),([5,61,784,1312,2583,3715],[(80,166954),(144,166977)]),([5,61,784,1312,3714,3894],[(80,139457)]),([5,61,784,1312,3715,3895],[(80,139297)]),([5,61,784,1315,1512,3715],[(144,166977)]),([5,61,784,1341,3715,3895],[]),([5,61,784,1512,1840,3715],[(80,134345),(104,166954),(136,131114),(152,166977)]),([5,61,784,1512,2783,3715],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,784,1512,3714,3787],[(80,204865),(116,139297)]),([5,61,784,1512,3714,3892],[(80,65737),(116,139297),(152,65736)]),([5,61,784,1512,3715,3786],[(80,204932),(148,139297)]),([5,61,784,1512,3715,3787],[(80,204932),(116,139297),(148,139297)]),([5,61,784,1512,3715,3895],[(80,134345)]),([5,61,784,1512,3715,4002],[(152,166977)]),([5,61,784,1512,3715,4003],[(108,166977),(152,166977)]),([5,61,784,1512,4003],[(0,166977),(2,32936),(4,166977),(6,166977),(8,166977),(10,166977),(12,166977),(14,163880),(57,166977),(58,166977),(81,166977),(82,166977),(106,166977),(109,166977)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([5,61,784,2783,3715,3895],[(116,40139)]),([5,61,984,1840,3715],[(0,134187),(2,32905),(4,134187),(6,134187),(8,134187),(10,43140),(12,134187),(14,134187),(81,134345),(114,163883)]),([5,61,1840,2040,3715],[(0,134345),(2,32905),(4,134345),(6,204932),(8,134345),(10,134345),(12,134345),(14,134345),(82,134345),(85,134345),(105,134345),(106,139297)]),([5,61,1840,3715,3895],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(12,139297),(14,139297),(82,131113),(85,40137),(106,139297),(109,139297)]),([5,61,1843,2040,3714],[(0,131114),(2,199817),(4,131114),(6,65668),(8,131114),(10,42113),(12,131114),(14,131114),(77,32968),(97,139460),(98,131114),(105,134209),(106,131113),(118,131113)]),([5,63,200,784,1341,3715],[]),([5,63,201,784,1312,3714],[(112,139457)]),([5,63,203,784,1341,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([5,63,203,1840,3714],[(0,32968),(2,196648),(4,32968),(6,32968),(8,32968),(10,32968),(12,32968),(14,203809),(74,32968),(81,32968),(82,32968),(110,32968),(114,32968),(117,32968)]),([5,136,784,1312,3714,3715],[]),([5,189,200,784,1312,3715],[(112,139297)]),([5,189,203,784,1312],[(0,140321),(2,32906),(4,140321),(6,140321),(8,140321),(10,140321),(12,140321),(14,140321),(74,0),(81,131114),(82,42113),(105,163883),(106,43169),(113,140321),(114,139297)]),([5,189,203,784,1312,3714],[(112,139304),(148,172065),(156,139297)]),([5,200,203,784,1321,3714],[(72,0)]),([5,200,253,784,1341,3715],[]),([5,200,256,784,1341,3715],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([5,200,259,784,1341,3714],[]),([5,200,317,784,1312,3715],[]),([5,200,380,784,829,1312],[]),([5,200,380,784,1312,4034],[(80,32842),(104,32843),(112,32905)]),([5,200,573,784,1312,3715],[(112,139297)]),([5,200,573,1312,3715],[(0,172065),(2,172065),(4,172065),(6,32937),(8,172065),(10,172065),(12,172065),(14,172065),(73,167113),(74,172065),(114,163881),(117,41025)]),([5,200,768,1312,3715,4034],[(56,0),(80,32937)]),([5,200,784,793,1312,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([5,200,784,829,1312,3715],[]),([5,200,784,829,1512,3715],[]),([5,200,784,829,2783,3715],[]),([5,200,784,1312,1853,3715],[]),([5,200,784,1312,2754,3715],[]),([5,200,784,1312,3714,3723],[(56,0)]),([5,200,784,1312,3714,4086],[(56,0)]),([5,200,784,1312,3715,4034],[(80,32905)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([5,200,784,1312,3715,4050],[(56,0)]),([5,200,784,1312,3722,3723],[(56,0)]),([5,200,784,1315,1341,3715],[]),([5,200,784,1320,3714,3715],[(56,0)]),([5,200,784,1341,1512,3715],[(56,0)]),([5,200,784,1341,2783,3715],[]),([5,200,784,1341,3714,4035],[]),([5,200,784,1341,3715,3775],[(148,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([5,200,784,1341,3715,4002],[]),([5,200,784,1341,3715,4003],[]),([5,200,784,1341,3715,4034],[]),([5,200,784,1512,3715,4034],[(80,32905)]),([5,200,784,2783,3715,4034],[(116,32843)]),([5,200,1840,3714,4034,4035],[(108,199745),(116,199745),(152,199745)]),([5,200,1840,3714,4035],[(0,199745),(2,199745),(4,199745),(6,199745),(8,199745),(10,199745),(12,199745),(14,32968),(57,199745),(58,199745),(82,199745),(85,199745),(109,199745),(114,199745),(117,199745)]),([5,200,1840,3715,4034],[(0,32905),(2,32905),(4,32905),(6,32905),(8,32905),(10,32905),(12,32905),(14,139297),(57,32905),(58,32905),(82,32905),(85,32841)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([5,201,784,829,1312,3714],[]),([5,201,784,1312,3714,3775],[(80,139457)]),([5,201,784,1312,3714,4034],[(80,196745)]),([5,203,784,829,1512,3714],[]),([5,203,784,1341,1512,3714],[]),([5,203,784,1512,3714,4034],[(80,199817),(116,32905),(148,32906)]),([5,784,829,984,1312,3715],[]),([5,784,829,1312,1512,3715],[(144,166977)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([5,784,829,1312,3715,3895],[]),([5,784,984,1312,3715,4034],[(72,32905),(96,32904),(128,0)]),([5,784,1312,3715,3895,4034],[(56,32905)]),([6,0,61,200,784,1312,3715],[(152,139297)]),([6,1,8,200,784,1312,3714],[(104,0),(112,0)]),([6,1,61,200,381,784,1312],[(152,203818),(192,203819),(200,139460)]),([6,1,61,200,784,1312,3714],[(152,139460)]),([6,1,61,200,784,1312,3715],[(96,0),(152,139460)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,61,200,784,1312,3775],[]),([6,1,61,200,784,1313,3714],[(152,139460)]),([6,1,61,200,784,1341,3714],[]),([6,1,61,200,784,1512,3714],[(152,204932),(204,139460)]),([6,1,61,200,784,2783,3714],[(204,43208)]),([6,1,61,200,1840,3714],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,139460),(61,139460),(73,139460),(74,139460),(97,139460),(98,139460),(113,134345),(114,204932),(129,139460),(130,139460),(137,139460),(150,139460),(154,139460),(157,41160)]),([6,1,61,201,784,1312,3714],[(96,0),(152,139460)]),([6,1,61,784,984,1312,3714],[(72,131112),(144,134187),(184,134344)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([6,1,61,784,1312,3714,3895],[(112,139460)]),([6,1,63,200,784,1312,3714],[(152,139460)]),([6,1,200,784,829,1312,3714],[]),([6,1,200,784,1312,3714,3775],[(112,139460)]),([6,1,200,784,1312,3714,4034],[(112,199817),(168,199745)]),([6,2,61,200,784,1312,3715],[(152,139460)]),([6,2,61,203,784,1312,3714],[(56,32968),(96,40298),(128,40299),(152,139457)]),([6,3,8,61,200,1840,3714],[(80,139460),(104,139460),(112,139624),(168,139297),(196,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,8,61,784,1512,3714],[(84,32906),(204,139297)]),([6,3,8,253,784,1312,3714],[(152,139624)]),([6,3,8,784,1512,3714],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,32906),(16,32906),(18,140321),(57,32906),(58,32906),(73,32906),(74,32906),(81,32906),(82,32906),(97,32906),(98,32906),(106,32906),(109,32906),(138,32906)]),([6,3,9,200,784,1312,3714],[(56,32906),(104,0),(112,0)]),([6,3,9,203,784,1312,3714],[(56,32906),(96,40105),(104,0),(112,0),(128,40073)]),([6,3,16,61,984,1312,3714],[(56,131140),(136,134345),(176,134344)]),([6,3,16,200,784,1341,3714],[(56,131145),(80,134217),(176,139339)]),([6,3,29,200,784,1312,3714],[(104,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,29,200,784,2783,3714],[]),([6,3,48,61,200,1840,3714],[(56,131434),(80,139460),(104,134506),(136,139460),(176,140484)]),([6,3,61,61,200,1840,3714],[(60,139460),(64,139460),(68,139460),(176,140321)]),([6,3,61,63,200,1840,3714],[(60,139460),(76,139460),(80,32968),(84,139460),(144,42049),(184,140321)]),([6,3,61,128,200,784,1341],[(80,75976),(144,0)]),([6,3,61,128,200,1840],[(0,139297),(2,139297),(4,139297),(6,32905),(8,139297),(10,139297),(12,139297),(14,139297),(16,139297),(18,139297),(61,139460),(73,139297),(74,139297),(81,139297),(97,139297),(98,139297),(110,139297),(114,139297),(117,139297),(129,131113),(130,139297),(145,139297),(146,139297),(153,134345),(154,204932)]),([6,3,61,128,784,1312,3786],[(112,0),(152,139460)]),([6,3,61,136,784,1312],[(0,140321),(2,140321),(4,140321),(6,32906),(8,140321),(10,140321),(12,140321),(14,140321),(16,140321),(18,140321),(73,140321),(74,140321),(81,140321),(97,131114),(98,140321),(106,0),(113,140321),(114,140321),(129,163883),(130,140321),(145,140321),(146,140321),(153,140321),(154,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_53 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,136,784,1312,3714],[(196,172065),(204,139297)]),([6,3,61,189,200,784,1312],[(60,140484),(80,140321),(116,140321),(136,74952),(144,0),(176,75976)]),([6,3,61,200,253,1840,3714],[(84,139624),(100,139460),(108,139460),(116,139460),(152,204868),(176,140321),(196,139297)]),([6,3,61,200,256,1840,3714],[(152,139460)]),([6,3,61,200,380,784,1312],[(152,204138),(192,204139),(200,139297)]),([6,3,61,200,381,784,1312],[(152,204138),(192,204139),(200,139460)]),([6,3,61,200,381,784,1341],[(152,204138),(192,204139)]),([6,3,61,200,381,784,1512],[(84,140321),(116,203940),(152,204138),(200,204932)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_53 : K_53.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_54 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,200,381,784,2783],[(152,204138)]),([6,3,61,200,381,1840],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,203809),(61,139460),(73,139460),(74,139460),(98,139297),(101,139460),(106,139460),(109,139460),(118,139297),(129,131114),(130,139460),(145,134345),(146,204932),(153,139460),(154,204868)]),([6,3,61,200,383,784,1312],[(152,204138),(192,204139),(200,139297)]),([6,3,61,200,512,1312,3986],[(152,0)]),([6,3,61,200,512,1341,3714],[(104,74090)]),([6,3,61,200,573,1312,3714],[(60,172074),(104,172228),(136,74090)]),([6,3,61,200,640,1312],[(0,172065),(2,172065),(4,172065),(6,32937),(8,172065),(10,172065),(12,172065),(14,172065),(16,172065),(18,172065),(61,172228),(73,172065),(74,172065),(86,172065),(97,172065),(98,172065),(105,172065),(113,172065),(129,163881),(130,172065),(145,167113),(146,204964),(152,0),(153,172065),(154,172065)]),([6,3,61,200,768,1312,3714],[(112,0),(152,172228)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_54 : K_54.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_55 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,200,784,1312,3712],[(152,139297)]),([6,3,61,200,784,1312,3714],[(152,139460)]),([6,3,61,200,784,1312,3715],[(152,139297)]),([6,3,61,200,784,1312,3722],[(112,0),(188,140321)]),([6,3,61,200,784,1312,3970],[(104,0)]),([6,3,61,200,784,1313,3714],[(152,139460)]),([6,3,61,200,784,1315,3715],[(72,40299),(96,41160),(152,139297)]),([6,3,61,200,784,1320,3714],[(112,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_55 : K_55.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_56 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,200,784,1341,3714],[]),([6,3,61,200,784,1341,3715],[]),([6,3,61,200,784,1341,3775],[(104,73928)]),([6,3,61,200,784,1341,3986],[(112,134344),(168,131114)]),([6,3,61,200,784,1341,4002],[(152,0)]),([6,3,61,200,784,1341,4031],[]),([6,3,61,200,784,1405],[(0,204139),(2,204139),(4,204139),(6,199755),(8,204139),(10,68811),(12,204139),(14,204139),(16,204139),(18,370888),(58,203809),(61,203819),(73,204139),(74,204139),(97,204139),(98,204139),(106,204139),(113,204139),(114,204139),(130,204139),(133,203819),(138,204139),(141,204139),(153,204868),(154,204139)]),([6,3,61,200,784,1440],[(0,140321),(2,140321),(4,140321),(6,32906),(8,140321),(10,140321),(12,140321),(14,140321),(16,140321),(18,140321),(61,140484),(73,140321),(74,140321),(86,140321),(97,131114),(98,140321),(113,134346),(114,205956),(129,163883),(130,140321),(145,167112),(153,140321),(154,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_56 : K_56.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_57 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,200,784,1440,3714],[(84,32906),(152,139460),(196,172065),(204,139297)]),([6,3,61,200,784,1512,3714],[(84,32906),(152,204932),(204,139297)]),([6,3,61,200,784,1512,3715],[(152,204932),(204,139297)]),([6,3,61,200,784,1824,3714],[(152,139460),(192,0)]),([6,3,61,200,784,1853,3714],[]),([6,3,61,200,784,2583,3714],[(84,32906),(136,32906)]),([6,3,61,200,784,2690],[(0,370888),(2,370888),(4,370888),(6,199755),(8,370888),(10,68811),(12,370888),(14,370888),(16,370888),(18,204139),(58,32968),(61,43208),(73,370888),(74,370888),(97,370888),(98,370888),(106,370888),(113,370888),(114,370888),(129,206888),(130,370888),(137,75972),(138,370888),(154,370888),(157,368840)]),([6,3,61,200,784,2754,3714],[(128,43073),(204,370888)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_57 : K_57.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_58 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,200,784,2783,3714],[(204,370888)]),([6,3,61,200,784,2783,3715],[(204,370888)]),([6,3,61,200,784,2815,3714],[(204,370888)]),([6,3,61,200,787,1315,3714],[(56,32968),(96,41160),(128,41160),(152,139460),(168,41160)]),([6,3,61,200,829,1341,3714],[(176,73928)]),([6,3,61,200,829,1512,3714],[(152,204868),(204,0)]),([6,3,61,200,829,1840,3714],[(100,139460),(108,139460),(192,139297)]),([6,3,61,200,829,1853,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_58 : K_58.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_59 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,200,829,2783,3714],[(204,370888)]),([6,3,61,200,984,1512,3714],[(72,204865),(152,204932),(196,204964),(204,204932)]),([6,3,61,200,984,2783,3714],[(84,32904),(196,172065),(204,370888)]),([6,3,61,200,1536,3714],[(0,368840),(2,368840),(4,368840),(6,199753),(8,368840),(10,68809),(12,368840),(14,368840),(16,368840),(18,204137),(58,32968),(61,41160),(73,368840),(74,368840),(97,368840),(98,368840),(105,368840),(106,368840),(113,368840),(114,368840),(129,204840),(130,368840),(137,73924),(138,368840),(154,368840),(157,368840)]),([6,3,61,200,1808,3714],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,32968),(61,139460),(73,139460),(74,139460),(97,131114),(98,139460),(113,134345),(114,204932),(129,139460),(130,139297),(137,139460),(138,140321),(150,139297),(154,139460),(157,368840)]),([6,3,61,200,1840,1853,3714],[(132,139460),(140,139460),(156,139460),(200,139297)]),([6,3,61,200,1840,3714],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,32968),(61,139460),(73,139460),(74,139460),(97,131114),(98,139460),(113,134345),(114,204932),(129,139460),(130,139297),(137,139460),(138,140321),(150,139297),(154,139460),(157,368840)]),([6,3,61,200,1840,3714,3775],[(60,139460),(156,368840),(172,139460),(176,139460),(180,139460),(196,368840),(200,140321),(204,139460)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_59 : K_59.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_60 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,200,1840,3714,4034],[(60,199817),(136,32906),(204,139460)]),([6,3,61,200,1840,3715],[(0,139297),(2,139297),(4,139297),(6,32905),(8,139297),(10,139297),(12,139297),(14,139297),(16,139297),(18,139297),(61,139460),(73,139297),(74,139297),(77,139297),(97,139297),(98,139297),(101,139297),(113,134345),(114,204932),(129,139297),(130,139297),(133,139297),(138,140321),(150,139297),(154,139297),(157,368840)]),([6,3,61,200,1840,3775],[(0,140321),(2,140321),(4,140321),(6,32906),(8,140321),(10,140321),(12,140321),(14,140321),(16,140321),(18,140321),(73,140321),(74,140321),(81,140321),(97,131114),(98,140321),(113,134345),(114,204932),(130,140321),(133,140321),(138,140321),(141,140321),(149,140321),(150,139297),(154,139297),(157,368840)]),([6,3,61,200,1840,3986],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,32968),(61,139460),(73,139460),(74,139460),(97,163881),(98,139460),(113,139460),(114,139460),(129,139460),(130,139297),(138,139297),(150,139297),(154,139460),(157,139460)]),([6,3,61,200,1840,4018],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,32968),(61,139460),(73,139460),(74,139460),(97,139460),(98,139460),(113,139460),(114,139460),(129,139460),(130,139297),(138,139297),(150,139297),(154,139460),(157,139460)]),([6,3,61,200,1843,3714],[(0,139460),(2,131114),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,32968),(73,42113),(74,139460),(98,139460),(101,139460),(106,42049),(113,134345),(114,204932),(130,139297),(137,139460),(138,140321),(150,139297),(154,139297),(157,368840)]),([6,3,61,200,1853,3714],[(98,42049),(114,204868),(157,368840)]),([6,3,61,200,2040,3714],[(0,204932),(2,204932),(4,204932),(6,199817),(8,204932),(10,134345),(12,204932),(14,204932),(16,204932),(18,204932),(58,32968),(61,204932),(73,139460),(74,204932),(97,131114),(98,204932),(106,204868),(109,32968),(114,204932),(117,204932),(129,204932),(130,204932),(137,139460),(138,204932),(145,204932),(150,204932),(157,204868),(158,204932)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_60 : K_60.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_61 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,200,2255,3714],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,32968),(61,139460),(73,139460),(74,139460),(98,139460),(101,139460),(114,139460),(117,139460),(129,139460),(130,139297),(137,139460),(138,140321),(150,139297),(157,204868),(158,139460)]),([6,3,61,200,2783,3311,3714],[(156,139460),(196,370888),(204,369864)]),([6,3,61,201,784,1312,3714],[(152,139460)]),([6,3,61,203,381,784,1312],[(56,203809),(128,40298),(152,204138),(168,40299),(192,204139),(200,139460)]),([6,3,61,203,784,1312,3714],[(56,32968),(96,40298),(128,40299),(152,139460)]),([6,3,61,203,784,1312,3715],[(96,40298),(128,40299),(152,139297)]),([6,3,61,203,784,1315,3714],[(56,32968),(72,40299),(128,40299),(152,139460),(168,40299)]),([6,3,61,203,784,1341,3714],[(96,40298),(128,40299)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_61 : K_61.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_62 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,203,784,1512,3714],[(56,32968),(96,42113),(152,204932),(204,139297)]),([6,3,61,203,784,1515,3714],[(56,32968),(96,40298),(152,204932),(204,139460)]),([6,3,61,203,784,2783,3714],[(56,32968),(96,40298),(204,370888)]),([6,3,61,203,1840,3714],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,32968),(74,139460),(77,139460),(97,139460),(98,139460),(113,134345),(114,204932),(130,139297),(133,139457),(137,139460),(138,140321),(150,139460),(154,139460),(157,368840)]),([6,3,61,381,784,984,1312],[(96,131114),(184,204139),(192,134345)]),([6,3,61,381,784,1312,3895],[(112,68810),(144,68811),(152,139460)]),([6,3,61,456,784,1312,3714],[(104,0)]),([6,3,61,712,784,1312,3714],[(152,139460)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_62 : K_62.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_63 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,712,1312,3714],[(0,172228),(2,172228),(4,172228),(6,199849),(8,172228),(10,172228),(12,172228),(14,172228),(16,172228),(18,172228),(58,32968),(61,172228),(73,172228),(74,172228),(97,163883),(98,172228),(113,167113),(114,204964),(129,172228),(130,172065),(137,172228),(138,174113),(150,172065),(154,172228),(157,368840)]),([6,3,61,784,984,1312,3714],[(72,131114),(144,134345),(184,134344)]),([6,3,61,784,984,1312,3715],[(72,0),(144,134345),(184,134344)]),([6,3,61,784,984,1341,3714],[(72,131114),(184,134344)]),([6,3,61,784,984,1512,3714],[(72,131114),(96,131114),(108,32936),(184,140484),(204,134345)]),([6,3,61,784,984,2783,3714],[(72,131114),(184,134344),(204,370888)]),([6,3,61,784,987,1312,3714],[(56,32968),(128,40299),(144,134345),(184,134344)]),([6,3,61,784,1312,2040,3714],[(72,131114),(96,163883),(112,134345),(184,134344),(192,167112)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_63 : K_63.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_64 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,784,1312,2583,3714],[(96,43169),(112,167113),(192,167112)]),([6,3,61,784,1312,3714,3892],[(56,32968),(72,68650),(96,68651),(112,139460)]),([6,3,61,784,1312,3714,3895],[(112,139460)]),([6,3,61,784,1312,3715,3895],[(112,139297)]),([6,3,61,784,1315,1512,3714],[(56,32968),(72,42113),(96,163883),(112,167113),(192,167112)]),([6,3,61,784,1341,3714,3895],[]),([6,3,61,784,1512,1840,3714],[(72,131114),(112,134345),(128,166977),(144,167113),(184,167274),(200,167112)]),([6,3,61,784,1512,2783,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_64 : K_64.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_65 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,61,784,1512,3714,3786],[(112,204932),(136,32906),(156,139460),(180,32906),(196,139460)]),([6,3,61,784,1512,3714,3895],[(112,134345),(156,139297),(200,167112)]),([6,3,61,784,1512,3714,4002],[(148,167112),(168,166977),(200,167112)]),([6,3,61,784,1512,4002],[(0,167112),(2,167112),(4,167112),(6,199848),(8,167112),(10,167112),(12,167112),(14,167112),(16,167112),(18,203940),(58,32968),(61,167112),(73,167112),(74,167112),(81,167050),(82,167112),(97,167112),(98,167112),(109,32906),(113,167112),(114,167112),(129,171204),(130,167112),(146,167112),(149,167112),(158,167112)]),([6,3,61,784,2783,3714,3895],[(156,68811)]),([6,3,61,984,1840,3714],[(0,134345),(2,134345),(4,134345),(6,199817),(8,134345),(10,134345),(12,134345),(14,204932),(16,134345),(18,134345),(58,32968),(61,134187),(73,134345),(74,134345),(85,32939),(97,163883),(98,134345),(113,134345),(129,134187),(130,134345),(137,139460),(138,134345),(150,134345),(154,139460)]),([6,3,61,1840,2040,3714],[(0,134345),(2,134345),(4,134345),(6,199817),(8,134345),(10,204932),(12,134345),(14,134345),(16,134345),(18,134345),(58,32968),(61,134345),(73,139460),(74,134345),(97,134345),(98,134345),(109,32968),(114,134345),(117,134345),(129,134345),(130,134345),(137,139460),(138,134345),(145,134345),(146,139460),(158,134345)]),([6,3,61,1840,3714,3895],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(58,32968),(61,139460),(73,131114),(74,139460),(97,139460),(98,139297),(105,139460),(106,140321),(114,139460),(117,68809),(130,139460),(133,139460),(146,139460),(149,139460),(153,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_65 : K_65.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_66 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,63,200,784,1341,3714],[]),([6,3,63,200,1840,3714],[(0,32968),(2,32968),(4,32968),(6,199817),(8,32968),(10,32968),(12,32968),(14,32968),(16,32968),(18,203809),(58,32968),(61,32968),(73,32968),(74,32968),(97,32968),(98,32968),(106,32968),(113,32968),(114,32968),(129,139460),(137,139460),(154,32968),(157,32968)]),([6,3,136,784,1312,3714],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,32906),(16,32906),(18,140321),(57,32906),(58,32906),(73,32906),(74,32906),(81,32906),(82,32906),(97,32906),(98,32906),(105,32906),(106,32906),(138,32906)]),([6,3,189,200,784,1312],[(0,140321),(2,140321),(4,140321),(6,32906),(8,140321),(10,140321),(12,140321),(14,140321),(16,140321),(18,140321),(61,140484),(73,140321),(74,140321),(86,140321),(97,131114),(98,140321),(106,0),(113,134346),(114,205956),(129,163883),(130,140321),(145,167115),(146,207012),(153,140321),(154,139297)]),([6,3,189,200,784,1312,3714],[(84,32906),(152,139460),(196,172065),(204,139297)]),([6,3,200,253,784,1341,3714],[(56,139304)]),([6,3,200,256,784,1341,3714],[]),([6,3,200,317,784,1312,3714],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_66 : K_66.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_67 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,200,381,784,829,1312],[]),([6,3,200,381,784,1312,4034],[(112,199754),(144,199755),(152,199817),(168,199745)]),([6,3,200,573,784,1312,3714],[(152,139460)]),([6,3,200,573,1312,3714],[(0,172228),(2,172228),(4,172228),(6,172228),(8,172228),(10,199849),(12,172228),(14,172228),(16,172228),(18,172228),(57,172228),(58,172228),(74,32842),(77,172074),(97,163883),(98,172228),(105,167113),(106,172228),(129,172074),(130,172065),(154,173417),(157,368714)]),([6,3,200,768,1312,3714,4034],[(80,0),(112,199849),(168,199745)]),([6,3,200,784,829,1312,3714],[]),([6,3,200,784,829,1312,3715],[(72,0)]),([6,3,200,784,829,1512,3714],[(108,32906)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_67 : K_67.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_68 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,200,784,829,2783,3714],[]),([6,3,200,784,1312,1853,3714],[]),([6,3,200,784,1312,2754,3714],[(128,32939)]),([6,3,200,784,1312,3714,3722],[(80,0),(128,32964),(180,32906),(200,32906)]),([6,3,200,784,1312,3714,4034],[(112,199817),(168,199745)]),([6,3,200,784,1312,3714,4050],[(80,0),(168,199745)]),([6,3,200,784,1312,3715,4034],[(112,32905)]),([6,3,200,784,1312,3722],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,32906),(16,32906),(18,140321),(57,32906),(58,32906),(73,32906),(74,32906),(80,0),(81,32906),(82,32906),(97,32906),(98,32906),(105,32906),(106,32906),(141,32906)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_68 : K_68.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_69 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,200,784,1315,1341,3714],[(56,40073),(72,42113)]),([6,3,200,784,1320,3714],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,32906),(16,32906),(18,140321),(57,32906),(58,32906),(73,32906),(74,32906),(80,0),(81,32906),(82,32906),(97,32906),(98,32906)]),([6,3,200,784,1341,1512,3714],[(80,0),(108,32906),(156,32906)]),([6,3,200,784,1341,2783,3714],[]),([6,3,200,784,1341,3714,3775],[(196,139460)]),([6,3,200,784,1341,3714,4002],[]),([6,3,200,784,1341,3714,4034],[]),([6,3,200,784,1512,3714,4034],[(112,199817),(156,32905),(168,199745),(196,32906)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_69 : K_69.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_70 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,200,784,2783,3714,4034],[(156,199755),(168,199745)]),([6,3,200,1840,3714,3775],[(0,139460),(2,139460),(4,139460),(6,139460),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,32906),(57,139460),(58,139460),(73,139460),(74,139460),(81,139460),(82,139460),(97,139460),(106,32906),(117,73924),(130,139460),(133,139460),(141,32906),(149,73924),(154,139460),(157,139460)]),([6,3,200,1840,3714,4034],[(0,199817),(2,199817),(4,199817),(6,199817),(8,199817),(10,199817),(12,199817),(14,199817),(16,199817),(18,139460),(57,199817),(58,199817),(73,199817),(74,199817),(81,199817),(82,199817),(97,199817),(98,32905),(110,32905),(114,199817),(117,199753),(130,199817),(154,199817),(157,199817)]),([6,3,203,784,829,1312,3714],[(72,40105),(96,32906),(128,40073)]),([6,3,203,784,1312,3714,4034],[(72,40298),(96,40299),(112,199817)]),([6,3,784,829,984,1312,3714],[(56,131140)]),([6,3,784,829,1312,1512,3714],[(96,163883),(192,167050)]),([6,3,784,829,1312,3714,3895],[])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_70 : K_70.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_71 : List (List ℕ × List (ℕ × ℕ)) := [([6,3,784,984,1312,3714,4034],[(56,131114),(104,199817),(136,199816),(168,199745),(176,0)]),([6,3,784,1312,3714,3895,4034],[(80,199817),(168,199745)]),([6,8,61,200,784,1312,3715],[(96,0),(112,0),(152,139297)]),([6,8,200,784,1312,3714,3715],[(72,0),(80,0),(128,32964)]),([6,9,61,200,784,1312,3714],[(112,0)]),([6,9,200,203,784,1312,3714],[(96,0),(104,0)]),([6,9,200,784,1312,3714],[(10,0),(74,0),(80,0),(82,0),(97,0),(105,0)]),([6,11,61,200,784,1312,3714],[(112,0),(188,140321)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_71 : K_71.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_72 : List (List ℕ × List (ℕ × ℕ)) := [([6,11,200,784,1312,3714],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,32906),(16,32906),(18,140321),(58,32906),(73,32906),(74,32906),(80,0),(81,32906),(82,32906),(97,32906),(98,32906),(105,32906),(106,32906),(141,32906)]),([6,16,61,200,784,1312,3715],[(72,134186),(128,139297),(152,172065),(168,131114)]),([6,60,61,200,784,1312,3714],[(60,32968),(96,65578),(104,0),(128,65579),(168,65736)]),([6,60,200,784,1312,3714],[(0,32968),(2,199745),(4,32968),(6,40129),(8,32968),(10,32968),(12,32968),(14,32968),(16,32968),(18,203809),(73,32906),(74,32968),(81,32968),(82,32968),(97,32939),(98,32968),(105,32968),(106,32968),(113,32968),(114,32968),(129,65732),(130,32968),(146,32968),(149,32968),(154,32968),(157,32968)]),([6,61,61,200,784,1312,3715],[(96,0)]),([6,61,63,200,784,1312,3715],[(96,0)]),([6,61,63,203,784,1312,3714],[(56,32968),(96,0),(104,40298),(136,40299)]),([6,61,128,200,784,1312,3715],[(104,0),(152,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_72 : K_72.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_73 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,128,203,784,1312],[(0,140321),(2,32906),(4,140321),(6,140321),(8,140321),(10,140321),(12,140321),(14,140321),(16,140321),(18,140321),(57,140321),(82,140321),(85,140321),(98,0),(104,0),(105,140321),(106,140321),(113,131114),(114,42113),(137,140321),(138,140321),(145,163883),(146,43169),(153,140321),(154,139297)]),([6,61,128,203,784,1312,3714],[(104,0),(152,139457),(180,140321),(196,172065),(204,139297)]),([6,61,131,200,784,1312],[(0,140321),(2,32906),(4,140321),(6,140321),(8,140321),(10,140321),(12,140321),(14,140321),(16,140321),(18,140321),(98,0),(105,131114),(106,42113),(113,134346),(114,205956),(137,163883),(138,43169),(145,167115),(146,207012),(153,140321),(154,139297)]),([6,61,131,200,784,1312,3714],[(152,139460),(196,172065),(204,139297)]),([6,61,200,200,784,1312,3715],[(104,0),(152,139297)]),([6,61,200,201,784,1312,3714],[(104,0),(152,139460),(180,140481)]),([6,61,200,203,381,784,1312],[(116,203841),(136,0),(152,204138),(192,204139),(200,139460)]),([6,61,200,203,784,1312,3714],[(104,0),(152,139460),(180,140321)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_73 : K_73.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_74 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,200,203,784,1312,3715],[(104,0),(152,139297),(180,140321),(188,140321)]),([6,61,200,203,784,1341,3714],[(56,139304),(104,0),(136,139457)]),([6,61,200,203,784,1512,3714],[(60,32906),(104,204865),(152,139460),(180,206913),(204,139297)]),([6,61,200,203,784,2783,3714],[(180,140321),(204,370888)]),([6,61,200,203,1840,3714],[(0,139460),(2,199817),(4,139460),(6,139460),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(82,139460),(85,139460),(105,139460),(106,139460),(113,131114),(114,42113),(129,139460),(130,140321),(141,139457),(142,139297),(145,139460),(150,139460),(154,139460),(157,368840)]),([6,61,200,253,784,1312,3715],[(96,0),(112,172228),(144,139460),(188,140484)]),([6,61,200,256,784,1312,3715],[(96,0)]),([6,61,200,259,784,1312,3714],[(96,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_74 : K_74.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_75 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,200,380,784,1312],[(14,0),(98,0),(106,0),(112,0),(113,140321),(114,172065),(129,0),(137,0),(145,174113),(146,139297),(153,172065),(154,139297)]),([6,61,200,380,784,1312,3714],[(76,32968),(112,65578),(144,65579),(152,139460),(196,172065),(204,139297)]),([6,61,200,380,784,1312,3715],[(112,172065),(144,139297),(152,139297),(196,172065),(204,139297)]),([6,61,200,381,784,1312,3715],[(112,172228),(144,139460),(152,139460)]),([6,61,200,381,784,1312,4092],[(112,204138),(144,204139),(152,139460),(172,203809)]),([6,61,200,512,784,1312,3715],[(116,172065),(152,139297)]),([6,61,200,512,1312,3715],[(0,172065),(2,32937),(4,172065),(6,172065),(8,172065),(10,172065),(12,172065),(14,172065),(16,172065),(18,172065),(73,172065),(81,172065),(82,172065),(105,167113),(106,204964),(112,0),(113,172065),(114,172065),(146,172065),(149,172065),(154,163881),(157,41025)]),([6,61,200,515,784,1312,3714],[(152,139460)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_75 : K_75.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_76 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,200,784,784,1312,3715],[(144,139297),(184,131114)]),([6,61,200,784,785,1312,3714],[(80,131112),(144,131115),(184,131272),(192,131114)]),([6,61,200,784,787,1312,3715],[(72,0),(80,0),(144,139297),(192,131114)]),([6,61,200,784,829,1312,3715],[(112,0)]),([6,61,200,784,984,1312,3715],[(72,0),(112,0),(144,139297),(152,139297),(184,131114)]),([6,61,200,784,1312,1840,3715],[(80,0),(112,139297),(144,172065),(152,139297),(184,131114),(192,163883),(200,163883)]),([6,61,200,784,1312,2783,3715],[(112,172065),(148,172065),(192,43169),(204,174113)]),([6,61,200,784,1312,3712,4092],[(112,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_76 : K_76.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_77 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,200,784,1312,3714,3715],[(112,139460),(148,172065),(156,139297)]),([6,61,200,784,1312,3714,3787],[(80,0),(112,139460)]),([6,61,200,784,1312,3714,3892],[(80,0),(112,139460),(140,140321),(200,65736)]),([6,61,200,784,1312,3714,4035],[(72,0)]),([6,61,200,784,1312,3714,4092],[(112,139460),(172,32968)]),([6,61,200,784,1312,3714,4094],[(112,139460),(172,32968)]),([6,61,200,784,1312,3715],[(10,0),(74,0),(82,0),(97,0),(105,0),(113,172065),(114,139297),(146,131114),(149,172065),(154,163883),(157,139297)]),([6,61,200,784,1312,3715,3715],[(112,139297),(148,172065),(156,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_77 : K_77.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_78 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,200,784,1312,3715,3775],[(72,0),(188,172065),(196,139297)]),([6,61,200,784,1312,3715,3786],[(80,0),(112,139460),(188,172065),(196,139297)]),([6,61,200,784,1312,3715,3787],[(80,0),(112,139297),(188,172065),(196,139297)]),([6,61,200,784,1312,3715,3895],[(80,0),(112,139297)]),([6,61,200,784,1312,3715,3986],[(72,0),(80,0),(112,139460),(196,0),(200,131114)]),([6,61,200,784,1312,3715,3987],[(72,0),(80,0),(112,139297),(156,131113),(196,0),(200,131114)]),([6,61,200,784,1312,3715,4034],[(72,0),(196,0)]),([6,61,200,784,1312,3715,4092],[(112,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_78 : K_78.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_79 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,200,784,1312,3987],[(0,131114),(2,32906),(4,131114),(6,131114),(8,131114),(10,42113),(12,131114),(14,131114),(16,131114),(18,131114),(80,0),(81,140321),(82,131114),(97,140321),(98,131114),(105,131114),(106,131114),(113,131114),(114,139297),(146,131114),(149,131114),(154,163883),(157,131114)]),([6,61,200,784,1341,3714,3715],[(156,139297),(196,139460)]),([6,61,200,784,1341,3714,4092],[(196,65579)]),([6,61,200,784,1341,3715],[(10,0),(82,0),(106,139460),(113,0),(146,131114),(157,139460)]),([6,61,200,784,1512,3714,3715],[(112,204932),(148,204964),(156,139297)]),([6,61,200,784,1512,3714,4092],[(60,32906),(112,204932),(156,139297),(172,32968)]),([6,61,200,784,1512,3715],[(10,0),(98,139460),(113,204964),(114,139297),(146,131114),(149,204964),(157,139297)]),([6,61,200,784,1840,3715],[(0,139297),(2,32905),(4,139297),(6,139297),(8,139297),(10,139297),(12,139297),(14,139297),(16,139297),(18,139297),(78,172065),(81,139297),(82,139297),(86,139297),(105,139297),(106,139297),(113,139297),(114,139297),(117,139297),(145,139297),(146,139297),(149,139297),(154,163883),(157,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_79 : K_79.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_80 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,200,784,2783,3714,3715],[(148,172065),(156,139460),(196,43073)]),([6,61,200,784,2783,3714,4092],[(156,370888),(172,32968)]),([6,61,200,784,2783,3715],[(114,139297),(117,172065),(146,131114),(149,172065),(157,139297),(158,174113)]),([6,61,200,787,1315,3714],[(0,41160),(2,41160),(4,41160),(6,41160),(8,41160),(10,41160),(12,41160),(14,41160),(16,41160),(18,42113),(61,32906),(73,32906),(81,41160),(82,41160),(97,32939),(105,41160),(106,41160),(129,32906),(130,41160)]),([6,61,200,787,1840,3714],[(0,131114),(2,199817),(4,131114),(6,131114),(8,131114),(10,131114),(12,131114),(14,42113),(16,131114),(18,131114),(78,131114),(81,131114),(82,131114),(105,139460),(106,131114),(113,131114),(129,139460),(130,131114),(142,131113),(145,131114),(146,131113),(154,139460)]),([6,61,200,1840,1843,3714],[(0,131114),(2,199817),(4,131114),(6,131114),(8,131114),(10,42113),(12,131114),(14,131114),(16,131114),(18,131114),(81,139460),(82,131114),(102,131114),(105,131114),(106,131114),(114,131114),(117,131114),(129,139460),(130,131114),(142,131113),(146,139460),(153,131114),(154,131113)]),([6,61,200,1840,3714,3715],[(0,139460),(2,199817),(4,139460),(6,139460),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(81,134345),(82,204932),(97,139460),(102,139297),(106,139460),(110,139297),(114,139460),(117,204840),(118,139297),(129,139460),(134,139460),(138,139460),(146,131114),(149,204840),(153,139297),(154,139460),(157,139460)]),([6,61,200,1840,3714,4092],[(0,139460),(2,199817),(4,139460),(6,139460),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(81,134345),(82,204932),(97,139460),(98,140321),(110,139297),(114,139460),(117,368840),(133,32968),(138,139460),(141,139460),(146,139460),(149,139460),(154,139460),(157,139297)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_80 : K_80.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_81 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,200,1840,3715],[(5,139297),(7,139297),(9,139297),(11,139297),(13,139297),(15,139297),(63,139297),(83,139297),(87,139297),(103,139460),(107,139297),(111,139297),(115,139297),(119,139297)]),([6,61,201,784,1312,3714],[(10,0),(74,0),(82,0),(97,0),(105,0),(113,172225),(114,139457),(142,140481),(146,140481),(149,172225),(154,174273),(157,139457)]),([6,61,203,253,784,1312,3714],[(96,172072),(112,172225),(128,139304),(144,139457),(168,140321),(188,140321)]),([6,61,203,784,787,1312,3714],[(72,40105),(96,32906),(112,40298),(144,139460),(152,40299),(184,40298)]),([6,61,203,784,984,1312,3714],[(72,0),(112,0),(144,139460),(152,139460),(184,140484),(196,174113)]),([6,61,203,784,1312,3714,3895],[(112,139460),(168,40129)]),([6,61,203,784,1312,3714,4092],[(112,139460)]),([6,61,203,784,1315,3714],[(0,40299),(2,40299),(4,40299),(6,68651),(8,40299),(10,40299),(12,40299),(14,370728),(16,40299),(18,40299),(61,40073),(73,40073),(74,40299),(81,40299),(82,40299),(97,32939),(98,40299),(113,43076),(114,40299),(129,32906),(130,40299),(142,40299),(146,40299),(149,40299),(154,40299),(157,40299)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_81 : K_81.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_82 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,203,784,1512,3714],[(10,0),(81,131114),(82,42113),(98,139457),(101,32906),(113,204865),(114,139460),(129,32906),(130,140321),(142,206913),(146,140484),(149,204865),(156,0),(157,139457),(158,140321)]),([6,61,784,787,984,1312,3714],[(56,131140),(80,131114),(104,131114),(136,139460),(176,140484),(184,140321)]),([6,61,784,984,987,1312,3714],[(136,134345),(144,134345),(176,134344),(188,174113)]),([6,61,784,984,1312,3714,3715],[(104,134187),(136,0),(156,134345),(176,134209)]),([6,61,784,984,1312,3714,4092],[(104,134345),(136,134344),(172,32968)]),([6,61,784,984,1312,3715],[(6,0),(10,0),(97,0),(105,0),(106,139297),(114,134345),(136,0),(137,0),(138,140321),(154,163883),(157,134345)]),([6,61,784,1312,3714,3715,3895],[(80,139460),(108,172065),(116,139297)]),([6,61,784,1312,3714,3895,4092],[(80,139460),(172,40129)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_82 : K_82.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_83 : List (List ℕ × List (ℕ × ℕ)) := [([6,61,784,1312,3715,3895],[(6,0),(58,0),(73,0),(81,172065),(82,139297),(106,131114),(109,172065),(114,163883),(117,139297)]),([6,61,784,1315,1512,3714],[(0,163883),(2,163883),(4,163883),(6,163883),(8,163883),(10,65700),(12,163883),(14,43169),(16,163883),(18,163883),(57,163883),(58,163883),(73,32939),(78,163880),(81,163883),(82,166977),(101,32906),(105,166977),(106,163883),(129,32906),(130,163883),(138,163883),(141,163883),(145,166977),(146,163883),(158,163908)]),([6,63,200,784,1312,3714,3715],[(112,139460)]),([6,63,203,784,1312,3714],[(0,32968),(2,196648),(4,32968),(6,32968),(8,32968),(10,32968),(12,32968),(14,32968),(16,32968),(18,203809),(61,32906),(73,32906),(74,32968),(81,32968),(82,32968),(97,32939),(98,32968),(105,32968),(106,32968),(113,32968),(114,32968),(142,32968),(146,32968),(149,32968),(154,32968),(157,32968)]),([6,200,203,784,829,1312,3714],[(72,0)]),([6,200,203,784,1312,3714,4034],[(72,0),(112,199817),(132,32906),(172,32906)]),([6,200,784,787,829,1312,3714],[(56,131140)]),([6,200,784,829,1312,3714,3715],[(136,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_83 : K_83.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_84 : List (List ℕ × List (ℕ × ℕ)) := [([6,200,784,829,1312,3714,4092],[(188,32906)]),([6,200,784,829,1312,3715],[(6,0),(10,0),(58,0),(109,0),(137,0),(154,163883)]),([6,200,784,1312,3714,3715,3775],[(80,139460)]),([6,200,784,1312,3714,3715,4034],[(80,199817),(108,32937),(116,32905),(200,199745)]),([6,200,784,1312,3714,4034,4035],[(140,199745),(148,199745),(156,199745),(200,199745)]),([6,200,784,1312,3714,4034,4092],[(80,199817)]),([6,200,784,1312,3714,4035],[(0,199745),(2,199745),(4,199745),(6,199745),(8,199745),(10,199745),(12,199745),(14,199745),(16,199745),(18,32968),(57,199745),(58,199745),(73,199745),(74,199745),(81,199745),(82,199745),(106,199745),(109,199745),(114,199745),(117,199745),(138,199745),(141,199745),(146,199745),(149,199745),(154,199745),(157,199745)]),([6,200,784,1312,3715,4034],[(6,0),(58,0),(73,0),(81,32937),(82,32905),(106,32906),(109,32937),(114,32939),(117,32905),(146,0),(149,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_84 : K_84.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_85 : List (List ℕ × List (ℕ × ℕ)) := [([7,0,3,61,200,784,1312,3714],[(200,139460)]),([7,1,3,61,200,784,1312,3714],[(128,0),(200,139460)]),([7,1,61,200,784,1312,3714],[(14,0),(98,0),(106,0),(114,0),(129,0),(137,0),(145,0),(153,172228),(154,139460),(190,140484),(194,140484),(197,172228),(202,174276),(205,139460)]),([7,2,3,61,200,784,1312,3714],[(72,32968),(96,40001),(128,42049),(168,43073),(200,139460)]),([7,3,3,61,200,784,1312,3714],[(72,32968),(128,42113),(168,43169),(200,139460)]),([7,3,8,61,200,784,1312,3714],[(84,32906),(136,0),(152,0),(244,140321)]),([7,3,8,200,784,1312,3714],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,32906),(16,32906),(18,32906),(20,32906),(22,140321),(57,32906),(58,32906),(73,32906),(74,32906),(82,32906),(85,32906),(97,32906),(98,32906),(104,0),(105,32906),(106,32906),(112,0),(113,32906),(114,32906),(129,32906),(130,32906),(137,32906),(138,32906),(145,32906),(146,32906),(178,32906),(189,32906)]),([7,3,16,61,200,784,1312,3714],[(56,131434),(104,134506),(176,139460),(200,172228),(224,140484)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_85 : K_85.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_86 : List (List ℕ × List (ℕ × ℕ)) := [([7,3,61,61,200,784,1312,3714],[(136,0),(224,140321)]),([7,3,61,63,200,784,1312,3714],[(80,32968),(136,0),(144,42049),(184,43073),(232,140321)]),([7,3,61,128,200,784,1312],[(0,140321),(2,140321),(4,140321),(6,32906),(8,140321),(10,140321),(12,140321),(14,140321),(16,140321),(18,140321),(20,140321),(22,140321),(61,140484),(73,140321),(74,140321),(81,140321),(97,140321),(98,140321),(110,140321),(114,140321),(117,140321),(129,131114),(130,140321),(138,0),(144,0),(145,140321),(146,140321),(153,134346),(154,205956),(169,163883),(170,140321),(185,140321),(186,140321),(193,167115),(194,207012),(201,140321),(202,139297)]),([7,3,61,128,200,784,1312,3714],[(108,32906),(144,0),(200,139460),(236,140321),(252,172065),(260,139297)]),([7,3,61,200,200,784,1312,3714],[(84,32906),(144,0),(200,139460),(236,140321)]),([7,3,61,200,203,784,1312,3714],[(56,32968),(84,32906),(128,42113),(144,0),(152,42113),(168,43169),(192,43169),(200,139460),(236,140321),(244,140484)]),([7,3,61,200,253,784,1312,3714],[(136,0),(152,172228),(192,139460),(224,140321),(244,140321)]),([7,3,61,200,256,784,1312,3714],[(136,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_86 : K_86.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_87 : List (List ℕ × List (ℕ × ℕ)) := [([7,3,61,200,381,784,1312],[(18,0),(58,203809),(85,140321),(118,140321),(129,131114),(130,42113),(138,0),(146,0),(152,0),(153,140484),(154,172228),(169,163883),(170,43169),(177,0),(185,0),(193,174276),(194,139460),(201,172228),(202,139460)]),([7,3,61,200,381,784,1312,3714],[(152,172228),(192,139460),(200,139460),(224,140321),(252,172228),(260,139460)]),([7,3,61,200,512,784,1312,3714],[(156,172228),(200,139460)]),([7,3,61,200,512,1312,3714],[(0,172228),(2,172228),(4,172228),(6,199849),(8,172228),(10,172228),(12,172228),(14,172228),(16,172228),(18,172228),(20,172228),(22,172228),(58,32968),(61,172228),(73,172228),(74,172228),(97,172228),(98,172228),(105,172228),(113,172228),(114,172228),(129,163883),(130,172228),(145,167113),(146,204964),(152,0),(153,172228),(154,172228),(169,172228),(170,172065),(177,172228),(178,174113),(190,172065),(194,172228),(197,172228),(202,172228),(205,368840)]),([7,3,61,200,784,784,1312,3714],[(96,131114),(192,139460),(240,140484)]),([7,3,61,200,784,787,1312,3714],[(56,32968),(104,0),(112,0),(128,131114),(136,32906),(152,42113),(168,43169),(192,139460),(200,139460),(240,140484),(248,140321)]),([7,3,61,200,784,829,1312,3714],[(152,0),(240,0),(248,140321)]),([7,3,61,200,784,984,1312,3714],[(84,32906),(96,131114),(104,0),(128,131114),(140,32939),(152,0),(192,139460),(200,139460),(236,134346),(240,140484),(252,174113)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_87 : K_87.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_88 : List (List ℕ × List (ℕ × ℕ)) := [([7,3,61,200,784,1312,1840,3714],[(96,131114),(112,0),(128,163883),(152,139460),(168,163883),(192,172228),(200,139460),(240,140484),(248,174276),(256,140484)]),([7,3,61,200,784,1312,2783,3714],[(128,43169),(152,172228),(196,172228),(248,174276),(260,174276)]),([7,3,61,200,784,1312,3714],[(14,0),(58,32968),(85,32906),(97,131114),(98,42113),(106,0),(114,0),(129,163883),(130,43169),(137,0),(145,0),(153,172228),(154,139460),(177,32906),(178,140321),(190,140321),(194,140484),(197,172228),(202,174276),(205,139460)]),([7,3,61,200,784,1312,3714,3714],[(152,139460),(176,32906),(196,172228),(204,139460)]),([7,3,61,200,784,1312,3714,3715],[(152,139460),(196,172065),(204,139297),(224,32906),(244,172228),(252,139460)]),([7,3,61,200,784,1312,3714,3775],[(104,0),(196,174113),(204,140321),(224,32906),(244,172228),(252,139460),(256,140321)]),([7,3,61,200,784,1312,3714,3786],[(112,0),(152,139460),(176,32906),(228,32906),(244,172228),(252,139460)]),([7,3,61,200,784,1312,3714,3895],[(84,32906),(112,0),(152,139460),(188,140321),(224,32906),(256,140321)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_88 : K_88.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_89 : List (List ℕ × List (ℕ × ℕ)) := [([7,3,61,200,784,1312,3714,3986],[(104,0),(112,0),(152,139460),(204,139460),(216,131114),(224,32906),(252,0),(256,140484)]),([7,3,61,200,784,1312,3714,4034],[(104,0),(176,32906),(252,0)]),([7,3,61,200,784,1312,3714,4092],[(56,32968),(96,131114),(128,163883),(152,139460),(228,32968)]),([7,3,61,200,784,1312,3715],[(14,0),(98,0),(106,0),(114,0),(129,0),(137,0),(145,0),(153,172065),(154,139297),(178,140321),(190,140321),(194,140321),(197,172065),(202,174113),(205,139297)]),([7,3,61,200,784,1312,3775],[(0,140321),(2,140321),(4,140321),(6,32906),(8,140321),(10,140321),(12,140321),(14,140321),(16,140321),(18,140321),(20,140321),(22,140321),(73,140321),(74,140321),(81,140321),(97,131114),(98,140321),(106,0),(113,140321),(114,140321),(129,163883),(130,140321),(145,140321),(146,140321),(153,140321),(154,140321),(170,140321),(173,140321),(178,140321),(181,140321),(189,140321),(190,140321),(194,140321),(197,140321),(202,140321),(205,140321)]),([7,3,61,200,784,1312,3986],[(0,140484),(2,140484),(4,140484),(6,199818),(8,140484),(10,140484),(12,140484),(14,140484),(16,140484),(18,140484),(20,140484),(22,140484),(58,32968),(61,140484),(73,140484),(74,140484),(97,140484),(98,140484),(106,0),(112,0),(113,140484),(114,140484),(129,163883),(130,140484),(137,140484),(145,140484),(146,140484),(153,140484),(154,139460),(169,140484),(170,140321),(178,140321),(190,140321),(194,140484),(197,140484),(202,140484),(205,140484)]),([7,3,61,200,784,1315,3714],[(0,43169),(2,163883),(4,43169),(6,43169),(8,43169),(10,43169),(12,43169),(14,43169),(16,43169),(18,43169),(20,43169),(22,43169),(58,32968),(73,43169),(85,32906),(97,43169),(105,43169),(106,43169),(113,43169),(114,43169),(130,43169),(133,43169),(137,32939),(138,43073),(145,43169),(146,43169),(153,172228),(154,139460),(177,32906),(178,140321),(190,140321),(194,140484),(197,172228),(202,174113),(205,139460)]),([7,3,61,200,784,1341,3714],[(14,0),(97,131114),(98,42113),(114,0),(130,43073),(146,139460),(153,0),(205,139460)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_89 : K_89.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_90 : List (List ℕ × List (ℕ × ℕ)) := [([7,3,61,200,784,1512,3714],[(14,0),(58,32968),(85,32906),(97,131114),(98,42113),(129,163883),(130,43169),(138,139460),(141,32906),(153,204964),(154,139460),(177,32906),(178,140321),(190,207012),(194,140484),(197,204964),(204,0),(205,139460),(206,140321)]),([7,3,61,200,784,1840,3714],[(0,139460),(2,139460),(4,139460),(6,199817),(8,139460),(10,139460),(12,139460),(14,139460),(16,139460),(18,139460),(20,139460),(22,139460),(58,32968),(61,139460),(73,139460),(74,139460),(97,139460),(98,139460),(102,139460),(110,172228),(113,139460),(114,139460),(118,139460),(129,163883),(130,139460),(145,139460),(146,139460),(153,139460),(154,139460),(157,139460),(169,139460),(170,139297),(177,139460),(178,140321),(190,139297),(193,139460),(194,139460),(197,139460),(202,139460),(205,139460)]),([7,3,61,200,784,2783,3714],[(58,32968),(85,32906),(97,131114),(98,42113),(154,139460),(157,172228),(177,32906),(178,140321),(190,140321),(194,140484),(197,172228),(205,139460),(206,174276)]),([7,3,61,200,1840,3714],[(1,139460),(3,139460),(9,139460),(11,139460),(13,139460),(15,139460),(17,139460),(19,139460),(63,139460),(75,139460),(79,139460),(99,139460),(103,139460),(115,139460),(119,139460),(131,139460),(135,139460),(143,139460),(147,139460),(151,139460),(155,139460),(159,139460)]),([7,3,61,203,784,1312,3714],[(14,0),(58,32968),(96,0),(98,0),(106,0),(114,0),(129,0),(137,0),(145,0),(153,172228),(154,139460),(177,32906),(178,140321),(190,140484),(194,140484),(197,172228),(202,174276),(205,139460)]),([7,3,61,784,984,1312,3714],[(10,0),(14,0),(58,32968),(72,0),(74,0),(109,32939),(129,163883),(130,43169),(137,0),(145,0),(146,139460),(154,134345),(177,32906),(178,140321),(184,0),(185,0),(186,140484),(198,174113),(202,174276),(205,134345)]),([7,3,61,784,1312,3714,3895],[(10,0),(58,32968),(73,131114),(74,42113),(82,0),(97,163883),(98,43169),(105,0),(113,172228),(114,139460),(137,32906),(138,140321),(146,140484),(149,172228),(154,174276),(157,139460),(177,32906),(201,140321)]),([7,3,63,200,784,1312,3714],[(0,32968),(2,32968),(4,32968),(6,32968),(8,32968),(10,32968),(12,32968),(14,32968),(16,32968),(18,32968),(20,32968),(22,203809),(58,32968),(61,32968),(73,32968),(74,32968),(85,32906),(97,32968),(98,32968),(105,32906),(106,32968),(113,32968),(114,32968),(129,32968),(130,32968),(137,32939),(138,32968),(145,32968),(146,32968),(153,32968),(154,32968),(177,32906),(194,32968),(197,32968),(202,32968),(205,32968)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_90 : K_90.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_91 : List (List ℕ × List (ℕ × ℕ)) := [([7,3,200,784,829,1312,3714],[(10,0),(14,0),(74,0),(82,0),(98,32906),(110,32906),(129,163883),(130,43169),(149,0),(185,0),(193,32906),(202,174276)]),([7,3,200,784,1312,3714,3775],[(0,32906),(2,32906),(4,32906),(6,32906),(8,32906),(10,32906),(12,32906),(14,32906),(16,32906),(18,140321),(20,32906),(22,32906),(57,32906),(58,32906),(73,32906),(74,32906),(81,32906),(82,32906),(97,32906),(98,32906),(105,32906),(106,32906),(113,172228),(114,139460),(138,32906),(149,172228),(157,139460),(170,32906),(173,32906),(181,32906),(182,32906),(186,32906),(189,172228),(194,32906),(197,139460),(202,32906),(205,32906)]),([7,3,200,784,1312,3714,4034],[(10,0),(73,131114),(74,42113),(82,0),(97,163883),(98,43169),(105,0),(113,199849),(114,199817),(142,32906),(146,199818),(149,199849),(154,199851),(157,199817),(170,32968),(182,32906),(194,0),(197,0)]),([7,61,200,203,784,1312,3714],[(14,0),(61,32906),(98,0),(104,0),(106,0),(113,131114),(114,42113),(129,0),(137,0),(145,163883),(146,43169),(153,172228),(154,139460),(169,32906),(170,140321),(182,140321),(190,140484),(194,140484),(197,172228),(202,174276),(205,139460)]),([7,61,200,784,787,1312,3714],[(0,131114),(2,131114),(4,131114),(6,131114),(8,131114),(10,42113),(12,131114),(14,131114),(16,131114),(18,131114),(20,131114),(22,131114),(61,32906),(80,0),(82,131114),(97,32906),(102,131114),(105,131114),(106,131114),(114,131114),(117,131114),(129,131114),(130,131114),(137,131114),(138,131114),(145,131114),(146,139460),(153,163883),(154,43169),(169,32906),(170,131114),(182,131114),(186,140484),(193,131114),(194,131114),(202,131114),(205,131114)]),([7,61,200,784,1312,3714,3715],[(10,0),(74,0),(82,0),(97,0),(105,0),(113,172228),(114,139460),(149,172228),(154,0),(156,0),(157,139460),(158,0),(186,131114),(189,172228),(194,163883),(197,139460)]),([7,61,200,784,1312,3714,4092],[(10,0),(61,32906),(74,0),(82,0),(97,0),(105,0),(113,172228),(114,139460),(129,32906),(130,140321),(142,140321),(146,140484),(149,172228),(154,174276),(157,139460),(173,32968)]),([7,61,200,784,1312,3715],[(10,0),(11,0),(13,0),(74,0),(82,0),(97,0),(99,0),(103,0),(105,0),(107,0),(113,0),(154,0),(155,0),(157,0),(159,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_91 : K_91.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

noncomputable def K_92 : List (List ℕ × List (ℕ × ℕ)) := [([8,3,61,200,784,1312,3714],[(14,0),(15,0),(17,0),(98,0),(106,0),(114,0),(129,0),(131,0),(137,0),(139,0),(143,0),(145,0),(147,0),(153,0),(202,0),(203,0),(205,0),(207,0)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_92 : K_92.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = (((((((K_0 ++ K_1) ++ (K_2 ++ (K_3 ++ K_4))) ++ ((K_5 ++ (K_6 ++ K_7)) ++ (K_8 ++ (K_9 ++ K_10)))) ++ (((K_11 ++ (K_12 ++ K_13)) ++ (K_14 ++ (K_15 ++ K_16))) ++ ((K_17 ++ (K_18 ++ K_19)) ++ (K_20 ++ (K_21 ++ K_22))))) ++ ((((K_23 ++ K_24) ++ (K_25 ++ (K_26 ++ K_27))) ++ ((K_28 ++ (K_29 ++ K_30)) ++ (K_31 ++ (K_32 ++ K_33)))) ++ (((K_34 ++ (K_35 ++ K_36)) ++ (K_37 ++ (K_38 ++ K_39))) ++ ((K_40 ++ (K_41 ++ K_42)) ++ (K_43 ++ (K_44 ++ K_45)))))) ++ (((((K_46 ++ K_47) ++ (K_48 ++ (K_49 ++ K_50))) ++ ((K_51 ++ (K_52 ++ K_53)) ++ (K_54 ++ (K_55 ++ K_56)))) ++ (((K_57 ++ (K_58 ++ K_59)) ++ (K_60 ++ (K_61 ++ K_62))) ++ ((K_63 ++ (K_64 ++ K_65)) ++ (K_66 ++ (K_67 ++ K_68))))) ++ ((((K_69 ++ (K_70 ++ K_71)) ++ (K_72 ++ (K_73 ++ K_74))) ++ ((K_75 ++ (K_76 ++ K_77)) ++ (K_78 ++ (K_79 ++ K_80)))) ++ (((K_81 ++ (K_82 ++ K_83)) ++ (K_84 ++ (K_85 ++ K_86))) ++ ((K_87 ++ (K_88 ++ K_89)) ++ (K_90 ++ (K_91 ++ K_92)))))))).map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app (all_app c_0 c_1) (all_app c_2 (all_app c_3 c_4))) (all_app (all_app c_5 (all_app c_6 c_7)) (all_app c_8 (all_app c_9 c_10)))) (all_app (all_app (all_app c_11 (all_app c_12 c_13)) (all_app c_14 (all_app c_15 c_16))) (all_app (all_app c_17 (all_app c_18 c_19)) (all_app c_20 (all_app c_21 c_22))))) (all_app (all_app (all_app (all_app c_23 c_24) (all_app c_25 (all_app c_26 c_27))) (all_app (all_app c_28 (all_app c_29 c_30)) (all_app c_31 (all_app c_32 c_33)))) (all_app (all_app (all_app c_34 (all_app c_35 c_36)) (all_app c_37 (all_app c_38 c_39))) (all_app (all_app c_40 (all_app c_41 c_42)) (all_app c_43 (all_app c_44 c_45)))))) (all_app (all_app (all_app (all_app (all_app c_46 c_47) (all_app c_48 (all_app c_49 c_50))) (all_app (all_app c_51 (all_app c_52 c_53)) (all_app c_54 (all_app c_55 c_56)))) (all_app (all_app (all_app c_57 (all_app c_58 c_59)) (all_app c_60 (all_app c_61 c_62))) (all_app (all_app c_63 (all_app c_64 c_65)) (all_app c_66 (all_app c_67 c_68))))) (all_app (all_app (all_app (all_app c_69 (all_app c_70 c_71)) (all_app c_72 (all_app c_73 c_74))) (all_app (all_app c_75 (all_app c_76 c_77)) (all_app c_78 (all_app c_79 c_80)))) (all_app (all_app (all_app c_81 (all_app c_82 c_83)) (all_app c_84 (all_app c_85 c_86))) (all_app (all_app c_87 (all_app c_88 c_89)) (all_app c_90 (all_app c_91 c_92)))))))

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
    refine ⟨pt 6 (pairCode (0,5)),pt 6 (pairCode (0,1)),?_⟩
    rw [he (0,5) (by decide +kernel),he (0,1) (by decide +kernel)]
    decide +kernel
  have hl := lb_cert f points M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel)
    encode (by decide +kernel) nc (by decide +kernel) (by decide +kernel) hT_cert
    (by decide +kernel) 8 ⟨C,hfan,hsize,fun _ => rfl⟩
  omega

end PEqualNP.Outside.L_meta_24685.Core

open PEqualNP.Outside.L_meta_24685.Core in
theorem PEqualNP.Outside.L_meta_24685 (C : PEqualNP.CircuitLowerBounds.Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsize : C.size ≤ 8) : ¬ Matches C :=
  coreLower C hfan hsize
