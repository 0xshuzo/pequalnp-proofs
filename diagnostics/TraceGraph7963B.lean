import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7963_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The circuit simplifier is adapted from L_meta_7328 and L_meta_1411
-- in open-goat/pequalnp-proofs under the Apache 2.0 license.
abbrev Stat := Bool ⊕ ℕ

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

def Good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma op_cases {g : Gate} (h : Good g) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  simpa using h.1

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

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
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Good g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Good]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Good]
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

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
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Good g) → Inv n y w acc →
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
    have hs := simplify_sound g.op (op_cases hgok) w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

-- Every gate with a constant input can be omitted. An absorbing input
-- additionally marks the gate output as a constant for the next gate.
def absorb : GateOp → Bool
  | .or => true
  | _ => false

lemma simplify_drop (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : ∃ b, Sum.inl b ∈ ins) :
    (simplify op m ins).1 = none := by
  rcases hc with ⟨b, hb⟩
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hb hl
  all_goals cases s <;> (try cases t) <;> simp_all [simplify, simpAnd, simpOr]

lemma simplify_absorb (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : Sum.inl (absorb op) ∈ ins) :
    (simplify op m ins).2 = Sum.inl (absorb op) := by
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hc hl
  all_goals cases s <;> (try cases t) <;> simp_all [absorb, simplify, simpAnd, simpOr]
  grind

abbrev State := List Stat × List Gate

def stat (s : State) (i : ℕ) : Stat := s.1.getD i (Sum.inl false)

def plan (n : ℕ) (s : State) (g : Gate) : Option Gate × Stat :=
  simplify g.op (n + s.2.length) (g.inputs.map (stat s))

lemma elim_append (n : ℕ) (pre post : List Gate) (s : State) :
    elim n (pre ++ post) s = elim n post (elim n pre s) := by
  simp [elim, List.foldl_append]

lemma elim_extends (n : ℕ) (gs : List Gate) (s : State) :
    ∃ t, (elim n gs s).1 = s.1 ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp [elim], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (elimStep n s g)
    refine ⟨(plan n s g).2 :: t, ?_, by simp [hlen]⟩
    change (elim n gs (elimStep n s g)).1 = _
    rw [ht]
    change (s.1 ++ [(plan n s g).2]) ++ t = _
    simp

lemma elim_stat (n : ℕ) (gs : List Gate) (s : State) (i : ℕ) (hi : i < s.1.length) :
    stat (elim n gs s) i = stat s i := by
  obtain ⟨t, ht, _⟩ := elim_extends n gs s
  unfold stat
  rw [ht, List.getD_append _ _ _ _ hi]

lemma elim_good (n : ℕ) (gs : List Gate) (s : State)
    (h : ∀ g ∈ gs, Good g) (hs : ∀ g ∈ s.2, Good g) :
    ∀ g ∈ (elim n gs s).2, Good g := by
  induction gs generalizing s with
  | nil => exact hs
  | cons g gs ih =>
    change ∀ g' ∈ (elim n gs (elimStep n s g)).2, Good g'
    apply ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    intro a ha
    change a ∈ s.2 ++ (plan n s g).1.toList at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hs a ha
    · exact simplify_ok _ _ _ a (by simpa [plan] using ha)

def fix {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i = p then b else x i

def initial {n : ℕ} (p : Fin n) (b : Bool) : State :=
  (List.ofFn fun i : Fin n => if i = p then Sum.inl b else Sum.inr i.val, [])

lemma initial_length {n : ℕ} (p : Fin n) (b : Bool) :
    (initial p b).1.length = n := by simp [initial]

lemma initial_stat {n : ℕ} (p : Fin n) (b : Bool) : stat (initial p b) p.val = Sum.inl b := by
  simp [stat, initial]

lemma initial_inv {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (fix p b x)) (initial p b) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change (stat (initial p b) j.val).Valid _ ∧ (stat (initial p b) j.val).val _ = _
    by_cases hj : j = p <;>
      simp [stat, initial, fix, hj, Stat.Valid, Stat.val, wiresFrom, j, hi] at * <;> simp_all
  · rw [List.getD_eq_default _ _ (by simpa [initial] using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial, rfl⟩

lemma drop_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} {b : Bool} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl b) :
    (plan n s g).1 = none := by
  apply simplify_drop _ (op_cases hg) _ _ (by simpa using hg.2)
  exact ⟨b, hb ▸ List.mem_map_of_mem hi⟩

lemma absorb_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl (absorb g.op)) :
    (plan n s g).2 = Sum.inl (absorb g.op) := by
  apply simplify_absorb _ (op_cases hg) _ _ (by simpa using hg.2)
  exact hb ▸ List.mem_map_of_mem hi

def gv (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

def controlled (s : State) (x y : List Bool) : Prop :=
  ∀ i, x.getD i false ≠ y.getD i false → ∃ b, stat s i = Sum.inl b

noncomputable def bonus (s : State) (x y : List Bool) : ℕ := by
  classical
  exact if controlled s x y then 0 else 1

lemma pointwise_step (n : ℕ) (s : State) (g : Gate) (x y : List Bool)
    (hx : x.length = s.1.length) (hy : y.length = s.1.length)
    (h : controlled s x y)
    (ho : gv g x ≠ gv g y → ∃ b, (plan n s g).2 = Sum.inl b) :
    controlled (elimStep n s g) (x ++ [gv g x]) (y ++ [gv g y]) := by
  intro i hi
  change ∃ b, (s.1 ++ [(plan n s g).2]).getD i (Sum.inl false) = Sum.inl b
  by_cases he : i = s.1.length
  · subst i
    rw [getD_snoc_eq]
    rw [getD_snoc_len _ _ _ _ hx, getD_snoc_len _ _ _ _ hy] at hi
    exact ho hi
  · rw [getD_snoc_ne _ _ _ _ he]
    rw [getD_snoc_ne _ _ _ _ (by simpa only [hx] using he),
      getD_snoc_ne _ _ _ _ (by simpa only [hy] using he)] at hi
    exact h _ hi

def raw (p q : ℕ) (g : Gate) : Bool := decide (p ∈ g.inputs ∨ q ∈ g.inputs)

lemma plan_all_const (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    (hh : ∀ i ∈ g.inputs, ∃ b, stat s i = Sum.inl b) :
    ∃ b, (plan n s g).2 = Sum.inl b := by
  obtain ⟨op, ins⟩ := g
  obtain ha | ha := op_cases hg <;> change op = _ at ha <;> subst op
  all_goals
    have hl := hg.2
    change ins.length ≤ 2 at hl
    change ∀ i ∈ ins, _ at hh
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨z,hz⟩ := hh i (by simp)
      simp [plan, hz, simplify, simpAnd, simpOr]
    · obtain ⟨z,hz⟩ := hh i (by simp)
      obtain ⟨v,hv⟩ := hh j (by simp)
      simp [plan, hz, hv, simplify, simpAnd, simpOr]
    · simp at hl

lemma changed_input (g : Gate) (x y : List Bool) (h : gv g x ≠ gv g y) :
    ∃ i ∈ g.inputs, x.getD i false ≠ y.getD i false := by
  by_contra! hs
  apply h
  exact congrArg (GateOp.eval g.op) (List.map_congr_left hs)

lemma two_input_cases {is : List ℕ} {u v : ℕ} (hl : is.length ≤ 2)
    (hu : u ∈ is) (hv : v ∈ is) (hne : u ≠ v) :
    ∀ i ∈ is, i = u ∨ i = v := by
  rcases is with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩ <;> simp_all <;> grind

lemma accounted_const (n p q : ℕ) (s : State) (g : Gate) (hg : Good g)
    (x y : List Bool) (hs : controlled s x y)
    (hp : stat s p = Sum.inl true) (hq : stat s q = Sum.inl false)
    (same : x.getD q false = y.getD q false)
    (hor : p ∈ g.inputs → g.op = .or) (mark : raw p q g = true)
    (diff : gv g x ≠ gv g y) : ∃ b, (plan n s g).2 = Sum.inl b := by
  have hm : p ∈ g.inputs ∨ q ∈ g.inputs := by simpa [raw] using mark
  rcases hm with hm | hm
  · have hop := hor hm
    exact ⟨absorb g.op, absorb_at_reader n s g hg hm (by simpa [hop, absorb] using hp)⟩
  · obtain ⟨i, hi, hd⟩ := changed_input g x y diff
    have hn : q ≠ i := by rintro rfl; exact hd same
    apply plan_all_const n s g hg
    intro j hj
    rcases two_input_cases hg.2 hm hi hn j hj with rfl | rfl
    · exact ⟨false,hq⟩
    · exact hs _ hd

lemma drop_count_step (n p q : ℕ) (s : State) (g : Gate) (hg : Good g)
    (x y : List Bool) (hx : x.length = s.1.length) (hy : y.length = s.1.length)
    (hp : stat s p = Sum.inl true) (hq : stat s q = Sum.inl false)
    (same : x.getD q false = y.getD q false)
    (hor : p ∈ g.inputs → g.op = .or) :
    let t := elimStep n s g
    t.2.length + (if raw p q g then 1 else 0) + bonus t (x ++ [gv g x]) (y ++ [gv g y])
      ≤ s.2.length + 1 + bonus s x y := by
  classical
  dsimp only
  have len : (elimStep n s g).2.length = s.2.length + (plan n s g).1.toList.length :=
    List.length_append
  have le := toList_length_le (plan n s g).1
  rw [len]
  by_cases mark : raw p q g = true
  · have hm : p ∈ g.inputs ∨ q ∈ g.inputs := by simpa [raw] using mark
    have drop : (plan n s g).1 = none := hm.elim
      (fun h => drop_at_reader n s g hg h hp) (fun h => drop_at_reader n s g hg h hq)
    rw [drop]
    by_cases hs : controlled s x y
    · have ht := pointwise_step n s g x y hx hy hs
        (accounted_const n p q s g hg x y hs hp hq same hor mark)
      simp [mark, bonus, hs, ht]
    · simp only [mark, Bool.false_eq_true, if_true, if_false, bonus, hs, not_false_eq_true, Option.toList_none, List.length_nil, Nat.add_zero] <;> split <;> omega
  · by_cases hs : controlled s x y
    · by_cases diff : gv g x = gv g y
      · have ht := pointwise_step n s g x y hx hy hs (fun h => (h diff).elim)
        simp [mark, bonus, hs, ht] <;> omega
      · obtain ⟨i,hi,hd⟩ := changed_input g x y diff
        obtain ⟨v,hv⟩ := hs i hd
        rw [drop_at_reader n s g hg hi hv]
        simp only [mark, Bool.false_eq_true, if_true, if_false, bonus, hs, not_false_eq_true, Option.toList_none, List.length_nil, Nat.add_zero] <;> split <;> omega
    · simp only [mark, Bool.false_eq_true, if_true, if_false, bonus, hs, not_false_eq_true, Option.toList_none, List.length_nil, Nat.add_zero] <;> split <;> omega

lemma budget_list (n p q : ℕ) (gs : List Gate) (s : State) (x y : List Bool)
    (hx : x.length = s.1.length) (hy : y.length = s.1.length)
    (ip : p < s.1.length) (iq : q < s.1.length)
    (hp : stat s p = Sum.inl true) (hq : stat s q = Sum.inl false)
    (same : x.getD q false = y.getD q false)
    (hg : ∀ g ∈ gs, Good g) (hor : ∀ g ∈ gs, p ∈ g.inputs → g.op = .or) :
    let t := elim n gs s
    t.2.length + gs.countP (raw p q) + bonus t (wiresFrom gs x) (wiresFrom gs y)
      ≤ s.2.length + gs.length + bonus s x y := by
  induction gs generalizing s x y with
  | nil => simp [wiresFrom, elim]
  | cons g gs ih =>
    have hs := drop_count_step n p q s g (hg _ (.head _)) x y hx hy hp hq same
      (hor _ (.head _))
    let t := elimStep n s g
    have len : t.1.length = s.1.length + 1 := by simp [t, elimStep]
    have old (i : ℕ) (hi : i < s.1.length) : stat t i = stat s i := by
      exact List.getD_append _ _ _ _ hi
    have he : (x ++ [gv g x]).getD q false = (y ++ [gv g y]).getD q false := by
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact same
    have ht := ih t (x ++ [gv g x]) (y ++ [gv g y])
      (by simp [len,hx]) (by simp [len,hy]) (by omega) (by omega)
      ((old _ ip).trans hp) ((old _ iq).trans hq) he
      (fun k h => hg _ (.tail _ h)) (fun k h => hor _ (.tail _ h))
    change (elim n gs t).2.length + (g :: gs).countP (raw p q) +
      bonus (elim n gs t) (wiresFrom gs (x ++ [gv g x])) (wiresFrom gs (y ++ [gv g y]))
      ≤ s.2.length + (g :: gs).length + bonus s x y
    change t.2.length + (if raw p q g then 1 else 0) + bonus t (x ++ [gv g x]) (y ++ [gv g y]) ≤ _ at hs
    cases hmark : raw p q g <;> simp [List.countP_cons, hmark] at hs ⊢ <;> omega

def joint {n : ℕ} (p q : Fin n) : State :=
  (List.ofFn (fun i : Fin n => if i = p then Sum.inl true else if i = q then Sum.inl false
    else Sum.inr i.val), [])

lemma joint_inv {n : ℕ} (p q : Fin n) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (fix p true (fix q false x))) (joint p q) := by
  refine ⟨by simp [joint], ?_⟩
  intro i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change (stat (joint p q) j.val).Valid _ ∧ (stat (joint p q) j.val).val _ = _
    by_cases hp : j = p <;> by_cases hq : j = q <;>
      simp [stat, joint, fix, hp, hq, Stat.Valid, Stat.val, wiresFrom, j, hi] at * <;> simp_all
  · rw [List.getD_eq_default _ _ (by simpa [joint] using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial, rfl⟩

lemma bonus_initial {n : ℕ} (p q : Fin n) (x y : Fin n → Bool)
    (hh : ∀ i, i ≠ p → x i = y i) :
    bonus (joint p q) (List.ofFn x) (List.ofFn y) = 0 := by
  classical
  have hc : controlled (joint p q) (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases h : i < n
    · let j : Fin n := ⟨i,h⟩
      have hn : x j ≠ y j := by simpa [j,h] using hi
      have hj : j = p := by by_contra hne; exact hn (hh j hne)
      exact ⟨true, by change stat (joint p q) j.val = _; simp [stat,joint,hj]⟩
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)] at hi
      exact (hi rfl).elim
  simp [bonus,hc]

lemma restrict_joint {n : ℕ} (C : Circuit) (hm : Monotone2 C) (p q : Fin n)
    (hn : p ≠ q) (hor : ∀ g ∈ C.gates, p.val ∈ g.inputs → g.op = .or)
    (x y : Fin n → Bool) (hag : ∀ i, i ≠ p → x i = y i)
    (diff : circuitFun n C x ≠ circuitFun n C y)
    (nc : ∃ v w, circuitFun n C (fix p true (fix q false v)) ≠
      circuitFun n C (fix p true (fix q false w))) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ w, circuitFun n D w = circuitFun n C (fix p true (fix q false w))) ∧
      D.size + C.gates.countP (raw p.val q.val) + 1 ≤ C.size := by
  classical
  let s := joint p q
  let t := elim n C.gates s
  have hval (w : Fin n → Bool) :
      (stat t C.output).val (wiresFrom t.2 (List.ofFn w)) =
        circuitFun n C (fix p true (fix q false w)) := by
    exact ((inv_elim n _ (by simp) C.gates _ _ hm (joint_inv p q w)).2 C.output).2
  have hv : ∃ j, stat t C.output = Sum.inr j := by
    cases hz : stat t C.output with
    | inl c =>
      obtain ⟨v,w,hw⟩ := nc
      have hf := hval v
      have hf' := hval w
      rw [hz] at hf hf'
      exact (hw (hf.symm.trans hf')).elim
    | inr j => exact ⟨j,rfl⟩
  obtain ⟨j,hj⟩ := hv
  refine ⟨⟨t.2,j⟩,elim_good n _ _ hm (by simp [s,joint]), ?_, ?_⟩
  · intro w
    change (wiresFrom t.2 (List.ofFn w)).getD j false = _
    simpa only [hj,Stat.val] using hval w
  · have ht : ¬ controlled t (wiresFrom C.gates (List.ofFn x)) (wiresFrom C.gates (List.ofFn y)) := by
      intro hf
      obtain ⟨b,hb⟩ := hf C.output diff
      rw [hj] at hb
      cases hb
    have ha := budget_list n p.val q.val C.gates s (List.ofFn x) (List.ofFn y)
      (by simp [s,joint]) (by simp [s,joint]) (by simpa [s,joint] using p.isLt)
      (by simpa [s,joint] using q.isLt) (by simp [s,joint,stat])
      (by simp [s,joint,stat,hn.symm]) (by simpa using hag q hn.symm) hm hor
    change t.2.length + _ + bonus t _ _ ≤ s.2.length + _ + bonus (joint p q) _ _ at ha
    rw [bonus_initial p q x y hag, show bonus t _ _ = 1 from if_neg ht] at ha
    simpa [s, joint, Circuit.size] using ha
def Nonconstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ x y, f x ≠ f y

def Essential {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) : Prop :=
  ∃ x, f (fix p false x) ≠ f (fix p true x)

abbrev left {a b : ℕ} (e : Fin a × Fin b) : Fin (a + b) := Fin.castAdd b e.1

abbrev right {a b : ℕ} (e : Fin a × Fin b) : Fin (a + b) := Fin.natAdd a e.2

abbrev incident {a b : ℕ} (i : Fin (a + b)) (e : Fin a × Fin b) : Prop :=
  left e = i ∨ right e = i

def edgeFun {a b : ℕ} (E : Finset (Fin a × Fin b)) (x : Fin (a + b) → Bool) : Bool :=
  decide (∃ e ∈ E, x (left e) = true ∧ x (right e) = true)

lemma edge_true {a b : ℕ} {E : Finset (Fin a × Fin b)} {x : Fin (a + b) → Bool} :
    edgeFun E x = true ↔ ∃ e ∈ E, x (left e) = true ∧ x (right e) = true := by
  simp [edgeFun]

lemma endpoints_ne {a b : ℕ} (e : Fin a × Fin b) : left e ≠ right e := by
  intro h
  have hv := congrArg Fin.val h
  change e.1.val = a + e.2.val at hv
  omega

lemma both_endpoints {a b : ℕ} {e : Fin a × Fin b} {p q : Fin (a + b)}
    (hn : p ≠ q) (hp : incident p e) (hq : incident q e) :
    (left e = p ∧ right e = q) ∨ (left e = q ∧ right e = p) := by
  rcases hp with hl | hr <;> rcases hq with hl' | hr'
  · exact (hn (hl.symm.trans hl')).elim
  · exact Or.inl ⟨hl, hr'⟩
  · exact Or.inr ⟨hl', hr⟩
  · exact (hn (hr.symm.trans hr')).elim

lemma single_support_false {a b : ℕ} (E : Finset (Fin a × Fin b))
    (x : Fin (a + b) → Bool) (r : Fin (a + b))
    (h : ∀ i, x i = true → i = r) : edgeFun E x = false := by
  cases he : edgeFun E x with
  | false => rfl
  | true =>
    obtain ⟨e, _, hl, hr⟩ := edge_true.mp he
    exact (endpoints_ne e ((h _ hl).trans (h _ hr).symm)).elim

def one {n : ℕ} (r i : Fin n) : Bool := decide (i = r)

lemma one_false {a b : ℕ} (E : Finset (Fin a × Fin b)) (r : Fin (a + b)) :
    edgeFun E (one r) = false := by
  apply single_support_false E _ r
  simp [one]

lemma pair_true {a b : ℕ} {E : Finset (Fin a × Fin b)} {e : Fin a × Fin b}
    {p q : Fin (a + b)} (he : e ∈ E) (hn : p ≠ q)
    (hp : incident p e) (hq : incident q e) :
    edgeFun E (fix p true (one q)) = true := by
  apply edge_true.mpr
  refine ⟨e, he, ?_⟩
  rcases both_endpoints hn hp hq with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp [hl, hr, fix, one, hn.symm]

lemma fix_one_false {n : ℕ} {p q : Fin n} (h : p ≠ q) :
    fix p false (one q) = one q := by
  funext i
  by_cases hi : i = p <;> simp [fix, one, hi, h]

lemma graph_nonconstant {a b : ℕ} {E : Finset (Fin a × Fin b)}
    (h : E.Nonempty) (p : Fin (a + b)) : Nonconstant (edgeFun E) := by
  obtain ⟨e, he⟩ := h
  refine ⟨one p, fun _ => true, ?_⟩
  rw [one_false, edge_true.mpr ⟨e, he, rfl, rfl⟩]
  decide

lemma delete_center {a b : ℕ} (E : Finset (Fin a × Fin b))
    (p q : Fin (a + b)) (hpq : ∀ e ∈ E, incident p e → incident q e)
    (hn : p ≠ q) (bval : Bool) (x : Fin (a + b) → Bool) :
    edgeFun E (fix p bval (fix q false x)) = edgeFun (E.filter fun e => ¬incident q e) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [edge_true, Finset.mem_filter]
  constructor
  · rintro ⟨e, he, hl, hr⟩
    have hq : ¬incident q e := by
      rintro (hq | hq)
      · simp [fix, hq, hn.symm] at hl
      · simp [fix, hq, hn.symm] at hr
    have hp : ¬incident p e := fun h => hq (hpq e he h)
    simp only [incident, not_or] at hq hp
    exact ⟨e, ⟨he, not_or.mpr hq⟩, by simpa [fix, hp.1, hq.1] using hl,
      by simpa [fix, hp.2, hq.2] using hr⟩
  · rintro ⟨e, ⟨he, hq⟩, hl, hr⟩
    have hp : ¬incident p e := fun h => hq (hpq e he h)
    simp only [incident, not_or] at hq hp
    exact ⟨e, he, by simpa [fix, hp.1, hq.1] using hl,
      by simpa [fix, hp.2, hq.2] using hr⟩

def reads (v : ℕ) (g : Gate) : Bool := decide (v ∈ g.inputs)

lemma read_gap (p q : ℕ) (gs : List Gate)
    (he : ∃ g ∈ gs, p ∈ g.inputs ∧ q ∉ g.inputs) :
    gs.countP (reads q) + 1 ≤ gs.countP (raw p q) := by
  have aux (ks : List Gate) : ks.countP (reads q) ≤ ks.countP (raw p q) := by
    induction ks with
    | nil => simp
    | cons g gs ih =>
      by_cases hq : q ∈ g.inputs <;> by_cases hp : p ∈ g.inputs <;>
        simp [List.countP_cons,raw,reads,hp,hq] <;> omega
  induction gs with
  | nil => simp at he
  | cons g gs ih =>
    by_cases ggood : p ∈ g.inputs ∧ q ∉ g.inputs
    · have h := aux gs
      simp [List.countP_cons,raw,reads,ggood.1,ggood.2] <;> omega
    · obtain ⟨k,hk,hk'⟩ := he
      have hk2 : k ∈ gs := (List.mem_cons.mp hk).resolve_left (by rintro rfl; exact ggood hk')
      have hh := ih ⟨k,hk2,hk'⟩
      by_cases hq : q ∈ g.inputs <;> by_cases hp : p ∈ g.inputs <;>
        simp [List.countP_cons,raw,reads,hp,hq] <;> omega

lemma masked_leaf (n p q : ℕ) (gs : List Gate) (x y : List Bool)
    (hxy : ∀ i, i ≠ p → x.getD i false = y.getD i false)
    (hx : x.length = n) (hy : y.length = n) (ip : p < n) (iq : q < n)
    (qx : x.getD q false = true) (qy : y.getD q false = true)
    (hm : ∀ g ∈ gs, p ∈ g.inputs → q ∈ g.inputs ∧ g.op = .or) :
    ∀ i, i ≠ p → (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => exact hxy
  | append_singleton gs g ih =>
    have hpre : ∀ k ∈ gs, p ∈ k.inputs → q ∈ k.inputs ∧ k.op = .or := by
      intro k hk
      exact hm _ (List.mem_append_left _ hk)
    have old := ih hpre
    let X := wiresFrom gs x
    let Y := wiresFrom gs y
    have xl : X.length = n + gs.length := (length_wiresFrom _ _).trans (by rw [hx])
    have yl : Y.length = n + gs.length := (length_wiresFrom _ _).trans (by rw [hy])
    have gsame : gv g X = gv g Y := by
      by_cases hp : p ∈ g.inputs
      · obtain ⟨hq,hop⟩ := hm g (by simp) hp
        have qtrue (w : List Bool) (hl : w.length = n) (h : w.getD q false = true) :
            (wiresFrom gs w).getD q false = true := by
          obtain ⟨t,ht,_⟩ := wiresFrom_prefix gs w
          rw [ht, List.getD_append _ _ _ _ (by omega), h]
        have hv (W : List Bool) (hh : W.getD q false = true) : gv g W = true := by
          change g.op.eval _ = _
          rw [hop]
          change List.any _ id = true
          apply List.any_eq_true.mpr
          exact ⟨true,List.mem_map.mpr ⟨q,hq,hh⟩,rfl⟩
        exact (hv X (qtrue x hx qx)).trans (hv Y (qtrue y hy qy)).symm
      · apply congrArg (GateOp.eval g.op)
        apply List.map_congr_left
        intro i hi
        exact old _ (by rintro rfl; exact hp hi)
    intro i hi
    rw [wiresFrom_append, wiresFrom_append]
    change (X ++ [gv g X]).getD i false = (Y ++ [gv g Y]).getD i false
    by_cases hh : i = n + gs.length
    · rw [getD_snoc_len _ _ _ _ (xl.trans hh.symm), getD_snoc_len _ _ _ _ (yl.trans hh.symm), gsame]
    · rw [getD_snoc_ne _ _ _ _ (by rwa [xl]), getD_snoc_ne _ _ _ _ (by rwa [yl])]
      exact old i hi

lemma raw_extra {a b : ℕ} {E : Finset (Fin a × Fin b)} {C : Circuit}
    (p q : Fin (a+b)) (hn : p ≠ q) (hc : circuitFun (a+b) C = edgeFun E)
    (hor : ∀ g ∈ C.gates, p.val ∈ g.inputs → g.op = .or)
    (e : Fin a × Fin b) (he : e ∈ E) (hp : incident p e) (hq : incident q e) :
    ∃ g ∈ C.gates, p.val ∈ g.inputs ∧ q.val ∉ g.inputs := by
  classical
  by_contra! h
  let x := one q
  let y := fix p true (one q)
  have hs (i : Fin (a+b)) (hi : i ≠ p) : x i = y i := by simp [x,y,fix,hi]
  have hs' (i : ℕ) (hi : i ≠ p.val) :
      (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
    by_cases hh : i < a+b
    · simpa [hh] using hs ⟨i,hh⟩ (fun h => hi (congrArg Fin.val h))
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
  have hdiff : circuitFun (a+b) C x ≠ circuitFun (a+b) C y := by
    rw [hc, show edgeFun E x = false from one_false E q, show edgeFun E y = true from pair_true he hn hp hq]
    decide
  have ho : C.output ≠ p.val := by
    intro h'
    have hv := congrFun hc (one p)
    change (wiresFrom C.gates (List.ofFn (one p))).getD C.output false = _ at hv
    obtain ⟨t,ht,_⟩ := wiresFrom_prefix C.gates (List.ofFn (one p))
    rw [h',ht,List.getD_append _ _ _ _ (by simp),one_false] at hv
    simp [one] at hv
  apply hdiff
  apply masked_leaf (a+b) p.val q.val C.gates _ _ hs' (by simp) (by simp) p.isLt q.isLt
    (by simp [x,one]) (by simp [y,fix,one,hn.symm]) _ _ ho
  intro g hg hi
  exact ⟨h g hg hi,hor g hg hi⟩

theorem leaf_hub_budget {a b : ℕ} (E : Finset (Fin a × Fin b)) (C : Circuit)
    (hm : Monotone2 C) (hc : circuitFun (a+b) C = edgeFun E)
    (p q : Fin (a+b)) (hn : p ≠ q) (e : Fin a × Fin b) (he : e ∈ E)
    (hp : incident p e) (hq : incident q e) (huniq : ∀ d ∈ E, incident p d → incident q d)
    (hne : (E.filter fun d => ¬incident q d).Nonempty)
    (hor : ∀ g ∈ C.gates, p.val ∈ g.inputs → g.op = .or) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun (a+b) D = edgeFun (E.filter fun d => ¬incident q d) ∧
      D.size + C.gates.countP (reads q.val) + 2 ≤ C.size := by
  have hdel (w) : circuitFun (a+b) C (fix p true (fix q false w)) =
      edgeFun (E.filter fun d => ¬incident q d) w := by rw [hc]; exact delete_center _ _ _ huniq hn _ _
  obtain ⟨v,w,hvw⟩ := graph_nonconstant hne p
  have nc : circuitFun (a+b) C (fix p true (fix q false v)) ≠ circuitFun (a+b) C (fix p true (fix q false w)) := by simpa only [hdel] using hvw
  have diff : circuitFun (a+b) C (one q) ≠ circuitFun (a+b) C (fix p true (one q)) := by
    rw [hc,one_false,pair_true he hn hp hq]
    decide
  obtain ⟨D,hmD,hD,sz⟩ := restrict_joint C hm p q hn hor (one q) (fix p true (one q))
    (by intro i hi; simp [fix,hi]) diff ⟨v,w,nc⟩
  have span := read_gap p.val q.val C.gates (raw_extra p q hn hc hor e he hp hq)
  exact ⟨D,hmD,funext (fun z => (hD z).trans (hdel z)),by omega⟩

def trueFixed (s : State) (z : List Bool) : Prop :=
  ∀ i, z.getD i false = true → stat s i = Sum.inl true

lemma fixed_gate (n : Nat) (s : State) (g : Gate) (hg : Good g)
    (z : List Bool) (hz : trueFixed s z) (fire : gv g z=true) :
    (plan n s g).1=none ∧ (plan n s g).2=Sum.inl true := by
  obtain go|go := op_cases hg
  · have allTrue : ∀ i∈g.inputs,z.getD i false=true := by
      simpa [gv,go,GateOp.eval] using fire
    have hh : g.inputs.map (stat s) = g.inputs.map (fun _ => Sum.inl true) :=
      List.map_congr_left (fun i hi => hz _ (allTrue i hi))
    unfold plan
    rw [hh,go]
    have len := hg.2
    cases hins : g.inputs with
    | nil => exact ⟨rfl,rfl⟩
    | cons a t =>
      cases t with
      | nil => exact ⟨rfl,rfl⟩
      | cons b t =>
        cases t with
        | nil => exact ⟨rfl,rfl⟩
        | cons c t => simp [hins] at len
  · obtain ⟨i,hi,zi⟩ : ∃ i∈g.inputs,z.getD i false=true := by simpa [gv,go,GateOp.eval] using fire
    have a := hz i zi
    have force := absorb_at_reader n s g hg hi (by simpa [go,absorb] using a)
    exact ⟨drop_at_reader n s g hg hi a, by simpa [go,absorb] using force⟩

lemma trueFixed_step (n : Nat) (s : State) (g : Gate) (hg : Good g) (z : List Bool)
    (len : z.length=s.1.length) (hz : trueFixed s z) :
    trueFixed (elimStep n s g) (z ++ [gv g z]) := by
  intro i hi
  change (s.1 ++ [(plan n s g).2]).getD i (Sum.inl false) = _
  by_cases he : i=s.1.length
  · subst i
    rw [getD_snoc_len _ _ _ _ len] at hi
    rw [getD_snoc_eq]
    exact (fixed_gate _ _ _ hg _ hz hi).2
  · rw [getD_snoc_ne _ _ _ _ he]
    rw [getD_snoc_ne _ _ _ _ (by simpa only [len] using he)] at hi
    exact hz i hi

def hit (p q : Nat) (z : List Bool) (g : Gate) : Bool := raw p q g || gv g z

def traced (p q : Nat) : List Gate → List Bool → Nat
  | [], _ => 0
  | g::gs,z => (if hit p q z g then 1 else 0) + traced p q gs (z ++ [gv g z])

lemma trace_step (n p q : ℕ) (s : State) (g : Gate) (hg : Good g)
    (x y z : List Bool) (hx : x.length = s.1.length) (hy : y.length = s.1.length)
    (pin : trueFixed s z)
    (hp : stat s p = Sum.inl true) (hq : stat s q = Sum.inl false)
    (same : x.getD q false = y.getD q false) (hor : p ∈ g.inputs → g.op = .or) :
    let t := elimStep n s g
    t.2.length + (if hit p q z g then 1 else 0) + bonus t (x ++ [gv g x]) (y ++ [gv g y])
      ≤ s.2.length + 1 + bonus s x y := by
  classical
  cases fire : gv g z with
  | false => simpa [hit,fire] using drop_count_step n p q s g hg x y hx hy hp hq same hor
  | true =>
    obtain ⟨drop,yes⟩ := fixed_gate n s g hg z pin fire
    have sz : (elimStep n s g).2.length = s.2.length := by
      change (s.2 ++ (plan n s g).1.toList).length = _
      simp [drop]
    dsimp only
    rw [sz]
    by_cases old : controlled s x y
    · have newpin := pointwise_step n s g x y hx hy old (fun _ => ⟨true,yes⟩)
      simp [hit,fire,bonus,old,newpin]
    · simp [hit,fire,bonus,old]; split <;> omega
lemma trace_list (n p q : ℕ) (gs : List Gate) (s : State) (x y z : List Bool) (hz : z.length = s.1.length) (fixz : trueFixed s z)
    (hx : x.length = s.1.length) (hy : y.length = s.1.length)
    (ip : p < s.1.length) (iq : q < s.1.length)
    (hp : stat s p = Sum.inl true) (hq : stat s q = Sum.inl false)
    (same : x.getD q false = y.getD q false)
    (hg : ∀ g ∈ gs, Good g) (hor : ∀ g ∈ gs, p ∈ g.inputs → g.op = .or) :
    let t := elim n gs s
    t.2.length + traced p q gs z + bonus t (wiresFrom gs x) (wiresFrom gs y)
      ≤ s.2.length + gs.length + bonus s x y := by
  induction gs generalizing s x y z with
  | nil => simp [wiresFrom, elim,traced]
  | cons g gs ih =>
    have hs := trace_step n p q s g (hg _ (.head _)) x y z hx hy fixz hp hq same
      (hor _ (.head _))
    let t := elimStep n s g
    have len : t.1.length = s.1.length + 1 := by simp [t, elimStep]
    have old (i : ℕ) (hi : i < s.1.length) : stat t i = stat s i := by
      exact List.getD_append _ _ _ _ hi
    have he : (x ++ [gv g x]).getD q false = (y ++ [gv g y]).getD q false := by
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact same
    have ht := ih t (x ++ [gv g x]) (y ++ [gv g y]) (z ++ [gv g z]) (by simp [len,hz]) (trueFixed_step n s g (hg _ (.head _)) z hz fixz)
      (by simp [len,hx]) (by simp [len,hy]) (by omega) (by omega)
      ((old _ ip).trans hp) ((old _ iq).trans hq) he
      (fun k h => hg _ (.tail _ h)) (fun k h => hor _ (.tail _ h))
    change (elim n gs t).2.length + traced p q (g::gs) z +
      bonus (elim n gs t) (wiresFrom gs (x ++ [gv g x])) (wiresFrom gs (y ++ [gv g y]))
      ≤ s.2.length + (g :: gs).length + bonus s x y
    change t.2.length + (if hit p q z g then 1 else 0) + bonus t (x ++ [gv g x]) (y ++ [gv g y]) ≤ _ at hs
    cases hmark : hit p q z g <;> simp [traced, hmark] at hs ⊢ <;> omega

lemma restrict_trace {n : ℕ} (C : Circuit) (hm : Monotone2 C) (p q : Fin n)
    (hn : p ≠ q) (hor : ∀ g ∈ C.gates, p.val ∈ g.inputs → g.op = .or)
    (x y : Fin n → Bool) (hag : ∀ i, i ≠ p → x i = y i)
    (diff : circuitFun n C x ≠ circuitFun n C y)
    (nc : ∃ v w, circuitFun n C (fix p true (fix q false v)) ≠
      circuitFun n C (fix p true (fix q false w))) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ w, circuitFun n D w = circuitFun n C (fix p true (fix q false w))) ∧
      D.size + traced p.val q.val C.gates (List.ofFn fun i : Fin n => decide (i = p)) + 1 ≤ C.size := by
  classical
  let s := joint p q
  let t := elim n C.gates s
  have hval (w : Fin n → Bool) :
      (stat t C.output).val (wiresFrom t.2 (List.ofFn w)) =
        circuitFun n C (fix p true (fix q false w)) := by
    exact ((inv_elim n _ (by simp) C.gates _ _ hm (joint_inv p q w)).2 C.output).2
  have hv : ∃ j, stat t C.output = Sum.inr j := by
    cases hz : stat t C.output with
    | inl c =>
      obtain ⟨v,w,hw⟩ := nc
      have hf := hval v
      have hf' := hval w
      rw [hz] at hf hf'
      exact (hw (hf.symm.trans hf')).elim
    | inr j => exact ⟨j,rfl⟩
  obtain ⟨j,hj⟩ := hv
  refine ⟨⟨t.2,j⟩,elim_good n _ _ hm (by simp [s,joint]), ?_, ?_⟩
  · intro w
    change (wiresFrom t.2 (List.ofFn w)).getD j false = _
    simpa only [hj,Stat.val] using hval w
  · have ht : ¬ controlled t (wiresFrom C.gates (List.ofFn x)) (wiresFrom C.gates (List.ofFn y)) := by
      intro hf
      obtain ⟨b,hb⟩ := hf C.output diff
      rw [hj] at hb
      cases hb
    let z := List.ofFn (fun i : Fin n => decide (i=p))
    have fixz : trueFixed s z := by
      intro i h
      by_cases valid : i<n
      · have eq : (⟨i,valid⟩ : Fin n)=p := by simpa [z,valid] using h
        change stat (joint p q) (⟨i,valid⟩ : Fin n).val = _
        rw [eq]
        simp [stat,joint]
      · unfold z at h
        rw [List.getD_eq_default _ _ (by simp; omega)] at h
        contradiction
    have ha := trace_list n p.val q.val C.gates s (List.ofFn x) (List.ofFn y) z (by simp [z,s,joint]) fixz
      (by simp [s,joint]) (by simp [s,joint]) (by simpa [s,joint] using p.isLt)
      (by simpa [s,joint] using q.isLt) (by simp [s,joint,stat])
      (by simp [s,joint,stat,hn.symm]) (by simpa using hag q hn.symm) hm hor
    change t.2.length + _ + bonus t _ _ ≤ s.2.length + _ + bonus (joint p q) _ _ at ha
    rw [bonus_initial p q x y hag, show bonus t _ _ = 1 from if_neg ht] at ha
    simpa [s, joint, Circuit.size] using ha

theorem graph_trace_budget {a b : ℕ} (E : Finset (Fin a × Fin b)) (C : Circuit)
    (hm : Monotone2 C) (hc : circuitFun (a+b) C = edgeFun E)
    (p q : Fin (a+b)) (hn : p ≠ q) (e : Fin a × Fin b) (he : e ∈ E)
    (hp : incident p e) (hq : incident q e) (huniq : ∀ d ∈ E, incident p d → incident q d)
    (hne : (E.filter fun d => ¬incident q d).Nonempty)
    (hor : ∀ g ∈ C.gates, p.val ∈ g.inputs → g.op = .or) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun (a+b) D = edgeFun (E.filter fun d => ¬incident q d) ∧
      D.size + traced p.val q.val C.gates (List.ofFn (one p)) + 1 ≤ C.size := by
  have hdel (w) : circuitFun (a+b) C (fix p true (fix q false w)) =
      edgeFun (E.filter fun d => ¬incident q d) w := by rw [hc]; exact delete_center _ _ _ huniq hn _ _
  obtain ⟨v,w,hvw⟩ := graph_nonconstant hne p
  have nc : circuitFun (a+b) C (fix p true (fix q false v)) ≠ circuitFun (a+b) C (fix p true (fix q false w)) := by simpa only [hdel] using hvw
  have diff : circuitFun (a+b) C (one q) ≠ circuitFun (a+b) C (fix p true (one q)) := by
    rw [hc,one_false,pair_true he hn hp hq]
    decide
  obtain ⟨D,hmD,hD,sz⟩ := restrict_trace C hm p q hn hor (one q) (fix p true (one q))
    (by intro i hi; simp [fix,hi]) diff ⟨v,w,nc⟩
  exact ⟨D,hmD,funext (fun z => (hD z).trans (hdel z)),sz⟩

end PEqualNP.Outside.L_meta_7963_aux
