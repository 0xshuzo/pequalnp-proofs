import PEqualNP.Defs

/-!
# Shannon expansion as a straight-line program

Helper for `L-meta-001`. The construction is made at an arbitrary wire offset: the function
reads the first `k` wires of a wire list of length `m`, and the new gates are appended after
wire `m - 1`. So two subcircuits are put one after the other without renumbering any gate.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

/-- The four gates that close one Shannon expansion step, appended to the wires `v`: with
`a = v[k]`, `p = v[o0]`, `q = v[o1]` they produce `(¬a ∧ p) ∨ (a ∧ q)` on the last wire. -/
theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.MetaComplexity.Helpers


/-!
# Supports of wires

Helper for `L-meta-011`. Every wire gets a support: the set of inputs it can depend on, read
off the gates. Two facts: the value of a wire depends only on the inputs in its support, and
any set `W` of wires has a joint support of size at most (number of gates) + `|W|`, because a
gate of fan-in two replaces itself by at most two earlier wires.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

/-- A function that depends on each of its `n` inputs has no circuit with fewer than `n - 1`
gates. -/
theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.Outside.L_meta_9829.LineChannels

variable {P L : Type} (A : P → L → Bool) (E : P → L → Bool → Bool)
    (D : (L → Bool) → Bool) (base : P)

def Computes : Prop :=
  ∀ (x : P) (y : L → Bool),
    D (fun i => E x i (y i)) = true ↔ ∃ i, A x i = true ∧ y i = true

theorem bitSeparation (h : Computes A E D) (allOn : ∀ i, A base i = true) (j : L) :
    E base j false ≠ E base j true := by
  classical
  intro same
  let one : L → Bool := fun i => decide (i=j)
  have eqv : (fun i => E base i false) = (fun i => E base i (one i)) := by
    funext i
    by_cases hit : i=j
    · subst i; simpa [one] using same
    · simp [one,hit]
  have yes := (h base one).2 ⟨j,allOn j,by simp [one]⟩
  rw [← eqv] at yes
  obtain ⟨_,_,bad⟩ := (h base (fun _ => false)).1 yes
  cases bad

theorem table (h : Computes A E D) (allOn : ∀ i, A base i = true) (z : L → Bool) :
    D z = true ↔ ∃ i, z i ≠ E base i false := by
  classical
  let test : L → Bool := fun i => decide (z i ≠ E base i false)
  have full : (fun i => E base i (test i)) = z := by
    funext i
    have dist := bitSeparation A E D base h allOn i
    dsimp [test]
    cases hz : z i <;> cases h0 : E base i false <;> cases h1 : E base i true <;>
      simp_all
  constructor
  · intro on
    have yes : D (fun i => E base i (test i)) = true := full.symm ▸ on
    obtain ⟨i,_,hi⟩ := (h base test).1 yes
    exact ⟨i,by simpa [test] using hi⟩
  · rintro ⟨i,hi⟩
    rw [← full]
    exact (h base test).2 ⟨i,allOn i,by simpa [test] using hi⟩

theorem offChannels (h : Computes A E D) (allOn : ∀ i, A base i = true)
    (x : P) (i : L) : E x i false = E base i false := by
  by_contra diff
  have on := (table A E D base h allOn (fun j => E x j false)).2 ⟨i,diff⟩
  obtain ⟨_,_,bad⟩ := (h x (fun _ => false)).1 on
  cases bad

theorem activeChannel (h : Computes A E D) (allOn : ∀ i, A base i = true)
    (x : P) (j : L) : E x j true ≠ E base j false ↔ A x j = true := by
  classical
  let one : L → Bool := fun i => decide (i=j)
  have hj : one j = true := by simp [one]
  constructor
  · intro changeBit
    have on := (table A E D base h allOn (fun i => E x i (one i))).2
      ⟨j,by simpa only [hj] using changeBit⟩
    obtain ⟨i,hi,fi⟩ := (h x one).1 on
    have eqij : i=j := by simpa [one] using fi
    simpa [eqij] using hi
  · intro active
    have on := (h x one).2 ⟨j,active,hj⟩
    obtain ⟨i,hi⟩ := (table A E D base h allOn _).1 on
    by_cases ij : i=j
    · subst i; simpa only [hj] using hi
    · have low : one i=false := by simp [one,ij]
      rw [low,offChannels A E D base h allOn x i] at hi
      exact (hi rfl).elim

theorem requiredInput (h : Computes A E D) (allOn : ∀ i, A base i = true)
    (x y : P) (j : L) (off : A x j=false) (on : A y j=true) :
    E x j true ≠ E y j true := by
  intro same
  have hy := (activeChannel A E D base h allOn y j).2 on
  rw [← same] at hy
  have hx := (activeChannel A E D base h allOn x j).1 hy
  rw [off] at hx
  cases hx


def nb : Fin 11 → Nat := ![2092,4184,177,354,708,1416,2832,5664,3137,6274,4357]
def flag (p : Fin 13) (j : Fin 11) := (nb j).testBit p
def lit (x : Fin 13 → Bool) (j : Fin 11) : Bool :=
  (List.finRange 13).any (fun p => flag p j && x p)
def onePoint (p : Fin 13) : Fin 13 → Bool := fun q => decide (q=p)
def dark : Fin 13 → Bool := fun _ => false
def bright : Fin 13 → Bool := fun _ => true

private theorem allLit : ∀ j, lit bright j = true := by decide +kernel
private theorem allDark : ∀ j, lit dark j = false := by decide +kernel
private theorem oneLit : ∀ p j, flag p j = true → lit (onePoint p) j = true := by
  decide +kernel

theorem everyFlag (E : (Fin 13 → Bool) → Fin 11 → Bool → Bool)
    (D : (Fin 11 → Bool) → Bool) (hh : Computes lit E D)
    (p : Fin 13) (j : Fin 11) (adj : flag p j=true) :
    E dark j true ≠ E (onePoint p) j true :=
  requiredInput lit E D bright hh allLit dark (onePoint p) j (allDark j) (oneLit p j adj)

theorem missingFlag (E : (Fin 13 → Bool) → Fin 11 → Bool → Bool)
    (D : (Fin 11 → Bool) → Bool) (p : Fin 13) (j : Fin 11) (adj : flag p j=true)
    (noRead : E dark j true = E (onePoint p) j true) :
    ¬Computes lit E D :=
  fun hh => everyFlag E D hh p j adj noRead

-- Global vertex 16 is local line 3. This is the single omitted flag
-- in each of the ten 53-site controls.
theorem controlMissing (E : (Fin 13 → Bool) → Fin 11 → Bool → Bool)
    (D : (Fin 11 → Bool) → Bool)
    (noRead : E dark 3 true = E (onePoint 5) 3 true) :
    ¬Computes lit E D := missingFlag E D 5 3 (by decide) noRead

end PEqualNP.Outside.L_meta_9829.LineChannels

namespace PEqualNP.Outside.L_meta_9829.LinePrice
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.Outside.L_meta_9829.LineChannels

def controlledFour (phase : Bool) (x : Fin 5 → Bool) : Bool :=
  xor phase (x 4 && (x 0 || x 1 || x 2 || x 3))

private theorem controlDep : ∀ (c : Bool) (i : Fin 5), ∃ x : Fin 5 → Bool,
    controlledFour c (Function.update x i (!x i)) ≠ controlledFour c x := by
  decide +kernel

theorem decoderPrice (E : (Fin 13 → Bool) → Fin 11 → Bool → Bool)
    (D : (Fin 11 → Bool) → Bool) (h : Computes lit E D)
    (litBase : ∀ j, lit bright j=true)
    (k : Nat) (hc : HasCircuitSize 11 D k) : 10 ≤ k := by
  let z : Fin 11 → Bool := fun j => E bright j false
  have off : D z ≠ true := by
    intro yes
    obtain ⟨j,ne⟩ := (table lit E D bright h litBase z).1 yes
    exact ne rfl
  have lower := dep_lower 11 D (by
    intro j
    refine ⟨z,?_⟩
    have on : D (Function.update z j (!z j))=true := by
      apply (table lit E D bright h litBase _).2
      refine ⟨j,?_⟩
      rw [Function.update_self]
      change (!z j) ≠ z j
      cases z j <;> decide
    rw [on]
    exact Ne.symm off) k hc
  omega

theorem separated54 (E : (Fin 13 → Bool) → Fin 11 → Bool → Bool)
    (D : (Fin 11 → Bool) → Bool) (h : Computes lit E D)
    (sizes : Fin 11 → Nat) (outer : Nat)
    (owned : ∀ j, HasCircuitSize 5 (controlledFour (E bright j false)) (sizes j))
    (decoder : HasCircuitSize 11 D outer) :
    54 ≤ (∑ j : Fin 11, sizes j) + outer := by
  have dk := decoderPrice E D h (by decide +kernel) outer decoder
  have each (j : Fin 11) : 4 ≤ sizes j := by
    have w := dep_lower 5 _ (controlDep (E bright j false)) _ (owned j)
    omega
  have total : (∑ _j : Fin 11, (4:Nat)) ≤ ∑ j : Fin 11, sizes j :=
    Finset.sum_le_sum fun j _ => each j
  simp at total
  omega

def points : Fin 11 → Fin 4 → Fin 13 := ![![2,3,5,11],![3,4,6,12],![0,4,5,7],![1,5,6,8],![2,6,7,9],![3,7,8,10],![4,8,9,11],![5,9,10,12],![0,6,10,11],![1,7,11,12],![0,2,8,12]]

def face (j : Fin 11) (v : Fin 5 → Bool) (p : Fin 13) :=
  (List.finRange 4).any fun i => decide (points j i=p) && v i.castSucc

private theorem litFace : ∀ (j : Fin 11) (v : Fin 5 → Bool),
    lit (face j v) j = (v 0 || v 1 || v 2 || v 3) := by decide +kernel

theorem channelIdentity (E : (Fin 13 → Bool) → Fin 11 → Bool → Bool)
    (D : (Fin 11 → Bool) → Bool) (h : Computes lit E D) (x : Fin 13 → Bool)
    (j : Fin 11) (b : Bool) : E x j b = xor (E bright j false) (b && lit x j) := by
  have hb : ∀ t, lit bright t=true := by decide +kernel
  cases b with
  | false =>
    have off := offChannels lit E D bright h hb x j
    rw [off]; cases E bright j false <;> rfl
  | true =>
    have ha := activeChannel lit E D bright h hb x j
    cases E x j true <;> cases E bright j false <;> cases lit x j <;> simp_all

theorem actualSeparated54 (E : (Fin 13 → Bool) → Fin 11 → Bool → Bool)
    (D : (Fin 11 → Bool) → Bool) (h : Computes lit E D)
    (sizes : Fin 11 → Nat) (outer : Nat)
    (owned : ∀ j, HasCircuitSize 5 (fun v => E (face j v) j (v 4)) (sizes j))
    (decoder : HasCircuitSize 11 D outer) : 54 ≤ (∑ j : Fin 11, sizes j) + outer := by
  apply separated54 E D h sizes outer _ decoder
  intro j
  have eqv : (fun v : Fin 5 → Bool => E (face j v) j (v 4)) =
      controlledFour (E bright j false) := by
    funext v
    rw [channelIdentity E D h,litFace]
    rfl
  rw [← eqv]
  exact owned j

end PEqualNP.Outside.L_meta_9829.LinePrice
