import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Choose
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import PEqualNP.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Formula5176

open PEqualNP.MetaComplexity

def leafLabel {n : ℕ} : (φ : DMFormula n) → Fin φ.leaves → Fin n
  | .lit v _, _ => v
  | .and a b, i => Fin.addCases (motive := fun _ => Fin n) (leafLabel a) (leafLabel b) i
  | .or a b, i => Fin.addCases (motive := fun _ => Fin n) (leafLabel a) (leafLabel b) i

private theorem cover531_splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
    (h : ((∃! i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, ¬ P (Fin.natAdd m j))) ∨
      ((∀ i : Fin m, ¬ P (Fin.castAdd n i)) ∧ (∃! j : Fin n, P (Fin.natAdd m j)))) :
    ∃! i, P i := by
  rcases h with ⟨⟨i, hi, hunique⟩, hnone⟩ | ⟨hnone, ⟨j, hj, hunique⟩⟩
  · refine ⟨Fin.castAdd n i, hi, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.castAdd n i) ?_ ?_ k
    · intro k hk
      exact congrArg (Fin.castAdd n) (hunique k hk)
    · intro k hk
      exact (hnone k hk).elim
  · refine ⟨Fin.natAdd m j, hj, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.natAdd m j) ?_ ?_ k
    · intro k hk
      exact (hnone k hk).elim
    · intro k hk
      exact congrArg (Fin.natAdd m) (hunique k hk)

private theorem cover531_formulaRectanglesStrong {n : ℕ}
    (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n), label = leafLabel φ ∧
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → φ.eval x = true ∧ x (label i) = true) ∧
        (∀ i y, Y i y → φ.eval y = false ∧ y (label i) = false) := by
  induction φ with
  | lit v c =>
      change c = true at mono
      subst c
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, fun _ => v, rfl, ?_, ?_, ?_⟩
      · intro x y hx hy
        change ∃! _i : Fin 1, x v = true ∧ y v = false
        exact ⟨0, ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx,
          by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy⟩,
          fun i _ => Subsingleton.elim i 0⟩
      · intro i x hx
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx, hx⟩
      · intro i y hy
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy, hy⟩
  | and a b ihA ihB =>
      obtain ⟨XA, YA, LA, hLA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, hLB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ b.eval x = true) (fun i x => XB i x ∧ a.eval x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ a.eval y = true)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases (motive := fun _ => Fin n) LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_, ?_⟩
      · subst LA
        subst LB
        rfl
      · intro x y hx hy
        have hx' : a.eval x = true ∧ b.eval x = true := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true_iff] using hx
        apply cover531_splitUnique
        cases ha : a.eval y with
        | false =>
            left
            constructor
            · simpa [X, Y, hx'.2] using totalA x y hx'.1 ha
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
        | true =>
            right
            have hb : b.eval y = false := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hy
            constructor
            · intro i hi
              have hLeft : YA i y := by simpa [Y] using hi.2
              have hFalse := (yA i y hLeft).1
              simp [ha] at hFalse
            · simpa [X, Y, hx'.1, ha, Fin.addCases_right] using totalB x y hx'.2 hb
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x ∧ b.eval x = true := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = true := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = true := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
  | or a b ihA ihB =>
      obtain ⟨XA, YA, LA, hLA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, hLB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ a.eval x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ b.eval y = false) (fun i y => YB i y ∧ a.eval y = false)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases (motive := fun _ => Fin n) LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_, ?_⟩
      · subst LA
        subst LB
        rfl
      · intro x y hx hy
        have hy' : a.eval y = false ∧ b.eval y = false := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_false_iff] using hy
        apply cover531_splitUnique
        cases ha : a.eval x with
        | false =>
            right
            have hb : b.eval x = true := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hx
            constructor
            · intro i hi
              have hLeft : XA i x := by simpa [X] using hi.1
              have hTrue := (xA i x hLeft).1
              simp [ha] at hTrue
            · simpa [X, Y, hy'.1, ha, Fin.addCases_right] using totalB x y hb hy'.2
        | true =>
            left
            constructor
            · simpa [X, Y, hy'.2] using totalA x y ha hy'.1
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = false := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y ∧ b.eval y = false := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = false := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩

private theorem cover531_formulaRectangles {n : ℕ} (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n), label = leafLabel φ ∧
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x y, φ.eval x = true → φ.eval y = false → X i x → Y i y →
          x (label i) = true ∧ y (label i) = false) := by
  obtain ⟨X, Y, label, same, total, goodX, goodY⟩ := cover531_formulaRectanglesStrong φ mono
  exact ⟨X, Y, label, same, total, fun i x y _ _ hx hy => ⟨(goodX i x hx).2, (goodY i y hy).2⟩⟩

private lemma cover531_starIndependent {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (v : Fin n) : ∀ u w, G.Adj u w → ¬ (G.Adj v u ∧ G.Adj v w) := by
  intro u w huw h
  exact triangle v u w ⟨h.1, huw, h.2.symm⟩

private lemma cover531_pairIndependent {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (square : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (a b : Fin n) (edge : G.Adj a b) : ∀ u w, G.Adj u w →
      ¬ (((G.Adj a u ∨ G.Adj b u) ∧ u ≠ a ∧ u ≠ b) ∧
         ((G.Adj a w ∨ G.Adj b w) ∧ w ≠ a ∧ w ≠ b)) := by
  intro u w huw h
  rcases h with ⟨⟨hu, hua, hub⟩, ⟨hw, hwa, hwb⟩⟩
  rcases hu with hau | hbu <;> rcases hw with haw | hbw
  · exact triangle a u w ⟨hau, huw, haw.symm⟩
  · exact square a u w b hwa.symm hub ⟨hau, huw, hbw.symm, edge.symm⟩
  · exact square b u w a hwb.symm hua ⟨hbu, huw, haw.symm, edge⟩
  · exact triangle b u w ⟨hbu, huw, hbw.symm⟩

private theorem cover531_rank {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] {m : ℕ} (a b reject : E → V) (T : Finset V) (R : Fin m → (V × E → ℚ))
    (anchor : ∀ v ∈ T, ∃ e, v ≠ reject e ∧ (a e = v ∨ b e = v))
    (units : ∀ e, Pi.single (reject e, e) 1 ∈ Submodule.span ℚ (Set.range R))
    (stars : ∀ v ∈ T, (fun p : V × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v)
      then 1 else 0) ∈ Submodule.span ℚ (Set.range R)) :
    Fintype.card E + T.card ≤ m := by
  classical
  let unit (e : E) : V × E → ℚ := Pi.single (reject e, e) 1
  let star (v : V) : V × E → ℚ :=
    fun p => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0
  let family : E ⊕ ↥T → (V × E → ℚ) := Sum.elim unit (fun v => star v.val)
  let W := Submodule.span ℚ (Set.range R)
  have inSpan (i : E ⊕ ↥T) : family i ∈ W := by
    cases i with
    | inl e => exact units e
    | inr v => exact stars v.val v.property
  have independent : LinearIndependent ℚ family := by
    rw [Fintype.linearIndependent_iff]
    intro c relation
    have atCoord (p : V × E) :
        (Finset.univ.sum fun e : E => c (Sum.inl e) * unit e p) +
          (Finset.univ.sum fun v : ↥T => c (Sum.inr v) * star v.val p) = 0 := by
      simpa [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, family] using
        congrFun relation p
    have starZero (v : ↥T) : c (Sum.inr v) = 0 := by
      obtain ⟨e, different, incident⟩ := anchor v.val v.property
      have unitSum : (Finset.univ.sum fun j : E => c (Sum.inl j) * unit j (v.val, e)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have h : (v.val, e) ≠ (reject j, j) := by
          intro same
          have ej : e = j := congrArg Prod.snd same
          subst j
          exact different (congrArg Prod.fst same)
        simp [unit, Pi.single_eq_of_ne h]
      have starSum : (Finset.univ.sum fun w : ↥T => c (Sum.inr w) * star w.val (v.val, e)) =
          c (Sum.inr v) := by
        rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ v)]
        · simp [star, incident]
        · intro w _ differentSub
          have h : v.val ≠ w.val := fun same => differentSub (Subtype.ext same.symm)
          simp [star, h]
      simpa only [unitSum, starSum, zero_add] using atCoord (v.val, e)
    intro i
    cases i with
    | inr v => exact starZero v
    | inl e =>
      have starSum : (Finset.univ.sum fun v : ↥T => c (Sum.inr v) * star v.val (reject e, e)) = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        simp [starZero v]
      have unitSum : (Finset.univ.sum fun j : E => c (Sum.inl j) * unit j (reject e, e)) = c (Sum.inl e) := by
        rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
        · simp [unit]
        · intro j _ different
          have h : (reject e, e) ≠ (reject j, j) := fun same =>
            different (congrArg Prod.snd same).symm
          simp [unit, Pi.single_eq_of_ne h]
      simpa only [unitSum, starSum, add_zero] using atCoord (reject e, e)
  have : Module.Finite ℚ ↥W := Module.Finite.span_of_finite ℚ (Set.finite_range R)
  let lifted (i : E ⊕ ↥T) : ↥W := ⟨family i, inSpan i⟩
  have liftedIndependent : LinearIndependent ℚ lifted := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent ℚ family
    exact independent
  have lower : Fintype.card E + T.card ≤ Module.finrank ℚ ↥W := by
    simpa only [Fintype.card_sum, Fintype.card_coe] using liftedIndependent.fintype_card_le_finrank
  have upper : Module.finrank ℚ W ≤ m := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range R)) ≤ m
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    simpa only [Fintype.card_fin] using Fintype.card_range_le R
  exact lower.trans upper

set_option maxHeartbeats 1000000 in
theorem colouredPrice : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ φ : PEqualNP.MetaComplexity.DMFormula n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ → (∀ x : Fin n → Bool, φ.eval x = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ T : Finset (Fin n), (∀ u w : Fin n, G.Adj u w → u ∈ T ∨ w ∈ T) ∧ G.edgeFinset.card + T.card ≤ φ.leaves ∧
    ∀ Z : Finset (Fin n), (∀ u v, G.Adj u v → u∈T → v∈Z) →
    G.edgeFinset.card ≤ ((Finset.univ : Finset (Fin φ.leaves)).filter (fun i => leafLabel φ i∈Z)).card := by
  intro n G _ triangle square φ monotone evaluates
  classical
  obtain ⟨X, Y, label, sameLabel, partitions, labels⟩ := cover531_formulaRectangles φ monotone
  let E := {e : Sym2 (Fin n) // e ∈ G.edgeFinset}
  have endpoints (e : E) : ∃ u v : Fin n, G.Adj u v ∧ Sym2.mk u v = e.val := by
    have member : e.val ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.property
    revert member
    refine Sym2.inductionOn e.val ?_
    intro u v member
    exact ⟨u, v, member, rfl⟩
  choose a b adjacent represented using endpoints
  let row (e : E) (v : Fin n) : Bool := decide (v = a e ∨ v = b e)
  let starColumn (v w : Fin n) : Bool := decide (G.Adj v w)
  let edgeColumn (e : E) (w : Fin n) : Bool :=
    decide ((G.Adj (a e) w ∨ G.Adj (b e) w) ∧ w ≠ a e ∧ w ≠ b e)
  have rowPositive (e : E) : φ.eval (row e) = true := by
    rw [evaluates]
    exact decide_eq_true ⟨a e, b e, adjacent e, by simp [row], by simp [row]⟩
  have starNegative (v : Fin n) : φ.eval (starColumn v) = false := by
    rw [evaluates]
    apply decide_eq_false
    rintro ⟨u, w, edge, hu, hw⟩
    exact cover531_starIndependent G triangle v u w edge
      ⟨of_decide_eq_true hu, of_decide_eq_true hw⟩
  have edgeNegative (e : E) : φ.eval (edgeColumn e) = false := by
    rw [evaluates]
    apply decide_eq_false
    rintro ⟨u, w, edge, hu, hw⟩
    exact cover531_pairIndependent G triangle square (a e) (b e) (adjacent e) u w edge
      ⟨of_decide_eq_true hu, of_decide_eq_true hw⟩
  let route (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) : Fin φ.leaves :=
    Classical.choose (partitions (row e) y (rowPositive e) hy)
  have routeMem (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) :
      X (route e y hy) (row e) ∧ Y (route e y hy) y :=
    (Classical.choose_spec (partitions (row e) y (rowPositive e) hy)).1
  have routeUnique (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (i : Fin φ.leaves) (hi : X i (row e) ∧ Y i y) : i = route e y hy :=
    (Classical.choose_spec (partitions (row e) y (rowPositive e) hy)).2 i hi
  let selected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) := label (route e y hy)
  have labelProperties (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) :
      (selected e y hy = a e ∨ selected e y hy = b e) ∧ y (selected e y hy) = false := by
    have result := labels (route e y hy) (row e) y (rowPositive e) hy
      (routeMem e y hy).1 (routeMem e y hy).2
    exact ⟨of_decide_eq_true result.1, result.2⟩
  have leftSelected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (opposite : y (b e) = true) : selected e y hy = a e := by
    rcases labelProperties e y hy with ⟨chosen | chosen, missing⟩
    · exact chosen
    · simp [chosen, opposite] at missing
  have rightSelected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (opposite : y (a e) = true) : selected e y hy = b e := by
    rcases labelProperties e y hy with ⟨chosen | chosen, missing⟩
    · simp [chosen, opposite] at missing
    · exact chosen
  let chosen (e : E) := selected e (edgeColumn e) (edgeNegative e)
  let reject (e : E) := if chosen e = a e then b e else a e
  have chosenEnd (e : E) : chosen e = a e ∨ chosen e = b e :=
    (labelProperties e (edgeColumn e) (edgeNegative e)).1
  have rejectEnd (e : E) : a e = reject e ∨ b e = reject e := by
    dsimp only [reject]
    split <;> simp
  have differentEnd (e : E) : chosen e ≠ reject e := by
    have distinct := (adjacent e).ne
    rcases chosenEnd e with left | right
    · simp [reject, left, distinct]
    · simp [reject, right, distinct.symm]
  let R (i : Fin φ.leaves) (p : Fin n × E) : ℚ :=
    if p.1 = label i ∧ X i (row p.2) then 1 else 0
  let col (v : Fin n) (y : Fin n → Bool) : Fin n × E → ℚ :=
    Finset.univ.sum fun i : Fin φ.leaves => if Y i y ∧ label i = v then R i else 0
  let span := Submodule.span ℚ (Set.range R)
  have colInSpan (v : Fin n) (y : Fin n → Bool) : col v y ∈ span := by
    apply Submodule.sum_mem
    intro i _
    split
    · exact Submodule.subset_span ⟨i, rfl⟩
    · exact span.zero_mem
  have colValue (v : Fin n) (y : Fin n → Bool) (hy : φ.eval y = false) (p : Fin n × E) :
      col v y p = if p.1 = v ∧ selected p.2 y hy = v then 1 else 0 := by
    simp only [col, Finset.sum_apply]
    rw [Finset.sum_eq_single (route p.2 y hy)]
    · by_cases same : label (route p.2 y hy) = v
      · simp [R, selected, same, (routeMem p.2 y hy).1, (routeMem p.2 y hy).2]
      · simp [selected, same]
    · intro i _ other
      by_cases inColumn : Y i y ∧ label i = v
      · have noRow : ¬ X i (row p.2) := fun hx => other (routeUnique p.2 y hy i ⟨hx, inColumn.1⟩)
        simp [inColumn, R, noRow]
      · simp [inColumn]
    · simp
  have columnOpposite (e : E) (v w : Fin n) (hv : a e = v ∨ b e = v)
      (edge : G.Adj v w) (other : Sym2.mk v w ≠ e.val) : edgeColumn e w = true := by
    rcases hv with rfl | rfl
    · have notLeft : w ≠ a e := edge.ne.symm
      have notRight : w ≠ b e := by
        intro equal
        apply other
        rw [equal]
        exact represented e
      exact decide_eq_true ⟨Or.inl edge, notLeft, notRight⟩
    · have notRight : w ≠ b e := edge.ne.symm
      have notLeft : w ≠ a e := by
        intro equal
        apply other
        rw [equal]
        exact Sym2.eq_swap.trans (represented e)
      exact decide_eq_true ⟨Or.inr edge, notLeft, notRight⟩
  have starSelected (v : Fin n) (e : E) :
      selected e (starColumn v) (starNegative v) = v ↔ a e = v ∨ b e = v := by
    constructor
    · intro equals
      simpa [equals, eq_comm] using (labelProperties e (starColumn v) (starNegative v)).1
    · rintro (rfl | rfl)
      · exact leftSelected e (starColumn (a e)) (starNegative (a e)) (decide_eq_true (adjacent e))
      · exact rightSelected e (starColumn (b e)) (starNegative (b e)) (decide_eq_true (adjacent e).symm)
  have otherSelected (e e' : E) (different : e' ≠ e) (v : Fin n) (hv : a e = v ∨ b e = v) :
      selected e' (edgeColumn e) (edgeNegative e) = v ↔ a e' = v ∨ b e' = v := by
    have diffRep : e'.val ≠ e.val := fun equals => different (Subtype.ext equals)
    constructor
    · intro equals
      simpa [equals, eq_comm] using (labelProperties e' (edgeColumn e) (edgeNegative e)).1
    · rintro (rfl | rfl)
      · exact leftSelected e' (edgeColumn e) (edgeNegative e)
          (columnOpposite e _ _ hv (adjacent e') (by simpa [represented e'] using diffRep))
      · have notReversed : Sym2.mk (b e') (a e') ≠ e.val := by
          rw [Sym2.eq_swap, represented e']
          exact diffRep
        exact rightSelected e' (edgeColumn e) (edgeNegative e)
          (columnOpposite e _ _ hv (adjacent e').symm notReversed)
  let T : Finset (Fin n) := Finset.univ.image chosen
  have starInSpan (v : Fin n) :
      (fun p : Fin n × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0) ∈ span := by
    have equals : col v (starColumn v) =
        (fun p : Fin n × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0) := by
      funext p
      simp only [colValue v _ (starNegative v), starSelected]
    rw [← equals]
    exact colInSpan v (starColumn v)
  have unitFrom (e : E) (W : Submodule ℚ (Fin n × E → ℚ))
      (hc : ∀ y, col (reject e) y∈W) : Pi.single (reject e, e) (1 : ℚ) ∈ W := by
    let v := reject e
    have equals : col v (starColumn v) - col v (edgeColumn e) = Pi.single (v, e) (1 : ℚ) := by
      funext p
      rcases p with ⟨w, e'⟩
      change col v (starColumn v) (w, e') - col v (edgeColumn e) (w, e') = (Pi.single (v, e) 1 : Fin n × E → ℚ) (w, e')
      simp only [colValue v _ (starNegative v), colValue v _ (edgeNegative e), starSelected]
      by_cases first : w = v
      · subst w
        by_cases second : e' = e
        · subst e'
          have miss : selected e (edgeColumn e) (edgeNegative e) ≠ v := differentEnd e
          simp [rejectEnd e, miss, v]
        · simp only [otherSelected e e' second v (rejectEnd e)]
          simp [second]
      · simp [first]
    rw [← equals]
    exact W.sub_mem (hc _) (hc _)
  have units (e : E) : Pi.single (reject e,e) (1 : ℚ) ∈ span :=
    unitFrom e span (colInSpan _)
  have anchor : ∀ v ∈ T, ∃ e, v ≠ reject e ∧ (a e = v ∨ b e = v) := by
    intro v hv
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hv
    rcases chosenEnd e with first | second
    · exact ⟨e, differentEnd e, Or.inl first.symm⟩
    · exact ⟨e, differentEnd e, Or.inr second.symm⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · intro u w edge
    let e : E := ⟨Sym2.mk u w, SimpleGraph.mem_edgeFinset.mpr edge⟩
    have inCover : chosen e ∈ T := Finset.mem_image_of_mem chosen (Finset.mem_univ e)
    have pair : Sym2.mk (a e) (b e) = Sym2.mk u w := represented e
    rcases Sym2.eq_iff.mp pair with ⟨left, right⟩ | ⟨left, right⟩
    · rcases chosenEnd e with first | second
      · exact Or.inl ((first.trans left) ▸ inCover)
      · exact Or.inr ((second.trans right) ▸ inCover)
    · rcases chosenEnd e with first | second
      · exact Or.inr ((first.trans left) ▸ inCover)
      · exact Or.inl ((second.trans right) ▸ inCover)
  · have bound := cover531_rank a b reject T R anchor units (fun v _ => starInSpan v)
    have count : Fintype.card E = G.edgeFinset.card := Fintype.card_coe _
    rwa [count] at bound

  · intro Z hz
    let I := (Finset.univ : Finset (Fin φ.leaves)).filter (fun i => label i∈Z)
    let ix : ↥I ≃ Fin I.card := Fintype.equivFinOfCardEq (Fintype.card_coe I)
    let rows (j : Fin I.card) := R (ix.symm j).val
    let W := Submodule.span ℚ (Set.range rows)
    have selectedIn (i : Fin φ.leaves) (hi : label i∈Z) : R i∈W := by
      let a : ↥I := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
      apply Submodule.subset_span
      exact ⟨ix a,by simp [rows,a]⟩
    have otherIn (e : E) : reject e∈Z := by
      have hc : chosen e∈T := Finset.mem_image_of_mem _ (Finset.mem_univ e)
      rcases chosenEnd e with h|h
      · have hr : reject e=b e := by simp [reject,h]
        rw [hr]; exact hz _ _ (adjacent e) (h ▸ hc)
      · have diff : b e≠a e := (adjacent e).ne.symm
        have hr : reject e=a e := by simp [reject,h,diff]
        rw [hr]; exact hz _ _ (adjacent e).symm (h ▸ hc)
    have localUnits (e : E) : Pi.single (reject e,e) (1 : ℚ) ∈ W := by
      apply unitFrom e W
      intro y
      apply Submodule.sum_mem
      intro i _
      split
      next hh => exact selectedIn i (hh.2.symm ▸ otherIn e)
      next => exact W.zero_mem
    have z := cover531_rank a b reject ∅ rows (by simp) localUnits (by simp)
    have cnt : Fintype.card E = G.edgeFinset.card := Fintype.card_coe _
    rw [cnt] at z
    simpa [I,sameLabel] using z
end Formula5176



namespace PlaneOrdered
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

theorem ordered (n : ℕ) (D : Circuit) (h : PEqualNP.TopForm.IsAO2 n D) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (D.wires (List.ofFn x)).getD w false) := by
  let C : Circuit := ⟨D.gates,w⟩
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    exact ⟨h.1 g hg,by have eq := h.2.2 g hg; omega⟩
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  exact cmono C hm n x y hxy

end PlaneOrdered

namespace Promise17245
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := Fin 13
abbrev W := Fin 26
def Inc (p l : V) := (p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat)
instance (p l : V) : Decidable (Inc p l) := by unfold Inc; infer_instance
def vec (X Y : Finset V) (i : W) : Bool :=
  if i.val<13 then decide (Fin.ofNat 13 i.val∈X) else decide (Fin.ofNat 13 i.val∈Y)
def pts (x : W → Bool) := Finset.univ.filter fun p : V => x (Fin.castAdd 13 p)=true
def lns (x : W → Bool) := Finset.univ.filter fun l : V => x (Fin.natAdd 13 l)=true
theorem rebuild (x : W → Bool) : vec (pts x) (lns x)=x := by
  funext i
  unfold vec
  split <;> rename_i hi
  · have eq : Fin.castAdd 13 (Fin.ofNat 13 i.val) = i := Fin.ext (by change i.val%13=i.val; omega)
    simp [pts]
    exact congrArg x eq
  · have eq : Fin.natAdd 13 (Fin.ofNat 13 i.val) = i := Fin.ext (by change 13+i.val%13=i.val; have := i.isLt; omega)
    simp only [lns,Finset.mem_filter,Finset.mem_univ,true_and,eq]
    cases x i <;> rfl
end Promise17245

namespace TerminalStars6530
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Promise17245
abbrev X := W → Bool
abbrev Flag := V × V
def pt (z : Flag) : W := Fin.castAdd 13 z.1
def ln (z : Flag) : W := Fin.natAdd 13 z.2
def flags : Finset Flag := Finset.univ.filter fun e => Inc e.1 e.2
def hasEdge (x : X) : Prop :=
  ∃p l : V, Inc p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
def singletonInput (a : W) : X := fun v => decide (v=a)
def pair (a b : W) : X := fun v => decide (v=a ∨ v=b)
def adj (a b : W) : Bool :=
  decide ((a.val<13 ∧ 13≤b.val ∨ b.val<13 ∧ 13≤a.val) ∧
    (a.val+b.val)%13 ∈ ([0,1,3,9] : List Nat))
def closed (a v : W) : Bool := decide (v=a) || adj a v
def away (a : W) : Finset Flag := flags.filter fun z =>
  closed a (pt z)=false ∧ closed a (ln z)=false
def outside (a : W) : Finset Flag := flags.filter fun z => pt z ≠ a ∧ ln z ≠ a
theorem away_count : ∀a, (away a).card=36 := by decide +kernel
theorem outside_count : ∀a, (outside a).card=48 := by decide +kernel
theorem c4 : ∀a b c d : W, a≠b → c≠d → adj a c=true → adj a d=true →
    adj b c=true → adj b d=false := by decide +kernel
theorem symm : ∀a b, adj a b=adj b a := by decide +kernel
theorem pairEdge : ∀a b, hasEdge (pair a b) ↔ adj a b=true := by
  unfold hasEdge
  decide +kernel
def wire (C : Circuit) (k : Nat) (x : X) := (C.wires (List.ofFn x)).getD k false
def exactPair (C : Circuit) (a b : Nat) : Prop :=
  ∀P L : Finset V, GateOp.and.eval ([a,b].map (fun w => wire C w (vec P L)))=true ↔
    ∃p∈P,∃l∈L,Inc p l
def S (C : Circuit) (k : Nat) := Finset.univ.filter fun a : W =>
  wire C k (singletonInput a)=true
theorem decode {C a b} (h : exactPair C a b) (x : X) :
    wire C a x=true ∧ wire C b x=true ↔ hasEdge x := by
  have step := h (pts x) (lns x)
  rw [rebuild] at step
  change (wire C a x && (wire C b x && true))=true ↔ _ at step
  simp only [Bool.and_true,Bool.and_eq_true] at step
  rw [step]
  constructor
  · rintro ⟨p,hp,l,hl,ed⟩
    exact ⟨p,l,ed,(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hl).2⟩
  · rintro ⟨p,l,ed,hp,hl⟩
    exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩,ed⟩
theorem liftWire (C : Circuit) (h : Monotone2 C) (k : Nat) (v a b : W)
    (hv : v=a ∨ v=b) (yes : wire C k (singletonInput v)=true) : wire C k (pair a b)=true := by
  let D : Circuit := ⟨C.gates,k⟩
  have hd : Monotone2 D := h
  apply PlaneOrdered.cmono D hd 26 (singletonInput v) (pair a b) _ yes
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  have eq : i=v := of_decide_eq_true hi
  apply decide_eq_true
  simpa only [eq] using hv
theorem cross {C a b} (h : Monotone2 C) (e : exactPair C a b) :
    ∀u∈S C a,∀v∈S C b, adj u v=true := by
  intro u hu v hv
  apply (pairEdge u v).mp
  apply (decode e _).mp
  exact ⟨liftWire C h a u u v (Or.inl rfl) (Finset.mem_filter.mp hu).2,
    liftWire C h b v u v (Or.inr rfl) (Finset.mem_filter.mp hv).2⟩
theorem shape {A B : Finset W} (h : ∀u∈A,∀v∈B,adj u v=true) (ha : A.Nonempty) (hb : B.Nonempty) :
    ∃k, (A={k} ∨ B={k}) ∧ ∀v∈A∪B, closed k v=true := by
  obtain ⟨u,hu⟩ := ha
  obtain ⟨v,hv⟩ := hb
  by_cases one : ∀w∈A,w=u
  · have ea : A={u} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hu,one⟩
    refine ⟨u,Or.inl ea,?_⟩
    intro w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · simp [closed,one w hw]
    · simp [closed,h u hu w hw]
  · push_neg at one
    obtain ⟨z,hz,hzu⟩ := one
    have only (w : W) (hw : w∈B) : w=v := by
      by_contra hne
      have bad := c4 z u w v hzu hne (h z hz w hw) (h z hz v hv) (h u hu w hw)
      rw [h u hu v hv] at bad
      contradiction
    have eb : B={v} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hv,only⟩
    refine ⟨v,Or.inr eb,?_⟩
    intro w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · have same : adj v w=true := (symm v w).trans (h w hw v hv)
      simp [closed,same]
    · simp [closed,only w hw]
def doubleFlags (C : Circuit) (a b : Nat) : Finset Flag :=
  flags.filter fun z => pt z ∉ S C a ∪ S C b ∧ ln z ∉ S C a ∪ S C b
def splitFlags (C : Circuit) (a b : Nat) : Finset Flag :=
  flags.filter fun z => (pt z ∈ S C a ∧ ln z ∈ S C b) ∨ (ln z ∈ S C a ∧ pt z ∈ S C b)
theorem bounds {C a b} (h : Monotone2 C) (e : exactPair C a b)
    (ha : (S C a).Nonempty) (hb : (S C b).Nonempty) :
    36≤(doubleFlags C a b).card ∧ 48≤(flags \ splitFlags C a b).card := by
  obtain ⟨k,one,sub⟩ := shape (cross h e) ha hb
  constructor
  · rw [←away_count k]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨flag,pp,ll⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨flag,fun y => by rw [sub _ y] at pp; contradiction,
      fun y => by rw [sub _ y] at ll; contradiction⟩
  · rw [←outside_count k]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨flag,pp,ll⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_sdiff.mpr ⟨flag,?_⟩
    intro hh
    have hh' := (Finset.mem_filter.mp hh).2
    rcases one with eo|eo <;> rw [eo] at hh' <;>
      simp only [Finset.mem_singleton] at hh' <;> tauto
end TerminalStars6530
namespace TerminalStars6530
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Promise17245

def boost (x : X) (a : W) : X := fun i => x i || decide (i=a)
def Agree (f : X → Bool) (x : X) : Prop := f x=true ↔ hasEdge x
theorem monotoneWire (C : Circuit) (hm : Monotone2 C) (w : Nat) : Monotone (wire C w) := by
  intro x y sub
  let D : Circuit := ⟨C.gates,w⟩
  have hd : Monotone2 D := hm
  exact Bool.le_iff_imp.mpr (PlaneOrdered.cmono D hd 26 x y sub)
theorem leBoost (x : X) (a : W) : x ≤ boost x a := by
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  simp [boost,hi]
theorem singletonBoost (x : X) (a : W) : singletonInput a ≤ boost x a := by
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  have e : i=a := of_decide_eq_true hi
  simp [e,boost]
theorem flagAdj : ∀p l : V, Inc p l → adj (Fin.castAdd 13 p) (Fin.natAdd 13 l)=true := by decide +kernel
theorem boostEdge (a : W) (x : X) (off : ∀v,x v=true → adj a v=false) :
    hasEdge (boost x a) → hasEdge x := by
  rintro ⟨p,l,ed,hp,hl⟩
  have ad := flagAdj p l ed
  change (x _ || decide (_=a))=true at hp hl
  simp only [Bool.or_eq_true,decide_eq_true_eq] at hp hl
  rcases hp with hp|hp <;> rcases hl with hl|hl
  · exact ⟨p,l,ed,hp,hl⟩
  · rw [hl] at ad
    have bad := off _ hp
    rw [symm,ad] at bad
    contradiction
  · rw [hp] at ad
    rw [off _ hl] at ad
    contradiction
  · have noSame : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro eq
      have eq' := congrArg Fin.val eq
      change p.val=13+l.val at eq'
      omega
    exact (noSame (hp.trans hl.symm)).elim
theorem guardRestriction {C : Circuit} {a b : Nat} (hm : Monotone2 C) (ex : exactPair C a b)
    (u : W) (hu : u∈S C a) (x : X) (off : ∀v,x v=true → adj u v=false) :
    Agree (wire C b) x := by
  constructor
  · intro yes
    have ha := Bool.le_iff_imp.mp (monotoneWire C hm a (singletonBoost x u)) (Finset.mem_filter.mp hu).2
    have hb := Bool.le_iff_imp.mp (monotoneWire C hm b (leBoost x u)) yes
    exact boostEdge u x off ((decode ex _).mp ⟨ha,hb⟩)
  · intro yes
    exact ((decode ex _).mpr yes).2
theorem flipPair {C : Circuit} {a b : Nat} (ex : exactPair C a b) : exactPair C b a := by
  intro P L
  have e := ex P L
  change (_ && (_ && true))=true ↔ _ at e ⊢
  simpa only [Bool.and_true,Bool.and_eq_true,and_comm] using e
def coreVertices (u v : W) : Finset W := Finset.univ.filter fun w => adj u w=false ∧ adj v w=false
def coreFlags (u v : W) : Finset Flag := flags.filter fun f => pt f∈coreVertices u v ∧ ln f∈coreVertices u v
theorem coreCounts : ∀u v, adj u v=true → (coreVertices u v).card=18 ∧ (coreFlags u v).card=27 := by decide +kernel
theorem sameCore {C : Circuit} {a b : Nat} (hm : Monotone2 C) (ex : exactPair C a b) {u v : W}
    (hu : u∈S C a) (hv : v∈S C b) :
    (coreVertices u v).card=18 ∧ (coreFlags u v).card=27 ∧
    ∀x : X,(∀w,x w=true → w∈coreVertices u v) → Agree (wire C a) x ∧ Agree (wire C b) x := by
  have ad := cross hm ex _ hu _ hv
  obtain ⟨m,n⟩ := coreCounts u v ad
  refine ⟨m,n,?_⟩
  intro x mask
  exact ⟨guardRestriction hm (flipPair ex) v hv x (fun w h => (Finset.mem_filter.mp (mask w h)).2.2),
    guardRestriction hm ex u hu x (fun w h => (Finset.mem_filter.mp (mask w h)).2.1)⟩
theorem distinguish : ∀a v : W, a≠v → ∃k : W,adj a k=false ∧ adj v k=true := by decide +kernel
theorem essential25 {C : Circuit} {a b : Nat} (hm : Monotone2 C) (ex : exactPair C a b) {u : W}
    (hu : u∈S C a) (v : W) (different : u≠v) :
    ∃x y : X, x u=true ∧ y u=true ∧ (∀i,i≠v → x i=y i) ∧ wire C b x=false ∧ wire C b y=true := by
  obtain ⟨k,uk,vk⟩ := distinguish _ _ different
  let x := pair u k
  let y := boost x v
  have hit : wire C a x=true := liftWire C hm a u u k (Or.inl rfl) (Finset.mem_filter.mp hu).2
  have no : wire C b x=false := by
    cases h : wire C b x with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion (uk.symm.trans ((pairEdge u k).mp ((decode ex x).mp ⟨hit,h⟩))))
  have pos : hasEdge y := by
    obtain ⟨p,l,edge,hp,hl⟩ := (pairEdge v k).mpr vk
    have sub (j : W) (h : pair v k j=true) : y j=true := by
      have h' : j=v ∨ j=k := of_decide_eq_true h
      rcases h' with rfl|rfl <;> simp [y,boost,x,pair]
    exact ⟨p,l,edge,sub _ hp,sub _ hl⟩
  refine ⟨x,y,by simp [x,pair],by simp [x,y,boost,pair],?_,no,((decode ex y).mpr pos).2⟩
  intro i hi
  simp [y,boost,hi]
end TerminalStars6530
namespace CofactorPrice6530
open PEqualNP.MetaComplexity Promise17245 TerminalStars6530 Formula5176
abbrev F := DMFormula 26
abbrev Pos (f : F) : Prop := DMFormula.rec (motive:=fun _ : F => Prop)
  (fun _ c => c=true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) f
def live (u v : W) := !(closed u v)
def pin (u : W) (x : X) (v : W) := if v=u then true else live u v && x v
def adjH (u a b : W) : Bool := adj a b && live u a && live u b
theorem irr : ∀a : W, adj a a=false := by decide +kernel
def H (u : W) : SimpleGraph W where
  Adj := fun a b => adjH u a b=true
  symm := ⟨by
    intro a b h
    unfold adjH at h ⊢
    rw [symm b a]
    simp only [Bool.and_eq_true] at h ⊢
    tauto⟩
  loopless := ⟨by intro a; simp [adjH,irr]⟩
instance (u : W) : DecidableRel (H u).Adj := fun _ _ => inferInstanceAs (Decidable (_ = true))
def mp (i : V) : W := Fin.castAdd 13 i
def ml (i : V) : W := Fin.natAdd 13 (-i)
def mateCode (v : W) : V := if v.val<13 then Fin.ofNat 13 v.val else -(Fin.ofNat 13 v.val)
def mset (u : W) := Finset.univ.filter fun i : V => adjH u (mp i) (ml i)=true
theorem certA : ∀u : W, (H u).edgeFinset.card=36 ∧ (mset u).card=9 := by decide +kernel
theorem certB : ∀i : V, mateCode (mp i)=i ∧ mateCode (ml i)=i := by decide +kernel
theorem noTri : ∀a b c : W, adj a b=true → adj b c=true → adj c a=false := by decide +kernel
theorem projectedCost (u : W) (f : F) (pos : Pos f)
    (computes : ∀x, f.eval x=decide (∃a b : W,(H u).Adj a b ∧ x a=true ∧ x b=true)) :
    45≤f.leaves := by
  have inc {a b : W} (h : (H u).Adj a b) : adj a b=true := by
    change adjH u a b=true at h
    simp only [adjH,Bool.and_eq_true] at h
    exact h.1.1
  have tri (a b c : W) : ¬((H u).Adj a b ∧ (H u).Adj b c ∧ (H u).Adj c a) := by
    rintro ⟨ab,bc,ca⟩
    have bad := noTri a b c (inc ab) (inc bc)
    rw [inc ca] at bad
    contradiction
  have sq (a b c d : W) (ac : a≠c) (bd : b≠d) :
      ¬((H u).Adj a b ∧ (H u).Adj b c ∧ (H u).Adj c d ∧ (H u).Adj d a) := by
    rintro ⟨ab,bc,cd,da⟩
    have bad := c4 a c b d ac bd (inc ab) (inc da.symm) (inc bc.symm)
    rw [inc cd] at bad
    contradiction
  obtain ⟨K,hit,cost,_⟩ := colouredPrice 26 (H u) tri sq f pos computes
  let pick (i : V) := if mp i∈K then mp i else ml i
  have inv (i : V) : mateCode (pick i)=i := by
    dsimp [pick]
    split
    · exact (certB i).1
    · exact (certB i).2
  have inj : Function.Injective pick := fun a b h => (inv a).symm.trans ((congrArg mateCode h).trans (inv b))
  have sub : (mset u).image pick ⊆ K := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have ed : (H u).Adj (mp i) (ml i) := (Finset.mem_filter.mp hi).2
    dsimp [pick]
    split <;> rename_i h
    · exact h
    · exact (hit _ _ ed).resolve_left h
  have number := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj,(certA u).2] at number
  rw [(certA u).1] at cost
  omega

inductive Reduced where
  | constant (b : Bool)
  | formula (f : F)
def ev : Reduced → X → Bool
  | .constant b,_ => b
  | .formula f,x => f.eval x
def sz : Reduced → Nat
  | .constant _ => 0
  | .formula f => f.leaves
def posR : Reduced → Prop
  | .constant _ => True
  | .formula f => Pos f
def merge : Bool → Reduced → Reduced → Reduced
  | true,.constant false,_ | true,_,.constant false => .constant false
  | true,.constant true,b | true,b,.constant true => b
  | true,.formula a,.formula b => .formula (.and a b)
  | false,.constant true,_ | false,_,.constant true => .constant true
  | false,.constant false,b | false,b,.constant false => b
  | false,.formula a,.formula b => .formula (.or a b)
theorem calcMerge (b : Bool) (a c : Reduced) (x : X) :
    ev (merge b a c) x=(if b then ev a x && ev c x else ev a x || ev c x) ∧
    sz (merge b a c)≤sz a+sz c ∧ (posR a → posR c → posR (merge b a c)) := by
  cases b <;> cases a with
  | constant p => cases p <;> cases c with
    | constant q => cases q <;> simp [merge,ev,sz,posR]
    | formula g => simp [merge,ev,sz,posR,DMFormula.eval]
  | formula f => cases c with
    | constant q => cases q <;> simp [merge,ev,sz,posR,DMFormula.eval]
    | formula g => simp [merge,ev,sz,posR,Pos,DMFormula.eval,DMFormula.leaves] <;> tauto

def sliced (u : W) : F → Reduced
  | .lit v b => if live u v then .formula (.lit v b) else .constant (if b then decide (v=u) else !decide (v=u))
  | .and a b => merge true (sliced u a) (sliced u b)
  | .or a b => merge false (sliced u a) (sliced u b)
def weight (u : W) : F → Nat
  | .lit v _ => if live u v then 1 else 0
  | .and a b | .or a b => weight u a+weight u b
theorem slicedFacts (u : W) (f : F) (hp : Pos f) (x : X) :
    ev (sliced u f) x=f.eval (pin u x) ∧ sz (sliced u f)≤weight u f ∧ posR (sliced u f) := by
  induction f with
  | lit v b =>
    change b=true at hp
    subst b
    by_cases eq : v=u
    · simp [eq,sliced,live,closed,pin,ev,sz,weight,posR,DMFormula.eval]
    · cases z : live u v <;> simp [sliced,z,eq,pin,ev,sz,weight,posR,Pos,DMFormula.eval,DMFormula.leaves]
  | and a b ia ib =>
    obtain ⟨ha,sa,pa⟩ := ia hp.1
    obtain ⟨hb,sb,pb⟩ := ib hp.2
    obtain ⟨e,s,p⟩ := calcMerge true (sliced u a) (sliced u b) x
    exact ⟨by simpa [sliced,DMFormula.eval,ha,hb] using e, s.trans (Nat.add_le_add sa sb),p pa pb⟩
  | or a b ia ib =>
    obtain ⟨ha,sa,pa⟩ := ia hp.1
    obtain ⟨hb,sb,pb⟩ := ib hp.2
    obtain ⟨e,s,p⟩ := calcMerge false (sliced u a) (sliced u b) x
    exact ⟨by simpa [sliced,DMFormula.eval,ha,hb] using e, s.trans (Nat.add_le_add sa sb),p pa pb⟩

theorem nonconst : ∀u : W,∃a b : W,(H u).Adj a b := by decide +kernel
theorem weightedPrice (u : W) (f : F) (p : Pos f)
    (correct : ∀x, f.eval (pin u x)=decide (∃a b : W,(H u).Adj a b ∧ x a=true ∧ x b=true)) :
    45≤weight u f := by
  have eq (x : X) := (slicedFacts u f p x).1.trans (correct x)
  cases h : sliced u f with
  | constant b =>
    obtain ⟨a,c,ac⟩ := nonconst u
    have pos := eq (fun _ => true)
    have neg := eq (fun _ => false)
    rw [h] at pos neg
    have yes : ∃a b : W,(H u).Adj a b ∧ (true=true) ∧ (true=true) := ⟨a,c,ac,rfl,rfl⟩
    have pp : b=true := pos.trans (decide_eq_true yes)
    have nn : b=false := by simpa [ev] using neg
    rw [nn] at pp
    contradiction
  | formula q =>
    have r := (slicedFacts u f p (fun _=>false)).2
    rw [h] at r
    exact (projectedCost u q r.2 (fun x => by simpa [h,ev] using eq x)).trans r.1
end CofactorPrice6530
namespace CofactorPrice6530
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Promise17245 TerminalStars6530
theorem oriented : ∀a b : W, adj a b=true → ∃p l : V, Inc p l ∧
  ((a=Fin.castAdd 13 p ∧ b=Fin.natAdd 13 l) ∨ (b=Fin.castAdd 13 p ∧ a=Fin.natAdd 13 l)) := by decide +kernel
theorem activePair {u a b : W} {x : X} (ad : adj a b=true) (ha : pin u x a=true) (hb : pin u x b=true) :
    live u a=true ∧ live u b=true ∧ x a=true ∧ x b=true := by
  have ea : a≠u := by
    rintro rfl
    by_cases eq : b=a
    · rw [eq,irr] at ad
      contradiction
    · simp [pin,eq,live,closed,ad] at hb
  have eb : b≠u := by
    rintro rfl
    have f := (symm b a).trans ad
    simp [pin,ea,live,closed,f] at ha
  simp only [pin,if_neg ea,if_neg eb,Bool.and_eq_true] at ha hb
  exact ⟨ha.1,hb.1,ha.2,hb.2⟩
theorem pinEdge (u : W) (x : X) : hasEdge (pin u x) ↔
    ∃a b : W,(H u).Adj a b ∧ x a=true ∧ x b=true := by
  constructor
  · rintro ⟨p,l,ed,hp,hl⟩
    have ad := flagAdj _ _ ed
    obtain ⟨lp,ll,pp,pl⟩ := activePair ad hp hl
    exact ⟨_,_,by change adjH u (Fin.castAdd 13 p) (Fin.natAdd 13 l)=true; unfold adjH; simp only [ad,lp,ll,Bool.and_self],pp,pl⟩
  · rintro ⟨a,b,ed,ha,hb⟩
    change adjH u a b=true at ed
    simp only [adjH,Bool.and_eq_true] at ed
    have aOn : pin u x a=true := by simp [pin,ed.1.2,ha]
    have bOn : pin u x b=true := by simp [pin,ed.2,hb]
    obtain ⟨p,l,h,horder⟩ := oriented a b ed.1.1
    rcases horder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨p,l,h,aOn,bOn⟩
    · exact ⟨p,l,h,bOn,aOn⟩
theorem affWire {C a b} (hm : Monotone2 C) (ex : exactPair C a b) {u : W} (hu : u∈S C a) (x : X) :
    wire C b (pin u x)=true ↔ ∃v w : W,(H u).Adj v w ∧ x v=true ∧ x w=true := by
  have sub : singletonInput u ≤ pin u x := by
    intro i
    apply Bool.le_iff_imp.mpr
    intro h
    have eq : i=u := of_decide_eq_true h
    simp [pin,eq]
  have hit := Bool.le_iff_imp.mp (monotoneWire C hm a sub) (Finset.mem_filter.mp hu).2
  simpa [hit,pinEdge] using decode ex (pin u x)
def labs : F → List W
  | .lit v _ => [v]
  | .and a b | .or a b => labs a++labs b
theorem respects (f : F) (x y : X) (agree : ∀i∈labs f,x i=y i) : f.eval x=f.eval y := by
  induction f with
  | lit v c => simp [DMFormula.eval,agree v (by simp [labs])]
  | and a b ia ib =>
    rw [DMFormula.eval,DMFormula.eval,ia (fun i hi => agree i (by simp [labs,hi])),ib (fun i hi => agree i (by simp [labs,hi]))]
  | or a b ia ib =>
    rw [DMFormula.eval,DMFormula.eval,ia (fun i hi => agree i (by simp [labs,hi])),ib (fun i hi => agree i (by simp [labs,hi]))]
theorem leafSum (u : W) (f : F) : weight u f+((labs f).filter fun i => !(live u i)).length=f.leaves := by
  induction f with
  | lit v c => cases h : live u v <;> simp [weight,labs,h,DMFormula.leaves]
  | and a b ia ib => simp [labs,weight,DMFormula.leaves,List.filter_append] at *;omega
  | or a b ia ib => simp [labs,weight,DMFormula.leaves,List.filter_append] at *;omega
theorem neighborsFour : ∀u : W,(Finset.univ.filter fun v : W => adj u v=true).card=4 := by decide +kernel
theorem tapPrice {C a b} (hm : Monotone2 C) (ex : exactPair C a b) {u : W} (hu : u∈S C a)
    (f : F) (pf : Pos f) (computes : ∀x, f.eval x=wire C b x) : 49≤f.leaves := by
  have core := weightedPrice u f pf (fun x => by
    rw [computes]
    cases h : wire C b (pin u x) with
    | true => exact (decide_eq_true ((affWire hm ex hu x).mp h)).symm
    | false => apply Eq.symm; apply decide_eq_false; intro h';rw [(affWire hm ex hu x).mpr h'] at h;contradiction)
  let L := (labs f).filter fun i => !(live u i)
  have sub : (Finset.univ.filter (fun v : W => adj u v=true)) ⊆ L.toFinset := by
    intro v hv
    have ad := (Finset.mem_filter.mp hv).2
    have diff : u≠v := by rintro rfl;rw [irr] at ad;contradiction
    obtain ⟨x,y,_,_,same,off,on⟩ := essential25 hm ex hu v diff
    have readV : v∈labs f := by
      by_contra nn
      have eq := respects f x y (fun i hi => same i (fun e => nn (e ▸ hi)))
      rw [computes,computes,off,on] at eq
      contradiction
    apply List.mem_toFinset.mpr
    exact List.mem_filter.mpr ⟨readV,by simp [live,closed,ad]⟩
  have c := (Finset.card_le_card sub).trans (List.toFinset_card_le L)
  rw [neighborsFour] at c
  have q := leafSum u f
  change 4≤((labs f).filter fun i => !(live u i)).length at c
  omega
end CofactorPrice6530
