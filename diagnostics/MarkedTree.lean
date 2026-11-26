import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Choose
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_18294
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
      · funext i; subst LA; subst LB; rfl
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
      · funext i; subst LA; subst LB; rfl
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
    let ix : ↥I ≃ Fin I.card := by simpa only [Fintype.card_coe] using Fintype.equivFin (↥I)
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


namespace CoverRigidity4801

abbrev pt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
abbrev ln (l : Fin 13) : Fin 26 := Fin.natAdd 13 l

/-- Two cyclic matchings already force every cover of size 13 to be a whole side. -/
theorem two_matchings (T : Finset (Fin 26)) (card : T.card = 13)
    (first : ∀ i, pt (i+1) ∈ T ∨ ln i ∈ T)
    (third : ∀ i, pt (i+3) ∈ T ∨ ln i ∈ T) :
    (∀ i, pt i ∈ T) ∨ (∀ i, ln i ∈ T) := by
  let pick (i : Fin 13) : T := if h : pt (i+1) ∈ T then ⟨pt (i+1),h⟩ else ⟨ln i,(first i).resolve_left h⟩
  let index : Fin 26 → Fin 13 := fun w => Fin.addCases (motive := fun _ => Fin 13) (fun p : Fin 13 => p-1) (fun l : Fin 13 => l) w
  have idxL (i : Fin 13) : index (ln i) = i := by
    change Fin.addCases (motive := fun _ => Fin 13) (fun p : Fin 13 => p-1) (fun l : Fin 13 => l) (Fin.natAdd 13 i) = i
    rw [Fin.addCases_right]
  have idxP (i : Fin 13) : index (pt (i+1)) = i := by simp [index,pt,Fin.addCases_left]
  have idx (i : Fin 13) : index (pick i).val = i := by
    dsimp only [pick]
    split <;> first | exact idxP i | exact idxL i
  have inj : Function.Injective pick := by
    intro i j h
    simpa only [idx] using congrArg (fun t : T => index t.val) h
  have sur := ((Fintype.bijective_iff_injective_and_card pick).mpr ⟨inj,by simp [card]⟩).surjective
  have apart : ∀ i j, pt i ≠ ln j := by decide
  have excl (i : Fin 13) (inP : pt (i+1) ∈ T) : ln i ∉ T := by
    intro inL
    obtain ⟨j,eq⟩ := sur ⟨ln i,inL⟩
    have v : (pick j).val = ln i := congrArg Subtype.val eq
    have same : j = i := by simpa only [idx,idxL] using congrArg index v
    subst j
    exact apart _ _ (by simpa [pick,inP] using v)
  let P (i : Fin 13) := pt (i+1) ∈ T
  have next (i : Fin 13) (h : P i) : P (i+2) := by
    have v := (third i).resolve_right (excl i h)
    change pt ((i+2)+1) ∈ T
    have plus : ∀ x : Fin 13, (x+2)+1 = x+3 := by decide
    rw [plus]
    exact v
  let step (x : Fin 13) := x+2
  have many (i : Fin 13) (k : ℕ) (h : P i) : P (step^[k] i) := by
    induction k with
    | zero => exact h
    | succ k ih => rw [Function.iterate_succ_apply']; exact next _ ih
  by_cases somePoint : ∃ i, P i
  · obtain ⟨i,h⟩ := somePoint
    have orbit : ∀ a b : Fin 13, ∃ k : Fin 13, step^[k.val] a = b := by decide
    left
    intro j
    obtain ⟨k,hk⟩ := orbit i (j-1)
    have a := many i k.val h
    rw [hk] at a
    have plus : ∀ x : Fin 13, (x-1)+1 = x := by decide
    change pt ((j-1)+1) ∈ T at a
    rwa [plus] at a
  · exact Or.inr (fun i => (first i).resolve_left (fun h => somePoint ⟨i,h⟩))

end CoverRigidity4801

namespace Tree5176

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (u v : Fin 26) : Bool :=
  if u.val < 13 then decide (13 ≤ v.val) && [0,1,3,9].contains ((u.val+26-v.val)%13)
  else decide (v.val < 13) && [0,1,3,9].contains ((v.val+26-u.val)%13)

def plane : SimpleGraph (Fin 26) where
  Adj u v := edge u v = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel plane.Adj := fun u v => inferInstanceAs (Decidable (edge u v = true))

open Formula5176 PEqualNP.MetaComplexity CoverRigidity4801

theorem onlyLeaves {n : ℕ} (φ : DMFormula n) (x y : Fin n → Bool)
    (equal : ∀ i, x (leafLabel φ i)=y (leafLabel φ i)) : φ.eval x = φ.eval y := by
  induction φ with
  | lit v t =>
    have h := equal ⟨0,by change 0<1; decide⟩
    change x v=y v at h
    simp [DMFormula.eval,h]
  | and a b ha hb =>
    have ea := ha (fun i => by simpa only [leafLabel,Fin.addCases_left] using equal (Fin.castAdd b.leaves i))
    have eb := hb (fun i => by simpa only [leafLabel,Fin.addCases_right] using equal (Fin.natAdd a.leaves i))
    simp only [DMFormula.eval,ea,eb]
  | or a b ha hb =>
    have ea := ha (fun i => by simpa only [leafLabel,Fin.addCases_left] using equal (Fin.castAdd b.leaves i))
    have eb := hb (fun i => by simpa only [leafLabel,Fin.addCases_right] using equal (Fin.natAdd a.leaves i))
    simp only [DMFormula.eval,ea,eb]

theorem allUsed (φ : DMFormula 26)
    (spec : ∀ x, φ.eval x=decide (∃ u v, plane.Adj u v ∧ x u=true ∧ x v=true)) :
    Function.Surjective (leafLabel φ) := by
  intro t
  by_contra no
  have neighbor : ∀ t : Fin 26, ∃ v : Fin 26, plane.Adj t v := by decide
  obtain ⟨v,e⟩ := neighbor t
  let x := fun i : Fin 26 => decide (i=t ∨ i=v)
  let y := fun i : Fin 26 => decide (i=v)
  have eq := onlyLeaves φ x y (by
    intro i; have hn : leafLabel φ i ≠ t := fun h => no ⟨i,h⟩
    simp [x,y,hn])
  have hx : φ.eval x=true := (spec x).trans (decide_eq_true ⟨t,v,e,by simp [x],by simp [x]⟩)
  have hy : φ.eval y=false := by
    rw [spec]; apply decide_eq_false
    rintro ⟨u,w,ed,hu,hw⟩
    change decide (u=v)=true at hu
    change decide (w=v)=true at hw
    rw [of_decide_eq_true hu,of_decide_eq_true hw] at ed
    exact plane.loopless.irrefl _ ed
  exact Bool.noConfusion (hx.symm.trans (eq.trans hy))

theorem fibreOne {m : ℕ} (f : Fin m → Fin 26) (surj : Function.Surjective f)
    (hm : m≤65) (T : Finset (Fin 26)) (ht : T.card=13)
    (other : 52 ≤ (Finset.univ.filter (fun i => f i∉T)).card) :
    ∀ t∈T, ∃! i, f i=t := by
  let U := Finset.univ.filter (fun i => f i∈T)
  have split : U.card+(Finset.univ.filter (fun i => f i∉T)).card=m := by
    simpa [U] using (Finset.card_filter_add_card_filter_not (s:=(Finset.univ : Finset (Fin m))) (fun i => f i∈T))
  let g (i : ↥U) : ↥T := ⟨f i.val,(Finset.mem_filter.mp i.property).2⟩
  have gs : Function.Surjective g := by
    intro t; obtain ⟨i,hi⟩ := surj t.val
    have iu : i∈U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.symm ▸ t.property⟩
    exact ⟨⟨i,iu⟩,Subtype.ext hi⟩
  have lb := Fintype.card_le_of_surjective g gs
  simp only [Fintype.card_coe] at lb
  have same : Fintype.card (↥U)=Fintype.card (↥T) := by simp only [Fintype.card_coe]; omega
  have gi : Function.Injective g := ((Fintype.bijective_iff_surjective_and_card g).2 ⟨gs,same⟩).injective
  intro t hT
  obtain ⟨i,hi⟩ := surj t
  refine ⟨i,hi,?_⟩
  intro j hj
  let ij (k : Fin m) (h : f k=t) : ↥U := ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.symm ▸ hT⟩⟩
  exact congrArg Subtype.val (gi (a₁:=ij j hj) (a₂:=ij i hi) (Subtype.ext (hj.trans hi.symm)))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem wholeSide (φ : DMFormula 26) (hm : φ.leaves≤65)
    (positive : DMFormula.rec (motive := fun _ : DMFormula 26 => Prop)
      (fun (_ : Fin 26) (c : Bool) => c=true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ)
    (spec : ∀ x, φ.eval x=decide (∃ u v, plane.Adj u v ∧ x u=true ∧ x v=true)) :
    (∀ p : Fin 13, ∃! i, leafLabel φ i=pt p) ∨ (∀ l : Fin 13, ∃! i, leafLabel φ i=ln l) := by
  let P : Finset (Fin 26) := Finset.univ.image pt
  let L : Finset (Fin 26) := Finset.univ.image ln
  have tri : ∀ a b c, ¬(plane.Adj a b ∧ plane.Adj b c ∧ plane.Adj c a) := by decide +kernel
  have thin : ∀ u v : Fin 26, u≠v → (Finset.univ.filter (fun t : Fin 26 => plane.Adj u t ∧ plane.Adj v t)).card≤1 := by decide +kernel
  have sq (a b c d : Fin 26) (hac : a≠c) (hbd : b≠d) :
      ¬(plane.Adj a b ∧ plane.Adj b c ∧ plane.Adj c d ∧ plane.Adj d a) := by
    rintro ⟨hab,hbc,hcd,hda⟩
    exact hbd (Finset.card_le_one.mp (thin a c hac) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab,hbc.symm⟩)
      d (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hda.symm,hcd⟩))
  obtain ⟨T,cover,cost,colors⟩ := colouredPrice 26 plane tri sq φ positive spec
  have ec : plane.edgeFinset.card=52 := by decide +kernel
  have matchE : ∀ i : Fin 13, plane.Adj (pt i) (ln i) := by decide
  let pick (i : Fin 13) := if pt i∈T then pt i else ln i
  have inside (i : Fin 13) : pick i∈T := by
    by_cases h : pt i∈T
    · simpa [pick,h] using h
    · simpa [pick,h] using (cover _ _ (matchE i)).resolve_left h
  let left (i : Fin 26) := Fin.ofNat 13 i.val
  have inv : ∀ i : Fin 13, left (pt i)=i ∧ left (ln i)=i := by decide
  have back (i : Fin 13) : left (pick i)=i := by dsimp only [pick]; split <;> first | exact (inv i).1 | exact (inv i).2
  have inj : Function.Injective pick := fun i j h => (back i).symm.trans ((congrArg left h).trans (back j))
  have lb := Finset.card_le_card_of_injOn (s:=(Finset.univ : Finset (Fin 13))) (t:=T) pick (fun i _ => inside i) inj.injOn
  simp only [Finset.card_univ,Fintype.card_fin] at lb
  have ht : T.card=13 := by omega
  have eis : ∀ i : Fin 13, plane.Adj (pt (i+1)) (ln i) ∧ plane.Adj (pt (i+3)) (ln i) := by decide
  obtain pure|pure := two_matchings T ht (fun i => cover _ _ (eis i).1) (fun i => cover _ _ (eis i).2)
  · left
    have eq : P=T := Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr (fun i _ => pure i)) (by rw [ht]; decide)
    have neighbors : ∀ u v, plane.Adj u v → u∈P → v∈Pᶜ := by decide
    have other := colors Pᶜ (by simpa only [←eq] using neighbors)
    rw [ec] at other
    exact fun i => fibreOne _ (allUsed φ spec) hm T ht (by simpa [←eq] using other) _ (pure i)
  · right
    have eq : L=T := Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr (fun i _ => pure i)) (by rw [ht]; decide)
    have neighbors : ∀ u v, plane.Adj u v → u∈L → v∈Lᶜ := by decide
    have other := colors Lᶜ (by simpa only [←eq] using neighbors)
    rw [ec] at other
    exact fun i => fibreOne _ (allUsed φ spec) hm T ht (by simpa [←eq] using other) _ (pure i)

end Tree5176

-- The clean-gate cover certificate below is adapted from the project’s L_meta_1602.
namespace Singleton5176

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

theorem singleton_protection : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (z : Fin n → Bool) (S : Set ℕ),
    PEqualNP.TopForm.IsAO2 n C →
    let w := fun k => (C.wires (List.ofFn z)).getD k false
    (∀ i : Fin n, ↑i ∈ S → z i = false) →
    (∀ j g, C.gates[j]? = some g → n+j ∈ S →
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i ∈ g.inputs, i ∈ S) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∃ i ∈ g.inputs, i ∈ S) ∨ ∀ i ∈ g.inputs, w i = false)) →
    ∀ k ∈ S, w k = false := by
  intro n C z S model _ raw closed
  let w := fun (k : ℕ) => (wiresFrom C.gates (List.ofFn z)).getD k false
  change ∀ k ∈ S, w k = false
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro mem
    by_cases hk : k<n
    · change (wiresFrom _ _).getD k false = false
      rw [getD_wiresFrom_lt _ _ _ (by simpa using hk)]
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
      exact raw ⟨k,hk⟩ mem
    by_cases hend : k<n+C.gates.length
    · let j := k-n
      have hj : j<C.gates.length := by dsimp [j]; omega
      have pos : k=n+j := by dsimp [j]; omega
      let g := C.gates[j]
      have hit : C.gates[j]?=some g := List.getElem?_eq_getElem hj
      have gin : g∈C.gates := List.mem_of_getElem? hit
      have prior (a) (ha : a∈g.inputs) : a<n+j := by
        apply model.2.1 j hj a
        change a∈(C.gates.getD j ⟨.or,[]⟩).inputs
        simpa only [List.getD_eq_getElem _ _ hj] using ha
      have eqv : w k = g.op.eval (g.inputs.map w) := by
        have h := getD_wiresFrom_gate C.gates (List.ofFn z) j hj
        rw [List.length_ofFn] at h
        rw [pos]
        change (wiresFrom C.gates _).getD (n+j) false = _
        refine h.trans ?_
        congr 1
        apply List.map_congr_left
        intro i hi
        exact if_pos (prior i hi)
      have stop := closed j g hit (pos ▸ mem)
      rw [eqv]
      rcases model.1 g gin with tag|tag
      · rw [tag]
        apply Bool.eq_false_iff.mpr
        intro all
        simp only [GateOp.eval, List.all_eq_true, id_eq] at all
        have accepts (i) (hi : i∈g.inputs) : w i=true := all _ (List.mem_map_of_mem hi)
        rcases stop.2 tag with ⟨i,hi,si⟩|none
        · exact Bool.noConfusion ((ih i (by have := prior i hi; omega) si).symm.trans (accepts i hi))
        · obtain ⟨i,hi⟩ : ∃ i, i∈g.inputs := List.exists_mem_of_ne_nil _ (by
            intro emp; have h := model.2.2 g gin; simp [emp] at h)
          exact Bool.noConfusion ((none i hi).symm.trans (accepts i hi))
      · rw [tag]
        apply Bool.eq_false_iff.mpr
        intro any
        simp only [GateOp.eval, List.any_eq_true, id_eq] at any
        obtain ⟨t,ht,vt⟩ := any
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
        exact Bool.noConfusion ((ih i (by have := prior i hi; omega) (stop.1 tag i hi)).symm.trans vt)
    · apply List.getD_eq_default
      rw [length_wiresFrom, List.length_ofFn]
      omega

end Singleton5176
namespace Occurrence5176
open PEqualNP.MetaComplexity

/-- Number of occurrences of the selected raw input in the unfolded circuit. -/
def copies {n} (t : Fin n) : DMFormula n → Nat
  | .lit v _ => if v=t then 1 else 0
  | .and a b | .or a b => copies t a + copies t b

/-- The linear trace for one raw input on the evaluation at `x`. -/
def trace {n} (t : Fin n) (x : Fin n → Bool) : DMFormula n → Bool
  | .lit v _ => decide (v=t)
  | .and a b => (trace t x a && b.eval x) || (a.eval x && trace t x b)
  | .or a b => trace t x a || trace t x b

theorem unchanged {n} (t : Fin n) (x y : Fin n → Bool)
    (same : ∀ i, i≠t → x i=y i) (φ : DMFormula n) (h : copies t φ=0) : φ.eval x = φ.eval y := by
  induction φ with
  | lit v c =>
    have hv : v≠t := by rintro rfl; simp [copies] at h
    simp only [DMFormula.eval,same v hv]
  | and a b ha hb =>
    change copies t a+copies t b=0 at h
    rw [DMFormula.eval,DMFormula.eval,ha (by omega),hb (by omega)]
  | or a b ha hb =>
    change copies t a+copies t b=0 at h
    rw [DMFormula.eval,DMFormula.eval,ha (by omega),hb (by omega)]

theorem trace_of_unique {n} (t : Fin n) (x y : Fin n → Bool)
    (same : ∀ i, i≠t → x i=y i) (φ : DMFormula n) (h : copies t φ≤1)
    (off : φ.eval x=false) (on_ : φ.eval y=true) : trace t x φ=true := by
  induction φ with
  | lit v c =>
    by_cases hv : v=t
    · simp [trace,hv]
    · have z := unchanged t x y same (.lit v c) (by simp [copies,hv]); simp_all
  | and a b ha hb =>
    change copies t a+copies t b≤1 at h
    have yes := Bool.and_eq_true_iff.mp on_
    change (a.eval x && b.eval x)=false at off
    change ((trace t x a && b.eval x) || (a.eval x && trace t x b))=true
    by_cases nz : copies t a=0
    · have at_ := (unchanged t x y same a nz).trans yes.1
      have bf : b.eval x=false := by simpa [at_] using off
      simp [at_,hb (by omega) bf yes.2]
    · have bt := (unchanged t x y same b (by omega)).trans yes.2
      have af : a.eval x=false := by simpa [bt] using off
      simp [bt,ha (by omega) af yes.1]
  | or a b ha hb =>
    change copies t a+copies t b≤1 at h
    have no := Bool.or_eq_false_iff.mp off
    change (trace t x a || trace t x b)=true
    cases h1 : a.eval y with
    | true => simp [ha (by omega) no.1 h1]
    | false =>
      have h2 : b.eval y=true := by simpa [DMFormula.eval,h1] using on_
      simp [hb (by omega) no.2 h2]

end Occurrence5176
namespace Occurrence5176
open Formula5176 PEqualNP.MetaComplexity

private theorem hasLeaf {n} (t : Fin n) (φ : DMFormula n) (h : 0<copies t φ) :
    ∃ i, leafLabel φ i=t := by
  induction φ with
  | lit v c =>
    refine ⟨0,?_⟩
    change v=t
    by_contra hne
    simp [copies,hne] at h
  | and a b ha hb | or a b ha hb =>
    change 0<copies t a+copies t b at h
    by_cases z : 0<copies t a
    · obtain ⟨i,hi⟩ := ha z
      exact ⟨Fin.castAdd _ i,by simpa [leafLabel] using hi⟩
    · obtain ⟨i,hi⟩ := hb (by omega)
      exact ⟨Fin.natAdd _ i,by simpa [leafLabel] using hi⟩

theorem copies_unique {n} (t : Fin n) (φ : DMFormula n)
    (one : ∀ i j, leafLabel φ i=t → leafLabel φ j=t → i=j) : copies t φ≤1 := by
  induction φ with
  | lit v b => by_cases h : v=t <;> simp [copies,h]
  | and a b ha hb | or a b ha hb =>
    change copies t a+copies t b≤1
    have la := ha (by intro i j hi hj; have z := one (Fin.castAdd b.leaves i) (Fin.castAdd b.leaves j) (by simpa [leafLabel] using hi) (by simpa [leafLabel] using hj); exact Fin.ext (congrArg Fin.val z))
    have lb := hb (by
      intro i j hi hj
      have z := one (Fin.natAdd a.leaves i) (Fin.natAdd a.leaves j) (by simpa [leafLabel] using hi) (by simpa [leafLabel] using hj)
      have zz := congrArg Fin.val z
      exact Fin.ext (Nat.add_left_cancel zz))
    by_contra big
    obtain ⟨i,hi⟩ := hasLeaf t a (by omega)
    obtain ⟨j,hj⟩ := hasLeaf t b (by omega)
    have z := one (Fin.castAdd b.leaves i) (Fin.natAdd a.leaves j) (by simpa [leafLabel] using hi) (by simpa [leafLabel] using hj)
    have zz := congrArg Fin.val z
    change i.val = a.leaves+j.val at zz
    omega

end Occurrence5176
namespace Wires5176
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Singleton5176 Occurrence5176

abbrev F := DMFormula 26
abbrev raw0 : F := .lit 0 true

def tree (C : Circuit) (k : Nat) : F :=
  if h : k<26 then .lit ⟨k,h⟩ true else
    let g := C.gates.getD (k-26) ⟨.or,[]⟩
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    if ha : a<k then
      if hb : b<k then
        match g.op with
        | .and => .and (tree C a) (tree C b)
        | _ => .or (tree C a) (tree C b)
      else raw0
    else raw0
termination_by k

private theorem rawTree (C : Circuit) (i : Fin 26) : tree C i.val = .lit i true := by
  rw [tree]
  simp only [i.isLt, ↓reduceDIte]

private theorem childPrior {C : Circuit} (ao : IsAO2 26 C) {j : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) {i : Nat} (mem : i∈g.inputs) : i<26+j := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  apply ao.2.1 j hj i
  simpa only [List.getD_eq_getElem _ _ hj,hg] using mem

private theorem atGate {C : Circuit} (ao : IsAO2 26 C) {j a b : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) (ins : g.inputs=[a,b]) :
    (g.op=.and → tree C (26+j)=.and (tree C a) (tree C b)) ∧
    (g.op=.or → tree C (26+j)=.or (tree C a) (tree C b)) := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  have ga : a<26+j := childPrior ao hit (by simp [ins])
  have gb : b<26+j := childPrior ao hit (by simp [ins])
  have hget : C.gates.getD j ⟨.or,[]⟩=g := by rw [List.getD_eq_getElem _ _ hj,hg]
  constructor <;> intro op <;> rw [tree] <;> simp [hget,ins,op,ga,gb]

abbrev Positive (φ : F) := DMFormula.rec (motive:=fun _ : F => Prop)
    (fun _ c => c=true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

abbrev wire (C : Circuit) (x : Fin 26 → Bool) (k : Nat) := (C.wires (List.ofFn x)).getD k false

private theorem rawValue (C : Circuit) (x : Fin 26 → Bool) (i : Fin 26) : wire C x i.val=x i := by
  change (wiresFrom C.gates (List.ofFn x)).getD i.val false=_
  rw [getD_wiresFrom_lt _ _ _ (by simpa using i.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]

private theorem gateValue {C : Circuit} (ao : IsAO2 26 C) (x : Fin 26 → Bool) {j : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) : wire C x (26+j)=g.op.eval (g.inputs.map (wire C x)) := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  have h := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn,hg] at h
  refine h.trans ?_
  congr 1
  apply List.map_congr_left
  intro i hi
  exact if_pos (childPrior ao hit hi)

theorem semantics {C : Circuit} (ao : IsAO2 26 C) (k : Nat) (valid : k<26+C.size) :
    Positive (tree C k) ∧ ∀ x, (tree C k).eval x=wire C x k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases raw : k<26
    · let i : Fin 26 := ⟨k,raw⟩
      change Positive (tree C i.val) ∧ _
      rw [rawTree]
      exact ⟨rfl,fun x => by simpa [DMFormula.eval] using (rawValue C x i).symm⟩
    let j := k-26
    have hj : j<C.gates.length := by change k<26+C.gates.length at valid; dsimp [j]; omega
    let g := C.gates[j]
    have hit : C.gates[j]?=some g := List.getElem?_eq_getElem hj
    have gin := List.mem_of_getElem? hit
    have pos : k=26+j := by dsimp [j]; omega
    obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g gin)
    have ha := childPrior ao hit (i:=a) (by simp [ins])
    have hb := childPrior ao hit (i:=b) (by simp [ins])
    obtain ⟨pa,ea⟩ := ih a (by omega) (by omega)
    obtain ⟨pb,eb⟩ := ih b (by omega) (by omega)
    rw [pos]
    rcases ao.1 g gin with op|op
    · rw [(atGate ao hit ins).1 op]
      exact ⟨⟨pa,pb⟩,fun x => by simp [gateValue ao x hit,op,ins,GateOp.eval,DMFormula.eval,ea,eb]⟩
    · rw [(atGate ao hit ins).2 op]
      exact ⟨⟨pa,pb⟩,fun x => by simp [gateValue ao x hit,op,ins,GateOp.eval,DMFormula.eval,ea,eb]⟩

end Wires5176
namespace Wires5176
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Singleton5176 Occurrence5176 Formula5176 CoverRigidity4801

private theorem exclude {C : Circuit} (ao : IsAO2 26 C) (x : Fin 26 → Bool) (t : Fin 26)
    (S : Set Nat) (raw : ∀ i : Fin 26, i.val∈S → i≠t)
    (protected_ : ∀ i∈S, wire C x i=false)
    (closed : ∀ j g, C.gates[j]?=some g → 26+j∈S →
      (g.op=.or → ∀ a∈g.inputs,a∈S) ∧
      (g.op=.and → (∃ a∈g.inputs,a∈S) ∨ ∀ a∈g.inputs,wire C x a=false))
    (k : Nat) (hk : k<26+C.size) (hs : k∈S) : trace t x (tree C k)=false := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases h : k<26
    · let i : Fin 26 := ⟨k,h⟩
      change trace t x (tree C i.val)=false
      rw [rawTree]
      simp [trace,raw i hs]
    let j := k-26
    have hj : j<C.gates.length := by change k<26+C.gates.length at hk; dsimp [j]; omega
    let g := C.gates[j]
    have hit : C.gates[j]?=some g := List.getElem?_eq_getElem hj
    have gin := List.mem_of_getElem? hit
    have pos : k=26+j := by dsimp [j]; omega
    obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g gin)
    have ha := childPrior ao hit (i:=a) (by simp [ins])
    have hb := childPrior ao hit (i:=b) (by simp [ins])
    have ea := (semantics ao a (by omega)).2 x
    have eb := (semantics ao b (by omega)).2 x
    obtain ⟨co,ca⟩ := closed j g hit (pos ▸ hs)
    rw [pos]
    rcases ao.1 g gin with op|op
    · rw [(atGate ao hit ins).1 op]
      simp only [trace,ea,eb]
      rcases ca op with ⟨i,hi,si⟩|quiet
      · have ab : i=a ∨ i=b := by simpa [ins] using hi
        rcases ab with rfl|rfl
        · simp [ih _ (by omega) (by omega) si,protected_ _ si]
        · simp [ih _ (by omega) (by omega) si,protected_ _ si]
      · simp [quiet a (by simp [ins]),quiet b (by simp [ins])]
    · rw [(atGate ao hit ins).2 op]
      simp [trace,ih a (by omega) (by omega) (co op a (by simp [ins])),
        ih b (by omega) (by omega) (co op b (by simp [ins]))]

private abbrev oriented (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
private abbrev accepts (x : Fin 26→Bool) := ∃ p l : Fin 13, oriented p l ∧ x (pt p)=true ∧ x (ln l)=true
private abbrev bits (m : Nat) (i : Fin 26) := m.testBit i.val

private theorem graphAccept (x : Fin 26→Bool) : accepts x ↔ ∃ u v, Tree5176.plane.Adj u v ∧ x u=true ∧ x v=true := by
  have forward : ∀ p l, oriented p l → Tree5176.plane.Adj (pt p) (ln l) := by decide
  have back : ∀ u v : Fin 26, Tree5176.plane.Adj u v → ∃ p l, oriented p l ∧
      ((u=pt p ∧ v=ln l) ∨ (v=pt p ∧ u=ln l)) := by decide +kernel
  constructor
  · rintro ⟨p,l,h,hp,hl⟩; exact ⟨_,_,forward p l h,hp,hl⟩
  · rintro ⟨u,v,h,hu,hv⟩
    obtain ⟨p,l,e,s|s⟩ := back u v h
    · exact ⟨p,l,e,s.1 ▸ hu,s.2 ▸ hv⟩
    · exact ⟨p,l,e,s.1 ▸ hv,s.2 ▸ hu⟩


open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

theorem childCopies {C : Circuit} (ao : IsAO2 26 C) (t : Fin 26) (j u : Nat)
    (hj : j<C.gates.length) (hu : u∈(gateAt C j).inputs) :
    copies t (tree C u) ≤ copies t (tree C (26+j)) := by
  let g := C.gates[j]
  have hit : C.gates[j]? = some g := List.getElem?_eq_getElem hj
  have ga : gateAt C j = g := List.getD_eq_getElem _ _ hj
  obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g (List.mem_of_getElem? hit))
  rw [ga,ins] at hu
  have hab : u=a ∨ u=b := by simpa using hu
  rcases ao.1 g (List.mem_of_getElem? hit) with op|op
  · rw [(atGate ao hit ins).1 op]; simp only [copies]; rcases hab with rfl|rfl <;> omega
  · rw [(atGate ao hit ins).2 op]; simp only [copies]; rcases hab with rfl|rfl <;> omega

theorem coneCopies {C : Circuit} (ao : IsAO2 26 C) (t : Fin 26) (i j : Nat)
    (hj : j<C.gates.length) (h : InCone 26 C i j) :
    copies t (tree C (26+i)) ≤ copies t (tree C (26+j)) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨w,hw,hlo,hup,eq|below⟩ := (PEqualNP.Outside.L_meta_18294.Flat.inCone_iff 26 C i j hj).mp h
    · have e : 26+i=w := by omega
      rw [e]; exact childCopies ao t j w hj hw
    · have e : 26+(w-26)=w := by omega
      have cl := ih (w-26) (by omega) (by omega) below
      rw [e] at cl
      exact cl.trans (childCopies ao t j w hj hw)

theorem markedCopies {C : Circuit} (ao : IsAO2 26 C) (k : Nat)
    (op : (gateAt C k).op = .and)
    (live : 26+k=C.output ∨ InCone 26 C k (C.output-26))
    (pair : gateVal 26 C k (pairInput (0 : Fin 26) 13)=true)
    (quiet : ∀ b : Fin 2, wire C (pairInput (0 : Fin 26) 0) (opnd C k b)=false ∧
      wire C (pairInput (13 : Fin 26) 13) (opnd C k b)=false)
    (valid : C.output<26+C.size) : ∀ t ∈ ([0,13] : List (Fin 26)), 2 ≤ copies t (tree C C.output) := by
  have hk : k<C.gates.length := by
    by_contra h
    simp [gateAt,List.getD_eq_default _ _ (Nat.le_of_not_gt h)] at op
  let g := C.gates[k]
  have hit : C.gates[k]?=some g := List.getElem?_eq_getElem hk
  have ga : gateAt C k=g := List.getD_eq_getElem _ _ hk
  have gand : g.op=.and := ga ▸ op
  obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g (List.mem_of_getElem? hit))
  have ea : opnd C k 0 = a := by simp [opnd,ga,ins,List.getD_eq_getElem?_getD]
  have eb : opnd C k 1 = b := by simp [opnd,ga,ins,List.getD_eq_getElem?_getD]
  let xy := pairInput (0 : Fin 26) 13
  have both : wire C xy a=true ∧ wire C xy b=true := by
    change wire C xy (26+k)=true at pair
    simpa [gateValue ao xy hit,gand,ins,GateOp.eval] using pair
  intro t ht
  suffices hh : 2 ≤ copies t (tree C (26+k)) by
    rcases live with e|co
    · rwa [←e]
    · have gte : 26≤C.output := by
        by_contra! raw
        have z : C.output-26=0 := by omega
        rw [z] at co
        have h0 : 0<C.gates.length := by omega
        obtain ⟨w,_,hw1,hw2,_⟩ := (PEqualNP.Outside.L_meta_18294.Flat.inCone_iff 26 C k 0 h0).mp co
        omega
      have idx : C.output-26<C.gates.length := by change C.output<26+C.gates.length at valid; omega
      have e : 26+(C.output-26)=C.output := by omega
      have z := coneCopies ao t k (C.output-26) idx co
      rw [e] at z
      exact hh.trans z
  rw [(atGate ao hit ins).1 gand]
  simp only [copies]
  rcases (show t=0 ∨ t=13 by simpa using ht) with rfl|rfl
  · have hdiff : ∀ i : Fin 26, i≠0 → (pairInput (13 : Fin 26) 13) i=xy i := by decide
    have pos (w : Nat) (hw:w<26+k) (on:wire C xy w=true) (off:wire C (pairInput (13:Fin 26) 13) w=false) : 0<copies 0 (tree C w) := by
      by_contra! zz
      have eq := Occurrence5176.unchanged (0:Fin 26) _ _ hdiff (tree C w) (by omega)
      have val := (semantics ao w (by change w<26+C.gates.length;omega)).2
      rw [val,val,off,on] at eq; cases eq
    have ha := pos a (childPrior ao hit (by simp [ins])) both.1 (ea ▸ (quiet 0).2)
    have hb := pos b (childPrior ao hit (by simp [ins])) both.2 (eb ▸ (quiet 1).2)
    omega
  · have hdiff : ∀ i : Fin 26, i≠13 → (pairInput (0 : Fin 26) 0) i=xy i := by decide
    have pos (w : Nat) (hw:w<26+k) (on:wire C xy w=true) (off:wire C (pairInput (0:Fin 26) 0) w=false) : 0<copies 13 (tree C w) := by
      by_contra! zz
      have eq := Occurrence5176.unchanged (13:Fin 26) _ _ hdiff (tree C w) (by omega)
      have val := (semantics ao w (by change w<26+C.gates.length;omega)).2
      rw [val,val,off,on] at eq; cases eq
    have ha := pos a (childPrior ao hit (by simp [ins])) both.1 (ea ▸ (quiet 0).1)
    have hb := pos b (childPrior ao hit (by simp [ins])) both.2 (eb ▸ (quiet 1).1)
    omega


theorem markedLower {C : Circuit} (ao : IsAO2 26 C) (spec : ∀ x : Fin 26 → Bool,
    C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧
      x (pt p)=true ∧ x (ln l)=true)
    {k : Nat} (op : (gateAt C k).op = .and)
    (live : 26+k=C.output ∨ InCone 26 C k (C.output-26))
    (pair : gateVal 26 C k (pairInput (0 : Fin 26) 13)=true)
    (quiet : ∀ b : Fin 2, wire C (pairInput (0 : Fin 26) 0) (opnd C k b)=false ∧
      wire C (pairInput (13 : Fin 26) 13) (opnd C k b)=false) : 66 ≤ (tree C C.output).leaves := by
  by_contra! small
  have inc : ∀ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ↔ oriented p l := by decide +kernel
  have spec' (x : Fin 26→Bool) : wire C x C.output=true ↔ accepts x :=
    (spec x).trans (exists_congr fun p => exists_congr fun l => and_congr_left fun _ => inc p l)
  have flag : wire C (bits 8193) C.output=true := (spec' _).2 ⟨0,0,Or.inl rfl,by decide,by decide⟩
  have valid : C.output<26+C.size := by
    by_contra h
    change (wiresFrom C.gates (List.ofFn (bits 8193))).getD C.output false=true at flag
    rw [List.getD_eq_default] at flag
    · contradiction
    · rw [length_wiresFrom,List.length_ofFn]; exact Nat.le_of_not_gt h
  obtain ⟨hp,he⟩ := semantics ao C.output valid
  have gr (x : Fin 26→Bool) : (tree C C.output).eval x=decide (∃ u v, Tree5176.plane.Adj u v ∧ x u=true ∧ x v=true) := by
    rw [he]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (spec' x).trans (graphAccept x)
  have many := markedCopies ao k op live pair quiet valid
  obtain side|side := Tree5176.wholeSide _ (by omega) hp gr
  · have one := side 0
    have upper := copies_unique (pt 0) _ (fun i j hi hj => one.unique hi hj)
    have lower := many 0 (by simp)
    change copies 0 (tree C C.output) ≤ 1 at upper
    omega
  · have one := side 0
    have upper := copies_unique (ln 0) _ (fun i j hi hj => one.unique hi hj)
    have lower := many 13 (by simp)
    change copies 13 (tree C C.output) ≤ 1 at upper
    omega
end Wires5176
