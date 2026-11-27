import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18611
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
theorem planeLeaves (φ : DMFormula 26)
    (positive : DMFormula.rec (motive := fun _ : DMFormula 26 => Prop)
      (fun (_ : Fin 26) (c : Bool) => c=true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ)
    (spec : ∀ x, φ.eval x=decide (∃ u v, plane.Adj u v ∧ x u=true ∧ x v=true)) :
    65 ≤ φ.leaves := by
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
  omega

inductive Cut where
  | raw (i : Fin 26)
  | port
  | meet (a b : Cut)
  | join (a b : Cut)

def Cut.eval (t : Cut) (x : Fin 26 → Bool) (h : Bool) : Bool :=
  match t with
  | .raw i => x i
  | .port => h
  | .meet a b => a.eval x h && b.eval x h
  | .join a b => a.eval x h || b.eval x h

def Cut.rawCount : Cut → ℕ
  | .raw _ => 1
  | .port => 0
  | .meet a b | .join a b => a.rawCount+b.rawCount

theorem Cut.mono (t : Cut) {x y : Fin 26 → Bool} {h k : Bool}
    (hin : ∀ i, x i=true → y i=true) (port : h=true → k=true) :
    t.eval x h=true → t.eval y k=true := by
  induction t with
  | raw i => exact hin i
  | port => exact port
  | meet a b ha hb =>
    simp only [Cut.eval,Bool.and_eq_true] at *
    exact fun h => ⟨ha h.1,hb h.2⟩
  | join a b ha hb =>
    simp only [Cut.eval,Bool.or_eq_true] at *
    exact fun h => h.elim (fun u => Or.inl (ha u)) (fun u => Or.inr (hb u))

abbrev Positive (φ : DMFormula 26) : Prop :=
  DMFormula.rec (motive := fun _ : DMFormula 26 => Prop)
    (fun (_ : Fin 26) (c : Bool) => c=true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

theorem Cut.zeroFormula (t : Cut) :
    (∀ x, t.eval x false=false) ∨
    (∃ φ : DMFormula 26, Positive φ ∧ φ.leaves ≤ t.rawCount ∧ ∀ x, φ.eval x=t.eval x false) := by
  induction t with
  | raw i => exact .inr ⟨.lit i true,rfl,by rfl,fun _ => rfl⟩
  | port => exact .inl (fun _ => rfl)
  | meet a b ha hb =>
    rcases ha with za | ⟨f,pf,cf,ef⟩
    · exact .inl (fun x => by simp [Cut.eval,za x])
    rcases hb with zb | ⟨g,pg,cg,eg⟩
    · exact .inl (fun x => by simp [Cut.eval,zb x])
    exact .inr ⟨.and f g,⟨pf,pg⟩,Nat.add_le_add cf cg,fun x => by simp only [DMFormula.eval,Cut.eval,ef,eg]⟩
  | join a b ha hb =>
    rcases ha with za | ⟨f,pf,cf,ef⟩ <;> rcases hb with zb | ⟨g,pg,cg,eg⟩
    · exact .inl (fun x => by simp [Cut.eval,za x,zb x])
    · exact .inr ⟨g,pg,by change _ ≤ a.rawCount+b.rawCount; omega,fun x => by simp [Cut.eval,za x,eg]⟩
    · exact .inr ⟨f,pf,by change _ ≤ a.rawCount+b.rawCount; omega,fun x => by simp [Cut.eval,zb x,ef]⟩
    · exact .inr ⟨.or f g,⟨pf,pg⟩,Nat.add_le_add cf cg,fun x => by simp only [DMFormula.eval,Cut.eval,ef,eg]⟩

def row (a b : Fin 26) (i : Fin 26) : Bool := decide (i=a ∨ i=b)

def flagFun (x : Fin 26 → Bool) : Bool := decide (∃ i j, plane.Adj i j ∧ x i=true ∧ x j=true)

theorem oneFlagRaw (t : Cut) (H : (Fin 26 → Bool) → Bool) (u v : Fin 26)
    (edgeUV : plane.Adj u v) (spec : ∀ x, t.eval x (H x)=flagFun x)
    (single : ∀ a b, plane.Adj a b → H (row a b)=true → (a=u ∧ b=v) ∨ (a=v ∧ b=u)) :
    65 ≤ t.rawCount+2 := by
  have recover (x : Fin 26 → Bool) : t.eval x false || (x u && x v) = flagFun x := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,Bool.and_eq_true,flagFun,decide_eq_true_eq]
    constructor
    · rintro (h|⟨l,r⟩)
      · have z := t.mono (x:=x) (y:=x) (h:=false) (k:=H x) (fun _ hi => hi) (by simp) h
        simpa only [spec,flagFun,decide_eq_true_eq] using z
      · exact ⟨u,v,edgeUV,l,r⟩
    · rintro ⟨a,b,ab,xa,xb⟩
      by_cases hp : H (row a b)=true
      · right
        rcases single a b ab hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨xa,xb⟩
        · exact ⟨xb,xa⟩
      · left
        have hf : H (row a b)=false := by cases h : H (row a b) <;> simp_all
        have good : flagFun (row a b)=true := by
          apply decide_eq_true
          exact ⟨a,b,ab,by simp [row],by simp [row]⟩
        have atRow := (spec (row a b)).trans good
        rw [hf] at atRow
        apply t.mono (x:=row a b) (h:=false) (k:=false) _ (fun z => z) atRow
        intro i hi
        rcases (of_decide_eq_true hi : i=a ∨ i=b) with rfl|rfl
        · exact xa
        · exact xb
  let e : DMFormula 26 := .and (.lit u true) (.lit v true)
  have epos : Positive e := ⟨rfl,rfl⟩
  rcases t.zeroFormula with zero | ⟨f,pf,cf,ef⟩
  · have specE (x : Fin 26 → Bool) : e.eval x = flagFun x := by
      simpa [e,DMFormula.eval,zero x] using recover x
    have lb := planeLeaves e epos specE
    change 65 ≤ 2 at lb
    omega
  · have full (x : Fin 26 → Bool) : (DMFormula.or f e).eval x = flagFun x := by
      simpa only [DMFormula.eval,e,if_true,ef] using recover x
    have lb := planeLeaves (.or f e) ⟨pf,epos⟩ full
    change 65 ≤ f.leaves+2 at lb
    omega

end Tree5176
end PEqualNP.Outside.L_meta_18611
