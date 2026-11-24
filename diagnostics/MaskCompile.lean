import Mathlib
import PEqualNP.Defs

namespace MaskCompile4684
open PEqualNP.AndCount

lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

lemma fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

lemma gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

theorem compile : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n) (E : Type)
      (D : Set E) (bad : E → Finset (Fin n)),
      (∀ e ∈ D, C.eval (bad e) = false) →
      ∃ G : Fin C.size → Bool → Set E, ∀ U, C.eval U = true →
        ∃ T : Set (Fin C.size),
          let can := fun (j : ℕ) (W : Set E) =>
            (∃ v ∈ U, ∀ e ∈ W, v ∉ bad e) ∨
            ∃ i ∈ T, i.val < j ∧ W ⊆ G i false ∪ G i true
          (∀ i ∈ T, ∀ b, can i.val (G i b)) ∧ can C.size D := by
  intro n C E D bad neg
  classical
  let side (i : Fin C.size) (b : Bool) (u : Finset (Fin n)) : Bool :=
    if b then AndCountCircuit.sideTrue u (C.rightVars i) (C.rightGates i) i (C.gateVal u)
    else AndCountCircuit.sideTrue u (C.leftVars i) (C.leftGates i) i (C.gateVal u)
  let G := fun i b => {e : E | e ∈ D ∧ side i b (bad e) = false}
  have both (i : Fin C.size) (u) : C.gateVal u i = (side i false u && side i true u) := by
    exact gateVal_eq C u i
  have fails (i : Fin C.size) (e : E) (ed : e ∈ D) (h : C.gateVal (bad e) i = false) :
      e ∈ G i false ∪ G i true := by
    rw [both] at h
    cases hf : side i false (bad e) with
    | false => exact Or.inl ⟨ed,hf⟩
    | true => exact Or.inr ⟨ed,by simpa [hf] using h⟩
  refine ⟨G, ?_⟩
  intro U pos
  let T := {i : Fin C.size | C.gateVal U i = true}
  refine ⟨T, ?_, ?_⟩
  · intro i hi b
    change C.gateVal U i = true at hi
    rw [both, Bool.and_eq_true] at hi
    have side_ok (B : Finset (Fin n)) (F : Finset (Fin C.size))
        (h : AndCountCircuit.sideTrue U B F i (C.gateVal U) = true)
        (hz : ∀ e ∈ G i b, AndCountCircuit.sideTrue (bad e) B F i (C.gateVal (bad e)) = false) :
        (∃ v ∈ U, ∀ e ∈ G i b, v ∉ bad e) ∨
          ∃ k ∈ T, k.val < i.val ∧ G i b ⊆ G k false ∪ G k true := by
      rcases of_decide_eq_true h with ⟨v,hv,vu⟩|⟨k,hk,ki,ku⟩
      · refine Or.inl ⟨v,vu,?_⟩
        intro e he vb
        have yes : AndCountCircuit.sideTrue (bad e) B F i (C.gateVal (bad e)) = true :=
          decide_eq_true (Or.inl ⟨v,hv,vb⟩)
        exact Bool.noConfusion ((hz e he).symm.trans yes)
      · refine Or.inr ⟨k,ku,ki,?_⟩
        intro e he
        apply fails k e he.1
        cases kt : C.gateVal (bad e) k with
        | false => rfl
        | true =>
          have yes : AndCountCircuit.sideTrue (bad e) B F i (C.gateVal (bad e)) = true :=
            decide_eq_true (Or.inr ⟨k,hk,ki,kt⟩)
          exact False.elim (Bool.noConfusion ((hz e he).symm.trans yes))
    cases b with
    | false => exact side_ok _ _ hi.1 (fun _ he => he.2)
    | true => exact side_ok _ _ hi.2 (fun _ he => he.2)
  · rcases of_decide_eq_true pos with ⟨v,hv,vu⟩|⟨k,hk,ku⟩
    · refine Or.inl ⟨v,vu,?_⟩
      intro e ed vb
      have yes : C.eval (bad e) = true := decide_eq_true (Or.inl ⟨v,hv,vb⟩)
      exact Bool.noConfusion ((neg e ed).symm.trans yes)
    · refine Or.inr ⟨k,ku,k.isLt,?_⟩
      intro e ed
      apply fails k e ed
      cases h : C.gateVal (bad e) k with
      | false => rfl
      | true =>
        have yes : C.eval (bad e) = true := decide_eq_true (Or.inr ⟨k,hk,h⟩)
        exact False.elim (Bool.noConfusion ((neg e ed).symm.trans yes))

end MaskCompile4684
