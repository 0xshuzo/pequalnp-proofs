import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3568

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def cutSlots (C : Circuit) (z : Nat) (A : Finset Nat) (j : Nat) :=
  if j ∈ A then (gateAt C j).inputs.toFinset.erase z else (gateAt C j).inputs.toFinset

def cutBank (C : Circuit) (z : Nat) (A P : Finset Nat) :=
  (P ∪ A).biUnion (cutSlots C z A)

theorem cut_capacity (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (z : Fin n) (A P : Finset Nat) (apart : Disjoint P A)
    (indices : ∀ j ∈ P ∪ A, j < C.gates.length)
    (read : ∀ j ∈ A, z.val ∈ (gateAt C j).inputs)
    (live : ∀ j ∈ P, n+j ∈ cutBank C z.val A P) :
    ((cutBank C z.val A P) \ P.image (fun j => n+j)).card ≤ P.card + A.card := by
  classical
  let slots := cutSlots C z.val A
  let bank := cutBank C z.val A P
  let ints := P.image (fun j => n+j)
  have two (j) (hj : j ∈ P ∪ A) : (gateAt C j).inputs.toFinset.card ≤ 2 := by
    refine (List.toFinset_card_le _).trans ?_
    apply Nat.le_of_eq
    apply hAO.2.2
    unfold gateAt
    rw [List.getD_eq_getElem _ _ (indices j hj)]
    apply List.getElem_mem
  have sp : ∑ j ∈ P, (slots j).card ≤ 2*P.card := by
    calc
      _ ≤ ∑ _j ∈ P, 2 := Finset.sum_le_sum fun j hj => by
        have no : j ∉ A := Finset.disjoint_left.mp apart hj
        simpa [slots,cutSlots,no] using two j (Finset.mem_union_left _ hj)
      _ = _ := by simp [Nat.mul_comm]
  have sa : ∑ j ∈ A, (slots j).card ≤ A.card := by
    calc
      _ ≤ ∑ _j ∈ A, 1 := Finset.sum_le_sum fun j hj => by
        have hz : z.val ∈ (gateAt C j).inputs.toFinset := by simpa using read j hj
        have lo := Finset.card_erase_add_one hz
        have hi := two j (Finset.mem_union_right _ hj)
        simp only [slots,cutSlots,if_pos hj]
        omega
      _ = _ := by simp
  have total : bank.card ≤ 2*P.card+A.card := by
    calc
      bank.card ≤ ∑ j ∈ (P ∪ A), (slots j).card := Finset.card_biUnion_le
      _ = _ := Finset.sum_union apart
      _ ≤ _ := Nat.add_le_add sp sa
  have sub : ints ⊆ bank := by
    intro t ht
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
    exact live j hj
  have sz : ints.card=P.card := Finset.card_image_of_injective _ (by intro i j eq; omega)
  have decomp := Finset.card_sdiff_add_card_eq_card sub
  change (bank \ ints).card ≤ P.card + A.card
  omega

theorem singleton_capacity {U W : Type*} [DecidableEq U] [DecidableEq W]
    (N : Finset U) (B : Finset W) (trace : W → Finset U)
    (cover : N ⊆ B.biUnion trace) (unit : ∀ w ∈ B, (trace w).card ≤ 1) : N.card ≤ B.card := by
  calc
    N.card ≤ (B.biUnion trace).card := Finset.card_le_card cover
    _ ≤ ∑ w ∈ B, (trace w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ B, 1 := Finset.sum_le_sum unit
    _ = B.card := by simp

end PEqualNP.Outside.L_meta_3568
