import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9792.ExitAccounting
/-- In the live cone, every sufficient wire other than the output occupies an
operand slot of a nonproducer sufficient gate or the single sufficient slot
of a bypass gate. This pays for joining all emitted products to one output. -/
theorem charge (s p b : Finset Nat) (out : Nat) (left right exitWire : Nat → Nat)
    (included : p⊆s)
    (live : ∀i∈s,i≠out →
      (∃j∈s \ p, left j=i ∨ right j=i) ∨ (∃j∈b,exitWire j=i)) :
    2*p.card≤s.card+b.card+1 := by
  classical
  let u := s \ p
  have cover : s⊆insert out (u.image left ∪ u.image right ∪ b.image exitWire) := by
    intro i hi
    by_cases eq : i=out
    · exact Finset.mem_insert.mpr (Or.inl eq)
    · apply Finset.mem_insert.mpr
      apply Or.inr
      rcases live i hi eq with ⟨j,hj,h|h⟩|⟨j,hj,h⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,hj,h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,h⟩)
  have a := Finset.card_le_card cover
  have b₁ := Finset.card_insert_le out (u.image left ∪ u.image right ∪ b.image exitWire)
  have b₂ := Finset.card_union_le (u.image left ∪ u.image right) (b.image exitWire)
  have b₃ := Finset.card_union_le (u.image left) (u.image right)
  have c₁ : (u.image left).card≤u.card := Finset.card_image_le
  have c₂ : (u.image right).card≤u.card := Finset.card_image_le
  have c₃ : (b.image exitWire).card≤b.card := Finset.card_image_le
  have d : u.card+p.card=s.card := Finset.card_sdiff_add_card_eq_card included
  omega
end PEqualNP.Outside.L_meta_9792.ExitAccounting
