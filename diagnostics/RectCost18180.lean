import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18180
open Finset
theorem rectangle_price (n m : Nat) (E : Finset (Fin n × Fin m)) (k : Nat)
    (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))
    (linear : ∀ a b i j, a≠b → i≠j → ¬ ((a,i)∈E ∧ (a,j)∈E ∧ (b,i)∈E ∧ (b,j)∈E))
    (positive : ∀ i, (A i).Nonempty ∧ (B i).Nonempty)
    (valid : ∀ i, ∀ p∈A i, ∀ l∈B i, (p,l)∈E)
    (cover : ∀ e∈E, ∃ i, e.1∈A i ∧ e.2∈B i) :
    ∃ P : Finset (Fin n), ∃ Q : Finset (Fin m),
      (∀ e∈E,e.1∈P ∨ e.2∈Q) ∧ E.card+P.card+Q.card≤∑ i, ((A i).card+(B i).card) := by
  classical
  have small (i) : (A i).card=1 ∨ (B i).card=1 := by
    by_contra! h
    have hA : ¬ ∀ x∈A i, ∀ y∈A i, x=y := by
      intro all
      have one := Finset.card_le_one.mpr all
      have pos := Finset.card_pos.mpr (positive i).1
      omega
    have hB : ¬ ∀ x∈B i, ∀ y∈B i, x=y := by
      intro all
      have one := Finset.card_le_one.mpr all
      have pos := Finset.card_pos.mpr (positive i).2
      omega
    push_neg at hA hB
    obtain ⟨p,hp,q,hq,pq⟩ := hA
    obtain ⟨s,hs,t,ht,st⟩ := hB
    exact linear p q s t pq st ⟨valid i p hp s hs,valid i p hp t ht,valid i q hq s hs,valid i q hq t ht⟩
  let X := fun i => if (A i).card=1 then A i else ∅
  let Y := fun i => if (A i).card=1 then ∅ else B i
  let box := fun i => (A i) ×ˢ (B i)
  have sub : E⊆univ.biUnion box := by
    intro e he
    obtain ⟨i,hi,hj⟩ := cover e he
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_product.mpr ⟨hi,hj⟩⟩
  have bounds : E.card≤∑ i, (box i).card :=
    (card_le_card sub).trans (card_biUnion_le _ _)
  have cx := card_biUnion_le (univ : Finset (Fin k)) X
  have cy := card_biUnion_le (univ : Finset (Fin k)) Y
  have sum : (∑ i, (box i).card)+(∑ i, (X i).card)+(∑ i, (Y i).card)
      = ∑ i, ((A i).card+(B i).card) := by
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (A i).card=1
    · simp [box,X,Y,h,Nat.add_comm]
    · have hh := (small i).resolve_left h
      simp [box,X,Y,h,hh]
  refine ⟨univ.biUnion X,univ.biUnion Y,?_,by omega⟩
  intro e he
  obtain ⟨i,hi,hj⟩ := cover e he
  by_cases h : (A i).card=1
  · exact Or.inl (mem_biUnion.mpr ⟨i,mem_univ _,by simpa [X,h] using hi⟩)
  · exact Or.inr (mem_biUnion.mpr ⟨i,mem_univ _,by simpa [Y,h] using hj⟩)
end PEqualNP.Outside.L_meta_18180
