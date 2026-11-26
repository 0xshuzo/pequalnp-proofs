import Mathlib
import PEqualNP.Defs

namespace PetersenSplitStar
def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(0,4),(3,4),(0,5),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8),(4,9),(6,9),(7,9)]
def edge (e : Fin 15) : Fin 10 × Fin 10 := edges[e.val]'(by simpa [edges] using e.isLt)
def covers (S : Finset (Fin 10)) (e : Fin 15) : Prop := (edge e).1 ∈ S ∨ (edge e).2 ∈ S
instance (S : Finset (Fin 10)) (e : Fin 15) : Decidable (covers S e) := by unfold covers; infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem minimumCover (S : Finset (Fin 10)) (h : ∀ e, covers S e) : 6 ≤ S.card := by
  exact (by decide +kernel : ∀ S : Finset (Fin 10), (∀ e, covers S e) → 6 ≤ S.card) S h

-- A direct star with k assigned spokes uses k gates. The final union of s disjoint
-- gate lists uses s - 1 more gates. Each side therefore costs |edges| + |centers| - 1.
theorem splitPrice (q f : Finset (Fin 15)) (cq cf : Finset (Fin 10))
    (allEdges : q ∪ f = Finset.univ)
    (hq : ∀ e ∈ q, covers cq e) (hf : ∀ e ∈ f, covers cf e) :
    19 ≤ (q.card + cq.card - 1) + (f.card + cf.card - 1) := by
  have hc : ∀ e, covers (cq ∪ cf) e := by
    intro e
    have he : e ∈ q ∪ f := by rw [allEdges]; exact Finset.mem_univ e
    rcases Finset.mem_union.mp he with h|h
    · rcases hq e h with a|b
      · exact Or.inl (Finset.mem_union_left cf a)
      · exact Or.inr (Finset.mem_union_left cf b)
    · rcases hf e h with a|b
      · exact Or.inl (Finset.mem_union_right cq a)
      · exact Or.inr (Finset.mem_union_right cq b)
  have m := minimumCover (cq ∪ cf) hc
  have c := Finset.card_union_le cq cf
  have d := Finset.card_union_le q f
  rw [allEdges] at d
  simp only [Finset.card_univ, Fintype.card_fin] at d
  omega
end PetersenSplitStar
