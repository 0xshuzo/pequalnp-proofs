import Mathlib
import PEqualNP.Outside.L_meta_1483

namespace Profile9774
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1483

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

/-- Every first branch for a vertex agrees with that vertex on every maximal negative row. -/
theorem first_on_negative (hC : Monotone2 C) (he : GraphEval C G)
    (v : Fin n) (hv : Eligible C v) (M : Finset (Fin n))
    (indep : ∀ i∈M,∀ j∈M,¬G.Adj i j)
    (maxi : ∀ i, i∉M → ∃ j∈M,G.Adj i j) :
    val C (point M) (firstBranch C v hv) = point M v := by
  let b := firstBranch C v hv
  have born : val C (point {v}) b = true := (carries_iff hC).mp (firstBranch_spec v hv).2.1 |>.1
  by_cases hi : v∈M
  · have sub : ({v} : Finset (Fin n)) ⊆ M := Finset.singleton_subset_iff.mpr hi
    have bit := acts_mono hC (point_mono sub) b born
    simpa [point,hi,b] using bit
  · have quiet : val C (point M) C.output ≠ true := by
      rintro h
      obtain ⟨i,hi,j,hj,e⟩ := (edge_of_point he).mp h
      exact indep i hi j hj e
    obtain ⟨j,hj,e⟩ := maxi v hi
    have loud : val C (point (insert v M)) C.output = true :=
      (edge_of_point he).mpr ⟨v,Finset.mem_insert_self v M,j,Finset.mem_insert_of_mem hj,e⟩
    have sub : ({v} : Finset (Fin n)) ⊆ insert v M := by simp
    have on := acts_mono hC (point_mono sub) b born
    have off : val C (point M) b = false := by
      cases hx : val C (point M) b with
      | false => rfl
      | true =>
        have hout := value_at_branch hv (fun i hi => (point_insert hi).symm)
          (x:=point M) (y:=point (insert v M)) (hx.trans on.symm)
        exact (quiet (hout.trans loud)).elim
    simpa [point,hi,b] using off
end Profile9774
