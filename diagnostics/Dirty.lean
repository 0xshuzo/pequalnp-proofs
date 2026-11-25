import PEqualNP.Outside.L_meta_2615

namespace Dirty2620

open PEqualNP.Outside.L_meta_2615 PEqualNP.CircuitLowerBounds
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem an_unsound_inner_AND (C : Circuit) (hsize : C.size ≤ 64) (ao : IsAO2 26 C)
    (nd : ∀ (j : ℕ) (g : Gate), C.gates[j]?=some g → g.inputs.Nodup)
    (spec : ∀ x : Fin 26 → Bool, val C x C.output=true ↔ F x)
    (j a b : ℕ) (out : C.output=26+j) (gate : C.gates[j]?=some ⟨.and,[a,b]⟩)
    (coldA : val C (one 13) a=false) (coldB : val C (one 13) b=false) :
    ∃ k < C.gates.length, k≠j ∧ (gateAt C k).op=GateOp.and ∧
      ∃ x : Fin 26 → Bool, val C x (26+k)=true ∧ ¬F x := by
  classical
  by_contra missing
  have clean : CleanHyp C := by
    refine ⟨hsize,ao,nd,spec,?_⟩
    intro k op x hk
    by_cases eq : k=j
    · simpa [out,eq] using hk
    by_cases yes : F x
    · exact (spec x).mpr yes
    have below : k < C.gates.length := by
      by_contra! high
      have bad := val_ge_len C x (26+k) (by omega)
      rw [bad] at hk
      contradiction
    exact False.elim (missing ⟨k,below,eq,op,x,hk,yes⟩)
  have pos : F (pair 0 13) := ⟨0,0,by decide,by decide,by decide⟩
  have on := (spec (pair 0 13)).mpr pos
  rw [out] at on
  exact main_contradiction clean 0 13 j a b gate on (by simp [coldA,coldB])

end Dirty2620
