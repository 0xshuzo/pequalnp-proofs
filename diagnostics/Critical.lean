import Mathlib
import PEqualNP.Outside.L_meta_1485
import PEqualNP.Outside.L_meta_5242

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_5242
namespace Critical1768
open PEqualNP.Outside.L_meta_1485
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem critical (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (b : Fin 2) :
    ∃ S : Finset (Fin n), GraphSupport.bad G S ∧
      (∀ T : Finset (Fin n), S ⊆ T → GraphSupport.bad G T → T = S) ∧
      circuitFun n (bypass n C j (opnd C j b)) (GraphSupport.input S) = true ∧
      val C (List.ofFn (GraphSupport.input S)) (opnd C j b) = true ∧
      val C (List.ofFn (GraphSupport.input S)) (opnd C j (1-b)) = false := by
  classical
  let i := opnd C j b
  let D := bypass n C j i
  have hi : i < n+j := Structural.opnd_lt hL.1 hj b
  have hD : IsAO2 n D := isAO2_bypass hL.1 hi
  have hAO (k) (hk : k < C.gates.length) := hL.1.1 _ (Base.gateAt_mem hk)
  have gateBound (x : Fin n → Bool) : val C (List.ofFn x) (n+j) = true → val C (List.ofFn x) i = true :=
    fun h => (Structural.and_true_iff hL.1 hj hand x).mp h b
  have lift (x : Fin n → Bool) : circuitFun n C x = true → circuitFun n D x = true :=
    bypass_eval_rel (R := fun a b => a = true → b = true) (fun _ => id) opMono_imp
      (by simp) hAO hj (Or.inl hi) (gateBound x)
  have fail : circuitFun n D ≠ graphFun G ∅ := by
    intro h
    have wrong := hL.2.2 D hD h
    have sz := bypass_length n C j i
    change C.gates.length ≤ (bypass n C j i).gates.length at wrong
    omega
  obtain ⟨x,hx⟩ : ∃ x, circuitFun n D x ≠ graphFun G ∅ x := by
    by_contra! same
    exact fail (funext same)
  have up : graphFun G ∅ x = true → circuitFun n D x = true := hL.2.1 ▸ lift x
  have off : graphFun G ∅ x = false := Bool.eq_false_iff.mpr (fun h => hx ((up h).trans h.symm))
  have on : circuitFun n D x = true := by cases hh : circuitFun n D x <;> simp_all
  let source := GraphSupport.support x
  let pool := (Finset.univ : Finset (Finset (Fin n))).filter (fun s => source ⊆ s ∧ GraphSupport.bad G s)
  have start : source ∈ pool := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.Subset.rfl,by
    simpa only [source,GraphSupport.bad,GraphSupport.input_support] using off⟩
  obtain ⟨S,hs,hmax⟩ := pool.exists_max_image Finset.card ⟨_,start⟩
  obtain ⟨hsub,hbad⟩ := (Finset.mem_filter.mp hs).2
  let y := GraphSupport.input S
  have hon : circuitFun n D y = true := by
    apply Structural.wire_mono hD x y _ D.output on
    intro z hz
    exact decide_eq_true (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩))
  have reject : circuitFun n C y = false := by rw [hL.2.1]; exact hbad
  have diff : val C (List.ofFn y) (n+j) ≠ val C (List.ofFn y) i := by
    intro same
    have out := bypass_eval_eq (by simp) hAO hj (Or.inl hi) same
    change circuitFun n D y = circuitFun n C y at out
    rw [hon,reject] at out
    contradiction
  have gateoff : val C (List.ofFn y) (n+j) ≠ true := fun h => diff (h.trans (gateBound y h).symm)
  have inputon : val C (List.ofFn y) i = true := by
    cases hw : val C (List.ofFn y) i
    · exact (diff ((Bool.eq_false_iff.mpr gateoff).trans hw.symm)).elim
    · rfl
  have other : val C (List.ofFn y) (opnd C j (1-b)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hother
    apply gateoff
    apply (Structural.and_true_iff hL.1 hj hand y).mpr
    intro d
    rcases Final.two_cases b d with e | e
    · simpa only [e] using inputon
    · simpa only [e] using hother
  refine ⟨S,hbad,?_,hon,inputon,other⟩
  intro T hST hb
  exact (Finset.eq_of_subset_of_card_le hST
    (hmax T (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub.trans hST,hb⟩))).symm

end Critical1768
