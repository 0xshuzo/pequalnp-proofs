import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_26031_aux
open Module
section Sol
local notation "𝔽" => ZMod 2
variable {K : Type} [Field K] [Algebra 𝔽 K] {g : ℕ}

private lemma nonzero_one {x : 𝔽} (h : x ≠ 0) : x = 1 := by
  fin_cases x <;> first | rfl | contradiction

private noncomputable def correction (bit : K →ₗ[𝔽] 𝔽) (d : Fin g → K) (S : Finset (Fin g)) :
    K →ₗ[𝔽] K := ∑ i ∈ S, (bit.comp (LinearMap.mulLeft 𝔽 (d i))).smulRight (d i)

private lemma correction_apply (bit : K →ₗ[𝔽] 𝔽) (d : Fin g → K) (S : Finset (Fin g)) (x : K) :
    correction bit d S x = ∑ i ∈ S, bit (d i * x) • d i := by
  simp [correction]

private theorem singularChoice (bit : K →ₗ[𝔽] 𝔽) (d : Fin g → K) (z : K) (hz : z ≠ 0)
    (interaction : ∃ i j, bit (z⁻¹*d i*d j) ≠ 0) :
    ∃ S : Finset (Fin g), S.card ≤ 2 ∧ ∃ x : K, x ≠ 0 ∧
      (correction bit d S + LinearMap.mulLeft 𝔽 z) x = 0 := by
  classical
  have zz : z*z⁻¹=1 := mul_inv_cancel₀ hz
  have double (x : K) : x+x=0 := by
    have h : (1:𝔽)+(1:𝔽)=0 := by decide
    calc x+x = ((1:𝔽)+1) • x := by rw [add_smul,one_smul]
         _ = 0 := by rw [h,zero_smul]
  by_cases diag : ∃ i, bit (z⁻¹*d i*d i) ≠ 0
  · obtain ⟨i,hi⟩ := diag
    have hd : d i ≠ 0 := by intro h; simp [h] at hi
    have ht : bit (d i*(z⁻¹*d i))=1 := by
      convert nonzero_one hi using 2 <;> ring
    refine ⟨{i},by simp, z⁻¹*d i,mul_ne_zero (inv_ne_zero hz) hd,?_⟩
    simp only [LinearMap.add_apply,correction_apply,Finset.sum_singleton,ht,one_smul,
      LinearMap.mulLeft_apply]
    rw [←mul_assoc,zz,one_mul,double]
  · obtain ⟨i,j,hij⟩ := interaction
    have diag0 (l : Fin g) : bit (z⁻¹*d l*d l)=0 := by
      by_contra hh
      exact diag ⟨l,hh⟩
    have hne : i ≠ j := fun h => hij (h ▸ diag0 j)
    have cross := nonzero_one hij
    let w := z⁻¹*(d i+d j)
    have i1 : bit (d i*w) = 1 := by
      rw [show d i*w = z⁻¹*d i*d i + z⁻¹*d i*d j by dsimp [w]; ring,map_add,diag0,cross,zero_add]
    have j1 : bit (d j*w) = 1 := by
      rw [show d j*w = z⁻¹*d i*d j + z⁻¹*d j*d j by dsimp [w]; ring,map_add,diag0,cross,add_zero]
    have hW : w ≠ 0 := by intro h; simp [h] at i1
    refine ⟨{i,j},by simp [hne],w,hW,?_⟩
    simp only [LinearMap.add_apply,correction_apply,Finset.mem_singleton,Finset.sum_insert
      (show i ∉ ({j}:Finset _) by simpa using hne),Finset.sum_singleton,i1,j1,one_smul,LinearMap.mulLeft_apply]
    change d i + d j + z*(z⁻¹*(d i+d j)) = 0
    rw [←mul_assoc z,zz,one_mul,double]

end Sol

end PEqualNP.Outside.L_meta_26031_aux
