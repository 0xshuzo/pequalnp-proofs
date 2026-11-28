import PEqualNP.Outside.L_meta_10006
namespace Lmeta10008Weighted
open PEqualNP.Outside.L_meta_10006 Finset
open scoped BigOperators

noncomputable def weightedVector (f : V → ℝ) : E := ∑ i, f i • signedRow code i

theorem columnFrame (j : V) (f : V → ℝ)
    (zero : ∀ i, matrix i j=true → f i=0)
    (blank : ∀ i, matrix i j=false → 5≤f i ∧ f i≤11) :
    0 < ‖weightedVector f‖^2 ∧
      11*‖weightedVector f‖^2 ≤ 20*((weightedVector f) j)^2 := by
  let s := ∑ i, f i
  let n (i : V) : ℝ := zeroEntry matrix i j
  have count : ∑ i, n i = 25 := by
    exact_mod_cast (zeroEntry_sum_sq matrix count_table j).1
  have positive (i : V) : 5*n i ≤ f i := by
    cases k : matrix i j with
    | true => simp [n,zeroEntry,k,zero _ k]
    | false => simpa [n,zeroEntry,k] using (blank _ k).1
  have pos : 0 < s := by
    have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset V)) => positive i)
    rw [←mul_sum,count] at h
    dsimp [s]
    linarith
  have single (i : V) : (f i)^2 ≤ 16*f i-55*n i := by
    cases k : matrix i j with
    | true => simp [n,zeroEntry,k,zero _ k]
    | false =>
      obtain ⟨lo,hi⟩ := blank i k
      simp [n,zeroEntry,k]
      nlinarith [mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr hi)]
  have q := sum_le_sum (fun i (_ : i∈(univ : Finset V)) => single i)
  rw [sum_sub_distrib,←mul_sum,←mul_sum,count] at q
  have coeff (i : V) : f i*(code i j : ℝ)=f i := by
    cases k : matrix i j with
    | true => simp [zero i k]
    | false => simp [code,k]
  have coord : (weightedVector f) j=s := by
    unfold weightedVector
    change ev j (∑ i, f i • signedRow code i)=s
    rw [map_sum]
    apply sum_congr rfl
    intro i _
    rw [map_smul, ev_apply, signedRow_apply]
    exact coeff i
  have nz : weightedVector f ≠ 0 := by
    intro eq
    rw [eq] at coord
    change (0 : ℝ) = s at coord
    linarith
  have norm := signed_sum_sq code signedData_original f
  change ‖weightedVector f‖^2 = 125*(∑ i, (f i)^2)-4*s^2 at norm
  refine ⟨by positivity,?_⟩
  rw [coord,norm]
  change (∑ i, (f i)^2) ≤ 16*s - 55*25 at q
  nlinarith [sq_nonneg (8*s-1375)]

theorem weightedRank (K : Submodule ℝ E) (A : V → V → ℝ)
    (mem : ∀ j, weightedVector (fun i => A i j)∈K)
    (zero : ∀ i j, matrix i j=true → A i j=0)
    (blank : ∀ i j, matrix i j=false → 5≤A i j ∧ A i j≤11) :
    18 ≤ Module.finrank ℝ K := by
  have each (j : V) : (11 : ℝ) ≤ 20*(K.starProjection (basisVector j)) j := by
    let f := fun i => A i j
    obtain ⟨pos,cap⟩ := columnFrame j f (fun i => zero i j) (fun i => blank i j)
    have proj := coord_sq_le K j (mem j)
    have h : 11*‖weightedVector f‖^2 ≤ (20*(K.starProjection (basisVector j)) j)*‖weightedVector f‖^2 := by
      change ((weightedVector f) j)^2 ≤ (K.starProjection (basisVector j)) j * ‖weightedVector f‖^2 at proj
      linarith only [cap, mul_le_mul_of_nonneg_left proj (by norm_num : (0 : ℝ) ≤ 20)]
    exact (le_of_mul_le_mul_right h pos)
  have sum := sum_le_sum (fun j (_ : j ∈ (univ : Finset V)) => each j)
  rw [←mul_sum,trace_projection] at sum
  norm_num at sum
  by_contra! no
  have small : (Module.finrank ℝ K : ℝ) ≤ 17 := by exact_mod_cast (show Module.finrank ℝ K ≤ 17 by omega)
  linarith

noncomputable def total {k : Nat} (U : Fin k → V → ℝ) (B : Fin k → V → ℝ)
    (i j : V) := ∑ t, U t i * B t j

theorem weightedFactors {k : Nat} (U B : Fin k → V → ℝ)
    (zero : ∀ i j, matrix i j=true → total U B i j=0)
    (blank : ∀ i j, matrix i j=false → 5≤total U B i j ∧ total U B i j≤11) :
    18 ≤ k := by
  let K := Submodule.span ℝ (Set.range (fun t => weightedVector (U t)))
  have mem (j : V) : weightedVector (fun i => total U B i j) ∈ K := by
    have eq : weightedVector (fun i => total U B i j) = ∑ t, B t j • weightedVector (U t) := by
      unfold weightedVector total
      simp_rw [Finset.sum_smul,Finset.smul_sum,smul_smul]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro i _
      rw [mul_comm]
    rw [eq]
    exact Submodule.sum_mem K (fun t _ => Submodule.smul_mem K _ (Submodule.subset_span (Set.mem_range_self t)))
  have dim : Module.finrank ℝ K ≤ k := by
    simpa [K,Set.finrank] using (finrank_range_le_card (R:=ℝ) (fun t : Fin k => weightedVector (U t)))
  exact (weightedRank K (total U B) mem zero blank).trans dim
end Lmeta10008Weighted
