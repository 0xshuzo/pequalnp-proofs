import PEqualNP.Outside.L_meta_10006
namespace Lmeta10008Four
open PEqualNP.Outside.L_meta_10006 Finset
open scoped BigOperators

noncomputable def ct (i j : V) := code j i
noncomputable def weightedVector (f : V → ℝ) : E := ∑ i, f i • signedRow ct i

set_option maxHeartbeats 3000000 in
theorem columnFrame (j : V) (f : V → ℝ)
    (zero : ∀ i, matrix j i=true → f i=0)
    (blank : ∀ i, matrix j i=false → 1≤f i ∧ f i≤2) :
    0 < ‖weightedVector f‖^2 ∧
      8*‖weightedVector f‖^2 ≤ 13*((weightedVector f) j)^2 := by
  let s := ∑ i, f i
  let n (i : V) : ℝ := zeroEntry matrix j i
  have count : ∑ i, n i = 25 := by
    have raw : (∑ i : V, zeroEntry (transposeMatrix matrix) i j) = 25 := (zeroEntry_sum_sq (transposeMatrix matrix) row_counts j).1
    change (∑ i : V, (zeroEntry (transposeMatrix matrix) i j : ℝ)) = 25
    simpa only [Nat.cast_sum,Nat.cast_ofNat] using (congrArg (fun a : Nat => (a : ℝ)) raw)
  have positive (i : V) : 1*n i ≤ f i := by
    cases k : matrix j i with
    | true => simp [n,zeroEntry,transposeMatrix,k,zero _ k]
    | false => simpa [n,zeroEntry,transposeMatrix,k] using (blank _ k).1
  have pos : 0 < s := by
    have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset V)) => positive i)
    rw [←mul_sum,count] at h
    dsimp [s]
    linarith
  have single (i : V) : (f i)^2 ≤ 16*f i-51*n i := by
    cases k : matrix j i with
    | true => simp [n,zeroEntry,transposeMatrix,k,zero _ k]
    | false =>
      obtain ⟨lo,hi⟩ := blank i k
      simp [n,zeroEntry,transposeMatrix,k]
      nlinarith [mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr hi)]
  have q := sum_le_sum (fun i (_ : i∈(univ : Finset V)) => single i)
  rw [sum_sub_distrib,←mul_sum,←mul_sum,count] at q
  have coeff (i : V) : f i*(ct i j : ℝ)=f i := by
    cases k : matrix j i with
    | true => simp [zero i k]
    | false => simp [ct,code,k]
  have coord : (weightedVector f) j=s := by
    unfold weightedVector
    change ev j (∑ i, f i • signedRow ct i)=s
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
  have norm := signed_sum_sq ct signedData_transpose f
  change ‖weightedVector f‖^2 = 125*(∑ i, (f i)^2)-4*s^2 at norm
  refine ⟨by positivity,?_⟩
  rw [coord,norm]
  change (∑ i, (f i)^2) ≤ 3*s - 2*25 at q
  nlinarith [sq_nonneg (3*s-100)]


noncomputable def value {k : Nat} (R : Fin k → Box) (i j : V) (w : Fin k → ℝ) :=
  ∑ t, if i∈(R t).1 ∧ j∈(R t).2 then w t else 0
def easy {k : Nat} (R : Fin k → Box) (i : V) : Prop :=
  ∃ w : Fin k → ℝ, ∀ j, matrix i j=false → 1≤value R i j w ∧ value R i j w≤2

theorem manyHard {k : Nat} (R : Fin k → Box) (budget : k≤17)
    (legal : ∀ t i, i∈(R t).1 → ∀ j, j∈(R t).2 → matrix i j=false) :
    ∃ D : Finset V, 4 ≤ D.card ∧ ∀ i∈D, ¬easy R i := by
  classical
  let Q := univ.filter (easy R)
  let B (t : Fin k) (j : V) : ℝ := if j∈(R t).2 then 1 else 0
  let K := Submodule.span ℝ (Set.range fun t => weightedVector (B t))
  have bound : Module.finrank ℝ K ≤ k := by
    simpa [K,Set.finrank] using (finrank_range_le_card (R:=ℝ) (fun t : Fin k => weightedVector (B t)))
  have price (i : V) (mem : i∈Q) : (8 : ℝ) ≤ 13*(K.starProjection (basisVector i)) i := by
    obtain ⟨w,ok⟩ := (mem_filter.mp mem).2
    let f (j : V) := value R i j w
    have zero (j : V) (h : matrix i j=true) : f j=0 := by
      apply sum_eq_zero
      intro t _
      have no : ¬(i∈(R t).1 ∧ j∈(R t).2) := fun p => Bool.noConfusion (h.symm.trans (legal t _ p.1 _ p.2))
      simp [no]
    have spans : weightedVector f ∈ K := by
      let u (t : Fin k) : ℝ := if i∈(R t).1 then w t else 0
      have eqf (j) : f j=∑ t, u t*B t j := by
        apply sum_congr rfl
        intro t _
        by_cases a : i∈(R t).1 <;> by_cases b : j∈(R t).2 <;> simp [u,B,a,b]
      have eq : weightedVector f=∑ t, u t • weightedVector (B t) := by
        unfold weightedVector
        simp_rw [eqf,Finset.sum_smul,Finset.smul_sum,smul_smul]
        rw [sum_comm]
      rw [eq]
      exact Submodule.sum_mem K (fun t _ => Submodule.smul_mem K _ (Submodule.subset_span (Set.mem_range_self t)))
    obtain ⟨pos,cap⟩ := columnFrame i f zero ok
    have pr := coord_sq_le K i spans
    have h : 8*‖weightedVector f‖^2 ≤ (13*(K.starProjection (basisVector i)) i)*‖weightedVector f‖^2 := by
      linarith only [cap,mul_le_mul_of_nonneg_left pr (by norm_num : (0:ℝ)≤13)]
    exact le_of_mul_le_mul_right h pos
  have diag (i : V) : 0 ≤ (K.starProjection (basisVector i)) i := by
    have h2 := K.starProjection_inner_eq_zero (basisVector i) (K.starProjection (basisVector i)) (K.starProjection_apply_mem _)
    rw [inner_sub_left,sub_eq_zero,real_inner_self_eq_norm_sq,show inner ℝ (basisVector i) (K.starProjection (basisVector i)) = (K.starProjection (basisVector i)) i from basis_inner _ _] at h2
    rw [h2]
    positivity
  have h := sum_le_sum (s:=Q) price
  have sub := sum_le_sum_of_subset_of_nonneg (f:=fun i => 13*(K.starProjection (basisVector i)) i)
    (subset_univ Q) (fun i _ _ => mul_nonneg (by norm_num) (diag i))
  have whole := h.trans sub
  rw [←mul_sum,trace_projection] at whole
  simp only [sum_const,nsmul_eq_mul] at whole
  have exactN : 8*Q.card ≤ 13*Module.finrank ℝ K := by
    exact_mod_cast (by linarith only [whole] : (8:ℝ)*Q.card ≤ 13*Module.finrank ℝ K)
  refine ⟨univ \ Q,?_,?_⟩
  · have size := card_sdiff_add_card_eq_card (subset_univ Q)
    simp only [card_univ,Fintype.card_fin] at size
    omega
  · intro i hi yes
    exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,yes⟩)
end Lmeta10008Four
