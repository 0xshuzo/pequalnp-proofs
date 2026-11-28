import PEqualNP.Outside.L_meta_10006
namespace Lmeta10008Weighted
open PEqualNP.Outside.L_meta_10006 Finset
open scoped BigOperators

noncomputable def weightedVector (f : V → ℝ) : E := ∑ i, f i • signedRow code i

set_option maxHeartbeats 3000000 in
theorem columnFrame (j : V) (f : V → ℝ)
    (zero : ∀ i, matrix i j=true → f i=0)
    (blank : ∀ i, matrix i j=false → 5≤f i ∧ f i≤11) :
    0 < ‖weightedVector f‖^2 ∧
      11*‖weightedVector f‖^2 ≤ 20*((weightedVector f) j)^2 := by
  let s := ∑ i, f i
  let n (i : V) : ℝ := zeroEntry matrix i j
  have count : ∑ i, n i = 25 := by
    have raw : (∑ i : V, zeroEntry matrix i j) = 25 := (zeroEntry_sum_sq matrix count_table j).1
    change (∑ i : V, (zeroEntry matrix i j : ℝ)) = 25
    simpa only [Nat.cast_sum,Nat.cast_ofNat] using (congrArg (fun a : Nat => (a : ℝ)) raw)
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
namespace Lmeta10008Weighted
open PEqualNP.Outside.L_meta_10006 Finset
open scoped BigOperators
noncomputable def localValue {k : Nat} (R : Fin k → Box) (i j : V) (w : Fin k → ℝ) :=
  ∑ t, if i∈(R t).1 ∧ j∈(R t).2 then w t else 0

theorem badRow {k : Nat} (R : Fin k → Box) (budget : k≤17)
    (good : ∀ t i, i∈(R t).1 → ∀ j, j∈(R t).2 → matrix i j=false) :
    ∃ i : V, ∀ w : Fin k → ℝ, ∃ j : V, matrix i j=false ∧
      (localValue R i j w < 5 ∨ 11 < localValue R i j w) := by
  classical
  by_contra! no
  choose weight fits using no
  let U (t : Fin k) (i : V) : ℝ := if i∈(R t).1 then weight i t else 0
  let B (t : Fin k) (j : V) : ℝ := if j∈(R t).2 then 1 else 0
  have eq (i j : V) : total U B i j=localValue R i j (weight i) := by
    apply sum_congr rfl
    intro t _
    by_cases l : i∈(R t).1 <;> by_cases r : j∈(R t).2 <;> simp [U,B,l,r]
  have zero (i j : V) (h : matrix i j=true) : total U B i j=0 := by
    rw [eq,localValue]
    apply sum_eq_zero
    intro t _
    have miss : ¬(i∈(R t).1 ∧ j∈(R t).2) := fun q => Bool.noConfusion (h.symm.trans (good t _ q.1 _ q.2))
    simp [miss]
  have blank (i j : V) (h : matrix i j=false) : 5 ≤ total U B i j ∧ total U B i j ≤ 11 := by
    rw [eq]
    exact fits i j h
  have bound := weightedFactors U B zero blank
  omega

theorem tripleEverySubcover {k : Nat} (R : Fin k → Box) (budget : k≤17)
    (good : ∀ t i, i∈(R t).1 → ∀ j, j∈(R t).2 → matrix i j=false) :
    ∃ i : V, ∀ T : Finset (Fin k),
      (∀ j, matrix i j=false → ∃ t∈T, i∈(R t).1 ∧ j∈(R t).2) →
      ∃ j : V, matrix i j=false ∧ 3≤(T.filter fun t => i∈(R t).1 ∧ j∈(R t).2).card := by
  classical
  obtain ⟨i,failure⟩ := badRow R budget good
  refine ⟨i,?_⟩
  intro T cover
  let w (t : Fin k) : ℝ := if t∈T then 5 else 0
  obtain ⟨j,hj,fail⟩ := failure w
  let A := T.filter (fun t => i∈(R t).1 ∧ j∈(R t).2)
  obtain ⟨t,mem,both⟩ := cover j hj
  have non : 0 < A.card := card_pos.mpr ⟨t,mem_filter.mpr ⟨mem,both⟩⟩
  have sum : localValue R i j w = 5*(A.card : ℝ) := by
    calc
      localValue R i j w = ∑ t : Fin k, if t∈A then (5 : ℝ) else 0 := by
        apply sum_congr rfl
        intro t _
        by_cases inc : t∈T <;> by_cases ok : i∈(R t).1 ∧ j∈(R t).2 <;> simp [A,w,inc,ok]
      _ = 5*(A.card : ℝ) := by simp [←Finset.sum_filter,mul_comm]
  refine ⟨j,hj,?_⟩
  change 3≤A.card
  rw [sum] at fail
  by_contra! small
  have lo : (1 : ℝ) ≤ A.card := by exact_mod_cast non
  have hi : (A.card : ℝ) ≤ 2 := by exact_mod_cast (show A.card ≤2 by omega)
  rcases fail with under|over <;> linarith
end Lmeta10008Weighted
namespace Lmeta10008Weighted
open PEqualNP.Outside.L_meta_10006 Finset
def hits {k : Nat} (R : Fin k → Box) (i j : V) (t : Fin k) := i∈(R t).1 ∧ j∈(R t).2
def serves {k : Nat} (R : Fin k → Box) (i : V) (T : Finset (Fin k)) :=
  ∀ j, matrix i j=false → ∃ t∈T, hits R i j t

theorem anchor {k : Nat} (R : Fin k → Box) (budget : k≤17)
    (good : ∀ t i, i∈(R t).1 → ∀ j, j∈(R t).2 → matrix i j=false)
    (cover : ∀ i j, matrix i j=false → ∃ t, hits R i j t) :
    ∃ i j : V, ∃ slots : Fin 3 → Fin k, ∃ privateCol : Fin 3 → V,
       Function.Injective slots ∧ Function.Injective privateCol ∧ matrix i j=false ∧
       (∀ a, hits R i j (slots a)) ∧
       (∀ a, privateCol a≠j ∧ matrix i (privateCol a)=false) ∧
       ∀ a b, privateCol b∈(R (slots a)).2 ↔ a=b := by
  classical
  obtain ⟨i,hard⟩ := tripleEverySubcover R budget good
  have ex : ∃ n : Nat, ∃ T : Finset (Fin k), serves R i T ∧ T.card=n := by
    refine ⟨_,univ,?_,rfl⟩
    intro j hj
    obtain ⟨t,ht⟩ := cover i j hj
    exact ⟨t,mem_univ _,ht⟩
  obtain ⟨T,ok,size⟩ := Nat.find_spec ex
  have witness (t : Fin k) (inT : t∈T) : ∃ c : V, matrix i c=false ∧ hits R i c t ∧
      ∀ u∈T, hits R i c u → u=t := by
    have no : ¬serves R i (T.erase t) := by
      intro yes
      apply Nat.find_min ex (m := (T.erase t).card)
        (by rw [card_erase_of_mem inT]; have pos := card_pos.mpr ⟨t,inT⟩; omega)
      exact ⟨T.erase t,yes,rfl⟩
    unfold serves at no
    push_neg at no
    obtain ⟨c,hc,sole⟩ := no
    obtain ⟨u,hu,hit⟩ := ok c hc
    have eqn (v) (hv : v∈T) (hh : hits R i c v) : v=t := by
      by_contra ne
      exact sole v (mem_erase.mpr ⟨ne,hv⟩) hh
    exact ⟨c,hc,(eqn u hu hit) ▸ hit,eqn⟩
  obtain ⟨j,hj,many⟩ := hard T ok
  let pool := T.filter (fun t => i∈(R t).1 ∧ j∈(R t).2)
  let select (a : Fin 3) : pool := pool.orderIsoOfFin rfl (Fin.castLE many a)
  let slots (a : Fin 3) : Fin k := (select a).val
  have si : Function.Injective slots := Subtype.val_injective.comp
    ((pool.orderIsoOfFin rfl).injective.comp (Fin.castLE_injective many))
  have picked (a : Fin 3) : slots a∈T ∧ hits R i j (slots a) := mem_filter.mp (select a).property
  choose col cs using fun a => witness (slots a) (picked a).1
  have inc (a b : Fin 3) : col b∈(R (slots a)).2 ↔ a=b := by
    constructor
    · intro cell
      exact si ((cs b).2.2 _ (picked a).1 ⟨(picked a).2.1,cell⟩)
    · rintro rfl
      exact (cs a).2.1.2
  refine ⟨i,j,slots,col,si,?_,hj,fun a => (picked a).2,?_,inc⟩
  · intro a b eb
    exact (inc a b).mp (eb ▸ (cs a).2.1.2)
  · intro a
    refine ⟨?_,(cs a).1⟩
    intro he
    have all (b : Fin 3) : b=a := (inc b a).mp (he.symm ▸ (picked b).2.2)
    have absurd : (0 : Fin 3)=1 := (all 0).trans (all 1).symm
    exact (by decide : (0 : Fin 3)≠1) absurd
end Lmeta10008Weighted
