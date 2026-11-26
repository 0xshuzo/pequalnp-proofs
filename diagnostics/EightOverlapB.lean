import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9345.Rank
open Finset
abbrev V := Fin 21
def board : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def zeroCell (r c : V) : Bool := !((board.getD r.val 0).testBit c.val)
def column (c r : V) : ℚ := if zeroCell r c then 1 else 0
def dual (c r : V) : ℚ := if zeroCell r c then 1 else -3
set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem evaluate : ∀ i j : V, (∑ r : V, dual i r * column j r) =
    if i=j then 16 else 0 := by decide +kernel

theorem independent : LinearIndependent ℚ column := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff rel i
  have coord (r : V) : (∑ j : V, coeff j * column j r)=0 := by
    simpa [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun rel r
  have dot : (∑ r : V, dual i r * (∑ j : V, coeff j * column j r))=0 := by
    simp [coord]
  have swap : (∑ r : V, dual i r * (∑ j : V, coeff j * column j r)) =
      ∑ j : V, coeff j * (∑ r : V, dual i r * column j r) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro r _
    ring
  rw [swap] at dot
  simp_rw [evaluate] at dot
  have atI : (∑ j : V, coeff j * (if i=j then 16 else 0))=coeff i * 16 := by
    rw [sum_eq_single_of_mem i (mem_univ i)]
    · simp
    · intro j _ ne
      simp [Ne.symm ne]
  rw [atI] at dot
  linarith

theorem budget {n m : Nat} (cols : Fin n → V) (distinct : Function.Injective cols)
    (rows : Fin m → Finset V) (used : Fin n → Finset (Fin m))
    (exactly : ∀ j r, (∑ b ∈ used j, (if r∈rows b then (1:ℚ) else 0)) = column (cols j) r) :
    n≤m := by
  classical
  let R (b : Fin m) (r : V) : ℚ := if r∈rows b then 1 else 0
  let W := Submodule.span ℚ (Set.range R)
  have inSpan (j : Fin n) : column (cols j) ∈ W := by
    have eq : column (cols j) = ∑ b ∈ used j, R b := by
      funext r
      simpa only [Finset.sum_apply,R] using (exactly j r).symm
    rw [eq]
    exact Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨b,rfl⟩
  have : Module.Finite ℚ ↥W := Module.Finite.span_of_finite ℚ (Set.finite_range R)
  let lifted (j : Fin n) : ↥W := ⟨column (cols j),inSpan j⟩
  have li : LinearIndependent ℚ lifted := by
    apply LinearIndependent.of_comp W.subtype
    exact independent.comp cols distinct
  have lo : n ≤ Module.finrank ℚ W := by simpa using li.fintype_card_le_finrank
  have hi : Module.finrank ℚ W ≤ m := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range R)) ≤ m
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    simpa only [Fintype.card_fin] using Fintype.card_range_le R
  exact lo.trans hi

theorem sevenNotSix (cols : Fin 7 → V) (distinct : Function.Injective cols)
    (rows : Fin 6 → Finset V) (used : Fin 7 → Finset (Fin 6)) :
    ¬ (∀ j r, (∑ b ∈ used j, (if r∈rows b then (1:ℚ) else 0)) = column (cols j) r) := by
  intro exactCover
  have impossible := budget cols distinct rows used exactCover
  omega
abbrev Box := Finset V × Finset V
def exactColumn {m : Nat} (B : Fin m → Box) (j : V) : Prop :=
  ∀ r : V, (∑ i ∈ (univ.filter (fun i : Fin m => j∈(B i).2)),
    (if r∈(B i).1 then (1:ℚ) else 0)) = column j r
instance {m} (B : Fin m → Box) (j : V) : Decidable (exactColumn B j) := by
  unfold exactColumn
  infer_instance
def exactSet {m} (B : Fin m → Box) := univ.filter (exactColumn B)
theorem exactQuota {m} (B : Fin m → Box) : (exactSet B).card ≤ m := by
  classical
  let T := exactSet B
  let e : ↥T ≃ Fin T.card := Fintype.equivFinOfCardEq (Fintype.card_coe T)
  let c (j : Fin T.card) := (e.symm j).val
  apply budget c (fun i j eq => e.symm.injective (Subtype.ext eq)) (fun i => (B i).1)
    (fun j => univ.filter (fun i : Fin m => c j∈(B i).2))
  intro j r
  have hj : c j∈exactSet B := (e.symm j).property
  exact (Finset.mem_filter.mp hj).2 r
theorem eightNonExact (L : List Box) (small : L.length≤13) :
    8 ≤ ((univ : Finset V) \ exactSet L.get).card := by
  rw [card_sdiff, inter_univ]
  have bound := exactQuota L.get
  have all : (univ : Finset V).card=21 := by decide +kernel
  rw [all]
  omega

end PEqualNP.Outside.L_meta_9345.Rank
