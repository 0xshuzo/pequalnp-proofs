import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33669
open Finset
variable {E : Type} [DecidableEq E]
theorem alt_sum (W : Finset E) :
    W.powerset.sum (fun V => (-1 : ℤ) ^ (W.card - V.card)) = if W = ∅ then 1 else 0 := by
  have h : ∀ V ∈ W.powerset, (-1 : ℤ) ^ (W.card - V.card) = (-1) ^ W.card * (-1) ^ V.card := by
    intro V hV
    have hle : V.card ≤ W.card := card_le_card (mem_powerset.mp hV)
    have e : (-1 : ℤ) ^ W.card = (-1) ^ (W.card - V.card) * (-1) ^ V.card := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  rw [sum_congr rfl h, ← mul_sum, sum_powerset_neg_one_pow_card]
  split_ifs with hW <;> simp [hW]

theorem mob_ind (A S : Finset E) :
    S.powerset.sum (fun T => (-1 : ℤ) ^ (S.card - T.card) * (if A ⊆ T then 1 else 0))
      = if A = S then 1 else 0 := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  by_cases hAS : A ⊆ S
  · have key : (S.powerset.filter (fun T => A ⊆ T)).sum (fun T => (-1 : ℤ) ^ (S.card - T.card))
        = (S \ A).powerset.sum (fun V => (-1 : ℤ) ^ ((S \ A).card - V.card)) := by
      apply sum_nbij' (fun T => T \ A) (fun V => V ∪ A)
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        simp only [mem_powerset]
        exact sdiff_subset_sdiff hT.1 le_rfl
      · intro V hV
        simp only [mem_powerset] at hV
        simp only [mem_filter, mem_powerset]
        exact ⟨union_subset (hV.trans sdiff_subset) hAS, subset_union_right⟩
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        exact sdiff_union_of_subset hT.2
      · intro V hV
        simp only [mem_powerset] at hV
        exact union_sdiff_cancel_right (disjoint_of_subset_left hV disjoint_sdiff_self_left)
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        have h1 := card_sdiff_add_card_eq_card hAS
        have h2 := card_sdiff_add_card_eq_card hT.2
        have h3 := card_le_card hT.1
        congr 1
        omega
    rw [key, alt_sum]
    by_cases hA : A = S
    · subst hA; simp
    · rw [if_neg hA, if_neg]
      intro he
      exact hA (subset_antisymm hAS (sdiff_eq_empty_iff_subset.mp he))
  · have : S.powerset.filter (fun T => A ⊆ T) = ∅ := by
      rw [filter_eq_empty_iff]
      intro T hT hA
      exact hAS (hA.trans (mem_powerset.mp hT))
    rw [this, sum_empty, if_neg]
    rintro rfl
    exact hAS subset_rfl


def mob (S : Finset E) (F : Finset E → Int) := S.powerset.sum (fun U => (-1:Int)^(S.card-U.card)*F U)
def lin (b : Int) (w : E → Int) (S : Finset E) := b + S.sum w

theorem vanish_lin (S : Finset E) (two : 2≤S.card) (b : Int) (w : E → Int) :
    mob S (lin b w) = 0 := by
  classical
  have ne : S≠∅ := by intro eq; subst S; simp at two
  have fixed (U : Finset E) (sub : U⊆S) :
      U.sum w=∑ e∈S,(if {e}⊆U then (1:Int) else 0)*w e := by
    calc
      U.sum w = (S.filter (fun e => e∈U)).sum w := by
        congr 1; ext e; simp only [mem_filter]; exact ⟨fun h => ⟨sub h,h⟩,And.right⟩
      _ = _ := by rw [sum_filter]; simp
  unfold mob lin
  simp_rw [mul_add]
  rw [sum_add_distrib,←sum_mul,alt_sum,if_neg ne,zero_mul,zero_add]
  calc
    _ = ∑ U∈S.powerset, ∑ e∈S, ((-1:Int)^(S.card-U.card)*(if {e}⊆U then 1 else 0))*w e := by
      apply sum_congr rfl
      intro U hU
      rw [fixed U (mem_powerset.mp hU),mul_sum]
      apply sum_congr rfl
      intro e _
      ring
    _ = ∑ e∈S, (if {e}=S then (1:Int) else 0)*w e := by
      rw [sum_comm]
      apply sum_congr rfl
      intro e _
      rw [←sum_mul, mob_ind]
    _ = 0 := by
      apply sum_eq_zero
      intro e _
      have neq : ({e}:Finset E)≠S := by intro h; rw [←h] at two; simp at two
      simp [neq]

theorem affine_or_cube (D : Finset E → Prop) (down : ∀ {T U},D T → U⊆T → D U)
    (F : Finset E → Int) :
    (∃ b : Int, ∃ w : E → Int, ∀ S, D S → F S=lin b w S) ∨
    ∃ T, D T ∧ 2≤T.card ∧ (∀ U⊆T,D U) ∧ mob T F≠0 := by
  classical
  let b := F ∅
  let w (e : E) := F {e}-b
  by_cases yes : ∀ S, D S → F S=lin b w S
  · exact Or.inl ⟨b,w,yes⟩
  right
  push_neg at yes
  obtain ⟨S,hD,hbad⟩ := yes
  let bad := (S.powerset.filter (fun U => F U≠lin b w U))
  have hS : S∈bad := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl,hbad⟩
  obtain ⟨T,hT,minT⟩ := bad.exists_min_image Finset.card ⟨S,hS⟩
  have small (U : Finset E) (sub : U⊆T) (neq : U≠T) : F U=lin b w U := by
    by_contra diff
    have mem : U∈bad := mem_filter.mpr ⟨mem_powerset.mpr (sub.trans (mem_powerset.mp (mem_filter.mp hT).1)),diff⟩
    have least := minT U mem
    have lt := card_lt_card (ssubset_of_subset_of_ne sub neq)
    omega
  have two : 2≤T.card := by
    by_contra! h
    obtain emp|⟨e,one⟩ := T.eq_empty_or_nonempty
    · exact (mem_filter.mp hT).2 (by rw [emp]; simp [b,lin])
    · have eq : T={e} := by
        symm
        exact eq_of_subset_of_card_le (singleton_subset_iff.mpr one) (by simp; omega)
      exact (mem_filter.mp hT).2 (by rw [eq]; simp [w,lin]; ring)
  refine ⟨T,down hD (mem_powerset.mp (mem_filter.mp hT).1),two,fun U sub => down hD
    (sub.trans (mem_powerset.mp (mem_filter.mp hT).1)),?_⟩
  have delta : mob T (fun U => F U-lin b w U)=F T-lin b w T := by
    unfold mob
    rw [sum_eq_single T]
    · simp
    · intro U hU neq
      simp [small U (mem_powerset.mp hU) neq]
    · intro hn
      exact (hn (mem_powerset.mpr Subset.rfl)).elim
  have expand : mob T (fun U => F U-lin b w U)=mob T F-mob T (lin b w) := by
    simp [mob,mul_sub,sum_sub_distrib]
  rw [expand,vanish_lin T two,sub_zero] at delta
  intro zero
  exact (mem_filter.mp hT).2 (sub_eq_zero.mp (delta.symm.trans zero))

end PEqualNP.Outside.L_meta_33669
