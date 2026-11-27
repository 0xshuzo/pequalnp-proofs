import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_912_aux
open Finset

def nextSite {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

def equalEdges {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun i => (i ∈ S ↔ nextSite i ∈ S))

def encode {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : Bool × Finset (Fin n) :=
  (decide ((⟨0,hn⟩ : Fin n) ∈ S), equalEdges S)

theorem encode_injective {n : ℕ} (hn : 0 < n) : Function.Injective (encode hn) := by
  intro S T he
  have h0 : ((⟨0,hn⟩ : Fin n) ∈ S) ↔ (⟨0,hn⟩ : Fin n) ∈ T := by
    have h := congrArg Prod.fst he
    simpa [encode] using h
  have hd : equalEdges S = equalEdges T := congrArg Prod.snd he
  have step (i : Fin n) (h : i ∈ S ↔ i ∈ T) : nextSite i ∈ S ↔ nextSite i ∈ T := by
    have hh : (i ∈ S ↔ nextSite i ∈ S) ↔ (i ∈ T ↔ nextSite i ∈ T) := by
      have hm : i ∈ equalEdges S ↔ i ∈ equalEdges T := by rw [hd]
      simpa [equalEdges] using hm
    tauto
  have go (k : ℕ) (hk : k < n) : (⟨k,hk⟩ : Fin n) ∈ S ↔ (⟨k,hk⟩ : Fin n) ∈ T := by
    induction k with
    | zero => exact h0
    | succ k ih =>
      have hk' : k < n := by omega
      have hs := step ⟨k,hk'⟩ (ih hk')
      have heq : nextSite (⟨k,hk'⟩ : Fin n) = ⟨k+1,hk⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hk)
      rwa [heq] at hs
  ext i
  exact go i.val i.isLt

lemma small_subsets (n k : ℕ) (hn : 2 ≤ n) :
    ((univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k)).card ≤ 2*n^k := by
  let sets := fun j => (univ : Finset (Fin n)).powersetCard j
  have hsub : (univ.filter (fun S : Finset (Fin n) => S.card ≤ k)) ⊆
      (range (k+1)).biUnion sets := by
    intro S hS
    exact mem_biUnion.mpr ⟨S.card, mem_range.mpr (by have := (mem_filter.mp hS).2; omega),
      mem_powersetCard.mpr ⟨subset_univ _,rfl⟩⟩
  have hsum : ∀ m : ℕ, (∑ j ∈ range (m+1), n^j) ≤ 2*n^m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      have hpow : 2*n^m ≤ n^(m+1) := by
        rw [pow_succ, Nat.mul_comm (n^m)]
        exact Nat.mul_le_mul_right _ hn
      omega
  calc
    _ ≤ ((range (k+1)).biUnion sets).card := card_le_card hsub
    _ ≤ ∑ j ∈ range (k+1), (sets j).card := card_biUnion_le
    _ ≤ ∑ j ∈ range (k+1), n^j := by
      apply sum_le_sum
      intro j _
      simpa [sets] using Nat.choose_le_pow n j
    _ ≤ _ := hsum _

theorem count_supports {n k : ℕ} (hn : 2 ≤ n) :
    ((univ : Finset (Finset (Fin n))).filter (fun S => (equalEdges S).card ≤ k)).card ≤
      4*n^k := by
  have hp : 0 < n := by omega
  let small := (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k)
  have hle : ((univ : Finset (Finset (Fin n))).filter
      (fun S => (equalEdges S).card ≤ k)).card ≤ ((univ : Finset Bool).product small).card := by
    apply card_le_card_of_injOn (encode hp)
    · intro S hS
      exact mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hS).2⟩⟩
    · exact (encode_injective hp).injOn
  have hs := small_subsets n k hn
  calc
    _ ≤ ((univ : Finset Bool).product small).card := hle
    _ = (univ : Finset Bool).card * small.card := card_product _ _
    _ = 2*small.card := by simp
    _ ≤ 2*(2*n^k) := Nat.mul_le_mul_left 2 hs
    _ = _ := by ring

end PEqualNP.Outside.L_lib_912_aux
