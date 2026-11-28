import PEqualNP.Defs
namespace Plane9348.OvalPhysical
open Finset
abbrev V := Fin 21
abbrev J := Fin 7
abbrev Box := Finset V × Finset V
def rows : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def black (r c : V) := (rows.getD r.val 0).testBit c.val

def target (r : V) := univ.filter fun c : V => black r c=false
theorem shape : ∀r : V,(target r).card=16 := by decide +kernel
def owners (B : List Box) (r : V) := univ.filter fun i : Fin B.length => r ∈ (B.get i).1
def degree (B : List Box) (r : V) := (owners B r).card
theorem degreePrice (B : List Box) (cost : ∀b∈B,b.2.card=6)
    (cov : ∀r c,black r c=false → ∃b∈B,r∈b.1 ∧ c∈b.2) (r : V) : 3≤degree B r := by
  classical
  have sub : target r ⊆ (owners B r).biUnion (fun i => (B.get i).2) := by
    intro c hc
    obtain ⟨b,bb,rr,cc⟩ := cov r c (mem_filter.mp hc).2
    obtain ⟨i,e⟩ := List.mem_iff_get.mp bb
    exact mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,e.symm ▸ rr⟩,e.symm ▸ cc⟩
  have ct:= (card_le_card sub).trans card_biUnion_le
  have same : (∑i∈owners B r,(B.get i).2.card) = (owners B r).card*6 := by
    simp only [cost _ (List.get_mem B _),sum_const,nsmul_eq_mul]
    rfl
  rw [shape,same] at ct
  unfold degree
  omega
theorem allDegrees (B : List Box) (cost : ∀b∈B,b.1.card=6) :
    (∑r : V,degree B r)=B.length*6 := by
  classical
  have per (r : V) : degree B r = ∑ i : Fin B.length, (if r∈(B.get i).1 then 1 else 0 : Nat) := by
    simp [degree,owners,Finset.sum_boole]
  simp_rw [per]
  rw [sum_comm]
  have inner (i : Fin B.length) : (∑r : V, if r∈(B.get i).1 then 1 else 0 : Nat)=6 := by
    simpa using cost (B.get i) (List.get_mem B i)
  simp_rw [inner]
  simp
theorem lowSites (d : V → Nat) (atleast : ∀r,3≤d r) (total : (∑r,d r)≤84) :
    11 ≤ (univ.filter fun r => d r≤4).card := by
  classical
  have h : (∑ _ : V,(5:Nat)) ≤ ∑ r : V,(d r+2*(if d r≤4 then 1 else 0)) := by
    apply sum_le_sum
    intro r _
    by_cases hr:d r≤4
    · simp [hr]; have := atleast r; omega
    · simp [hr]; omega
  rw [sum_add_distrib,←Finset.mul_sum] at h
  have cnt : (∑r : V,(if d r≤4 then 1 else 0 : Nat)) = (univ.filter fun r => d r≤4).card := by simp
  rw [cnt] at h
  have z : (∑_ : V,(5:Nat))=105 := by decide
  rw [z] at h
  omega
theorem rowBound (B : List Box) (n : B.length≤14) (oval : ∀b∈B,b.1.card=6 ∧ b.2.card=6)
    (cov : ∀r c,black r c=false → ∃b∈B,r∈b.1 ∧ c∈b.2) :
    11≤(univ.filter fun r => degree B r≤4).card := by
  apply lowSites (degree B) (degreePrice B (fun b h => (oval b h).2) cov)
  rw [allDegrees B (fun b h => (oval b h).1)]
  omega
end Plane9348.OvalPhysical
