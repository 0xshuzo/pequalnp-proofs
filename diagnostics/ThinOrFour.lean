import PEqualNP.Outside.L_meta_10006

namespace PEqualNP.Outside.L_meta_10008.ThinOrFour
open PEqualNP.Outside.L_meta_10006 Finset
open scoped BigOperators
def high (d : Nat) : Nat := if 5≤d then 1 else 0
def squareTag (a b : Nat) : Nat := if a=7 ∧ b=7 then 1 else 0

private theorem sides {a b : Nat} (lo : 7≤a) (lo' : 7≤b) (area : a*b ≤ 60) :
    a≤8 ∧ b≤8 ∧ a+b+squareTag a b≤15 := by
  have ha : a*7≤60 := (Nat.mul_le_mul_left a lo').trans area
  have hb : 7*b≤60 := (Nat.mul_le_mul_right b lo).trans area
  have aa : a≤8 := by omega
  have bb : b≤8 := by omega
  interval_cases a <;> interval_cases b <;> decide +revert

theorem boundedDegree {k : Nat} (M : V → V → Bool) (R : Fin k → Box)
    (good : ∀t,Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (covers : ∀i j,M i j=false → ∃t,i∈(R t).1 ∧ j∈(R t).2)
    (count : ∀i,(univ.filter fun j => M i j=false).card=25)
    (width : ∀t,(R t).2.card ≤ 8) (i : V) : 4 ≤ degree R i := by
  classical
  have h := row_load R good covers count i
  have a : (∑t ∈ rowSupport R i,(R t).2.card) ≤ ∑_t ∈ rowSupport R i,8 :=
    sum_le_sum (fun t _ => width t)
  simp only [sum_const,nsmul_eq_mul] at a
  unfold degree
  omega

theorem highPrice {k : Nat} (R : Fin k → Box) (floor : ∀i,4≤degree R i) :
    124 + (∑i : V,high (degree R i)) ≤ ∑t,(R t).1.card := by
  classical
  have h : ∀i : V,4+high (degree R i)≤degree R i := by
    intro i
    have f := floor i
    unfold high
    split <;> omega
  have hs := sum_le_sum (s:=(univ:Finset V)) (fun i _ => h i)
  have tot : (∑i : V,degree R i)=∑t,(R t).1.card := by
    simpa [degree] using sum_support R (fun _ => 1)
  simpa [sum_add_distrib,tot] using hs

theorem concentration {k : Nat} (R : Fin k → Box) (budget : k ≤ 17)
    (good : ∀t,plain (R t))
    (cov : ∀i j,matrix i j=false → ∃t,i∈(R t).1 ∧ j∈(R t).2)
    (large : ∀t,7≤(R t).1.card ∧ 7≤(R t).2.card) :
    k=17 ∧ (∀i,4≤degree R i ∧ 4≤degree (flip R) i) ∧
    (∑i : V,high (degree R i))+(∑j : V,high (degree (flip R) j))+
    (∑t,squareTag (R t).1.card (R t).2.card) ≤ 7 := by
  classical
  have shape (t : Fin k) := sides (large t).1 (large t).2 (Area.matrix_area_le_60 _ _ (good t))
  have rf := boundedDegree matrix R good cov row_counts (fun t => (shape t).2.1)
  have tg (t : Fin k) : Area.Moments.EmptyRectangle (transposeMatrix matrix) ((flip R) t).1 ((flip R) t).2 :=
    fun j hj i hi => good t i hi j hj
  have tc (j i : V) (h : transposeMatrix matrix j i=false) :
      ∃t,j∈(flip R t).1 ∧ i∈(flip R t).2 := by
    obtain ⟨t,hi,hj⟩ := cov i j h
    exact ⟨t,hj,hi⟩
  have cf := boundedDegree (transposeMatrix matrix) (flip R) tg tc count_table (fun t => (shape t).1)
  have h₁ := highPrice R rf
  have h₂ := highPrice (flip R) cf
  change 124 + _ ≤ ∑t,(R t).2.card at h₂
  have h₃ := sum_le_sum (s:=(univ:Finset (Fin k))) (fun t _ => (shape t).2.2)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at h₃
  refine ⟨by omega,fun i => ⟨rf i,cf i⟩,by omega⟩

-- Deleting a short column side preserves the complete covering of all other lines.
theorem deleteThin {k : Nat} (R : Fin k → Box)
    (cov : ∀i j,matrix i j=false → ∃t,i∈(R t).1 ∧ j∈(R t).2)
    (s : Fin k) (thin : (R s).2.card ≤ 6) :
    ∃ lines : Finset V, 25≤lines.card ∧
      ∀j∈lines,∀i,matrix i j=false → ∃t,t≠s ∧ i∈(R t).1 ∧ j∈(R t).2 := by
  classical
  refine ⟨univ \ (R s).2,?_,?_⟩
  · have size := card_sdiff_add_card_eq_card (subset_univ (R s).2)
    simp only [card_univ,Fintype.card_fin] at size
    omega
  · intro j hj i blank
    obtain ⟨t,hi,hit⟩ := cov i j blank
    exact ⟨t,fun e => (mem_sdiff.mp hj).2 (e ▸ hit),hi,hit⟩
end PEqualNP.Outside.L_meta_10008.ThinOrFour
