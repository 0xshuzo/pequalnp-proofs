import Mathlib

namespace Counter3576

/-- The ordered four-vertex certificates with left endpoint a. -/
def cycles {N : ℕ} (E : Finset (Fin N × Fin N)) (a : Fin N) :=
  Finset.univ.filter (fun t : Fin N × Fin N × Fin N =>
    a ≠ t.1 ∧ t.2.1 ≠ t.2.2 ∧ (a,t.2.1)∈E ∧ (a,t.2.2)∈E ∧ (t.1,t.2.1)∈E ∧ (t.1,t.2.2)∈E)

def cleaned {N : ℕ} (E : Finset (Fin N × Fin N)) :=
  E.filter (fun e => (cycles E e.1).card=0)

theorem no_square {N : ℕ} (E : Finset (Fin N × Fin N)) (a a' b b' : Fin N)
    (ha : a≠a') (hb : b≠b') :
    ¬((a,b)∈cleaned E ∧ (a,b')∈cleaned E ∧ (a',b)∈cleaned E ∧ (a',b')∈cleaned E) := by
  rintro ⟨h1,h2,h3,h4⟩
  have good := (Finset.mem_filter.mp h1).2
  have cert : (a',b,b')∈cycles E a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hb,
    (Finset.mem_filter.mp h1).1,(Finset.mem_filter.mp h2).1,(Finset.mem_filter.mp h3).1,
    (Finset.mem_filter.mp h4).1⟩
  exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨_,cert⟩)) good

theorem alteration_bound {N : ℕ} (E : Finset (Fin N × Fin N)) :
    E.card ≤ (cleaned E).card + ∑ a : Fin N,(cycles E a).card*(E.filter (fun e => e.1=a)).card := by
  classical
  let R := E \ cleaned E
  have count := Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (s:=R) (t:=Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  have each (a : Fin N) :
      (R.filter (fun e => e.1=a)).card ≤ (cycles E a).card*(E.filter (fun e => e.1=a)).card := by
    by_cases small : (cycles E a).card=0
    · have empty : R.filter (fun e => e.1=a)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain ⟨re,eq⟩ := Finset.mem_filter.mp he
        obtain ⟨inE,out⟩ := Finset.mem_sdiff.mp re
        exact out (Finset.mem_filter.mpr ⟨inE,by simpa only [eq] using small⟩)
      rw [empty,Finset.card_empty]
      exact Nat.zero_le _
    · have sub : R.filter (fun e => e.1=a) ⊆ E.filter (fun e => e.1=a) := by
        intro e he
        obtain ⟨re,eq⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp re).1,eq⟩
      exact (Finset.card_le_card sub).trans (by
        calc
          _ = 1*(E.filter (fun e => e.1=a)).card := (Nat.one_mul _).symm
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega))
  have h := Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin N))) => each a)
  have pr := Finset.card_le_card_sdiff_add_card (s:=E) (t:=cleaned E)
  change E.card ≤ R.card + (cleaned E).card at pr
  omega

theorem finite_averaging {N : ℕ} {Ω : Type} [Fintype Ω] (E : Ω → Finset (Fin N × Fin N)) (B : ℕ)
    (margin : Fintype.card Ω * B + ∑ x : Ω, ∑ a : Fin N,
       (cycles (E x) a).card*((E x).filter (fun e => e.1=a)).card < ∑ x : Ω,(E x).card) :
    ∃ x, B < (cleaned (E x)).card := by
  classical
  by_contra! low
  have h (x : Ω) :
      (E x).card ≤ B + ∑ a : Fin N,(cycles (E x) a).card*((E x).filter (fun e => e.1=a)).card :=
    (alteration_bound (E x)).trans (Nat.add_le_add_right (low x) _)
  have summed := Finset.sum_le_sum (fun x (_ : x∈(Finset.univ : Finset Ω)) => h x)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at summed
  omega

end Counter3576
