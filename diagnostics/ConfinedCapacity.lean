import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10007.Pencil
open Finset
def rows : List ℕ := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def inc (p : Fin 31) (l : Fin 31) : Bool := (rows.getD p.val 0).testBit l.val
abbrev Box := Finset (Fin 31) × Finset (Fin 31)
def Good (R : Box) : Prop := ∀ p ∈ R.1, ∀ l ∈ R.2, inc p l = false
def cov {k : ℕ} (R : Fin k → Box) (p : Fin 31) (l : Fin 31) : ℕ :=
  (univ.filter fun t => p ∈ (R t).1 ∧ l ∈ (R t).2).card
def tp {k : ℕ} (R : Fin k → Box) (p : Fin 31) : Finset (Fin k) := univ.filter fun t => p ∈ (R t).1
def tl {k : ℕ} (R : Fin k → Box) (l : Fin 31) : Finset (Fin k) := univ.filter fun t => l ∈ (R t).2

def confined (p x : Fin 31) : Finset (Fin 31) :=
  univ.filter fun q => ∀ l : Fin 31, inc x l = true → inc p l = false → inc q l = false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem five : ∀ p x : Fin 31, p ≠ x → (confined p x).card = 5 := by
  intro p
  fin_cases p <;> decide +kernel


def joint {k : ℕ} (R : Fin k → Box) (I : Finset (Fin k)) : Finset (Fin 31) :=
  univ.filter (fun q => ∀ t ∈ I, q ∈ (R t).1)

theorem mem_joint {k : ℕ} {R : Fin k → Box} {I : Finset (Fin k)} {q : Fin 31} :
    q ∈ joint R I ↔ ∀ t ∈ I, q ∈ (R t).1 := by simp [joint]

theorem partitionConfinement {k : ℕ} (R : Fin k → Box) (good : ∀ t, Good (R t))
    (hit : ∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2)
    (p x : Fin 31) (I : Finset (Fin k))
    (hx : x ∈ joint R (tp R p \ I)) : joint R I ⊆ confined p x := by
  intro q hq
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  intro l hxl hpl
  obtain ⟨t,hp,hl⟩ := hit p l hpl
  by_cases ht : t ∈ I
  · exact good t q ((mem_joint.mp hq) t ht) l hl
  · have hpt : t ∈ tp R p := mem_filter.mpr ⟨mem_univ _,hp⟩
    have hxt := mem_joint.mp hx t (mem_sdiff.mpr ⟨hpt,ht⟩)
    have bad := good t x hxt l hl
    rw [hxl] at bad
    contradiction

theorem privateComplement {k : ℕ} (R : Fin k → Box) (good : ∀ t, Good (R t))
    (hit : ∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2)
    (p : Fin 31) (I : Finset (Fin k)) (wide : 6 ≤ (joint R I).card) :
    joint R (tp R p \ I) = {p} := by
  ext x
  constructor
  · intro hx
    by_contra hn
    have ne : p ≠ x := by
      intro e
      subst x
      exact hn (mem_singleton_self p)
    have h := card_le_card (partitionConfinement R good hit p x I hx)
    rw [five p x ne] at h
    omega
  · intro hx
    have e := mem_singleton.mp hx
    subst x
    apply mem_joint.mpr
    intro t ht
    exact (mem_filter.mp (mem_sdiff.mp ht).1).2

theorem distinctResidual {k : ℕ} (R : Fin k → Box) (good : ∀ t, Good (R t))
    (hit : ∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2)
    {p q : Fin 31} (neq : p ≠ q) (I J : Finset (Fin k))
    (hi : 6 ≤ (joint R I).card) (hj : 6 ≤ (joint R J).card) :
    tp R p \ I ≠ tp R q \ J := by
  intro e
  have same := congrArg (joint R) e
  rw [privateComplement R good hit p I hi, privateComplement R good hit q J hj] at same
  have hq : p ∈ ({q} : Finset (Fin 31)) := same ▸ mem_singleton_self p
  exact neq (mem_singleton.mp hq)


theorem rowDegree : ∀ p : Fin 31, (univ.filter (fun l => inc p l = true)).card = 6 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem uniqueJoin : ∀ p q : Fin 31, p ≠ q →
    ∃! l : Fin 31, inc p l = true ∧ inc q l = true := by
  intro p
  fin_cases p <;> decide +kernel

theorem confinedInLine {p q : Fin 31} (ne : p ≠ q) :
    ∃ l : Fin 31, ∀ x ∈ confined p q, inc x l = true := by
  obtain ⟨l,hl,uq⟩ := uniqueJoin p q ne
  refine ⟨l,?_⟩
  intro x hx
  by_cases e : q = x
  · exact e ▸ hl.2
  obtain ⟨m,hm,_⟩ := uniqueJoin q x e
  have pm : inc p m = true := by
    cases hh : inc p m with
    | true => rfl
    | false =>
      have bad := (mem_filter.mp hx).2 m hm.1 hh
      rw [hm.2] at bad
      contradiction
  have eq := uq m ⟨pm,hm.1⟩
  exact eq ▸ hm.2

theorem collinearWidth (A B : Finset (Fin 31)) (l : Fin 31)
    (onLine : ∀ p ∈ A, inc p l = true)
    (blank : ∀ p ∈ A, ∀ j ∈ B, inc p j = false) :
    5 * A.card + B.card ≤ 31 := by
  let D : Finset (Fin 31) := univ.erase l
  have countAt (p : Fin 31) (hp : p ∈ A) :
      (D.filter (fun j => inc p j = true)).card = 5 := by
    have eq : D.filter (fun j => inc p j = true) =
        (univ.filter (fun j => inc p j = true)).erase l := by
      ext j
      simp [D, and_left_comm, and_assoc, and_comm]
    rw [eq,card_erase_of_mem (mem_filter.mpr ⟨mem_univ _,onLine p hp⟩), rowDegree]
  have cap (j : Fin 31) (hj : j ∈ D) :
      (A.filter (fun p => inc p j = true)).card ≤ (if j ∈ B then 0 else 1 : ℕ) := by
    by_cases hB : j ∈ B
    · have emp : A.filter (fun p => inc p j = true) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p m
        obtain ⟨hp,hj'⟩ := mem_filter.mp m
        simpa [blank p hp j hB] using hj'
      simp [hB,emp]
    · rw [if_neg hB]
      apply card_le_one.mpr
      intro p hp q hq
      by_contra ne
      obtain ⟨_,_,unique⟩ := uniqueJoin p q ne
      obtain ⟨pa,pj⟩ := mem_filter.mp hp
      obtain ⟨qa,qj⟩ := mem_filter.mp hq
      have eq := (unique j ⟨pj,qj⟩).trans (unique l ⟨onLine p pa,onLine q qa⟩).symm
      exact (mem_erase.mp hj).1 eq
  have grid : (∑ j ∈ D, (A.filter (fun p => inc p j = true)).card) =
      ∑ p ∈ A, (D.filter (fun j => inc p j = true)).card := by
    simp only [card_filter]
    rw [sum_comm]
  have tot := sum_le_sum cap
  rw [grid, sum_congr rfl countAt] at tot
  have cost : (∑ j ∈ D, (if j ∈ B then 0 else 1 : ℕ)) = (D \ B).card := by
    rw [sdiff_eq_filter, card_filter]
    apply sum_congr rfl
    intro j _
    by_cases h : j ∈ B <;> simp [h]
  rw [cost] at tot
  have sub : D \ B ⊆ univ \ B := fun j hj => mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hj).2⟩
  have remaining := card_le_card sub
  rw [card_sdiff_of_subset (subset_univ B), card_univ, Fintype.card_fin] at remaining
  have hb : B.card ≤ 31 := card_le_univ B
  simp only [sum_const, nsmul_eq_mul] at tot
  omega

theorem confinedCapacity {p q : Fin 31} (ne : p ≠ q) (R : Box)
    (h : Good R) (s : R.1 ⊆ confined p q) :
    5 * R.1.card + R.2.card ≤ 31 := by
  obtain ⟨l,hl⟩ := confinedInLine ne
  exact collinearWidth _ _ l (fun x hx => hl x (s hx)) h

end PEqualNP.Outside.L_meta_10007.Pencil
