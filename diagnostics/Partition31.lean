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

end PEqualNP.Outside.L_meta_10007.Pencil
