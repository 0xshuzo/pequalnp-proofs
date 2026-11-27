import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007.RowCompletion
open Finset

variable {n m k : ℕ}
abbrev Rect (n m : ℕ) := Finset (Fin n) × Finset (Fin m)
def lawful (inc : Fin n → Fin m → Bool) (R : Fin k → Rect n m) : Prop :=
  (∀ t, ∀ p ∈ (R t).1, ∀ l ∈ (R t).2, inc p l = false) ∧
  (∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2)

def separates (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n)) : Prop :=
  ∀ p l, inc p l = false → ∃ t, p ∈ S t ∧ ∀ q ∈ S t, inc q l = false

def completed (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n)) :
    Fin k → Rect n m := fun t =>
  (S t, univ.filter fun l => ∀ q ∈ S t, inc q l = false)

theorem projection (inc : Fin n → Fin m → Bool) (R : Fin k → Rect n m)
    (h : lawful inc R) : separates inc (fun t => (R t).1) := by
  intro p l e
  obtain ⟨t, a, b⟩ := h.2 p l e
  exact ⟨t, a, fun q z => h.1 t q z l b⟩

theorem complete_iff (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n)) :
    lawful inc (completed inc S) ↔ separates inc S := by
  constructor
  · exact projection inc (completed inc S)
  · intro h
    constructor
    · intro t p hp l hl
      exact (mem_filter.mp hl).2 p hp
    · intro p l e
      obtain ⟨t, a, b⟩ := h p l e
      exact ⟨t, a, mem_filter.mpr ⟨mem_univ _, b⟩⟩

def unblocked (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n))
    (U : Finset (Fin n)) : Prop :=
  ∀ p l, inc p l = false → p ∈ U ∨
    ∃ t, p ∈ S t ∧ ∀ q ∈ S t, inc q l = true → q ∈ U

theorem candidate_unblocks (inc : Fin n → Fin m → Bool) (R : Fin k → Rect n m)
    (S : Fin k → Finset (Fin n)) (U : Finset (Fin n))
    (h : lawful inc R) (fixedRows : ∀ p ∉ U, ∀ t, p ∈ S t ↔ p ∈ (R t).1) :
    unblocked inc S U := by
  intro p l e
  by_cases f : p ∈ U
  · exact Or.inl f
  · obtain ⟨t, a, b⟩ := h.2 p l e
    refine Or.inr ⟨t, (fixedRows p f t).mpr a, ?_⟩
    intro q qt e'
    by_contra outside
    have v := h.1 t q ((fixedRows q outside t).mp qt) l b
    rw [e'] at v
    contradiction

end PEqualNP.Outside.L_meta_10007.RowCompletion
