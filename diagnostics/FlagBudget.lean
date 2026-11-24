import Mathlib

namespace FlagBudget4801

abbrev pt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
abbrev ln (l : Fin 13) : Fin 26 := Fin.natAdd 13 l

def flags : Finset (Fin 13 × Fin 13) := Finset.univ.filter fun e =>
  e.1=e.2 ∨ e.1=e.2+1 ∨ e.1=e.2+3 ∨ e.1=e.2+9

def star (v : Fin 26) := flags.filter fun e => pt e.1=v ∨ ln e.2=v

private theorem total : flags.card = 52 := by decide
private theorem degree : ∀ v, (star v).card = 4 := by decide

/-- The exact deficit in the easy-edge charging bound, allowing arbitrarily many missing flags. -/
theorem deficit (E : Finset (Fin 13 × Fin 13)) (T : Finset (Fin 26)) (s : ℕ)
    (sub : E ⊆ flags) (cover : ∀ e ∈ E, pt e.1 ∈ T ∨ ln e.2 ∈ T)
    (paid : E.card+T.card ≤ s+1) : 64 ≤ s+(flags \ E).card+(flags \ E).card/4 := by
  have cap : E ⊆ T.biUnion star := by
    intro e he
    rcases cover e he with h|h
    · exact Finset.mem_biUnion.mpr ⟨_,h,Finset.mem_filter.mpr ⟨sub he,Or.inl rfl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨_,h,Finset.mem_filter.mpr ⟨sub he,Or.inr rfl⟩⟩
  have deg : E.card ≤ T.card*4 := (Finset.card_le_card cap).trans
    (Finset.card_biUnion_le.trans (by simp [degree]))
  have all := Finset.card_sdiff_add_card_eq_card sub
  rw [total] at all
  omega

end FlagBudget4801
