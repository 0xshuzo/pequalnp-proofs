import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20241

private def matrix (r c : Fin 8) : Bool :=
  (12147342212780283915 : ℕ).testBit (8 * r.val + c.val)

private def diagonal : Fin 8 → Fin 8 := ![0, 3, 6, 4, 1, 2, 7, 5]

private theorem positiveDiagonal : ∀ i, matrix i (diagonal i) = true := by
  decide +kernel

private theorem incompatible : ∀ i j, i ≠ j →
    matrix i (diagonal j) = false ∨ matrix j (diagonal i) = false := by
  decide +kernel

private theorem falseRow : ∀ r, ∃ c, matrix r c = false := by decide +kernel
private theorem falseColumn : ∀ c, ∃ r, matrix r c = false := by decide +kernel

private theorem coverBound {k : ℕ} (R C : Fin k → Fin 8 → Prop)
    (rep : ∀ i j, matrix i j = true ↔ ∃ q, R q i ∧ C q j) : 8 ≤ k := by
  classical
  have selected (i : Fin 8) := (rep i (diagonal i)).1 (positiveDiagonal i)
  let slot (i : Fin 8) : Fin k := Classical.choose (selected i)
  have hslot (i : Fin 8) : R (slot i) i ∧ C (slot i) (diagonal i) :=
    Classical.choose_spec (selected i)
  have key : Function.Injective slot := by
    intro i j eq
    by_contra neq
    have same : R (slot i) j ∧ C (slot i) (diagonal j) := eq.symm ▸ hslot j
    have h₁ := (rep i (diagonal j)).2 ⟨slot i, (hslot i).1, same.2⟩
    have h₂ := (rep j (diagonal i)).2 ⟨slot i, same.1, (hslot i).2⟩
    rcases incompatible i j neq with f | f <;> simp_all
  simpa using Fintype.card_le_of_injective slot key

theorem productCount {k : ℕ} (A B C D : Fin k → Fin 8 → Prop)
    (rep : ∀ i j, matrix i j = true ↔
      ∃ t, (A t i ∨ B t j) ∧ (C t i ∨ D t j)) : 4 ≤ k := by
  classical
  let Q := Fin k × Bool
  let row (q : Q) (i : Fin 8) : Prop := if q.2 then A q.1 i else C q.1 i
  let col (q : Q) (j : Fin 8) : Prop := if q.2 then D q.1 j else B q.1 j
  have expanded (i j : Fin 8) : matrix i j = true ↔ ∃ q : Q, row q i ∧ col q j := by
    constructor
    · intro h
      obtain ⟨t, h₁, h₂⟩ := (rep i j).1 h
      rcases h₁ with a | b <;> rcases h₂ with c | d
      · obtain ⟨z, hz⟩ := falseRow i
        have bad := (rep i z).2 ⟨t, Or.inl a, Or.inl c⟩
        simp_all
      · exact ⟨⟨t, true⟩, a, d⟩
      · exact ⟨⟨t, false⟩, c, b⟩
      · obtain ⟨z, hz⟩ := falseColumn j
        have bad := (rep z j).2 ⟨t, Or.inr b, Or.inr d⟩
        simp_all
    · rintro ⟨⟨t, flag⟩, r, c⟩
      cases flag
      · exact (rep i j).2 ⟨t, Or.inr c, Or.inl r⟩
      · exact (rep i j).2 ⟨t, Or.inl r, Or.inr c⟩
  let e := Fintype.equivFin Q
  have h : 8 ≤ Fintype.card Q := coverBound
      (fun q => row (e.symm q)) (fun q => col (e.symm q)) (by
    intro i j
    rw [expanded]
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨e q, by simpa using hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨e.symm q, hq⟩)
  have bound : 8 ≤ k * 2 := by simpa [Q] using h
  omega

end PEqualNP.Outside.L_meta_20241
