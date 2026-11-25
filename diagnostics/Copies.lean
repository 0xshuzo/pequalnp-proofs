import PEqualNP.Defs

namespace PCX150

/-- Incoming slots are listed with multiplicity. Before a shared vertex is expanded,
    cutting its incoming edges makes that vertex a separate fragment root. -/
theorem unitExpansion (roots : Nat → Bool) (incoming : Nat → List Nat) (occurs : Nat → Nat)
    (recurrence : ∀ i, occurs i =
      if roots i then 1 else ((incoming i).map occurs).sum)
    (single : ∀ i, roots i = false → ∃ p, incoming i = [p] ∧ p < i) :
    ∀ i, occurs i = 1 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [recurrence i]
    cases hr : roots i with
    | true => rfl
    | false =>
      obtain ⟨p,hp,lt⟩ := single i hr
      simp [hp,ih p lt]

/-- At a cut, the number of leaf copies is the number of incoming parent slots. -/
theorem incomingCopies {occurs : Nat → Nat} (one : ∀ i, occurs i = 1) (slots : List Nat) :
    (slots.map occurs).sum = slots.length := by
  induction slots with
  | nil => rfl
  | cons x xs ih => simp [one,ih,Nat.add_comm]

/-- Duplicating one small fragment eliminates one of three shared nodes and
    yields a two-lemma proof below the calibrated threshold. -/
theorem fragmentCost {t a b c d : Nat} (total : t = a+b+c+d) (small : t ≤ 29)
    (copyFirst : 38 ≤ t+a) (copySecond : 38 ≤ t+b) (copyThird : 38 ≤ t+c) :
    9 ≤ a ∧ 9 ≤ b ∧ 9 ≤ c ∧ d ≤ 2 := by
  omega
end PCX150
