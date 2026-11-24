import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3469_271
    (h1 : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)),
      2 ≤ q → N = q^2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ a b, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) →
      (PEqualNP.HeptadCover.incidences S).card = N * (q + 1) ∧
      ∀ f ∈ PEqualNP.HeptadCover.incidences S,
        ∀ g ∈ PEqualNP.HeptadCover.incidences S, f ≠ g →
          ∃ u ∈ (S f.2).erase f.1,
            ∃ l : Fin N, l ≠ g.2 ∧ g.1 ∈ S l ∧ u ∈ S l)
    (h2 : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      200 ≤ q → N = q^2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ a b, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) →
      PEqualNP.TopForm.IsAO2 (N+N) C →
      N+N ≤ C.output → C.output < N+N+C.size →
      (∃ g, C.gates[C.output - (N+N)]? = some g ∧
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      PEqualNP.GenericRejection.RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin N), Y.card ≤ q → PEqualNP.GenericRejection.IsFalseInput S X Y →
        C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false) →
      ∃ A B : Fin (100 * C.size + N) → Finset (Fin N),
        (∀ i, PEqualNP.GenericRejection.IsFalseInput S (A i) (B i)) ∧
        ∀ f ∈ PEqualNP.HeptadCover.incidences S, ∃ i,
          (S f.2).erase f.1 ⊆ A i ∧
          (∀ l : Fin N, l ≠ f.2 → f.1 ∈ S l → l ∈ B i)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q N S C hq hN hline hu hao hlow hhigh hgate hright hfalse
  obtain ⟨hcard, cross⟩ := h1 q N S (by omega) hN hline hu
  obtain ⟨A, B, hrect, hcover⟩ :=
    h2 q N S C hq hN hline hu hao hlow hhigh hgate hright hfalse
  let F := PEqualNP.HeptadCover.incidences S
  let idx (f : ↥F) := Classical.choose (hcover f.val f.property)
  have spec (f : ↥F) :
      (S f.val.2).erase f.val.1 ⊆ A (idx f) ∧
      (∀ l : Fin N, l ≠ f.val.2 → f.val.1 ∈ S l → l ∈ B (idx f)) :=
    Classical.choose_spec (hcover f.val f.property)
  have inj : Function.Injective idx := by
    intro f g heq
    by_contra hn
    have hne : f.val ≠ g.val := fun h => hn (Subtype.ext h)
    obtain ⟨u, huX, l, hlne, hrl, hul⟩ := cross f.val f.property g.val g.property hne
    have huA := (spec f).1 huX
    have hlB := (spec g).2 l hlne hrl
    rw [← heq] at hlB
    exact (Finset.disjoint_left.mp (hrect (idx f) l hlB)) hul huA
  have h := Fintype.card_le_of_injective idx inj
  change Fintype.card ↥F ≤ Fintype.card (Fin (100 * C.size + N)) at h
  rw [Fintype.card_coe, Fintype.card_fin] at h
  change (PEqualNP.HeptadCover.incidences S).card ≤ _ at h
  rw [hcard, Nat.mul_add, Nat.mul_one] at h
  omega
