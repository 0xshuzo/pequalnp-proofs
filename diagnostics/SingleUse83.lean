import PEqualNP.Defs

namespace PhysicalSingleUse

open PEqualNP.ProofComplexity

theorem memD {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

-- resolution lines, newest first; a hint (i, j, v): the premises are entries i and j of the tail, pivot v
def chkR {V : Type} [DecidableEq V] (ax : Clause V → Bool) :
    List (Clause V × Option (ℕ × ℕ × V)) → Bool
  | [] => true
  | (R, none) :: t => ax R && chkR ax t
  | (R, some (i, j, v)) :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide ((v, true) ∈ (t.map Prod.fst).getD i ∅ ∧ (v, false) ∈ (t.map Prod.fst).getD j ∅ ∧
        R = ((t.map Prod.fst).getD i ∅).erase (v, true) ∪ ((t.map Prod.fst).getD j ∅).erase (v, false)) &&
      chkR ax t

theorem chkR_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkR ax l = true → IsDerivation F (l.map Prod.fst)
  | [], _ => IsDerivation.nil
  | (R, none) :: t, h => by
    simp only [chkR, Bool.and_eq_true] at h
    exact IsDerivation.ax (chkR_sound F ax hax t h.2) (hax R h.1)
  | (R, some (i, j, v)) :: t, h => by
    simp only [chkR, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, ht⟩ := h
    exact IsDerivation.res (chkR_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨v, h1, h2, h3⟩

-- Res(lin): the assignment check of a weakening runs over the variables vs only
def axPHP (m n : ℕ) (C : Clause (Fin m × Fin n)) : Bool :=
  decide (∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))) ||
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ j : Fin n, i ≠ i' ∧ C = {((i, j), false), ((i', j), false)})

theorem axPHP_sound (m n : ℕ) : ∀ C, axPHP m n C = true → C ∈ PHP m n := by
  intro C h
  simp only [axPHP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, hC⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨i, i', j, hne, hC⟩

def cert : List (Clause (Fin 4 × Fin 3) × Option (ℕ × ℕ × (Fin 4 × Fin 3))) := [
  (∅, some (0, 7, (1, 2))),
  ({((1, 2), true)}, some (0, 4, (1, 1))),
  ({((1, 1), true), ((1, 2), true)}, some (78, 0, (1, 0))),
  ({((1, 0), false)}, some (0, 1, (2, 2))),
  ({((2, 2), true), ((1, 0), false)}, some (33, 3, (1, 2))),
  ({((2, 2), false)}, some (7, 1, (3, 2))),
  ({((1, 1), false)}, some (11, 0, (3, 2))),
  ({((3, 2), false)}, some (24, 0, (1, 2))),
  ({((1, 2), false)}, some (0, 53, (3, 2))),
  ({((3, 2), true)}, some (0, 1, (3, 1))),
  ({((3, 1), true), ((3, 2), true)}, some (68, 9, (3, 0))),
  ({((3, 2), true), ((3, 1), false)}, some (0, 1, (2, 2))),
  ({((2, 2), true), ((3, 2), true), ((3, 1), false)}, some (35, 1, (2, 0))),
  ({((3, 2), true), ((2, 2), false)}, some (13, 0, (2, 0))),
  ({((3, 2), true), ((2, 0), false)}, some (0, 1, (0, 2))),
  ({((0, 2), true), ((3, 2), true), ((2, 0), false)}, some (37, 3, (0, 1))),
  ({((3, 2), true), ((0, 2), false)}, some (0, 1, (1, 1))),
  ({((1, 1), true), ((3, 2), true), ((0, 2), false)}, some (17, 1, (0, 1))),
  ({((3, 2), true), ((1, 1), false)}, some (36, 1, (3, 0))),
  ({((3, 2), true), ((0, 1), false)}, some (36, 0, (3, 0))),
  ({((3, 2), true), ((3, 0), false)}, some (0, 52, (2, 0))),
  ({((2, 0), true), ((3, 2), true), ((3, 0), false)}, some (0, 1, (0, 2))),
  ({((0, 2), true), ((2, 0), true), ((3, 0), false)}, some (36, 3, (0, 1))),
  ({((2, 0), true), ((3, 2), true), ((0, 2), false)}, some (0, 1, (1, 1))),
  ({((1, 1), true), ((2, 0), true), ((3, 2), true), ((0, 2), false)}, some (10, 1, (0, 1))),
  ({((2, 0), true), ((1, 1), false)}, some (28, 1, (2, 2))),
  ({((2, 0), true), ((0, 1), false)}, some (30, 0, (2, 2))),
  ({((2, 0), true), ((2, 2), false)}, some (0, 36, (1, 2))),
  ({((1, 2), true), ((2, 0), true), ((2, 2), false)}, some (0, 3, (3, 2))),
  ({((1, 2), true), ((2, 0), true), ((3, 2), true), ((2, 2), false)}, some (19, 0, (0, 1))),
  ({((1, 2), true), ((2, 0), true), ((0, 1), false)}, some (27, 0, (1, 0))),
  ({((1, 2), true), ((2, 0), true), ((1, 0), false)}, some (12, 0, (3, 2))),
  ({((1, 2), true), ((3, 2), false)}, some (0, 28, (2, 2))),
  ({((1, 2), true), ((2, 2), true), ((3, 2), false)}, some (7, 0, (0, 1))),
  ({((1, 2), true), ((2, 2), true), ((0, 1), false)}, some (23, 3, (1, 0))),
  ({((0, 1), true), ((1, 1), true), ((3, 2), true), ((0, 2), false)}, some (0, 30, (1, 2))),
  ({((0, 1), true), ((1, 1), true), ((1, 2), true), ((3, 2), true)}, some (44, 0, (1, 0))),
  ({((0, 1), true), ((1, 2), true), ((3, 2), true), ((1, 0), false)}, some (0, 11, (2, 2))),
  ({((1, 2), true), ((2, 2), true), ((1, 0), false)}, some (0, 37, (2, 0))),
  ({((1, 2), true), ((2, 0), true), ((2, 2), true), ((1, 0), false)}, some (4, 0, (3, 2))),
  ({((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 2), false)}, some (0, 16, (0, 1))),
  ({((0, 1), true), ((1, 2), true), ((2, 2), true), ((3, 2), false)}, some (0, 21, (0, 2))),
  ({((0, 1), true), ((0, 2), true), ((1, 2), true), ((2, 2), true)}, some (8, 0, (1, 1))),
  ({((0, 1), true), ((0, 2), true), ((2, 2), true), ((1, 1), false)}, some (10, 9, (2, 0))),
  ({((1, 2), true), ((2, 0), true), ((3, 2), true), ((1, 0), false)}, some (0, 29, (3, 0))),
  ({((1, 2), true), ((2, 0), true), ((3, 0), true), ((3, 2), true)}, some (33, 0, (3, 1))),
  ({((1, 2), true), ((2, 0), true), ((3, 0), true), ((3, 2), true), ((3, 1), false)}, some (1, 0, (2, 2))),
  ({((1, 2), true), ((3, 0), true), ((3, 2), true), ((2, 2), false)}, some (1, 8, (0, 1))),
  ({((2, 0), true), ((2, 2), true), ((3, 1), false)}, some (31, 18, (2, 1))),
  ({((0, 1), true), ((1, 2), true), ((3, 2), true), ((2, 2), false)}, some (0, 15, (0, 2))),
  ({((0, 1), true), ((0, 2), true), ((1, 2), true), ((3, 2), true)}, some (0, 1, (1, 1))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true)}, some (29, 8, (1, 0))),
  ({((0, 1), true), ((0, 2), true), ((3, 2), true), ((1, 1), false)}, some (2, 6, (3, 0))),
  ({((0, 1), true), ((0, 2), true), ((2, 0), false)}, some (28, 23, (0, 0))),
  ({((2, 0), true), ((2, 2), true), ((1, 1), false)}, some (25, 15, (2, 1))),
  ({((3, 0), true), ((3, 2), true), ((1, 1), false)}, some (23, 12, (3, 1))),
  ({((3, 0), true), ((3, 2), true), ((0, 1), false)}, some (22, 12, (3, 1))),
  ({((2, 0), true), ((2, 2), true), ((0, 1), false)}, some (22, 13, (2, 1))),
  ({((1, 0), true), ((1, 2), true), ((0, 1), false)}, some (22, 13, (1, 1))),
  ({((0, 1), true), ((0, 2), true), ((3, 0), false)}, some (22, 15, (0, 0))),
  ({((0, 1), true), ((0, 2), true), ((1, 0), false)}, some (21, 17, (0, 0))),
  ({((2, 2), false), ((3, 2), false)}, none),
  ({((1, 2), false), ((3, 2), false)}, none),
  ({((0, 2), false), ((3, 2), false)}, none),
  ({((1, 2), false), ((2, 2), false)}, none),
  ({((0, 2), false), ((2, 2), false)}, none),
  ({((0, 2), false), ((1, 2), false)}, none),
  ({((2, 1), false), ((3, 1), false)}, none),
  ({((1, 1), false), ((3, 1), false)}, none),
  ({((0, 1), false), ((3, 1), false)}, none),
  ({((1, 1), false), ((2, 1), false)}, none),
  ({((0, 1), false), ((2, 1), false)}, none),
  ({((0, 1), false), ((1, 1), false)}, none),
  ({((2, 0), false), ((3, 0), false)}, none),
  ({((1, 0), false), ((3, 0), false)}, none),
  ({((0, 0), false), ((3, 0), false)}, none),
  ({((1, 0), false), ((2, 0), false)}, none),
  ({((0, 0), false), ((2, 0), false)}, none),
  ({((0, 0), false), ((1, 0), false)}, none),
  ({((3, 0), true), ((3, 1), true), ((3, 2), true)}, none),
  ({((2, 0), true), ((2, 1), true), ((2, 2), true)}, none),
  ({((1, 0), true), ((1, 1), true), ((1, 2), true)}, none),
  ({((0, 0), true), ((0, 1), true), ((0, 2), true)}, none)
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hc : chkR (axPHP 4 3) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hm : (∅ : Clause (Fin 4 × Fin 3)) ∈ cert.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hl : (cert.map Prod.fst).length ≤ 83 := by decide +kernel


abbrev LocalV := Fin 4 × Fin 3
abbrev LocalLine := Clause LocalV × Option (ℕ × ℕ × LocalV)
def usedNegative : List LocalLine → List (Clause LocalV)
  | [] => []
  | (_, none) :: tail => usedNegative tail
  | (_, some (_, j, _)) :: tail => (tail.map Prod.fst).getD j ∅ :: usedNegative tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem everyCollisionOnce : ∀ i k : Fin 4, i ≠ k → ∀ j : Fin 3,
    (usedNegative cert).count {((i,j),false), ((k,j),false)} = 1 := by decide +kernel

end PhysicalSingleUse

theorem PhysicalSingleUse.upper : ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 83 := by
  exact ⟨PhysicalSingleUse.cert.map Prod.fst, ⟨PhysicalSingleUse.chkR_sound _ (PhysicalSingleUse.axPHP 4 3) (PhysicalSingleUse.axPHP_sound 4 3) _ PhysicalSingleUse.hc, PhysicalSingleUse.hm⟩, PhysicalSingleUse.hl⟩
