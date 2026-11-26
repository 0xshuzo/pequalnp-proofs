import PEqualNP.Defs

namespace L151Witness

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


def axPHP (m n : ℕ) (C : Clause (Fin m × Fin n)) : Bool :=
  decide (∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))) ||
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ j : Fin n, i ≠ i' ∧ C = {((i, j), false), ((i', j), false)})

theorem axPHP_sound (m n : ℕ) : ∀ C, axPHP m n C = true → C ∈ PHP m n := by
  intro C h
  simp only [axPHP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, hC⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨i, i', j, hne, hC⟩

abbrev V := Fin 4 × Fin 3
abbrev Hint := Option (ℕ × ℕ × V)

def cert : List (Clause V × Hint) := [
  (∅, some (0, 22, (3, 0))),
  ({((3, 0), true)}, some (0, 9, (3, 1))),
  ({((3, 0), true), ((3, 1), true)}, some (51, 0, (3, 2))),
  ({((3, 2), false)}, some (0, 32, (2, 2))),
  ({((2, 2), true), ((3, 2), false)}, some (0, 32, (1, 2))),
  ({((1, 2), true), ((2, 2), true), ((3, 2), false)}, some (2, 0, (0, 0))),
  ({((0, 0), false), ((1, 2), true), ((2, 2), true)}, some (11, 0, (1, 1))),
  ({((0, 0), false), ((1, 1), false), ((2, 2), true)}, some (11, 37, (2, 1))),
  ({((0, 0), true), ((1, 2), true), ((2, 2), true), ((3, 2), false)}, some (0, 29, (0, 2))),
  ({((0, 0), true), ((0, 2), true), ((1, 2), true), ((2, 2), true)}, some (20, 0, (1, 0))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), false), ((2, 2), true)}, some (11, 23, (2, 1))),
  ({((3, 1), false)}, some (0, 30, (2, 1))),
  ({((2, 1), true), ((3, 1), false)}, some (0, 31, (0, 1))),
  ({((0, 1), true), ((2, 1), true), ((3, 1), false)}, some (0, 29, (1, 1))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true)}, some (0, 5, (0, 2))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((2, 1), true)}, some (41, 0, (0, 0))),
  ({((0, 0), false), ((1, 1), true), ((2, 1), true)}, some (2, 0, (2, 2))),
  ({((0, 0), false), ((1, 1), true), ((2, 2), false)}, some (0, 21, (1, 2))),
  ({((0, 0), false), ((1, 1), true), ((1, 2), true)}, some (37, 34, (1, 0))),
  ({((0, 0), false), ((2, 1), true), ((2, 2), true)}, some (35, 32, (2, 0))),
  ({((0, 2), false), ((1, 1), true), ((2, 1), true)}, some (14, 0, (1, 0))),
  ({((0, 2), false), ((1, 0), false), ((2, 1), true)}, some (0, 18, (2, 2))),
  ({((1, 0), false), ((2, 1), true), ((2, 2), true)}, some (32, 28, (2, 0))),
  ({((3, 0), false)}, some (0, 25, (1, 0))),
  ({((1, 0), true), ((3, 0), false)}, some (0, 25, (0, 0))),
  ({((0, 0), true), ((1, 0), true), ((3, 0), false)}, some (0, 22, (2, 0))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true)}, some (0, 5, (2, 1))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 1), true)}, some (27, 0, (2, 2))),
  ({((0, 0), true), ((1, 0), true), ((2, 2), false)}, some (0, 11, (0, 2))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((2, 2), false)}, some (0, 9, (1, 2))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true)}, some (26, 0, (0, 1))),
  ({((0, 1), false), ((1, 0), true), ((1, 2), true)}, some (24, 15, (1, 1))),
  ({((0, 0), true), ((1, 0), true), ((2, 1), false)}, some (0, 12, (1, 1))),
  ({((0, 0), true), ((1, 0), true), ((1, 1), true), ((2, 1), false)}, some (0, 1, (0, 2))),
  ({((0, 0), true), ((0, 2), true), ((2, 1), false)}, some (22, 11, (0, 1))),
  ({((0, 2), false), ((1, 0), true), ((1, 1), true)}, some (20, 5, (1, 2))),
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
  ({((0, 0), true), ((0, 1), true), ((0, 2), true)}, none)]

def isColl (c : Clause V) : Bool :=
  decide (∃ i : Fin 4, ∃ j : Fin 4, ∃ h : Fin 3, i ≠ j ∧ c = {((i,h),false),((j,h),false)})

def collReads : List (Clause V × Hint) → Nat
  | [] => 0
  | (_, none) :: t => collReads t
  | (_, some (_, j, _)) :: t =>
      collReads t + if isColl ((t.map Prod.fst).getD j ∅) then 1 else 0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem counts : cert.length = 58 ∧ collReads cert = 21 := by decide +kernel

theorem derivation : IsRefutation (PHP 4 3) (cert.map Prod.fst) :=
  ⟨chkR_sound _ (axPHP 4 3) (axPHP_sound 4 3) _ (by decide +kernel), by decide +kernel⟩

end L151Witness

theorem L151Witness.witness : ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 58 := by
  exact ⟨L151Witness.cert.map Prod.fst, L151Witness.derivation, by simpa only [List.length_map, L151Witness.counts.1] using (show (58 : Nat) ≤ 58 by decide)⟩
