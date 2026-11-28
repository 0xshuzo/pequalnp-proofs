import PEqualNP.Defs

namespace Split9806

def graph (x : Fin 14 → Bool) := (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def pins (l r : Nat) : Fin 14 → Bool := ![l.testBit 0,l.testBit 1,l.testBit 2,l.testBit 3,l.testBit 4,l.testBit 5,l.testBit 6,r.testBit 0,r.testBit 1,r.testBit 2,r.testBit 3,r.testBit 4,r.testBit 5,r.testBit 6]
def board (l r : Nat) := graph (pins l r)
def yes : Fin 7 → Nat × Nat := ![(1,8),(2,1),(4,2),(8,16),(16,64),(32,32),(64,4)]
theorem yesDiag : ∀ i, board (yes i).1 (yes i).2 = true := by decide +kernel
theorem yesCross : ∀ i j, i≠j → board (yes i).1 (yes j).2 ≠ true ∨ board (yes j).1 (yes i).2 ≠ true := by decide +kernel
def below (a b : Nat) := a &&& b = a
def avoidLeft : Fin 7 → Nat := ![78,117,59,39,105,83,29]
def avoidRight : Fin 7 → Nat := ![119,58,29,78,39,83,105]
theorem leftBad : ∀ j, board (avoidLeft j) (yes j).2 = false := by decide +kernel
theorem rightBad : ∀ j, board (yes j).1 (avoidRight j) = false := by decide +kernel
theorem leftOverlap : ∀ i j, i ≠ j →
  below (yes i).1 (avoidLeft j) ∨ below (yes j).1 (avoidLeft i) := by decide +kernel
theorem rightOverlap : ∀ i j, i ≠ j →
  below (yes i).2 (avoidRight j) ∨ below (yes j).2 (avoidRight i) := by decide +kernel

theorem sidePrice {n : Nat} (X Y Z : Fin 7 → Nat) (f : Nat → Nat → Bool)
    (hit : ∀ i, f (X i) (Y i) = true) (miss : ∀ i, f (Z i) (Y i) = false)
    (over : ∀ i j, i ≠ j → below (X i) (Z j) ∨ below (X j) (Z i))
    (w : Fin n → Nat → Bool)
    (up : ∀ i a b, below a b → w i a = true → w i b = true)
    (decode : ∀ a b y, (∀ i, w i a = true → w i b = true) → f a y = true → f b y = true) :
    7 ≤ n := by
  classical
  have sep (j : Fin 7) : ∃ i, w i (X j) = true ∧ w i (Z j) = false := by
    by_contra zero
    have order (i : Fin n) (one : w i (X j) = true) : w i (Z j) = true := by
      cases h : w i (Z j) with
      | false => exact False.elim (zero ⟨i,one,h⟩)
      | true => rfl
    have wild := decode (X j) (Z j) (Y j) order (hit j)
    rw [miss j] at wild
    contradiction
  let tag (j : Fin 7) : Fin n := (sep j).choose
  have facts (j : Fin 7) : w (tag j) (X j) = true ∧ w (tag j) (Z j) = false :=
    (sep j).choose_spec
  have inj : Function.Injective tag := by
    intro i j eq
    by_contra ne
    have hi := facts i
    have hj := facts j
    rw [←eq] at hj
    rcases over i j ne with ov|ov
    · have wild := up _ _ _ ov hi.1
      rw [hj.2] at wild
      contradiction
    · have wild := up _ _ _ ov hj.1
      rw [hi.2] at wild
      contradiction
  simpa using Fintype.card_le_of_injective tag inj

theorem cleanLeft {n : Nat} (w : Fin n → Nat → Bool)
    (up : ∀ i a b, below a b → w i a = true → w i b = true)
    (decode : ∀ a b y, (∀ i, w i a = true → w i b = true) →
      board a y = true → board b y = true) : 7 ≤ n :=
  sidePrice (fun i => (yes i).1) (fun i => (yes i).2) avoidLeft board
    yesDiag leftBad leftOverlap w up decode

theorem cleanRight {n : Nat} (w : Fin n → Nat → Bool)
    (up : ∀ i a b, below a b → w i a = true → w i b = true)
    (decode : ∀ a b y, (∀ i, w i a = true → w i b = true) →
      board y a = true → board y b = true) : 7 ≤ n :=
  sidePrice (fun i => (yes i).2) (fun i => (yes i).1) avoidRight (fun a y => board y a)
    yesDiag rightBad rightOverlap w up decode

end Split9806
