import PEqualNP.Defs

namespace Split9806

def graph (x : Fin 14 → Bool) := (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def pins (l r : Nat) : Fin 14 → Bool := ![l.testBit 0,l.testBit 1,l.testBit 2,l.testBit 3,l.testBit 4,l.testBit 5,l.testBit 6,r.testBit 0,r.testBit 1,r.testBit 2,r.testBit 3,r.testBit 4,r.testBit 5,r.testBit 6]
def board (l r : Nat) := graph (pins l r)
def yes : Fin 7 → Nat × Nat := ![(1,8),(2,1),(4,2),(8,16),(16,64),(32,32),(64,4)]
theorem yesDiag : ∀ i, board (yes i).1 (yes i).2 = true := by decide +kernel
theorem yesCross : ∀ i j, i≠j → board (yes i).1 (yes j).2 ≠ true ∨ board (yes j).1 (yes i).2 ≠ true := by decide +kernel
def no : Fin 35 → Nat × Nat := ![(0,127),(1,119),(64,105),(65,97),(33,83),(8,78),(72,72),(9,70),(41,66),(97,65),(105,64),(2,58),(3,50),(66,40),(17,39),(19,34),(81,33),(83,32),(4,29),(6,24),(5,21),(35,18),(37,17),(39,16),(12,12),(10,10),(68,9),(78,8),(25,6),(21,5),(29,4),(49,3),(59,2),(117,1),(127,0)]
theorem noDiag : ∀ i, board (no i).1 (no i).2 = false := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem noCross : ∀ i j, i≠j → board (no i).1 (no j).2 ≠ false ∨ board (no j).1 (no i).2 ≠ false := by decide +kernel

theorem price {k b : Nat} {t : Bool} {p : Fin k → Nat × Nat}
    (diag : ∀ i,board (p i).1 (p i).2=t)
    (cross : ∀ i j,i≠j → board (p i).1 (p j).2≠t ∨ board (p j).1 (p i).2≠t)
    (L R : Fin b → Nat → Prop)
    (safe : ∀ c l r,L c l → R c r → board l r=t)
    (cover : ∀ l r,board l r=t → ∃ c,L c l ∧ R c r) : k≤b := by
  classical
  have each (i : Fin k) := cover (p i).1 (p i).2 (diag i)
  let tag (i : Fin k) := (each i).choose
  have hit (i : Fin k) : L (tag i) (p i).1 ∧ R (tag i) (p i).2 := (each i).choose_spec
  have inj : Function.Injective tag := by
    intro i j eq
    by_contra ne
    have a := hit i
    have d := hit j
    rw [←eq] at d
    rcases cross i j ne with h|h
    · exact h (safe _ _ _ a.1 d.2)
    · exact h (safe _ _ _ d.1 a.2)
  simpa using Fintype.card_le_of_injective tag inj

theorem both {k m : Nat} (L R : Fin k → Nat → Prop) (P Q : Fin m → Nat → Prop)
    (one : ∀ l r,board l r=true ↔ ∃ i,L i l ∧ R i r)
    (zero : ∀ l r,board l r=false ↔ ∃ j,P j l ∧ Q j r) : 7≤k ∧ 35≤m := by
  exact ⟨price yesDiag yesCross L R (fun i l r a b => (one l r).2 ⟨i,a,b⟩)
      (fun l r => (one l r).1),
    price noDiag noCross P Q (fun i l r a b => (zero l r).2 ⟨i,a,b⟩)
      (fun l r => (zero l r).1)⟩

end Split9806
