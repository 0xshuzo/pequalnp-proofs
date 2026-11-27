import PEqualNP.Defs

namespace Lpcx178Relation
abbrev Board := Fin 4 → Fin 32

def column (w : Fin 32) : Fin 11 :=
  if Bool.xor (w.val.testBit 0) (w.val.testBit 1) then
    if (w.val.testBit 2) then
      if (w.val.testBit 0) then
        2
      else
        5
    else
      if (w.val.testBit 3) then
        if (w.val.testBit 0) then
          3
        else
          6
      else
        if (w.val.testBit 4) then
          if (w.val.testBit 0) then
            4
          else
            7
        else
          0
  else
    if (w.val.testBit 0) then
      1
    else
      if Bool.xor (w.val.testBit 2) (w.val.testBit 3) then
        if (w.val.testBit 4) then
          if (w.val.testBit 2) then
            9
          else
            10
        else
          0
      else
        if (w.val.testBit 2) then
          8
        else
          0

def safe (i : Fin 6) : Fin 32 := ![0,1,2,4,8,16] i
def collision (i : Fin 11) : Fin 5 × Fin 5 :=
  ![(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)] i
def trueCollision (w : Fin 32) (c : Fin 11) : Prop :=
  (collision c).1 ≠ (collision c).2 ∧ w.val.testBit (collision c).1.val = true ∧
    w.val.testBit (collision c).2.val = true

theorem localZero : ∀ w, column w = 0 → ∃ i, safe i = w := by decide +kernel
theorem localHit : ∀ w, column w ≠ 0 → (collision (column w)).1 ≠ (collision (column w)).2 ∧
    w.val.testBit (collision (column w)).1.val = true ∧
    w.val.testBit (collision (column w)).2.val = true := by decide +kernel

def atCell (x : Board) (r : Fin 5) (h : Fin 4) := (x h).val.testBit r.val
def occupied (x : Board) (p : Fin 5) : Bool :=
  atCell x p 0 || atCell x p 1 || atCell x p 2 || atCell x p 3
def rowParity (x : Board) (p : Fin 5) : Bool :=
  Bool.xor (Bool.xor (atCell x p 0) (atCell x p 1)) (Bool.xor (atCell x p 2) (atCell x p 3))
def decode (x : Board) : Fin 5 :=
  if !(occupied x 0) then 0 else if !(occupied x 1) then 1 else
  if rowParity x 2 then (if rowParity x 3 then 4 else 3) else
  if Bool.xor (atCell x 2 2) (atCell x 2 3) then 3 else
  if Bool.xor (atCell x 2 1) (atCell x 2 3) then 3 else 2

theorem decoder : ∀ (i : Fin 4 → Fin 6) (h : Fin 4),
    atCell (fun h => safe (i h)) (decode (fun h => safe (i h))) h = false := by decide +kernel

def output (x : Board) : (Fin 4 × Fin 11) ⊕ Fin 5 :=
  if column (x 0) ≠ 0 then .inl (0,column (x 0)) else
  if column (x 1) ≠ 0 then .inl (1,column (x 1)) else
  if column (x 2) ≠ 0 then .inl (2,column (x 2)) else
  if column (x 3) ≠ 0 then .inl (3,column (x 3)) else .inr (decode x)

def failed (x : Board) : (Fin 4 × Fin 11) ⊕ Fin 5 → Prop
  | .inl (h,c) => trueCollision (x h) c
  | .inr p => ∀ h, atCell x p h = false

theorem allBoards (x : Board) : failed x (output x) := by
  unfold output
  split
  next h => exact localHit _ h
  split
  next h => exact localHit _ h
  split
  next h => exact localHit _ h
  split
  next h => exact localHit _ h
  next =>
    have z (h : Fin 4) : column (x h) = 0 := by
      fin_cases h <;> simp_all
    have ex (h : Fin 4) := localZero _ (z h)
    choose i hi using ex
    have equal : (fun h => safe (i h)) = x := funext hi
    change ∀ h, atCell x (decode x) h = false
    rw [← equal]
    exact decoder i

end Lpcx178Relation
