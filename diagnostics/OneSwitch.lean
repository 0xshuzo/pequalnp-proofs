import PEqualNP.Defs

namespace Pcx177.RowAddress

/-- Four coefficients followed by an affine constant. -/
def bit (form : Fin 32) (row : Fin 16) : Bool :=
  Bool.xor (form.val.testBit 4)
    (Bool.xor ((form.val.testBit 0) && (row.val.testBit 0))
    (Bool.xor ((form.val.testBit 1) && (row.val.testBit 1))
    (Bool.xor ((form.val.testBit 2) && (row.val.testBit 2))
              ((form.val.testBit 3) && (row.val.testBit 3)))))

def addr (lo hi : Fin 32) (row : Fin 16) : Fin 4 :=
  if bit hi row then (if bit lo row then 3 else 2) else (if bit lo row then 1 else 0)

def pick (row : Fin 16) : Fin 4 :=
  if bit 3 row then addr 2 0 row else addr 8 17 row

theorem occupied : ∀ row : Fin 16, row ≠ 0 → row.val.testBit (pick row).val = true := by
  decide +kernel

theorem collision {a b : Fin 16} (ha : a ≠ 0) (hb : b ≠ 0) (e : pick a = pick b) :
    ∃ h : Fin 4, a.val.testBit h.val = true ∧ b.val.testBit h.val = true := by
  exact ⟨pick a,occupied a ha,by simpa only [e] using occupied b hb⟩

theorem noAffine : ∀ lo hi : Fin 32, ∃ row : Fin 16, row ≠ 0 ∧
    row.val.testBit (addr lo hi row).val = false := by
  decide +kernel

def side (test : Fin 32) (v : Bool) (lo hi : Fin 32) : Bool :=
  (List.finRange 16).all (fun row => row == 0 || bit test row != v ||
    row.val.testBit (addr lo hi row).val)

def hasLeaf (test : Fin 32) (v : Bool) : Bool :=
  (List.finRange 32).any (fun lo => (List.finRange 32).any (fun hi => side test v lo hi))

/-- Exactly the homogeneous tests involving two of the four cells work as
    the single switch of a total occupied-hole selector. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem firstCuts : ∀ f : Fin 16,
    (hasLeaf ⟨f.val,by omega⟩ false && hasLeaf ⟨f.val,by omega⟩ true) =
    ([3,5,6,9,10,12] : List Nat).contains f.val := by
  decide +kernel

end Pcx177.RowAddress
