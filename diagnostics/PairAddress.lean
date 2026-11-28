import PEqualNP.Defs

namespace PEqualNP.Outside.Pcx177Pair

abbrev Form := Fin 256

def par (x y : Form) : Bool :=
  let v := x.val &&& y.val
  Bool.xor ((27030 : Nat).testBit (v % 16)) ((27030 : Nat).testBit (v / 16))

def legal (x : Form) : Bool :=
  let a := x.val % 16
  let b := x.val / 16
  a != 0 && b != 0 && (a &&& b) == 0

def plans : List (List Form) := [[18, 72, 90], [20, 40, 60], [33, 132, 165], [28, 36, 56], [24, 44, 52], [65, 130, 195], [26, 66, 88], [22, 24, 30, 40, 56], [20, 130, 150], [22, 26, 28, 44, 60], [36, 40, 44, 72, 104], [52, 56, 60, 88, 104], [18, 132, 150], [18, 20, 22, 36, 52], [52, 56, 60, 72, 120], [18, 20, 22, 104, 120], [20, 26, 30, 36, 52], [18, 28, 30, 44, 60], [20, 24, 28, 72, 88], [18, 24, 26, 40, 56], [40, 65, 105], [24, 66, 90], [33, 36, 37, 88, 120]]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem cover : ∀ u : Form, plans.any (fun p => p.all (fun x => !par u x)) = true := by
  decide +kernel

theorem hit : ∀ v : Form, plans.all (fun p => p.any (fun x => legal x && !par v x)) = true := by
  decide +kernel

theorem zeroFiber (u v : Form) : ∃ x : Form, legal x = true ∧ par u x = false ∧ par v x = false := by
  obtain ⟨p, hp, one⟩ := List.any_eq_true.mp (cover u)
  obtain ⟨x, hx, two⟩ := List.any_eq_true.mp (List.all_eq_true.mp (hit v) p hp)
  have aa := List.all_eq_true.mp one x hx
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at two aa
  exact ⟨x,two.1,aa,two.2⟩

/-- Every affine four-address scheme has a coincident pair at the zero board.
On boards supported in its two rows the relative address then has zero constant.
Some legal board in those two rows preserves both components of that equality. -/
theorem counterPair (atZero : Fin 5 → Fin 4) (first second : Fin 5 → Fin 5 → Form) :
    ∃ i j : Fin 5, i ≠ j ∧ atZero i = atZero j ∧
      ∃ x : Form, legal x = true ∧ par (first i j) x = false ∧ par (second i j) x = false := by
  obtain ⟨i,j,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt atZero (by decide)
  exact ⟨i,j,ne,eq,zeroFiber _ _⟩

end PEqualNP.Outside.Pcx177Pair
