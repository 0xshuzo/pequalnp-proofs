import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19985_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 9]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [1, 19]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [16, 21]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [23, 11]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [25, 10]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [27, 28]⟩, ⟨.and, [26, 29]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [10, 31]⟩, ⟨.and, [3, 32]⟩, ⟨.or, [30, 33]⟩, ⟨.or, [24, 34]⟩, ⟨.or, [22, 35]⟩, ⟨.or, [8, 17]⟩, ⟨.and, [0, 37]⟩, ⟨.or, [12, 15]⟩, ⟨.and, [1, 39]⟩, ⟨.or, [38, 40]⟩, ⟨.or, [36, 41]⟩], 42⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9891717104032518705 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19985_aux

theorem PEqualNP.Outside.L_meta_19985 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9891717104032518705 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19985_aux.main
