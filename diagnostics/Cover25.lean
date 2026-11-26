import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20241_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [5, 11]⟩,
  ⟨.or, [3, 13]⟩,
  ⟨.or, [0, 16]⟩,
  ⟨.or, [4, 12]⟩,
  ⟨.or, [6, 14]⟩,
  ⟨.or, [0, 10]⟩,
  ⟨.or, [2, 20]⟩,
  ⟨.or, [1, 15]⟩,
  ⟨.or, [1, 9]⟩,
  ⟨.or, [18, 19]⟩,
  ⟨.or, [2, 10]⟩,
  ⟨.or, [19, 26]⟩,
  ⟨.or, [17, 20]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [15, 17]⟩,
  ⟨.or, [18, 30]⟩,
  ⟨.and, [21, 16]⟩,
  ⟨.and, [22, 23]⟩,
  ⟨.and, [24, 25]⟩,
  ⟨.and, [27, 28]⟩,
  ⟨.and, [29, 31]⟩,
  ⟨.or, [36, 35]⟩,
  ⟨.or, [37, 34]⟩,
  ⟨.or, [38, 33]⟩,
  ⟨.or, [39, 32]⟩], 40⟩

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

end PEqualNP.Outside.L_meta_20241_aux

theorem PEqualNP.Outside.L_meta_20241 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12147342212780283915 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  ⟨PEqualNP.Outside.L_meta_20241_aux.witness, PEqualNP.Outside.L_meta_20241_aux.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
