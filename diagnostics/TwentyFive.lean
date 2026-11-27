import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20236_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [9, 5]⟩,
  ⟨.or, [15, 2]⟩,
  ⟨.or, [17, 16]⟩,
  ⟨.or, [10, 3]⟩,
  ⟨.or, [13, 7]⟩,
  ⟨.or, [0, 4]⟩,
  ⟨.or, [12, 21]⟩,
  ⟨.or, [17, 19]⟩,
  ⟨.or, [11, 22]⟩,
  ⟨.and, [12, 0]⟩,
  ⟨.or, [14, 1]⟩,
  ⟨.or, [8, 6]⟩,
  ⟨.or, [4, 18]⟩,
  ⟨.or, [1, 11]⟩,
  ⟨.or, [16, 29]⟩,
  ⟨.and, [26, 22]⟩,
  ⟨.and, [23, 30]⟩,
  ⟨.or, [19, 24]⟩,
  ⟨.or, [28, 14]⟩,
  ⟨.and, [27, 34]⟩,
  ⟨.or, [35, 32]⟩,
  ⟨.and, [20, 33]⟩,
  ⟨.or, [31, 37]⟩,
  ⟨.or, [38, 36]⟩,
  ⟨.or, [39, 25]⟩], 40⟩

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

end PEqualNP.Outside.L_meta_20236_aux

theorem PEqualNP.Outside.L_meta_20236 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2072365430907573360 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  ⟨PEqualNP.Outside.L_meta_20236_aux.witness, PEqualNP.Outside.L_meta_20236_aux.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
