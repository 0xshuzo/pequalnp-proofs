import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20267_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [0, 6]⟩,
  ⟨.or, [4, 13]⟩,
  ⟨.or, [9, 17]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [3, 11]⟩,
  ⟨.or, [12, 20]⟩,
  ⟨.or, [15, 17]⟩,
  ⟨.or, [15, 0]⟩,
  ⟨.or, [14, 2]⟩,
  ⟨.or, [19, 22]⟩,
  ⟨.or, [20, 10]⟩,
  ⟨.or, [19, 24]⟩,
  ⟨.or, [6, 27]⟩,
  ⟨.or, [26, 9]⟩,
  ⟨.and, [28, 21]⟩,
  ⟨.or, [12, 25]⟩,
  ⟨.or, [1, 23]⟩,
  ⟨.or, [27, 10]⟩,
  ⟨.and, [16, 33]⟩,
  ⟨.or, [29, 22]⟩,
  ⟨.or, [29, 24]⟩,
  ⟨.or, [1, 36]⟩,
  ⟨.and, [18, 32]⟩,
  ⟨.and, [31, 37]⟩,
  ⟨.or, [38, 30]⟩,
  ⟨.and, [35, 5]⟩,
  ⟨.or, [41, 34]⟩,
  ⟨.or, [40, 42]⟩,
  ⟨.or, [39, 43]⟩], 44⟩

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

end PEqualNP.Outside.L_meta_20267_aux

theorem PEqualNP.Outside.L_meta_20267 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6799783216241292135 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_meta_20267_aux.witness, PEqualNP.Outside.L_meta_20267_aux.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
