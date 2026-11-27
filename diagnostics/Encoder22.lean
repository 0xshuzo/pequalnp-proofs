import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19061
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def encoder : Circuit :=
  ⟨[⟨.or, [15, 14]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.or, [11, 10]⟩,
    ⟨.or, [9, 19]⟩,
    ⟨.or, [18, 8]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [7, 6]⟩,
    ⟨.or, [5, 23]⟩,
    ⟨.or, [18, 4]⟩,
    ⟨.or, [24, 25]⟩,
    ⟨.or, [3, 23]⟩,
    ⟨.or, [19, 16]⟩,
    ⟨.or, [2, 27]⟩,
    ⟨.or, [28, 29]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [15, 1]⟩,
    ⟨.or, [31, 32]⟩,
    ⟨.or, [33, 34]⟩,
    ⟨.or, [35, 36]⟩], 0⟩

def outputAt (v : Fin 4) : Nat := ([37, 30, 26, 22] : List Nat).getD v.val 0

theorem encoderFit : Monotone2 encoder := by
  intro g hg
  have h : encoder.gates.all (fun z => (match z.op with | .or => true | _ => false) && decide (z.inputs.length ≤ 2)) = true := by decide +kernel
  have he := List.all_eq_true.mp h g hg
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 22 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16, (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false = Nat.testBit p.val v.val := by
  refine ⟨encoder, encoderFit, by decide, ?_⟩
  have h : ∀ v : Fin 4, ∀ p : Fin 16, (encoder.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD (outputAt v) false = Nat.testBit p.val v.val := by decide +kernel
  exact fun v => ⟨outputAt v, h v⟩
end PEqualNP.Outside.L_meta_19061
