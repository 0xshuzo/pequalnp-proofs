import PEqualNP.Defs

namespace RankWitness17719
open PEqualNP.CircuitLowerBounds
def C : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[25,3]⟩,⟨.and,[7,26]⟩,⟨.or,[5,6]⟩,⟨.or,[28,1]⟩,⟨.or,[27,12]⟩,⟨.or,[27,29]⟩,⟨.and,[30,31]⟩,⟨.or,[6,0]⟩,⟨.or,[33,2]⟩,⟨.and,[13,34]⟩,⟨.or,[32,35]⟩,⟨.or,[4,5]⟩,⟨.or,[37,0]⟩,⟨.and,[11,38]⟩,⟨.or,[36,39]⟩],40⟩

def good (j : Nat) (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs=[g.inputs.getD 0 0,g.inputs.getD 1 0] ∧
    g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 ∧ g.inputs.getD 0 0 < 25+j ∧ g.inputs.getD 1 0 < 25+j

instance (j : Nat) (g : Gate) : Decidable (good j g) := by unfold good; infer_instance

def rank (b : Bool) (i : Nat) : Nat := (if b then ([0,2,2,2,2,2,2,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,0,0,1,2,2,1,1,2,0,0,2,2,2,0,2,2] : List Nat) else [1,2,2,2,2,2,2,0,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,2,2,1,1,2,1,1,2,2,2,1,2,2]).getD i 2

def bounds (b : Bool) (j : Nat) (g : Gate) : Prop :=
  (g.op = .and → rank b (25+j) ≤ rank b (g.inputs.getD 0 0)+rank b (g.inputs.getD 1 0)) ∧
  (g.op = .or → rank b (25+j) ≤ min (rank b (g.inputs.getD 0 0)) (rank b (g.inputs.getD 1 0)))
instance (b : Bool) (j : Nat) (g : Gate) : Decidable (bounds b j g) := by unfold bounds; infer_instance

theorem good_gate (j : Nat) (g : Gate) (hg : C.gates[j]? = some g) : good j g := by
  obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp hg
  have hm : ∀ i : Fin C.gates.length, good i.val (C.gates[i.val]) := by decide +kernel
  simpa only [eq] using hm ⟨j,hj⟩

theorem bound_gate (b : Bool) (j : Nat) (g : Gate) (hg : C.gates[j]? = some g) : bounds b j g := by
  obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp hg
  have hm : ∀ s : Bool, ∀ i : Fin C.gates.length, bounds s i.val (C.gates[i.val]) := by decide +kernel
  simpa only [eq] using hm b ⟨j,hj⟩

end RankWitness17719

open RankWitness17719 in
set_option maxRecDepth 4096 in
theorem RankWitness17719.near : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (16 : ℕ) ∧ (25 : ℕ) ≤ x1.output ∧ x1.output < (25 : ℕ) + x1.size ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧ (∀ x2 ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ), (2064 : ℕ), (2080 : ℕ), (2049 : ℕ), (4128 : ℕ), (4160 : ℕ), (4098 : ℕ), (8256 : ℕ), (8193 : ℕ), (8196 : ℕ)], x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.false) = Bool.true) ∧ (∀ x2 ∈ [(1919 : ℕ), (2036 : ℕ), (3918 : ℕ), (4036 : ℕ), (5917 : ℕ), (6036 : ℕ), (7948 : ℕ), (8068 : ℕ), (10042 : ℕ), (10160 : ℕ), (12042 : ℕ), (14104 : ℕ), (14224 : ℕ), (16136 : ℕ), (16256 : ℕ)], x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.true) = Bool.false) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x4 < (25 : ℕ), x4 ≠ (0 : ℕ) → x4 ≠ (7 : ℕ) → x3 x4 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((25 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((25 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7)) := by
  refine ⟨C, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro j g hg
    have h := good_gate j g hg
    exact ⟨h.1,_,_,h.2⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro b
    refine ⟨rank b, ?_, ?_, ?_, ?_, ?_⟩
    · cases b <;> decide
    · cases b <;> decide
    · have h : ∀ (b : Bool) (i : Fin 25), i.val ≠ 0 → i.val ≠ 7 → rank b i.val = 2 := by decide +kernel
      intro i hi
      exact h b ⟨i,hi⟩
    · cases b <;> decide
    · intro i g a c hg he
      have h := bound_gate b i g hg
      simpa [bounds,he] using h
