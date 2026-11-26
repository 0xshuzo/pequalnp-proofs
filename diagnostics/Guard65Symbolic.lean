import PEqualNP.Defs

namespace Guard7832
open PEqualNP.CircuitLowerBounds PEqualNP.BlindGate
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev V := Fin 13
def C : Circuit := ⟨[
  ⟨.or,[1,2]⟩,
  ⟨.or,[26,4]⟩,
  ⟨.or,[27,10]⟩,
  ⟨.and,[14,28]⟩,
  ⟨.or,[2,3]⟩,
  ⟨.or,[30,5]⟩,
  ⟨.or,[31,11]⟩,
  ⟨.and,[15,32]⟩,
  ⟨.or,[3,4]⟩,
  ⟨.or,[34,6]⟩,
  ⟨.or,[35,12]⟩,
  ⟨.and,[16,36]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.or,[38,7]⟩,
  ⟨.or,[39,0]⟩,
  ⟨.and,[17,40]⟩,
  ⟨.or,[5,6]⟩,
  ⟨.or,[42,8]⟩,
  ⟨.or,[43,1]⟩,
  ⟨.and,[18,44]⟩,
  ⟨.or,[6,7]⟩,
  ⟨.or,[46,9]⟩,
  ⟨.or,[47,2]⟩,
  ⟨.and,[19,48]⟩,
  ⟨.or,[7,8]⟩,
  ⟨.or,[50,10]⟩,
  ⟨.or,[51,3]⟩,
  ⟨.and,[20,52]⟩,
  ⟨.or,[8,9]⟩,
  ⟨.or,[54,11]⟩,
  ⟨.or,[55,4]⟩,
  ⟨.and,[21,56]⟩,
  ⟨.or,[9,10]⟩,
  ⟨.or,[58,12]⟩,
  ⟨.or,[59,5]⟩,
  ⟨.and,[22,60]⟩,
  ⟨.or,[10,11]⟩,
  ⟨.or,[62,0]⟩,
  ⟨.or,[63,6]⟩,
  ⟨.and,[23,64]⟩,
  ⟨.or,[11,12]⟩,
  ⟨.or,[66,1]⟩,
  ⟨.or,[67,7]⟩,
  ⟨.and,[24,68]⟩,
  ⟨.or,[12,0]⟩,
  ⟨.or,[70,2]⟩,
  ⟨.or,[71,8]⟩,
  ⟨.and,[25,72]⟩,
  ⟨.or,[29,33]⟩,
  ⟨.or,[74,37]⟩,
  ⟨.or,[75,41]⟩,
  ⟨.or,[76,45]⟩,
  ⟨.or,[77,49]⟩,
  ⟨.or,[78,53]⟩,
  ⟨.or,[79,57]⟩,
  ⟨.or,[80,61]⟩,
  ⟨.or,[81,65]⟩,
  ⟨.or,[82,69]⟩,
  ⟨.or,[83,73]⟩,
  ⟨.or,[0,1]⟩,
  ⟨.or,[85,3]⟩,
  ⟨.or,[86,9]⟩,
  ⟨.or,[84,87]⟩,
  ⟨.or,[84,13]⟩,
  ⟨.and,[88,89]⟩],90⟩
def bank (x : V → Bool) (i : V) := x i || x (i+1) || x (i+3) || x (i+9)
def opp (x : V → Bool) (i : V) := !(bank x i)
def star (x y : V → Bool) (i : V) := y i && bank x i
def rest (x y : V → Bool) := star x y 1 || star x y 2 || star x y 3 || star x y 4 || star x y 5 || star x y 6 || star x y 7 || star x y 8 || star x y 9 || star x y 10 || star x y 11 || star x y 12
def o (p q : Bool) := GateOp.or.eval [p,q]
def a (p q : Bool) := GateOp.and.eval [p,q]
theorem or_test (p q : Bool) : o p q = (p || q) := by cases p <;> cases q <;> rfl
theorem and_test (p q : Bool) : a p q = (p && q) := by cases p <;> cases q <;> rfl
def circuitBank (x : V → Bool) (l : V) := o (o (o (x l) (x (l+1))) (x (l+3))) (x (l+9))
def circuitStar (x y : V → Bool) (l : V) := a (y l) (circuitBank x l)
def circuitRest (x y : V → Bool) := (o (o (o (o (o (o (o (o (o (o (o (circuitStar x y 1) (circuitStar x y 2)) (circuitStar x y 3)) (circuitStar x y 4)) (circuitStar x y 5)) (circuitStar x y 6)) (circuitStar x y 7)) (circuitStar x y 8)) (circuitStar x y 9)) (circuitStar x y 10)) (circuitStar x y 11)) (circuitStar x y 12))
theorem left_wire (x y : V → Bool) :
    wireValue C 26 (Fin.append x y) 88 = (rest x y || bank x 0) := by
  have h : wireValue C 26 (Fin.append x y) 88 = o (circuitRest x y) (circuitBank x 0) := rfl
  simpa only [circuitRest,circuitStar,circuitBank,rest,star,bank,or_test,and_test] using h
theorem right_wire (x y : V → Bool) :
    wireValue C 26 (Fin.append x y) 89 = (rest x y || y 0) := by
  have h : wireValue C 26 (Fin.append x y) 89 = o (circuitRest x y) (y 0) := rfl
  simpa only [circuitRest,circuitStar,circuitBank,rest,star,bank,or_test,and_test] using h
theorem silent (x : V → Bool) : rest x (opp x) = false := by
  have no (l : V) : star x (opp x) l = false := by
    unfold star opp
    cases bank x l <;> rfl
  simp [rest,no]
theorem oneMore : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (65 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (13 : ℕ) → Bool), (∀ (x8 : Fin (13 : ℕ)), x7 x8 = Bool.false → ∃ (x10 : Fin (13 : ℕ)), x1 x8 x10 ∧ x2 x7 x10 = Bool.true) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (Fin.append x7 (x2 x7)) (if x2 x7 (0 : Fin (13 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  dsimp only
  refine ⟨C,64,88,89,by decide,by decide +kernel,by decide +kernel,rfl,rfl,?_,?_⟩
  · decide +kernel
  · intro x _
    change wireValue C 26 (Fin.append x (opp x)) (if opp x 0 = true then 88 else 89) = false
    by_cases chosen : opp x 0 = true
    · rw [if_pos chosen,left_wire,silent]
      change (!bank x 0) = true at chosen
      simpa using chosen
    · rw [if_neg chosen,right_wire,silent]
      simpa using chosen
end Guard7832
