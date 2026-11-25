import PEqualNP.Defs

namespace Near2620
open PEqualNP.CircuitLowerBounds
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def C : Circuit := ⟨[
  ⟨.or,[0,1]⟩,
  ⟨.or,[26,3]⟩,
  ⟨.or,[27,9]⟩,
  ⟨.and,[13,28]⟩,
  ⟨.or,[1,2]⟩,
  ⟨.or,[30,4]⟩,
  ⟨.or,[31,10]⟩,
  ⟨.and,[14,32]⟩,
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
  ⟨.or,[2,3]⟩,
  ⟨.or,[85,5]⟩,
  ⟨.or,[86,11]⟩,
  ⟨.or,[84,15]⟩,
  ⟨.or,[84,87]⟩,
  ⟨.and,[88,89]⟩],90⟩

def o (p q : Bool) := GateOp.or.eval [p,q]
def a (p q : Bool) := GateOp.and.eval [p,q]

theorem oT (p q : Bool) : o p q=true ↔ p=true ∨ q=true := by cases p <;> cases q <;> decide
theorem aT (p q : Bool) : a p q=true ↔ p=true ∧ q=true := by cases p <;> cases q <;> decide
theorem bridge (h p q : Bool) : a (o h p) (o h q) = o h (a p q) := by
  cases h <;> cases p <;> cases q <;> decide


def bank (x : Fin 13 → Bool) (l : Fin 13) :=
  o (o (o (x l) (x (l+1))) (x (l+3))) (x (l+9))
def star (x y : Fin 13 → Bool) (l : Fin 13) := a (y l) (bank x l)
def rest (x y : Fin 13 → Bool) := o (o (o (o (o (o (o (o (o (o (o (star x y 0) (star x y 1)) (star x y 3)) (star x y 4)) (star x y 5)) (star x y 6)) (star x y 7)) (star x y 8)) (star x y 9)) (star x y 10)) (star x y 11)) (star x y 12)

theorem formula (x y : Fin 13 → Bool) :
    C.eval (List.ofFn (fun i : Fin (13+13) => Fin.addCases x y i)) =
      a (o (rest x y) (y 2)) (o (rest x y) (bank x 2)) := by
  let step := fun (b : List Bool) (g : Gate) => b ++ [g.op.eval (g.inputs.map (fun i => b.getD i false))]
  let u26 := o (x 0) (x 1)
  let u27 := o (u26) (x 3)
  let u28 := o (u27) (x 9)
  let u29 := a (y 0) (u28)
  let u30 := o (x 1) (x 2)
  let u31 := o (u30) (x 4)
  let u32 := o (u31) (x 10)
  let u33 := a (y 1) (u32)
  let u34 := o (x 3) (x 4)
  let u35 := o (u34) (x 6)
  let u36 := o (u35) (x 12)
  let u37 := a (y 3) (u36)
  let u38 := o (x 4) (x 5)
  let u39 := o (u38) (x 7)
  let u40 := o (u39) (x 0)
  let u41 := a (y 4) (u40)
  let u42 := o (x 5) (x 6)
  let u43 := o (u42) (x 8)
  let u44 := o (u43) (x 1)
  let u45 := a (y 5) (u44)
  let u46 := o (x 6) (x 7)
  let u47 := o (u46) (x 9)
  let u48 := o (u47) (x 2)
  let u49 := a (y 6) (u48)
  let u50 := o (x 7) (x 8)
  let u51 := o (u50) (x 10)
  let u52 := o (u51) (x 3)
  let u53 := a (y 7) (u52)
  let u54 := o (x 8) (x 9)
  let u55 := o (u54) (x 11)
  let u56 := o (u55) (x 4)
  let u57 := a (y 8) (u56)
  let u58 := o (x 9) (x 10)
  let u59 := o (u58) (x 12)
  let u60 := o (u59) (x 5)
  let u61 := a (y 9) (u60)
  let u62 := o (x 10) (x 11)
  let u63 := o (u62) (x 0)
  let u64 := o (u63) (x 6)
  let u65 := a (y 10) (u64)
  let u66 := o (x 11) (x 12)
  let u67 := o (u66) (x 1)
  let u68 := o (u67) (x 7)
  let u69 := a (y 11) (u68)
  let u70 := o (x 12) (x 0)
  let u71 := o (u70) (x 2)
  let u72 := o (u71) (x 8)
  let u73 := a (y 12) (u72)
  let u74 := o (u29) (u33)
  let u75 := o (u74) (u37)
  let u76 := o (u75) (u41)
  let u77 := o (u76) (u45)
  let u78 := o (u77) (u49)
  let u79 := o (u78) (u53)
  let u80 := o (u79) (u57)
  let u81 := o (u80) (u61)
  let u82 := o (u81) (u65)
  let u83 := o (u82) (u69)
  let u84 := o (u83) (u73)
  let u85 := o (x 2) (x 3)
  let u86 := o (u85) (x 5)
  let u87 := o (u86) (x 11)
  let u88 := o (u84) (y 2)
  let u89 := o (u84) (u87)
  let u90 := a (u88) (u89)
  let values : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,u26,u27,u28,u29,u30,u31,u32,u33,u34,u35,u36,u37,u38,u39,u40,u41,u42,u43,u44,u45,u46,u47,u48,u49,u50,u51,u52,u53,u54,u55,u56,u57,u58,u59,u60,u61,u62,u63,u64,u65,u66,u67,u68,u69,u70,u71,u72,u73,u74,u75,u76,u77,u78,u79,u80,u81,u82,u83,u84,u85,u86,u87,u88,u89,u90]
  have h26 : step (values.take 26) (⟨.or,[0,1]⟩ : Gate) = values.take 27 := by rfl
  have h27 : step (values.take 27) (⟨.or,[26,3]⟩ : Gate) = values.take 28 := by rfl
  have h28 : step (values.take 28) (⟨.or,[27,9]⟩ : Gate) = values.take 29 := by rfl
  have h29 : step (values.take 29) (⟨.and,[13,28]⟩ : Gate) = values.take 30 := by rfl
  have h30 : step (values.take 30) (⟨.or,[1,2]⟩ : Gate) = values.take 31 := by rfl
  have h31 : step (values.take 31) (⟨.or,[30,4]⟩ : Gate) = values.take 32 := by rfl
  have h32 : step (values.take 32) (⟨.or,[31,10]⟩ : Gate) = values.take 33 := by rfl
  have h33 : step (values.take 33) (⟨.and,[14,32]⟩ : Gate) = values.take 34 := by rfl
  have h34 : step (values.take 34) (⟨.or,[3,4]⟩ : Gate) = values.take 35 := by rfl
  have h35 : step (values.take 35) (⟨.or,[34,6]⟩ : Gate) = values.take 36 := by rfl
  have h36 : step (values.take 36) (⟨.or,[35,12]⟩ : Gate) = values.take 37 := by rfl
  have h37 : step (values.take 37) (⟨.and,[16,36]⟩ : Gate) = values.take 38 := by rfl
  have h38 : step (values.take 38) (⟨.or,[4,5]⟩ : Gate) = values.take 39 := by rfl
  have h39 : step (values.take 39) (⟨.or,[38,7]⟩ : Gate) = values.take 40 := by rfl
  have h40 : step (values.take 40) (⟨.or,[39,0]⟩ : Gate) = values.take 41 := by rfl
  have h41 : step (values.take 41) (⟨.and,[17,40]⟩ : Gate) = values.take 42 := by rfl
  have h42 : step (values.take 42) (⟨.or,[5,6]⟩ : Gate) = values.take 43 := by rfl
  have h43 : step (values.take 43) (⟨.or,[42,8]⟩ : Gate) = values.take 44 := by rfl
  have h44 : step (values.take 44) (⟨.or,[43,1]⟩ : Gate) = values.take 45 := by rfl
  have h45 : step (values.take 45) (⟨.and,[18,44]⟩ : Gate) = values.take 46 := by rfl
  have h46 : step (values.take 46) (⟨.or,[6,7]⟩ : Gate) = values.take 47 := by rfl
  have h47 : step (values.take 47) (⟨.or,[46,9]⟩ : Gate) = values.take 48 := by rfl
  have h48 : step (values.take 48) (⟨.or,[47,2]⟩ : Gate) = values.take 49 := by rfl
  have h49 : step (values.take 49) (⟨.and,[19,48]⟩ : Gate) = values.take 50 := by rfl
  have h50 : step (values.take 50) (⟨.or,[7,8]⟩ : Gate) = values.take 51 := by rfl
  have h51 : step (values.take 51) (⟨.or,[50,10]⟩ : Gate) = values.take 52 := by rfl
  have h52 : step (values.take 52) (⟨.or,[51,3]⟩ : Gate) = values.take 53 := by rfl
  have h53 : step (values.take 53) (⟨.and,[20,52]⟩ : Gate) = values.take 54 := by rfl
  have h54 : step (values.take 54) (⟨.or,[8,9]⟩ : Gate) = values.take 55 := by rfl
  have h55 : step (values.take 55) (⟨.or,[54,11]⟩ : Gate) = values.take 56 := by rfl
  have h56 : step (values.take 56) (⟨.or,[55,4]⟩ : Gate) = values.take 57 := by rfl
  have h57 : step (values.take 57) (⟨.and,[21,56]⟩ : Gate) = values.take 58 := by rfl
  have h58 : step (values.take 58) (⟨.or,[9,10]⟩ : Gate) = values.take 59 := by rfl
  have h59 : step (values.take 59) (⟨.or,[58,12]⟩ : Gate) = values.take 60 := by rfl
  have h60 : step (values.take 60) (⟨.or,[59,5]⟩ : Gate) = values.take 61 := by rfl
  have h61 : step (values.take 61) (⟨.and,[22,60]⟩ : Gate) = values.take 62 := by rfl
  have h62 : step (values.take 62) (⟨.or,[10,11]⟩ : Gate) = values.take 63 := by rfl
  have h63 : step (values.take 63) (⟨.or,[62,0]⟩ : Gate) = values.take 64 := by rfl
  have h64 : step (values.take 64) (⟨.or,[63,6]⟩ : Gate) = values.take 65 := by rfl
  have h65 : step (values.take 65) (⟨.and,[23,64]⟩ : Gate) = values.take 66 := by rfl
  have h66 : step (values.take 66) (⟨.or,[11,12]⟩ : Gate) = values.take 67 := by rfl
  have h67 : step (values.take 67) (⟨.or,[66,1]⟩ : Gate) = values.take 68 := by rfl
  have h68 : step (values.take 68) (⟨.or,[67,7]⟩ : Gate) = values.take 69 := by rfl
  have h69 : step (values.take 69) (⟨.and,[24,68]⟩ : Gate) = values.take 70 := by rfl
  have h70 : step (values.take 70) (⟨.or,[12,0]⟩ : Gate) = values.take 71 := by rfl
  have h71 : step (values.take 71) (⟨.or,[70,2]⟩ : Gate) = values.take 72 := by rfl
  have h72 : step (values.take 72) (⟨.or,[71,8]⟩ : Gate) = values.take 73 := by rfl
  have h73 : step (values.take 73) (⟨.and,[25,72]⟩ : Gate) = values.take 74 := by rfl
  have h74 : step (values.take 74) (⟨.or,[29,33]⟩ : Gate) = values.take 75 := by rfl
  have h75 : step (values.take 75) (⟨.or,[74,37]⟩ : Gate) = values.take 76 := by rfl
  have h76 : step (values.take 76) (⟨.or,[75,41]⟩ : Gate) = values.take 77 := by rfl
  have h77 : step (values.take 77) (⟨.or,[76,45]⟩ : Gate) = values.take 78 := by rfl
  have h78 : step (values.take 78) (⟨.or,[77,49]⟩ : Gate) = values.take 79 := by rfl
  have h79 : step (values.take 79) (⟨.or,[78,53]⟩ : Gate) = values.take 80 := by rfl
  have h80 : step (values.take 80) (⟨.or,[79,57]⟩ : Gate) = values.take 81 := by rfl
  have h81 : step (values.take 81) (⟨.or,[80,61]⟩ : Gate) = values.take 82 := by rfl
  have h82 : step (values.take 82) (⟨.or,[81,65]⟩ : Gate) = values.take 83 := by rfl
  have h83 : step (values.take 83) (⟨.or,[82,69]⟩ : Gate) = values.take 84 := by rfl
  have h84 : step (values.take 84) (⟨.or,[83,73]⟩ : Gate) = values.take 85 := by rfl
  have h85 : step (values.take 85) (⟨.or,[2,3]⟩ : Gate) = values.take 86 := by rfl
  have h86 : step (values.take 86) (⟨.or,[85,5]⟩ : Gate) = values.take 87 := by rfl
  have h87 : step (values.take 87) (⟨.or,[86,11]⟩ : Gate) = values.take 88 := by rfl
  have h88 : step (values.take 88) (⟨.or,[84,15]⟩ : Gate) = values.take 89 := by rfl
  have h89 : step (values.take 89) (⟨.or,[84,87]⟩ : Gate) = values.take 90 := by rfl
  have h90 : step (values.take 90) (⟨.and,[88,89]⟩ : Gate) = values.take 91 := by rfl
  have decode : C.gates = [(⟨.or,[0,1]⟩ : Gate),(⟨.or,[26,3]⟩ : Gate),(⟨.or,[27,9]⟩ : Gate),(⟨.and,[13,28]⟩ : Gate),(⟨.or,[1,2]⟩ : Gate),(⟨.or,[30,4]⟩ : Gate),(⟨.or,[31,10]⟩ : Gate),(⟨.and,[14,32]⟩ : Gate),(⟨.or,[3,4]⟩ : Gate),(⟨.or,[34,6]⟩ : Gate),(⟨.or,[35,12]⟩ : Gate),(⟨.and,[16,36]⟩ : Gate),(⟨.or,[4,5]⟩ : Gate),(⟨.or,[38,7]⟩ : Gate),(⟨.or,[39,0]⟩ : Gate),(⟨.and,[17,40]⟩ : Gate),(⟨.or,[5,6]⟩ : Gate),(⟨.or,[42,8]⟩ : Gate),(⟨.or,[43,1]⟩ : Gate),(⟨.and,[18,44]⟩ : Gate),(⟨.or,[6,7]⟩ : Gate),(⟨.or,[46,9]⟩ : Gate),(⟨.or,[47,2]⟩ : Gate),(⟨.and,[19,48]⟩ : Gate),(⟨.or,[7,8]⟩ : Gate),(⟨.or,[50,10]⟩ : Gate),(⟨.or,[51,3]⟩ : Gate),(⟨.and,[20,52]⟩ : Gate),(⟨.or,[8,9]⟩ : Gate),(⟨.or,[54,11]⟩ : Gate),(⟨.or,[55,4]⟩ : Gate),(⟨.and,[21,56]⟩ : Gate),(⟨.or,[9,10]⟩ : Gate),(⟨.or,[58,12]⟩ : Gate),(⟨.or,[59,5]⟩ : Gate),(⟨.and,[22,60]⟩ : Gate),(⟨.or,[10,11]⟩ : Gate),(⟨.or,[62,0]⟩ : Gate),(⟨.or,[63,6]⟩ : Gate),(⟨.and,[23,64]⟩ : Gate),(⟨.or,[11,12]⟩ : Gate),(⟨.or,[66,1]⟩ : Gate),(⟨.or,[67,7]⟩ : Gate),(⟨.and,[24,68]⟩ : Gate),(⟨.or,[12,0]⟩ : Gate),(⟨.or,[70,2]⟩ : Gate),(⟨.or,[71,8]⟩ : Gate),(⟨.and,[25,72]⟩ : Gate),(⟨.or,[29,33]⟩ : Gate),(⟨.or,[74,37]⟩ : Gate),(⟨.or,[75,41]⟩ : Gate),(⟨.or,[76,45]⟩ : Gate),(⟨.or,[77,49]⟩ : Gate),(⟨.or,[78,53]⟩ : Gate),(⟨.or,[79,57]⟩ : Gate),(⟨.or,[80,61]⟩ : Gate),(⟨.or,[81,65]⟩ : Gate),(⟨.or,[82,69]⟩ : Gate),(⟨.or,[83,73]⟩ : Gate),(⟨.or,[2,3]⟩ : Gate),(⟨.or,[85,5]⟩ : Gate),(⟨.or,[86,11]⟩ : Gate),(⟨.or,[84,15]⟩ : Gate),(⟨.or,[84,87]⟩ : Gate),(⟨.and,[88,89]⟩ : Gate)] := by rfl
  let input := List.ofFn (fun i : Fin (13+13) => Fin.addCases x y i)
  have init : input = values.take 26 := by rfl
  have computed : C.wires input = values.take 91 := by
    change C.gates.foldl step input = _
    rw [decode,init]
    rw [List.foldl_cons,h26,List.foldl_cons,h27,List.foldl_cons,h28,List.foldl_cons,h29,List.foldl_cons,h30]
    rw [List.foldl_cons,h31,List.foldl_cons,h32,List.foldl_cons,h33,List.foldl_cons,h34,List.foldl_cons,h35]
    rw [List.foldl_cons,h36,List.foldl_cons,h37,List.foldl_cons,h38,List.foldl_cons,h39,List.foldl_cons,h40]
    rw [List.foldl_cons,h41,List.foldl_cons,h42,List.foldl_cons,h43,List.foldl_cons,h44,List.foldl_cons,h45]
    rw [List.foldl_cons,h46,List.foldl_cons,h47,List.foldl_cons,h48,List.foldl_cons,h49,List.foldl_cons,h50]
    rw [List.foldl_cons,h51,List.foldl_cons,h52,List.foldl_cons,h53,List.foldl_cons,h54,List.foldl_cons,h55]
    rw [List.foldl_cons,h56,List.foldl_cons,h57,List.foldl_cons,h58,List.foldl_cons,h59,List.foldl_cons,h60]
    rw [List.foldl_cons,h61,List.foldl_cons,h62,List.foldl_cons,h63,List.foldl_cons,h64,List.foldl_cons,h65]
    rw [List.foldl_cons,h66,List.foldl_cons,h67,List.foldl_cons,h68,List.foldl_cons,h69,List.foldl_cons,h70]
    rw [List.foldl_cons,h71,List.foldl_cons,h72,List.foldl_cons,h73,List.foldl_cons,h74,List.foldl_cons,h75]
    rw [List.foldl_cons,h76,List.foldl_cons,h77,List.foldl_cons,h78,List.foldl_cons,h79,List.foldl_cons,h80]
    rw [List.foldl_cons,h81,List.foldl_cons,h82,List.foldl_cons,h83,List.foldl_cons,h84,List.foldl_cons,h85]
    rw [List.foldl_cons,h86,List.foldl_cons,h87,List.foldl_cons,h88,List.foldl_cons,h89,List.foldl_cons,h90]
  change (C.wires input).getD 90 false = _
  rw [computed]
  rfl

theorem allStars (f : Fin 13 → Bool) :
    o (o (o (o (o (o (o (o (o (o (o (o (f 0) (f 1)) (f 3)) (f 4)) (f 5)) (f 6)) (f 7)) (f 8)) (f 9)) (f 10)) (f 11)) (f 12)) (f 2) = true ↔ ∃ l, f l=true := by
  simp only [oT]
  constructor
  · intro h
    rcases h with ((((((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)
    all_goals exact ⟨_,by assumption⟩
  · rintro ⟨l,hl⟩
    fin_cases l <;> tauto

theorem correct (x y : Fin 13 → Bool) :
    C.eval (List.ofFn (fun i : Fin (13+13) => Fin.addCases x y i)) = true ↔
      ∃ l : Fin 13, y l = true ∧ (x l || x (l+1) || x (l+3) || x (l+9)) = true := by
  rw [formula,bridge]
  change (o (o (o (o (o (o (o (o (o (o (o (o (star x y 0) (star x y 1)) (star x y 3)) (star x y 4)) (star x y 5)) (star x y 6)) (star x y 7)) (star x y 8)) (star x y 9)) (star x y 10)) (star x y 11)) (star x y 12)) (star x y 2) = true) ↔ _
  rw [allStars (star x y)]
  apply exists_congr
  intro l
  simp only [star,aT,bank,oT,Bool.or_eq_true]

theorem oneMore : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size = (65 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧       (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧         (∀ (x2 x3 : Fin (13 : ℕ) → Bool), x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)), x3 x4 = Bool.true ∧ (x2 x4 || x2 (x4 + (1 : Fin (13 : ℕ))) || x2 (x4 + (3 : Fin (13 : ℕ))) || x2 (x4 + (9 : Fin (13 : ℕ)))) = Bool.true) ∧           ∃ (x2 : ℕ) (x3 : ℕ) (x4 : ℕ),             x1.output = (26 : ℕ) + x2 ∧               x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧                 ∀ (x5 : Bool),                   have x6 : List Bool := x1.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                   x6.getD x3 Bool.false = Bool.false ∧ x6.getD x4 Bool.false = Bool.false := by
  refine ⟨C,rfl,?_,?_,correct,64,88,89,rfl,rfl,?_⟩
  all_goals decide +kernel

end Near2620
