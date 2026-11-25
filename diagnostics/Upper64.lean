import PEqualNP.Defs
namespace Upper1874
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev I := Fin 13
def D : Finset I := {0,1,3,9}
def quad (q : Finset I) := q.card=4 ∧ ∀ l : I,(q.filter fun p=>p-l∈D).card≤2
instance (q : Finset I) : Decidable (quad q) := inferInstanceAs (Decidable (_ ∧ _))
def vec (P L : I→Bool) := List.ofFn P ++ List.ofFn L
def pos (p l : I) := vec (fun i=>decide (i=p)) (fun i=>decide (i=l))
def neg (q : Finset I) := vec (fun i=>decide (i∈q)) (fun l=>decide (∀ p∈q,p-l∉D))
def O (a b : Bool) := GateOp.or.eval [a,b]
def A (a b : Bool) := GateOp.and.eval [a,b]
theorem orBool (a b : Bool) : O a b=(a||b) := by cases a <;> cases b <;> rfl
theorem andBool (a b : Bool) : A a b=(a&&b) := by cases a <;> cases b <;> rfl
def C : Circuit := ⟨[⟨.or,[4,10]⟩,⟨.or,[2,26]⟩,⟨.or,[1,27]⟩,⟨.and,[14,28]⟩,⟨.or,[5,11]⟩,⟨.or,[3,30]⟩,⟨.or,[2,31]⟩,⟨.and,[15,32]⟩,⟨.or,[6,12]⟩,⟨.or,[4,34]⟩,⟨.or,[3,35]⟩,⟨.and,[16,36]⟩,⟨.or,[7,0]⟩,⟨.or,[5,38]⟩,⟨.or,[4,39]⟩,⟨.and,[17,40]⟩,⟨.or,[8,1]⟩,⟨.or,[6,42]⟩,⟨.or,[5,43]⟩,⟨.and,[18,44]⟩,⟨.or,[9,2]⟩,⟨.or,[7,46]⟩,⟨.or,[6,47]⟩,⟨.and,[19,48]⟩,⟨.or,[10,3]⟩,⟨.or,[8,50]⟩,⟨.or,[7,51]⟩,⟨.and,[20,52]⟩,⟨.or,[11,4]⟩,⟨.or,[9,54]⟩,⟨.or,[8,55]⟩,⟨.and,[21,56]⟩,⟨.or,[12,5]⟩,⟨.or,[10,58]⟩,⟨.or,[9,59]⟩,⟨.and,[22,60]⟩,⟨.or,[0,6]⟩,⟨.or,[11,62]⟩,⟨.or,[10,63]⟩,⟨.and,[23,64]⟩,⟨.or,[1,7]⟩,⟨.or,[12,66]⟩,⟨.or,[11,67]⟩,⟨.and,[24,68]⟩,⟨.or,[2,8]⟩,⟨.or,[0,70]⟩,⟨.or,[12,71]⟩,⟨.and,[25,72]⟩,⟨.or,[69,73]⟩,⟨.or,[65,74]⟩,⟨.or,[61,75]⟩,⟨.or,[57,76]⟩,⟨.or,[53,77]⟩,⟨.or,[49,78]⟩,⟨.or,[45,79]⟩,⟨.or,[41,80]⟩,⟨.or,[37,81]⟩,⟨.or,[33,82]⟩,⟨.or,[29,83]⟩,⟨.or,[3,9]⟩,⟨.or,[1,85]⟩,⟨.or,[0,86]⟩,⟨.or,[84,13]⟩,⟨.or,[84,87]⟩],89⟩
def rows : List (I × List I) := [(1,[1, 2, 4, 10]),(2,[2, 3, 5, 11]),(3,[3, 4, 6, 12]),(4,[4, 5, 7, 0]),(5,[5, 6, 8, 1]),(6,[6, 7, 9, 2]),(7,[7, 8, 10, 3]),(8,[8, 9, 11, 4]),(9,[9, 10, 12, 5]),(10,[10, 11, 0, 6]),(11,[11, 12, 1, 7]),(12,[12, 0, 2, 8])]
def zVal (P L : I→Bool) := rows.any fun q=>L q.1 && q.2.any P
def nVal (P : I→Bool) := ([0,1,3,9] : List I).any P
def wire (w : Nat) (v : List Bool) := (C.wires v).getD w false
def answers (P L : I→Bool) := (zVal P L || L 0,zVal P L || nVal P)
def expanded (P L : I→Bool) := ((O (O (A (L 1) (O (P 1) (O (P 2) (O (P 4) (P 10))))) (O (A (L 2) (O (P 2) (O (P 3) (O (P 5) (P 11))))) (O (A (L 3) (O (P 3) (O (P 4) (O (P 6) (P 12))))) (O (A (L 4) (O (P 4) (O (P 5) (O (P 7) (P 0))))) (O (A (L 5) (O (P 5) (O (P 6) (O (P 8) (P 1))))) (O (A (L 6) (O (P 6) (O (P 7) (O (P 9) (P 2))))) (O (A (L 7) (O (P 7) (O (P 8) (O (P 10) (P 3))))) (O (A (L 8) (O (P 8) (O (P 9) (O (P 11) (P 4))))) (O (A (L 9) (O (P 9) (O (P 10) (O (P 12) (P 5))))) (O (A (L 10) (O (P 10) (O (P 11) (O (P 0) (P 6))))) (O (A (L 11) (O (P 11) (O (P 12) (O (P 1) (P 7))))) (A (L 12) (O (P 12) (O (P 0) (O (P 2) (P 8)))))))))))))))) (L 0)),(O (O (A (L 1) (O (P 1) (O (P 2) (O (P 4) (P 10))))) (O (A (L 2) (O (P 2) (O (P 3) (O (P 5) (P 11))))) (O (A (L 3) (O (P 3) (O (P 4) (O (P 6) (P 12))))) (O (A (L 4) (O (P 4) (O (P 5) (O (P 7) (P 0))))) (O (A (L 5) (O (P 5) (O (P 6) (O (P 8) (P 1))))) (O (A (L 6) (O (P 6) (O (P 7) (O (P 9) (P 2))))) (O (A (L 7) (O (P 7) (O (P 8) (O (P 10) (P 3))))) (O (A (L 8) (O (P 8) (O (P 9) (O (P 11) (P 4))))) (O (A (L 9) (O (P 9) (O (P 10) (O (P 12) (P 5))))) (O (A (L 10) (O (P 10) (O (P 11) (O (P 0) (P 6))))) (O (A (L 11) (O (P 11) (O (P 12) (O (P 1) (P 7))))) (A (L 12) (O (P 12) (O (P 0) (O (P 2) (P 8)))))))))))))))) (O (P 0) (O (P 1) (O (P 3) (P 9))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
theorem staged (P L : I→Bool) : (wire 88 (vec P L),wire 89 (vec P L)) = expanded P L := by
  let u26 := O (P 4) (P 10)
  let u27 := O (P 2) u26
  let u28 := O (P 1) u27
  let u29 := A (L 1) u28
  let u30 := O (P 5) (P 11)
  let u31 := O (P 3) u30
  let u32 := O (P 2) u31
  let u33 := A (L 2) u32
  let u34 := O (P 6) (P 12)
  let u35 := O (P 4) u34
  let u36 := O (P 3) u35
  let u37 := A (L 3) u36
  let u38 := O (P 7) (P 0)
  let u39 := O (P 5) u38
  let u40 := O (P 4) u39
  let u41 := A (L 4) u40
  let u42 := O (P 8) (P 1)
  let u43 := O (P 6) u42
  let u44 := O (P 5) u43
  let u45 := A (L 5) u44
  let u46 := O (P 9) (P 2)
  let u47 := O (P 7) u46
  let u48 := O (P 6) u47
  let u49 := A (L 6) u48
  let u50 := O (P 10) (P 3)
  let u51 := O (P 8) u50
  let u52 := O (P 7) u51
  let u53 := A (L 7) u52
  let u54 := O (P 11) (P 4)
  let u55 := O (P 9) u54
  let u56 := O (P 8) u55
  let u57 := A (L 8) u56
  let u58 := O (P 12) (P 5)
  let u59 := O (P 10) u58
  let u60 := O (P 9) u59
  let u61 := A (L 9) u60
  let u62 := O (P 0) (P 6)
  let u63 := O (P 11) u62
  let u64 := O (P 10) u63
  let u65 := A (L 10) u64
  let u66 := O (P 1) (P 7)
  let u67 := O (P 12) u66
  let u68 := O (P 11) u67
  let u69 := A (L 11) u68
  let u70 := O (P 2) (P 8)
  let u71 := O (P 0) u70
  let u72 := O (P 12) u71
  let u73 := A (L 12) u72
  let u74 := O u69 u73
  let u75 := O u65 u74
  let u76 := O u61 u75
  let u77 := O u57 u76
  let u78 := O u53 u77
  let u79 := O u49 u78
  let u80 := O u45 u79
  let u81 := O u41 u80
  let u82 := O u37 u81
  let u83 := O u33 u82
  let u84 := O u29 u83
  let u85 := O (P 3) (P 9)
  let u86 := O (P 1) u85
  let u87 := O (P 0) u86
  let u88 := O u84 (L 0)
  let u89 := O u84 u87
  let values : List Bool := [(P 0),(P 1),(P 2),(P 3),(P 4),(P 5),(P 6),(P 7),(P 8),(P 9),(P 10),(P 11),(P 12),(L 0),(L 1),(L 2),(L 3),(L 4),(L 5),(L 6),(L 7),(L 8),(L 9),(L 10),(L 11),(L 12),u26,u27,u28,u29,u30,u31,u32,u33,u34,u35,u36,u37,u38,u39,u40,u41,u42,u43,u44,u45,u46,u47,u48,u49,u50,u51,u52,u53,u54,u55,u56,u57,u58,u59,u60,u61,u62,u63,u64,u65,u66,u67,u68,u69,u70,u71,u72,u73,u74,u75,u76,u77,u78,u79,u80,u81,u82,u83,u84,u85,u86,u87,u88,u89]
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have h26 : step (values.take 26) (⟨.or,[4,10]⟩ : Gate) = values.take 27 := by rfl
  have h27 : step (values.take 27) (⟨.or,[2,26]⟩ : Gate) = values.take 28 := by rfl
  have h28 : step (values.take 28) (⟨.or,[1,27]⟩ : Gate) = values.take 29 := by rfl
  have h29 : step (values.take 29) (⟨.and,[14,28]⟩ : Gate) = values.take 30 := by rfl
  have h30 : step (values.take 30) (⟨.or,[5,11]⟩ : Gate) = values.take 31 := by rfl
  have h31 : step (values.take 31) (⟨.or,[3,30]⟩ : Gate) = values.take 32 := by rfl
  have h32 : step (values.take 32) (⟨.or,[2,31]⟩ : Gate) = values.take 33 := by rfl
  have h33 : step (values.take 33) (⟨.and,[15,32]⟩ : Gate) = values.take 34 := by rfl
  have h34 : step (values.take 34) (⟨.or,[6,12]⟩ : Gate) = values.take 35 := by rfl
  have h35 : step (values.take 35) (⟨.or,[4,34]⟩ : Gate) = values.take 36 := by rfl
  have h36 : step (values.take 36) (⟨.or,[3,35]⟩ : Gate) = values.take 37 := by rfl
  have h37 : step (values.take 37) (⟨.and,[16,36]⟩ : Gate) = values.take 38 := by rfl
  have h38 : step (values.take 38) (⟨.or,[7,0]⟩ : Gate) = values.take 39 := by rfl
  have h39 : step (values.take 39) (⟨.or,[5,38]⟩ : Gate) = values.take 40 := by rfl
  have h40 : step (values.take 40) (⟨.or,[4,39]⟩ : Gate) = values.take 41 := by rfl
  have h41 : step (values.take 41) (⟨.and,[17,40]⟩ : Gate) = values.take 42 := by rfl
  have h42 : step (values.take 42) (⟨.or,[8,1]⟩ : Gate) = values.take 43 := by rfl
  have h43 : step (values.take 43) (⟨.or,[6,42]⟩ : Gate) = values.take 44 := by rfl
  have h44 : step (values.take 44) (⟨.or,[5,43]⟩ : Gate) = values.take 45 := by rfl
  have h45 : step (values.take 45) (⟨.and,[18,44]⟩ : Gate) = values.take 46 := by rfl
  have h46 : step (values.take 46) (⟨.or,[9,2]⟩ : Gate) = values.take 47 := by rfl
  have h47 : step (values.take 47) (⟨.or,[7,46]⟩ : Gate) = values.take 48 := by rfl
  have h48 : step (values.take 48) (⟨.or,[6,47]⟩ : Gate) = values.take 49 := by rfl
  have h49 : step (values.take 49) (⟨.and,[19,48]⟩ : Gate) = values.take 50 := by rfl
  have h50 : step (values.take 50) (⟨.or,[10,3]⟩ : Gate) = values.take 51 := by rfl
  have h51 : step (values.take 51) (⟨.or,[8,50]⟩ : Gate) = values.take 52 := by rfl
  have h52 : step (values.take 52) (⟨.or,[7,51]⟩ : Gate) = values.take 53 := by rfl
  have h53 : step (values.take 53) (⟨.and,[20,52]⟩ : Gate) = values.take 54 := by rfl
  have h54 : step (values.take 54) (⟨.or,[11,4]⟩ : Gate) = values.take 55 := by rfl
  have h55 : step (values.take 55) (⟨.or,[9,54]⟩ : Gate) = values.take 56 := by rfl
  have h56 : step (values.take 56) (⟨.or,[8,55]⟩ : Gate) = values.take 57 := by rfl
  have h57 : step (values.take 57) (⟨.and,[21,56]⟩ : Gate) = values.take 58 := by rfl
  have h58 : step (values.take 58) (⟨.or,[12,5]⟩ : Gate) = values.take 59 := by rfl
  have h59 : step (values.take 59) (⟨.or,[10,58]⟩ : Gate) = values.take 60 := by rfl
  have h60 : step (values.take 60) (⟨.or,[9,59]⟩ : Gate) = values.take 61 := by rfl
  have h61 : step (values.take 61) (⟨.and,[22,60]⟩ : Gate) = values.take 62 := by rfl
  have h62 : step (values.take 62) (⟨.or,[0,6]⟩ : Gate) = values.take 63 := by rfl
  have h63 : step (values.take 63) (⟨.or,[11,62]⟩ : Gate) = values.take 64 := by rfl
  have h64 : step (values.take 64) (⟨.or,[10,63]⟩ : Gate) = values.take 65 := by rfl
  have h65 : step (values.take 65) (⟨.and,[23,64]⟩ : Gate) = values.take 66 := by rfl
  have h66 : step (values.take 66) (⟨.or,[1,7]⟩ : Gate) = values.take 67 := by rfl
  have h67 : step (values.take 67) (⟨.or,[12,66]⟩ : Gate) = values.take 68 := by rfl
  have h68 : step (values.take 68) (⟨.or,[11,67]⟩ : Gate) = values.take 69 := by rfl
  have h69 : step (values.take 69) (⟨.and,[24,68]⟩ : Gate) = values.take 70 := by rfl
  have h70 : step (values.take 70) (⟨.or,[2,8]⟩ : Gate) = values.take 71 := by rfl
  have h71 : step (values.take 71) (⟨.or,[0,70]⟩ : Gate) = values.take 72 := by rfl
  have h72 : step (values.take 72) (⟨.or,[12,71]⟩ : Gate) = values.take 73 := by rfl
  have h73 : step (values.take 73) (⟨.and,[25,72]⟩ : Gate) = values.take 74 := by rfl
  have h74 : step (values.take 74) (⟨.or,[69,73]⟩ : Gate) = values.take 75 := by rfl
  have h75 : step (values.take 75) (⟨.or,[65,74]⟩ : Gate) = values.take 76 := by rfl
  have h76 : step (values.take 76) (⟨.or,[61,75]⟩ : Gate) = values.take 77 := by rfl
  have h77 : step (values.take 77) (⟨.or,[57,76]⟩ : Gate) = values.take 78 := by rfl
  have h78 : step (values.take 78) (⟨.or,[53,77]⟩ : Gate) = values.take 79 := by rfl
  have h79 : step (values.take 79) (⟨.or,[49,78]⟩ : Gate) = values.take 80 := by rfl
  have h80 : step (values.take 80) (⟨.or,[45,79]⟩ : Gate) = values.take 81 := by rfl
  have h81 : step (values.take 81) (⟨.or,[41,80]⟩ : Gate) = values.take 82 := by rfl
  have h82 : step (values.take 82) (⟨.or,[37,81]⟩ : Gate) = values.take 83 := by rfl
  have h83 : step (values.take 83) (⟨.or,[33,82]⟩ : Gate) = values.take 84 := by rfl
  have h84 : step (values.take 84) (⟨.or,[29,83]⟩ : Gate) = values.take 85 := by rfl
  have h85 : step (values.take 85) (⟨.or,[3,9]⟩ : Gate) = values.take 86 := by rfl
  have h86 : step (values.take 86) (⟨.or,[1,85]⟩ : Gate) = values.take 87 := by rfl
  have h87 : step (values.take 87) (⟨.or,[0,86]⟩ : Gate) = values.take 88 := by rfl
  have h88 : step (values.take 88) (⟨.or,[84,13]⟩ : Gate) = values.take 89 := by rfl
  have h89 : step (values.take 89) (⟨.or,[84,87]⟩ : Gate) = values.take 90 := by rfl
  have init : vec P L=values.take 26 := by rfl
  have ws : C.wires (vec P L) = values.take 90 := by
    change C.gates.foldl step (vec P L) = _
    rw [init]
    unfold C
    rw [List.foldl_cons,h26,List.foldl_cons,h27,List.foldl_cons,h28,List.foldl_cons,h29]
    rw [List.foldl_cons,h30,List.foldl_cons,h31,List.foldl_cons,h32,List.foldl_cons,h33]
    rw [List.foldl_cons,h34,List.foldl_cons,h35,List.foldl_cons,h36,List.foldl_cons,h37]
    rw [List.foldl_cons,h38,List.foldl_cons,h39,List.foldl_cons,h40,List.foldl_cons,h41]
    rw [List.foldl_cons,h42,List.foldl_cons,h43,List.foldl_cons,h44,List.foldl_cons,h45]
    rw [List.foldl_cons,h46,List.foldl_cons,h47,List.foldl_cons,h48,List.foldl_cons,h49]
    rw [List.foldl_cons,h50,List.foldl_cons,h51,List.foldl_cons,h52,List.foldl_cons,h53]
    rw [List.foldl_cons,h54,List.foldl_cons,h55,List.foldl_cons,h56,List.foldl_cons,h57]
    rw [List.foldl_cons,h58,List.foldl_cons,h59,List.foldl_cons,h60,List.foldl_cons,h61]
    rw [List.foldl_cons,h62,List.foldl_cons,h63,List.foldl_cons,h64,List.foldl_cons,h65]
    rw [List.foldl_cons,h66,List.foldl_cons,h67,List.foldl_cons,h68,List.foldl_cons,h69]
    rw [List.foldl_cons,h70,List.foldl_cons,h71,List.foldl_cons,h72,List.foldl_cons,h73]
    rw [List.foldl_cons,h74,List.foldl_cons,h75,List.foldl_cons,h76,List.foldl_cons,h77]
    rw [List.foldl_cons,h78,List.foldl_cons,h79,List.foldl_cons,h80,List.foldl_cons,h81]
    rw [List.foldl_cons,h82,List.foldl_cons,h83,List.foldl_cons,h84,List.foldl_cons,h85]
    rw [List.foldl_cons,h86,List.foldl_cons,h87,List.foldl_cons,h88,List.foldl_cons,h89] <;> rfl
  change ((C.wires (vec P L)).getD 88 false,(C.wires (vec P L)).getD 89 false)=_
  rw [ws] <;> rfl
theorem semantic (P L : I→Bool) : (wire 88 (vec P L),wire 89 (vec P L))=answers P L := by
  rw [staged]
  simp only [expanded,orBool,andBool,answers,zVal,nVal,rows,List.any_cons,List.any_nil,Bool.or_false]
theorem members : ∀ s∈rows,∀ p∈s.2,p-s.1∈D := by decide +kernel
theorem negZ (q : Finset I) : zVal (fun p=>decide (p∈q)) (fun l=>decide (∀ p∈q,p-l∉D))=false := by
  cases h : zVal (fun p=>decide (p∈q)) (fun l=>decide (∀ p∈q,p-l∉D)) with
  | false => rfl
  | true =>
    simp only [zVal,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨s,hs,no,p,hp,hq⟩ := h
    exact (no p hq (members s hs p hp)).elim
theorem posTable : ∀ p l : I,p-l∈D → answers (fun j=>decide (j=p)) (fun j=>decide (j=l))=(true,true) := by decide +kernel
theorem positive (p l : I) (h : p-l∈D) : wire 88 (pos p l)=true ∧ wire 89 (pos p l)=true :=
  (Prod.mk.inj ((semantic _ _).trans (posTable p l h)))
theorem negative (q : Finset I) : wire 88 (neg q)=false ∨ wire 89 (neg q)=false := by
  have pair := semantic (fun p=>decide (p∈q)) (fun l=>decide (∀ p∈q,p-l∉D))
  simp only [answers,negZ,Bool.false_or] at pair
  obtain ⟨le,ri⟩ := Prod.mk.inj pair
  by_cases eh : ∀ p∈q,p-(0:I)∉D
  · right
    rw [show wire 89 (neg q)=_ from ri]
    cases h : nVal (fun p=>decide (p∈q)) with
    | false => rfl
    | true =>
      simp only [nVal,List.any_eq_true,decide_eq_true_eq] at h
      obtain ⟨p,hp,hs⟩ := h
      have mem : p-(0:I)∈D := (show ∀ p : I,p∈([0,1,3,9] : List I) → p-(0:I)∈D from by decide) p hp
      exact (eh p hs mem).elim
  · exact Or.inl (le.trans (decide_eq_false eh))
def qa : Finset I := {0,1,2,5}
def qb : Finset I := {2,4,5,6}
theorem privateA : quad qa ∧ wire 88 (neg qa)=false ∧ wire 89 (neg qa)=true := by
  have eqs : answers (fun p=>decide (p∈qa)) (fun l=>decide (∀ p∈qa,p-l∉D))=(false,true) := by decide +kernel
  exact ⟨by decide +kernel, Prod.mk.inj ((semantic _ _).trans eqs)⟩
theorem privateB : quad qb ∧ wire 88 (neg qb)=true ∧ wire 89 (neg qb)=false := by
  have eqs : answers (fun p=>decide (p∈qb)) (fun l=>decide (∀ p∈qb,p-l∉D))=(true,false) := by decide +kernel
  exact ⟨by decide +kernel, Prod.mk.inj ((semantic _ _).trans eqs)⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)
theorem monotone : Monotone2 C := by
  intro g hg
  have all : C.gates.all legal = true := by decide +kernel
  have h := List.all_eq_true.mp all g hg
  cases e : g.op <;> simp [legal,e] at h ⊢ <;> exact h
theorem back : NestedCover.ReadsBack 26 C := by
  have F : ∀ j : Fin C.gates.length,∀ w∈(C.gates.get j).inputs,w<26+j.val := by decide +kernel
  intro j hj w hw
  apply F ⟨j,hj⟩ w
  simpa [NestedCover.gateAt,List.getD_eq_getElem?_getD,hj] using hw
theorem size : C.size=64 := rfl
theorem valid : 88<26+C.size ∧ 89<26+C.size := by decide
end Upper1874
