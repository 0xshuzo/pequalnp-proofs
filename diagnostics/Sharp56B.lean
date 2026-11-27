import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17744
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
def C : Circuit := ⟨[⟨.or,[5,11]⟩,⟨.or,[3,26]⟩,⟨.or,[2,27]⟩,⟨.and,[15,28]⟩,⟨.or,[6,12]⟩,⟨.or,[4,30]⟩,⟨.or,[3,31]⟩,⟨.and,[16,32]⟩,⟨.or,[5,7]⟩,⟨.or,[4,34]⟩,⟨.and,[17,35]⟩,⟨.or,[8,1]⟩,⟨.or,[6,37]⟩,⟨.or,[5,38]⟩,⟨.and,[18,39]⟩,⟨.or,[9,2]⟩,⟨.or,[7,41]⟩,⟨.or,[6,42]⟩,⟨.and,[19,43]⟩,⟨.or,[10,3]⟩,⟨.or,[8,45]⟩,⟨.or,[7,46]⟩,⟨.and,[20,47]⟩,⟨.or,[11,4]⟩,⟨.or,[9,49]⟩,⟨.or,[8,50]⟩,⟨.and,[21,51]⟩,⟨.or,[12,5]⟩,⟨.or,[10,53]⟩,⟨.or,[9,54]⟩,⟨.and,[22,55]⟩,⟨.or,[11,6]⟩,⟨.or,[10,57]⟩,⟨.and,[23,58]⟩,⟨.or,[1,7]⟩,⟨.or,[12,60]⟩,⟨.or,[11,61]⟩,⟨.and,[24,62]⟩,⟨.or,[2,8]⟩,⟨.or,[12,64]⟩,⟨.and,[25,65]⟩,⟨.or,[63,66]⟩,⟨.or,[59,67]⟩,⟨.or,[56,68]⟩,⟨.or,[52,69]⟩,⟨.or,[48,70]⟩,⟨.or,[44,71]⟩,⟨.or,[40,72]⟩,⟨.or,[36,73]⟩,⟨.or,[33,74]⟩,⟨.or,[29,75]⟩,⟨.or,[4,10]⟩,⟨.or,[2,77]⟩,⟨.or,[1,78]⟩,⟨.or,[76,14]⟩,⟨.or,[76,79]⟩],81⟩
def rows : List (I × List I) := [(2,[2, 3, 5, 11]),(3,[3, 4, 6, 12]),(4,[4, 5, 7]),(5,[5, 6, 8, 1]),(6,[6, 7, 9, 2]),(7,[7, 8, 10, 3]),(8,[8, 9, 11, 4]),(9,[9, 10, 12, 5]),(10,[10, 11, 6]),(11,[11, 12, 1, 7]),(12,[12, 2, 8])]
def zVal (P L : I→Bool) := rows.any fun q=>L q.1 && q.2.any P
def nVal (P : I→Bool) := ([1,2,4,10] : List I).any P
def wire (w : Nat) (v : List Bool) := (C.wires v).getD w false
def answers (P L : I→Bool) := (zVal P L || L 1,zVal P L || nVal P)
def expanded (P L : I→Bool) := ((O (O (A (L 2) (O (P 2) (O (P 3) (O (P 5) (P 11))))) (O (A (L 3) (O (P 3) (O (P 4) (O (P 6) (P 12))))) (O (A (L 4) (O (P 4) (O (P 5) (P 7)))) (O (A (L 5) (O (P 5) (O (P 6) (O (P 8) (P 1))))) (O (A (L 6) (O (P 6) (O (P 7) (O (P 9) (P 2))))) (O (A (L 7) (O (P 7) (O (P 8) (O (P 10) (P 3))))) (O (A (L 8) (O (P 8) (O (P 9) (O (P 11) (P 4))))) (O (A (L 9) (O (P 9) (O (P 10) (O (P 12) (P 5))))) (O (A (L 10) (O (P 10) (O (P 11) (P 6)))) (O (A (L 11) (O (P 11) (O (P 12) (O (P 1) (P 7))))) (A (L 12) (O (P 12) (O (P 2) (P 8)))))))))))))) (L 1)),(O (O (A (L 2) (O (P 2) (O (P 3) (O (P 5) (P 11))))) (O (A (L 3) (O (P 3) (O (P 4) (O (P 6) (P 12))))) (O (A (L 4) (O (P 4) (O (P 5) (P 7)))) (O (A (L 5) (O (P 5) (O (P 6) (O (P 8) (P 1))))) (O (A (L 6) (O (P 6) (O (P 7) (O (P 9) (P 2))))) (O (A (L 7) (O (P 7) (O (P 8) (O (P 10) (P 3))))) (O (A (L 8) (O (P 8) (O (P 9) (O (P 11) (P 4))))) (O (A (L 9) (O (P 9) (O (P 10) (O (P 12) (P 5))))) (O (A (L 10) (O (P 10) (O (P 11) (P 6)))) (O (A (L 11) (O (P 11) (O (P 12) (O (P 1) (P 7))))) (A (L 12) (O (P 12) (O (P 2) (P 8)))))))))))))) (O (P 1) (O (P 2) (O (P 4) (P 10))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
theorem staged (P L : I→Bool) : (wire 80 (vec P L),wire 81 (vec P L)) = expanded P L := by
  let u26 := O (P 5) (P 11)
  let u27 := O (P 3) u26
  let u28 := O (P 2) u27
  let u29 := A (L 2) u28
  let u30 := O (P 6) (P 12)
  let u31 := O (P 4) u30
  let u32 := O (P 3) u31
  let u33 := A (L 3) u32
  let u34 := O (P 5) (P 7)
  let u35 := O (P 4) u34
  let u36 := A (L 4) u35
  let u37 := O (P 8) (P 1)
  let u38 := O (P 6) u37
  let u39 := O (P 5) u38
  let u40 := A (L 5) u39
  let u41 := O (P 9) (P 2)
  let u42 := O (P 7) u41
  let u43 := O (P 6) u42
  let u44 := A (L 6) u43
  let u45 := O (P 10) (P 3)
  let u46 := O (P 8) u45
  let u47 := O (P 7) u46
  let u48 := A (L 7) u47
  let u49 := O (P 11) (P 4)
  let u50 := O (P 9) u49
  let u51 := O (P 8) u50
  let u52 := A (L 8) u51
  let u53 := O (P 12) (P 5)
  let u54 := O (P 10) u53
  let u55 := O (P 9) u54
  let u56 := A (L 9) u55
  let u57 := O (P 11) (P 6)
  let u58 := O (P 10) u57
  let u59 := A (L 10) u58
  let u60 := O (P 1) (P 7)
  let u61 := O (P 12) u60
  let u62 := O (P 11) u61
  let u63 := A (L 11) u62
  let u64 := O (P 2) (P 8)
  let u65 := O (P 12) u64
  let u66 := A (L 12) u65
  let u67 := O u63 u66
  let u68 := O u59 u67
  let u69 := O u56 u68
  let u70 := O u52 u69
  let u71 := O u48 u70
  let u72 := O u44 u71
  let u73 := O u40 u72
  let u74 := O u36 u73
  let u75 := O u33 u74
  let u76 := O u29 u75
  let u77 := O (P 4) (P 10)
  let u78 := O (P 2) u77
  let u79 := O (P 1) u78
  let u80 := O u76 (L 1)
  let u81 := O u76 u79
  let values : List Bool := [(P 0),(P 1),(P 2),(P 3),(P 4),(P 5),(P 6),(P 7),(P 8),(P 9),(P 10),(P 11),(P 12),(L 0),(L 1),(L 2),(L 3),(L 4),(L 5),(L 6),(L 7),(L 8),(L 9),(L 10),(L 11),(L 12),u26,u27,u28,u29,u30,u31,u32,u33,u34,u35,u36,u37,u38,u39,u40,u41,u42,u43,u44,u45,u46,u47,u48,u49,u50,u51,u52,u53,u54,u55,u56,u57,u58,u59,u60,u61,u62,u63,u64,u65,u66,u67,u68,u69,u70,u71,u72,u73,u74,u75,u76,u77,u78,u79,u80,u81]
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have h26 : step (values.take 26) (⟨.or,[5,11]⟩ : Gate) = values.take 27 := by rfl
  have h27 : step (values.take 27) (⟨.or,[3,26]⟩ : Gate) = values.take 28 := by rfl
  have h28 : step (values.take 28) (⟨.or,[2,27]⟩ : Gate) = values.take 29 := by rfl
  have h29 : step (values.take 29) (⟨.and,[15,28]⟩ : Gate) = values.take 30 := by rfl
  have h30 : step (values.take 30) (⟨.or,[6,12]⟩ : Gate) = values.take 31 := by rfl
  have h31 : step (values.take 31) (⟨.or,[4,30]⟩ : Gate) = values.take 32 := by rfl
  have h32 : step (values.take 32) (⟨.or,[3,31]⟩ : Gate) = values.take 33 := by rfl
  have h33 : step (values.take 33) (⟨.and,[16,32]⟩ : Gate) = values.take 34 := by rfl
  have h34 : step (values.take 34) (⟨.or,[5,7]⟩ : Gate) = values.take 35 := by rfl
  have h35 : step (values.take 35) (⟨.or,[4,34]⟩ : Gate) = values.take 36 := by rfl
  have h36 : step (values.take 36) (⟨.and,[17,35]⟩ : Gate) = values.take 37 := by rfl
  have h37 : step (values.take 37) (⟨.or,[8,1]⟩ : Gate) = values.take 38 := by rfl
  have h38 : step (values.take 38) (⟨.or,[6,37]⟩ : Gate) = values.take 39 := by rfl
  have h39 : step (values.take 39) (⟨.or,[5,38]⟩ : Gate) = values.take 40 := by rfl
  have h40 : step (values.take 40) (⟨.and,[18,39]⟩ : Gate) = values.take 41 := by rfl
  have h41 : step (values.take 41) (⟨.or,[9,2]⟩ : Gate) = values.take 42 := by rfl
  have h42 : step (values.take 42) (⟨.or,[7,41]⟩ : Gate) = values.take 43 := by rfl
  have h43 : step (values.take 43) (⟨.or,[6,42]⟩ : Gate) = values.take 44 := by rfl
  have h44 : step (values.take 44) (⟨.and,[19,43]⟩ : Gate) = values.take 45 := by rfl
  have h45 : step (values.take 45) (⟨.or,[10,3]⟩ : Gate) = values.take 46 := by rfl
  have h46 : step (values.take 46) (⟨.or,[8,45]⟩ : Gate) = values.take 47 := by rfl
  have h47 : step (values.take 47) (⟨.or,[7,46]⟩ : Gate) = values.take 48 := by rfl
  have h48 : step (values.take 48) (⟨.and,[20,47]⟩ : Gate) = values.take 49 := by rfl
  have h49 : step (values.take 49) (⟨.or,[11,4]⟩ : Gate) = values.take 50 := by rfl
  have h50 : step (values.take 50) (⟨.or,[9,49]⟩ : Gate) = values.take 51 := by rfl
  have h51 : step (values.take 51) (⟨.or,[8,50]⟩ : Gate) = values.take 52 := by rfl
  have h52 : step (values.take 52) (⟨.and,[21,51]⟩ : Gate) = values.take 53 := by rfl
  have h53 : step (values.take 53) (⟨.or,[12,5]⟩ : Gate) = values.take 54 := by rfl
  have h54 : step (values.take 54) (⟨.or,[10,53]⟩ : Gate) = values.take 55 := by rfl
  have h55 : step (values.take 55) (⟨.or,[9,54]⟩ : Gate) = values.take 56 := by rfl
  have h56 : step (values.take 56) (⟨.and,[22,55]⟩ : Gate) = values.take 57 := by rfl
  have h57 : step (values.take 57) (⟨.or,[11,6]⟩ : Gate) = values.take 58 := by rfl
  have h58 : step (values.take 58) (⟨.or,[10,57]⟩ : Gate) = values.take 59 := by rfl
  have h59 : step (values.take 59) (⟨.and,[23,58]⟩ : Gate) = values.take 60 := by rfl
  have h60 : step (values.take 60) (⟨.or,[1,7]⟩ : Gate) = values.take 61 := by rfl
  have h61 : step (values.take 61) (⟨.or,[12,60]⟩ : Gate) = values.take 62 := by rfl
  have h62 : step (values.take 62) (⟨.or,[11,61]⟩ : Gate) = values.take 63 := by rfl
  have h63 : step (values.take 63) (⟨.and,[24,62]⟩ : Gate) = values.take 64 := by rfl
  have h64 : step (values.take 64) (⟨.or,[2,8]⟩ : Gate) = values.take 65 := by rfl
  have h65 : step (values.take 65) (⟨.or,[12,64]⟩ : Gate) = values.take 66 := by rfl
  have h66 : step (values.take 66) (⟨.and,[25,65]⟩ : Gate) = values.take 67 := by rfl
  have h67 : step (values.take 67) (⟨.or,[63,66]⟩ : Gate) = values.take 68 := by rfl
  have h68 : step (values.take 68) (⟨.or,[59,67]⟩ : Gate) = values.take 69 := by rfl
  have h69 : step (values.take 69) (⟨.or,[56,68]⟩ : Gate) = values.take 70 := by rfl
  have h70 : step (values.take 70) (⟨.or,[52,69]⟩ : Gate) = values.take 71 := by rfl
  have h71 : step (values.take 71) (⟨.or,[48,70]⟩ : Gate) = values.take 72 := by rfl
  have h72 : step (values.take 72) (⟨.or,[44,71]⟩ : Gate) = values.take 73 := by rfl
  have h73 : step (values.take 73) (⟨.or,[40,72]⟩ : Gate) = values.take 74 := by rfl
  have h74 : step (values.take 74) (⟨.or,[36,73]⟩ : Gate) = values.take 75 := by rfl
  have h75 : step (values.take 75) (⟨.or,[33,74]⟩ : Gate) = values.take 76 := by rfl
  have h76 : step (values.take 76) (⟨.or,[29,75]⟩ : Gate) = values.take 77 := by rfl
  have h77 : step (values.take 77) (⟨.or,[4,10]⟩ : Gate) = values.take 78 := by rfl
  have h78 : step (values.take 78) (⟨.or,[2,77]⟩ : Gate) = values.take 79 := by rfl
  have h79 : step (values.take 79) (⟨.or,[1,78]⟩ : Gate) = values.take 80 := by rfl
  have h80 : step (values.take 80) (⟨.or,[76,14]⟩ : Gate) = values.take 81 := by rfl
  have h81 : step (values.take 81) (⟨.or,[76,79]⟩ : Gate) = values.take 82 := by rfl
  have init : vec P L=values.take 26 := by rfl
  have ws : C.wires (vec P L) = values.take 82 := by
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
    rw [List.foldl_cons,h78,List.foldl_cons,h79,List.foldl_cons,h80,List.foldl_cons,h81] <;> rfl
  change ((C.wires (vec P L)).getD 80 false,(C.wires (vec P L)).getD 81 false)=_
  rw [ws] <;> rfl
theorem semantic (P L : I→Bool) : (wire 80 (vec P L),wire 81 (vec P L))=answers P L := by
  rw [staged]
  simp only [expanded,orBool,andBool,answers,zVal,nVal,rows,List.any_cons,List.any_nil,Bool.or_false]
open PEqualNP.HeptadCover PEqualNP.GenericRejection
abbrev leftC : Circuit := ⟨C.gates,80⟩
abbrev rightC : Circuit := ⟨C.gates,81⟩

def obs (p l : Finset I) :=
  answers (fun i => decide (i ∈ p)) (fun i => decide (i ∈ l))

theorem evals (p l : Finset I) :
    (leftC.eval (incidenceInput p l), rightC.eval (incidenceInput p l)) = obs p l :=
  semantic _ _

def err (F : Circuit) := (quadrangles singerLines3).filter (fun Q =>
  F.eval (incidenceInput (Q.erase 0) ((missLines singerLines3 Q).erase 0)) = true)

theorem residual_pos : ∀ p l : I, p ≠ 0 → l ≠ 0 → p ∈ singerLines3 l →
    obs {p} {l} = (true,true) := by decide +kernel

theorem independent (P L : Finset I) (h : ∀ p ∈ P, ∀ l ∈ L, p ∉ singerLines3 l) :
    (obs P L).1 = false ∨ (obs P L).2 = false := by
  have members : ∀ s∈rows, ∀ p∈s.2, p∈singerLines3 s.1 := by decide +kernel
  have hn : ∀ p∈([1,2,4,10] : List I), p∈singerLines3 1 := by decide +kernel
  have zz : zVal (fun i => decide (i∈P)) (fun i => decide (i∈L)) = false := by
    cases eq : zVal (fun i => decide (i∈P)) (fun i => decide (i∈L)) with
    | false => rfl
    | true =>
      simp only [zVal,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] at eq
      obtain ⟨s,hs,hl,p,hp,hP⟩ := eq
      exact (h p hP s.1 hl (members s hs p hp)).elim
  simp only [obs,answers,zz,Bool.false_or]
  by_cases hl : (1:I) ∈ L
  · right
    cases e : nVal (fun i => decide (i ∈ P)) with
    | false => rfl
    | true =>
      simp only [nVal,List.any_eq_true,decide_eq_true_eq] at e
      obtain ⟨p,hp,hP⟩ := e
      exact (h p hP 1 hl (hn p hp)).elim
  · exact Or.inl (decide_eq_false hl)

theorem separate : Disjoint (err leftC) (err rightC) := by
  apply Finset.disjoint_left.mpr
  intro Q h1 h2
  have hin : ∀ p∈Q.erase (0:I), ∀ l∈(missLines singerLines3 Q).erase 0, p∉singerLines3 l := by
    intro p hp l hl hpl
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hl)).2
      hpl (Finset.mem_of_mem_erase hp)
  obtain ⟨ea,eb⟩ := Prod.mk.inj (evals (Q.erase 0) ((missLines singerLines3 Q).erase 0))
  have A := (Finset.mem_filter.mp h1).2
  have B := (Finset.mem_filter.mp h2).2
  rcases independent _ _ hin with ha | hb
  · exact Bool.noConfusion (A.symm.trans (ea.trans ha))
  · exact Bool.noConfusion (B.symm.trans (eb.trans hb))

def witnessP : Finset I := {0,1,2,5}
def witnessL : Finset I := {0,3,5,6}
theorem witness (Q : Finset I) (hQ : Q.card = 4)
    (hl : ∀ l, (Q ∩ singerLines3 l).card ≤ 2) : Q ∈ quadrangles singerLines3 := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hQ⟩,hl⟩
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
theorem leaks : (err leftC).Nonempty ∧ (err rightC).Nonempty := by
  refine ⟨⟨witnessL, Finset.mem_filter.mpr ⟨witness _ (by decide) (by decide),?_⟩⟩,
    ⟨witnessP, Finset.mem_filter.mpr ⟨witness _ (by decide) (by decide),?_⟩⟩⟩
  · have e := congrArg Prod.fst (evals (witnessL.erase 0) ((missLines singerLines3 witnessL).erase 0))
    exact e.trans (by decide +kernel)
  · have e := congrArg Prod.snd (evals (witnessP.erase 0) ((missLines singerLines3 witnessP).erase 0))
    exact e.trans (by decide +kernel)

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)
theorem monotone : Monotone2 leftC := by
  intro g hg
  have all : C.gates.all legal = true := by decide +kernel
  have h := List.all_eq_true.mp all g hg
  cases e : g.op <;> simp [legal,e] at h ⊢ <;> exact h
theorem sharp :
    (0:I) ∈ singerLines3 0 ∧ leftC.gates = rightC.gates ∧ Monotone2 leftC ∧
    (∀ p l : I, p ≠ 0 → l ≠ 0 → p ∈ singerLines3 l →
      ∀ F ∈ [leftC,rightC], F.eval (incidenceInput {p} {l}) = true) ∧
    Disjoint (err leftC) (err rightC) ∧ (err leftC).Nonempty ∧
    (err rightC).Nonempty ∧ leftC.size = 56 := by
  refine ⟨by decide,rfl,monotone,?_,separate,leaks.1,leaks.2,rfl⟩
  intro p l hp hl hit F hF
  have pair := Prod.mk.inj ((evals {p} {l}).trans (residual_pos p l hp hl hit))
  rcases List.mem_cons.mp hF with rfl | h
  · exact pair.1
  · rcases List.mem_singleton.mp h with rfl
    exact pair.2
end PEqualNP.Outside.L_meta_17744
