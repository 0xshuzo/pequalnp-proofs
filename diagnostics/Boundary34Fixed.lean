import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18854.Work
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 65536

abbrev Op := Fin 3 × Nat × Nat
def gate (t : Op) : Gate := if t.1=0 then ⟨.and,[t.2.1,t.2.2]⟩ else
  if t.1=1 then ⟨.or,[t.2.1,t.2.2]⟩ else ⟨.not,[t.2.1]⟩
def ops : List Op := [(0,12,5),(0,10,6),(1,16,15),(0,9,7),(1,18,17),(0,19,4),(0,14,5),(0,11,7),(1,22,21),(0,10,8),(1,24,23),(0,25,2),(1,26,20),(0,14,6),(0,13,7),(1,29,28),(0,12,8),(1,31,30),(0,32,1),(1,33,27),(0,14,9),(0,13,10),(1,36,35),(0,12,11),(1,38,37),(0,39,0),(0,13,5),(0,11,6),(1,42,41),(0,9,8),(1,44,43),(0,45,3),(1,46,40),(1,47,34)]
def out : Nat := 48
def circuit : Circuit := ⟨ops.map gate,out⟩

def full : Nat := 18446744073709551615
def numStep (w : List Nat) (t : Op) : List Nat :=
  let a:=w.getD t.2.1 0
  let b:=w.getD t.2.2 0
  w++[if t.1=0 then a &&& b else if t.1=1 then a ||| b else a ^^^ full]
def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def sample (w : List Nat) (k : Nat) := w.map (fun a => a.testBit k)

private theorem fullBit : ∀k : Fin 64,full.testBit k.val=true := by decide +kernel
theorem getSample (w : List Nat) (i k : Nat) :
    (sample w k).getD i false=(w.getD i 0).testBit k := by
  induction w generalizing i with
  | nil => simp [sample]
  | cons h t ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem step (w : List Nat) (k : Fin 64) (t : Op) :
    boolStep (sample w k.val) (gate t)=sample (numStep w t) k.val := by
  have readBit (o : Option Nat) : (o.map (fun a=>a.testBit k.val)).getD false=(o.getD 0).testBit k.val := by
    cases o <;> simp
  rcases t with ⟨d,a,b⟩
  fin_cases d <;> simp [gate,boolStep,sample,numStep,GateOp.eval,List.getD_eq_getElem?_getD,
    readBit,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,fullBit]

theorem run (ts : List Op) (w : List Nat) (k : Fin 64) :
    (ts.map gate).foldl boolStep (sample w k.val)=sample (ts.foldl numStep w) k.val := by
  induction ts generalizing w with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons,List.foldl_cons,step,ih]

def loIndex (x : Fin 6 → Bool) : Fin 64 := ⟨(if x 0 then 1 else 0)+(if x 1 then 2 else 0)+(if x 2 then 4 else 0)+(if x 3 then 8 else 0)+(if x 4 then 16 else 0)+(if x 5 then 32 else 0),by
  have lim : ∀ y : Fin 6→Bool,(if y 0 then 1 else 0)+(if y 1 then 2 else 0)+(if y 2 then 4 else 0)+(if y 3 then 8 else 0)+(if y 4 then 16 else 0)+(if y 5 then 32 else 0) < 64 := by decide +kernel
  exact lim x⟩
def lowMask : Fin 6 → Nat := ![12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
private theorem lowBits : ∀(x:Fin 6→Bool) (i:Fin 6),(lowMask i).testBit (loIndex x).val=x i := by decide +kernel
def column (h : Fin 9→Bool) : Fin 15→Nat :=
  ![lowMask 0,lowMask 1,lowMask 2,lowMask 3,lowMask 4,lowMask 5,if h 0 then full else 0,if h 1 then full else 0,if h 2 then full else 0,if h 3 then full else 0,if h 4 then full else 0,if h 5 then full else 0,if h 6 then full else 0,if h 7 then full else 0,if h 8 then full else 0]
def seed (h : Fin 9→Bool) := List.ofFn (column h)
def low (x : Fin 15→Bool) (i:Fin 6) := x (Fin.castAdd 9 i)
def high (x : Fin 15→Bool) (j:Fin 9) := x (Fin.natAdd 6 j)
theorem reads (x : Fin 15→Bool) (i:Fin 15) :
    (column (high x) i).testBit (loIndex (low x)).val=x i := by
  have highBit (j : Fin 9) : (if high x j then full else 0).testBit (loIndex (low x)).val = high x j := by
    cases hj : high x j <;> simp [hj, fullBit]
  fin_cases i
  · exact lowBits (low x) 0
  · exact lowBits (low x) 1
  · exact lowBits (low x) 2
  · exact lowBits (low x) 3
  · exact lowBits (low x) 4
  · exact lowBits (low x) 5
  · exact highBit 0
  · exact highBit 1
  · exact highBit 2
  · exact highBit 3
  · exact highBit 4
  · exact highBit 5
  · exact highBit 6
  · exact highBit 7
  · exact highBit 8
theorem starts (x : Fin 15→Bool) : sample (seed (high x)) (loIndex (low x)).val=List.ofFn x := by
  simp only [sample,seed,List.map_ofFn,Function.comp_def,reads]

def posted (x : Fin 15→Bool) : Bool := (x 0 && x 9 && x 14) || (x 0 && x 10 && x 13) || (x 0 && x 11 && x 12) || (x 1 && x 6 && x 14) || (x 1 && x 7 && x 13) || (x 1 && x 8 && x 12) || (x 2 && x 5 && x 14) || (x 2 && x 7 && x 11) || (x 2 && x 8 && x 10) || (x 3 && x 5 && x 13) || (x 3 && x 6 && x 11) || (x 3 && x 8 && x 9) || (x 4 && x 5 && x 12) || (x 4 && x 6 && x 10) || (x 4 && x 7 && x 9)
def target (h : Fin 9→Bool) : Nat :=
  let c:=column h
  (c 0 &&& c 9 &&& c 14) ||| (c 0 &&& c 10 &&& c 13) ||| (c 0 &&& c 11 &&& c 12) ||| (c 1 &&& c 6 &&& c 14) ||| (c 1 &&& c 7 &&& c 13) ||| (c 1 &&& c 8 &&& c 12) ||| (c 2 &&& c 5 &&& c 14) ||| (c 2 &&& c 7 &&& c 11) ||| (c 2 &&& c 8 &&& c 10) ||| (c 3 &&& c 5 &&& c 13) ||| (c 3 &&& c 6 &&& c 11) ||| (c 3 &&& c 8 &&& c 9) ||| (c 4 &&& c 5 &&& c 12) ||| (c 4 &&& c 6 &&& c 10) ||| (c 4 &&& c 7 &&& c 9)

theorem audit : ∀ h : Fin 9→Bool,(ops.foldl numStep (seed h)).getD out 0=target h := by decide +kernel
theorem targetBit (x : Fin 15→Bool) : (target (high x)).testBit (loIndex (low x)).val=posted x := by
  simp only [target,posted,Nat.testBit_and,Nat.testBit_or,reads]

theorem upper : HasCircuitSize 15 posted 34 := by
  refine ⟨circuit,?_,by decide +kernel,?_⟩
  · intro g hg
    change g∈ops.map gate at hg
    obtain ⟨t,_,rfl⟩:=List.mem_map.mp hg
    rcases t with ⟨d,a,b⟩
    fin_cases d <;> simp [gate]
  · intro x
    rw [←starts x]
    change ((ops.map gate).foldl boolStep (sample (seed (high x)) (loIndex (low x)).val)).getD out false=posted x
    rw [run,getSample,audit,targetBit]

end PEqualNP.Outside.L_meta_18854.Work
