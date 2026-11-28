import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_931.Clock
open Turing

inductive K | input | bank | back | acc | temp | build
  deriving DecidableEq, Fintype
inductive L | getN | getT | scanB | scanA | restoreA | restoreB | clearA | moveC | drain | finish
  deriving DecidableEq, Fintype

abbrev Stmt := TM2.Stmt (fun _ : K => Bool) L Bool
abbrev State := TM2.Cfg (fun _ : K => Bool) L Bool
def jump (b : L) : Stmt := .load (fun _ => false) (.goto (fun _ => b))
def push (k : K) (q : Stmt) : Stmt := .push k (fun _ => true) q
def nxt (k : K) (p q : Stmt) : Stmt := .pop k (fun _ o => o.isSome) (.branch id p q)
def bit (p q : Stmt) : Stmt := .pop K.input (fun _ o => o.getD false) (.branch id p q)
def prog : L → Stmt
  | .getN => bit (push .bank (jump .getN)) (push .bank (push .acc (jump .getT)))
  | .getT => bit (jump .scanB) (jump .drain)
  | .scanB => nxt .bank (push .back (jump .scanA)) (jump .restoreB)
  | .scanA => nxt .acc (push .temp (push .build (jump .scanA))) (jump .restoreA)
  | .restoreA => nxt .temp (push .acc (jump .restoreA)) (jump .scanB)
  | .restoreB => nxt .back (push .bank (jump .restoreB)) (jump .clearA)
  | .clearA => nxt .acc (jump .clearA) (jump .moveC)
  | .moveC => nxt .build (push .acc (jump .moveC)) (jump .getT)
  | .drain => nxt .input (jump .drain) (jump .finish)
  | .finish => nxt .bank (jump .finish) (.load (fun _ => false) .halt)

def tm : FinTM2 where
  K := K
  k₀ := .input
  k₁ := .acc
  Γ _ := Bool
  Λ := L
  main := .getN
  σ := Bool
  initialState := false
  m := prog

def stk (xs : List Bool) (b r a h c : Nat) : K → List Bool
  | .input => xs | .bank => List.replicate b true | .back => List.replicate r true
  | .acc => List.replicate a true | .temp => List.replicate h true | .build => List.replicate c true

def cfg (l : Option L) (xs : List Bool) (b r a h c : Nat) : State := ⟨l,false,stk xs b r a h c⟩
def Run (n : Nat) (x y : State) := (flip bind (TM2.step prog))^[n] (some x) = some y
theorem reflRun (x : State) : Run 0 x x := rfl
theorem transRun {n k x y z} (h : Run n x y) (j : Run k y z) : Run (n+k) x z := by
  unfold Run at *
  rw [Nat.add_comm,Function.iterate_add_apply,h]
  exact j

variable {xs : List Bool} {b r a h c : Nat} {v : Bool}
theorem readN : Run 1 (cfg (some .getN) (true::xs) (b) (r) (a) (h) (c)) (cfg (some .getN) (xs) (b+1) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem stopN : Run 1 (cfg (some .getN) (false::xs) (b) (r) (a) (h) (c)) (cfg (some .getT) (xs) (b+1) (r) (a+1) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem readT : Run 1 (cfg (some .getT) (true::xs) (b) (r) (a) (h) (c)) (cfg (some .scanB) (xs) (b) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem stopT : Run 1 (cfg (some .getT) (false::xs) (b) (r) (a) (h) (c)) (cfg (some .drain) (xs) (b) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem takeB : Run 1 (cfg (some .scanB) (xs) (b+1) (r) (a) (h) (c)) (cfg (some .scanA) (xs) (b) (r+1) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem outB : Run 1 (cfg (some .scanB) (xs) (0) (r) (a) (h) (c)) (cfg (some .restoreB) (xs) (0) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem takeA : Run 1 (cfg (some .scanA) (xs) (b) (r) (a+1) (h) (c)) (cfg (some .scanA) (xs) (b) (r) (a) (h+1) (c+1)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem outA : Run 1 (cfg (some .scanA) (xs) (b) (r) (0) (h) (c)) (cfg (some .restoreA) (xs) (b) (r) (0) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem putA : Run 1 (cfg (some .restoreA) (xs) (b) (r) (a) (h+1) (c)) (cfg (some .restoreA) (xs) (b) (r) (a+1) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem doneA : Run 1 (cfg (some .restoreA) (xs) (b) (r) (a) (0) (c)) (cfg (some .scanB) (xs) (b) (r) (a) (0) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem putB : Run 1 (cfg (some .restoreB) (xs) (b) (r+1) (a) (h) (c)) (cfg (some .restoreB) (xs) (b+1) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem doneB : Run 1 (cfg (some .restoreB) (xs) (b) (0) (a) (h) (c)) (cfg (some .clearA) (xs) (b) (0) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem clearOne : Run 1 (cfg (some .clearA) (xs) (b) (r) (a+1) (h) (c)) (cfg (some .clearA) (xs) (b) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem cleared : Run 1 (cfg (some .clearA) (xs) (b) (r) (0) (h) (c)) (cfg (some .moveC) (xs) (b) (r) (0) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem moveOne : Run 1 (cfg (some .moveC) (xs) (b) (r) (a) (h) (c+1)) (cfg (some .moveC) (xs) (b) (r) (a+1) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem moved : Run 1 (cfg (some .moveC) (xs) (b) (r) (a) (h) (0)) (cfg (some .getT) (xs) (b) (r) (a) (h) (0)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem drainOne : Run 1 (cfg (some .drain) (v::xs) (b) (r) (a) (h) (c)) (cfg (some .drain) (xs) (b) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem drained : Run 1 (cfg (some .drain) ([]) (b) (r) (a) (h) (c)) (cfg (some .finish) ([]) (b) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem eraseB : Run 1 (cfg (some .finish) (xs) (b+1) (r) (a) (h) (c)) (cfg (some .finish) (xs) (b) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem halted : Run 1 (cfg (some .finish) (xs) (0) (r) (a) (h) (c)) (cfg none (xs) (0) (r) (a) (h) (c)) := by
  change TM2.step prog _ = some _
  simp [cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }

end PEqualNP.Outside.L_lib_931.Clock
