import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_931.Clock
open Turing

inductive K | input | bank | back | acc | temp | build
  deriving DecidableEq
instance : Fintype K := ⟨{.input,.bank,.back,.acc,.temp,.build},by intro x; cases x <;> simp⟩
inductive L | getN | getT | scanB | scanA | restoreA | restoreB | clearA | moveC | drain | finish
  deriving DecidableEq
instance : Fintype L := ⟨{.getN,.getT,.scanB,.scanA,.restoreA,.restoreB,.clearA,.moveC,.drain,.finish},by intro x; cases x <;> simp⟩

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
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem stopN : Run 1 (cfg (some .getN) (false::xs) (b) (r) (a) (h) (c)) (cfg (some .getT) (xs) (b+1) (r) (a+1) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem readT : Run 1 (cfg (some .getT) (true::xs) (b) (r) (a) (h) (c)) (cfg (some .scanB) (xs) (b) (r) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem stopT : Run 1 (cfg (some .getT) (false::xs) (b) (r) (a) (h) (c)) (cfg (some .drain) (xs) (b) (r) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem takeB : Run 1 (cfg (some .scanB) (xs) (b+1) (r) (a) (h) (c)) (cfg (some .scanA) (xs) (b) (r+1) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem outB : Run 1 (cfg (some .scanB) (xs) (0) (r) (a) (h) (c)) (cfg (some .restoreB) (xs) (0) (r) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem takeA : Run 1 (cfg (some .scanA) (xs) (b) (r) (a+1) (h) (c)) (cfg (some .scanA) (xs) (b) (r) (a) (h+1) (c+1)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem outA : Run 1 (cfg (some .scanA) (xs) (b) (r) (0) (h) (c)) (cfg (some .restoreA) (xs) (b) (r) (0) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem putA : Run 1 (cfg (some .restoreA) (xs) (b) (r) (a) (h+1) (c)) (cfg (some .restoreA) (xs) (b) (r) (a+1) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem doneA : Run 1 (cfg (some .restoreA) (xs) (b) (r) (a) (0) (c)) (cfg (some .scanB) (xs) (b) (r) (a) (0) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem putB : Run 1 (cfg (some .restoreB) (xs) (b) (r+1) (a) (h) (c)) (cfg (some .restoreB) (xs) (b+1) (r) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem doneB : Run 1 (cfg (some .restoreB) (xs) (b) (0) (a) (h) (c)) (cfg (some .clearA) (xs) (b) (0) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem clearOne : Run 1 (cfg (some .clearA) (xs) (b) (r) (a+1) (h) (c)) (cfg (some .clearA) (xs) (b) (r) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem cleared : Run 1 (cfg (some .clearA) (xs) (b) (r) (0) (h) (c)) (cfg (some .moveC) (xs) (b) (r) (0) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem moveOne : Run 1 (cfg (some .moveC) (xs) (b) (r) (a) (h) (c+1)) (cfg (some .moveC) (xs) (b) (r) (a+1) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem moved : Run 1 (cfg (some .moveC) (xs) (b) (r) (a) (h) (0)) (cfg (some .getT) (xs) (b) (r) (a) (h) (0)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem drainOne : Run 1 (cfg (some .drain) (v::xs) (b) (r) (a) (h) (c)) (cfg (some .drain) (xs) (b) (r) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem drained : Run 1 (cfg (some .drain) ([]) (b) (r) (a) (h) (c)) (cfg (some .finish) ([]) (b) (r) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem eraseB : Run 1 (cfg (some .finish) (xs) (b+1) (r) (a) (h) (c)) (cfg (some .finish) (xs) (b) (r) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }
theorem halted : Run 1 (cfg (some .finish) (xs) (0) (r) (a) (h) (c)) (cfg none (xs) (0) (r) (a) (h) (c)) := by
  simp [Run,flip,cfg,TM2.step,prog,bit,nxt,jump,push,TM2.stepAux,stk,List.replicate_succ,
    List.replicate_zero,TM2.Cfg.mk.injEq]
  all_goals try { funext i; cases i <;> simp [Function.update,stk,List.replicate_succ] }


theorem copyA (j b r h c : Nat) (xs : List Bool) : Run j
    (cfg (some .scanA) xs b r j h c) (cfg (some .scanA) xs b r 0 (h+j) (c+j)) := by
  induction j generalizing h c with
  | zero => simpa using reflRun (cfg (some .scanA) xs b r 0 h c)
  | succ j ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      transRun takeA (ih (h+1) (c+1))

theorem returnA (j b r a c : Nat) (xs : List Bool) : Run j
    (cfg (some .restoreA) xs b r a j c) (cfg (some .restoreA) xs b r (a+j) 0 c) := by
  induction j generalizing a with
  | zero => simpa using reflRun (cfg (some .restoreA) xs b r a 0 c)
  | succ j ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using transRun putA (ih (a+1))

theorem returnB (j b a c : Nat) (xs : List Bool) : Run j
    (cfg (some .restoreB) xs b j a 0 c) (cfg (some .restoreB) xs (b+j) 0 a 0 c) := by
  induction j generalizing b with
  | zero => simpa using reflRun (cfg (some .restoreB) xs b 0 a 0 c)
  | succ j ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using transRun putB (ih (b+1))

theorem deleteA (j b c : Nat) (xs : List Bool) : Run j
    (cfg (some .clearA) xs b 0 j 0 c) (cfg (some .clearA) xs b 0 0 0 c) := by
  induction j with
  | zero => exact reflRun _
  | succ j ih => simpa [Nat.add_comm] using transRun clearOne ih

theorem moveAll (j b a : Nat) (xs : List Bool) : Run j
    (cfg (some .moveC) xs b 0 a 0 j) (cfg (some .moveC) xs b 0 (a+j) 0 0) := by
  induction j generalizing a with
  | zero => simpa using reflRun (cfg (some .moveC) xs b 0 a 0 0)
  | succ j ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using transRun moveOne (ih (a+1))

theorem scanOne (b r a c : Nat) (xs : List Bool) : Run (2*a+3)
    (cfg (some .scanB) xs (b+1) r a 0 c) (cfg (some .scanB) xs b (r+1) a 0 (c+a)) := by
  have h := transRun takeB (copyA a b (r+1) 0 c xs)
  simp only [Nat.zero_add] at h
  have j := transRun (transRun h outA) (returnA a b (r+1) 0 (c+a) xs)
  simp only [Nat.zero_add] at j
  convert transRun j doneA using 1 <;> omega

theorem scanAll (b r a c : Nat) (xs : List Bool) : Run (b*(2*a+3))
    (cfg (some .scanB) xs b r a 0 c) (cfg (some .scanB) xs 0 (r+b) a 0 (c+b*a)) := by
  induction b generalizing r c with
  | zero => simpa using reflRun (cfg (some .scanB) xs 0 r a 0 c)
  | succ b ih =>
    simpa [Nat.succ_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      transRun (scanOne b r a c xs) (ih (r+1) (c+a))

def roundCost (b a : Nat) := b*(2*a+3)+b+a+b*a+4

theorem round_run (b a : Nat) (xs : List Bool) : Run (roundCost b a)
    (cfg (some .scanB) xs b 0 a 0 0) (cfg (some .getT) xs b 0 (b*a) 0 0) := by
  have hs := scanAll b 0 a 0 xs
  simp only [Nat.zero_add] at hs
  have h1 := transRun (transRun hs outB) (returnB b 0 a (b*a) xs)
  simp only [Nat.zero_add] at h1
  have h2 := transRun (transRun h1 doneB) (deleteA a b (b*a) xs)
  have h3 := transRun (transRun h2 cleared) (moveAll (b*a) b 0 xs)
  simp only [Nat.zero_add] at h3
  convert transRun h3 moved using 1 <;> unfold roundCost <;> omega

def work (b a : Nat) : Nat → Nat
  | 0 => 0
  | t+1 => 1 + roundCost b a + work b (b*a) t
termination_by t => t

theorem powers (t b a : Nat) (xs : List Bool) : Run (work b a t)
    (cfg (some .getT) (List.replicate t true ++ xs) b 0 a 0 0)
    (cfg (some .getT) xs b 0 (a*b^t) 0 0) := by
  induction t generalizing a with
  | zero => simpa [work] using reflRun (cfg (some .getT) xs b 0 a 0 0)
  | succ t ih =>
    have h := transRun readT (round_run b a (List.replicate t true ++ xs))
    simpa [work,List.replicate_succ,pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      transRun h (ih (b*a))

theorem readNum (n b : Nat) (xs : List Bool) : Run n
    (cfg (some .getN) (List.replicate n true ++ xs) b 0 0 0 0)
    (cfg (some .getN) xs (b+n) 0 0 0 0) := by
  induction n generalizing b with
  | zero => simpa using reflRun (cfg (some .getN) xs b 0 0 0 0)
  | succ n ih =>
    simpa [List.replicate_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      transRun readN (ih (b+1))

theorem drainAll (xs : List Bool) (b a : Nat) : Run xs.length
    (cfg (some .drain) xs b 0 a 0 0) (cfg (some .drain) [] b 0 a 0 0) := by
  induction xs with
  | nil => exact reflRun _
  | cons v xs ih => simpa [Nat.add_comm] using transRun (drainOne (v:=v)) ih

theorem finishAll (b a : Nat) : Run b (cfg (some .finish) [] b 0 a 0 0)
    (cfg (some .finish) [] 0 0 a 0 0) := by
  induction b with
  | zero => exact reflRun _
  | succ b ih => simpa [Nat.add_comm] using transRun eraseB ih

def headN (n : Nat) := List.replicate n true ++ [false]
theorem program (n t : Nat) (tail : List Bool) :
    Run (n+1+work (n+1) 1 t+1+tail.length+1+(n+1)+1)
      (cfg (some .getN) (headN n ++ headN t ++ tail) 0 0 0 0 0)
      (cfg none [] 0 0 ((n+1)^t) 0 0) := by
  have hn := readNum n 0 (false :: (headN t ++ tail))
  simp only [Nat.zero_add] at hn
  have h1 := transRun hn stopN
  have ht := powers t (n+1) 1 (false :: tail)
  simp only [Nat.one_mul] at ht
  have h2 := transRun h1 (by simpa [headN,List.append_assoc] using ht)
  have h3 := transRun (transRun h2 stopT) (drainAll tail (n+1) ((n+1)^t))
  have h4 := transRun (transRun h3 drained) (finishAll (n+1) ((n+1)^t))
  simpa [headN,List.append_assoc] using transRun h4 halted


theorem work_bound (t b a : Nat) (hb : 1 ≤ b) :
    work b a t ≤ t * (5*(b+1)*(a*b^t+1)) := by
  induction t generalizing a with
  | zero => simp [work]
  | succ t ih =>
    have h := ih (b*a)
    have he : b*a*b^t = a*b^(t+1) := by rw [pow_succ]; ring
    rw [he] at h
    have ha : a ≤ a*b^(t+1) := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    have hstep : 1+roundCost b a ≤ 5*(b+1)*(a*b^(t+1)+1) := by
      calc 1+roundCost b a ≤ 5*(b+1)*(a+1) := by unfold roundCost; nlinarith
           _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    rw [work,Nat.succ_mul]
    omega

theorem exact_exponent (n t : Nat) (tail : List Bool) :
    n+1+work (n+1) 1 t+1+tail.length+1+(n+1)+1 ≤
      ((headN n ++ headN t ++ tail).length + 2) ^ (t+4) := by
  let N := (headN n ++ headN t ++ tail).length+2
  have hN : N=n+t+tail.length+4 := by simp [N,headN]; omega
  have hN1 : 1 ≤ N := by omega
  have hB : (n+1)^t ≤ N^t := Nat.pow_le_pow_left (by omega) _
  have hP : 1 ≤ N^t := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have hW := work_bound t (n+1) 1 (by omega)
  simp only [Nat.one_mul] at hW
  have hW' : work (n+1) 1 t ≤ 10*N^t*N^2 := by
    calc work (n+1) 1 t ≤ _ := hW
         _ ≤ N*(5*N*(2*N^t)) := by
           apply Nat.mul_le_mul (by omega)
           apply Nat.mul_le_mul (Nat.mul_le_mul_left 5 (by omega))
           omega
         _ = _ := by ring
  have hNle : N ≤ N^t*N^2 := by
    have ha : N ≤ N^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
    exact ha.trans (Nat.le_mul_of_pos_left _ (by omega))
  have h13 : 13 ≤ N^2 := by rw [pow_two]; nlinarith [show 4 ≤ N by omega]
  rw [mul_assoc] at hW'
  change _ ≤ N^(t+4)
  calc _ ≤ 13*(N^t*N^2) := by omega
       _ ≤ N^2*(N^t*N^2) := Nat.mul_le_mul_right _ h13
       _ = _ := by rw [show t+4=t+2+2 by omega,pow_add,pow_add]; ring

lemma i7 (tm:FinTM2) (s:List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main,tm.initialState,Function.update (fun _=>[]) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold initList
  congr 1
  funext k
  by_cases h:k=tm.k₀
  · subst h;simp
  · simp [h]
lemma i9 (tm:FinTM2) (s:List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none,tm.initialState,Function.update (fun _=>[]) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold haltList
  congr 1
  funext k
  by_cases h:k=tm.k₁
  · subst h;simp
  · simp [h]

def machine : TM2ComputableAux Bool Bool := ⟨tm,Equiv.refl _,Equiv.refl _⟩

theorem finite_alphabet (i : machine.tm.K) : Finite (machine.tm.Γ i) := inferInstanceAs (Finite Bool)

theorem clocked (n t : Nat) (tail : List Bool) :
    let x := headN n ++ headN t ++ tail
    Nonempty (TM2OutputsInTime machine.tm (x.map machine.inputAlphabet.invFun)
      (some ((List.replicate ((n+1)^t) true).map machine.outputAlphabet.invFun))
      ((x.length+2)^(t+4))) := by
  dsimp only
  refine ⟨{steps := n+1+work (n+1) 1 t+1+tail.length+1+(n+1)+1
           steps_le_m := exact_exponent n t tail
           evals_in_steps := ?_}⟩
  have hinit (x : List Bool) : initList tm x = cfg (some .getN) x 0 0 0 0 0 := by
    rw [i7]
    change (⟨some .getN,false,Function.update (fun _ : K => ([] : List Bool)) K.input x⟩ : State) = _
    unfold cfg
    congr 1
    funext i
    cases i <;> simp [tm,stk,Function.update]
  have hhalt (k : Nat) : haltList tm (List.replicate k true) = cfg none [] 0 0 k 0 0 := by
    rw [i9]
    change (⟨none,false,Function.update (fun _ : K => ([] : List Bool)) K.acc (List.replicate k true)⟩ : State) = _
    unfold cfg
    congr 1
    funext i
    cases i <;> simp [tm,stk,Function.update]
  change (flip bind (TM2.step prog))^[_] (some (initList tm (List.map (Equiv.refl Bool).invFun _))) =
    some (haltList tm (List.map (Equiv.refl Bool).invFun _))
  have hm (l : List Bool) : l.map (Equiv.refl Bool).invFun = l := by simp
  let x := headN n ++ headN t ++ tail
  let z := List.replicate ((n+1)^t) true
  let rounds := n+1+work (n+1) 1 t+1+tail.length+1+(n+1)+1
  have mid : (flip bind (TM2.step prog))^[rounds] (some (initList tm x)) = some (haltList tm z) :=
    (congrArg (fun q : State => (flip bind (TM2.step prog))^[rounds] (some q)) (hinit x)).trans
      ((program n t tail).trans (congrArg some (hhalt ((n+1)^t))).symm)
  exact (congrArg (fun y : List Bool =>
    (flip bind (TM2.step prog))^[rounds] (some (initList tm y))) (hm x)).trans
    (mid.trans (congrArg (fun y : List Bool => some (haltList tm y)) (hm z)).symm)

end PEqualNP.Outside.L_lib_931.Clock
