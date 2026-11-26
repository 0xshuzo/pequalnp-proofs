import Mathlib
import PEqualNP.Outside.L_meta_18284

namespace PEqualNP.Outside.L_meta_4037_pilot

def edges10 : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def hasEdge (x : Fin 10 → Bool) : Bool :=
  edges10.any (fun e => x e.1 && x e.2)

def row (r : Fin 512) (b : Bool) (i : Fin 10) : Bool :=
  if i.val = 0 then b else r.val.testBit (i.val-1)

def adj (i j : Fin 9) : Bool :=
  edges10.any fun e => (e.1 == i.succ && e.2 == j.succ) || (e.2 == i.succ && e.1 == j.succ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem maskingPairs : ∀ (i j : Fin 9) (b c : Bool),
    (∃ r : Fin 512, r.val.testBit i.val = b ∧ r.val.testBit j.val = c ∧
      hasEdge (row r false) = false ∧ hasEdge (row r true) = true) ↔
    (i = j → b = c) ∧ (b = true → c = true → adj i j = false) := by
  decide +kernel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def noRead (s : ℕ) (g : Gate) :=
  (g.op = .not → g.inputs.head? ≠ some s) ∧ (g.op ≠ .not → s ∉ g.inputs)

def maskGate (pin : Nat) (i : Fin 9) (b : Bool) (g : Gate) :=
  g.op = (if b then GateOp.or else GateOp.and) ∧
  (g.inputs = [pin,i.succ.val] ∨ g.inputs = [i.succ.val,pin])

def valAt (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun k => w.getD k false)
def extend (w : List Bool) (g : Gate) := w ++ [valAt w g]

def same (w t : List Bool) :=
  ∀ k : ℕ, k ≠ 0 → k ≠ 10 → w.getD k false = t.getD k false

lemma gateSame (g : Gate) (legal : g.op ∈ ({GateOp.and,.or,.not} : Set GateOp))
    (z : noRead 0 g) (s : noRead 10 g) {w t : List Bool} (eq : same w t) :
    valAt w g = valAt t g := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at legal
  by_cases hn : g.op = .not
  · have hz := z.1 hn
    have hs := s.1 hn
    unfold valAt
    rw [hn]
    cases hi : g.inputs with
    | nil => rfl
    | cons a as =>
      rw [hi] at hz hs
      simp only [List.head?_cons,ne_eq,Option.some.injEq] at hz hs
      change !(w.getD a false) = !(t.getD a false)
      rw [eq a hz hs]
  · unfold valAt
    congr 1
    apply List.map_congr_left
    intro k hk
    exact eq k (fun h => z.2 hn (h ▸ hk)) (fun h => s.2 hn (h ▸ hk))

lemma fixedGate (pin : Nat) (i : Fin 9) (b : Bool) {g : Gate} (h : maskGate pin i b g) (w : List Bool)
    (hval : w.getD i.succ.val false = b) : valAt w g = b := by
  obtain ⟨hop,hargs⟩ := h
  unfold valAt
  rw [hop]
  rcases hargs with h | h <;> rw [h] <;> cases b <;>
    simp [GateOp.eval,hval]

lemma sameAppend {w t : List Bool} {b : Bool} (eq : same w t) (len : w.length=t.length) :
    same (w++[b]) (t++[b]) := by
  intro k hk hs
  by_cases lt : k < w.length
  · rw [List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ (len ▸ lt),eq k hk hs]
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt lt),
        List.getD_append_right _ _ _ _ (len ▸ Nat.le_of_not_gt lt),len]

def maskedRun (gs : List Gate) (w : List Bool) := gs.foldl extend w

lemma maskSim (i j : Fin 9) (b c : Bool) (gs : List Gate) (w t : List Bool)
    (len : w.length=t.length) (pref : 11 ≤ w.length) (eq : same w t)
    (vi : w.getD i.succ.val false = b) (vj : w.getD j.succ.val false = c)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,.or,.not} : Set GateOp))
    (covered : ∀ g ∈ gs, (noRead 0 g ∧ noRead 10 g) ∨ maskGate 0 i b g ∨ maskGate 10 j c g) :
    same (maskedRun gs w) (maskedRun gs t) := by
  induction gs generalizing w t with
  | nil => exact eq
  | cons g gs ih =>
    have gateEq : valAt w g = valAt t g := by
      rcases covered g (by simp) with no | m | m
      · exact gateSame g (legal g (by simp)) no.1 no.2 eq
      · rw [fixedGate 0 i b m w vi, fixedGate 0 i b m t]
        exact (eq _ (by simp) (by have := i.isLt; simp; omega)).symm.trans vi
      · rw [fixedGate 10 j c m w vj, fixedGate 10 j c m t]
        exact (eq _ (by simp) (by have := j.isLt; simp; omega)).symm.trans vj
    apply ih (extend w g) (extend t g) (by simp [extend,len]) (by simp [extend]; omega)
    · unfold extend
      rw [gateEq]
      exact sameAppend eq len
    · rw [extend,List.getD_append _ _ _ _ (by have := i.isLt; simp; omega)]
      exact vi
    · rw [extend,List.getD_append _ _ _ _ (by have := j.isLt; simp; omega)]
      exact vj
    · exact fun q h => legal q (by simp [h])
    · exact fun q h => covered q (by simp [h])

def augmented (x : Fin 10 → Bool) := List.ofFn x ++ [!x 0]

lemma rawVal (x : Fin 10 → Bool) (k : Fin 10) :
    (augmented x).getD k.val false = x k := by
  rw [augmented, List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma stayInput (gs : List Gate) (w : List Bool) (k : ℕ) (small : k < w.length) :
    (maskedRun gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (maskedRun gs (extend w g)).getD k false = _
    rw [ih (extend w g) (by simp [extend]; omega),extend,List.getD_append _ _ _ _ small]

theorem remainingMaskPairs (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x, C.eval (augmented x) = hasEdge x)
    (i j : Fin 9) (b c : Bool)
    (covered : ∀ g ∈ C.gates, (noRead 0 g ∧ noRead 10 g) ∨ maskGate 0 i b g ∨ maskGate 10 j c g) :
    (i = j ∧ b ≠ c) ∨ (b = true ∧ c = true ∧ adj i j = true) := by
  by_contra! bad
  have dif : i = j → b = c := by aesop
  have edge : b = true → c = true → adj i j = false := by
    intro hb hc
    cases h : adj i j <;> aesop
  obtain ⟨r,ri,rj,neg,pos⟩ := (maskingPairs i j b c).mpr ⟨dif,edge⟩
  let x := row r false
  let y := row r true
  have eq : same (augmented x) (augmented y) := by
    intro k hz hs
    by_cases lt : k < 10
    · let u : Fin 10 := ⟨k,lt⟩
      rw [show k = u.val from rfl,rawVal,rawVal]
      simp [x,y,row,u,hz]
    · rw [List.getD_eq_default _ _ (by simp [augmented]; omega),List.getD_eq_default _ _ (by simp [augmented]; omega)]
  have agrees := maskSim i j b c C.gates (augmented x) (augmented y) (by simp [augmented])
    (by simp [augmented]) eq
    (by rw [rawVal]; simpa [x,row] using ri)
    (by rw [rawVal]; simpa [x,row] using rj)
    (fun g hg => (fan g hg).1) covered
  have left : C.output ≠ 0 := by
    intro h
    let s : Fin 10 → Bool := fun v => decide (v=0)
    have H := correct s
    change (maskedRun C.gates (augmented s)).getD C.output false = hasEdge s at H
    rw [h,stayInput _ _ _ (by decide)] at H
    exact (by decide : (augmented s).getD 0 false ≠ hasEdge s) H
  have right : C.output ≠ 10 := by
    intro h
    let s : Fin 10 → Bool := fun _ => false
    have H := correct s
    change (maskedRun C.gates (augmented s)).getD C.output false = hasEdge s at H
    rw [h,stayInput _ _ _ (by decide)] at H
    exact (by decide : (augmented s).getD 10 false ≠ hasEdge s) H
  have H : C.eval (augmented x) = C.eval (augmented y) := agrees C.output left right
  rw [correct,correct,neg,pos] at H
  contradiction


theorem differentRaw (C : Circuit) (fan : FanInTwo C) (correct : ∀ x,C.eval (augmented x)=hasEdge x)
    (i j : Fin 9)
    (covered : ∀ g ∈ C.gates, (noRead 0 g ∧ noRead 10 g) ∨ maskGate 0 i true g ∨ maskGate 10 j false g) :
    i=j := by
  rcases remainingMaskPairs C fan correct i j true false covered with h|h
  · exact h.1
  · exact False.elim (Bool.false_ne_true h.2.1)

def target (x : Fin 10 → Bool) :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

theorem oneNot (C : Circuit) (fan : FanInTwo C) (budget : C.size=18)
    (correct : ∀ x, C.eval (augmented x)=target x) : PEqualNP.NotBracket.notCount C ≤ 1 := by
  let pre : Gate := ⟨.not,[0]⟩
  let D : Circuit := ⟨pre :: C.gates,C.output⟩
  have legal : FanInTwo D := by
    intro g hg
    change g ∈ pre :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl | member
    · simp [pre]
    · exact fan _ member
  have newInput (x : Fin 10 → Bool) :
      pre.op.eval (pre.inputs.map fun i => (List.ofFn x).getD i false) = !x 0 := by
    change !((List.ofFn x).getD 0 false) = !(x 0)
    rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have ev (x : Fin 10 → Bool) : D.eval (List.ofFn x)=target x := by
    rw [← correct x]
    change (C.gates.foldl _ (List.ofFn x ++ [pre.op.eval (pre.inputs.map fun i => (List.ofFn x).getD i false)])).getD C.output false = _
    rw [newInput] <;> rfl
  have bound := PEqualNP.Outside.L_meta_18284 D legal ev
  have n : PEqualNP.NotBracket.notCount D = 1+PEqualNP.NotBracket.notCount C := by
    simp [PEqualNP.NotBracket.notCount,D,pre,Nat.add_comm]
  have sizeD : D.size=C.size+1 := rfl
  omega

def avoidZero (g : Gate) : Prop :=
  (g.op = .not → g.inputs.head? ≠ some 0) ∧ (g.op ≠ .not → 0 ∉ g.inputs)

def gateVal (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) := w ++ [gateVal w g]

def dominated (a b : List Bool) : Prop :=
  ∀ i : ℕ, i ≠ 0 → a.getD i false = true → b.getD i false = true

lemma binaryDominated (a b : List Bool) (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    (avoid : avoidZero g) (h : dominated a b) :
    gateVal a g = true → gateVal b g = true := by
  rcases hg with ha | ho
  · have hz := avoid.2 (by rw [ha]; intro eq; cases eq)
    simp only [gateVal, ha, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro H t ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact h i (fun e => hz (e ▸ hi)) (H _ ⟨i, hi, rfl⟩)
  · have hz := avoid.2 (by rw [ho]; intro eq; cases eq)
    simp only [gateVal, ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨t, ⟨i, hi, rfl⟩, hv⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i (fun e => hz (e ▸ hi)) hv⟩

lemma stepDominated (a b : List Bool) (g : Gate) (len : a.length = b.length)
    (h : dominated a b) (hg : gateVal a g = true → gateVal b g = true) :
    dominated (step a g) (step b g) := by
  intro i hn H
  by_cases small : i < a.length
  · rw [step,List.getD_append _ _ _ _ small] at H
    rw [step,List.getD_append _ _ _ _ (len ▸ small)]
    exact h i hn H
  by_cases eq : i = a.length
  · subst i
    simpa [step, List.getD_eq_getElem?_getD, len] using
      hg (by simpa [step, List.getD_eq_getElem?_getD] using H)
  · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at H
    contradiction

def localColumn (gs : List Gate) (w : List Bool) (j : Fin gs.length) : Bool :=
  gateVal ((gs.take j.val).foldl step w) (gs.get j)

lemma dominatedUnless (gs : List Gate) (a b : List Bool) (len : a.length = b.length)
    (initial : dominated a b)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, .or, .not} : Set GateOp))
    (idx : Fin 9) (pref : 11≤a.length)
    (valueB : b.getD idx.succ.val false=true)
    (avoid : ∀ g ∈ gs, avoidZero g ∨ maskGate 0 idx true g)
    (pass : ∀ j : Fin gs.length, (gs.get j).op = .not →
      localColumn gs a j = true → localColumn gs b j = true) :
    dominated (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact initial
  | cons g gs ih =>
    have op := legal g (by simp)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    have hstep : gateVal a g = true → gateVal b g = true := by
      rcases avoid g (by simp) with hz|mask
      · rcases op with h | h | h
        · exact binaryDominated a b g (Or.inl h) hz initial
        · exact binaryDominated a b g (Or.inr h) hz initial
        · exact pass ⟨0,by simp⟩ h
      · intro _
        exact fixedGate 0 idx true mask b valueB
    apply ih (step a g) (step b g) (by simp [step,len])
      (stepDominated a b g len initial hstep)
    · exact fun q h => legal q (by simp [h])
    · simp [step]; omega
    · rw [step,List.getD_append _ _ _ _ (by have := idx.isLt; simp; omega)]
      exact valueB
    · exact fun q h => avoid q (by simp [h])
    · intro j h ha
      let k : Fin (g::gs).length := ⟨j.val+1,by simp; have := j.isLt; omega⟩
      exact pass k h ha



/-- On every sensitive row containing the raw partner of the positive marked OR,
some internal NOT has a strictly increasing output. -/
theorem rawPartnerNot (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x,C.eval (augmented x)=hasEdge x) (idx : Fin 9)
    (avoid : ∀ g∈C.gates,avoidZero g ∨ maskGate 0 idx true g)
    (r : Fin 512) (bit : r.val.testBit idx.val=true)
    (lo : hasEdge (row r false)=false) (hi : hasEdge (row r true)=true) :
    ∃ j : Fin C.gates.length, (C.gates.get j).op=.not ∧
      localColumn C.gates (augmented (row r true)) j=true ∧
      localColumn C.gates (augmented (row r false)) j=false := by
  let a := augmented (row r true)
  let b := augmented (row r false)
  have initial : dominated a b := by
    intro k hk h
    by_cases small : k<10
    · let v : Fin 10 := ⟨k,small⟩
      change (augmented (row r true)).getD v.val false=true at h
      change (augmented (row r false)).getD v.val false=true
      rw [rawVal] at h ⊢
      simpa [row,v,hk] using h
    · by_cases special : k=10
      · subst k
        have dead : a.getD 10 false = false := by
          change (List.ofFn (row r true) ++ [_]).getD 10 false=false
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp [row]
        rw [dead] at h
        contradiction
      · rw [List.getD_eq_default _ _ (by simp [a,augmented]; omega)] at h
        contradiction
  have output : C.output≠0 := by
    intro h
    let s : Fin 10 → Bool := fun v => decide (v=0)
    have he := correct s
    change (maskedRun C.gates (augmented s)).getD C.output false=hasEdge s at he
    rw [h,stayInput _ _ _ (by decide)] at he
    exact (by decide : (augmented s).getD 0 false ≠ hasEdge s) he
  by_contra! no
  have pass (j : Fin C.gates.length) (hn : (C.gates.get j).op=.not)
      (hot : localColumn C.gates a j=true) : localColumn C.gates b j=true := by
    cases eq : localColumn C.gates b j
    · exact False.elim (by simpa [eq,a,b] using no j hn hot)
    · rfl
  have valB : b.getD idx.succ.val false=true := by
    rw [show b=augmented (row r false) by rfl,rawVal]
    simpa [row] using bit
  have rel := dominatedUnless C.gates a b (by simp [a,b,augmented]) initial (fun g hg => (fan g hg).1)
    idx (by simp [a,augmented]) valB avoid pass
  have on : C.eval a=true := (correct _).trans hi
  have off : C.eval b=false := (correct _).trans lo
  exact Bool.noConfusion ((rel C.output output on).symm.trans off)

theorem rawPositiveImpossible (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x,C.eval (augmented x)=hasEdge x) (idx : Fin 9)
    (avoid : ∀ g∈C.gates,avoidZero g ∨ maskGate 0 idx true g)
    (mono : ∀ g∈C.gates,g.op≠.not) : False := by
  have diagonal : ∀ i : Fin 9, adj i i=false := by decide +kernel
  obtain ⟨r,rp,_,lo,hi⟩ := (maskingPairs idx idx true true).mpr
    ⟨by simp,fun _ _ => diagonal idx⟩
  obtain ⟨j,hn,_,_⟩ := rawPartnerNot C fan correct idx avoid r rp lo hi
  exact mono _ (List.get_mem _ _) hn

end PEqualNP.Outside.L_meta_4037_pilot
