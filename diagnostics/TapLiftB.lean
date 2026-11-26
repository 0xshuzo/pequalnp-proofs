import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9806.CoreTap
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def raw : Fin 12 → Fin 14 := ![4,1,5,2,6,3,7,11,8,12,9,13]
def proj (x : Fin 14 → Bool) (i : Fin 12) := x (raw i)
def ren (i : Nat) := if h : i<12 then (raw ⟨i,h⟩).val else i+2
theorem ren_lt (i : Fin 12) : ren i.val<14 := by
  rw [ren,dif_pos i.isLt]
  exact (raw i).isLt
theorem ren_ge {i : Nat} (h : 12 ≤ i) : ren i=i+2 := by simp [ren,show ¬i<12 by omega]
theorem ren_raw (i : Fin 12) : ren i.val=(raw i).val := by simp [ren,i.isLt]

theorem getD_ge (w : List Bool) (i : Nat) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def gstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gstep_length (w : List Bool) (g : Gate) : (gstep w g).length = w.length + 1 := by
  simp [gstep]

theorem gstep_getD_lt (w : List Bool) (g : Gate) {i : ℕ} (h : i < w.length) :
    (gstep w g).getD i false = w.getD i false :=
  List.getD_append _ _ _ _ h

theorem gstep_getD_last (w : List Bool) (g : Gate) :
    (gstep w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [gstep, List.getD_eq_getElem?_getD]

theorem gstep_or (w : List Bool) (a b : ℕ) :
    (gstep w ⟨.or, [a, b]⟩).getD w.length false = (w.getD a false || w.getD b false) := by
  rw [gstep_getD_last]; simp [GateOp.eval]

theorem fold_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl gstep w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih => intro w; rw [List.foldl_cons, ih, gstep_length, List.length_cons]; omega

theorem fold_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl gstep w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ _ (by rw [gstep_length]; omega), gstep_getD_lt _ _ h]

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

-- A gate with its wires renamed.
def renGate (g : Gate) : Gate := ⟨g.op, g.inputs.map ren⟩

-- The wire list `w'` carries every wire of `w` at its renamed place.
def Agree (w w' : List Bool) : Prop :=
  w'.length = w.length + 2 ∧ 12 ≤ w.length ∧ ∀ i, w'.getD (ren i) false = w.getD i false

-- Evaluating gates on `w` and the renamed gates on `w'` keeps the two wire lists in agreement.
theorem agree_fold (gs : List Gate) : ∀ w w' : List Bool, Agree w w' →
    Agree (gs.foldl gstep w) ((gs.map renGate).foldl gstep w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    rintro w w' ⟨hl, h12, hr⟩
    refine ih _ _ ⟨by rw [gstep_length, gstep_length, hl], by rw [gstep_length]; omega,
      fun i => ?_⟩
    rcases lt_trichotomy i w.length with hi | rfl | hi
    · have hi' : ren i < w'.length := by
        by_cases h : i < 12
        · exact (ren_lt ⟨i, h⟩).trans_le (by omega)
        · rw [ren_ge (by omega)]; omega
      rw [gstep_getD_lt _ _ hi', gstep_getD_lt _ _ hi, hr]
    · rw [ren_ge h12, ← hl, gstep_getD_last, gstep_getD_last]
      simp only [renGate, List.map_map, Function.comp_def, hr]
    · rw [ren_ge (by omega), getD_ge _ _ (by rw [gstep_length]; omega),
        getD_ge _ _ (by rw [gstep_length]; omega)]



theorem base_agree (x : Fin 14 → Bool) : Agree (List.ofFn (proj x)) (List.ofFn x) := by
  refine ⟨by simp,by simp,fun i => ?_⟩
  by_cases hi : i<12
  · let j : Fin 12 := ⟨i,hi⟩
    change (List.ofFn x).getD (ren j.val) false = _
    rw [ren_raw,getD_ofFn _ _ (raw j).isLt,getD_ofFn _ _ hi]
    rfl
  · rw [ren_ge (by omega),getD_ge _ _ (by simp; omega),getD_ge _ _ (by simp; omega)]
def tail (C : Circuit) (tap : Nat) : List Gate :=
  [⟨.or,[0,ren tap]⟩,⟨.and,[10,14+C.size]⟩,⟨.or,[ren C.output,14+C.size+1]⟩]
def liftC (C : Circuit) (tap : Nat) : Circuit :=
  ⟨C.gates.map renGate ++ tail C tap,14+C.size+2⟩
theorem cost (C : Circuit) (tap : Nat) : (liftC C tap).size=C.size+3 := by simp [liftC,Circuit.size,tail]
theorem fan (C : Circuit) (tap : Nat) (h : FanInTwo C) : FanInTwo (liftC C tap) := by
  intro g hg
  change g∈C.gates.map renGate ++ tail C tap at hg
  rcases List.mem_append.mp hg with a|a
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp a
    simpa [renGate] using h u hu
  · simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at a
    rcases a with rfl|rfl|rfl <;> simp
theorem gstep_and (w : List Bool) (a b : Nat) :
    (gstep w ⟨.and,[a,b]⟩).getD w.length false = (w.getD a false && w.getD b false) := by
  rw [gstep_getD_last]; simp [GateOp.eval]

theorem lift_eval (C : Circuit) (tap : Nat) (valid : C.output < 12+C.size) (x : Fin 14 → Bool) :
    (liftC C tap).eval (List.ofFn x) =
      (C.eval (List.ofFn (proj x)) || (x 10 && (x 0 || (C.wires (List.ofFn (proj x))).getD tap false))) := by
  let W := (C.gates.map renGate).foldl gstep (List.ofFn x)
  let z := 14+C.size
  have hw : W.length=z := by simp [W,z,fold_length,Circuit.size]
  obtain ⟨_,_,hr⟩ := agree_fold C.gates _ _ (base_agree x)
  have old : W.getD (ren C.output) false=C.eval (List.ofFn (proj x)) := hr _
  have tp : W.getD (ren tap) false=(C.wires (List.ofFn (proj x))).getD tap false := hr _
  have pin (i : Fin 14) : W.getD i.val false=x i := by
    change ((C.gates.map renGate).foldl gstep (List.ofFn x)).getD _ false=_
    rw [fold_getD_lt _ _ _ (by simp),getD_ofFn _ _ i.isLt]
  have ok : ren C.output<W.length := by
    rw [hw]
    by_cases h : C.output<12
    · have H : ren C.output < 14 := ren_lt ⟨C.output,h⟩; dsimp [z]; omega
    · rw [ren_ge (by omega)]; dsimp [z]; omega
  let W1 := gstep W ⟨.or,[0,ren tap]⟩
  let W2 := gstep W1 ⟨.and,[10,z]⟩
  have l1 : W1.length=z+1 := by change (gstep W _).length=_; rw [gstep_length,hw]
  have l2 : W2.length=z+2 := by change (gstep W1 _).length=_; rw [gstep_length,l1]
  have out1 : W1.getD (ren C.output) false=C.eval (List.ofFn (proj x)) := (gstep_getD_lt _ _ ok).trans old
  have out2 : W2.getD (ren C.output) false=C.eval (List.ofFn (proj x)) :=
    (gstep_getD_lt _ _ (by omega : ren C.output<W1.length)).trans out1
  have raw10 : W1.getD 10 false = x 10 :=
    (gstep_getD_lt _ _ (by dsimp [z] at hw; omega : 10<W.length)).trans (pin 10)
  have q1 : W1.getD z false=(x 0 || (C.wires (List.ofFn (proj x))).getD tap false) := by
    change (gstep W _).getD z false=_
    have p0 : W.getD 0 false=x 0 := pin 0
    rw [←hw,gstep_or,p0,tp]
  have q2 : W2.getD (z+1) false=(x 10 && (x 0 || (C.wires (List.ofFn (proj x))).getD tap false)) := by
    change (gstep W1 _).getD (z+1) false=_
    rw [←l1,gstep_and,raw10,q1]
  change ((C.gates.map renGate ++ tail C tap).foldl gstep (List.ofFn x)).getD (z+2) false=_
  rw [List.foldl_append]
  change (gstep W2 ⟨.or,[ren C.output,z+1]⟩).getD (z+2) false=_
  rw [←l2,gstep_or,out2,q2]
def small (x : Fin 12 → Bool) := (x 0 && x 7) || (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 9) || (x 2 && x 10) || (x 3 && x 8) || (x 3 && x 9) || (x 3 && x 11) || (x 4 && x 7) || (x 4 && x 8) || (x 4 && x 10) || (x 5 && x 6) || (x 5 && x 7) || (x 5 && x 9)
def target (x : Fin 14 → Bool) := (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
theorem decomposition (x : Fin 14 → Bool) : target x = (small (proj x) || (x 10 && (x 0 || (x 4 || x 5)))) := by
  change ((x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)) = ((x 4 && x 11) || (x 4 && x 13) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 5 && x 12) || (x 5 && x 9) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 6 && x 11) || (x 6 && x 8) || (x 6 && x 9) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 10 && (x 0 || (x 4 || x 5))))
  simp only [Bool.and_or_distrib_left] <;> ac_rfl
theorem tap_suffices (C : Circuit) (tap : Nat) (ok : FanInTwo C) (size : C.size≤21)
    (valid : C.output<12+C.size) (ev : ∀y : Fin 12 → Bool,C.eval (List.ofFn y)=small y)
    (second : ∀y : Fin 12 → Bool,small y=false →
       (C.wires (List.ofFn y)).getD tap false=(y 0 || y 2)) :
    HasCircuitSize 14 target 24 := by
  refine ⟨liftC C tap,fan C tap ok,by rw [cost]; omega,?_⟩
  intro x
  rw [lift_eval C tap valid x,ev,decomposition]
  cases h : small (proj x) with
  | true => simp
  | false =>
    rw [second (proj x) h]
    rfl
end PEqualNP.Outside.L_meta_9806.CoreTap
