import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18836

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Op := Bool × ℕ × ℕ

def gate (t : Op) : Gate := ⟨if t.1 then .and else .or, [t.2.1, t.2.2]⟩

-- After the 124 inputs come both mixed copies of the 31 vertex labels.
-- Each star uses the six translates of the difference set.
def star (u : ℕ) : List Op :=
  let w := 186 + 6 * u
  let line := fun k : ℕ => 155 + (u + k) % 31
  [(false, line 0, line 1), (false, w, line 3), (false, w+1, line 8),
   (false, w+2, line 12), (false, w+3, line 18), (true, 124+u, w+4)]

def ops : List Op :=
  ((List.range 31).map fun i => (false, i, 93+i)) ++
  ((List.range 31).map fun i => (false, 62+i, 31+i)) ++
  ((List.range 31).flatMap star) ++
  [(false, 191, 197)] ++
  ((List.range 29).map fun i => (false, 372+i, 203+6*i))

def circuit : Circuit := ⟨ops.map gate, 401⟩

-- Read one bit of a simultaneous evaluation of all promise inputs.
def numStep (w : List ℕ) (t : Op) : List ℕ :=
  let a := w.getD t.2.1 0
  let b := w.getD t.2.2 0
  w ++ [if t.1 then a &&& b else a ||| b]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def sample (w : List ℕ) (k : ℕ) := w.map (fun a => a.testBit k)

theorem getSample (w : List ℕ) (i k : ℕ) :
    (sample w k).getD i false = (w.getD i 0).testBit k := by
  induction w generalizing i with
  | nil => simp [sample]
  | cons h t ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem step (w : List ℕ) (k : ℕ) (t : Op) :
    boolStep (sample w k) (gate t) = sample (numStep w t) k := by
  have readBit (o : Option ℕ) :
      (o.map (fun a => a.testBit k)).getD false = (o.getD 0).testBit k := by
    cases o <;> simp
  rcases t with ⟨b,a,c⟩
  cases b <;> simp [boolStep,gate,numStep,GateOp.eval,sample,List.map_append,
    Nat.testBit_or,Nat.testBit_and,readBit]

theorem run (ts : List Op) (w : List ℕ) (k : ℕ) :
    (ts.map gate).foldl boolStep (sample w k) = sample (ts.foldl numStep w) k := by
  induction ts generalizing w with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons,List.foldl_cons,step,ih]

-- Position 62*u+v records the promised pair (u,v).
def stride : ℕ := (List.range 62).foldl (fun m u => m ||| (1 <<< (62*u))) 0

def leftMask (i : Fin 62) : ℕ := (2^62-1) <<< (62*i.val)
def rightMask (i : Fin 62) : ℕ := stride <<< i.val
def seed : List ℕ := List.ofFn leftMask ++ List.ofFn rightMask
-- A row of the first block translates the difference set forwards.
-- A row of the transpose translates it backwards inside the second block.
def rowMask (u : ℕ) : ℕ :=
  ([0, 1, 3, 8, 12, 18] : List ℕ).foldl (fun m d =>
    let v := if u < 31 then (u+d)%31 else 31+(u-d)%31
    m ||| (1 <<< v)) 0

def resultMask : ℕ :=
  (List.range 62).foldl (fun m u => m ||| (rowMask u <<< (62*u))) 0

def posted : Fin 62 → Fin 62 → Bool :=
  fun u v : Fin 62 => decide ((u.val < 31 ∧ v.val < 31 ∧ (v.val + 31 - u.val) % 31 ∈ [0, 1, 3, 8, 12, 18]) ∨ (31 ≤ u.val ∧ 31 ≤ v.val ∧ (u.val + 31 - v.val) % 31 ∈ [0, 1, 3, 8, 12, 18]))

set_option maxRecDepth 100000 in
theorem strideGrid : ∀ u v : Fin 62,
    stride.testBit (62*u.val+v.val) = decide (v.val=0) := by decide +kernel

theorem strideBits (t : Fin 3844) : stride.testBit t.val = decide (t.val % 62 = 0) := by
  have ht := t.isLt
  let u : Fin 62 := ⟨t.val / 62, by omega⟩
  let v : Fin 62 := ⟨t.val % 62, by omega⟩
  have index : 62*u.val+v.val = t.val := by dsimp [u,v]; omega
  have h := strideGrid u v
  rw [index] at h
  exact h

theorem leftBits (i u v : Fin 62) :
    (leftMask i).testBit (62*u.val+v.val) = decide (i=u) := by
  have hv := v.isLt
  by_cases h : 62*i.val ≤ 62*u.val+v.val
  · have e : 62*u.val+v.val-62*i.val < 62 ↔ i=u := by
      rw [Fin.ext_iff]
      omega
    rw [leftMask,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one]
    simp [h,e]
  · have e : i ≠ u := by rintro rfl; omega
    simp [leftMask,Nat.testBit_shiftLeft,h,e]

theorem rightBits (i u v : Fin 62) :
    (rightMask i).testBit (62*u.val+v.val) = decide (i=v) := by
  have hi := i.isLt
  have hu := u.isLt
  have hv := v.isLt
  by_cases h : i.val ≤ 62*u.val+v.val
  · have bound : 62*u.val+v.val-i.val < 3844 := by omega
    have bit := strideBits ⟨62*u.val+v.val-i.val,bound⟩
    change stride.testBit (62*u.val+v.val-i.val) =
      decide ((62*u.val+v.val-i.val) % 62 = 0) at bit
    have e : (62*u.val+v.val-i.val) % 62 = 0 ↔ i=v := by
      rw [Fin.ext_iff]
      omega
    simp [rightMask,Nat.testBit_shiftLeft,h,bit,e]
  · have e : i ≠ v := by rintro rfl; omega
    simp [rightMask,Nat.testBit_shiftLeft,h,e]

theorem starts (u v : Fin 62) : sample seed (62*u.val+v.val) = oneEach u v := by
  simp only [sample,seed,oneEach,List.map_append,List.map_ofFn,Function.comp_def,
    leftBits,rightBits]

set_option maxRecDepth 100000 in
theorem finishes : (ops.foldl numStep seed).getD 401 0 = resultMask := by decide +kernel

set_option maxRecDepth 100000 in
theorem matchesTable : ∀ u v : Fin 62, resultMask.testBit (62*u.val+v.val) = posted u v := by
  decide +kernel

theorem upper : RepSizeAtMost posted 278 := by
  refine ⟨circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    change g ∈ ops.map gate at hg
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hg
    rcases t with ⟨b,a,c⟩
    cases b <;> simp [gate]
  · intro u v
    rw [← starts u v]
    change ((ops.map gate).foldl boolStep (sample seed (62*u.val+v.val))).getD 401 false =
      posted u v
    rw [run,getSample,finishes,matchesTable]

end PEqualNP.Outside.L_meta_18836

theorem PEqualNP.Outside.L_meta_18836 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 62 => decide ((u.val < 31 ∧ v.val < 31 ∧ (v.val + 31 - u.val) % 31 ∈ [0, 1, 3, 8, 12, 18]) ∨ (31 ≤ u.val ∧ 31 ≤ v.val ∧ (u.val + 31 - v.val) % 31 ∈ [0, 1, 3, 8, 12, 18]))) 278 := by
  exact PEqualNP.Outside.L_meta_18836.upper
