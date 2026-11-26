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
  rcases t with ⟨b,a,c⟩
  cases b <;> simp [boolStep,gate,numStep,GateOp.eval,sample,List.map_append,
    show ∀ i,(w.map (fun v => v.testBit k)).getD i false=(w.getD i 0).testBit k from
      fun i => getSample w i k, Nat.testBit_or,Nat.testBit_and]

theorem run (ts : List Op) (w : List ℕ) (k : ℕ) :
    (ts.map gate).foldl boolStep (sample w k) = sample (ts.foldl numStep w) k := by
  induction ts generalizing w with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons,List.foldl_cons,step,ih]

def stride : ℕ := 0x4000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001000000000000000400000000000000100000000000000040000000000000010000000000000004000000000000001
def leftMask (i : Fin 62) : ℕ := (2^62-1) <<< (62*i.val)
def rightMask (i : Fin 62) : ℕ := stride <<< i.val
def seed : List ℕ := List.ofFn leftMask ++ List.ofFn rightMask
def resultMask : ℕ := 0xd088200000000001a1104000000000034220800000000006844100000000000d088200000000001a1104000000000034220800000000006844100000000000d088200000000001a1104000000000034220800000000006844100000000000d088200000002001a1100000000040034220000000008006844000000001000d088000000002001a1100000000040034220000000208006840000000041000d080000000082001a1000000001040034200000002208006800000000441000d000000000882001a0000000011040034000000002208006800000008441000c00000001088200180000000a1104002000000000000000400208850000000180041108000000030008221000000016001044000000002c002088000000005800411000000000b0008220000000016001044000000042c002080000000085800410000000010b0008200000000216001040000000442c002000000000885800400000000110b0008000000002216001000000000442c002000000000885800400000004110b0000000000082216000000000010442c000000000020885800000000004110b0000000000082216000000000010442c000000000020885800000000004110b0000000000082216000000000010442c000000000020885800000000004110b

def posted : Fin 62 → Fin 62 → Bool :=
  fun u v : Fin 62 => decide ((u.val < 31 ∧ v.val < 31 ∧ (v.val + 31 - u.val) % 31 ∈ [0, 1, 3, 8, 12, 18]) ∨ (31 ≤ u.val ∧ 31 ≤ v.val ∧ (u.val + 31 - v.val) % 31 ∈ [0, 1, 3, 8, 12, 18]))

set_option maxRecDepth 100000 in
theorem strideBits : ∀ t : Fin 3844, stride.testBit t.val = decide (t.val % 62 = 0) := by
  decide +kernel

theorem leftBits (i u v : Fin 62) :
    (leftMask i).testBit (62*u.val+v.val) = decide (i=u) := by
  have hv := v.isLt
  by_cases h : 62*i.val ≤ 62*u.val+v.val
  · have e : 62*u.val+v.val-62*i.val < 62 ↔ i=u := by
      rw [Fin.ext_iff]
      omega
    simp [leftMask,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,h,
      Nat.not_lt.mpr h,e]
  · have e : i ≠ u := by rintro rfl; omega
    simp [leftMask,Nat.testBit_shiftLeft,h,Nat.lt_of_not_ge h,e]

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
    simp [rightMask,Nat.testBit_shiftLeft,h,Nat.not_lt.mpr h,bit,e]
  · have e : i ≠ v := by rintro rfl; omega
    simp [rightMask,Nat.testBit_shiftLeft,h,Nat.lt_of_not_ge h,e]

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
