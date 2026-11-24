import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Compose2567

def run (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w

theorem lengthRun (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run,Circuit.wires]
  | cons g rest ih =>
    change (run rest (w ++ [_])).length = _
    rw [ih]
    simp
    omega

theorem keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    change (run rest (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]

theorem join (m : ℕ) (P C : Circuit) (pmono : Monotone2 P) (cmono : Monotone2 C)
    (hp : P.output < m + P.size) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = P.size + C.size + 1 ∧
      ∀ w : List Bool, w.length = m → D.eval w = (P.eval w || C.eval (P.wires w)) := by
  let g : Gate := ⟨.or,[P.output,C.output]⟩
  let D : Circuit := ⟨P.gates ++ C.gates ++ [g],m + P.size + C.size⟩
  have mono : Monotone2 D := by
    intro a ha
    change a ∈ P.gates ++ C.gates ++ [g] at ha
    simp only [List.mem_append,List.mem_singleton] at ha
    rcases ha with (h | h) | h
    · exact pmono a h
    · exact cmono a h
    · subst a
      simp [g]
  refine ⟨D,mono,by simp [D,Circuit.size,Nat.add_assoc],?_⟩
  intro w hw
  let u := P.wires w
  let v := C.wires u
  have hu : u.length = m + P.size := by simpa only [u,run,Circuit.size,Circuit.wires,hw] using lengthRun P.gates w
  have hv : v.length = m + P.size + C.size := (lengthRun C.gates u).trans (by rw [hu]; rfl)
  have hkeep : v.getD P.output false = u.getD P.output false := keep C.gates u _ (by rw [hu]; exact hp)
  change (((P.gates ++ C.gates ++ [g]).foldl _ w).getD (m + P.size + C.size) false) = _
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))]).getD (m + P.size + C.size) false = _
  rw [← hv,List.getD_append_right _ _ _ _ (by omega)]
  change ([g.op.eval (g.inputs.map (fun i => v.getD i false))]).getD (v.length - v.length) false = (u.getD P.output false || v.getD C.output false)
  rw [Nat.sub_self]
  change GateOp.or.eval [v.getD P.output false,v.getD C.output false] = _
  rw [hkeep]
  simp [GateOp.eval]

end Compose2567
