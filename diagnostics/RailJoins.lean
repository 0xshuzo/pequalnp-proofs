import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.Rail
open PEqualNP.CircuitLowerBounds

inductive Pat where
  | lo | left | right | meet | join | hi
  deriving DecidableEq

def bits : Pat → Nat
  | .lo => 0 | .left => 12 | .right => 10 | .meet => 8 | .join => 14 | .hi => 15

def decode : Nat → Pat
  | 0 => .lo | 12 => .left | 10 => .right | 8 => .meet | 14 => .join | _ => .hi

def mix (d : Bool) (u v : Pat) : Pat :=
  decode (if d then bits u ||| bits v else bits u &&& bits v)

def aim (d : Bool) : Pat := if d then .join else .meet
def op (d : Bool) : GateOp := if d then .or else .and
def paired (u v : Pat) : Prop :=
  (u = .left ∧ v = .right) ∨ (u = .right ∧ v = .left)

theorem creates (d e : Bool) (u v : Pat) :
    u ≠ aim d → v ≠ aim d → mix e u v = aim d → e = d ∧ paired u v := by
  cases d <;> cases e <;> cases u <;> cases v <;> decide

theorem traces (d leftRail : Bool) (u v : Pat) :
    let tag : Pat := if leftRail then .left else .right
    mix d u v = tag → u = tag ∨ v = tag := by
  cases d <;> cases leftRail <;> cases u <;> cases v <;> decide

def val : Pat → Bool → Bool → Bool
  | .lo, _, _ => false | .hi, _, _ => true | .left, a, _ => a | .right, _, b => b
  | .meet, a,b => a && b | .join, a,b => a || b

theorem mixVal (d : Bool) (u v : Pat) (a b : Bool) :
    val (mix d u v) a b = (if d then val u a b || val v a b else val u a b && val v a b) := by
  cases d <;> cases u <;> cases v <;> cases a <;> cases b <;> decide

def wire (w : List Pat) (j : Nat) := w.getD j .lo

def gate (w : List Pat) (g : Gate) : Pat :=
  match g.inputs with
  | [] => if g.op = .and then .hi else .lo
  | [i] => wire w i
  | i::j::_ => mix (decide (g.op = .or)) (wire w i) (wire w j)

def push (w : List Pat) (g : Gate) := w ++ [gate w g]
def run (gs : List Gate) (w : List Pat) := gs.foldl push w

def joined (d : Bool) (w : List Pat) (g : Gate) : Prop :=
  g.op = op d ∧ ∃ i j, g.inputs = [i,j] ∧ paired (wire w i) (wire w j)

def occurs (d : Bool) : List Gate → List Pat → Prop
  | [], _ => False
  | g::gs, w => joined d w g ∨ occurs d gs (push w g)

def good (g : Gate) : Prop := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2

theorem fromList {A : Type} (w : List A) (i : Nat) (a : A) :
    w.getD i a=a ∨ w.getD i a∈w := by
  induction w generalizing i with
  | nil => simp [List.getD_eq_getElem?_getD]
  | cons x w ih =>
    cases i with
    | zero => simp [List.getD_eq_getElem?_getD]
    | succ i =>
      rcases ih i with h | h
      · exact Or.inl (by simpa [List.getD_eq_getElem?_getD] using h)
      · exact Or.inr (List.mem_cons_of_mem _ (by simpa [List.getD_eq_getElem?_getD] using h))

theorem clean {d : Bool} {w : List Pat} (abs : aim d ∉ w) (j : Nat) : wire w j ≠ aim d := by
  intro eqn
  rcases fromList w j Pat.lo with h | h
  · have e : Pat.lo = aim d := h.symm.trans eqn
    cases d <;> cases e
  · change wire w j ∈ w at h
    exact abs (eqn ▸ h)

theorem newGate {d : Bool} {w : List Pat} {g : Gate} (well : good g)
    (abs : aim d ∉ w) (eqn : gate w g = aim d) : joined d w g := by
  rcases g with ⟨tag,args⟩
  rcases well with ⟨tagOk,arity⟩
  change tag=.and ∨ tag=.or at tagOk
  change args.length ≤ 2 at arity
  cases args with
  | nil =>
    rcases tagOk with rfl | rfl <;> cases d <;> cases eqn
  | cons i rem =>
    cases rem with
    | nil => exact False.elim (clean abs i eqn)
    | cons j rem =>
      cases rem with
      | cons k rest => simp at arity
      | nil =>
        rcases tagOk with rfl | rfl
        · have h := creates d false (wire w i) (wire w j) (clean abs i) (clean abs j) eqn
          obtain ⟨rfl,pp⟩ := h
          exact ⟨rfl,i,j,rfl,pp⟩
        · have h := creates d true (wire w i) (wire w j) (clean abs i) (clean abs j) eqn
          obtain ⟨rfl,pp⟩ := h
          exact ⟨rfl,i,j,rfl,pp⟩

theorem discover {d : Bool} (w : List Pat) (gs : List Gate)
    (valid : ∀ g∈gs,good g) (abs : aim d ∉ w) (found : aim d ∈ run gs w) : occurs d gs w := by
  induction gs generalizing w with
  | nil => exact False.elim (abs found)
  | cons g gs ih =>
    by_cases fresh : gate w g=aim d
    · exact Or.inl (newGate (valid _ (by simp)) abs fresh)
    · apply Or.inr
      apply ih (push w g) (fun t h => valid t (by simp [h])) _ found
      intro m
      rcases List.mem_append.mp m with h | h
      · exact abs h
      · have z : aim d = gate w g := by simpa using h
        exact fresh z.symm

theorem findsOutput {d : Bool} (w : List Pat) (gs : List Gate) (out : Nat)
    (valid : ∀ g∈gs,good g) (abs : aim d ∉ w) (found : wire (run gs w) out=aim d) :
    occurs d gs w := by
  apply discover w gs valid abs
  by_contra h
  exact clean h out found

end PEqualNP.Outside.L_meta_9809.Rail
