import Mathlib
import PEqualNP.Defs
namespace Rename1479
open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

def rew (n : Nat) (p : Fin n → Fin n) (w : Nat) : Nat :=
  if h : w<n then (p ⟨w,h⟩).val else w
def mg (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
def mc (n : Nat) (p : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mg (rew n p)),rew n p C.output⟩
def run (alg : GateOp → List α → α) (d : α) (gs : List Gate) (xs : List α) :=
  gs.foldl (fun w g => w++[alg g.op (g.inputs.map fun i => w.getD i d)]) xs

theorem congr_run (alg : GateOp → List α → α) (d : α) (n : Nat) (p : Fin n → Fin n)
    (gs : List Gate) (x y : List α) (len : x.length=y.length) (lo : n≤x.length)
    (agree : ∀ w, y.getD (rew n p w) d=x.getD w d) :
    ∀ w, (run alg d (gs.map (mg (rew n p))) y).getD (rew n p w) d =
      (run alg d gs x).getD w d := by
  induction gs generalizing x y with
  | nil => exact agree
  | cons g gs ih =>
    let b := alg g.op (g.inputs.map fun i => x.getD i d)
    have same : alg (mg (rew n p) g).op ((mg (rew n p) g).inputs.map
        (fun i => y.getD i d)) = b := by
      simp only [mg,List.map_map,Function.comp_def,agree,b]
    change ∀ w, (run alg d (gs.map (mg (rew n p))) (y++[_])).getD (rew n p w) d =
      (run alg d gs (x++[b])).getD w d
    rw [same]
    apply ih _ _ (by simp [len]) (by simp; omega)
    intro i
    by_cases hi : i<x.length
    · have sm : rew n p i<y.length := by
        unfold rew
        split
        next h => have := (p ⟨i,h⟩).isLt; omega
        next => omega
      rw [List.getD_append _ _ _ _ sm,List.getD_append _ _ _ _ hi]
      exact agree i
    · have at_or_after : n≤i := by omega
      rw [show rew n p i=i by simp [rew,Nat.not_lt.mpr at_or_after],
        List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]

theorem input_perm (p : Fin n → Fin n) (x : Fin n → α) (d : α) (w : Nat) :
    (List.ofFn x).getD (rew n p w) d = (List.ofFn (x ∘ p)).getD w d := by
  by_cases h : w<n
  · have hw : rew n p w<n := by simpa [rew,h] using (p ⟨w,h⟩).isLt
    rw [List.getD_eq_getElem _ _ (by simpa using hw),
        List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_ofFn,Function.comp_apply]
    congr 1
    apply Fin.ext
    simp [rew,h]
  · simp [rew,h,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)]

theorem eval_perm (n : Nat) (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (mc n p C).eval (List.ofFn x)=C.eval (List.ofFn (x ∘ p)) :=
  congr_run GateOp.eval false n p C.gates _ _ (by simp) (by simp)
    (input_perm p x false) C.output

def cost (op : GateOp) (ins : List (Option Nat)) :=
  match op with
  | GateOp.or => ins.foldl (fun acc o => match acc,o with
    | none,o => o
    | some a,none => some a
    | some a,some b => some (min a b)) none
  | GateOp.and => ins.foldl (fun acc o => match acc,o with
    | some a,some b => some (a+b)
    | _,_ => none) (some 0)
  | _ => none
def seed (n : Nat) (S : List Nat) (v : Nat) : List (Option Nat) :=
  (List.range n).map (fun i => if i=v then some 1 else if i∈S then some 0 else none)

theorem cost_perm (n : Nat) (p : Fin n → Fin n) (C : Circuit)
    (S T : List Nat) (u v : Nat)
    (h : ∀ w, (seed n T v).getD (rew n p w) none=(seed n S u).getD w none) :
    ((scalarMults (mc n p C) n T v).getD (mc n p C).output none)=
    ((scalarMults C n S u).getD C.output none) :=
  congr_run cost none n p C.gates (seed n S u) (seed n T v) (by simp [seed])
    (by simp [seed]) h C.output

theorem swap_first (alg : GateOp → List α → α) (d : α) (op : GateOp)
    (comm : ∀ a b : α, alg op [a,b]=alg op [b,a]) (a b : Nat)
    (tail : List Gate) (xs : List α) :
    run alg d (⟨op,[a,b]⟩::tail) xs=run alg d (⟨op,[b,a]⟩::tail) xs := by
  change run alg d tail (xs++[alg op [xs.getD a d,xs.getD b d]]) =
    run alg d tail (xs++[alg op [xs.getD b d,xs.getD a d]])
  rw [comm]

theorem commute_value (op : GateOp) (ao : op=.and ∨ op=.or) (a b : Bool) :
    op.eval [a,b]=op.eval [b,a] := by
  rcases ao with rfl|rfl <;> cases a <;> cases b <;> rfl
theorem commute_cost (op : GateOp) (ao : op=.and ∨ op=.or) (a b : Option Nat) :
    cost op [a,b]=cost op [b,a] := by
  rcases ao with rfl|rfl <;> cases a <;> cases b <;> simp [cost,Nat.add_comm, min_comm]
end Rename1479
