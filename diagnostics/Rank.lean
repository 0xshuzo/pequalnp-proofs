import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_4127

namespace Rank1479
open PEqualNP.CircuitLowerBounds PEqualNP.ReadK
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

def rank : Option Nat → Nat
  | none => 2
  | some a => min 2 a

def degree (a : Bool × Bool) : Nat := if a.1 then 0 else if a.2 then 1 else 2

def addOpt (a b : Option Nat) : Option Nat :=
  match a,b with
  | some x,some y => some (x+y)
  | _,_ => none

def minOpt (a b : Option Nat) : Option Nat :=
  match a,b with
  | none,b => b
  | some a,none => some a
  | some a,some b => some (min a b)

def land (a b : Bool × Bool) := (a.1 && b.1, (a.1 && b.2) || (a.2 && b.1))
def lor (a b : Bool × Bool) := (a.1 || b.1, a.2 || b.2)

theorem ra (a b : Option Nat) : rank (addOpt a b)=min 2 (rank a + rank b) := by
  cases a <;> cases b <;> simp [rank,addOpt] <;> omega

theorem ro (a b : Option Nat) : rank (minOpt a b)=min (rank a) (rank b) := by
  cases a <;> cases b <;> simp [rank,minOpt] <;> omega

theorem da (a b : Bool × Bool) : degree (land a b)=min 2 (degree a + degree b) := by
  obtain ⟨x,y⟩ := a
  obtain ⟨z,w⟩ := b
  cases x <;> cases y <;> cases z <;> cases w <;> rfl

theorem dor (a b : Bool × Bool) : degree (lor a b)=min (degree a) (degree b) := by
  obtain ⟨x,y⟩ := a
  obtain ⟨z,w⟩ := b
  cases x <;> cases y <;> cases z <;> cases w <;> rfl

def st (R : List (Option Nat)) (g : Gate) : List (Option Nat) :=
  let ins := g.inputs.map fun i => R.getD i none
  R ++ [match g.op with
    | GateOp.or => ins.foldl minOpt none
    | GateOp.and => ins.foldl addOpt (some 0)
    | _ => none]

def lt (R : List (Bool × Bool)) (g : Gate) : List (Bool × Bool) :=
  let ins := g.inputs.map fun i => R.getD i (false,false)
  R ++ [match g.op with
    | GateOp.or => (ins.any (·.1),ins.any (·.2))
    | GateOp.and => ins.foldl land (true,false)
    | _ => (false,false)]

theorem mapget {α β : Type*} (f : α → β) (xs : List α) (i : Nat) (d : α) :
    (xs.map f).getD i (f d)=f (xs.getD i d) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases xs[i]? <;> rfl

theorem same_get (A : List (Option Nat)) (B : List (Bool × Bool))
    (h : A.map rank=B.map degree) (i : Nat) :
    rank (A.getD i none)=degree (B.getD i (false,false)) := by
  rw [← mapget,← mapget]
  exact congrArg (fun l : List Nat => l.getD i 2) h

theorem scan_agrees (gs : List Gate)
    (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ, g.inputs=[a,b]) :
    ∀ (A : List (Option Nat)) (B : List (Bool × Bool)), A.map rank=B.map degree →
      (gs.foldl st A).map rank=(gs.foldl lt B).map degree := by
  induction gs with
  | nil => intro A B h; exact h
  | cons g gs ih =>
    intro A B h
    apply ih (fun k hk => legal k (List.mem_cons_of_mem _ hk))
    obtain ⟨op,a,b,inputs⟩ := legal g List.mem_cons_self
    have aa := same_get A B h a
    have bb := same_get A B h b
    have and_s (x y : Option Nat) : addOpt (addOpt (some 0) x) y=addOpt x y := by
      cases x <;> cases y <;> simp [addOpt]
    have and_l (x y : Bool × Bool) : land (land (true,false) x) y=land x y := by
      simp [land]
    rcases op with hop|hop
    · simp only [st,lt,inputs,hop,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,
        and_s,and_l,List.map_append,h,ra,da,aa,bb]
    · simp only [st,lt,inputs,hop,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,
        show ∀ x, minOpt none x=x from fun _ => rfl,List.any_cons,List.any_nil,Bool.or_false,
        List.map_append,h]
      change _ ++ [rank (minOpt _ _)] = _ ++ [degree (lor _ _)]
      rw [ro,dor,aa,bb]

theorem no_linear (C : Circuit)
    (shape : ∀ (j : ℕ) (g : Gate), C.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
       ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j)
    (s : Bool) (large : ∃ k : ℕ, 2≤k ∧
      ((scalarMults C 14 [0,7] (if s then 7 else 0)).getD C.output none)=some k) :
    ((linearParts C (fun i => decide (i=if s then 7 else 0))
      (List.ofFn fun i : Fin 14 => decide (i.val=0 ∨ i.val=7))).getD C.output (false,false)).2=false := by
  let m : Nat := if s then 7 else 0
  let A : List (Option Nat) := (List.range 14).map
    (fun i => if i=m then some 1 else if i∈([0,7] : List Nat) then some 0 else none)
  let B : List (Bool × Bool) := ((List.ofFn fun i : Fin 14 => decide (i.val=0 ∨ i.val=7)).zipIdx).map
    (fun z => if decide (z.2=m) then (false,z.1) else (z.1,false))
  have base : A.map rank = B.map degree := by dsimp only [A,B,m]; cases s <;> decide +kernel
  have legal : ∀ g∈C.gates, (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ, g.inputs=[a,b] := by
    intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨op,a,b,inputs,_⟩ := shape j g hj
    exact ⟨op,a,b,inputs⟩
  obtain ⟨k,hk,hout⟩ := large
  have eq := same_get _ _ (scan_agrees C.gates legal A B base) C.output
  change (C.gates.foldl st A).getD C.output none=some k at hout
  rw [hout] at eq
  have two : rank (some k) = 2 := Nat.min_eq_left hk
  rw [two] at eq
  change ((C.gates.foldl lt B).getD C.output (false,false)).2=false
  cases h : (C.gates.foldl lt B).getD C.output (false,false) with
  | mk a b =>
    rw [h] at eq
    cases a <;> cases b <;> simp_all [degree]

theorem convertRank : ∀ C : Circuit, (∀ (j : ℕ) (g : Gate), C.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
       ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) → ∀ s : Bool, (∃ k : ℕ, 2≤k ∧ ((PEqualNP.ReadK.scalarMults C 14 [0,7] (if s then 7 else 0)).getD C.output none)=some k) → ∃ d : ℕ → Bool, (∀ i : Fin 7, d i.val = (if s then false else decide (i = 0)) ∧ d (7+i.val) = (if s then decide (i = 0) else false)) ∧ (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] → let w := C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then Fin.castAdd 7 (0 : Fin 7) else Fin.natAdd 7 (0 : Fin 7))); (g.op = GateOp.and → d (14+j) = ((w.getD a false && d b) || (d a && w.getD b false))) ∧ (g.op = GateOp.or → d (14+j) = (d a || d b))) ∧ d C.output = false := by
  intro C shaped s rank
  apply PEqualNP.Outside.L_meta_4127 C shaped s
  exact no_linear C shaped s rank

end Rank1479
