import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_3720
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace Minimum3722

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK
open PEqualNP.MetaComplexity.Helpers.PermInputs

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
local instance : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

def edges : List (ℕ×ℕ) := [(0,3),(0,4),(0,5),(1,4),(2,3)]
abbrev G := edgeGraph 6 edges
abbrev f := graphFun G ∅
def I (p l : Fin 3) := (p.val,3+l.val)∈edges
instance : DecidableRel I := fun p l => by unfold I; infer_instance
def bad : Circuit :=
  ⟨[⟨.and,[1,4]⟩,⟨.or,[4,5]⟩,⟨.or,[0,6]⟩,⟨.or,[2,8]⟩,⟨.and,[7,8]⟩,⟨.or,[3,10]⟩,⟨.and,[9,11]⟩],12⟩
def good : Circuit :=
  ⟨[⟨.or,[3,4]⟩,⟨.or,[6,5]⟩,⟨.and,[0,7]⟩,⟨.and,[1,4]⟩,⟨.and,[2,3]⟩,⟨.or,[8,9]⟩,⟨.or,[11,10]⟩],12⟩
def lines (w : ℕ) := decide (3≤w)

theorem incidence : (∀ u v : Fin (3+3), G.Adj u v ↔ ∃ p l : Fin 3,I p l ∧
    ((u=Fin.castAdd 3 p ∧ v=Fin.natAdd 3 l) ∨ (u=Fin.natAdd 3 l ∧ v=Fin.castAdd 3 p))) ∧ NoFourCycle G ∧
    ((List.finRange 3).flatMap fun p => ((List.finRange 3).filter fun l => decide (I p l)).map fun l => (p.val,3+l.val))=edges := by decide +kernel

def once (b : Bool) (x : Fin 6 → Bool) := f (Function.update x 1 b)
def twice (b c : Bool) (x : Fin 6 → Bool) := once b (Function.update x 2 c)
def active : Finset (Fin 6) := {0,3,4,5}
theorem dependence : ∀ b c : Bool,∀ i∈active, ∃ x : Fin 6 → Bool,
    twice b c (Function.update x i (!x i)) ≠ twice b c x := by decide +kernel

theorem lower (s : ℕ) (sc : HasCircuitSize 6 f s) : 7≤s := by
  have dep1 : ∃ x : Fin 6 → Bool,f (Function.update x 1 (!x 1))≠f x := by decide +kernel
  have nc1 : ∀ b : Bool,∃ x y : Fin 6 → Bool,once b x≠once b y := by decide +kernel
  obtain ⟨b,t,save1,c1⟩ := gate_elim_at 5 f 1 s dep1 nc1 sc
  have dep2 : ∀ a : Bool,∃ x : Fin 6 → Bool,once a (Function.update x 2 (!x 2))≠once a x := by decide +kernel
  have nc2 : ∀ a v : Bool,∃ x y : Fin 6 → Bool, twice a v x≠ twice a v y := by decide +kernel
  obtain ⟨v,u,save2,c2⟩ := gate_elim_at 5 (once b) 2 t (dep2 b) (nc2 b) c1
  have bound := dep_lower_set 6 (twice b v) active (dependence b v) u c2
  have four : active.card=4 := by decide +kernel
  omega

theorem least (D : Circuit) (ao : IsAO2 6 D) (corr : ∀ x : Fin 6 → Bool,circuitFun 6 D x=f x)
    (sz : D.size=7) : IsLeastAO G D := by
  refine ⟨ao,funext corr,?_⟩
  intro C aC eq
  rw [sz]
  apply lower
  refine ⟨C,?_,le_rfl,fun x => congrFun eq x⟩
  intro g hg
  refine ⟨?_,(aC.2.2 g hg).le⟩
  rcases aC.1 g hg with h|h <;> simp [h]

def clean (D : Circuit) := ∀ k : Fin D.gates.length, (gateAt D k).op=.and → ∀ t∈(gateAt D k).inputs,
    ¬(∀ x : Fin 6 → Bool, (Circuit.mk D.gates t).eval (List.ofFn x)=true → f x=true)
instance (D : Circuit) : Decidable (clean D) := by unfold clean; infer_instance
theorem badLeast : IsLeastAO G bad := least bad (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem goodLeast : IsLeastAO G good := least good (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem badFacts : PEqualNP.FactorSubst.liveSize 6 bad=bad.size ∧ clean bad ∧
    doubleReread bad 6 lines edges=[(1,4)] ∧ LiftAt G bad 2 1 ∧ LiftAt G bad 5 1 := by decide +kernel
theorem goodFacts : PEqualNP.FactorSubst.liveSize 6 good=good.size ∧ clean good ∧
    IsLiftFixedPoint G good ∧ doubleReread good 6 lines edges=[] := by decide +kernel

end Minimum3722

namespace Lift3722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK Minimum3722
local instance : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

def perform (D : Circuit) (h : ℕ) (b : Fin 2) : Circuit :=
  let w := opnd D h b
  let r := opnd D h (1-b)
  let del := PEqualNP.Outside.L_meta_3720.del 6 h r D.gates
  ⟨del++[⟨.or,[PEqualNP.Outside.L_meta_3720.sg 6 h r D.output,w]⟩],6+del.length⟩
def state1 := perform bad 2 1
def state2 := perform bad 5 1
def state3 := perform state1 4 1
def state4 := perform state2 2 1
def states : Fin 5 → Circuit := ![bad,state1,state2,state3,state4]
def sites : Fin 5 → List (ℕ×Fin 2) := ![[(2,1),(5,1)],[(4,1)],[(2,1)],[],[]]

theorem allSites : ∀ i : Fin 5, ∀ k : Fin (states i).gates.length,∀ b : Fin 2,
    LiftAt G (states i) k.val b ↔ (k.val,b)∈sites i := by
  intro i
  fin_cases i <;> decide +kernel
theorem classify : ∀ i : Fin 5,(IsLiftFixedPoint G (states i) ↔ i=3 ∨ i=4) ∧
    doubleReread (states i) 6 lines edges = (if i=0 then [(1,4)] else []) := by
  intro i
  fin_cases i <;> decide +kernel
theorem allNormal (i : Fin 5) : IsLeastAO G (states i) ∧ clean (states i) ∧
    PEqualNP.FactorSubst.liveSize 6 (states i)=(states i).size ∧ (states i).size=7 := by
  have all : ∀ j : Fin 5, IsAO2 6 (states j) ∧ (∀ x : Fin 6 → Bool,circuitFun 6 (states j) x=f x) ∧
      clean (states j) ∧ PEqualNP.FactorSubst.liveSize 6 (states j)=(states j).size ∧ (states j).size=7 := by
    intro j
    fin_cases j <;> decide +kernel
  obtain ⟨ao,corr,clean,live,sz⟩ := all i
  exact ⟨least _ ao corr sz,clean,live,sz⟩

end Lift3722
