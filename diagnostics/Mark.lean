import Mathlib
import PEqualNP.Defs

namespace EdgeBank4081

abbrev E := Sym2 (Fin 11)
abbrev Label := Finset (Fin 11) × Finset E
def allowed : List Label := [
  ({0},∅),
  ({1},∅),
  ({2},∅),
  ({3},∅),
  ({4},∅),
  ({5},∅),
  ({6},∅),
  ({7},∅),
  ({8},∅),
  ({9},∅),
  ({10},∅),
  ({9,10},{s((0 : Fin 11),(9 : Fin 11)),s((0 : Fin 11),(10 : Fin 11))}),
  ({4,8},{s((1 : Fin 11),(4 : Fin 11)),s((1 : Fin 11),(8 : Fin 11))}),
  ({5,10},{s((2 : Fin 11),(5 : Fin 11)),s((2 : Fin 11),(10 : Fin 11))}),
  ({6,7},{s((3 : Fin 11),(6 : Fin 11)),s((3 : Fin 11),(7 : Fin 11))}),
  ({1,8},{s((1 : Fin 11),(4 : Fin 11)),s((4 : Fin 11),(8 : Fin 11))}),
  ({1,10},{s((1 : Fin 11),(4 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({8,10},{s((4 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({1,8,10},{s((1 : Fin 11),(4 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({2,8},{s((2 : Fin 11),(5 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({2,9},{s((2 : Fin 11),(5 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({8,9},{s((5 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({2,8,9},{s((2 : Fin 11),(5 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({3,7},{s((3 : Fin 11),(6 : Fin 11)),s((6 : Fin 11),(7 : Fin 11))}),
  ({3,10},{s((3 : Fin 11),(6 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({7,10},{s((6 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({3,7,10},{s((3 : Fin 11),(6 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({3,6},{s((3 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(7 : Fin 11))}),
  ({3,9},{s((3 : Fin 11),(7 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({6,9},{s((6 : Fin 11),(7 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({3,6,9},{s((3 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({1,4},{s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(8 : Fin 11))}),
  ({1,5},{s((1 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({1,9},{s((1 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({4,5},{s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({4,9},{s((4 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({5,9},{s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({1,4,5},{s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({1,4,9},{s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({1,5,9},{s((1 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({4,5,9},{s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({1,4,5,9},{s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,5},{s((0 : Fin 11),(9 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({0,7},{s((0 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({0,8},{s((0 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({5,7},{s((5 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({5,8},{s((5 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({7,8},{s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,5,7},{s((0 : Fin 11),(9 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({0,5,8},{s((0 : Fin 11),(9 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,7,8},{s((0 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({5,7,8},{s((5 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,5,7,8},{s((0 : Fin 11),(9 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,2},{s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(10 : Fin 11))}),
  ({0,4},{s((0 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({0,6},{s((0 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({2,4},{s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({2,6},{s((2 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({4,6},{s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({0,2,4},{s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({0,2,6},{s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({0,4,6},{s((0 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({2,4,6},{s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({0,2,4,6},{s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))})]
def allEdges : Finset E := {s((0 : Fin 11),(9 : Fin 11)),s((0 : Fin 11),(10 : Fin 11)),s((1 : Fin 11),(4 : Fin 11)),s((1 : Fin 11),(8 : Fin 11)),s((2 : Fin 11),(5 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((3 : Fin 11),(6 : Fin 11)),s((3 : Fin 11),(7 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}

def hits (A : Finset (Fin 11)) (e : E) : Prop := ∃ v∈A, v∈e
instance (A : Finset (Fin 11)) (e : E) : Decidable (hits A e) := by unfold hits;infer_instance
end EdgeBank4081
namespace Triple4081
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership EdgeBank4081

def independent (Z : Finset (Fin 11)) := ∀ u∈Z, ∀ v∈Z, s(u,v)∉allEdges
instance (Z : Finset (Fin 11)) : Decidable (independent Z) := by unfold independent;infer_instance

def tests : List (Finset (Fin 11)) := [{0,1,2,3},{0,2,3,4},{0,1,3,5},{0,3,4,5},{0,1,2,6},{0,2,4,6},{0,1,5,6},{0,4,5,6},{0,1,2,7},{0,2,4,7},{0,1,5,7},{0,4,5,7},{0,2,3,8},{0,2,6,8},{0,2,7,8},{1,2,3,9},{2,3,4,9},{1,2,6,9},{2,4,6,9},{1,3,5,10},{1,5,7,10},{3,8,10},{7,8,10},{1,3,9,10}]
end Triple4081
namespace Pair5184
open EdgeBank4081 Triple4081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def distinguished : Finset E := {s(9,0),s(8,1),s(2,5),s(3,7),s(10,6)}
def pairs : Finset (Finset E) := {{s((0 : Fin 11),10),s((5 : Fin 11),8)},{s((1 : Fin 11),4),s((5 : Fin 11),9)},{s((2 : Fin 11),10),s((8 : Fin 11),9)},{s((4 : Fin 11),10),s((5 : Fin 11),9)}}
def z0 : Finset (Fin 11) := {7,8,10}
def cls0 : Finset (Finset E) := {{s((0 : Fin 11),9),s((1 : Fin 11),8)},{s((0 : Fin 11),9),s((3 : Fin 11),7)},{s((0 : Fin 11),9),s((5 : Fin 11),8)},{s((0 : Fin 11),10),s((1 : Fin 11),4)},{s((0 : Fin 11),10),s((1 : Fin 11),8)},{s((0 : Fin 11),10),s((2 : Fin 11),10)},{s((0 : Fin 11),10),s((3 : Fin 11),6)},{s((0 : Fin 11),10),s((3 : Fin 11),7)},{s((0 : Fin 11),10),s((4 : Fin 11),8)},{s((0 : Fin 11),10),s((4 : Fin 11),10)},{s((0 : Fin 11),10),s((5 : Fin 11),9)},{s((0 : Fin 11),10),s((6 : Fin 11),7)},{s((0 : Fin 11),10),s((6 : Fin 11),10)},{s((0 : Fin 11),10),s((7 : Fin 11),9)},{s((0 : Fin 11),10),s((8 : Fin 11),9)},{s((1 : Fin 11),4),s((2 : Fin 11),10)},{s((1 : Fin 11),4),s((3 : Fin 11),7)},{s((1 : Fin 11),4),s((5 : Fin 11),8)},{s((1 : Fin 11),4),s((6 : Fin 11),10)},{s((1 : Fin 11),4),s((8 : Fin 11),9)},{s((1 : Fin 11),8),s((2 : Fin 11),5)},{s((1 : Fin 11),8),s((2 : Fin 11),10)},{s((1 : Fin 11),8),s((3 : Fin 11),6)},{s((1 : Fin 11),8),s((3 : Fin 11),7)},{s((1 : Fin 11),8),s((4 : Fin 11),8)},{s((1 : Fin 11),8),s((4 : Fin 11),10)},{s((1 : Fin 11),8),s((5 : Fin 11),8)},{s((1 : Fin 11),8),s((5 : Fin 11),9)},{s((1 : Fin 11),8),s((6 : Fin 11),7)},{s((1 : Fin 11),8),s((6 : Fin 11),10)},{s((1 : Fin 11),8),s((7 : Fin 11),9)},{s((1 : Fin 11),8),s((8 : Fin 11),9)},{s((2 : Fin 11),5),s((3 : Fin 11),7)},{s((2 : Fin 11),5),s((6 : Fin 11),10)},{s((2 : Fin 11),5),s((8 : Fin 11),9)},{s((2 : Fin 11),10),s((3 : Fin 11),6)},{s((2 : Fin 11),10),s((3 : Fin 11),7)},{s((2 : Fin 11),10),s((4 : Fin 11),8)},{s((2 : Fin 11),10),s((4 : Fin 11),10)},{s((2 : Fin 11),10),s((5 : Fin 11),8)},{s((2 : Fin 11),10),s((5 : Fin 11),9)},{s((2 : Fin 11),10),s((6 : Fin 11),7)},{s((2 : Fin 11),10),s((6 : Fin 11),10)},{s((3 : Fin 11),6),s((4 : Fin 11),10)},{s((3 : Fin 11),6),s((5 : Fin 11),8)},{s((3 : Fin 11),6),s((7 : Fin 11),9)},{s((3 : Fin 11),7),s((4 : Fin 11),8)},{s((3 : Fin 11),7),s((4 : Fin 11),10)},{s((3 : Fin 11),7),s((5 : Fin 11),8)},{s((3 : Fin 11),7),s((5 : Fin 11),9)},{s((3 : Fin 11),7),s((6 : Fin 11),7)},{s((3 : Fin 11),7),s((6 : Fin 11),10)},{s((3 : Fin 11),7),s((7 : Fin 11),9)},{s((3 : Fin 11),7),s((8 : Fin 11),9)},{s((4 : Fin 11),8),s((5 : Fin 11),8)},{s((4 : Fin 11),8),s((5 : Fin 11),9)},{s((4 : Fin 11),8),s((6 : Fin 11),10)},{s((4 : Fin 11),8),s((7 : Fin 11),9)},{s((4 : Fin 11),8),s((8 : Fin 11),9)},{s((4 : Fin 11),10),s((5 : Fin 11),8)},{s((4 : Fin 11),10),s((6 : Fin 11),7)},{s((4 : Fin 11),10),s((6 : Fin 11),10)},{s((4 : Fin 11),10),s((8 : Fin 11),9)},{s((5 : Fin 11),8),s((6 : Fin 11),7)},{s((5 : Fin 11),8),s((6 : Fin 11),10)},{s((5 : Fin 11),8),s((7 : Fin 11),9)},{s((5 : Fin 11),8),s((8 : Fin 11),9)},{s((5 : Fin 11),9),s((6 : Fin 11),7)},{s((6 : Fin 11),7),s((7 : Fin 11),9)},{s((6 : Fin 11),7),s((8 : Fin 11),9)},{s((6 : Fin 11),10),s((7 : Fin 11),9)}}
def z1 : Finset (Fin 11) := {2,4,6,9}
def cls1 : Finset (Finset E) := {{s((0 : Fin 11),9),s((1 : Fin 11),4)},{s((0 : Fin 11),9),s((2 : Fin 11),5)},{s((0 : Fin 11),9),s((2 : Fin 11),10)},{s((0 : Fin 11),9),s((3 : Fin 11),6)},{s((0 : Fin 11),9),s((4 : Fin 11),8)},{s((0 : Fin 11),9),s((4 : Fin 11),10)},{s((0 : Fin 11),9),s((5 : Fin 11),9)},{s((0 : Fin 11),9),s((6 : Fin 11),7)},{s((0 : Fin 11),9),s((6 : Fin 11),10)},{s((0 : Fin 11),9),s((7 : Fin 11),9)},{s((0 : Fin 11),9),s((8 : Fin 11),9)},{s((1 : Fin 11),4),s((3 : Fin 11),6)},{s((1 : Fin 11),4),s((4 : Fin 11),8)},{s((1 : Fin 11),4),s((4 : Fin 11),10)},{s((1 : Fin 11),4),s((6 : Fin 11),7)},{s((1 : Fin 11),4),s((7 : Fin 11),9)},{s((2 : Fin 11),5),s((2 : Fin 11),10)},{s((2 : Fin 11),5),s((3 : Fin 11),6)},{s((2 : Fin 11),5),s((4 : Fin 11),10)},{s((2 : Fin 11),5),s((7 : Fin 11),9)},{s((3 : Fin 11),6),s((4 : Fin 11),8)},{s((3 : Fin 11),6),s((5 : Fin 11),9)},{s((3 : Fin 11),6),s((6 : Fin 11),7)},{s((3 : Fin 11),6),s((6 : Fin 11),10)},{s((3 : Fin 11),6),s((8 : Fin 11),9)},{s((4 : Fin 11),8),s((4 : Fin 11),10)},{s((5 : Fin 11),9),s((7 : Fin 11),9)},{s((5 : Fin 11),9),s((8 : Fin 11),9)},{s((6 : Fin 11),7),s((6 : Fin 11),10)},{s((7 : Fin 11),9),s((8 : Fin 11),9)}}
def z2 : Finset (Fin 11) := {0,4,5,7}
def cls2 : Finset (Finset E) := {{s((0 : Fin 11),9),s((0 : Fin 11),10)},{s((0 : Fin 11),10),s((2 : Fin 11),5)},{s((1 : Fin 11),4),s((2 : Fin 11),5)},{s((2 : Fin 11),5),s((4 : Fin 11),8)},{s((2 : Fin 11),5),s((5 : Fin 11),8)},{s((2 : Fin 11),5),s((5 : Fin 11),9)},{s((4 : Fin 11),8),s((6 : Fin 11),7)},{s((5 : Fin 11),8),s((5 : Fin 11),9)}}
def z3 : Finset (Fin 11) := {1,3,9,10}
def cls3 : Finset (Finset E) := {{s((1 : Fin 11),4),s((1 : Fin 11),8)},{s((2 : Fin 11),10),s((7 : Fin 11),9)},{s((3 : Fin 11),6),s((3 : Fin 11),7)},{s((4 : Fin 11),10),s((7 : Fin 11),9)},{s((5 : Fin 11),9),s((6 : Fin 11),10)},{s((6 : Fin 11),10),s((8 : Fin 11),9)}}
def z4 : Finset (Fin 11) := {0,2,7,8}
def cls4 : Finset (Finset E) := {{s((2 : Fin 11),5),s((6 : Fin 11),7)}}
abbrev Row := Finset (Fin 11) × Finset (Finset E)
def good (g : Row) : Prop := independent g.1 ∧ ∀ F∈g.2, ∀ t∈allowed, Disjoint t.2 F → (∀e∈F, hits t.1 e) → ¬Disjoint t.1 g.1
instance (g : Row) : Decidable (good g) := by unfold good; infer_instance
def rows : List Row := [(z0,cls0),(z1,cls1),(z2,cls2),(z3,cls3),(z4,cls4)]
end Pair5184
namespace Pair5184
open EdgeBank4081 Triple4081
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def marks (g : Row) : Prop :=
  ∀ F∈g.2, ∀ x : Fin 11, (∀ e∈F, x∉e) →
    ∃ e∈F, ∀ y : Fin 11, y∈e → s(x,y)∈allEdges → y∈g.1

instance (g : Row) : Decidable (marks g) := by unfold marks; infer_instance

theorem marks0 : marks (z0,cls0) := by decide +kernel
theorem marks1 : marks (z1,cls1) := by decide +kernel
theorem marks2 : marks (z2,cls2) := by decide +kernel
theorem marks3 : marks (z3,cls3) := by decide +kernel
theorem marks4 : marks (z4,cls4) := by decide +kernel

theorem marked_rows (g : Row) (h : g∈rows) : marks g := by
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact marks0
  · exact marks1
  · exact marks2
  · exact marks3
  · exact marks4

end Pair5184
