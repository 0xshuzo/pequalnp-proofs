import Mathlib
import PEqualNP.Defs
open scoped BigOperators

namespace EdgeBank4081

abbrev E := Sym2 (Fin 11)
abbrev Entry := Finset E × Finset E
def weight (x : Entry) := x.1.card-1
def compat (x y : Entry) : Prop := Disjoint x.1 y.1 ∧ Disjoint x.1 y.2 ∧ Disjoint y.1 x.2
instance (x y : Entry) : Decidable (compat x y) := by unfold compat; infer_instance

def cap : ℕ → List Entry → ℕ
  | 0, _ => 0
  | _+1, [] => 0
  | k+1, x::xs => max (cap k xs) (weight x + cap k (xs.filter (fun y => decide (compat x y))))

theorem sum_le_cap (k : ℕ) (xs : List Entry) (hlen : xs.length ≤ k) (S : Finset Entry)
    (available : ∀ a∈S, a∈xs) (indep : ∀ a∈S, ∀ b∈S, a≠b → compat a b) :
    (∑ a∈S,weight a) ≤ cap k xs := by
  induction k generalizing xs S with
  | zero =>
    have e : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    have empty : S=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => by simpa using available a ha)
    simp [empty,cap]
  | succ k ih =>
    cases xs with
    | nil =>
      have empty : S=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => by simpa using available a ha)
      simp [empty,cap]
    | cons x xs =>
      have l : xs.length ≤ k := by simpa using hlen
      by_cases has : x∈S
      · let T := S.erase x
        have smaller : (xs.filter (fun y => decide (compat x y))).length ≤ k :=
          (List.length_filter_le _ xs).trans l
        have listT : ∀ a∈T, a∈xs.filter (fun y => decide (compat x y)) := by
          intro a ha
          obtain ⟨neq,member⟩ := Finset.mem_erase.mp ha
          obtain h|h := List.mem_cons.mp (available a member)
          · exact False.elim (neq h)
          · exact List.mem_filter.mpr ⟨h,decide_eq_true (indep x has a member neq.symm)⟩
        have diff := ih _ smaller T listT (fun a ha b hb ab => indep a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) ab)
        have sm := Finset.sum_erase_add S weight has
        change (∑ a∈S.erase x, weight a) ≤ _ at diff
        simp only [cap]
        exact (by omega : (∑ a∈S,weight a) ≤ weight x + cap k (xs.filter (fun y => decide (compat x y)))) |>.trans (le_max_right _ _)
      · have listS : ∀ a∈S, a∈xs := by
          intro a ha
          rcases List.mem_cons.mp (available a ha) with eq|mem
          · exact False.elim (has (eq ▸ ha))
          · exact mem
        exact (ih _ l S listS indep).trans (le_max_left _ _)

def catalog : List Entry := [
  ({s((0 : Fin 11),(9 : Fin 11)),s((1 : Fin 11),(4 : Fin 11))},{s((0 : Fin 11),(10 : Fin 11)),s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((0 : Fin 11),(10 : Fin 11)),s((1 : Fin 11),(8 : Fin 11))},{s((0 : Fin 11),(9 : Fin 11)),s((1 : Fin 11),(4 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((0 : Fin 11),(9 : Fin 11)),s((2 : Fin 11),(5 : Fin 11))},{s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((1 : Fin 11),(4 : Fin 11)),s((2 : Fin 11),(5 : Fin 11))},{s((1 : Fin 11),(8 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({s((0 : Fin 11),(9 : Fin 11)),s((1 : Fin 11),(4 : Fin 11)),s((2 : Fin 11),(5 : Fin 11))},{s((0 : Fin 11),(10 : Fin 11)),s((1 : Fin 11),(8 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((1 : Fin 11),(8 : Fin 11)),s((2 : Fin 11),(10 : Fin 11))},{s((1 : Fin 11),(4 : Fin 11)),s((2 : Fin 11),(5 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({s((0 : Fin 11),(9 : Fin 11)),s((3 : Fin 11),(6 : Fin 11))},{s((0 : Fin 11),(10 : Fin 11)),s((3 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({s((0 : Fin 11),(10 : Fin 11)),s((3 : Fin 11),(7 : Fin 11))},{s((0 : Fin 11),(9 : Fin 11)),s((3 : Fin 11),(6 : Fin 11)),s((6 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({s((0 : Fin 11),(9 : Fin 11)),s((4 : Fin 11),(8 : Fin 11))},{s((0 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({s((2 : Fin 11),(5 : Fin 11)),s((4 : Fin 11),(8 : Fin 11))},{s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((0 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))},{s((0 : Fin 11),(9 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({s((0 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))},{s((0 : Fin 11),(9 : Fin 11)),s((2 : Fin 11),(5 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))},{s((1 : Fin 11),(4 : Fin 11)),s((1 : Fin 11),(8 : Fin 11)),s((2 : Fin 11),(5 : Fin 11)),s((2 : Fin 11),(10 : Fin 11))}),
  ({s((1 : Fin 11),(4 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))},{s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))},{s((0 : Fin 11),(9 : Fin 11)),s((0 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))},{s((2 : Fin 11),(5 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((2 : Fin 11),(5 : Fin 11)),s((6 : Fin 11),(7 : Fin 11))},{s((2 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((6 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({s((4 : Fin 11),(8 : Fin 11)),s((6 : Fin 11),(7 : Fin 11))},{s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((2 : Fin 11),(5 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((6 : Fin 11),(7 : Fin 11))},{s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((6 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((5 : Fin 11),(9 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))},{s((2 : Fin 11),(5 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({s((2 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))},{s((2 : Fin 11),(5 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({s((4 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))},{s((4 : Fin 11),(8 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(10 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({s((6 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))},{s((0 : Fin 11),(9 : Fin 11)),s((0 : Fin 11),(10 : Fin 11)),s((3 : Fin 11),(6 : Fin 11)),s((3 : Fin 11),(7 : Fin 11))}),
  ({s((2 : Fin 11),(10 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))},{s((0 : Fin 11),(9 : Fin 11)),s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(5 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({s((2 : Fin 11),(10 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))},{s((2 : Fin 11),(5 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({s((4 : Fin 11),(10 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))},{s((0 : Fin 11),(9 : Fin 11)),s((0 : Fin 11),(10 : Fin 11)),s((1 : Fin 11),(4 : Fin 11)),s((1 : Fin 11),(8 : Fin 11))}),
  ({s((6 : Fin 11),(10 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))},{s((4 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))})]

theorem exact_price : cap catalog.length catalog=3 := by decide +kernel

theorem three (S : Finset Entry) (available : ∀ a∈S, a∈catalog)
    (indep : ∀ a∈S, ∀ b∈S, a≠b → compat a b) : (∑ a∈S,weight a) ≤ 3 := by
  have h := sum_le_cap catalog.length catalog le_rfl S available indep
  simpa only [exact_price] using h


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

def availableEdges (A B : Label) : Finset E := (allEdges \ (A.2 ∪ B.2)).filter fun e => hits A.1 e ∧ hits B.1 e


def checkRow (A : Label) : Bool := allowed.all fun B =>
  if Disjoint A.1 B.1 then decide (((availableEdges A B).powerset.filter (fun T =>
    2 ≤ T.card ∧ catalog.any (fun v => decide (v.1=T ∧ v.2 ⊆ A.2 ∪ B.2))=false))=∅)
  else true

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem row_63 : checkRow (allowed[63]!)=true := by decide +kernel

end EdgeBank4081
