import Mathlib
import PEqualNP.Outside.L_meta_1708

namespace Pendant1739
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Sym2

def Priced {n : Nat} (G : SimpleGraph (Fin n)) (t : Nat) : Prop :=
  ∀ C : Circuit, Monotone2 C →
  (∀ x : Fin n → Bool,C.eval (List.ofFn x)=true ↔ ∃ u v,G.Adj u v ∧ x u=true ∧ x v=true) →
  G.edgeSet.ncard+t≤C.size+1

def Remove {n : Nat} (G H : SimpleGraph (Fin n)) : Prop :=
  open Classical in ∃ v : Fin n,G.degree v=1 ∧ H=G.deleteIncidenceSet v

theorem one {n t} {G H : SimpleGraph (Fin n)} (step : Remove G H) (base : Priced H t) :
    Priced G t := by
  classical
  obtain ⟨v,d,rfl⟩ := step
  intro C mc spec
  have full : circuitFun n C=fun x : Fin n → Bool => decide (∃ a b,G.Adj a b ∧ x a=true ∧ x b=true) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact spec x
  obtain ⟨D,dm,lt,eval⟩ := PEqualNP.Outside.L_meta_1708 n G v (by omega) (by omega) C mc full
  have cost := base D dm (fun x => by
    have e := congrFun eval x
    change D.eval (List.ofFn x)=_ at e
    rw [e,decide_eq_true_eq])
  have edge : 0<G.edgeSet.ncard := by
    have nn : (G.neighborFinset v).Nonempty := Finset.card_pos.mp (show 0<G.degree v by omega)
    obtain ⟨w,hw⟩ := nn
    rw [←SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
    exact Finset.card_pos.mpr ⟨s(v,w),by simpa using hw⟩
  have count : (G.deleteIncidenceSet v).edgeSet.ncard=G.edgeSet.ncard-1 := by
    simpa only [←Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset,d] using G.card_edgeFinset_deleteIncidenceSet v
  omega

theorem attachForest {n t} {G H : SimpleGraph (Fin n)} (strip : Relation.ReflTransGen Remove G H) :
    Priced H t → Priced G t := by
  induction strip with
  | refl => exact id
  | tail _ step ih => exact fun h => ih (one step h)

end Pendant1739
