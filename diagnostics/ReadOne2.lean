import PEqualNP.Outside.L_meta_6369
namespace PEqualNP.Outside.L_meta_9736_read
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
set_option maxRecDepth 32768
set_option maxHeartbeats 0
abbrev V := Fin 10
def edges : List (Nat × Nat) := [(0, 4), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7), (3, 4), (3, 8), (4, 9), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9)]
def rel (a b : V) := (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges
instance (a b : V) : Decidable (rel a b) := by unfold rel; infer_instance
def G : SimpleGraph V where
  Adj := rel
  symm := ⟨fun a b h => Or.symm h⟩
  loopless := by
    have h : ∀ a : V, ¬rel a a := by decide +kernel
    exact ⟨h⟩
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (rel a b))
theorem c4 : NoFourCycle G := by decide +kernel
theorem edgeCount : G.edgeFinset.card = 14 := by decide +kernel
theorem coverCount : ∀ S : Finset V, (∀ a b : V,G.Adj a b → a∈S ∨ b∈S) → 6≤S.card := by decide +kernel
theorem lower (C : Circuit) (ao : IsAO2 10 C) (r : IsReadK 10 C 1)
    (ok : ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ ∃ a b : V,(a.val,b.val)∈edges ∧ x a=true ∧ x b=true) : 19 ≤ C.size := by
  have h (x : V → Bool) : circuitFun 10 C x = decide (∃ a b : V, G.Adj a b ∧ x a=true ∧ x b=true) := by
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x)=true ↔ _
    rw [decide_eq_true_eq,ok]
    constructor
    · rintro ⟨a,b,ab,ha,hb⟩
      exact ⟨a,b,Or.inl ab,ha,hb⟩
    · rintro ⟨a,b,ab,ha,hb⟩
      rcases ab with ab | ba
      · exact ⟨a,b,ab,ha,hb⟩
      · exact ⟨b,a,ba,hb,ha⟩
  obtain ⟨S,hS,hcost⟩ := PEqualNP.Outside.L_meta_6369 10 G C c4 ao h r
  have hs := coverCount S hS
  rw [edgeCount] at hcost
  omega
end PEqualNP.Outside.L_meta_9736_read
