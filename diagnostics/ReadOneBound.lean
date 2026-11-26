import PEqualNP.Outside.L_meta_6369
namespace PEqualNP.Outside.L_meta_9738_read
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
set_option maxRecDepth 32768
set_option maxHeartbeats 0
abbrev V := Fin 25
def edges : List (Nat × Nat) := [(0, 16), (0, 22), (0, 24), (1, 13), (1, 17), (1, 23), (2, 13), (2, 14), (2, 18), (2, 24), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 17), (8, 19), (8, 20), (8, 24), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23), (12, 15), (12, 21), (12, 23), (12, 24)]
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
theorem edgeCount : G.edgeFinset.card = 48 := by decide +kernel
def leftPoint (i : Fin 12) : V :=
  ([1,2,3,4,5,6,8,11,9,10,7,0] : List V).getD i.val 0

def rightLine (i : Fin 12) : V := ⟨13+i.val,by omega⟩

private theorem matched : ∀ i : Fin 12, G.Adj (leftPoint i) (rightLine i) := by decide +kernel

private theorem apart : ∀ i j : Fin 12, i ≠ j →
    leftPoint i ≠ leftPoint j ∧ leftPoint i ≠ rightLine j ∧
    rightLine i ≠ leftPoint j ∧ rightLine i ≠ rightLine j := by decide +kernel

theorem coverCount (S : Finset V) (covers : ∀ a b : V, G.Adj a b → a ∈ S ∨ b ∈ S) :
    12 ≤ S.card := by
  let pick (i : Fin 12) : V := if leftPoint i ∈ S then leftPoint i else rightLine i
  have chosen (i : Fin 12) : pick i ∈ S := by
    by_cases h : leftPoint i ∈ S
    · simpa [pick,h] using h
    · simpa [pick,h] using (covers _ _ (matched i)).resolve_left h
  have injective : Function.Injective pick := by
    intro i j eq
    by_contra ne
    obtain ⟨hll,hlr,hrl,hrr⟩ := apart i j ne
    by_cases hi : leftPoint i ∈ S <;> by_cases hj : leftPoint j ∈ S <;>
      simp only [pick,hi,hj,ite_true,ite_false] at eq
    · exact hll eq
    · exact hlr eq
    · exact hrl eq
    · exact hrr eq
  let f (i : Fin 12) : {v // v ∈ S} := ⟨pick i,chosen i⟩
  have bound := Fintype.card_le_of_injective f (fun i j eq =>
    injective (congrArg Subtype.val eq))
  simpa using bound

theorem lower (C : Circuit) (ao : IsAO2 25 C) (r : IsReadK 25 C 1)
    (ok : ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ ∃ a b : V,(a.val,b.val)∈edges ∧ x a=true ∧ x b=true) : 59 ≤ C.size := by
  have h (x : V → Bool) : circuitFun 25 C x = decide (∃ a b : V, G.Adj a b ∧ x a=true ∧ x b=true) := by
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
  obtain ⟨S,hS,hcost⟩ := PEqualNP.Outside.L_meta_6369 25 G C c4 ao h r
  have hs := coverCount S hS
  rw [edgeCount] at hcost
  omega
end PEqualNP.Outside.L_meta_9738_read
