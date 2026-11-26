import PEqualNP.Defs

namespace Counter18726
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 1000000
def gate (a b : Nat) : Gate := ⟨.and,[a,b]⟩
def C : Circuit := ⟨[gate 0 1,gate 0 1,gate 3 4],5⟩
abbrev I := Fin C.gates.length
abbrev X := Fin 3 → Bool
def K : Finset I := {2}
def P : Finset I := {0,1}
def pin (x : X) := List.ofFn (Function.update x 2 false)
def W (x : X) (j : Nat) := (C.wires (pin x)).getD j false

theorem members {g : Gate} (h : g∈C.gates) : g=gate 0 1 ∨ g=gate 3 4 := by
  change g∈[gate 0 1,gate 0 1,gate 3 4] at h
  simpa [or_assoc] using h
theorem fan : FanInTwo C := by
  intro g hg
  rcases members hg with rfl|rfl <;> simp [gate]
theorem signed_shape (g : Gate) (hg : g∈C.gates) (nt : g.op=.not) : g.inputs.length=1 := by
  rcases members hg with rfl|rfl <;> cases nt
theorem copy3 : ∀x : X,W x 5=W x 3 := by decide +kernel
theorem copy4 : ∀x : X,W x 5=W x 4 := by decide +kernel
theorem lastReader : ∀ (p k : I), p∈P → 3+p.val∈(C.gates.get k).inputs → k=2 := by decide +kernel

theorem noZero (D : Circuit) (ds : D.size=0)
    (eq : ∀x : X,D.eval (List.ofFn x)=C.eval (pin x)) : False := by
  rcases D with ⟨gs,o⟩
  change gs.length=0 at ds
  have emp : gs=[] := by simpa using ds
  subst gs
  change ∀x : X,(List.ofFn x).getD o false=C.eval (pin x) at eq
  by_cases small : o<3
  · have misses : ∀i : Fin 3, ∃x : X,(List.ofFn x).getD i.val false≠C.eval (pin x) := by
      decide +kernel
    obtain ⟨x,h⟩ := misses ⟨o,small⟩
    exact h (eq x)
  · let high : X := fun _ => true
    have src : C.eval (pin high)=true := by decide +kernel
    have lo : (List.ofFn high).length≤o := by simpa using Nat.le_of_not_gt small
    have test := eq high
    rw [List.getD_eq_default _ _ lo,src] at test
    cases test

theorem exactNegation : ¬ (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool) (K P : Finset (Fin C.gates.length)), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → Disjoint K P → (∀ j ∈ K, (∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = c) ∨ (∃ w ∈ (C.gates.get j).inputs, ∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD w false = c) ∨ ∃ w ∈ (C.gates.get j).inputs, w < n + j.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = (C.wires (List.ofFn (Function.update x v b))).getD w false) → (∀ p ∈ P, n + p.val ≠ C.output ∧ ∀ k : Fin C.gates.length, n + p.val ∈ (C.gates.get k).inputs → k ∈ P ∨ (k ∈ K ∧ ((∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + k.val) false = c) ∨ ∃ w ∈ (C.gates.get k).inputs, w < n + k.val ∧ w ≠ n + p.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + k.val) false = (C.wires (List.ofFn (Function.update x v b))).getD w false))) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + K.card + P.card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b))) := by
  intro universal
  specialize universal 3 C 2 false K P fan signed_shape
    ⟨fun _ => false,by decide +kernel⟩ (by decide +kernel)
  have saved : ∀j∈K, ∃w∈(C.gates.get j).inputs, w<3+j.val ∧ ∀x : X,W x (3+j.val)=W x w := by
    intro j hj
    have j2 : j=2 := Finset.mem_singleton.mp hj
    subst j
    exact ⟨3,by decide,by decide,copy3⟩
  specialize universal (fun j hj => Or.inr (Or.inr (saved j hj)))
  have nr : ∀p∈P,3+p.val≠C.output := by decide +kernel
  specialize universal (by
    intro p hp
    refine ⟨nr p hp,?_⟩
    intro k hk
    have kr := lastReader p k hp hk
    subst k
    refine Or.inr ⟨by decide,Or.inr ?_⟩
    change p∈insert 0 ({1} : Finset I) at hp
    rcases Finset.mem_insert.mp hp with rfl|p1
    · exact ⟨4,by decide,by decide,by decide,copy4⟩
    · have p1' : p=1 := Finset.mem_singleton.mp p1
      subst p
      exact ⟨3,by decide,by decide,by decide,copy3⟩)
  obtain ⟨D,_,budget,eq⟩ := universal
  have bK : K.card=1 := by decide
  have bP : P.card=2 := by decide
  have bC : C.size=3 := rfl
  exact noZero D (by omega) eq

end Counter18726
