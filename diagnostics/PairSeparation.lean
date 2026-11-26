import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18723
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graphFn {n : ℕ} (E : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  E.any fun e => x e.1 && x e.2


def adj (E : List (Fin n × Fin n)) (a b : Fin n) : Prop :=
  (a,b) ∈ E ∨ (b,a) ∈ E

theorem adjSymm (E : List (Fin n × Fin n)) (a b : Fin n) : adj E a b ↔ adj E b a := or_comm

theorem freeNeighbor (E : List (Fin n × Fin n)) (v u w z : Fin n)
    (noFour : ∀ a b c d, a ≠ c → b ≠ d → adj E a b → adj E b c → adj E c d → adj E d a → False)
    (uw : u ≠ w) (vz : v ≠ z) (vu : adj E v u) (vw : adj E v w) :
    ∃ t, (t=u ∨ t=w) ∧ adj E v t ∧ ¬ adj E z t := by
  classical
  by_cases zu : adj E z u
  · refine ⟨w,Or.inr rfl,vw,fun zw => ?_⟩
    exact noFour v u z w vz uw vu ((adjSymm E z u).mp zu) zw ((adjSymm E v w).mp vw)
  · exact ⟨u,Or.inl rfl,vu,zu⟩

def pairBits (z t : Fin n) (i : Fin n) : Bool := decide (i=z ∨ i=t)

theorem pairOff (E : List (Fin n × Fin n)) (z t : Fin n)
    (loops : ∀ e ∈ E, e.1 ≠ e.2) (indep : ¬ adj E z t) :
    graphFn E (pairBits z t) = false := by
  classical
  cases h : graphFn E (pairBits z t) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨⟨a,b⟩,he,hbits⟩ := (List.any_eq_true.mp h)
    change (pairBits z t a && pairBits z t b) = true at hbits
    simp only [pairBits,Bool.and_eq_true,decide_eq_true_eq] at hbits
    rcases hbits with ⟨az | at',bz | bt⟩
    · exact loops _ he (az.trans bz.symm)
    · exact indep (Or.inl (by simpa [az,bt] using he))
    · exact indep (Or.inr (by simpa [at',bz] using he))
    · exact loops _ he (at'.trans bt.symm)

theorem togglesPair (E : List (Fin n × Fin n)) (v u w z : Fin n)
    (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (noFour : ∀ a b c d, a ≠ c → b ≠ d → adj E a b → adj E b c → adj E c d → adj E d a → False)
    (uw : u ≠ w) (vz : v ≠ z) (vu : adj E v u) (vw : adj E v w) :
    ∃ x : Fin n → Bool, x z = true ∧ x v = false ∧ graphFn E x = false ∧
      graphFn E (Function.update x v true) = true := by
  classical
  obtain ⟨t,_,vt,zt⟩ := freeNeighbor E v u w z noFour uw vz vu vw
  have tv : t ≠ v := by
    intro eq; subst t
    rcases vt with he|he <;> exact loops _ he rfl
  refine ⟨pairBits z t, by simp [pairBits], by simp [pairBits,vz,tv.symm], pairOff E z t loops zt, ?_⟩
  apply List.any_eq_true.mpr
  rcases vt with he|he
  · exact ⟨(v,t),he,by simp [Function.update_of_ne tv,pairBits]⟩
  · exact ⟨(t,v),he,by simp [Function.update_of_ne tv,pairBits]⟩

end PEqualNP.Outside.L_meta_18723
