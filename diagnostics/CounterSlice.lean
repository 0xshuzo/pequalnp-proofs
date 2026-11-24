import Mathlib
import PEqualNP.Defs

namespace StarSlice1900

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (l : List (Fin 5 × Fin 5)) (u v : Fin 5) : Bool := l.contains (u,v) || l.contains (v,u)

def graphOf (l : List (Fin 5 × Fin 5)) (h : ∀ i : Fin 5, edge l i i = false) : SimpleGraph (Fin 5) where
  Adj u v := edge l u v = true
  symm := ⟨fun u v hp => by simpa [edge,Bool.or_comm] using hp⟩
  loopless := ⟨fun i hi => by simpa [h i] using hi⟩

def G := graphOf [(0,1),(0,2),(0,4),(1,2),(2,3)] (by decide +kernel)
def H := graphOf [(1,2),(2,3)] (by decide +kernel)
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (edge _ a b = true))
instance : DecidableRel H.Adj := fun a b => inferInstanceAs (Decidable (edge _ a b = true))

def C : Circuit :=
  ⟨[⟨.or,[0,2]⟩, ⟨.or,[0,3]⟩, ⟨.or,[2,4]⟩, ⟨.and,[6,7]⟩, ⟨.or,[1,8]⟩, ⟨.and,[5,9]⟩],10⟩

def D : Circuit := ⟨[⟨.or,[1,3]⟩,⟨.and,[2,5]⟩],6⟩

def L : Finset (Fin 5) := {1,2,4}

theorem c_mono : Monotone2 C := by simp [Monotone2,C]
theorem c_computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by decide +kernel

theorem no_four : ∀ a b c d : Fin 5, a ≠ c → b ≠ d →
    ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by decide +kernel

def witness (i : Fin 5) : Bool := decide (i=3 ∨ i=4)
theorem dirty : (Finset.univ.filter fun i => witness i = true).card = 2 ∧
    (C.wires (List.ofFn witness)).getD (5+3) false = true ∧
    ¬ ∃ u v, G.Adj u v ∧ witness u = true ∧ witness v = true := by decide +kernel

theorem paid : L.Nonempty ∧ (∀ v ∈ L, G.Adj 0 v) ∧
    (∀ u v, H.Adj u v ↔ G.Adj u v ∧ ¬ ((u=0 ∧ v∈L) ∨ (v=0 ∧ u∈L))) ∧
    Monotone2 D ∧ (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = true ↔
       ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) ∧
    D.size + L.card + 1 = C.size := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  simp [Monotone2,D]

end StarSlice1900
