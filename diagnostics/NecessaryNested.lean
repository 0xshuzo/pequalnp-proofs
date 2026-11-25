import Mathlib
import PEqualNP.Outside.L_meta_1981
import PEqualNP.Outside.L_meta_1983

namespace Nested2732
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def edges : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def target (x : Fin 14 → Bool) := decide (∃ a b : Fin 14, (a.val,b.val) ∈ edges ∧ x a=true ∧ x b=true)

/-- A necessary condition on the complete, earlier-wire-only circuit, including both posted prefix gates. -/
theorem necessary : (have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x3 x4 x5 x6 : ℕ) => ((15 : ℕ) * Min.min x3 x4 + Max.max x3 x4) * (225 : ℕ) + ((15 : ℕ) * Min.min x5 x6 + Max.max x5 x6); have x4 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x4 : Equiv.Perm (Fin (14 : ℕ))) (x5 : Fin (15 : ℕ)) => if ↑x5 < (14 : ℕ) then ↑(x4 (Fin.ofNat (14 : ℕ) ↑x5)) else (14 : ℕ); ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)) (x7 : Fin (15 : ℕ)) (x8 : Fin (15 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.GateOp) (x10 : PEqualNP.CircuitLowerBounds.GateOp) (x11 : PEqualNP.CircuitLowerBounds.Circuit),   x5 < x6 ∧     x7 < x8 ∧       (x9 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x9 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧         (x10 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧           (∀ (x12 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x13 : Fin (14 : ℕ) → Bool), x2 (x13 ∘ ⇑x12) = x2 x13) → x3 ↑x5 ↑x6 ↑x7 ↑x8 ≤ x3 (↑(x12 x5)) (↑(x12 x6)) (x4 x12 x7) (x4 x12 x8)) ∧             PEqualNP.MetaComplexity.Monotone2 x11 ∧               x11.size ≤ (24 : ℕ) ∧                 ∀ (x12 : Fin (14 : ℕ) → Bool),                   have x13 : List Bool := List.ofFn x12 ++ [x9.eval [x12 x5, x12 x6]];                   x11.eval (x13 ++ [x10.eval [x13.getD (↑x7) Bool.false, x13.getD (↑x8) Bool.false]]) = x2 x12) →
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 14 D ∧ D.size≤26 ∧
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x)=target x) ∧
      ∃ i j, (gateAt D i).op=.and ∧ (gateAt D j).op=.and ∧ PEqualNP.EdgeOwnership.InCone 14 D i j := by
  dsimp only
  rintro ⟨a,b,c,d,op,oq,T,_,_,hop,hoq,_,mono,budget,he⟩
  let g : Gate := ⟨op,[a.val,b.val]⟩
  let h : Gate := ⟨oq,[c.val,d.val]⟩
  let C : Circuit := ⟨g :: h :: T.gates,T.output⟩
  have cm : Monotone2 C := by
    intro k hk
    change k∈g::h::T.gates at hk
    rcases List.mem_cons.mp hk with rfl|hk
    · exact ⟨hop,(show (2:ℕ)≤2 from le_rfl)⟩
    rcases List.mem_cons.mp hk with rfl|hk
    · exact ⟨hoq,(show (2:ℕ)≤2 from le_rfl)⟩
    · exact mono _ hk
  have value (x : Fin 14 → Bool) : C.eval (List.ofFn x)=target x := by
    have raw (i : Fin 14) : (List.ofFn x).getD i.val false=x i := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn];exact i.isLt),List.getElem_ofFn]
    change C.eval (List.ofFn x)=target x
    simpa only [C,g,h,Circuit.eval,Circuit.wires,List.foldl_cons,List.map_cons,List.map_nil,raw,target,edges] using he x
  obtain ⟨D,dm,dr,dc,de⟩ := PEqualNP.Outside.L_meta_1981 C cm
  have short : D.size≤26 := by
    change D.size≤T.gates.length+1+1 at dc
    change T.gates.length≤24 at budget
    omega
  have full (x : Fin 14 → Bool) := (de x).trans (value x)
  refine ⟨D,dm,dr,short,full,?_⟩
  by_contra no
  have large := PEqualNP.Outside.L_meta_1983 D dm dr no (fun x => by
    rw [full x]
    exact decide_eq_true_iff)
  omega

end Nested2732
