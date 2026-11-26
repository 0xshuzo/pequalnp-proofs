import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2428

namespace Near5206
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2428 (evalD tstep okb T0 good_fold good_init)
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
def C : Circuit := ⟨[⟨.or,[13,17]⟩,⟨.or,[26,23]⟩,⟨.or,[14,15]⟩,⟨.or,[28,19]⟩,⟨.or,[0,2]⟩,⟨.and,[0,27]⟩,⟨.or,[25,31]⟩,⟨.or,[2,32]⟩,⟨.or,[29,32]⟩,⟨.and,[30,33]⟩,⟨.and,[34,35]⟩,⟨.or,[13,14]⟩,⟨.or,[37,18]⟩,⟨.or,[38,24]⟩,⟨.and,[1,39]⟩,⟨.or,[13,15]⟩,⟨.or,[41,16]⟩,⟨.or,[42,20]⟩,⟨.and,[3,43]⟩,⟨.or,[14,16]⟩,⟨.or,[45,17]⟩,⟨.or,[46,21]⟩,⟨.and,[4,47]⟩,⟨.or,[15,17]⟩,⟨.or,[49,18]⟩,⟨.or,[50,22]⟩,⟨.and,[5,51]⟩,⟨.or,[16,18]⟩,⟨.or,[53,19]⟩,⟨.or,[54,23]⟩,⟨.and,[6,55]⟩,⟨.or,[17,19]⟩,⟨.or,[57,20]⟩,⟨.or,[58,24]⟩,⟨.and,[7,59]⟩,⟨.or,[18,20]⟩,⟨.or,[61,21]⟩,⟨.or,[62,25]⟩,⟨.and,[8,63]⟩,⟨.or,[13,19]⟩,⟨.or,[65,21]⟩,⟨.or,[66,22]⟩,⟨.and,[9,67]⟩,⟨.or,[14,20]⟩,⟨.or,[69,22]⟩,⟨.or,[70,23]⟩,⟨.and,[10,71]⟩,⟨.or,[15,21]⟩,⟨.or,[73,23]⟩,⟨.or,[74,24]⟩,⟨.and,[11,75]⟩,⟨.or,[16,22]⟩,⟨.or,[77,24]⟩,⟨.or,[78,25]⟩,⟨.and,[12,79]⟩,⟨.or,[36,40]⟩,⟨.or,[81,44]⟩,⟨.or,[82,48]⟩,⟨.or,[83,52]⟩,⟨.or,[84,56]⟩,⟨.or,[85,60]⟩,⟨.or,[86,64]⟩,⟨.or,[87,68]⟩,⟨.or,[88,72]⟩,⟨.or,[89,76]⟩,⟨.or,[90,80]⟩],91⟩
def offsets : Finset (Fin 13) := {0,1,3,9}
def terms := (C.gates.foldl tstep T0).getD C.output []
lemma reflect (x : Fin 26 → Bool) :
    C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 26 i)) terms := by
  have ok : ∀ g∈C.gates, okb g=true := by decide +kernel
  exact (good_fold _ C.gates ok _ _ (good_init x)).2 C.output

def flags : List (Fin 13 × Fin 13) := [(0,0),(0,4),(0,10),(0,12),(1,0),(1,1),(1,5),(1,11),(2,1),(2,2),(2,6),(2,12),(3,0),(3,2),(3,3),(3,7),(4,1),(4,3),(4,4),(4,8),(5,2),(5,4),(5,5),(5,9),(6,3),(6,5),(6,6),(6,10),(7,4),(7,6),(7,7),(7,11),(8,5),(8,7),(8,8),(8,12),(9,0),(9,6),(9,8),(9,9),(10,1),(10,7),(10,9),(10,10),(11,2),(11,8),(11,10),(11,11),(12,3),(12,9),(12,11),(12,12)]
lemma member : ∀ p l : Fin 13, (p,l) ∈ flags ↔ p-l ∈ offsets := by decide +kernel
lemma contains : ∀ term∈terms, ∃ e∈flags, e.1.val∈term ∧ (13+e.2.val)∈term := by decide +kernel
lemma complete : ∀ e∈flags, ∃ term∈terms, ∀ i∈term, i=e.1.val ∨ i=13+e.2.val := by decide +kernel

lemma correct (x : Fin 26 → Bool) : C.eval (List.ofFn x)=true ↔
    ∃ p l : Fin 13, p-l∈offsets ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
  have point : ∀ p : Fin 13, Fin.ofNat 26 p.val=Fin.castAdd 13 p := by decide
  have line : ∀ l : Fin 13, Fin.ofNat 26 (13+l.val)=Fin.natAdd 13 l := by decide
  rw [reflect,evalD,List.any_eq_true]
  constructor
  · rintro ⟨z,hz,good⟩
    obtain ⟨⟨p,l⟩,hf,hp,hl⟩ := contains z hz
    have on := List.all_eq_true.mp good
    exact ⟨p,l,(member p l).mp hf,by simpa only [point] using on p.val hp,
      by simpa only [line] using on (13+l.val) hl⟩
  · rintro ⟨p,l,hf,hp,hl⟩
    obtain ⟨z,hz,sub⟩ := complete (p,l) ((member p l).mpr hf)
    refine ⟨z,hz,List.all_eq_true.mpr ?_⟩
    intro i hi
    rcases sub i hi with rfl | rfl
    · simpa only [point] using hp
    · simpa only [line] using hl

local instance : DecidableEq GateOp := gateOpDecEq

def legal (j : Nat) (g : Gate) : Prop := (g.op=.and ∨ g.op=.or) ∧ ∃ a b : Nat, g.inputs=[a,b] ∧ a≠b ∧ a<26+j ∧ b<26+j

theorem gateTest : ∀ j : Fin 66, let g := C.gates.getD j.val ⟨.or,[]⟩; (g.op=.and ∨ g.op=.or) ∧ g.inputs=[g.inputs.getD 0 0,g.inputs.getD 1 0] ∧ g.inputs.getD 0 0≠g.inputs.getD 1 0 ∧ g.inputs.getD 0 0<26+j.val ∧ g.inputs.getD 1 0<26+j.val := by decide +kernel

theorem gateLegal (j : Nat) (g : Gate) (h : C.gates[j]?=some g) : legal j g := by
  obtain ⟨hj,e⟩ := List.getElem?_eq_some_iff.mp h
  have v := gateTest ⟨j,hj⟩
  have ge : C.gates.getD j ⟨.or,[]⟩=g := by rw [List.getD_eq_getElem _ _ hj,e]
  change (_ ∨ _) ∧ _ at v
  simp only [ge] at v
  exact ⟨v.1,_,_,v.2⟩

theorem boundary : ¬(¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = x3;     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     x1.size ≤ (66 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, x6 x10 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x4 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ), x6 x10 ∧ ((26 : ℕ) + x10 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x10 (x1.output - (26 : ℕ))) ∧ x4 x10 x9 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), x5 (PEqualNP.TopForm.opnd x1 x10 x11) x7 = Bool.false ∧ x5 (PEqualNP.TopForm.opnd x1 x10 x11) x8 = Bool.false) := by
  intro no
  apply no
  refine ⟨C, by decide, gateLegal, correct, ?_, ?_⟩
  · exact ⟨9, by decide, by decide, (fun i : Fin 26 => decide (i=2)), by decide +kernel, by decide +kernel⟩
  · exact ⟨10, by decide, Or.inr (by decide +kernel), by decide +kernel, by decide +kernel⟩
end Near5206
