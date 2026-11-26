import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2428

namespace Clean65
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2428 (evalD tstep okb T0 good_fold good_init)
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
def C : Circuit := ⟨[⟨.or,[13,17]⟩,⟨.or,[26,23]⟩,⟨.or,[14,15]⟩,⟨.or,[28,19]⟩,⟨.and,[0,27]⟩,⟨.or,[25,30]⟩,⟨.and,[0,31]⟩,⟨.or,[2,32]⟩,⟨.or,[29,31]⟩,⟨.and,[33,34]⟩,⟨.or,[13,14]⟩,⟨.or,[36,18]⟩,⟨.or,[37,24]⟩,⟨.and,[1,38]⟩,⟨.or,[13,15]⟩,⟨.or,[40,16]⟩,⟨.or,[41,20]⟩,⟨.and,[3,42]⟩,⟨.or,[14,16]⟩,⟨.or,[44,17]⟩,⟨.or,[45,21]⟩,⟨.and,[4,46]⟩,⟨.or,[15,17]⟩,⟨.or,[48,18]⟩,⟨.or,[49,22]⟩,⟨.and,[5,50]⟩,⟨.or,[16,18]⟩,⟨.or,[52,19]⟩,⟨.or,[53,23]⟩,⟨.and,[6,54]⟩,⟨.or,[17,19]⟩,⟨.or,[56,20]⟩,⟨.or,[57,24]⟩,⟨.and,[7,58]⟩,⟨.or,[18,20]⟩,⟨.or,[60,21]⟩,⟨.or,[61,25]⟩,⟨.and,[8,62]⟩,⟨.or,[13,19]⟩,⟨.or,[64,21]⟩,⟨.or,[65,22]⟩,⟨.and,[9,66]⟩,⟨.or,[14,20]⟩,⟨.or,[68,22]⟩,⟨.or,[69,23]⟩,⟨.and,[10,70]⟩,⟨.or,[15,21]⟩,⟨.or,[72,23]⟩,⟨.or,[73,24]⟩,⟨.and,[11,74]⟩,⟨.or,[16,22]⟩,⟨.or,[76,24]⟩,⟨.or,[77,25]⟩,⟨.and,[12,78]⟩,⟨.or,[35,39]⟩,⟨.or,[80,43]⟩,⟨.or,[81,47]⟩,⟨.or,[82,51]⟩,⟨.or,[83,55]⟩,⟨.or,[84,59]⟩,⟨.or,[85,63]⟩,⟨.or,[86,67]⟩,⟨.or,[87,71]⟩,⟨.or,[88,75]⟩,⟨.or,[89,79]⟩],90⟩
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

theorem gateTest : ∀ j : Fin 65, let g := C.gates.getD j.val ⟨.or,[]⟩; (g.op=.and ∨ g.op=.or) ∧ g.inputs=[g.inputs.getD 0 0,g.inputs.getD 1 0] ∧ g.inputs.getD 0 0≠g.inputs.getD 1 0 ∧ g.inputs.getD 0 0<26+j.val ∧ g.inputs.getD 1 0<26+j.val := by decide +kernel

theorem gateLegal (j : Nat) (g : Gate) (h : C.gates[j]?=some g) : legal j g := by
  obtain ⟨hj,e⟩ := List.getElem?_eq_some_iff.mp h
  have v := gateTest ⟨j,hj⟩
  have ge : C.gates.getD j ⟨.or,[]⟩=g := by rw [List.getD_eq_getElem _ _ hj,e]
  change (_ ∨ _) ∧ _ at v
  simp only [ge] at v
  exact ⟨v.1,_,_,v.2⟩


theorem sourceClean : ∀ j : Fin 65, (gateAt C j.val).op=.and →
    ∀ t∈(C.gates.foldl tstep T0).getD (26+j.val) [], ∃ e∈flags, e.1.val∈t ∧ (13+e.2.val)∈t := by decide +kernel

theorem clean (j : Fin 65) (op : (gateAt C j.val).op=.and) (x : Fin 26 → Bool) :
    PEqualNP.EdgeOwnership.gateVal 26 C j.val x=true → C.eval (List.ofFn x)=true := by
  intro on
  have ok : ∀ g∈C.gates, okb g=true := by decide +kernel
  have refl := (good_fold _ C.gates ok _ _ (good_init x)).2 (26+j.val)
  change (C.wires (List.ofFn x)).getD (26+j.val) false = true at on
  rw [refl,evalD,List.any_eq_true] at on
  obtain ⟨t,ht,ta⟩ := on
  obtain ⟨⟨p,l⟩,hf,hp,hl⟩ := sourceClean j op t ht
  have point : ∀ p : Fin 13, Fin.ofNat 26 p.val=Fin.castAdd 13 p := by decide
  have line : ∀ l : Fin 13, Fin.ofNat 26 (13+l.val)=Fin.natAdd 13 l := by decide
  have act := List.all_eq_true.mp ta
  exact (correct x).mpr ⟨p,l,(member p l).mp hf,by simpa only [point] using act _ hp,
    by simpa only [line] using act _ hl⟩

theorem marked : (gateAt C 9).op=.and ∧ PEqualNP.EdgeOwnership.InCone 26 C 9 (C.output-26) ∧
    PEqualNP.EdgeOwnership.gateVal 26 C 9 (PEqualNP.EdgeOwnership.pairInput 0 13)=true ∧
    ∀ i : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C 9 i) (PEqualNP.EdgeOwnership.pairInput 0 0)=false ∧
      PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C 9 i) (PEqualNP.EdgeOwnership.pairInput 13 13)=false := by decide +kernel
end Clean65
