import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8935.SharedCycle
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.ReadK PEqualNP.TopForm
abbrev G := edgeGraph 6 [(0,3),(0,4),(1,4),(1,5),(2,5),(2,3)]
def edge (i : Fin 6) : Fin 6 × Fin 6 := ![(0,3),(0,4),(1,4),(1,5),(2,5),(2,3)] i
def net (a b c d : ℕ) : Circuit := ⟨[
  ⟨.or,[3,4]⟩,⟨.or,[0,1]⟩,⟨.and,[a,b]⟩,⟨.and,[0,8]⟩,
  ⟨.or,[4,5]⟩,⟨.or,[1,2]⟩,⟨.and,[c,d]⟩,⟨.and,[1,12]⟩,
  ⟨.or,[5,3]⟩,⟨.and,[2,14]⟩,⟨.or,[9,13]⟩,⟨.or,[16,15]⟩],17⟩
def base := net 6 7 10 11
def withBanks := net 0 6 1 10
def direct (i j : Fin 6) := net (edge i).1.val (edge i).2.val (edge j).1.val (edge j).2.val
theorem model : IsAO2 6 base ∧ TopForm G base ∧ junk G base={2,6} := by decide +kernel
theorem exactBase : ∀ x : Fin 6→Bool, circuitFun 6 base x=graphFun G ∅ x := by decide +kernel
theorem failedReads : readsAtMost base 6 [0,3] 1=false ∧ readsAtMost base 6 [0,4] 1=false ∧
    gateVal 6 base 2 (pairInput (0:Fin 6) 3)=true ∧ gateVal 6 base 2 (pairInput (0:Fin 6) 4)=true := by decide +kernel
theorem impossibleDirect : ∀ i j : Fin 6, ∃ t : Fin 6,
    circuitFun 6 (direct i j) (pairInput (edge t).1 (edge t).2)=false := by decide +kernel
theorem banksWork : IsAO2 6 withBanks ∧ junk G withBanks=∅ ∧ withBanks.size=base.size ∧
    ∀ x : Fin 6→Bool, circuitFun 6 withBanks x=graphFun G ∅ x := by decide +kernel
end PEqualNP.Outside.L_meta_8935.SharedCycle
