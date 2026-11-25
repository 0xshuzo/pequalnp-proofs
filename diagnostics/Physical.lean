import Mathlib
import PEqualNP.Outside.L_meta_3483
namespace Components4970
variable {α : Type} [DecidableEq α]
def Rules (S : ℕ → Finset α) (good paid : ℕ → Prop) (m : ℕ) :=
  ∀ i < m, good i →
    (S i).card ≤ 1 ∨
    (∃ a < i, good a ∧ S i ⊆ S a) ∨
    (paid i ∧ ∃ a < i, ∃ b < i, good a ∧ good b ∧ S i ⊆ S a ∪ S b)


end Components4970
namespace Components4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3483_aux
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

variable {α : Type} [DecidableEq α] {n : Nat} (C : Circuit)

def probeSet (U : Finset α) (probes : α → Fin n → Bool) (w : Nat) :=
  U.filter (fun x => val C (probes x) w = true)

def offAt (base : Fin n → Bool) (w : Nat) : Prop := val C base w = false

def isMerge (U : Finset α) (probes : α → Fin n → Bool) (base : Fin n → Bool) (w : Nat) : Prop :=
  n ≤ w ∧ (gateAt C (w-n)).op = GateOp.or ∧ offAt C base w ∧ 2 ≤ (probeSet C U probes w).card

theorem physicalRules (ao : IsAO2 n C) (U : Finset α) (probes : α → Fin n → Bool)
    (base : Fin n → Bool)
    (raw : ∀i : Fin n, base i=false → (U.filter (fun x=>probes x i=true)).card ≤ 1) :
    Rules (probeSet C U probes) (offAt C base) (isMerge C U probes base) (n+C.gates.length) := by
  classical
  intro w hw bad
  by_cases small : w<n
  · left
    let i : Fin n := ⟨w,small⟩
    have r (z : Fin n→Bool) : val C z w=z i := val_input C z i
    change val C base w=false at bad
    rw [r base] at bad
    simpa only [probeSet,r] using raw i bad
  let j := w-n
  have eqw : n+j=w := by dsimp [j]; omega
  have hj : j<C.gates.length := by omega
  let g := gateAt C j
  have ge : g=C.gates[j] := List.getD_eq_getElem _ _ hj
  have get : C.gates[j]?=some g := by simp [ge,hj]
  have gm : g∈C.gates := by rw [ge]; exact List.getElem_mem ..
  obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g gm)
  have la : a<w := by rw [←eqw]; exact ao.2.1 j hj a (by change a∈g.inputs; rw [ins]; simp)
  have lb : b<w := by rw [←eqw]; exact ao.2.1 j hj b (by change b∈g.inputs; rw [ins]; simp)
  have ev (x : Fin n → Bool) : val C x w = g.op.eval [val C x a,val C x b] := by
    rw [←eqw,val_gate C x get,ins]
    simp [operand,eqw,la,lb]
  change val C base w=false at bad
  rcases ao.1 g gm with op|op
  · right; left
    have off : val C base a=false ∨ val C base b=false := by
      rw [ev,op] at bad
      cases h : val C base a
      · exact Or.inl rfl
      · exact Or.inr (by simpa [GateOp.eval,h] using bad)
    have sb : probeSet C U probes w ⊆ probeSet C U probes a ∩ probeSet C U probes b := by
      intro i hi
      obtain ⟨mem,hit⟩ := Finset.mem_filter.mp hi
      rw [ev,op] at hit
      have hits : val C (probes i) a=true ∧ val C (probes i) b=true := by simpa [GateOp.eval] using hit
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨mem,hits.1⟩,Finset.mem_filter.mpr ⟨mem,hits.2⟩⟩
    rcases off with h|h
    · exact ⟨a,la,h,fun i hi => (Finset.mem_inter.mp (sb hi)).1⟩
    · exact ⟨b,lb,h,fun i hi => (Finset.mem_inter.mp (sb hi)).2⟩
  · by_cases few : (probeSet C U probes w).card ≤ 1
    · exact Or.inl few
    right; right
    have off : val C base a=false ∧ val C base b=false := by simpa [ev base,op,GateOp.eval] using bad
    refine ⟨⟨by omega,op,bad,by omega⟩,a,la,b,lb,off.1,off.2,?_⟩
    intro i hi
    obtain ⟨mem,hit⟩ := Finset.mem_filter.mp hi
    have hits : val C (probes i) a=true ∨ val C (probes i) b=true := by simpa [ev (probes i),op,GateOp.eval] using hit
    rcases hits with h|h
    · exact Finset.mem_union.mpr (Or.inl (show i ∈ probeSet C U probes a from Finset.mem_filter.mpr ⟨mem,h⟩))
    · exact Finset.mem_union.mpr (Or.inr (show i ∈ probeSet C U probes b from Finset.mem_filter.mpr ⟨mem,h⟩))

end Components4970
