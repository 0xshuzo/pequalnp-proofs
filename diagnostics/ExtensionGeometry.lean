import PEqualNP.Defs

-- The pair-clean circuit argument is adapted from the checked L-meta-1602 proof.
-- The incidence graph has 105 edges and a matching of size 21. An independent
-- pair must therefore activate an AND in any circuit of size at most 124.
-- Cyclic shifts and point-line duality send this pair into the specified input.
namespace PEqualNP.Outside.L_meta_9743

namespace Dirty

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev inc (a b : Fin 42) : Prop :=
  a.val < 21 ∧ 21 ≤ b.val ∧ (b.val+21-a.val) % 21 ∈ [0,5,7,17,20] ∧ (a.val≠0 ∨ b.val≠21)


def yes (x : Fin 42 → Bool) : Prop := ∃ a b, inc a b ∧ x a = true ∧ x b = true

abbrev plane : SimpleGraph (Fin 42) where
  Adj a b := inc a b ∨ inc b a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun a ha => by rcases ha with ha|ha <;> have := ha.1 <;> have := ha.2.1 <;> omega⟩


theorem graphEval (x : Fin 42 → Bool) :
    (∃ a b, plane.Adj a b ∧ x a = true ∧ x b = true) ↔ yes x := by
  constructor
  · rintro ⟨a,b,ab,ha,hb⟩
    rcases ab with ab|ba
    · exact ⟨a,b,ab,ha,hb⟩
    · exact ⟨b,a,ba,hb,ha⟩
  · rintro ⟨a,b,ab,ha,hb⟩
    exact ⟨a,b,Or.inl ab,ha,hb⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 15000000 in
theorem overlap (a c : Fin 42) (ac : a ≠ c) :
    (Finset.univ.filter (fun b => plane.Adj a b ∧ plane.Adj c b)).card ≤ 1 := by
  revert a c; decide +kernel

theorem noFour (a b c d : Fin 42) (ac : a ≠ c) (bd : b ≠ d) :
    ¬ (plane.Adj a b ∧ plane.Adj b c ∧ plane.Adj c d ∧ plane.Adj d a) := by
  rintro ⟨ab,bc,cd,da⟩
  exact bd (Finset.card_le_one.mp (overlap a c ac) b
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ab, bc.symm⟩) d
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, da.symm, cd⟩))

abbrev Vertex := Fin 42
def anchor (s : Bool) : Vertex := if s then 0 else 21
def shore (s : Bool) (a : Vertex) := if s then a.val<21 else 21≤a.val
instance (s : Bool) (a : Vertex) : Decidable (shore s a) := by unfold shore; split <;> infer_instance
theorem shares : ∀ (s : Bool) (a b : Vertex), shore s a → shore s b → a≠anchor s → b≠anchor s →
    ∃ l : Vertex, ¬shore s l ∧ plane.Adj a l ∧ plane.Adj b l := by decide +kernel
theorem path3 : ∀ (a b : Vertex), a.val<21 → 21≤b.val → ¬inc a b → (a≠0 ∨ b≠21) →
    ∃ p l : Vertex, a≠p ∧ b≠l ∧ plane.Adj a l ∧ plane.Adj l p ∧ plane.Adj p b := by decide +kernel

abbrev FourFree (G : SimpleGraph Vertex) :=
  ∀ a b c d : Vertex,a≠c → b≠d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)
theorem cross_only {G : SimpleGraph Vertex} (includeH : plane≤G) (h : FourFree G)
    (a b : Vertex) (ap : a.val<21) (bl : 21≤b.val) (ab : G.Adj a b) :
    inc a b ∨ (a=0 ∧ b=21) := by
  by_contra! bad
  have ex : a≠0 ∨ b≠21 := by tauto
  obtain ⟨p,l,nep,nel,al,lp,pb⟩ := path3 a b ap bl bad.1 ex
  exact h a l p b nep nel.symm ⟨includeH al,includeH lp,includeH pb,ab.symm⟩

theorem unique_other {G : SimpleGraph Vertex} (includeH : plane≤G) (h : FourFree G)
    (s : Bool) (a b c : Vertex) (sa : shore s a) (sb : shore s b) (sc : shore s c)
    (nb : b≠anchor s) (nc : c≠anchor s) (ab : G.Adj a b) (ac : G.Adj a c) : b=c := by
  by_contra ne
  obtain ⟨l,out,bl,cl⟩ := shares s b c sb sc nb nc
  have al : a≠l := fun eq => out (eq ▸ sa)
  exact h b a c l ne al ⟨ab.symm,ac,includeH cl,(includeH bl).symm⟩
theorem anchor_mate {G : SimpleGraph Vertex} (includeH : plane≤G) (h : FourFree G)
    (s : Bool) (b c : Vertex) (sb : shore s b) (sc : shore s c)
    (ab : G.Adj (anchor s) b) (ac : G.Adj (anchor s) c) : b=c := by
  have sa : shore s (anchor s) := by cases s <;> decide
  apply unique_other includeH h s (anchor s) b c sa sb sc _ _ ab ac
  · exact ab.ne.symm
  · exact ac.ne.symm

theorem degree_two_location {G : SimpleGraph Vertex} (includeH : plane≤G) (h : FourFree G)
    (s : Bool) (a b c : Vertex) (sa : shore s a) (sb : shore s b) (sc : shore s c)
    (bc : b≠c) (ab : G.Adj a b) (ac : G.Adj a c) : G.Adj (anchor s) a := by
  by_cases e : b=anchor s
  · simpa only [e] using ab.symm
  by_cases f : c=anchor s
  · simpa only [f] using ac.symm
  exact (bc (unique_other includeH h s a b c sa sb sc e f ab ac)).elim

end Dirty
end PEqualNP.Outside.L_meta_9743
