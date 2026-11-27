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
instance (a b : Vertex) : Decidable (inc a b) := by unfold inc; infer_instance
instance punctureAdj : DecidableRel plane.Adj := fun a b => inferInstanceAs (Decidable (inc a b ∨ inc b a))
def anchor (s : Bool) : Vertex := if s then 0 else 21
def shore (s : Bool) (a : Vertex) := if s then a.val<21 else 21≤a.val
instance (s : Bool) (a : Vertex) : Decidable (shore s a) := by unfold shore; split <;> infer_instance
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem shares : ∀ (s : Bool) (a b : Vertex), shore s a → shore s b → a≠anchor s → b≠anchor s →
    ∃ l : Vertex, ¬shore s l ∧ plane.Adj a l ∧ plane.Adj b l := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
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

def side (a : Vertex) := decide (a.val<21)
def hole (a b : Vertex) := (a=0 ∧ b=21) ∨ (b=0 ∧ a=21)
instance (a b : Vertex) : Decidable (hole a b) := by unfold hole; infer_instance
def crossN (full : Bool) (a : Vertex) : Finset Vertex :=
  Finset.univ.filter (fun b => plane.Adj a b ∨ (full=true ∧ hole a b))
theorem in_side : ∀ a : Vertex, shore (side a) a := by decide +kernel
theorem cross_dirs : ∀ a b : Vertex, ¬shore (side a) b → (a.val<21 ∧ 21≤b.val) ∨ (b.val<21 ∧ 21≤a.val) := by decide +kernel
theorem cross_legal {G : SimpleGraph Vertex} (sub : plane≤G) (ok : FourFree G) {a b : Vertex}
    (h : G.Adj a b) (opp : ¬shore (side a) b) : plane.Adj a b ∨ hole a b := by
  rcases cross_dirs a b opp with ⟨pa,lb⟩|⟨pb,la⟩
  · rcases cross_only sub ok a b pa lb h with e|e
    · exact Or.inl (Or.inl e)
    · exact Or.inr (Or.inl e)
  · rcases cross_only sub ok b a pb la h.symm with e|e
    · exact Or.inl (Or.inr e)
    · exact Or.inr (Or.inr e)
theorem hole_on {G : SimpleGraph Vertex} {a b : Vertex} (h : hole a b) (ab : G.Adj a b) : G.Adj 0 21 := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ab
  · exact ab.symm
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem full_shares : ∀ (s : Bool) (b c : Vertex), shore s b → shore s c →
    ∃ l : Vertex, ¬shore s l ∧ (plane.Adj b l ∨ hole b l) ∧ (plane.Adj c l ∨ hole c l) := by decide +kernel
theorem crosses5 : ∀ a : Vertex,(crossN true a).card≤5 := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem cross208 : (∑ a : Vertex,(crossN false a).card)=208 := by decide +kernel

theorem full_degree {G : SimpleGraph Vertex} [DecidableRel G.Adj] (sub : plane≤G) (ok : FourFree G)
    (filled : G.Adj 0 21) (a : Vertex) : G.degree a≤6 := by
  let s := side a
  let S := Finset.univ.filter (fun b => shore s b ∧ G.Adj a b)
  have hS : S.card≤1 := by
    refine Finset.card_le_one.mpr ?_
    intro b hb c hc
    obtain ⟨sb,ab⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨sc,ac⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨l,nl,bl,cl⟩ := full_shares s b c sb sc
    have live (x y : Vertex) : plane.Adj x y ∨ hole x y → G.Adj x y := by
      rintro (e|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
      · exact sub e
      · exact filled
      · exact filled.symm
    by_contra bc
    exact ok b a c l bc (fun e => nl (e ▸ in_side a)) ⟨ab.symm,ac,live _ _ cl,(live _ _ bl).symm⟩
  have subN : G.neighborFinset a ⊆ crossN true a ∪ S := by
    intro b hb
    have ab := (G.mem_neighborFinset a b).mp hb
    by_cases sb : shore s b
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,sb,ab⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using cross_legal sub ok ab sb⟩)
  have hc := (Finset.card_le_card subN).trans (Finset.card_union_le ..)
  rw [G.card_neighborFinset_eq_degree] at hc
  have := crosses5 a; omega

theorem choose_mate {G : SimpleGraph Vertex} (sub : plane≤G) (ok : FourFree G) (s : Bool) :
    ∃ m : Vertex,∀ a,shore s a → G.Adj (anchor s) a → a=m := by
  classical
  by_cases ex : ∃ a,shore s a ∧ G.Adj (anchor s) a
  · obtain ⟨m,hs,hm⟩ := ex
    exact ⟨m,fun a ha h => anchor_mate sub ok s a m ha hs h hm⟩
  · exact ⟨0,fun a hs hm => (ex ⟨a,hs,hm⟩).elim⟩

theorem empty_degree {G : SimpleGraph Vertex} [DecidableRel G.Adj] (sub : plane≤G) (ok : FourFree G)
    (missing : ¬G.Adj 0 21) (p l : Vertex)
    (point : ∀ a,shore true a → G.Adj (anchor true) a → a=p)
    (line : ∀ a,shore false a → G.Adj (anchor false) a → a=l)
    (a : Vertex) : G.degree a≤ (crossN false a).card+1+(if a=p then 1 else 0)+(if a=l then 1 else 0) := by
  let s := side a
  let S := Finset.univ.filter (fun b => shore s b ∧ b≠anchor s ∧ G.Adj a b)
  have hS : S.card≤1 := by
    refine Finset.card_le_one.mpr ?_
    intro b hb c hc
    obtain ⟨sb,nb,ab⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨sc,nc,ac⟩ := (Finset.mem_filter.mp hc).2
    exact unique_other sub ok s a b c (in_side a) sb sc nb nc ab ac
  let e : Finset Vertex := if G.Adj a (anchor s) then {anchor s} else ∅
  have hE : e.card≤(if a=p then 1 else 0)+(if a=l then 1 else 0) := by
    by_cases ha : G.Adj a (anchor s)
    · have eq : a=p ∨ a=l := by
        cases hs : side a with
        | true => exact Or.inl (point a (hs ▸ in_side a) (by simpa only [s,hs] using ha.symm))
        | false => exact Or.inr (line a (hs ▸ in_side a) (by simpa only [s,hs] using ha.symm))
      rcases eq with eq|eq <;> simp [e,ha,eq]
    · simp [e,ha]
  have subN : G.neighborFinset a ⊆ (crossN false a ∪ S) ∪ e := by
    intro b hb
    have ab := (G.mem_neighborFinset a b).mp hb
    by_cases sb : shore s b
    · by_cases ba : b=anchor s
      · subst b; exact Finset.mem_union_right _ (by simp [e,ab])
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,sb,ba,ab⟩))
    · have q := (cross_legal sub ok ab sb).resolve_right (fun hh => missing (hole_on hh ab))
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl q⟩))
  have hc := (Finset.card_le_card subN).trans (Finset.card_union_le ..)
  rw [G.card_neighborFinset_eq_degree] at hc
  have hu := Finset.card_union_le (crossN false a) S
  omega

theorem greatest_card (G : SimpleGraph Vertex) [DecidableRel G.Adj] (sub : plane≤G) (ok : FourFree G) :
    G.edgeFinset.card≤126 := by
  have count := G.sum_degrees_eq_twice_card_edges
  by_cases e : G.Adj 0 21
  · have h := Finset.sum_le_sum (s:=(Finset.univ : Finset Vertex)) (fun a _ => full_degree sub ok e a)
    simp at h
    omega
  · obtain ⟨p,hp⟩ := choose_mate sub ok true
    obtain ⟨l,hl⟩ := choose_mate sub ok false
    have h := Finset.sum_le_sum (s:=(Finset.univ : Finset Vertex)) (fun a _ => empty_degree sub ok e p l hp hl a)
    simp [Finset.sum_add_distrib,cross208] at h
    omega

end Dirty
end PEqualNP.Outside.L_meta_9743
