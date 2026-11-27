import PEqualNP.Defs
namespace Card7808

variable {n:Nat}
def prune (G:SimpleGraph (Fin n)) (u v:Fin n) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a≠u ∧ a≠v ∧ b≠u ∧ b≠v
  symm := by rintro a b ⟨ab,au,av,bu,bv⟩; exact ⟨ab.symm,bu,bv,au,av⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

instance (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) : DecidableRel (prune G u v).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ a≠u ∧ a≠v ∧ b≠u ∧ b≠v))

theorem prune_card (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (uv:G.Adj u v)
    (hu:(G.neighborFinset u).card=3) (hv:(G.neighborFinset v).card=3) :
    (prune G u v).edgeFinset.card + 5 ≤ G.edgeFinset.card := by
  classical
  let P := (prune G u v).edgeFinset
  let L := (G.neighborFinset u).image (fun i => s(u,i))
  let R := ((G.neighborFinset v).erase u).image (fun i => s(v,i))
  have inj (z:Fin n) : Function.Injective (fun i:Fin n => s(z,i)) := by
    intro i j h
    rcases Sym2.eq_iff.mp h with h|h <;> grind
  have cl : L.card=3 := (Finset.card_image_of_injective _ (inj u)).trans hu
  have cr : R.card=2 := by
    have e : u∈G.neighborFinset v := (G.mem_neighborFinset _ _).mpr uv.symm
    change (Finset.image _ _).card=2
    rw [Finset.card_image_of_injective _ (inj v),Finset.card_erase_of_mem e,hv]
  have pl : Disjoint P L := by
    apply Finset.disjoint_left.mpr
    intro e he hl
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
    have bad : (prune G u v).Adj u i := SimpleGraph.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
    exact bad.2.1 rfl
  have pr : Disjoint (P ∪ L) R := by
    apply Finset.disjoint_left.mpr
    intro e h hl
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
    rcases Finset.mem_union.mp h with h|h
    · have bad : (prune G u v).Adj v i := SimpleGraph.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp h)
      exact bad.2.2.1 rfl
    · obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp h
      rcases Sym2.eq_iff.mp eq with h|h
      · exact uv.ne h.1
      · exact (Finset.mem_erase.mp hi).1 h.1.symm
  have sub : (P∪L)∪R ⊆ G.edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with h|h
    · rcases Finset.mem_union.mp h with p|l
      · revert p
        induction e using Sym2.ind with
        | _ a b =>
          intro p
          have ab : (prune G u v).Adj a b := SimpleGraph.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp p)
          exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.mem_edgeSet.mpr ab.1)
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp l
        exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.mem_edgeSet.mpr ((G.mem_neighborFinset _ _).mp hi))
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.mem_edgeSet.mpr ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hi).2))
  have count := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint pr, Finset.card_union_of_disjoint pl,cl,cr] at count
  omega

end Card7808
