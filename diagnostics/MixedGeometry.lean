import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18670.Mixed
abbrev V := Fin 26
def edges : List (V × V) := [(0,14),(0,16),(0,22),(1,15),(1,21),(1,25),(2,14),(2,20),(2,24),(2,25),(3,19),(3,23),(3,24),(4,18),(4,22),(4,23),(4,25),(5,17),(5,21),(5,22),(5,24),(6,16),(6,20),(6,21),(6,23),(7,15),(7,19),(7,20),(7,22),(8,14),(8,18),(8,19),(8,21),(10,16),(10,17),(10,19),(10,25),(11,15),(11,16),(11,18),(11,24),(12,14),(12,15),(12,17),(12,23),(13,0),(13,1),(13,3),(13,17),(13,18),(13,20)]
def masks : Array ℕ := #[4276224, 35684352, 51396608, 25690112, 46399488, 23199744, 11599872, 5799936, 2899968, 0, 34275328, 17137664, 8568832, 1441803, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def G : SimpleGraph V := SimpleGraph.fromRel (fun a b => ((masks[a.val]?).getD 0).testBit b.val=true)
instance : DecidableRel G.Adj := by unfold G SimpleGraph.fromRel; infer_instance
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem c4 : PEqualNP.TopForm.NoFourCycle G := by
  change ∀ p q r s : V, p≠r → q≠s → ¬(G.Adj p q ∧ G.Adj q r ∧ G.Adj r s ∧ G.Adj s p)
  decide +kernel
set_option maxRecDepth 12000 in
theorem flags : G.edgeFinset.card=51 := by decide +kernel
def m12 : Fin 12 → V × V := fun i => ([(0,16),(1,15),(2,25),(3,24),(4,22),(5,21),(6,23),(7,20),(8,19),(10,17),(11,18),(12,14)] : List (V×V)).getD i.val (0,0)
def m9 : Fin 9 → V × V := fun i => ([(2,24),(4,23),(5,22),(6,21),(7,15),(8,19),(10,25),(11,16),(12,14)] : List (V×V)).getD i.val (0,0)
def marks : Finset V := {0,1,3,17,18,20}
theorem cover (T : Finset V) (ht : ∀ u v, G.Adj u v → u∈T ∨ v∈T) : 13≤T.card := by
  classical
  have bank {n : ℕ} (m : Fin n → V×V) (ban : Finset V) (hb : ban⊆T)
      (he : ∀ i, G.Adj (m i).1 (m i).2)
      (hf : ∀ i, (m i).1∉ban ∧ (m i).2∉ban)
      (sep : ∀ i j, i≠j → (m i).1≠(m j).1 ∧ (m i).1≠(m j).2 ∧ (m i).2≠(m j).1 ∧ (m i).2≠(m j).2) :
      ban.card+n ≤ T.card := by
    let pick := fun i : Fin n => if (m i).1∈T then (m i).1 else (m i).2
    have inj : Function.Injective pick := by
      intro i j hij
      by_contra diff
      have h := sep i j diff
      dsimp only [pick] at hij
      split_ifs at hij <;> simp_all
    have dis : Disjoint ban (Finset.univ.image pick) := by
      apply Finset.disjoint_left.mpr
      rintro x xin xp
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xp
      have h := hf i
      dsimp only [pick] at xin
      split_ifs at xin <;> simp_all
    have sub : ban ∪ Finset.univ.image pick ⊆ T := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx|hx
      · exact hb hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      have h := ht _ _ (he i)
      dsimp only [pick]
      split <;> tauto
    have h := Finset.card_le_card sub
    simpa only [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ inj,
      Finset.card_univ,Fintype.card_fin] using h
  by_cases z : (13:V)∈T
  · have h := bank m12 {13} (by simpa) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    simpa using h
  · have near : ∀ u∈marks,G.Adj 13 u := by decide +kernel
    have h := bank m9 marks (fun u hu => (ht 13 u (near u hu)).resolve_left z)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have card : marks.card=6 := by decide +kernel
    omega
end PEqualNP.Outside.L_meta_18670.Mixed
