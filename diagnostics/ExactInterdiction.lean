import PEqualNP.Defs
namespace Dirty9739.Plane
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BicliqueBlockCost
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def masks : Array Nat := #[40969, 163878, 327756, 655512, 262448, 524897, 1218, 2437, 4874, 9748, 19496, 38992, 77984, 155968, 311936, 623872, 199168, 398337, 796674, 544772]
def direction (a b : Fin 40) : Bool := decide (20 ≤ b.val) && (masks[b.val-20]!).testBit a.val
def literal : List (Nat × Nat) := [(0, 20), (0, 25), (0, 27), (0, 37), (1, 21), (1, 26), (1, 28), (1, 38), (2, 21), (2, 22), (2, 27), (2, 29), (2, 39), (3, 20), (3, 22), (3, 23), (3, 28), (3, 30), (4, 23), (4, 24), (4, 29), (4, 31), (5, 21), (5, 24), (5, 25), (5, 30), (5, 32), (6, 22), (6, 25), (6, 26), (6, 31), (6, 33), (7, 23), (7, 26), (7, 27), (7, 32), (7, 34), (8, 24), (8, 27), (8, 28), (8, 33), (8, 35), (9, 25), (9, 28), (9, 29), (9, 34), (9, 36), (10, 26), (10, 29), (10, 30), (10, 35), (10, 37), (11, 27), (11, 30), (11, 31), (11, 36), (11, 38), (12, 28), (12, 31), (12, 32), (12, 37), (12, 39), (13, 20), (13, 29), (13, 32), (13, 33), (13, 38), (14, 30), (14, 33), (14, 34), (14, 39), (15, 20), (15, 21), (15, 31), (15, 34), (15, 35), (16, 22), (16, 32), (16, 35), (16, 36), (17, 21), (17, 23), (17, 33), (17, 36), (17, 37), (18, 22), (18, 24), (18, 34), (18, 37), (18, 38), (19, 23), (19, 25), (19, 35), (19, 38), (19, 39)]
theorem posted : ∀ a b : Fin 40, direction a b = true ↔ (a.val,b.val)∈literal := by decide +kernel

def G : SimpleGraph (Fin 40) where
  Adj i j := direction i j = true ∨ direction j i = true
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel G.Adj := fun i j =>
  inferInstanceAs (Decidable (direction i j = true ∨ direction j i = true))
abbrev P (i : Fin 20) : Fin 40 := Fin.castAdd 20 i
abbrev L : Fin 20 → Fin 40 := Fin.natAdd 20
def target (x : Fin 40 → Bool) : Prop :=
  ∃ u v : Fin 40, (u.val,v.val) ∈ literal ∧ x u=true ∧ x v=true
theorem graphTarget (x : Fin 40 → Bool) : target x ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by
  constructor
  · rintro ⟨i,j,ij,a,b⟩
    exact ⟨i,j,Or.inl ((posted i j).mpr ij),a,b⟩
  · rintro ⟨i,j,e,hi,hj⟩
    rcases e with e|e
    · exact ⟨i,j,(posted i j).mp e,hi,hj⟩
    · exact ⟨j,i,(posted j i).mp e,hj,hi⟩
set_option maxRecDepth 20000 in
theorem edgeCount : G.edgeSet.ncard = 95 := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem noFour : PEqualNP.TopForm.NoFourCycle G := by
  unfold PEqualNP.TopForm.NoFourCycle
  decide +kernel

theorem coverLower (S : Finset (Fin 40)) (covers : CoverPromise.IsVertexCover G S) : 20 ≤ S.card := by
  classical
  let pick := fun i : Fin 20 => if P i ∈ S then P i else L i
  have edges : ∀ i, G.Adj (P i) (L i) := by decide +kernel
  have pickMem (i) : pick i ∈ S := by
    unfold pick
    split_ifs with h
    · exact h
    · exact (covers _ _ (edges i)).resolve_left h
  have disjoint : ∀ i j : Fin 20, P i ≠ L j := by decide +kernel
  have inj : Function.Injective pick := by
    intro i j eq
    dsimp only [pick] at eq
    split_ifs at eq with hi hj hj
    · exact (show ∀ i j : Fin 20, P i = P j → i=j by decide +kernel) i j eq
    · exact False.elim (disjoint _ _ eq)
    · exact False.elim (disjoint _ _ eq.symm)
    · have facts : ∀ i j : Fin 20, L i = L j → i = j := by decide +kernel
      exact facts i j eq
  have bound := Finset.card_le_card (show Finset.univ.image pick ⊆ S from by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact pickMem j)
  simpa [Finset.card_image_of_injective _ inj] using bound



open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
abbrev V := Fin 40
abbrev Ix := Fin 4 × Fin 20
def matchingTable : Array (Fin 20) := #[17,18,2,0,11,4,5,6,7,8,9,16,19,12,10,1,15,13,14,3,0,1,9,8,4,10,6,3,13,14,15,7,12,18,19,11,16,17,2,5,7,8,19,3,9,5,11,12,4,16,6,10,17,13,14,0,2,1,18,15,5,6,7,10,3,1,2,14,8,9,17,18,11,0,13,15,12,16,4,19]
def pnt (x : Ix) : V := P x.2
def lin (x : Ix) : V := L (matchingTable[20*x.1.val+x.2.val]!)
def pairE (x : Ix) : Sym2 V := s(pnt x,lin x)
theorem matchingValid : ∀ x : Ix, G.Adj (pnt x) (lin x) := by decide +kernel
theorem matchingDistinct : ∀ x y : Ix, pairE x=pairE y → x=y := by decide +kernel
theorem endpoints : ∀ x y : Ix, x.1=y.1 →
    pnt x=pnt y ∨ pnt x=lin y ∨ lin x=pnt y ∨ lin x=lin y → x=y := by decide +kernel

theorem cover4 (U : Finset (Sym2 V)) (K : Finset V)
    (cover : ∀x : Ix, pairE x ∈ U ∨ pnt x ∈ K ∨ lin x ∈ K) :
    80 ≤ U.card + 4 * K.card := by
  classical
  let R := (Finset.univ : Finset Ix).filter (fun x => pairE x ∈ U)
  let H := (Finset.univ : Finset Ix).filter (fun x => pairE x ∉ U)
  have rb : R.card ≤ U.card := by
    have sub : R.image pairE ⊆ U := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    have le := Finset.card_le_card sub
    rwa [Finset.card_image_of_injective _ (fun _ _ h=>matchingDistinct _ _ h)] at le
  let pick (x : Ix) := (x.1,if pnt x∈K then pnt x else lin x)
  have inj : Function.Injective pick := by
    intro x y eq
    have tagEq : (pick x).1 = (pick y).1 := congrArg (fun t : Fin 4 × V => t.1) eq
    apply endpoints x y tagEq
    have hv := congrArg (fun t : Fin 4 × V => t.2) eq
    by_cases hx : pnt x∈K <;> by_cases hy : pnt y∈K <;> simp only [pick,hx,hy,ite_true,ite_false] at hv <;> tauto
  have hb : H.card ≤ 4*K.card := by
    have sub : H.image pick ⊆ (Finset.univ : Finset (Fin 4)).product K := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      have no := (Finset.mem_filter.mp hx).2
      obtain left|right := (cover x).resolve_left no
      · simp [pick,left]
      · by_cases h : pnt x ∈ K <;> simp [pick,h,right]
    have le := Finset.card_le_card sub
    simpa [Finset.card_image_of_injective _ inj] using le
  have whole : (Finset.univ : Finset Ix) ⊆ R ∪ H := by
    intro x _
    by_cases h : pairE x ∈ U <;> simp [R,H,h]
  have total := (Finset.card_le_card whole).trans (Finset.card_union_le R H)
  have ground : (Finset.univ : Finset Ix).card=80 := by decide
  omega

theorem remaining (U : Finset (Sym2 V)) (K : Finset V)
    (cover : (G.deleteEdges (U : Set (Sym2 V))).IsVertexCover (K : Set V)) :
    80 ≤ U.card + 4 * K.card := by
  apply cover4 U K
  intro x
  by_cases h : pairE x ∈ U
  · exact Or.inl h
  · right
    apply cover
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨matchingValid x,h⟩

theorem minCoverExists (H : SimpleGraph V) : ∃ K : Finset V, IsMinCover H K := by
  classical
  have he : ∃ k : Nat, ∃ S : Finset V, H.IsVertexCover (S : Set V) ∧ S.card=k := by
    exact ⟨_,Finset.univ,fun _ _ _=>Or.inl (by simp),rfl⟩
  obtain ⟨K,hK,eq⟩ := Nat.find_spec he
  refine ⟨K,hK,?_⟩
  intro S hs
  exact eq.trans_le (Nat.find_min' he ⟨S,hs,rfl⟩)

namespace Fifth
abbrev Ix := Fin 5 × Fin 20
def matchingTable : Array (Fin 20) := #[17,18,2,0,11,4,5,6,7,8,9,16,19,12,10,1,15,13,14,3,0,1,9,8,4,10,6,3,13,14,15,7,12,18,19,11,16,17,2,5,7,8,19,3,9,5,11,12,4,16,6,10,17,13,14,0,2,1,18,15,5,6,7,10,3,1,2,14,8,9,17,18,11,0,13,15,12,16,4,19,4,0,1,2,6,12,13,7,15,5,10,11,8,9,16,14,19,3,17,18]
def pnt (x : Ix) : V := P x.2
def lin (x : Ix) : V := L (matchingTable[20*x.1.val+x.2.val]!)
def pairE (x : Ix) : Sym2 V := s(pnt x,lin x)
def W : Finset Ix := Finset.univ.filter (fun x => G.Adj (pnt x) (lin x))
theorem matchingDistinct : ∀ x y : Ix, pairE x=pairE y → x=y := by decide +kernel
theorem endpoints : ∀ x y : Ix, x.1=y.1 →
    pnt x=pnt y ∨ pnt x=lin y ∨ lin x=pnt y ∨ lin x=lin y → x=y := by decide +kernel

theorem cover5 (U : Finset (Sym2 V)) (K : Finset V)
    (cover : ∀x : Ix, x∈W → pairE x ∈ U ∨ pnt x ∈ K ∨ lin x ∈ K) :
    95 ≤ U.card + 5 * K.card := by
  classical
  let R := W.filter (fun x => pairE x ∈ U)
  let H := W.filter (fun x => pairE x ∉ U)
  have rb : R.card ≤ U.card := by
    have sub : R.image pairE ⊆ U := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    have le := Finset.card_le_card sub
    rwa [Finset.card_image_of_injective _ (fun _ _ h=>matchingDistinct _ _ h)] at le
  let pick (x : Ix) := (x.1,if pnt x∈K then pnt x else lin x)
  have inj : Function.Injective pick := by
    intro x y eq
    have tagEq : (pick x).1 = (pick y).1 := congrArg (fun t : Fin 5 × V => t.1) eq
    apply endpoints x y tagEq
    have hv := congrArg (fun t : Fin 5 × V => t.2) eq
    by_cases hx : pnt x∈K <;> by_cases hy : pnt y∈K <;> simp only [pick,hx,hy,ite_true,ite_false] at hv <;> tauto
  have hb : H.card ≤ 5*K.card := by
    have sub : H.image pick ⊆ (Finset.univ : Finset (Fin 5)).product K := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      have no := (Finset.mem_filter.mp hx).2
      obtain left|right := (cover x (Finset.mem_filter.mp hx).1).resolve_left no
      · simp [pick,left]
      · by_cases h : pnt x ∈ K <;> simp [pick,h,right]
    have le := Finset.card_le_card sub
    simpa [Finset.card_image_of_injective _ inj] using le
  have whole : W ⊆ R ∪ H := by
    intro x wx
    by_cases h : pairE x ∈ U <;> simp [R,H,h,wx]
  have total := (Finset.card_le_card whole).trans (Finset.card_union_le R H)
  have ground : W.card=95 := by decide
  omega

theorem remaining (U : Finset (Sym2 V)) (K : Finset V)
    (cover : (G.deleteEdges (U : Set (Sym2 V))).IsVertexCover (K : Set V)) :
    95 ≤ U.card + 5 * K.card := by
  apply cover5 U K
  intro x wx
  by_cases h : pairE x ∈ U
  · exact Or.inl h
  · right
    apply cover
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨(Finset.mem_filter.mp wx).2,h⟩

end Fifth
end Dirty9739.Plane
namespace Dirty9739.Plane
def price (k : Nat) := max (95-5*k) (80-4*k)
def order : List V := [2,3,5,6,7,8,9,10,11,12,13,15,17,18,19,0,1,4,14,16]
def paidSet (k : Nat) : Finset V := (order.take k).toFinset
def cutEdges (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v∈S, v∉e)
theorem cutCover (S : Finset V) : (G.deleteEdges (↑(cutEdges S))).IsVertexCover (S : Set V) := by
  intro u v adj
  rw [SimpleGraph.deleteEdges_adj] at adj
  by_contra! miss
  apply adj.2
  apply Finset.mem_coe.mpr
  apply Finset.mem_filter.mpr
  refine ⟨SimpleGraph.mem_edgeFinset.mpr adj.1,?_⟩
  intro a ha h
  rcases Sym2.mem_iff.mp h with e|e
  · exact miss.1 (e ▸ ha)
  · exact miss.2 (e ▸ ha)
theorem attainableData : ∀ k : Fin 21, (paidSet k.val).card=k.val ∧
    (cutEdges (paidSet k.val)).card=price k.val := by decide +kernel

theorem exactSpectrum (k : Fin 21) :
    (∀ (K : Finset V) (U : Finset (Sym2 V)), K.card≤k.val →
     (G.deleteEdges (↑U)).IsVertexCover (K : Set V) → price k.val≤U.card) ∧
    ∃ (K : Finset V) (U : Finset (Sym2 V)), K.card=k.val ∧ U.card=price k.val ∧
      (G.deleteEdges (↑U)).IsVertexCover (K : Set V) := by
  constructor
  · intro K U kd cover
    have h := remaining U K cover
    have g := Fifth.remaining U K cover
    unfold price
    apply max_le <;> omega
  · exact ⟨paidSet k.val,cutEdges (paidSet k.val),(attainableData k).1,(attainableData k).2,cutCover _⟩
end Dirty9739.Plane
