import Mathlib
import PEqualNP.Outside.L_meta_1483
namespace Direct9836
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def pairs : List (Nat × Nat) := [(0, 24), (0, 26), (0, 36), (0, 39), (1, 25), (1, 27), (1, 37), (2, 21), (2, 26), (2, 28), (2, 38), (3, 21), (3, 22), (3, 27), (3, 29), (3, 39), (4, 22), (4, 23), (4, 28), (4, 30), (5, 23), (5, 24), (5, 29), (5, 31), (6, 21), (6, 24), (6, 25), (6, 30), (6, 32), (7, 22), (7, 25), (7, 26), (7, 31), (7, 33), (8, 23), (8, 26), (8, 27), (8, 32), (8, 34), (9, 24), (9, 27), (9, 28), (9, 33), (9, 35), (10, 25), (10, 28), (10, 29), (10, 34), (10, 36), (11, 26), (11, 29), (11, 30), (11, 35), (11, 37), (12, 27), (12, 30), (12, 31), (12, 36), (12, 38), (13, 28), (13, 31), (13, 32), (13, 37), (13, 39), (14, 29), (14, 32), (14, 33), (14, 38), (15, 30), (15, 33), (15, 34), (15, 39), (16, 21), (16, 31), (16, 34), (16, 35), (17, 22), (17, 32), (17, 35), (17, 36), (18, 21), (18, 23), (18, 33), (18, 36), (18, 37), (19, 22), (19, 24), (19, 34), (19, 37), (19, 38), (20, 23), (20, 25), (20, 35), (20, 38), (20, 39)]
def incidence : Array Nat := #[618559176704,137606725632,275215548416,550433193984,1354760192,2709520384,5421137920,10842275840,21684551680,43369103360,86738206720,173476413440,346952826880,693905653760,288299679744,576599359488,53689188352,107378376704,214758850560,429517701120,859035402240,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def rel (i j : Fin 40) : Prop := ((incidence[i.val]?).getD 0).testBit j.val = true
instance (i j : Fin 40) : Decidable (rel i j) := by unfold rel; infer_instance
theorem listed : ∀ i j : Fin 40, (i.val,j.val)∈pairs ↔ rel i j := by decide +kernel
def G : SimpleGraph (Fin 40) := SimpleGraph.fromRel rel
instance (i j : Fin 40) : Decidable (G.Adj i j) := by change Decidable (i ≠ j ∧ (rel i j ∨ rel j i)); infer_instance
theorem nature (i j : Fin 40) : G.Adj i j ↔ rel i j ∨ rel j i := by
  have h : ∀ i j, G.Adj i j ↔ rel i j ∨ rel j i := by decide +kernel
  exact h i j
def matchLeft (i : Fin 19) : Fin 40 := ![16,17,18,19,1,2,3,4,11,15,5,6,7,8,9,10,13,12,0] i
def matchRight (i : Fin 19) : Fin 40 := ⟨21+i.val,by omega⟩
theorem deg (v : Fin 40) : 2 ≤ (G.neighborSet v).ncard := by
  rw [SimpleGraph.ncard_neighborSet]
  have h : ∀ i : Fin 40, 2≤G.degree i := by decide +kernel
  exact h v
theorem cover (S : Finset (Fin 40)) (h : ∀ u v, G.Adj u v → 
    2≤(G.neighborSet u).ncard → 2≤(G.neighborSet v).ncard → u∈S ∨ v∈S) : 19≤S.card := by
  let f (i : Fin 19) := if matchLeft i∈S then matchLeft i else matchRight i
  have adj : ∀ i, G.Adj (matchLeft i) (matchRight i) := by decide +kernel
  have mem (i : Fin 19) : f i ∈ S := by
    have e := h _ _ (adj i) (deg _) (deg _)
    by_cases hi : matchLeft i∈S
    · simpa [f,hi] using hi
    · simpa [f,hi] using e.resolve_left hi
  have same : ∀ i j : Fin 19, (matchLeft i = matchLeft j ∨ matchRight i = matchRight j ∨
      matchLeft i = matchRight j ∨ matchRight i = matchLeft j) → i=j := by decide +kernel
  have inj : Set.InjOn f (Finset.univ : Finset (Fin 19)) := by
    intro i _ j _ h
    apply same
    unfold f at h
    split at h <;> split at h <;> tauto
  simpa using Finset.card_le_card_of_injOn f (fun i _ => mem i) inj
set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem lower (C : Circuit) (hm : Monotone2 C) (hc : ∀ x : Fin 40 → Bool,
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 40, (u.val,v.val)∈pairs ∧ x u=true ∧ x v=true) : 58≤C.size := by
  have hb := PEqualNP.Outside.L_meta_1483.step614 40 19 G C
  have nz : ∀ v, ∃ w,G.Adj v w := by decide +kernel
  have twins : ∀ v w : Fin 40,v≠w → ∃u, ¬(G.Adj v u ↔ G.Adj w u) := by decide +kernel
  have adj : ∀ v w : Fin 40,G.Adj v w → ∃ a b,
    G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a=b ∨ ¬G.Adj a b) := by decide +kernel
  let S : Finset (Fin 40) := Finset.univ.filter (fun i => 21≤i.val)
  have Scover : ∀u v,G.Adj u v → u∈S ∨ v∈S := by decide +kernel
  have h := hb nz (fun v w h _ _ _ => twins v w h) (fun v w h _ _ => adj v w h)
    ⟨S,fun u v h _ _ => Scover u v h,by decide +kernel⟩ (fun s hs => cover s hs) hm (by
      intro x
      rw [hc]
      constructor
      · rintro ⟨u,v,h,hu,hv⟩
        exact ⟨u,v,(nature u v).mpr (Or.inl ((listed _ _).mp h)),hu,hv⟩
      · rintro ⟨u,v,h,hu,hv⟩
        rcases (nature u v).mp h with h|h
        · exact ⟨u,v,(listed _ _).mpr h,hu,hv⟩
        · exact ⟨v,u,(listed _ _).mpr h,hv,hu⟩)
  omega
end Direct9836
