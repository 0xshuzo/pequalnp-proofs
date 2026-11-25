import Mathlib
import PEqualNP.Outside.L_meta_1483
namespace Direct9742
set_option maxHeartbeats 0
set_option maxRecDepth 16384
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def pairs : List (Nat × Nat) := [(0, 17), (0, 23), (0, 25), (1, 13), (1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 13), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 13), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)]
def rel (i j : Fin 26) : Prop := (i.val,j.val)∈pairs
instance (i j : Fin 26) : Decidable (rel i j) := by unfold rel; infer_instance
def G : SimpleGraph (Fin 26) := SimpleGraph.fromRel rel
instance (i j : Fin 26) : Decidable (G.Adj i j) := by change Decidable (i ≠ j ∧ (rel i j ∨ rel j i)); infer_instance
theorem nature (i j : Fin 26) : G.Adj i j ↔ rel i j ∨ rel j i := by
  have h : ∀ i j, G.Adj i j ↔ rel i j ∨ rel j i := by decide +kernel
  exact h i j
def matchLeft (i : Fin 13) : Fin 26 := ![9,1,2,3,4,5,6,8,11,12,10,7,0] i
def matchRight (i : Fin 13) : Fin 26 := Fin.natAdd 13 i
theorem deg (v : Fin 26) : 2 ≤ (G.neighborSet v).ncard := by
  rw [SimpleGraph.ncard_neighborSet]
  have h : ∀ i : Fin 26, 2≤G.degree i := by decide +kernel
  exact h v
theorem cover (S : Finset (Fin 26)) (h : ∀ u v, G.Adj u v → 
    2≤(G.neighborSet u).ncard → 2≤(G.neighborSet v).ncard → u∈S ∨ v∈S) : 13≤S.card := by
  let f (i : Fin 13) := if matchLeft i∈S then matchLeft i else matchRight i
  have adj : ∀ i, G.Adj (matchLeft i) (matchRight i) := by decide +kernel
  have mem (i : Fin 13) : f i ∈ S := by
    have e := h _ _ (adj i) (deg _) (deg _)
    by_cases hi : matchLeft i∈S
    · simpa [f,hi] using hi
    · simpa [f,hi] using e.resolve_left hi
  have same : ∀ i j : Fin 13, (matchLeft i = matchLeft j ∨ matchRight i = matchRight j ∨
      matchLeft i = matchRight j ∨ matchRight i = matchLeft j) → i=j := by decide +kernel
  have inj : Set.InjOn f (Finset.univ : Finset (Fin 13)) := by
    intro i _ j _ h
    apply same
    unfold f at h
    split at h <;> split at h <;> tauto
  simpa using Finset.card_le_card_of_injOn f (fun i _ => mem i) inj
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 1000000 in
theorem lower (C : Circuit) (hm : Monotone2 C) (hc : ∀ x : Fin 26 → Bool,
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val,v.val)∈pairs ∧ x u=true ∧ x v=true) : 38≤C.size := by
  have hb := PEqualNP.Outside.L_meta_1483.step614 26 13 G C
  have nz : ∀ v, ∃ w,G.Adj v w := by decide +kernel
  have twins : ∀ v w : Fin 26,v≠w → ∃u, ¬(G.Adj v u ↔ G.Adj w u) := by decide +kernel
  have adj : ∀ v w : Fin 26,G.Adj v w → ∃ a b,
    G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a=b ∨ ¬G.Adj a b) := by decide +kernel
  let S : Finset (Fin 26) := Finset.univ.filter (fun i => i.val<13)
  have Scover : ∀u v,G.Adj u v → u∈S ∨ v∈S := by decide +kernel
  have h := hb nz (fun v w h _ _ _ => twins v w h) (fun v w h _ _ => adj v w h)
    ⟨S,fun u v h _ _ => Scover u v h,by decide +kernel⟩ (fun s hs => cover s hs) hm (by
      intro x
      rw [hc]
      constructor
      · rintro ⟨u,v,h,hu,hv⟩
        exact ⟨u,v,(nature u v).mpr (Or.inl h),hu,hv⟩
      · rintro ⟨u,v,h,hu,hv⟩
        rcases (nature u v).mp h with h|h
        · exact ⟨u,v,h,hu,hv⟩
        · exact ⟨v,u,h,hv,hu⟩)
  omega
end Direct9742
