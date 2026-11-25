import Mathlib
import PEqualNP.Outside.L_meta_1483
namespace Direct9774
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def pairs : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def rel (i j : Fin 14) : Prop := (i.val,j.val)∈pairs
instance (i j : Fin 14) : Decidable (rel i j) := by unfold rel; infer_instance
def G : SimpleGraph (Fin 14) := SimpleGraph.fromRel rel
instance (i j : Fin 14) : Decidable (G.Adj i j) := by change Decidable (i ≠ j ∧ (rel i j ∨ rel j i)); infer_instance
theorem nature (i j : Fin 14) : G.Adj i j ↔ rel i j ∨ rel j i := by
  have h : ∀ i j, G.Adj i j ↔ rel i j ∨ rel j i := by decide
  exact h i j
def matchLeft (i : Fin 7) : Fin 14 := ⟨i.val,by omega⟩
def matchRight (i : Fin 7) : Fin 14 := ![8,7,12,11,13,10,9] i
theorem deg (v : Fin 14) : 2 ≤ (G.neighborSet v).ncard := by
  rw [SimpleGraph.ncard_neighborSet]
  have h : ∀ i : Fin 14, 2≤G.degree i := by decide
  exact h v
theorem cover (S : Finset (Fin 14)) (h : ∀ u v, G.Adj u v → 
    2≤(G.neighborSet u).ncard → 2≤(G.neighborSet v).ncard → u∈S ∨ v∈S) : 7≤S.card := by
  let f (i : Fin 7) := if matchLeft i∈S then matchLeft i else matchRight i
  have adj : ∀ i, G.Adj (matchLeft i) (matchRight i) := by decide
  have mem (i : Fin 7) : f i ∈ S := by
    have e := h _ _ (adj i) (deg _) (deg _)
    by_cases hi : matchLeft i∈S
    · simpa [f,hi] using hi
    · simpa [f,hi] using e.resolve_left hi
  have same : ∀ i j : Fin 7, (matchLeft i = matchLeft j ∨ matchRight i = matchRight j ∨
      matchLeft i = matchRight j ∨ matchRight i = matchLeft j) → i=j := by decide
  have inj : Set.InjOn f (Finset.univ : Finset (Fin 7)) := by
    intro i _ j _ h
    apply same
    unfold f at h
    split at h <;> split at h <;> tauto
  simpa using Finset.card_le_card_of_injOn f (fun i _ => mem i) inj
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 1000000 in
theorem lower (C : Circuit) (hm : Monotone2 C) (hc : ∀ x : Fin 14 → Bool,
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val,v.val)∈pairs ∧ x u=true ∧ x v=true) : 20≤C.size := by
  have hb := PEqualNP.Outside.L_meta_1483.step614 14 7 G C
  have nz : ∀ v, ∃ w,G.Adj v w := by decide
  have twins : ∀ v w : Fin 14,v≠w → ∃u, ¬(G.Adj v u ↔ G.Adj w u) := by decide
  have adj : ∀ v w : Fin 14,G.Adj v w → ∃ a b,
    G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a=b ∨ ¬G.Adj a b) := by decide
  let S : Finset (Fin 14) := Finset.univ.filter (fun i => i.val<7)
  have Scover : ∀u v,G.Adj u v → u∈S ∨ v∈S := by decide
  have h := hb nz (fun v w h _ _ _ => twins v w h) (fun v w h _ _ => adj v w h)
    ⟨S,fun u v h _ _ => Scover u v h,by decide⟩ (fun s hs => cover s hs) hm (by
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
end Direct9774
