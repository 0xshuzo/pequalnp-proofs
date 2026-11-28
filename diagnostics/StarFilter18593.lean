import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18593.Star
open Finset PEqualNP.TopForm
variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def Blocks (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n)) : Prop :=
  ∀ w∈W,∀ x∈A,∀ y∈B,G.Adj w x ∨ G.Adj w y ∨ G.Adj x y

theorem swap {W A B : Finset (Fin n)} (h : Blocks G W A B) : Blocks G W B A := by
  intro w hw x hx y hy
  rcases h w hw y hy x hx with v|v|v
  · exact Or.inr (Or.inl v)
  · exact Or.inl v
  · exact Or.inr (Or.inr v.symm)

theorem orientation (q : Nat) (hq : 3≤q) (a b : Fin q → Fin n)
    (ai : Function.Injective a) (bi : Function.Injective b)
    (four : NoFourCycle G) (A B W : Finset (Fin n)) (sep : ∀ w∈W,∀ i,¬G.Adj w (a i))
    (owner : ∀ i, a i∈A ∨ b i∈A) (side : ∀ i, b i∈B) (safe : Blocks G W A B) :
    W.card≤1 := by
  classical
  let E := univ.filter (fun i : Fin q => ∃ w∈W,¬G.Adj w (b i))
  have parent (i : Fin q) (ei : i∈E) : a i∈A := by
    obtain ⟨w,hw,no⟩ := (mem_filter.mp ei).2
    rcases owner i with h|h
    · exact h
    · rcases safe w hw _ h _ (side i) with bad|bad|loop
      · exact False.elim (no bad)
      · exact False.elim (no bad)
      · exact False.elim (G.loopless _ loop)
  have cross (i j : Fin q) (hi : i∈E) (hj : j∈E) : G.Adj (a i) (b j) := by
    obtain ⟨w,hw,no⟩ := (mem_filter.mp hj).2
    rcases safe w hw _ (parent i hi) _ (side j) with bad|bad|h
    · exact False.elim (sep w hw i bad)
    · exact False.elim (no bad)
    · exact h
  have exceptional : E.card≤1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra ne
    have h := four (a i) (a j) (fun eq => ne (ai eq))
    exact ne (bi (card_le_one.mp h _ (mem_filter.mpr ⟨mem_univ _,cross i i hi hi,cross j i hj hi⟩)
      _ (mem_filter.mpr ⟨mem_univ _,cross i j hi hj,cross j j hj hj⟩)))
  have cardAll := card_sdiff_add_card_eq_card (subset_univ E)
  simp only [card_univ,Fintype.card_fin] at cardAll
  have plenty : 1 < (univ \ E).card := by omega
  obtain ⟨i,hi,j,hj,ne⟩ := one_lt_card.mp plenty
  have common (k : Fin q) (hk : k∈univ \ E) {w : Fin n} (hw : w∈W) : G.Adj w (b k) := by
    by_contra h
    exact (mem_sdiff.mp hk).2 (mem_filter.mpr ⟨mem_univ _,w,hw,h⟩)
  apply card_le_one.mpr
  intro u hu v hv
  by_contra uv
  exact ne (bi (card_le_one.mp (four u v uv) _ (mem_filter.mpr ⟨mem_univ _,common i hi hu,common i hi hv⟩)
    _ (mem_filter.mpr ⟨mem_univ _,common j hj hu,common j hj hv⟩)))

theorem per_shore {q : Nat} (hq : 3≤q) (a b : Fin q → Fin n)
    (ai : Function.Injective a) (bi : Function.Injective b)
    (four : NoFourCycle G) (A B W : Finset (Fin n))
    (same : ∀ i j,¬G.Adj (a i) (a j)) (sep : ∀ w∈W,∀ i,¬G.Adj w (a i))
    (hA : ∀ i, a i∈A ∨ b i∈A) (hB : ∀ i, a i∈B ∨ b i∈B) (safe : Blocks G W A B) :
    W.card≤1 := by
  classical
  rcases W.eq_empty_or_nonempty with rfl|⟨w,hw⟩
  · simp
  by_cases f : ∀ i,b i∈B
  · exact orientation q hq a b ai bi four A B W sep hA f safe
  · obtain ⟨i,ni⟩ := not_forall.mp f
    have hin := (hB i).resolve_right ni
    have fb (j : Fin q) : b j∈A := by
      rcases hA j with h|h
      · rcases safe w hw _ h _ hin with e|e|e
        · exact False.elim (sep w hw j e)
        · exact False.elim (sep w hw i e)
        · exact False.elim (same j i e)
      · exact h
    exact orientation q hq a b ai bi four B A W sep hB fb (swap safe)
end PEqualNP.Outside.L_meta_18593.Star
