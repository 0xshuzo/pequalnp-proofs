import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18593.Ledger
open Finset
variable {n : Nat}

def Meets (A : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop := ∃ v ∈ A,v∈e

open Classical in
noncomputable def hit (U : Finset (Sym2 (Fin n))) (A : Finset (Fin n)) :=
  U.filter (Meets A)

theorem hit_mem {U : Finset (Sym2 (Fin n))} {A : Finset (Fin n)} {e} :
    e∈hit U A ↔ e∈U ∧ Meets A e := by classical simp [hit]

theorem budget (U : Finset (Sym2 (Fin n))) (d : Nat)
    (res : ∀ A : Finset (Fin n), (∀ e∈U,Meets A e) → d < A.card+U.card)
    (A : Finset (Fin n)) : d + (hit U A).card < 2*U.card + A.card := by
  classical
  have existsEnd (e : Sym2 (Fin n)) : ∃ v,v∈e := by
    induction e using Sym2.ind with
    | h a b => exact ⟨a,by simp⟩
  let f (e : Sym2 (Fin n)) := (existsEnd e).choose
  let R := U \ hit U A
  have bound := res (A ∪ R.image f) (by
    intro e he
    by_cases h : e∈hit U A
    · obtain ⟨v,hv,ev⟩ := (hit_mem.mp h).2
      exact ⟨v,mem_union_left _ hv,ev⟩
    · exact ⟨f e,mem_union_right _ (mem_image_of_mem _ (mem_sdiff.mpr ⟨he,h⟩)),(existsEnd e).choose_spec⟩)
  have su : hit U A ⊆ U := fun _ h => (hit_mem.mp h).1
  have add : R.card + (hit U A).card=U.card := card_sdiff_add_card_eq_card su
  have uni := card_union_le A (R.image f)
  have im : (R.image f).card ≤ R.card := card_image_le
  omega

theorem boundary (U : Finset (Sym2 (Fin n))) (d : Nat)
    (res : ∀ A : Finset (Fin n), (∀ e∈U,Meets A e) → d < A.card+U.card)
    (tight : 2*U.card ≤ d+1) :
    ∀ e∈U,∀ f∈U,e≠f → ¬∃ v : Fin n,v∈e ∧ v∈f := by
  classical
  rintro e he f hf ne ⟨v,ve,vf⟩
  have a := budget U d res {v}
  simp only [card_singleton] at a
  have two : 1 < (hit U {v}).card := one_lt_card.mpr
    ⟨e,hit_mem.mpr ⟨he,v,mem_singleton_self _,ve⟩,f,hit_mem.mpr ⟨hf,v,mem_singleton_self _,vf⟩,ne⟩
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
theorem three (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j2 : 2≤(junk G C).card) (o1 : 1≤(orN G C \ lam G C).card)
    (k3 : 3≤(centreless G C).card+(orN G C \ lam G C).card)
    (d5 : 5≤2*(centreless G C).card+(junk G C).card+(orN G C \ lam G C).card)
    (u3 : (Ustar G C).card=3)
    (res : ∀ A : Finset (Fin n), (∀ e∈Ustar G C,Meets A e) →
      2*(centreless G C).card+(junk G C).card+(orN G C \ lam G C).card < A.card+(Ustar G C).card) :
    (junk G C).card=2 ∧ (centreless G C).card=0 ∧ (orN G C \ lam G C).card=3 ∧
    ∀ e∈Ustar G C,∀ f∈Ustar G C,e≠f → ¬∃ v : Fin n,v∈e ∧ v∈f := by
  have h := budget _ _ res ∅
  simp only [card_empty,Nat.add_zero,u3] at h
  refine ⟨by omega,by omega,by omega,boundary _ _ res (by omega)⟩
end PEqualNP.Outside.L_meta_18593.Ledger
