import Mathlib.Combinatorics.Hall.Basic
import PEqualNP.Defs

namespace BlockQuotaRouting
open Finset

theorem switches {A : Type} [Fintype A] [DecidableEq A]
    (E : Equiv.Perm (A × Bool)) :
    ∃ (left right : A → Bool) (p q : Equiv.Perm A),
      (∀ i, E (i,left i) = (p i,right (p i))) ∧
      (∀ i, E (i,!(left i)) = (q i,!(right (q i)))) := by
  classical
  let adj (i : A) := ({(E (i,false)).1, (E (i,true)).1} : Finset A)
  have hall (S : Finset A) : S.card ≤ (S.biUnion adj).card := by
    let U := (S ×ˢ (univ : Finset Bool)).map E.toEmbedding
    have incl : U ⊆ (S.biUnion adj) ×ˢ (univ : Finset Bool) := by
      intro y hy
      obtain ⟨⟨i,b⟩,hi,rfl⟩ := mem_map.mp hy
      refine mem_product.mpr ⟨mem_biUnion.mpr ⟨i,(mem_product.mp hi).1,?_⟩,mem_univ _⟩
      cases b <;> simp [adj]
    have h := card_le_card incl
    simp [U] at h
    omega
  obtain ⟨f,hfi,hfa⟩ := (all_card_le_biUnion_card_iff_exists_injective adj).mp hall
  let p := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi)
  have pick (i : A) : ∃ b : Bool, (E (i,b)).1 = p i := by
    have h := hfa i
    change f i ∈ ({(E (i,false)).1, (E (i,true)).1} : Finset A) at h
    simp only [mem_insert, mem_singleton] at h
    rcases h with h|h
    · exact ⟨false,h.symm⟩
    · exact ⟨true,h.symm⟩
  choose a ha using pick
  let b (j : A) := (E (p.symm j,a (p.symm j))).2
  have sel (i : A) : E (i,a i) = (p i,b (p i)) := by
    apply Prod.ext
    · exact ha i
    · simp [b]
  let f' (i : A) := (E (i,!(a i))).1
  have other (i : A) : E (i,!(a i)) = (f' i,!(b (f' i))) := by
    apply Prod.ext
    · rfl
    · have neq : (E (i,!(a i))).2 ≠ b (f' i) := by
        intro h
        have ee : E (i,!(a i)) = E (p.symm (f' i),a (p.symm (f' i))) := by
          rw [sel,p.apply_symm_apply]
          exact Prod.ext rfl h
        have hin := E.injective ee
        have hp := congrArg Prod.fst hin
        have hb := congrArg Prod.snd hin
        change i = p.symm (f' i) at hp
        change (!(a i)) = a (p.symm (f' i)) at hb
        rw [← hp] at hb
        cases a i <;> contradiction
      change (E (i,!(a i))).2 = !(b (f' i))
      cases h : b (f' i) <;> cases hv : (E (i,!(a i))).2 <;> simp_all
  have hinj : Function.Injective f' := by
    intro i k he
    have ee : E (i,!(a i)) = E (k,!(a k)) := by rw [other,other,he]
    exact congrArg Prod.fst (E.injective ee)
  exact ⟨a,b,p,Equiv.ofBijective f' (Finite.injective_iff_bijective.mp hinj),sel,other⟩

end BlockQuotaRouting
