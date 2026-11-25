import Mathlib

namespace Clauses2846

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

def hits (c : Finset P × Finset L) (X : Finset P) (Y : Finset L) : Prop :=
  (∃ p ∈ c.1, p ∈ X) ∨ (∃ l ∈ c.2, l ∈ Y)

def Exact (N : P → Finset L) (Γ : Finset (Finset P × Finset L)) : Prop :=
  ∀ (X : Finset P) (Y : Finset L),
    (∀ c ∈ Γ, hits c X Y) ↔ ∃ p ∈ X, ∃ l ∈ Y, l ∈ N p

theorem forced {N : P → Finset L} {Γ : Finset (Finset P × Finset L)}
    (he : Exact N Γ) (A : Finset P) :
    ((Finset.univ.filter fun p => ¬ N p ⊆ A.biUnion N), A.biUnion N) ∈ Γ := by
  classical
  let U := A.biUnion N
  let X := Finset.univ.filter (fun p => N p ⊆ U)
  let Y := Finset.univ \ U
  have neg : ¬ (∀ c ∈ Γ, hits c X Y) := by
    intro all
    obtain ⟨p,hp,l,hl,h⟩ := (he X Y).mp all
    exact (Finset.mem_sdiff.mp hl).2 ((Finset.mem_filter.mp hp).2 h)
  obtain ⟨c,hc,miss⟩ : ∃ c ∈ Γ, ¬ hits c X Y := by
    by_contra! none
    exact neg none
  have cover (p : P) (l : L) (h : l ∈ N p) : p ∈ c.1 ∨ l ∈ c.2 := by
    have pos := (he {p} {l}).mpr ⟨p,by simp,l,by simp,h⟩ c hc
    rcases pos with ⟨v,hv,hvp⟩ | ⟨v,hv,hvl⟩
    · exact Or.inl (Finset.mem_singleton.mp hvp ▸ hv)
    · exact Or.inr (Finset.mem_singleton.mp hvl ▸ hv)
  have left (p : P) (h : p ∈ c.1) : ¬ N p ⊆ U := by
    intro sub
    exact miss (Or.inl ⟨p,h,Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub⟩⟩)
  have right (l : L) (h : l ∈ c.2) : l ∈ U := by
    by_contra hl
    exact miss (Or.inr ⟨l,h,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hl⟩⟩)
  have e₁ : c.1 = Finset.univ.filter (fun p => ¬ N p ⊆ U) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨left p,?_⟩
    intro nsub
    obtain ⟨l,hl,hu⟩ : ∃ l ∈ N p, l ∉ U := by
      by_contra! same
      exact nsub same
    exact (cover p l hl).resolve_right (fun h => hu (right l h))
  have e₂ : c.2 = U := by
    ext l
    refine ⟨right l,?_⟩
    intro hl
    obtain ⟨p,hp,he⟩ := Finset.mem_biUnion.mp hl
    exact (cover p l he).resolve_left (fun hh =>
      left p hh (fun _ hw => Finset.mem_biUnion.mpr ⟨p,hp,hw⟩))
  have eq : c = (Finset.univ.filter (fun p => ¬ N p ⊆ U), U) := Prod.ext e₁ e₂
  exact eq ▸ hc

theorem allUnions {N : P → Finset L} {Γ : Finset (Finset P × Finset L)}
    (he : Exact N Γ) :
    (Finset.univ.powerset.image (fun A : Finset P => A.biUnion N)).card ≤ Γ.card := by
  classical
  apply (Finset.card_le_card (t := Γ.image Prod.snd) ?_).trans Finset.card_image_le
  intro U hU
  obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hU
  exact Finset.mem_image.mpr ⟨_,forced he A,rfl⟩

theorem strict {N : P → Finset L} {Γ : Finset (Finset P × Finset L)}
    (he : Exact N Γ) (hne : (Finset.univ.biUnion N).Nonempty)
    (noUniversal : ∀ p, N p ≠ Finset.univ.biUnion N) :
    ((Finset.univ.image N).erase ∅).card + 2 ≤ Γ.card := by
  classical
  let F := (Finset.univ.image N).erase ∅
  let W := Finset.univ.biUnion N
  let K := Finset.univ.powerset.image (fun A : Finset P => A.biUnion N)
  have row (p : P) : N p ∈ K := by
    apply Finset.mem_image.mpr
    exact ⟨{p},by simp,by simp⟩
  have h0 : (∅ : Finset L) ∈ K := Finset.mem_image.mpr ⟨∅,by simp,by simp⟩
  have hW : W ∈ K := Finset.mem_image.mpr ⟨Finset.univ,by simp,rfl⟩
  have n0 : (∅ : Finset L) ∉ F := Finset.notMem_erase _ _
  have nW : W ∉ insert ∅ F := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact Finset.nonempty_iff_ne_empty.mp hne h
    · obtain ⟨p,_,eq⟩ := Finset.mem_image.mp (Finset.mem_erase.mp h).2
      exact noUniversal p eq
  have inc : insert W (insert ∅ F) ⊆ K := by
    intro U hU
    rcases Finset.mem_insert.mp hU with rfl | h
    · exact hW
    rcases Finset.mem_insert.mp h with rfl | h
    · exact h0
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp h).2
    exact row p
  have hc := Finset.card_le_card inc
  rw [Finset.card_insert_of_notMem nW,Finset.card_insert_of_notMem n0] at hc
  exact hc.trans (allUnions he)

end Clauses2846
