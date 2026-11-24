import Mathlib

namespace PlaneMandatory4467

variable {V : Type*} [DecidableEq V]

def mandatory (F : Finset (Finset V)) (forbid : Finset V) (p : V) : Prop :=
  ∀ A ∈ F, Disjoint A forbid → p ∈ A

def product (F G : Finset (Finset V)) : Finset (Finset V) :=
  F.biUnion fun A => G.image fun B => A ∪ B

lemma mandatory_choice (F G : Finset (Finset V)) (forbid : Finset V) (p : V) :
    mandatory (F ∪ G) forbid p ↔ mandatory F forbid p ∧ mandatory G forbid p := by
  simp [mandatory, Finset.mem_union, or_imp, forall_and]

lemma mandatory_product (F G : Finset (Finset V)) (forbid : Finset V) (p : V) :
    mandatory (product F G) forbid p ↔ mandatory F forbid p ∨ mandatory G forbid p := by
  classical
  constructor
  · intro h
    by_contra! bad
    obtain ⟨hf,hg⟩ := bad
    simp only [mandatory, not_forall] at hf hg
    obtain ⟨a,ha,da,pa⟩ := hf
    obtain ⟨b,hb,db,pb⟩ := hg
    have hab : a ∪ b ∈ product F G :=
      Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨b,hb,rfl⟩⟩
    have hp := h (a ∪ b) hab (Finset.disjoint_union_left.mpr ⟨da,db⟩)
    exact (Finset.mem_union.mp hp).elim pa pb
  · intro h x hx dx
    obtain ⟨a,ha,hab⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hab
    have hd := Finset.disjoint_union_left.mp dx
    exact h.elim (fun hf => Finset.mem_union_left _ (hf a ha hd.1))
      (fun hg => Finset.mem_union_right _ (hg b hb hd.2))

lemma mandatory_output {P L : Type*} [DecidableEq P] [DecidableEq L]
    (I : P → L → Prop) (F : Finset (Finset (P ⊕ L))) (S : Finset L)
    (cover : ∀ A ∈ F, ∀ p l, I p l → Sum.inl p ∈ A ∨ Sum.inr l ∈ A)
    (witness : ∃ C ∈ F, (∀ p, Sum.inl p ∈ C ↔ ∃ l ∈ S, I p l) ∧
      ∀ l, Sum.inr l ∈ C ↔ l ∉ S) (p : P) :
    mandatory F (S.image Sum.inr) (Sum.inl p) ↔ ∃ l ∈ S, I p l := by
  constructor
  · intro h
    obtain ⟨C,hC,hp,hl⟩ := witness
    apply (hp p).1
    apply h C hC
    rw [Finset.disjoint_left]
    intro t ht hs
    obtain ⟨l,hm,rfl⟩ := Finset.mem_image.mp hs
    exact (hl l).1 ht hm
  · rintro ⟨l,hl,hi⟩ A hA hd
    rcases cover A hA p l hi with hp|ht
    · exact hp
    · exact False.elim ((Finset.disjoint_left.mp hd) ht (Finset.mem_image.mpr ⟨l,hl,rfl⟩))

end PlaneMandatory4467
