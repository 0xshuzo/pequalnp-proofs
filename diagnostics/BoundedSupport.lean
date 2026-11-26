import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.MaskedFactor
variable {P L : Type*} [DecidableEq P] [DecidableEq L]
def Edge (r : P → L → Prop) (A : Finset P) (B : Finset L) := ∃ p∈A,∃ l∈B,r p l
def Up (H : Finset P → Finset L → Prop) :=
  ∀ {A A' B B'}, A ⊆ A' → B ⊆ B' → H A B → H A' B'

theorem whole_restriction (r : P → L → Prop) (H K : Finset P → Finset L → Prop)
    (monoH : Up H) (monoK : Up K) (exactness : ∀ A B, Edge r A B ↔ H A B ∧ K A B)
    (X : Finset P) (Y : Finset L) (bad : ¬Edge r X Y) (accepted : K X Y)
    (A : Finset P) (B : Finset L) (left : ∀ p∈A,∀ l∈Y,¬r p l)
    (right : ∀ p∈X,∀ l∈B,¬r p l) :
    H A B ↔ Edge r A B := by
  constructor
  · intro yes
    have positive := (exactness (X∪A) (Y∪B)).2
      ⟨monoH Finset.subset_union_right Finset.subset_union_right yes,
       monoK Finset.subset_union_left Finset.subset_union_left accepted⟩
    obtain ⟨p,hp,l,hl,e⟩ := positive
    rcases Finset.mem_union.mp hp with a|a <;> rcases Finset.mem_union.mp hl with b|b
    · exact False.elim (bad ⟨p,a,l,b,e⟩)
    · exact False.elim (right p a l b e)
    · exact False.elim (left p a l b e)
    · exact ⟨p,a,l,b,e⟩
  · exact fun yes => ((exactness A B).1 yes).1

theorem crossing (r h k : P → L → Prop)
    (exactness : ∀ A B, Edge r A B ↔ Edge h A B ∧ Edge k A B)
    {p q : P} {l m : L} (a : h p l) (b : k q m) (red : ¬r p l) (blue : ¬r q m) :
    r p m ∨ r q l := by
  have on := (exactness {p,q} {l,m}).2
    ⟨⟨p,by simp,l,by simp,a⟩,⟨q,by simp,m,by simp,b⟩⟩
  obtain ⟨u,hu,v,hv,e⟩ := on
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
  · exact False.elim (red e)
  · exact Or.inl e
  · exact Or.inr e
  · exact False.elim (blue e)

theorem graph_factors_iff (r h k : P → L → Prop) :
    (∀ A B, Edge r A B ↔ Edge h A B ∧ Edge k A B) ↔
    (∀ p l, r p l → h p l ∧ k p l) ∧
      ∀ p l q m, h p l → k q m → ¬r p l → ¬r q m → r p m ∨ r q l := by
  constructor
  · intro good
    refine ⟨?_,fun p l q m a b red blue => crossing r h k good a b red blue⟩
    intro p l e
    have z := (good {p} {l}).1 ⟨p,by simp,l,by simp,e⟩
    simpa [Edge] using z
  · rintro ⟨included,cross⟩ A B
    constructor
    · rintro ⟨p,a,l,b,e⟩
      exact ⟨⟨p,a,l,b,(included p l e).1⟩,⟨p,a,l,b,(included p l e).2⟩⟩
    · rintro ⟨⟨p,a,l,b,e⟩,⟨q,i,m,j,f⟩⟩
      by_cases red : r p l
      · exact ⟨p,a,l,b,red⟩
      by_cases blue : r q m
      · exact ⟨q,i,m,j,blue⟩
      rcases cross p l q m e f red blue with pos|pos
      · exact ⟨p,a,m,j,pos⟩
      · exact ⟨q,i,l,b,pos⟩
end PEqualNP.Outside.L_meta_2585.MaskedFactor
