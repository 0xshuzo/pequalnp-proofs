import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9792.Colors

variable {X I E : Type}
def CNF (S : Fin k → Set X) (x : Set X) := ∀ c, ∃ v∈S c, v∈x
def cell (a b : X) : Set X := {a,b}
def compatible (a b : E → X) (N : I → Set X) (i j : I) :=
  ∀ e, ¬(a e∈N i ∧ b e∈N j)

theorem hitsPair {S : Set X} {a b : X} :
    (∃v∈S,v∈cell a b) ↔ a∈S ∨ b∈S := by
  constructor
  · rintro ⟨v,h,m⟩
    rcases (show v=a ∨ v=b by simpa [cell] using m) with rfl|rfl
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h|h)
    · exact ⟨a,h,by simp [cell]⟩
    · exact ⟨b,h,by simp [cell]⟩

theorem coloring (a b : E → X) (N : I → Set X) (k : Nat) :
    (∃ S : Fin k → Set X, (∀e,CNF S (cell (a e) (b e))) ∧ (∀i,¬CNF S (N i))) ↔
    ∃ c : I → Fin k, ∀i j,c i=c j → compatible a b N i j := by
  classical
  constructor
  · rintro ⟨S,edge,off⟩
    have witness : ∀i,∃j,∀v∈S j,v∉N i := by
      intro i
      have bad := off i
      unfold CNF at bad
      push_neg at bad
      exact bad
    choose c hc using witness
    refine ⟨c,?_⟩
    intro i j eq e pair
    rcases hitsPair.mp (edge e (c i)) with m|m
    · exact hc i _ m pair.1
    · exact hc j _ (eq ▸ m) pair.2
  · rintro ⟨c,h⟩
    let S : Fin k → Set X := fun t v=>∀i,c i=t → v∉N i
    refine ⟨S,?_,?_⟩
    · intro e t
      apply hitsPair.mpr
      by_cases av : a e∈S t
      · exact Or.inl av
      · change ¬∀i,c i=t → a e∉N i at av
        push_neg at av
        obtain ⟨i,ci,ai⟩:=av
        apply Or.inr
        intro j cj bj
        exact h i j (ci.trans cj.symm) e ⟨ai,bj⟩
    · intro i ok
      obtain ⟨v,m,n⟩:=ok (c i)
      exact m i rfl n

theorem allInputs {S : Fin k → Set X} {N : I → Set X} {F : Set X → Prop}
    (off : ∀i,¬CNF S (N i))
    (complete : ∀ x, ¬F x → ∃i,x⊆N i) :
    ∀ x, CNF S x → F x := by
  intro x on
  by_contra no
  obtain ⟨i,le⟩:=complete x no
  apply off i
  intro t
  obtain ⟨v,mem,yes⟩:=on t
  exact ⟨v,mem,le yes⟩

theorem cliqueLower {a b : E → X} {N : I → Set X} {k h : Nat}
    (S : Fin k → Set X) (on : ∀e,CNF S (cell (a e) (b e))) (off : ∀i,¬CNF S (N i))
    (ids : Fin h → I) (conflict : ∀i j,i≠j →
      ¬compatible a b N (ids i) (ids j) ∨ ¬compatible a b N (ids j) (ids i)) : h≤k := by
  classical
  obtain ⟨c,good⟩ := (coloring a b N k).1 ⟨S,on,off⟩
  have inj : Function.Injective (fun i=>c (ids i)) := by
    intro i j eq
    by_contra ne
    rcases conflict i j ne with bad|bad
    · exact bad (good _ _ eq)
    · exact bad (good _ _ eq.symm)
  simpa using Fintype.card_le_of_injective _ inj
end PEqualNP.Outside.L_meta_9792.Colors
