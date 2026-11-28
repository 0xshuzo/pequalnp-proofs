import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9829.PencilPorts
variable {P L I J : Type}
def hit {T : Type} (S X : Set T) := ∃ t ∈ S, t ∈ X
def code {T K : Type} (A : K → Set T) (X : Set T) : K → Prop := fun i => hit (A i) X

theorem rising {T K : Type} (A : K → Set T) (X : Set T) (p : T)
    (ne : code A X ≠ code A (insert p X)) :
    ∃ i, p ∈ A i ∧ ∀ t ∈ A i, t ∉ X := by
  classical
  by_contra h
  apply ne
  funext i
  apply propext
  constructor
  · rintro ⟨t,ht,hx⟩
    exact ⟨t,ht,Set.mem_insert_of_mem p hx⟩
  · rintro ⟨t,ht,hx⟩
    rcases Set.mem_insert_iff.mp hx with rfl|hx
    · by_contra miss
      exact h ⟨i,ht,fun a ha ax => miss ⟨a,ha,ax⟩⟩
    · exact ⟨t,ht,hx⟩

def forest (g : P → L) (x : Set P) (y : Set L) := ∃ p ∈ x, g p ∈ y

theorem pointPorts (g : P → L) (A : I → Set P) (B : J → Set L)
    (D : (I → Prop) → (J → Prop) → Prop)
    (full : ∀ x y, D (code A x) (code B y) ↔ forest g x y)
    (thin : ∀ i p q, p ∈ A i → q ∈ A i → g p=g q → p=q) (p : P) :
    ∃ i, A i = {p} := by
  classical
  let base : Set P := {q | g q ≠ g p}
  have ne : code A base ≠ code A (insert p base) := by
    intro eq
    have yes : forest g (insert p base) {g p} := ⟨p,by simp,by simp⟩
    have dec := (full _ _).mpr yes
    rw [← eq] at dec
    obtain ⟨q,hq,hgp⟩ := (full _ _).mp dec
    exact hq (Set.mem_singleton_iff.mp hgp)
  obtain ⟨i,pi,all⟩ := rising A base p ne
  refine ⟨i,Set.Subset.antisymm ?_ ?_⟩
  · intro q hq
    have same : g q = g p := by
      by_contra bad
      exact all q hq bad
    exact Set.mem_singleton_iff.mpr (thin i q p hq pi same)
  · intro q hq
    rwa [Set.mem_singleton_iff.mp hq]

theorem linePorts (g : P → L) (A : I → Set P) (B : J → Set L)
    (D : (I → Prop) → (J → Prop) → Prop)
    (full : ∀ x y, D (code A x) (code B y) ↔ forest g x y)
    (surj : Function.Surjective g) (l : L) : ∃ j, B j = {l} := by
  classical
  obtain ⟨p,pl⟩ := surj l
  let base : Set L := {r | r ≠ l}
  have ne : code B base ≠ code B (insert l base) := by
    intro eq
    have yes : forest g {p} (insert l base) := ⟨p,by simp,by simp [pl]⟩
    have dec := (full _ _).mpr yes
    rw [← eq] at dec
    obtain ⟨q,hq,off⟩ := (full _ _).mp dec
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact off pl
  obtain ⟨j,lj,all⟩ := rising B base l ne
  refine ⟨j,Set.Subset.antisymm ?_ ?_⟩
  · intro r hr
    exact Set.mem_singleton_iff.mpr (by by_contra bad; exact all r hr bad)
  · intro r hr
    rwa [Set.mem_singleton_iff.mp hr]

theorem width {T K : Type} [Fintype T] [Fintype K] (A : K → Set T)
    (all : ∀ t, ∃ i, A i = {t}) : Fintype.card T ≤ Fintype.card K := by
  classical
  choose f bind using all
  apply Fintype.card_le_of_injective f
  intro x y eq
  have same : ({x} : Set T) = {y} := (bind x).symm.trans ((congrArg A eq).trans (bind y))
  simpa using same

theorem price [Fintype P] [Fintype L] [Fintype I] [Fintype J]
    (g : P → L) (A : I → Set P) (B : J → Set L)
    (D : (I → Prop) → (J → Prop) → Prop)
    (full : ∀ x y, D (code A x) (code B y) ↔ forest g x y)
    (thin : ∀ i p q, p ∈ A i → q ∈ A i → g p=g q → p=q)
    (surj : Function.Surjective g) (gates : Nat)
    (ports : Fintype.card I + Fintype.card J ≤ gates+1) :
    Fintype.card P + Fintype.card L ≤ gates+1 := by
  have a := width A (pointPorts g A B D full thin)
  have b := width B (linePorts g A B D full surj)
  omega

end PEqualNP.Outside.L_meta_9829.PencilPorts
