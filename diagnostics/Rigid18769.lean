import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18769.Rigid
open Finset
abbrev I := Fin 12
abbrev L := Fin 13
def idx (p : I) : L := ⟨p.val+1,by omega⟩
def nbr (p : I) : Finset L := univ.filter (fun l => idx p=l ∨ idx p=l+1 ∨ idx p=l+3 ∨ idx p=l+9)
theorem deg : ∀ p,(nbr p).card=4 := by decide +kernel
theorem loyal : ∀ p q : I,∀ l k : L, l≠k → l∈nbr p → l∈nbr q → k∈nbr p → k∈nbr q → p=q := by decide +kernel
def matching (l : L) (p : I) : L := (([[11, 12, 2, 1, 4, 10, 6, 5, 9, 7, 8, 3],[11, 2, 7, 4, 9, 5, 6, 12, 0, 10, 8, 3],[5, 12, 0, 1, 4, 6, 11, 8, 9, 7, 10, 3],[11, 12, 0, 1, 4, 10, 6, 5, 8, 7, 2, 9],[11, 2, 0, 8, 9, 5, 7, 12, 6, 1, 10, 3],[11, 12, 0, 1, 2, 6, 4, 7, 9, 10, 8, 3],[0, 12, 2, 4, 9, 5, 11, 7, 8, 1, 10, 3],[11, 12, 0, 1, 2, 10, 4, 5, 6, 9, 8, 3],[0, 12, 7, 1, 2, 10, 4, 5, 6, 9, 11, 3],[11, 12, 0, 1, 2, 10, 4, 5, 6, 7, 8, 3],[11, 12, 0, 1, 2, 5, 4, 7, 6, 9, 8, 3],[5, 12, 0, 1, 2, 10, 4, 7, 6, 9, 8, 3],[0, 2, 7, 1, 4, 10, 11, 5, 6, 9, 8, 3]] : List (List L)).getD l.val []).getD p.val 0

theorem avoids : ∀ l : L,(∀ p : I,matching l p∈nbr p ∧ matching l p≠l) ∧ Function.Injective (matching l) := by
  have facts : ∀ l : L,(∀ p : I,matching l p∈nbr p ∧ matching l p≠l) ∧
      (∀ p q : I,matching l p=matching l q → p=q) := by decide +kernel
  exact fun l => ⟨(facts l).1,fun _ _ => (facts l).2 _ _⟩
theorem cardinal12 {α : Type} [Fintype α] (A : α → Finset I) (B : α → Finset L)
    (valid : ∀a,∀p∈A a,∀l∈B a,l∈nbr p)
    (cover : ∀p,∀l∈nbr p,∃a,p∈A a ∧ l∈B a) :
    12≤Fintype.card α := by
  classical
  choose f hp hl using fun p => cover p (matching 0 p) ((avoids 0).1 p).1
  have inj : Function.Injective f := by
    intro p q eq
    by_contra ne
    have d : matching 0 p ≠ matching 0 q := fun h=>ne ((avoids 0).2 h)
    have pq : p∈A (f q) := eq ▸ hp p
    have lp : matching 0 p∈B (f q) := eq ▸ hl p
    exact ne (loyal p q _ _ d (valid _ p pq _ lp) (valid _ q (hp q) _ lp)
        (valid _ p pq _ (hl q)) (valid _ q (hp q) _ (hl q)))
  simpa using Fintype.card_le_of_injective f inj

theorem rigid {α : Type} [Fintype α] (A : α → Finset I) (B : α → Finset L)
    (valid : ∀a,∀p∈A a,∀l∈B a,l∈nbr p)
    (cover : ∀p,∀l∈nbr p,∃a,p∈A a ∧ l∈B a)
    (small : Fintype.card α≤12) :
    ∃ f : I → α,Function.Bijective f ∧ ∀p,A (f p)={p} ∧ B (f p)=nbr p := by
  classical
  have card : Fintype.card α=12 := le_antisymm small (cardinal12 A B valid cover)
  have hits (l : L) (a : α) : ∃ k∈B a,k≠l := by
    choose f hp hl using fun p => cover p (matching l p) ((avoids l).1 p).1
    have inj : Function.Injective f := by
      intro p q eq
      by_contra ne
      have d : matching l p ≠ matching l q := fun h=>ne ((avoids l).2 h)
      have pq : p∈A (f q) := eq ▸ hp p
      have lp : matching l p∈B (f q) := eq ▸ hl p
      exact ne (loyal p q _ _ d (valid _ p pq _ lp) (valid _ q (hp q) _ lp)
          (valid _ p pq _ (hl q)) (valid _ q (hp q) _ (hl q)))
    obtain ⟨p,rfl⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simp [card]⟩).2 a
    exact ⟨_,hl p,((avoids l).1 p).2⟩
  have single (a : α) {p q : I} (hp : p∈A a) (hq : q∈A a) : p=q := by
    obtain ⟨u,hu,_⟩ := hits 0 a
    obtain ⟨v,hv,vu⟩ := hits u a
    exact loyal p q v u vu (valid _ _ hp _ hv) (valid _ _ hq _ hv) (valid _ _ hp _ hu) (valid _ _ hq _ hu)
  choose f hp hl using fun p => cover p (matching 0 p) ((avoids 0).1 p).1
  have inj : Function.Injective f := fun p q eq=>single (f q) (eq ▸ hp p) (hp q)
  have bij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simp [card]⟩
  refine ⟨f,bij,fun p=>⟨?_,?_⟩⟩
  · ext q
    exact ⟨fun h=>mem_singleton.mpr (single _ h (hp p)),fun h=>by obtain rfl := mem_singleton.mp h; exact hp p⟩
  · apply Finset.Subset.antisymm
    · exact fun l h => valid _ _ (hp p) _ h
    · intro l hh
      obtain ⟨a,pa,la⟩ := cover p l hh
      obtain ⟨q,rfl⟩ := bij.2 a
      obtain rfl := single _ pa (hp q)
      exact la
end PEqualNP.Outside.L_meta_18769.Rigid
