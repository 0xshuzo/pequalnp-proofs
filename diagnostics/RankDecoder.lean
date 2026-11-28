import PEqualNP.Defs

namespace PEqualNP.Outside.Pcx177Rank

abbrev V := Fin 5
abbrev Holes := Fin 4
abbrev Board := Holes → Finset V
def zeroOn (x : Board) (s : Finset V) : Prop := ∀ h, Even (s ∩ x h).card

def difference (s t : Finset V) := (s \ t) ∪ (t \ s)

theorem difference_ne : ∀ s t : Finset V, s ≠ t → (difference s t).Nonempty := by
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem cancellation : ∀ s t c : Finset V,
    decide (Even (s ∩ c).card) = decide (Even (t ∩ c).card) →
    Even (difference s t ∩ c).card := by decide +kernel

theorem dependent (x : Board) : ∃ t : Finset V, t.Nonempty ∧ zeroOn x t := by
  let sig (s : Finset V) := fun h : Holes => decide (Even (s ∩ x h).card)
  have count : Fintype.card (Holes → Bool) < Fintype.card (Finset V) := by decide
  obtain ⟨s,t,ne,e⟩ := Fintype.exists_ne_map_eq_of_card_lt sig count
  exact ⟨difference s t,difference_ne _ _ ne,fun h => cancellation _ _ _ (congrFun e h)⟩

def connected (E : V → V → Prop) (s : Finset V) : Prop :=
  ∀ a : Finset V, a ⊆ s → a.Nonempty → a ≠ s →
    ∃ i ∈ a, ∃ j ∈ s, j ∉ a ∧ E i j

/-- For every graph of removed collision pairs, the retained collisions plus
nonzero row-XOR on its connected nonempty sets form an inconsistent decoder. -/
theorem connectedDefect (E : V → V → Prop) (x : Board)
   (keep : ∀ h, ∀ i ∈ x h, ∀ j ∈ x h, i ≠ j → E i j) :
   ∃ t : Finset V, t.Nonempty ∧ connected E t ∧ zeroOn x t := by
  classical
  let options := Finset.univ.filter (fun s : Finset V => s.Nonempty ∧ zeroOn x s)
  obtain ⟨t,ht,zt⟩ := dependent x
  have present : t ∈ options := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, zt⟩
  obtain ⟨s,hs,minimal⟩ := options.exists_min_image Finset.card ⟨_,present⟩
  have good := (Finset.mem_filter.mp hs).2
  refine ⟨s,good.1,?_,good.2⟩
  intro a sub ane neq
  by_contra no
  have za : zeroOn x a := by
    intro h
    by_cases yes : (a ∩ x h).Nonempty
    · obtain ⟨i,hi⟩ := yes
      have ia : i ∈ a := (Finset.mem_inter.mp hi).1
      have ih : i ∈ x h := (Finset.mem_inter.mp hi).2
      have same : a ∩ x h = s ∩ x h := by
        apply Finset.Subset.antisymm
        · intro j hj
          exact Finset.mem_inter.mpr ⟨sub (Finset.mem_inter.mp hj).1,(Finset.mem_inter.mp hj).2⟩
        · intro j hj
          obtain ⟨js,jh⟩ := Finset.mem_inter.mp hj
          by_cases ja : j ∈ a
          · exact Finset.mem_inter.mpr ⟨ja,jh⟩
          · exact False.elim (no ⟨i,ia,j,js,ja,keep h i ih j jh (fun eq => ja (eq ▸ ia))⟩)
      rw [same]
      exact good.2 h
    · have empty : a ∩ x h = ∅ := Finset.not_nonempty_iff_eq_empty.mp yes
      simp [empty]
  have mem : a ∈ options := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ane,za⟩
  have le := minimal a mem
  have lt : a.card < s.card := Finset.card_lt_card (lt_of_le_of_ne sub neq)
  omega

end PEqualNP.Outside.Pcx177Rank
