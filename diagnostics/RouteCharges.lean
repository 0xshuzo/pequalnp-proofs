import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166.RouteCharges

variable {I S : Type} [Fintype I] [DecidableEq S]

def used (f : I → S) : Finset S := Finset.univ.image f
def localSet (f : I → S) (v : S) : Finset I := Finset.univ.filter (fun i => f i=v)

theorem advance (f g : I → S) (v : S) (outs : Finset S)
    (fixed : ∀ i, f i≠v → g i=f i)
    (moves : ∀ i, f i=v → g i∈outs) :
    (used g).card ≤ (used f).card + min (localSet f v).card outs.card - 1
      ∨ used g=used f := by
  classical
  by_cases live : v∈used f
  · left
    let A := (localSet f v).image g
    have sub : used g ⊆ (used f).erase v ∪ A := by
      intro y hy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
      by_cases q : f i=v
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,q⟩,rfl⟩)
      · rw [fixed i q]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨q,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩)
    have asub : A ⊆ outs := by
      intro y hy
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hy
      exact moves i (Finset.mem_filter.mp hi).2
    have ac : A.card ≤ min (localSet f v).card outs.card :=
      le_min Finset.card_image_le (Finset.card_le_card asub)
    have q:=(Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have er:=Finset.card_erase_of_mem live
    have pos:=Finset.card_pos.mpr ⟨v,live⟩
    omega
  · right
    have eq : g=f := by
      funext i
      apply fixed
      intro hx
      exact live (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hx⟩)
    rw [eq]

theorem path_price (f : Nat → I → S) (step : Nat → S) (outs : Nat → Finset S)
    (fixed : ∀ k i, f k i≠step k → f (k+1) i=f k i)
    (moves : ∀ k i, f k i=step k → f (k+1) i∈outs k)
    (n : Nat) :
    (used (f n)).card ≤ (used (f 0)).card +
      ∑ k∈Finset.range n, (min (localSet (f k) (step k)).card (outs k).card - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases advance (f n) (f (n+1)) (step n) (outs n) (fixed n) (moves n) with bound|eq
    · omega
    · rw [eq]
      omega

end PEqualNP.Outside.L_pcx_166.RouteCharges
