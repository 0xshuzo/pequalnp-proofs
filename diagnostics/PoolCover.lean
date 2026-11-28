import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17257.Pools
open Finset

def hit {β : Type*} (pool : ℕ → Finset β) (Y : Finset β) (w : ℕ) : Prop :=
  ∃ l∈pool w, l∈Y

theorem pool_cover {β : Type*} [DecidableEq β] (L : Finset β) (pool : ℕ → Finset β)
    (ports : Finset ℕ) (q : ℕ) (fits : ports.card≤q) (accept : Finset β → Prop)
    (localMono : ∀ X Y : Finset β,(∀ w∈ports,hit pool X w → hit pool Y w) → accept X → accept Y)
    (pos : ∀ l∈L,accept {l}) (neg : ∀ Y : Finset β,Y.card≤q → Disjoint Y L → ¬accept Y) :
    ∀ l∈L,∃ w∈ports,l∈pool w ∧ pool w⊆L := by
  classical
  intro l hl
  by_contra miss
  let A := ports.filter (fun w => l∈pool w)
  have extra : ∀ w∈A,∃ b∈pool w,b∉L := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    by_contra! h
    exact miss ⟨w,hw'.1,hw'.2,h⟩
  let select (w : ℕ) := if h : w∈A then (extra w h).choose else l
  have chosen (w : ℕ) (h : w∈A) : select w∈pool w ∧ select w∉L := by
    simpa [select,dif_pos h] using (extra w h).choose_spec
  let Y := A.image select
  have small : Y.card≤q := (Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))).trans fits
  have clear : Disjoint Y L := by
    apply Finset.disjoint_left.mpr
    intro b hb
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
    exact (chosen w hw).2
  apply neg Y small clear
  apply localMono {l} Y _ (pos l hl)
  intro w hw h
  obtain ⟨v,hv,vl⟩ := h
  have e : v=l := Finset.mem_singleton.mp vl
  have hA : w∈A := Finset.mem_filter.mpr ⟨hw,e ▸ hv⟩
  exact ⟨select w,(chosen w hA).1,Finset.mem_image_of_mem _ hA⟩

end PEqualNP.Outside.L_meta_17257.Pools
