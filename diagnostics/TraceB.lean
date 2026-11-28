import PEqualNP.Defs

namespace Plane17872Trace

abbrev V := Fin 24
abbrev G := Fin 26
abbrev Wires := ℕ → Finset V
abbrev Homes := G → Finset V
abbrev Dem := Finset (G × ℕ)
abbrev Obligations := Finset (G × V)

def Covers (W : Wires) (D : Dem) (Z : Obligations) :=
  ∀ z ∈ Z, ∃ d ∈ D, d.1 = z.1 ∧ z.2 ∈ W d.2

def Fits (W : Wires) (H : Homes) (D : Dem) (bound : ℕ) :=
  ∀ d ∈ D, d.2 < bound ∧ W d.2 ⊆ H d.1

def Linear (H : Homes) := ∀ (g h : G), g ≠ h →
  ∀ u ∈ H g, u ∈ H h → ∀ v ∈ H g, v ∈ H h → u=v

def Legal (W : Wires) (s : ℕ) := ∀ j<s,
  W (24+j)=∅ ∨ (∃ v, W (24+j)={v}) ∨
  ∃ a<24+j, ∃ b<24+j, W (24+j) = W a ∪ W b

theorem trace_price (H : Homes) (lh : Linear H) (W : Wires)
    (raw : ∀ i : V, W i.val={i}) (s : ℕ) (hw : Legal W s)
    (D : Dem) (Z : Obligations) (fit : Fits W H D (24+s))
    (cov : Covers W D Z) : Z.card ≤ D.card + s := by
  classical
  induction s generalizing D with
  | zero =>
    let f : G × ℕ → G × V := fun d => (d.1,⟨d.2%24,Nat.mod_lt _ (by decide)⟩)
    have sub : Z ⊆ D.image f := by
      intro z hz
      obtain ⟨d,hd,eq,hin⟩ := cov z hz
      have b := (fit d hd).1
      let v : V := ⟨d.2,by omega⟩
      have rr : W d.2 = {v} := raw v
      have hv : z.2 = v := by simpa [rr] using hin
      apply Finset.mem_image.mpr
      refine ⟨d,hd,Prod.ext eq ?_⟩
      apply Fin.ext
      change d.2 % 24 = z.2.val
      rw [hv,Nat.mod_eq_of_lt (by omega)]
    simpa using (Finset.card_le_card sub).trans Finset.card_image_le
  | succ s ih =>
    let k := 24+s
    have hs : Legal W s := fun j h => hw j (by omega)
    have skip (hd : ∀ d ∈ D, d.2 ≠ k) : Z.card ≤ D.card + (s+1) := by
      have old : Fits W H D (24+s) := by
        intro d h
        have := (fit d h).1
        have := hd d h
        exact ⟨(by dsimp [k] at *; omega),(fit d h).2⟩
      exact Nat.le_trans (ih hs D old cov) (by omega)
    by_cases used : ∃ d∈D, d.2=k
    · obtain ⟨d0,hd0,ed⟩ := used
      rcases hw s (by omega) with empty|⟨v,hv⟩|⟨a,ha,b,hb,eq⟩
      · let E := D.filter fun d => d.2 ≠ k
        have old : Fits W H E (24+s) := by
          intro d h
          obtain ⟨h1,h2⟩ := Finset.mem_filter.mp h
          have := (fit d h1).1
          exact ⟨(by dsimp [k] at *; omega),(fit d h1).2⟩
        have cover : Covers W E Z := by
          intro z hz
          obtain ⟨d,hd,eg,iv⟩ := cov z hz
          refine ⟨d,Finset.mem_filter.mpr ⟨hd,?_⟩,eg,iv⟩
          intro dk
          simpa [dk,k,empty] using iv
        have sz : E.card ≤ D.card := Finset.card_filter_le _ _
        have := ih hs E old cover
        omega
      · let f : G × ℕ → G × ℕ := fun d => if d.2=k then (d.1,v.val) else d
        have old : Fits W H (D.image f) (24+s) := by
          intro y hy
          obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hy
          by_cases e : d.2=k
          · have hh := (fit d hd).2
            rw [e] at hh
            simpa [f,e,k,hv,raw] using And.intro (show v.val < 24+s by omega) hh
          · have h1 := (fit d hd).1
            rw [show f d=d from if_neg e]
            exact ⟨(by dsimp [k] at *; omega),(fit d hd).2⟩
        have cover : Covers W (D.image f) Z := by
          intro z hz
          obtain ⟨d,hd,eg,iv⟩ := cov z hz
          refine ⟨f d,Finset.mem_image_of_mem _ hd,?_,?_⟩
          · by_cases e : d.2=k <;> simp [f,e,eg]
          · by_cases e : d.2=k
            · simpa [f,e,k,hv,raw] using iv
            · simpa [f,e] using iv
        have sz : (D.image f).card ≤ D.card := Finset.card_image_le
        have := ih hs _ old cover
        omega
      · by_cases small : ∀ u∈W k, ∀ v∈W k, u=v
        · have collapse : W k = W a ∨ W k = W b := by
            by_cases h : (W a).Nonempty
            · obtain ⟨u,hu⟩ := h
              left; apply Finset.Subset.antisymm
              · intro v hv
                have eq' := small u (by rw [show W k=W a ∪ W b from eq]; exact Finset.mem_union_left _ hu) v hv
                simpa [←eq'] using hu
              · rw [show W k=W a ∪ W b from eq]; exact Finset.subset_union_left
            · right; simpa [k, Finset.not_nonempty_iff_eq_empty.mp h] using eq
          obtain ⟨c,hc,ec⟩ : ∃ c<k,W k=W c := collapse.elim (fun h => ⟨a,ha,h⟩) (fun h=>⟨b,hb,h⟩)
          let f : G × ℕ → G × ℕ := fun d => if d.2=k then (d.1,c) else d
          have fdata (d : G × ℕ) (hd : d∈D) : (f d).1=d.1 ∧ (f d).2<k ∧ W (f d).2=W d.2 := by
            by_cases h : d.2=k
            · simp [f,h,hc,ec]
            · have fl := (fit d hd).1
              simp only [f,if_neg h, true_and]
              exact ⟨(by dsimp [k] at *; omega),True.intro⟩
          have old : Fits W H (D.image f) (24+s) := by
            intro y hy
            obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hy
            obtain ⟨eg,eb,ew⟩ := fdata d hd
            exact ⟨eb,eg ▸ (ew ▸ (fit d hd).2)⟩
          have cover : Covers W (D.image f) Z := by
            intro z hz
            obtain ⟨d,hd,eg,iv⟩ := cov z hz
            obtain ⟨fg,_,fw⟩ := fdata d hd
            exact ⟨f d,Finset.mem_image_of_mem _ hd,fg.trans eg,fw ▸ iv⟩
          have sz : (D.image f).card ≤ D.card := Finset.card_image_le
          have := ih hs _ old cover
          omega
        · push_neg at small
          obtain ⟨u,hu,v,hv,uv⟩ := small
          have unique (d : G × ℕ) (hd : d∈D) (e : d.2=k) : d.1=d0.1 := by
            by_contra ne
            have h := (fit d hd).2
            have h0 := (fit d0 hd0).2
            rw [e] at h
            rw [ed] at h0
            exact uv (lh _ _ ne u (h hu) (h0 hu) v (h hv) (h0 hv))
          let f : G × ℕ → G × ℕ := fun d => if d.2=k then (d.1,a) else d
          let E := insert (d0.1,b) (D.image f)
          have old : Fits W H E (24+s) := by
            intro y hy
            rcases Finset.mem_insert.mp hy with rfl|hm
            · have h0 := (fit d0 hd0).2
              rw [ed,show W k=W a∪W b from eq] at h0
              exact ⟨hb, Finset.Subset.trans Finset.subset_union_right h0⟩
            · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hm
              by_cases e : d.2=k
              · have hh := (fit d hd).2
                rw [e,show W k=W a∪W b from eq] at hh
                exact (show f d=(d.1,a) from if_pos e) ▸ ⟨ha,Finset.Subset.trans Finset.subset_union_left hh⟩
              · have h1 := (fit d hd).1
                rw [show f d=d from if_neg e]
                exact ⟨(by dsimp [k] at *; omega),(fit d hd).2⟩
          have cover : Covers W E Z := by
            intro z hz
            obtain ⟨d,hd,eg,iv⟩ := cov z hz
            by_cases h : d.2=k
            · rw [h,show W k=W a∪W b from eq] at iv
              rcases Finset.mem_union.mp iv with ix|ix
              · refine ⟨f d,Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hd),?_,?_⟩ <;> simp [f,h,eg,ix]
              · exact ⟨_,Finset.mem_insert_self _ _,(unique d hd h).symm.trans eg,ix⟩
            · refine ⟨f d,Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hd),?_,?_⟩ <;> simp [f,h,eg,iv]
          have bz : E.card ≤ D.card+1 :=
            (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
          have := ih hs _ old cover
          omega
    · apply skip
      intro d h e
      exact used ⟨d,h,e⟩

end Plane17872Trace
