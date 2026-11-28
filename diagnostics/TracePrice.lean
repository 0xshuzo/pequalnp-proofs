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

namespace Plane17872Trace

def graph (a b : Fin 12) : Prop :=
  (9 : Fin 13).succAbove a + (0 : Fin 13).succAbove b ∈ ({0,1,3,9} : Finset (Fin 13))
instance (a b : Fin 12) : Decidable (graph a b) := by unfold graph; infer_instance

abbrev F := {e : Fin 12 × Fin 12 // graph e.1 e.2}
abbrev pt (i : Fin 12) := i.castAdd 12
abbrev ln (i : Fin 12) := i.natAdd 12
def name (i : V) : G := ⟨i.val,by omega⟩
def table : List (Finset V) := [
  {12,14,20},
  {13,19,23},
  {12,18,22,23},
  {17,21,22},
  {16,20,21,23},
  {15,19,20,22},
  {14,18,19,21},
  {13,17,18,20},
  {12,16,17,19},
  {14,15,17,23},
  {13,14,16,22},
  {12,13,15,21},
  {0,2,8,11},
  {1,7,10,11},
  {0,6,9,10},
  {5,9,11},
  {4,8,10},
  {3,7,8,9},
  {2,6,7},
  {1,5,6,8},
  {0,4,5,7},
  {3,4,6,11},
  {2,3,5,10},
  {1,2,4,9},
  {0,1,3},
  {15,16,18}]

def home (g : G) : Finset V := table.getD g.val ∅
def star (i : V) : Finset V := home (name i)

def extra (i : Fin 6) : G × V :=
  ((if i.val<3 then 24 else 25), ([0,1,3,15,16,18] : List V).getD i.val 0)

def flag (b : Bool) (e : F) : G × V :=
  if b then (name (pt e.val.1),ln e.val.2) else (name (ln e.val.2),pt e.val.1)

set_option maxHeartbeats 10000000 in
theorem finite_geometry :
    Fintype.card F=45 ∧
    (∀ (a b : Bool) (e f : F), flag a e=flag b f → e=f) ∧
    (∀ (a : Bool) (e : F) (i : Fin 6), flag a e ≠ extra i) ∧
    (∀ i j : Fin 6, extra i=extra j → i=j) ∧
    (∀ i : Fin 6, (extra i).2 ∈ home (extra i).1) := by decide +kernel

def color (v : V) : Fin 12 := ⟨([0,1,2,3,4,5,6,7,8,9,10,11,8,7,6,5,4,3,2,1,0,11,10,9] : List Nat).getD v.val 0 % 12, Nat.mod_lt _ (by decide)⟩
def diagonal (i : Fin 12) : Fin 12 := ⟨([8,7,6,5,4,3,2,1,0,11,10,9] : List Nat).getD i.val 0 % 12,Nat.mod_lt _ (by decide)⟩

theorem match_geom : ∀ i : Fin 12, graph i (diagonal i) ∧ color (pt i)=i ∧ color (ln (diagonal i))=i := by decide +kernel

def Oriented (W : Wires) {t : Nat} (cen : Fin t → V) (arm : Fin t → Nat) :=
  ∀ e : F, ∃ i : Fin t, ∃ b : Bool, (flag b e).1=name (cen i) ∧ (flag b e).2∈W (arm i)

theorem terms_floor {W : Wires} {t : Nat} {cen : Fin t → V} {arm : Fin t → Nat}
    (co : Oriented W cen arm) : 12≤t := by
  classical
  have sur : Function.Surjective (fun j : Fin t => color (cen j)) := by
    intro i
    obtain ⟨dg,hp,hl⟩ := match_geom i
    obtain ⟨j,b,hh,_⟩ := co ⟨(i,diagonal i),dg⟩
    refine ⟨j,?_⟩
    cases b
    · have hv : ln (diagonal i) = cen j := Fin.ext (congrArg (fun z : G => z.val) hh)
      simpa [←hv] using hl
    · have hv : pt i = cen j := Fin.ext (congrArg (fun z : G => z.val) hh)
      simpa [←hv] using hp
  simpa using Fintype.card_le_of_surjective _ sur

set_option maxHeartbeats 10000000 in
theorem geom_linear : Linear home := by
  have h : ∀ a b : G, a≠b → ((home a)∩(home b)).card ≤ 1 := by decide +kernel
  intro a b neq u hu hu' v hv hv'
  exact Finset.card_le_one.mp (h a b neq) _ (Finset.mem_inter.mpr ⟨hu,hu'⟩) _ (Finset.mem_inter.mpr ⟨hv,hv'⟩)

theorem symmetric_home : ∀ u v : V, u∈star v ↔ v∈star u := by decide +kernel

theorem singleton_home (c : V) (A B : Finset V) (a b : V) (ne : a≠b)
    (ha : a∈A) (hb : b∈A) (sound : ∀ u∈A, ∀ v∈B, v∈star u)
    (hc : c∈B) : B={c} := by
  apply Finset.Subset.antisymm
  · intro v hv
    apply Finset.mem_singleton.mpr
    exact geom_linear (name a) (name b) (fun h=>ne (Fin.ext (congrArg (fun z : G => z.val) h)))
      v (sound _ ha _ hv) (sound _ hb _ hv) c (sound _ ha _ hc) (sound _ hb _ hc)
  · simpa using hc

theorem term_star (W : Wires) (a b : Nat)
    (sound : ∀ u∈W a, ∀ v∈W b, v∈star u) :
    ∃ c : V, ∃ j : Nat, (j=a ∨ j=b) ∧ W j ⊆ star c ∧
      ∀ u∈W a, ∀ v∈W b, (u=c ∧ v∈W j) ∨ (v=c ∧ u∈W j) := by
  classical
  by_cases sa : (W a).Nonempty
  · obtain ⟨p,hp⟩ := sa
    by_cases sb : (W b).Nonempty
    · obtain ⟨l,hl⟩ := sb
      by_cases all : ∀ u∈W a,u=p
      · exact ⟨p,b,Or.inr rfl,sound _ hp,fun u hu v hv=>Or.inl ⟨all u hu,hv⟩⟩
      · push_neg at all
        obtain ⟨p',hp',ne⟩ := all
        have beq := singleton_home l _ _ p' p ne hp' hp sound hl
        refine ⟨l,a,Or.inl rfl,?_,?_⟩
        · intro v hv
          exact (symmetric_home l v).mp (sound _ hv _ hl)
        · intro u hu v hv
          exact Or.inr ⟨by simpa [beq] using hv,hu⟩
    · have emp : W b=∅ := Finset.not_nonempty_iff_eq_empty.mp sb
      exact ⟨0,b,Or.inr rfl,by simp [emp],by simp [emp]⟩
  · have emp : W a=∅ := Finset.not_nonempty_iff_eq_empty.mp sa
    exact ⟨0,a,Or.inl rfl,by simp [emp],by simp [emp]⟩

theorem marked_charge {W : Wires} {s t : ℕ} (raw : ∀ i : V, W i.val={i})
    (hw : Legal W s) (cen : Fin t → V) (arm : Fin t → Nat)
    (hcen : ∀ i, arm i<24+s ∧ W (arm i)⊆home (name (cen i)))
    (co : Oriented W cen arm) (ma mb : Nat) (ha : ma<24+s) (hb : mb<24+s)
    (pa : W ma=home 24) (pb : W mb=home 25) : 61≤s+2*t := by
  classical
  have t12 := terms_floor co
  choose sel orient geom hit using co
  let de : Fin t → G × Nat := fun j => (name (cen j),arm j)
  let D : Dem := insert (24,ma) (insert (25,mb) (Finset.univ.image de))
  let pack : F ⊕ Fin 6 → G × V := Sum.elim (fun e => flag (orient e) e) extra
  let Z : Obligations := Finset.univ.image pack
  obtain ⟨h45,inj,neq,exinj,exin⟩ := finite_geometry
  have inject : Function.Injective pack := by
    intro a b eq
    cases a with
    | inl e =>
      cases b with
      | inl f => exact congrArg Sum.inl (inj _ _ _ _ eq)
      | inr j => exact (neq _ _ _ eq).elim
    | inr i =>
      cases b with
      | inl f => exact (neq _ _ _ eq.symm).elim
      | inr j => exact congrArg Sum.inr (exinj i j eq)
  have zcard : Z.card=51 := by
    dsimp [Z]
    rw [Finset.card_image_of_injective _ inject]
    simp [Fintype.card_sum,h45]
  have dcard : D.card≤t+2 := by
    have h1 := Finset.card_insert_le (24,ma) (insert (25,mb) (Finset.univ.image de))
    have h2 := Finset.card_insert_le (25,mb) (Finset.univ.image de)
    have h3 : (Finset.univ.image de).card≤t := by simpa using (Finset.card_image_le (s := Finset.univ) (f := de))
    dsimp [D]; omega
  have ft : Fits W home D (24+s) := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl|hd
    · exact ⟨ha,pa.le⟩
    rcases Finset.mem_insert.mp hd with rfl|hd
    · exact ⟨hb,pb.le⟩
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
    exact hcen j
  have cv : Covers W D Z := by
    intro z hz
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hz
    cases e with
    | inl e =>
      refine ⟨de (sel e),Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))),?_,?_⟩
      · exact (geom e).symm
      · exact hit e
    | inr i =>
      have mem := exin i
      by_cases h : i.val<3
      · have exg : (extra i).1=24 := by simp [extra,h]
        refine ⟨(24,ma),Finset.mem_insert_self _ _,exg.symm,?_⟩
        simpa [pack,pa,exg] using mem
      · have exg : (extra i).1=25 := by simp [extra,h]
        refine ⟨(25,mb),Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),exg.symm,?_⟩
        simpa [pack,pb,exg] using mem
  have price := trace_price home geom_linear W raw s hw D Z ft cv
  omega

end Plane17872Trace

namespace Plane17872Trace

theorem clean_price {W : Wires} {s t : Nat} (raw : ∀ i : V,W i.val={i}) (hw : Legal W s)
    (pair : Fin t → Nat × Nat)
    (bd : ∀ i, (pair i).1<24+s ∧ (pair i).2<24+s)
    (sound : ∀ i, ∀ u∈W (pair i).1, ∀ v∈W (pair i).2,v∈star u)
    (complete : ∀ e : F, ∃ i : Fin t,
      (pt e.val.1 ∈ W (pair i).1 ∧ ln e.val.2 ∈ W (pair i).2) ∨
      (ln e.val.2 ∈ W (pair i).1 ∧ pt e.val.1 ∈ W (pair i).2))
    (ma mb : Nat) (ha : ma<24+s) (hb : mb<24+s)
    (pa : W ma=home 24) (pb : W mb=home 25) : 61 ≤ s+2*t := by
  classical
  choose center arm ids fits orient using fun i => term_star W (pair i).1 (pair i).2 (sound i)
  apply marked_charge raw hw center arm _ _ ma mb ha hb pa pb
  · intro i
    refine ⟨?_,fits i⟩
    rcases ids i with h|h
    · simpa [h] using (bd i).1
    · simpa [h] using (bd i).2
  · intro e
    obtain ⟨i,h|h⟩ := complete e
    · rcases orient i _ h.1 _ h.2 with ⟨he,hh⟩|⟨he,hh⟩
      · exact ⟨i,true,congrArg name he,hh⟩
      · exact ⟨i,false,congrArg name he,hh⟩
    · rcases orient i _ h.1 _ h.2 with ⟨he,hh⟩|⟨he,hh⟩
      · exact ⟨i,false,congrArg name he,hh⟩
      · exact ⟨i,true,congrArg name he,hh⟩

end Plane17872Trace
