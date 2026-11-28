import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17257.Selector
open Finset

theorem reach_price {β : Type*} [DecidableEq β] (A : ℕ → Finset β) (n s k : ℕ)
    (init : ∀ i<n,(A i).card≤k)
    (fork : ∀ j<s, k<(A (n+j)).card → ∃ a<n+j, ∃ b<n+j, A (n+j)⊆A a∪A b) :
    ∀ t≤s, ∀ Q : Finset ℕ, (∀ w∈Q,w<n+t) →
      (Q.biUnion A).card ≤ k*(Q.card+((range t).filter (fun j => k<(A (n+j)).card)).card) := by
  intro t
  induction t with
  | zero =>
    intro _ Q lo
    have h := Finset.card_biUnion_le (s:=Q) (t:=A)
    have l : ∑ i∈Q,(A i).card ≤ ∑ _i∈Q,k :=
      Finset.sum_le_sum (fun i hi => init i (by simpa using lo i hi))
    simpa [Nat.mul_comm] using h.trans l
  | succ t ih =>
    intro ts Q lo
    let v := n+t
    let U := (range t).filter (fun j => k<(A (n+j)).card)
    let T := (range (t+1)).filter (fun j => k<(A (n+j)).card)
    change (Q.biUnion A).card ≤ k*(Q.card+T.card)
    have incl : U⊆T := by
      intro j hj
      obtain ⟨lt,prop⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp lt)),prop⟩
    have inc := Finset.card_le_card incl
    have small (w : ℕ) (h : w∈Q) (ne : w≠v) : w<n+t := by
      have := lo w h
      dsimp [v] at ne
      omega
    by_cases hv : v∈Q
    · let E := Q.erase v
      have er : E.card+1=Q.card := Finset.card_erase_add_one hv
      have low (w : ℕ) (hw : w∈E) : w<n+t :=
        small w (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1
      by_cases rich : k<(A v).card
      · obtain ⟨a,ha,b,hb,f⟩ := fork t (by omega) rich
        let Q' := E∪{a,b}
        have sub : Q.biUnion A ⊆ Q'.biUnion A := by
          intro x hx
          obtain ⟨w,hw,hit⟩ := Finset.mem_biUnion.mp hx
          by_cases z : w=v
          · subst w
            rcases Finset.mem_union.mp (f hit) with h|h
            · exact Finset.mem_biUnion.mpr ⟨a,by simp [Q'],h⟩
            · exact Finset.mem_biUnion.mpr ⟨b,by simp [Q'],h⟩
          · exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨z,hw⟩),hit⟩
        have qlo : ∀ w∈Q',w<n+t := by
          intro w hw
          rcases Finset.mem_union.mp hw with h|h
          · exact low w h
          · simp only [Finset.mem_insert,Finset.mem_singleton] at h
            rcases h with rfl|rfl
            · exact ha
            · exact hb
        have c := Finset.card_union_le E ({a,b}:Finset ℕ)
        have two := Finset.card_le_two (a:=a) (b:=b)
        have mt : t∈T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self t),rich⟩
        have mu : t∉U := by simp [U]
        have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨incl,fun e => mu (e.symm ▸ mt)⟩)
        have price := ih (by omega) Q' qlo
        change (Q'.biUnion A).card ≤ k*(Q'.card+U.card) at price
        have cx : Q'.card+U.card≤Q.card+T.card := by dsimp [Q']; omega
        exact (Finset.card_le_card sub).trans (price.trans (Nat.mul_le_mul_left _ cx))
      · have sub : Q.biUnion A ⊆ E.biUnion A ∪ A v := by
          intro x hx
          obtain ⟨w,hw,hit⟩ := Finset.mem_biUnion.mp hx
          by_cases z : w=v
          · exact Finset.mem_union_right _ (z ▸ hit)
          · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w,Finset.mem_erase.mpr ⟨z,hw⟩,hit⟩)
        have price := ih (by omega) E low
        change (E.biUnion A).card ≤ k*(E.card+U.card) at price
        calc (Q.biUnion A).card ≤ (E.biUnion A∪A v).card := Finset.card_le_card sub
             _ ≤ (E.biUnion A).card+(A v).card := Finset.card_union_le _ _
             _ ≤ k*(E.card+U.card)+k := Nat.add_le_add price (by omega)
             _ = k*(E.card+U.card+1) := by ring
             _ ≤ k*(Q.card+T.card) := Nat.mul_le_mul_left _ (by omega)
    · have price := ih (by omega) Q (fun w hw => small w hw (fun e => hv (e ▸ hw)))
      exact price.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left inc _))

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)


end PEqualNP.Outside.L_meta_17257.Selector
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
namespace PEqualNP.Outside.L_meta_17257.Pools
open Finset
open PEqualNP.Outside.L_meta_17257.Selector

theorem pool_price {N q n s : ℕ} (L : Fin N → Finset (Fin N))
    (uniform : ∀ p,(L p).card=q+1)
    (linear : ∀ p r : Fin N,p≠r → (L p∩L r).card≤1)
    (pool : ℕ → Finset (Fin N)) (ports : Fin N → Finset ℕ)
    (raw : ∀ w<n,(pool w).card≤1)
    (fork : ∀ j<s,1<(pool (n+j)).card → ∃ a<n+j, ∃ b<n+j,pool (n+j)=pool a∪pool b)
    (live : ∀ p w,w∈ports p → w<n+s)
    (accept : Fin N → Finset (Fin N) → Prop)
    (query : ∀ p X Y,(∀ w∈ports p,hit pool X w → hit pool Y w) → accept p X → accept p Y)
    (pos : ∀ p l,l∈L p → accept p {l})
    (neg : ∀ p Y,Y.card≤q → Disjoint Y (L p) → ¬accept p Y) :
    N*(q+1) ≤ s+∑ p,(ports p).card := by
  classical
  let C (p : Fin N) (w : ℕ) : Finset (Fin N) := if pool w⊆L p then pool w else ∅
  let U (p : Fin N) := (range s).filter (fun j => 1<(C p (n+j)).card)
  have sub (p : Fin N) (w : ℕ) : C p w⊆pool w := by
    by_cases h : pool w⊆L p <;> simp [C,h]
  have genuine (p : Fin N) (w : ℕ) (rich : 1<(C p w).card) : pool w⊆L p := by
    by_contra h
    simp [C,h] at rich
  have bound (p : Fin N) : q+1 ≤ (ports p).card+(U p).card := by
    by_cases enough : q<(ports p).card
    · omega
    have cov := pool_cover (L p) pool (ports p) q (by omega) (accept p) (query p) (pos p) (neg p)
    have cover : L p ⊆ (ports p).biUnion (C p) := by
      intro l hl
      obtain ⟨w,hw,wl,inside⟩ := cov l hl
      exact Finset.mem_biUnion.mpr ⟨w,hw,by simpa [C,inside] using wl⟩
    have init (w : ℕ) (hw : w<n) : (C p w).card≤1 := (Finset.card_le_card (sub p w)).trans (raw w hw)
    have step (j : ℕ) (js : j<s) (rich : 1<(C p (n+j)).card) :
        ∃ a<n+j, ∃ b<n+j,C p (n+j)⊆C p a∪C p b := by
      have clean := genuine p (n+j) rich
      obtain ⟨a,ha,b,hb,eq⟩ := fork j js (rich.trans_le (Finset.card_le_card (sub p (n+j))))
      have ca : pool a⊆L p := fun _ h => clean <| eq.symm ▸ Finset.mem_union_left _ h
      have cb : pool b⊆L p := fun _ h => clean <| eq.symm ▸ Finset.mem_union_right _ h
      exact ⟨a,ha,b,hb,by simpa only [C,if_pos clean,if_pos ca,if_pos cb,eq] using (Finset.Subset.refl (pool a∪pool b))⟩
    have reach := reach_price (C p) n s 1 init step s le_rfl (ports p) (live p)
    rw [←uniform p]
    exact (Finset.card_le_card cover).trans (by simpa only [one_mul] using reach)
  have dis : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint U := by
    intro p _ r _ ne
    apply Finset.disjoint_left.mpr
    intro j hp hr
    have pa := (Finset.mem_filter.mp hp).2
    have ra := (Finset.mem_filter.mp hr).2
    have inside : pool (n+j)⊆L p∩L r := fun l hl =>
      Finset.mem_inter.mpr ⟨genuine p _ pa hl,genuine r _ ra hl⟩
    have le := (Finset.card_le_card (sub p (n+j))).trans ((Finset.card_le_card inside).trans (linear p r ne))
    omega
  have spent : ∑ p,(U p).card≤s := by
    have used : univ.biUnion U⊆range s := by
      intro j h
      obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hp).1
    have le := Finset.card_le_card used
    rw [Finset.card_biUnion dis,Finset.card_range] at le
    exact le
  have sum := Finset.sum_le_sum (s:=univ) (fun (p : Fin N) _ => bound p)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Finset.sum_add_distrib] at sum
  omega

end PEqualNP.Outside.L_meta_17257.Pools
