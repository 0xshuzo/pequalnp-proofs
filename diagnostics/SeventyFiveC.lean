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


theorem private_selectors {N q n s : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 299≤q) (order : N=q^2+q+1) (cols : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (join : ∀ p r : Fin N,p≠r → ∃! l, I p l ∧ I r l)
    (S : Fin N → ℕ → Finset (Fin N)) (out : Fin N → ℕ) (live : ∀ p,out p<n+s)
    (root : ∀ p l,I p l → l∈S p (out p))
    (flags : ∀ p w l,l∈S p w → I p l)
    (raw : ∀ p i,i<n → (S p i).card≤75)
    (binary : ∀ p j,j<s → 75<(S p (n+j)).card →
      ∃ a<n+j, ∃ b<n+j, S p (n+j)⊆S p a∪S p b)
    (shared : ∀ p r j,j<s → (S r (n+j)).Nonempty →
      ((S p (n+j)).filter (fun l => ¬I r l)).card≤74) :
    N*(q+1) ≤ 100*s := by
  classical
  let U : Fin N → Finset ℕ := fun p => (range s).filter (fun j => 75<(S p (n+j)).card)
  have one (p : Fin N) : q+1 ≤ 75*(1+(U p).card) := by
    have through := lines_through q N I (by omega) order (fun l => by
      simpa only [Fintype.card_subtype] using cols l) join p
    have pre : univ.filter (fun l => I p l) ⊆ S p (out p) :=
      fun l h => root p l (Finset.mem_filter.mp h).2
    have reach := reach_price (S p) n s 75 (raw p) (binary p) s le_rfl {out p}
      (by intro w hw; have e := Finset.mem_singleton.mp hw; exact e.symm ▸ live p)
    simp only [Finset.singleton_biUnion,Finset.card_singleton] at reach
    rw [←through]
    exact (Finset.card_le_card pre).trans reach
  have dis : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint U := by
    intro p _ r _ ne
    apply Finset.disjoint_left.mpr
    intro j hp hr
    obtain ⟨js,rich⟩ := Finset.mem_filter.mp hp
    have richr := (Finset.mem_filter.mp hr).2
    have present : (S r (n+j)).Nonempty := Finset.card_pos.mp (by omega)
    have lost := shared p r j (Finset.mem_range.mp js) present
    have lone : ((S p (n+j)).filter (fun l => I r l)).card≤1 := by
      apply Finset.card_le_one.mpr
      intro l hl m hm
      obtain ⟨fl,rl⟩ := Finset.mem_filter.mp hl
      obtain ⟨fm,rm⟩ := Finset.mem_filter.mp hm
      exact (join p r ne).unique ⟨flags p _ l fl,rl⟩ ⟨flags p _ m fm,rm⟩
    have tot := Finset.card_filter_add_card_filter_not (s:=S p (n+j)) (fun l => I r l)
    omega
  have bound : ∑ p,(U p).card ≤ s := by
    have sub : univ.biUnion U ⊆ range s := by
      intro j h
      obtain ⟨p,_,hj⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hj).1
    have cc := Finset.card_le_card sub
    rw [Finset.card_biUnion dis, Finset.card_range] at cc
    exact cc
  have summed := Finset.sum_le_sum (s:=univ) (fun (p : Fin N) _ => one p)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ←Finset.mul_sum, Finset.sum_add_distrib,Nat.mul_one] at summed
  have lim : N*(q+1) ≤ 75*(N+s) := summed.trans (Nat.mul_le_mul_left 75 (Nat.add_le_add_left bound N))
  have h300 := Nat.mul_le_mul_left N (show 300≤q+1 by omega)
  omega

end PEqualNP.Outside.L_meta_17257.Selector
