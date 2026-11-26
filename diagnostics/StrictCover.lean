import PEqualNP.Outside.L_meta_9091

namespace PlanePartial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9091.GraphProof PEqualNP.Outside.L_meta_9091.Extra
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
theorem budget (hC : Monotone2 C) (he : GraphEval C G)
    (X : Finset (Fin n)) (hdegree : ∀ v ∈ X, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in X.card + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have sub : X.image Fin.val ⊆ W.filter (fun a => a < n) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨by have := v.isLt; omega,input_live he hu⟩,v.isLt⟩
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at card
  have partition := Finset.card_filter_add_card_filter_not (s:=W) (fun a => a<n)
  have hW : X.card + S.card ≤ W.card := by
    change (W.filter (fun a => a<n)).card + S.card = W.card at partition
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change X.card+B.card ≤ C.gates.length+1
  omega


lemma strict_budget {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Monotone2 C) (he : GraphEval C G)
    (X : Finset (Fin n)) (hdegree : ∀ v ∈ X, ∃ u, G.Adj v u) (ho : C.output ∈ living n C)
    (h3 : ∃ b ∈ living n C, Branch n C b ∧ 3 ≤ (readers n C b).card) :
    open Classical in X.card + ((living n C).filter (Branch n C)).card ≤ C.size := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  obtain ⟨b0, hb0W, hb0_br, hb0_3⟩ := h3
  have hb0B : b0 ∈ B := Finset.mem_filter.mpr ⟨hb0W, hb0_br⟩
  have sub : X.image Fin.val ⊆ W.filter (fun a => a < n) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨by have := v.isLt; omega,input_live he hu⟩,v.isLt⟩
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at card
  have partition := Finset.card_filter_add_card_filter_not (s:=W) (fun a => a<n)
  have hW : X.card + S.card ≤ W.card := by
    change (W.filter (fun a => a<n)).card + S.card = W.card at partition
    omega
  have hR : R.card + 1 = W.card := Finset.card_erase_add_one ho
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a - n)
    · intro a ha
      have h : a < n + C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a - n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a - n = b - n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hb0_ne : b0 ≠ C.output := fun h => hoNone (h ▸ (Finset.mem_filter.mp hb0B).2)
  have hlow : R.card + B.card + 1 ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a = C.output then 0 else 1 : ℕ)) = R.card := by
      calc _ = ∑ a ∈ W, (if a ≠ C.output then 1 else 0 : ℕ) :=
            Finset.sum_congr rfl (fun a _ => by by_cases h : a = C.output <;> simp [h])
        _ = R.card := by rw [← Finset.sum_filter]; simp [R, Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]; simp [B]
    have hb0W' : b0 ∈ W := hb0W
    have e1 : (∑ a ∈ W, (if a = b0 then 1 else 0 : ℕ)) = 1 := by
      rw [Finset.sum_ite_eq', ite_eq_left hb0W']
    calc R.card + B.card + 1
      _ = (∑ a ∈ W, (if a = C.output then 0 else 1 : ℕ)) +
          (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) +
          (∑ a ∈ W, (if a = b0 then 1 else 0 : ℕ)) := by rw [eR, eB, e1]
      _ = ∑ a ∈ W, ((if a = C.output then 0 else 1) + (if Branch n C a then 1 else 0) + (if a = b0 then 1 else 0)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ ≤ ∑ a ∈ W, (readers n C a).card := by
        apply Finset.sum_le_sum
        intro a ha
        have hl := (mem_living.1 ha).2
        by_cases hab0 : a = b0
        · subst hab0
          have hbr : Branch n C a := (Finset.mem_filter.mp hb0B).2
          simp only [hb0_ne, ↓reduceIte, hbr]
          omega
        · by_cases heq : a = C.output
          · subst a; simp [hoNone, hab0]
          · by_cases hb : Branch n C a
            · have hb' : 2 ≤ (readers n C a).card := hb
              simpa [heq, hb, hab0] using hb'
            · simpa [heq, hb, hab0] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm : (∑ a ∈ W, (readers n C a).card) =
      ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2 * S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j < n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j < n then 0 else 2 : ℕ)) = 2 * S.card := by
      simp [S, Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change X.card + B.card ≤ C.gates.length
  omega


theorem injective_on (hC : Monotone2 C) (he : GraphEval C G)
    {v w : Fin n} (htwins : v ≠ w → ¬ G.Adj v w → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) (hv : Eligible C v) (hw : Eligible C w)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins hne hadj
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]


set_option maxHeartbeats 4000000 in
theorem strict_cover
    (G : SimpleGraph (Fin n)) (C : Circuit) (X : Finset (Fin n))
    (inX : ∀ {v w}, G.Adj v w → v ∈ X)
    (other : ∀ v ∈ X, ∀ w, ∃ u, G.Adj v u ∧ u ≠ w)
    (square : ∀ (v w a b : Fin n), v ≠ w → a ≠ b →
      G.Adj v a → G.Adj v b → G.Adj w a → G.Adj w b → False)
    (edge : ∃ a b, G.Adj a b)
    (hC : Monotone2 C) (eval : GraphEval C G) :
    ∃ S ⊆ X, (∀ v w, G.Adj v w → v ∈ S ∨ w ∈ S) ∧
      X.card + S.card ≤ C.size + 1 ∧
      (X.card + S.card ≤ C.size ∨ ∀ w ∈ S, ∀ v1 v2 v3,
        v1 ≠ v2 → v1 ≠ v3 → v2 ≠ v3 →
        G.Adj w v1 → G.Adj w v2 → G.Adj w v3 → v1 ∈ S ∨ v2 ∈ S ∨ v3 ∈ S) := by
  classical
  let S := X.filter (Eligible C)
  have hS (v) : v ∈ S ↔ v ∈ X ∧ Eligible C v := by simp [S]
  have degree (v) (hv : v ∈ X) : ∃ w, G.Adj v w := by
    obtain ⟨w,hw,_⟩ := other v hv v
    exact ⟨w,hw⟩
  have twins (v) (hv : v ∈ X) (w) (ne : v ≠ w) (_ : ¬G.Adj v w) :
      ∃ u, ¬(G.Adj v u ↔ G.Adj w u) := by
    obtain ⟨a,va⟩ := degree v hv
    obtain ⟨b,vb,ba⟩ := other v hv a
    by_cases wa : G.Adj w a
    · by_cases wb : G.Adj w b
      · exact (square v w a b ne ba.symm va vb wa wb).elim
      · exact ⟨b,fun h => wb (h.mp vb)⟩
    · exact ⟨a,fun h => wa (h.mp va)⟩
  have hits (v w) (vw : G.Adj v w) : v ∈ S ∨ w ∈ S := by
    obtain ⟨a,va,aw⟩ := other v (inX vw) w
    obtain ⟨b,wb,bv⟩ := other w (inX vw.symm) v
    have ab : ¬G.Adj a b := fun e => square v b w a bv.symm aw.symm vw va wb.symm e.symm
    exact (covers_edge hC eval vw va aw wb bv (Or.inr ab)).imp
      (fun h => (hS v).mpr ⟨inX vw,h⟩) (fun h => (hS w).mpr ⟨inX vw.symm,h⟩)
  obtain ⟨a0,b0,ab0⟩ := edge
  have hlt_out := (edge_at_output eval ab0).2
  have houtput : C.output ∈ living n C := mem_living.mpr ⟨hlt_out,ReflTransGen.refl⟩
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f, hu]
  have hf_maps : ∀ u ∈ S, f u ∈ B := by
    intro u hu
    have hs := ((hS u).mp hu).2
    have hb := firstBranch_spec u hs
    have hw := (next_le hb.1).trans_lt hlt_out
    rw [hf u hs]
    exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hw, hb.1⟩, hb.2.2⟩
  have hf_inj : Set.InjOn f S := by
    intro u hu v hv same
    have hsu := ((hS u).mp hu).2
    have hsv := ((hS v).mp hv).2
    rw [hf u hsu, hf v hsv] at same
    exact injective_on hC eval (twins u ((hS u).mp hu).1 v) hsu hsv same
  have hcap : S.card ≤ B.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
  have hbud_raw := budget hC eval X degree houtput
  have hB_card_eq : B.card = (open Classical in ((living n C).filter (Branch n C)).card) := by
    congr 1
  have hbud : X.card + B.card ≤ C.size + 1 := by rw [hB_card_eq]; exact hbud_raw
  refine ⟨S,Finset.filter_subset _ _,hits,by omega,?_⟩
  by_cases good : X.card + S.card ≤ C.size
  · exact Or.inl good
  apply Or.inr
  intro w hwS v1 v2 v3 h12 h13 h23 hw1 hw2 hw3
  by_contra! no
  obtain ⟨hv1,hv2,hv3⟩ := no
  have hBE : B.card = S.card := by omega
  have hB_img : S.image f = B := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact hf_maps u hu
    · rw [Finset.card_image_of_injOn hf_inj, hBE]
  have hB_deg2 : ∀ b ∈ B, (readers n C b).card = 2 := by
    intro b hb
    have hge2 : 2 ≤ (readers n C b).card := (Finset.mem_filter.mp hb).2
    by_contra hne2
    have hge3 : 3 ≤ (readers n C b).card := by omega
    have hstr_raw := strict_budget hC eval X degree houtput
      ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2, hge3⟩
    have hstr : X.card + B.card ≤ C.size := by rw [hB_card_eq]; exact hstr_raw
    omega
  have hwEl : Eligible C w := ((hS w).mp hwS).2
  have hmeet : ∀ v : Fin n, G.Adj w v →
      ∃ m a b g, C.gates[m - n]? = some g ∧ n ≤ m ∧
        LNext n C a m ∧ LNext n C b m ∧
        Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
        (∀ i ∈ g.inputs, i = a ∨ i = b) ∧ ¬ Carries C w m := by
    intro v hwv
    obtain ⟨p, g, a, b, hg, _, _, ha, hb, hva, hwa, hwb, hvb, h2, hwm⟩ := meeting_gate hC eval (G.adj_symm hwv)
    refine ⟨n + p, a, b, g, by simpa using hg, by omega, ha, hb, hva, hwa, hwb, hvb, h2, ?_⟩
    rw [carries_iff hC]
    simp [hwm]
  obtain ⟨m1, a1, b1, g1, hg1, hm1ge, ha1, hb1, hv1a1, hwa1, hwb1, _, h2g1, hwm1⟩ := hmeet v1 hw1
  obtain ⟨m2, a2, b2, g2, hg2, hm2ge, ha2, hb2, hv2a2, hwa2, hwb2, _, h2g2, hwm2⟩ := hmeet v2 hw2
  obtain ⟨m3, a3, b3, g3, hg3, hm3ge, ha3, hb3, hv3a3, hwa3, hwb3, _, h2g3, hwm3⟩ := hmeet v3 hw3
  have hm_ne : ∀ (u1 u2 : Fin n) (m a b c : ℕ) (g : Gate),
      u1 ∉ S → u1 ≠ u2 → G.Adj w u1 → G.Adj w u2 →
      C.gates[m - n]? = some g → n ≤ m →
      LNext n C a m → LNext n C c m →
      Carries C u1 a → ¬ Carries C w a → Carries C w b →
      Carries C u2 c → ¬ Carries C w c →
      (∀ i ∈ g.inputs, i = a ∨ i = b) → False := by
    intro u1 u2 m a b c g u1out hu12 hwu1 hwu2 hgm hmge ham hcm hu1a hwa hwb hu2c hwc h2g
    have hc_in : c ∈ g.inputs := by
      obtain ⟨⟨_, p', g', hg', hm', hmem⟩, _⟩ := hcm
      have hp' : p' = m - n := by omega
      subst hp'
      rw [hgm] at hg'; cases hg'
      exact hmem
    have hca : c = a := by
      rcases h2g c hc_in with rfl | rfl
      · rfl
      · exact (hwc hwb).elim
    rw [hca] at hu2c
    have hu1_not : ¬ Eligible C u1 := fun h => u1out ((hS u1).mpr ⟨inX hwu1.symm,h⟩)
    obtain ⟨w', hu1w', hw'ne⟩ := other u1 (inX hwu1.symm) w
    have hnot_u2w' : ¬ G.Adj u2 w' := fun h =>
      square u1 u2 w w' hu12 hw'ne.symm hwu1.symm hu1w' hwu2.symm h
    let x := point ({u2, w'} : Finset (Fin n))
    let y := point (insert u1 ({u2, w'} : Finset (Fin n)))
    have hax : val C x a = true :=
      acts_mono hC (point_mono (by simp)) a ((carries_iff hC).mp hu2c).1
    have hay : val C y a = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) a hax
    have hpath := singleton_path (live_before ham.1 ham.2) hu1a
    have huniq : ∀ k j j', k < a → Carries C u1 k → LNext n C k j → LNext n C k j' → j = j' :=
      fun k j j' _ => no_eligible_unique hu1_not k j j'
    have hxy_out : val C x C.output = val C y C.output := by
      by_contra hdiff
      rcases influence hpath huniq (fun _ hi => (point_insert hi).symm) ReflTransGen.refl hdiff with bad | bad
      · exact (Nat.not_lt_of_ge (next_le (live_before ham.1 ham.2))) bad.1
      · exact bad.2 (hax.trans hay.symm)
    have hx0 : val C x C.output = false := point_pair_quiet eval hnot_u2w'
    have hy1 : val C y C.output = true := point_contains_edge hC eval (u := u1) (v := w')
      (by simp) (by simp) hu1w'
    exact Bool.false_ne_true (hx0.symm.trans (hxy_out.trans hy1))
  have hm12 : m1 ≠ m2 := fun h => hm_ne v1 v2 m1 a1 b1 a2 g1 hv1 h12 hw1 hw2 hg1 hm1ge ha1 (h ▸ ha2) hv1a1 hwa1 hwb1 hv2a2 hwa2 h2g1
  have hm13 : m1 ≠ m3 := fun h => hm_ne v1 v3 m1 a1 b1 a3 g1 hv1 h13 hw1 hw3 hg1 hm1ge ha1 (h ▸ ha3) hv1a1 hwa1 hwb1 hv3a3 hwa3 h2g1
  have hm23 : m2 ≠ m3 := fun h => hm_ne v2 v3 m2 a2 b2 a3 g2 hv2 h23 hw2 hw3 hg2 hm2ge ha2 (h ▸ ha3) hv2a2 hwa2 hwb2 hv3a3 hwa3 h2g2
  let bw := firstBranch C w hwEl
  have hbw_spec := firstBranch_spec w hwEl
  have hbw_path : Trace n C (Carries C w) w.val bw := singleton_path hbw_spec.1 hbw_spec.2.1
  have hstep_from_bw : ∀ (m b : ℕ), LNext n C b m → Carries C w b → ¬ Carries C w m →
      ∃ r ∈ readers n C bw, Trace n C (Carries C w) r m := by
    intro m b hbm hwb hwm
    have hPm : Trace n C (Carries C w) w.val m :=
      (singleton_path (live_before hbm.1 hbm.2) hwb).tail ⟨hwb, hbm⟩
    rcases align hbw_path (firstBranch_unique w hwEl) m hPm with bad | htail
    · exact (hwm bad.2).elim
    · rcases htail.cases_head with heq | ⟨r, hr, hrest⟩
      · exact (hwm (heq ▸ hbw_spec.2.1)).elim
      · exact ⟨r, mem_readers.mpr hr.2, hrest⟩
  obtain ⟨r1, hr1, hQ1⟩ := hstep_from_bw m1 b1 hb1 hwb1 hwm1
  obtain ⟨r2, hr2, hQ2⟩ := hstep_from_bw m2 b2 hb2 hwb2 hwm2
  obtain ⟨r3, hr3, hQ3⟩ := hstep_from_bw m3 b3 hb3 hwb3 hwm3
  have hbwB : bw ∈ B := by
    have h1 := hf_maps w hwS
    rwa [hf w hwEl] at h1
  have hcard2 : (readers n C bw).card = 2 := hB_deg2 bw hbwB
  have hpig : r1 = r2 ∨ r1 = r3 ∨ r2 = r3 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨h12', h13', h23'⟩ := hnot
    have hsub : ({r1, r2, r3} : Finset ℕ) ⊆ readers n C bw := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc3 : ({r1, r2, r3} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12', h13']), Finset.card_pair h23']
    have hle := Finset.card_le_card hsub
    omega
  have hget_z : ∃ z, bw < z ∧ Live n C z ∧ Carries C w z ∧ Branch n C z := by
    rcases hpig with heq | heq | heq
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ1 hQ2 hm12 hwm1 hwm2
      exact ⟨z, (mem_readers.mp hr1).1.1.trans_le hzle, hzl, hzc, hzb⟩
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ1 hQ3 hm13 hwm1 hwm3
      exact ⟨z, (mem_readers.mp hr1).1.1.trans_le hzle, hzl, hzc, hzb⟩
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ2 hQ3 hm23 hwm2 hwm3
      exact ⟨z, (mem_readers.mp hr2).1.1.trans_le hzle, hzl, hzc, hzb⟩
  obtain ⟨z, hbw_lt_z, hzlive, hzcw, hzb⟩ := hget_z
  have hzB : z ∈ B :=
    Finset.mem_filter.mpr ⟨mem_living.mpr ⟨(next_le hzlive).trans_lt hlt_out, hzlive⟩, hzb⟩
  rw [← hB_img] at hzB
  obtain ⟨u, huS, hfu⟩ := Finset.mem_image.mp hzB
  have huEl : Eligible C u := ((hS u).mp huS).2
  rw [hf u huEl] at hfu
  have huw_ne : u ≠ w := by
    intro h; subst h
    have : firstBranch C u huEl = bw := rfl
    omega
  obtain ⟨a, hua⟩ := degree u ((hS u).mp huS).1
  obtain ⟨b, hub, hba⟩ := other u ((hS u).mp huS).1 a
  have hex_vprime : ∃ v', G.Adj u v' ∧ ¬ G.Adj w v' := by
    by_cases hwa : G.Adj w a
    · by_cases hwb : G.Adj w b
      · exact (square u w a b huw_ne hba.symm hua hub hwa hwb).elim
      · exact ⟨b, hub, hwb⟩
    · exact ⟨a, hua, hwa⟩
  obtain ⟨v', huv', hnot_wv'⟩ := hex_vprime
  have hzw : val C (point {w}) z = true := ((carries_iff hC).mp hzcw).1
  have hz1 : val C (point ({w, v'} : Finset (Fin n))) z = true :=
    acts_mono hC (point_mono (by simp)) z hzw
  have hz2 : val C (point (insert u ({w, v'} : Finset (Fin n)))) z = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) z hz1
  have heq_out := value_at_branch huEl
    (x := point ({w, v'} : Finset (Fin n)))
    (y := point (insert u ({w, v'} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm)
    (by rw [hfu, hz1, hz2])
  have hx0 : val C (point ({w, v'} : Finset (Fin n))) C.output = false :=
    point_pair_quiet eval hnot_wv'
  have hy1 : val C (point (insert u ({w, v'} : Finset (Fin n)))) C.output = true :=
    point_contains_edge hC eval (u := u) (v := v') (by simp) (by simp) huv'
  exact Bool.false_ne_true (hx0.symm.trans (heq_out.trans hy1))

end PlanePartial
