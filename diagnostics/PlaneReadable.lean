import PEqualNP.Outside.L_meta_2235
import PEqualNP.Outside.L_meta_2237

namespace PEqualNP.Outside.L_meta_2377_read
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Outside.L_meta_2235
set_option maxRecDepth 32768
set_option maxHeartbeats 0

def orSet (C : Circuit) : Set (Fin C.gates.length) := {i | (C.gates.get i).op = .or}

private theorem twoOrCount (C : Circuit) (A B : Set ℕ)
    (hA : ∀ i ∈ A, i < C.gates.length ∧ (gateAt C i).op = .or)
    (hB : ∀ i ∈ B, i < C.gates.length ∧ (gateAt C i).op = .or)
    (hAB : ∀ i ∈ A, i ∉ B) : A.ncard + B.ncard ≤ (orSet C).ncard := by
  classical
  have af : A.Finite := (Set.finite_lt_nat _).subset (fun i hi => (hA i hi).1)
  have bf : B.Finite := (Set.finite_lt_nat _).subset (fun i hi => (hB i hi).1)
  have hd : Disjoint af.toFinset bf.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hAB x ((Set.Finite.mem_toFinset af).mp hx) ((Set.Finite.mem_toFinset bf).mp hy)
  have hs : af.toFinset ∪ bf.toFinset ⊆ (orSet C).toFinset.image Fin.val := by
    intro i hi
    have prop : i < C.gates.length ∧ (gateAt C i).op = .or := by
      rcases Finset.mem_union.mp hi with ha | hb
      · exact hA i ((Set.Finite.mem_toFinset af).mp ha)
      · exact hB i ((Set.Finite.mem_toFinset bf).mp hb)
    obtain ⟨hi, hop⟩ := prop
    refine Finset.mem_image.mpr ⟨⟨i,hi⟩, ?_, rfl⟩
    rw [Set.mem_toFinset]
    change (C.gates.get ⟨i,hi⟩).op = .or
    simpa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hop
  rw [Set.ncard_eq_toFinset_card A af, Set.ncard_eq_toFinset_card B bf,
    ← Finset.card_union_of_disjoint hd, Set.ncard_eq_toFinset_card']
  exact le_trans (Finset.card_le_card hs) Finset.card_image_le

private theorem readableCore (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Fin n × Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (h30 : ∀ e ∈ E, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
        (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1)))
    (h31a : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → OrReaches n C C.output j →
      (∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 → G.Adj u v) ∧
      ((side (n := n) C j 0).card ≤ 1 ∨ (side (n := n) C j 1).card ≤ 1))
    (h33 : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        OrReaches n C C.output j) →
      F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} + 1)
    (h34 : ∀ (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ),
      (∀ j ∈ F, ∀ b : Fin n, b ∈ orIn n C (lf j) → G.Adj (ctr j) b) →
      (∀ i < C.gates.length, (gateAt C i).op = GateOp.or → 2 ≤ (orIn n C (n + i)).card →
        (∃ j1 ∈ F, OrReaches n C (lf j1) i) → ¬ OrReaches n C C.output i) ∧
      ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card ≤
        Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} + F.card) :
    E.card ≤ (orSet C).ncard + 1 := by
  classical
  by_cases hE : E = ∅
  · simp [hE]
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, ∀ j, j ∈ F ↔ (j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty) :=
    ⟨(Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hper : ∀ j : ℕ, ∃ (c : Fin n) (l : ℕ), j ∈ F →
      (∀ b : Fin n, b ∈ orIn n C l → G.Adj c b) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 →
        (c = u ∧ v ∈ orIn n C l) ∨ (c = v ∧ u ∈ orIn n C l)) := by
    intro j
    by_cases hj : j ∈ F
    · obtain ⟨hjl, hand, hor, hn0, hn1⟩ := (hF j).mp hj
      obtain ⟨hdis, hadj, hcard⟩ := h31a j hjl hand hor
      rcases hcard with hc | hc
      · obtain ⟨c, hc0⟩ := hn0
        refine ⟨c, opnd C j 1, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact hadj c hc0 b hb
        · intro u hu v hv
          exact Or.inl ⟨Finset.card_le_one.mp hc c hc0 u hu, hv⟩
      · obtain ⟨c, hc1⟩ := hn1
        refine ⟨c, opnd C j 0, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact (hadj b hb c hc1).symm
        · intro u hu v hv
          exact Or.inr ⟨Finset.card_le_one.mp hc c hc1 v hv, hu⟩
    · exact ⟨e0.1, 0, fun h => absurd h hj⟩
  choose ctr lf hcl using hper
  have hw : ∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
      ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
        (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1)) := by
    intro e he
    obtain ⟨j, hjl, hand, hor, hs⟩ := h30 e he
    refine ⟨j, (hF j).mpr ⟨hjl, hand, hor, ?_, ?_⟩, hjl, hand, hor, hs⟩
    · rcases hs with hs | hs
      · exact ⟨e.1, hs.1⟩
      · exact ⟨e.2, hs.1⟩
    · rcases hs with hs | hs
      · exact ⟨e.2, hs.2⟩
      · exact ⟨e.1, hs.2⟩
  have hFand : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j := by
    intro j hj
    obtain ⟨ha, hb, hc, _⟩ := (hF j).mp hj
    exact ⟨ha, hb, hc⟩
  have h3 := h33 F hFand
  obtain ⟨h4a, h4b⟩ := h34 F ctr lf (fun j hj => (hcl j hj).1)
  have hEsum := le_trans (sum_card_ge E (fun c => Finset.univ.filter (fun b2 : Fin n =>
      ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))) hlt (by
    intro e he
    obtain ⟨j, hjF, _, _, _, hs⟩ := hw e he
    rcases hs with hs | hs
    · rcases (hcl j hjF).2 e.1 hs.1 e.2 hs.2 with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
    · rcases (hcl j hjF).2 e.2 hs.1 e.1 hs.2 with h | h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩))) h4b
  have hOR := twoOrCount C
    {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i}
    {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
      2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2}
    (fun i hi => ⟨hi.1,hi.2.1⟩) (fun i hi => ⟨hi.1,hi.2.1⟩)
    (fun i hi hiB => h4a i hi.1 hi.2.1 hiB.2.2.1 hiB.2.2.2 hi.2.2)
  omega

theorem readBound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Fin n × Fin n)) (hlt : ∀ e ∈ E, e.1 < e.2)
    (hr : ∀ e ∈ E, readsAtMost C n [e.1.val, e.2.val] 1 = true)
    (h4 : NoFourCycle G) (ao : IsAO2 n C)
    (h1 : ∀ a : Fin n, circuitFun n C (fun k => decide (k = a)) = false)
    (h2 : ∀ a b : Fin n, a ≠ b → ¬G.Adj a b → circuitFun n C (fun k => decide (k = a ∨ k = b)) = false) :
    E.card ≤ (orSet C).ncard + 1 := by
  have h31 := s2231 n G C h4 ao h1 h2
  exact readableCore n G C E hlt
    (fun e he => s2230 n C e.1 e.2 ao h1 (hlt e he) (hr e he))
    h31.1 (fun F => s2233 n C F ao) (fun F ctr lf => s2234 n G C F ctr lf h4 ao h1)


private theorem readGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Fin n × Fin n)) (he : ∀ e ∈ E, e.1 < e.2 ∧ G.Adj e.1 e.2)
    (h4 : NoFourCycle G) (ao : IsAO2 n C) (hread : IsReadK n C 1)
    (hfun : ∀ x : Fin n → Bool, circuitFun n C x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) :
    E.card ≤ (orSet C).ncard + 1 := by
  have hw1 : ∀ a1 : Fin n,
      PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false := by
    intro a1
    rw [hfun, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu1 : u = a1 := by simpa using hu
    have hv1 : v = a1 := by simpa using hv
    exact huv.ne (hu1.trans hv1.symm)
  have hw2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false := by
    intro a2 b2 hne hna
    rw [hfun, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu1 : u = a2 ∨ u = b2 := by simpa using hu
    have hv1 : v = a2 ∨ v = b2 := by simpa using hv
    rcases hu1 with h1 | h1 <;> rcases hv1 with h2 | h2
    · exact huv.ne (h1.trans h2.symm)
    · rw [h1, h2] at huv
      exact hna huv
    · rw [h1, h2] at huv
      exact hna huv.symm
    · exact huv.ne (h1.trans h2.symm)
  have hrd : ∀ a b : Fin n, a < b → G.Adj a b →
      PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true := by
    intro a b hab hadj
    have hpi : PEqualNP.ReadK.IsPrimeImplicant n C ({a, b} : Finset (Fin n)) := by
      constructor
      · rw [hfun, decide_eq_true_eq]
        exact ⟨a, b, hadj, by simp [PEqualNP.ReadK.setInput], by simp [PEqualNP.ReadK.setInput]⟩
      · intro T hT
        rw [hfun, decide_eq_false_iff_not]
        rintro ⟨u, v, huv, hu, hv⟩
        have hu1 : u ∈ T := by simpa [PEqualNP.ReadK.setInput] using hu
        have hv1 : v ∈ T := by simpa [PEqualNP.ReadK.setInput] using hv
        obtain ⟨hsub, hnot⟩ := Finset.ssubset_def.mp (Finset.mem_ssubsets.mp hT)
        have hu2 := hsub hu1
        have hv2 := hsub hv1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu2 hv2
        have hboth : a ∈ T ∧ b ∈ T := by
          rcases hu2 with h1 | h1 <;> rcases hv2 with h2 | h2
          · exact absurd (h1.trans h2.symm) huv.ne
          · rw [h1] at hu1
            rw [h2] at hv1
            exact ⟨hu1, hv1⟩
          · rw [h1] at hu1
            rw [h2] at hv1
            exact ⟨hv1, hu1⟩
          · exact absurd (h1.trans h2.symm) huv.ne
        apply hnot
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · rw [hx]
          exact hboth.1
        · rw [hx]
          exact hboth.2
    have h1 := hread ({a, b} : Finset (Fin n)) hpi
    rw [PEqualNP.Outside.L_meta_2237.cor_setList_pair a b hab] at h1
    exact h1
  exact readBound G C E (fun e h => (he e h).1)
    (fun e h => hrd e.1 e.2 (he e h).1 (he e h).2) h4 ao hw1 hw2

abbrev V := Fin 42

def edges : List (Nat × Nat) := (List.range 21).flatMap fun i =>
  [(i,21+(i+20)%21),(i,21+i),(i,21+(i+5)%21),(i,21+(i+7)%21),(i,21+(i+17)%21)]

def incidence (u v : V) : Bool := decide (u.val < 21 ∧ 21 ≤ v.val) && (1179809 : Nat).testBit ((v.val + 21 - u.val) % 21)

private theorem listed : ∀ u v : V, (u.val,v.val) ∈ edges ↔ incidence u v = true := by decide +kernel

def G : SimpleGraph V where
  Adj u v := incidence u v = true ∨ incidence v u = true
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := by
    have h : ∀ u : V, ¬ (incidence u u = true ∨ incidence u u = true) := by decide +kernel
    exact ⟨h⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (incidence u v = true ∨ incidence v u = true))

private theorem noC4 : NoFourCycle G := by decide +kernel

def oriented : Finset (V × V) := Finset.univ.filter fun e => incidence e.1 e.2 = true

private theorem orientedCount : oriented.card = 105 := by decide +kernel

private theorem orderedEdges : ∀ e ∈ oriented, e.1 < e.2 ∧ G.Adj e.1 e.2 := by
  have h : ∀ e : V × V, incidence e.1 e.2 = true → e.1 < e.2 := by decide +kernel
  intro e he
  have he' : incidence e.1 e.2 = true := (Finset.mem_filter.mp he).2
  exact ⟨h e he',Or.inl he'⟩

theorem planeLower (C : Circuit) (ao : IsAO2 42 C) (hr : IsReadK 42 C 1)
    (ok : ∀ x : V → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b : V, (a.val,b.val) ∈ edges ∧ x a = true ∧ x b = true) :
    104 ≤ {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard := by
  have run (x : V → Bool) : circuitFun 42 C x = decide (∃ a b : V, G.Adj a b ∧ x a = true ∧ x b = true) := by
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x) = true ↔ _
    rw [decide_eq_true_eq,ok]
    constructor
    · rintro ⟨a,b,ab,ha,hb⟩
      exact ⟨a,b,Or.inl ((listed a b).mp ab),ha,hb⟩
    · rintro ⟨a,b,ab,ha,hb⟩
      rcases ab with ab | ba
      · exact ⟨a,b,(listed a b).mpr ab,ha,hb⟩
      · exact ⟨b,a,(listed b a).mpr ba,hb,ha⟩
  have h := readGraph G C oriented orderedEdges noC4 ao hr run
  rw [orientedCount] at h
  change 104 ≤ (orSet C).ncard
  omega

end PEqualNP.Outside.L_meta_2377_read
