import PEqualNP.Outside.L_meta_2235

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

end PEqualNP.Outside.L_meta_2377_read
