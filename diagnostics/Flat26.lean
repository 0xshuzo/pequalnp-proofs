import PEqualNP.Outside.L_meta_1983
namespace Flat9746
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1983
def hL_here : List (ℕ × ℕ) := [((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]

def adjB_here (u v : Fin 14) : Bool := decide ((u.1, v.1) ∈ hL_here ∨ (v.1, u.1) ∈ hL_here)

lemma adjB_symm_here : ∀ u v : Fin 14, adjB_here u v = adjB_here v u := by decide +kernel

lemma adjB_irrefl_here : ∀ u : Fin 14, adjB_here u u = false := by decide +kernel

lemma noLoop_here : ∀ a : Fin 14, (a.1, a.1) ∉ hL_here := by decide +kernel

set_option maxRecDepth 100000 in
lemma adjB_c4_here : ∀ a b c d : Fin 14, a ≠ c → b ≠ d →
    ¬ (adjB_here a b = true ∧ adjB_here b c = true ∧ adjB_here c d = true ∧ adjB_here d a = true) := by
  decide +kernel

def hw_here : SimpleGraph (Fin 14) := SimpleGraph.fromRel (fun u v => adjB_here u v = true)

lemma hw_adj_here (u v : Fin 14) : hw_here.Adj u v ↔ adjB_here u v = true := by
  unfold hw_here
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rw [adjB_symm_here]; exact h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rw [adjB_irrefl_here] at h
    exact Bool.false_ne_true h

lemma hw_c4_here : ∀ a b c d : Fin 14, a ≠ c → b ≠ d →
    ¬ (hw_here.Adj a b ∧ hw_here.Adj b c ∧ hw_here.Adj c d ∧ hw_here.Adj d a) := by
  rintro a b c d h1 h2 ⟨p, q, r, s⟩
  exact adjB_c4_here a b c d h1 h2
    ⟨(hw_adj_here _ _).1 p, (hw_adj_here _ _).1 q, (hw_adj_here _ _).1 r, (hw_adj_here _ _).1 s⟩

lemma edge_iff_here (x : Fin 14 → Bool) :
    (∃ a b : Fin 14, (a.1, b.1) ∈ hL_here ∧ x a = true ∧ x b = true) ↔
      ∃ u v : Fin 14, hw_here.Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨a, b, h, ha, hb⟩
    refine ⟨a, b, (hw_adj_here a b).2 ?_, ha, hb⟩
    unfold adjB_here
    rw [decide_eq_true_eq]
    exact Or.inl h
  · rintro ⟨u, v, h, hu, hv⟩
    have h' := (hw_adj_here u v).1 h
    unfold adjB_here at h'
    rw [decide_eq_true_eq] at h'
    rcases h' with h' | h'
    · exact ⟨u, v, h', hu, hv⟩
    · exact ⟨v, u, h', hv, hu⟩

def pairSet_here : Finset (Fin 14 × Fin 14) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ adjB_here p.1 p.2 = true)

lemma pairSet_card_here : pairSet_here.card = 20 := by decide +kernel

lemma hw_edges_here (inst : Fintype hw_here.edgeSet) :
    20 ≤ (@SimpleGraph.edgeFinset _ hw_here inst).card := by
  rw [← pairSet_card_here]
  refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
  · intro p hp
    have hp' : p.1 < p.2 ∧ adjB_here p.1 p.2 = true := by simpa [pairSet_here] using hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (hw_adj_here _ _).2 hp'.2
  · intro p hp q hq h
    have hp' : p.1 < p.2 ∧ adjB_here p.1 p.2 = true := by simpa [pairSet_here] using hp
    have hq' : q.1 < q.2 ∧ adjB_here q.1 q.2 = true := by simpa [pairSet_here] using hq
    have h' : s(p.1, p.2) = s(q.1, q.2) := h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have h3 := hp'.1
      rw [h1, h2] at h3
      exact absurd h3 (not_lt.2 hq'.1.le)

def mIdx_here (v : Fin 14) : Fin 7 :=
  ([0, 1, 2, 3, 4, 5, 6, 1, 2, 5, 0, 6, 3, 4] : List (Fin 7)).getD v.1 0

def mP_here (i : Fin 7) : Fin 14 := ([0, 1, 2, 3, 4, 5, 6] : List (Fin 14)).getD i.1 0

def mL_here (i : Fin 7) : Fin 14 := ([10, 7, 8, 12, 13, 9, 11] : List (Fin 14)).getD i.1 0

lemma match_facts_here : ∀ i : Fin 7,
    adjB_here (mP_here i) (mL_here i) = true ∧ mIdx_here (mP_here i) = i ∧ mIdx_here (mL_here i) = i := by decide +kernel

lemma cover7_here (T : Finset (Fin 14)) (h : ∀ u v : Fin 14, hw_here.Adj u v → u ∈ T ∨ v ∈ T) :
    7 ≤ T.card := by
  have hs : (Finset.univ : Finset (Fin 7)) ⊆ T.image mIdx_here := by
    intro i _
    obtain ⟨h1, h2, h3⟩ := match_facts_here i
    rcases h _ _ ((hw_adj_here _ _).2 h1) with hh | hh
    · exact Finset.mem_image.2 ⟨_, hh, h2⟩
    · exact Finset.mem_image.2 ⟨_, hh, h3⟩
  have h1 := Finset.card_le_card hs
  have h2 := Finset.card_image_le (s := T) (f := mIdx_here)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem core_here (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack 14 C)
    (hno : ¬∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 14 C i j)
    (hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin 14, (a.1, b.1) ∈ hL_here ∧ x a = true ∧ x b = true) : 26 ≤ C.size := by
  have hlen : ∀ x : Fin 14 → Bool, (List.ofFn x).length = 14 := fun x => by simp
  have hev : ∀ x : List Bool, C.eval x = V C.gates x C.output := fun x => rfl
  obtain ⟨o, ho, hout⟩ : ∃ o, o < C.gates.length ∧ C.output = 14 + o := by
    by_cases h1 : C.output < 14
    · exfalso
      have h := (hf (fun z => decide (z.1 = C.output))).1 (by
        rw [hev]
        unfold V
        rw [getD_wF _ _ _ (by simpa using h1), getD_ofFn 14 _ _ _ h1]
        simp)
      obtain ⟨a, b, hab, ha, hb⟩ := h
      have ha' : a.1 = C.output := by simpa using ha
      have hb' : b.1 = C.output := by simpa using hb
      have hab' : a = b := Fin.ext (ha'.trans hb'.symm)
      subst hab'
      exact absurd hab (noLoop_here a)
    · by_cases h2 : C.output < 14 + C.gates.length
      · exact ⟨C.output - 14, by omega, by omega⟩
      · exfalso
        have h := (hf (fun _ => true)).2 ⟨0, 8, by decide, rfl, rfl⟩
        rw [hev, V_out _ _ _ (by rw [hlen]; omega)] at h
        exact Bool.false_ne_true h
  have hfun : ∀ x : Fin 14 → Bool, V C.gates (List.ofFn x) (14 + o) = true ↔
      ∃ u v : Fin 14, hw_here.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    rw [← hout, ← hev, hf x]
    exact edge_iff_here x
  have hB := fun x : Fin 14 → Bool => same_val C hRB o ho (List.ofFn x) (hlen x)
  have hbin : ∀ g ∈ newG C o, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    obtain ⟨g0, hg0, he⟩ := newG_inv C o i _ (List.getElem?_eq_getElem hi)
    rw [he]
    have hm := hM g0 (List.mem_of_getElem? hg0)
    split_ifs
    · exact ⟨by simpa using hm.1, hm.2⟩
    · exact ⟨Or.inr rfl, by simp⟩
  have key := @pairCleanBound 14 hw_here (fun u v => decidable_of_iff _ (hw_adj_here u v).symm) hw_c4_here (newG C o) C.output hbin
  have key2 := key (by
    intro x
    have h1 : Circuit.eval ⟨newG C o, C.output⟩ (List.ofFn x)
        = V C.gates (List.ofFn x) (14 + o) := by
      rw [eval_eq, hout]; exact hB x o ho (Or.inl rfl)
    rw [h1]
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    exact hfun x) (by
    intro i x _ hop hv
    have hi : i.1 < C.gates.length := lt_of_lt_of_eq i.2 (newG_len C o)
    obtain ⟨g0, hg0, he⟩ := newG_inv C o i.1 ((newG C o).get i) (by simp)
    have hk : i.1 = o ∨ InCone 14 C i.1 o := by
      by_contra hk
      rw [he, ite_eq_right_of_eq_false _ _ (eq_false hk)] at hop
      simp at hop
    rw [he, ite_eq_left_of_eq_true _ _ (eq_true hk)] at hop
    have hga : gateAt C i.1 = g0 := by
      rw [gateAt_eq C _ hi]
      exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hg0)
    have hv' : V C.gates (List.ofFn x) (14 + i.1) = true := by
      rw [← hB x i.1 hi hk]; exact hv
    apply (hfun x).1
    rcases hk with hk | hk
    · rw [← hk]; exact hv'
    · exact up_true C hM hRB hno _ (hlen x) i.1 (by rw [hga]; exact hop) hv' o ho hk)
  obtain ⟨T, hT, hcard⟩ := key2
  rw [newG_len] at hcard
  have h7 := cover7_here T hT
  have h28 := le_trans (Nat.add_le_add (hw_edges_here _) h7) hcard
  show 26 ≤ C.gates.length
  omega

end Flat9746
