import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_5809

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

private def pgD : Finset (Fin 13) := {0, 1, 3, 9}

private def pgPairInput (p l : Fin 13) : List Bool :=
  (List.ofFn fun x : Fin 13 => Decidable.decide (x = p)) ++
    List.ofFn fun x : Fin 13 => Decidable.decide (x = l)

private def pgQuadInput (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun x : Fin 13 => Decidable.decide (x ∈ Q)) ++
    List.ofFn fun x : Fin 13 => Decidable.decide (∀ q ∈ Q, q - x ∉ pgD)

private abbrev isQuad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin 13, {q ∈ Q | q - l ∈ pgD}.card ≤ 2

private abbrev missesLine (Q : Finset (Fin 13)) (l : Fin 13) : Prop :=
  ∀ q ∈ Q, q - l ∉ pgD

private def shiftQuad (t : Fin 13) (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Q.image (· + t)

private def baseQuad : Fin 6 → Finset (Fin 13)
  | 0 => {0, 1, 4, 6}
  | 1 => {0, 1, 2, 5}
  | 2 => {0, 1, 2, 6}
  | 3 => {0, 1, 4, 8}
  | 4 => {0, 2, 3, 4}
  | 5 => {0, 3, 5, 6}

private lemma pg_edges_card :
    (Finset.univ.filter fun e : Fin 13 × Fin 13 => e.1 - e.2 ∈ pgD).card = 52 := by
  decide

private def difference : Fin 4 → Fin 13 := ![0, 1, 3, 9]

private lemma difference_index : ∀ x : Fin 13, x ∈ pgD → ∃ a, difference a = x := by
  decide

private lemma difference_unique :
    ∀ a b c d : Fin 4, difference a ≠ difference b →
      difference a - difference b = difference c - difference d → a = c := by
  decide

private lemma pg_no_c4 :
    ∀ p1 p2 l1 l2 : Fin 13, p1 ≠ p2 → l1 ≠ l2 →
      ¬ (p1 - l1 ∈ pgD ∧ p1 - l2 ∈ pgD ∧ p2 - l1 ∈ pgD ∧ p2 - l2 ∈ pgD) := by
  intro p1 p2 l1 l2 hp hl ⟨h11, h12, h21, h22⟩
  obtain ⟨a, ha⟩ := difference_index _ h11
  obtain ⟨b, hb⟩ := difference_index _ h12
  obtain ⟨c, hc⟩ := difference_index _ h21
  obtain ⟨d, hd⟩ := difference_index _ h22
  have hab : difference a ≠ difference b := by
    rw [ha, hb]
    exact fun h => hl (sub_right_inj.mp h)
  have hdiff : difference a - difference b = difference c - difference d := by
    rw [ha, hb, hc, hd]
    abel
  have heq := congrArg difference (difference_unique a b c d hab hdiff)
  rw [ha, hc] at heq
  exact hp (sub_left_inj.mp heq)

private lemma pg_zero_mem_D : (0 : Fin 13) ∈ pgD := by
  decide

private lemma pg_one_mem_D : (1 : Fin 13) ∈ pgD := by
  decide

private lemma baseQuad_isQuad : ∀ b : Fin 6, isQuad (baseQuad b) := by
  decide

private lemma baseQuad_mem_zero : ∀ b : Fin 6, (0 : Fin 13) ∈ baseQuad b := by
  decide

private lemma baseQuad_zero_misses_two : missesLine (baseQuad 0) 2 := by
  decide

private lemma baseQuad_pt_diff :
    ∀ d : Fin 13, d ≠ 0 → ∃ b : Fin 6, ∃ a ∈ baseQuad b, a + d ∈ baseQuad b := by
  decide

-- For each nonzero offset, a quadrangle and a line such that both lines miss the quadrangle.
private def lineWitness : Fin 13 → Fin 6 × Fin 13 :=
  ![(0, 0), (1, 7), (0, 7), (3, 6), (1, 3), (0, 2), (0, 9),
    (0, 2), (0, 7), (1, 7), (3, 9), (0, 9), (1, 8)]

private lemma lineWitness_spec : ∀ d : Fin 13, d ≠ 0 →
    missesLine (baseQuad (lineWitness d).1) (lineWitness d).2 ∧
    missesLine (baseQuad (lineWitness d).1) ((lineWitness d).2 + d) := by
  decide

private lemma baseQuad_line_diff :
    ∀ d : Fin 13, d ≠ 0 → ∃ b : Fin 6, ∃ l : Fin 13,
      missesLine (baseQuad b) l ∧ missesLine (baseQuad b) (l + d) :=
  fun d hd => ⟨(lineWitness d).1, (lineWitness d).2, lineWitness_spec d hd⟩

private def nonincWitness : Fin 13 → Fin 6 :=
  ![0, 5, 0, 1, 0, 4, 3, 0, 1, 0, 0, 4, 0]

private lemma nonincWitness_spec : ∀ d : Fin 13, (0 - d) ∉ pgD →
    missesLine (baseQuad (nonincWitness d)) d := by
  decide

private lemma baseQuad_noninc :
    ∀ d : Fin 13, (0 - d) ∉ pgD → ∃ b : Fin 6, missesLine (baseQuad b) d :=
  fun d hd => ⟨nonincWitness d, nonincWitness_spec d hd⟩

private lemma isQuad_shift (t : Fin 13) {Q : Finset (Fin 13)} (hQ : isQuad Q) :
    isQuad (shiftQuad t Q) := by
  refine ⟨?_, ?_⟩
  · unfold shiftQuad
    rw [Finset.card_image_of_injective Q (fun a b h => add_right_cancel h)]
    exact hQ.1
  · intro l
    have hbij : {q ∈ shiftQuad t Q | q - l ∈ pgD} =
        ({q ∈ Q | q - (l - t) ∈ pgD}).image (· + t) := by
      ext x
      simp only [shiftQuad, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hmem⟩
        refine ⟨a, ⟨ha, ?_⟩, rfl⟩
        have heq : a - (l - t) = a + t - l := by abel
        rwa [heq]
      · rintro ⟨a, ⟨ha, hmem⟩, rfl⟩
        refine ⟨⟨a, ha, rfl⟩, ?_⟩
        have heq : a + t - l = a - (l - t) := by abel
        rwa [heq]
    rw [hbij, Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
    exact hQ.2 (l - t)

private lemma missesLine_shift (t : Fin 13) {Q : Finset (Fin 13)} {l : Fin 13}
    (hm : missesLine Q l) : missesLine (shiftQuad t Q) (l + t) := by
  intro q hq
  simp only [shiftQuad, Finset.mem_image] at hq
  rcases hq with ⟨a, ha, rfl⟩
  have heq : a + t - (l + t) = a - l := by abel
  rw [heq]
  exact hm a ha

private lemma quad_has_pt (p : Fin 13) : ∃ Q : Finset (Fin 13), isQuad Q ∧ p ∈ Q := by
  refine ⟨shiftQuad p (baseQuad 0), isQuad_shift p (baseQuad_isQuad 0), ?_⟩
  simp only [shiftQuad, Finset.mem_image]
  exact ⟨0, baseQuad_mem_zero 0, zero_add p⟩

private lemma quad_misses_line (l : Fin 13) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ missesLine Q l := by
  refine ⟨shiftQuad (l - 2) (baseQuad 0), isQuad_shift (l - 2) (baseQuad_isQuad 0), ?_⟩
  have h := missesLine_shift (l - 2) baseQuad_zero_misses_two
  have heq : (2 : Fin 13) + (l - 2) = l := by abel
  rwa [heq] at h

private lemma quad_has_two_pts {p1 p2 : Fin 13} (hne : p1 ≠ p2) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ p1 ∈ Q ∧ p2 ∈ Q := by
  have hd : p2 - p1 ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases baseQuad_pt_diff (p2 - p1) hd with ⟨b, a, ha, had⟩
  refine ⟨shiftQuad (p1 - a) (baseQuad b), isQuad_shift (p1 - a) (baseQuad_isQuad b), ?_, ?_⟩
  · simp only [shiftQuad, Finset.mem_image]
    exact ⟨a, ha, by abel⟩
  · simp only [shiftQuad, Finset.mem_image]
    exact ⟨a + (p2 - p1), had, by abel⟩

private lemma quad_misses_two_lines {l1 l2 : Fin 13} (hne : l1 ≠ l2) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ missesLine Q l1 ∧ missesLine Q l2 := by
  have hd : l2 - l1 ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases baseQuad_line_diff (l2 - l1) hd with ⟨b, l, hm1, hm2⟩
  refine ⟨shiftQuad (l1 - l) (baseQuad b), isQuad_shift (l1 - l) (baseQuad_isQuad b), ?_, ?_⟩
  · have h := missesLine_shift (l1 - l) hm1
    have heq : l + (l1 - l) = l1 := by abel
    rwa [heq] at h
  · have h := missesLine_shift (l1 - l) hm2
    have heq : l + (l2 - l1) + (l1 - l) = l2 := by abel
    rwa [heq] at h

private lemma quad_noninc {p l : Fin 13} (hni : p - l ∉ pgD) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ p ∈ Q ∧ missesLine Q l := by
  have hni' : (0 : Fin 13) - (l - p) ∉ pgD := by
    have heq : (0 : Fin 13) - (l - p) = p - l := by abel
    rwa [heq]
  rcases baseQuad_noninc (l - p) hni' with ⟨b, hm⟩
  refine ⟨shiftQuad p (baseQuad b), isQuad_shift p (baseQuad_isQuad b), ?_, ?_⟩
  · simp only [shiftQuad, Finset.mem_image]
    exact ⟨0, baseQuad_mem_zero b, zero_add p⟩
  · have h := missesLine_shift p hm
    have heq : l - p + p = l := by abel
    rwa [heq] at h

private lemma pgPairInput_length (p l : Fin 13) : (pgPairInput p l).length = 26 := by
  unfold pgPairInput
  rw [List.length_append, List.length_ofFn, List.length_ofFn]

private lemma pgQuadInput_length (Q : Finset (Fin 13)) : (pgQuadInput Q).length = 26 := by
  unfold pgQuadInput
  rw [List.length_append, List.length_ofFn, List.length_ofFn]

private lemma pgPairInput_getD_pt (p l x : Fin 13) :
    (pgPairInput p l).getD x.val false = Decidable.decide (x = p) := by
  unfold pgPairInput
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (y = p)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hx, List.getElem?_eq_getElem hx,
    Option.getD_some, List.getElem_ofFn]

private lemma pgPairInput_getD_ln (p l x : Fin 13) :
    (pgPairInput p l).getD (13 + x.val) false = Decidable.decide (x = l) := by
  unfold pgPairInput
  have h1 : (List.ofFn fun y : Fin 13 => Decidable.decide (y = p)).length = 13 :=
    List.length_ofFn
  have hge : (List.ofFn fun y : Fin 13 => Decidable.decide (y = p)).length ≤ 13 + x.val := by
    omega
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (y = l)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, h1, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hx, Option.getD_some, List.getElem_ofFn]

private lemma pgQuadInput_getD_pt (Q : Finset (Fin 13)) (x : Fin 13) :
    (pgQuadInput Q).getD x.val false = Decidable.decide (x ∈ Q) := by
  unfold pgQuadInput
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (y ∈ Q)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hx, List.getElem?_eq_getElem hx,
    Option.getD_some, List.getElem_ofFn]

private lemma pgQuadInput_getD_ln (Q : Finset (Fin 13)) (x : Fin 13) :
    (pgQuadInput Q).getD (13 + x.val) false = Decidable.decide (∀ q ∈ Q, q - x ∉ pgD) := by
  unfold pgQuadInput
  have h1 : (List.ofFn fun y : Fin 13 => Decidable.decide (y ∈ Q)).length = 13 :=
    List.length_ofFn
  have hge : (List.ofFn fun y : Fin 13 => Decidable.decide (y ∈ Q)).length ≤ 13 + x.val := by
    omega
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (∀ q ∈ Q, q - y ∉ pgD)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, h1, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hx, Option.getD_some, List.getElem_ofFn]

private lemma quad_on_bit (i : Fin 26) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ (pgQuadInput Q).getD i.val false = true := by
  by_cases hi : i.val < 13
  · rcases quad_has_pt ⟨i.val, hi⟩ with ⟨Q, hQ, hp⟩
    refine ⟨Q, hQ, ?_⟩
    have hget := pgQuadInput_getD_pt Q ⟨i.val, hi⟩
    simpa [hp] using hget
  · have hl : i.val - 13 < 13 := by omega
    rcases quad_misses_line ⟨i.val - 13, hl⟩ with ⟨Q, hQ, hm⟩
    refine ⟨Q, hQ, ?_⟩
    have hget := pgQuadInput_getD_ln Q ⟨i.val - 13, hl⟩
    have heq : 13 + (i.val - 13) = i.val := by omega
    rw [heq] at hget
    rw [hget]
    exact decide_eq_true hm

private def toPt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p

private def toLn (l : Fin 13) : Fin 26 := Fin.natAdd 13 l

private def adj26 (u v : Fin 26) : Prop :=
  ∃ p l : Fin 13, p - l ∈ pgD ∧ ((u = toPt p ∧ v = toLn l) ∨ (u = toLn l ∧ v = toPt p))

private lemma toPt_val (p : Fin 13) : (toPt p).val = p.val := rfl

private lemma toLn_val (l : Fin 13) : (toLn l).val = 13 + l.val := by
  simp [toLn]
  omega

private lemma toPt_ne_toLn (p l : Fin 13) : toPt p ≠ toLn l := by
  intro h
  have hv := congrArg Fin.val h
  rw [toPt_val, toLn_val] at hv
  omega

private lemma toPt_inj {p1 p2 : Fin 13} (h : toPt p1 = toPt p2) : p1 = p2 := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [toPt_val] using hv

private lemma toLn_inj {l1 l2 : Fin 13} (h : toLn l1 = toLn l2) : l1 = l2 := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [toLn_val, toLn_val] at hv
  omega

private lemma adj26_no_c4 {c1 c2 u1 u2 : Fin 26} (hc : c1 ≠ c2) (hu : u1 ≠ u2)
    (h11 : adj26 c1 u1) (h12 : adj26 c1 u2) (h21 : adj26 c2 u1) (h22 : adj26 c2 u2) : False := by
  rcases h11 with ⟨p11, l11, hd11, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · rcases h12 with ⟨p12, l12, hd12, ⟨hp1, rfl⟩ | ⟨hbad, _⟩⟩
    · have hp : p11 = p12 := toPt_inj hp1
      subst hp
      rcases h21 with ⟨p21, l21, hd21, ⟨rfl, hl1⟩ | ⟨_, hbad⟩⟩
      · have hl : l11 = l21 := toLn_inj hl1
        subst hl
        rcases h22 with ⟨p22, l22, hd22, ⟨hp2, hl2⟩ | ⟨hbad, _⟩⟩
        · have hp' : p21 = p22 := toPt_inj hp2
          have hl' : l12 = l22 := toLn_inj hl2
          subst hp'; subst hl'
          exact pg_no_c4 p11 p21 l11 l12 (fun h => hc (congrArg toPt h))
            (fun h => hu (congrArg toLn h)) ⟨hd11, hd12, hd21, hd22⟩
        · exact toPt_ne_toLn p21 l22 hbad
      · exact toPt_ne_toLn p21 l11 hbad.symm
    · exact toPt_ne_toLn p11 l12 hbad
  · rcases h12 with ⟨p12, l12, hd12, ⟨hbad, _⟩ | ⟨hl1, rfl⟩⟩
    · exact toPt_ne_toLn p12 l11 hbad.symm
    · have hl : l11 = l12 := toLn_inj hl1
      subst hl
      rcases h21 with ⟨p21, l21, hd21, ⟨_, hbad⟩ | ⟨rfl, hp1⟩⟩
      · exact toPt_ne_toLn p11 l21 hbad
      · have hp : p11 = p21 := toPt_inj hp1
        subst hp
        rcases h22 with ⟨p22, l22, hd22, ⟨hbad, _⟩ | ⟨hl2, hp2⟩⟩
        · exact toPt_ne_toLn p22 l21 hbad.symm
        · have hl' : l21 = l22 := toLn_inj hl2
          have hp' : p12 = p22 := toPt_inj hp2
          subst hl'; subst hp'
          exact pg_no_c4 p11 p12 l11 l21 (fun h => hu (congrArg toPt h))
            (fun h => hc (congrArg toLn h)) ⟨hd11, hd21, hd12, hd22⟩

private def mkEdge (c u : Fin 26) : Fin 13 × Fin 13 :=
  if h : c.val < 13 then
    (⟨c.val, h⟩, ⟨u.val % 13, Nat.mod_lt _ (by decide)⟩)
  else
    (⟨u.val % 13, Nat.mod_lt _ (by decide)⟩, ⟨c.val % 13, Nat.mod_lt _ (by decide)⟩)

private lemma mkEdge_pt_ln (p l : Fin 13) : mkEdge (toPt p) (toLn l) = (p, l) := by
  unfold mkEdge
  have hp : (toPt p).val < 13 := p.isLt
  simp only [hp, ↓reduceDIte]
  apply Prod.ext
  · exact Fin.ext rfl
  · apply Fin.ext
    change (13 + l.val) % 13 = l.val
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt l.isLt

private lemma mkEdge_ln_pt (l p : Fin 13) : mkEdge (toLn l) (toPt p) = (p, l) := by
  unfold mkEdge
  have hl : ¬ (toLn l).val < 13 := by rw [toLn_val]; omega
  simp only [hl, ↓reduceDIte]
  apply Prod.ext
  · apply Fin.ext
    change p.val % 13 = p.val
    exact Nat.mod_eq_of_lt p.isLt
  · apply Fin.ext
    change (13 + l.val) % 13 = l.val
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt l.isLt

private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

private lemma lt_gates_of_and {C : Circuit} {j : ℕ} (hop : (gateAt C j).op = GateOp.and) :
    j < C.gates.length := by
  by_contra hge
  push Not at hge
  have hdef : gateAt C j = ⟨GateOp.or, []⟩ := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl
  rw [hdef] at hop
  cases hop

private lemma gateOp_and_or {C : Circuit} (hMono : Monotone2 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  have h := (hMono (gateAt C j) (gateAt_mem hj)).1
  simpa using h

private lemma gate_inputs_len_le {C : Circuit} (hMono : Monotone2 C) {j : ℕ}
    (hj : j < C.gates.length) :
    (gateAt C j).inputs.length ≤ 2 :=
  (hMono (gateAt C j) (gateAt_mem hj)).2

private lemma wires_length (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_append_length _ C.gates inp

private lemma wires_getD_ge (C : Circuit) (inp : List Bool) {w : ℕ}
    (hw : inp.length + C.gates.length ≤ w) :
    (C.wires inp).getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wires_length]; exact hw

private lemma wires_getD_input (C : Circuit) (inp : List Bool) {w : ℕ} (hw : w < inp.length) :
    (C.wires inp).getD w false = inp.getD w false := by
  unfold Circuit.wires
  exact foldl_append_getD_lt _ C.gates inp false w hw

private lemma wires_getD_gate {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    (inp : List Bool) (hlen : inp.length = n) {j : ℕ} (hj : j < C.gates.length) :
    (C.wires inp).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => (C.wires inp).getD w false) := by
  unfold Circuit.wires
  have hgate := foldl_append_getD_gate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates inp false j hj ⟨GateOp.or, []⟩
  rw [hlen] at hgate
  rw [hgate]
  change (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          inp).getD i false) =
    (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          inp).getD i false)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < inp.length + j := by
    rw [hlen]
    exact hRB j hj i hi
  exact foldl_append_take_getD _ C.gates inp false j i (Nat.le_of_lt hj) hilt

private lemma orSets_length (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  rw [foldl_append_length]
  simp

private lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [orSets_length]; exact hj

private lemma orSets_getD_lt_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = _
  rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
  congr 1
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma orSets_getD_lt_not_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = [j]
  rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]

private lemma orReaches_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ u ∈ (gateAt C j).inputs, OrReaches n C u g)) := by
  constructor
  · rintro ⟨hnw, hmem⟩
    have hlt : w - n < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [orSets_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨w - n, hlt, by omega, ?_⟩
    by_cases hop : (gateAt C (w - n)).op = GateOp.or
    · rw [orSets_getD_lt_or n C hlt hop, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨u, hu, hgu⟩
        rw [List.mem_filter, decide_eq_true_eq] at hu
        exact ⟨hop, u, hu.1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, u, hu, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨u, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨hu, hnu, hRB j hj u hu⟩

private lemma orReaches_self {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hRB (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

private lemma orReaches_le {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, u, hu, hug⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : u < n + j := hRB j hj u hu
      have hrec := ih _ hlt g hug
      exact ⟨by omega, hrec.2⟩

private lemma orReaches_trans {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ w g h : ℕ, OrReaches n C w g → OrReaches n C (n + g) h → OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g h hwg hgh
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
    · exact hgh
    · have hrec := ih _ (hRB j hj u hu) g h hug hgh
      exact (orReaches_iff hRB (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, u, hu, hrec⟩⟩

private lemma orReaches_parent {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      w = n + g ∨
        ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧ OrReaches n C w h ∧
          n + g ∈ (gateAt C h).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
    · exact Or.inl rfl
    · right
      rcases ih _ (hRB j hj u hu) g hug with rfl | ⟨h, hh, hhop, hreach, hmem⟩
      · exact ⟨j, hj, hop, orReaches_self hRB hj, hu⟩
      · exact ⟨h, hh, hhop,
          (orReaches_iff hRB (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, u, hu, hreach⟩⟩, hmem⟩

private lemma wires_true_of_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    (inp : List Bool) (hlen : inp.length = n) :
    ∀ w g : ℕ, OrReaches n C w g →
      (C.wires inp).getD (n + g) false = true → (C.wires inp).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg hg
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
    · exact hg
    · have hut : (C.wires inp).getD u false = true := ih u (hRB j hj u hu) g hug hg
      rw [wires_getD_gate hRB inp hlen hj, hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
      exact ⟨u, hu, hut⟩

private lemma cones_length (n : ℕ) (C : Circuit) :
    (cones n C).length = C.gates.length := by
  unfold cones coneStep
  rw [foldl_append_length]
  simp

private lemma cones_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (cones n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [cones_length]; exact hj

private lemma cones_getD_lt (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  unfold cones coneStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) =>
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change (((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
      (fun w => (w - n) :: pre.getD (w - n) [])) = _
  rw [hprelen]
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  congr 1
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma inCone_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (i j : ℕ) :
    InCone n C i j ↔
      j < C.gates.length ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  constructor
  · intro hmem
    have hj : j < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [cones_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨hj, ?_⟩
    rw [cones_getD_lt n C hj, List.mem_flatMap] at hmem
    rcases hmem with ⟨w, hw, hiw⟩
    rw [List.mem_filter, decide_eq_true_eq] at hw
    rw [List.mem_cons] at hiw
    exact ⟨w, hw.1, hw.2.1, hiw⟩
  · rintro ⟨hj, w, hw, hnw, hiw⟩
    rw [cones_getD_lt n C hj, List.mem_flatMap]
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨hw, hnw, hRB j hj w hw⟩
    · rw [List.mem_cons]
      exact hiw

private lemma inCone_lt {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ j i : ℕ, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hij
    rw [inCone_iff hRB] at hij
    rcases hij with ⟨hj, w, hw, hnw, rfl | hrec⟩
    · have hwlt := hRB j hj w hw
      exact ⟨by omega, hj⟩
    · have hwlt := hRB j hj w hw
      have hsub := ih (w - n) (by omega) i hrec
      exact ⟨by omega, hj⟩

private lemma inCone_trans {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ c a b : ℕ, InCone n C a b → InCone n C b c → InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    intro a b hab hbc
    rw [inCone_iff hRB] at hbc
    rcases hbc with ⟨hc, w, hw, hnw, rfl | hrec⟩
    · exact (inCone_iff hRB a c).mpr ⟨hc, w, hw, hnw, Or.inr hab⟩
    · have hwlt := hRB c hc w hw
      have hsub := ih (w - n) (by omega) a b hab hrec
      exact (inCone_iff hRB a c).mpr ⟨hc, w, hw, hnw, Or.inr hsub⟩

private lemma inCone_of_orReaches_ne {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ j i : ℕ, OrReaches n C (n + j) i → i ≠ j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hji hne
    rw [orReaches_iff hRB] at hji
    rcases hji with ⟨j', hj', heq, rfl | ⟨_, u, hu, hui⟩⟩
    · exact absurd (by omega) hne
    · rcases (by omega : j = j') with rfl
      have hnu : n ≤ u := hui.1
      have hult : u < n + j := hRB j hj' u hu
      by_cases hiu : i = u - n
      · exact (inCone_iff hRB i j).mpr ⟨hj', u, hu, hnu, Or.inl hiu⟩
      · have hui' : OrReaches n C (n + (u - n)) i := by
          have : n + (u - n) = u := by omega
          rwa [this]
        have hsub := ih (u - n) (by omega) i hui' hiu
        exact (inCone_iff hRB i j).mpr ⟨hj', u, hu, hnu, Or.inr hsub⟩

private lemma inCone_of_input_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    {j w i : ℕ} (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs)
    (hwi : OrReaches n C w i) :
    InCone n C i j := by
  have hnw : n ≤ w := hwi.1
  by_cases hiw : i = w - n
  · exact (inCone_iff hRB i j).mpr ⟨hj, w, hw, hnw, Or.inl hiw⟩
  · have hwi' : OrReaches n C (n + (w - n)) i := by
      have : n + (w - n) = w := by omega
      rwa [this]
    exact (inCone_iff hRB i j).mpr ⟨hj, w, hw, hnw, Or.inr (inCone_of_orReaches_ne hRB (w - n) i hwi' hiw)⟩

private lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) :
    orIn n C i.val = {i} := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (hu | ⟨k, _, ⟨hni, _⟩, _, _⟩)
    · exact Fin.ext hu
    · omega
  · rintro rfl
    exact Or.inl rfl

private lemma orIn_ge {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hRB] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

private lemma orIn_and {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hRB] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

private lemma mem_orIn_or {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (u : Fin n) :
    u ∈ orIn n C (n + j) ↔ ∃ w ∈ (gateAt C j).inputs, u ∈ orIn n C w := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hRB] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, w, hw, hwk⟩
      · exact ⟨u.val, huk, Or.inl rfl⟩
      · exact ⟨w, hw, Or.inr ⟨k, hk, hwk, hkop, huk⟩⟩
  · rintro ⟨w, hw, hEq | ⟨k, hk, hwk, hkop, huk⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hRB hj, hop, ?_⟩
      rwa [hEq]
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hRB (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, w, hw, hwk⟩⟩

private lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    {w g : ℕ} (hwg : OrReaches n C w g) :
    orIn n C (n + g) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hEq | ⟨k, hk, hgk, hkop, huk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans hRB w g k hwg hgk, hkop, huk⟩

private lemma wires_true_of_mem_orIn {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    (inp : List Bool) (hlen : inp.length = n) {w : ℕ} {i : Fin n}
    (hi : i ∈ orIn n C w) (hit : inp.getD i.val false = true) :
    (C.wires inp).getD w false = true := by
  unfold orIn at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with rfl | ⟨k, hk, hwk, hkop, hik⟩
  · rw [wires_getD_input C inp (hlen.symm ▸ i.isLt)]
    exact hit
  · apply wires_true_of_orReaches hRB inp hlen w k hwk
    rw [wires_getD_gate hRB inp hlen hk, hkop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    refine ⟨i.val, hik, ?_⟩
    rw [wires_getD_input C inp (hlen.symm ▸ i.isLt)]
    exact hit

private lemma wires_true_decomp {n : ℕ} {C : Circuit}
    (hMono : Monotone2 C) (hRB : ReadsBack n C)
    (inp : List Bool) (hlen : inp.length = n) :
    ∀ w : ℕ, (C.wires inp).getD w false = true →
      (∃ i ∈ orIn n C w, inp.getD i.val false = true) ∨
      (∃ g : ℕ, (gateAt C g).op = GateOp.and ∧ OrReaches n C w g ∧
        (C.wires inp).getD (n + g) false = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwt
    by_cases hlt : w < n
    · left
      refine ⟨⟨w, hlt⟩, ?_, ?_⟩
      · rw [orIn_input ⟨w, hlt⟩]; exact Finset.mem_singleton_self _
      · rwa [wires_getD_input C inp (hlen.symm ▸ hlt)] at hwt
    · by_cases hge : n + C.gates.length ≤ w
      · exfalso
        have hf : (C.wires inp).getD w false = false :=
          wires_getD_ge C inp (by omega)
        rw [hf] at hwt
        cases hwt
      · set j := w - n
        have hwj : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hwj] at hwt ⊢
        rcases gateOp_and_or hMono hj with hand | hor
        · exact Or.inr ⟨j, hand, orReaches_self hRB hj, hwt⟩
        · rw [wires_getD_gate hRB inp hlen hj, hor] at hwt
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and] at hwt
          rcases hwt with ⟨u, hu, hut⟩
          have hult : u < w := by
            have := hRB j hj u hu
            omega
          rcases ih u hult hut with ⟨i, hi, hit⟩ | ⟨g, hgop, hug, hgt⟩
          · exact Or.inl ⟨i, (mem_orIn_or hRB hj hor i).mpr ⟨u, hu, hi⟩, hit⟩
          · exact Or.inr ⟨g, hgop, (orReaches_iff hRB (n + j) g).mpr
              ⟨j, hj, rfl, Or.inr ⟨hor, u, hu, hug⟩⟩, hgt⟩

private lemma wires_iff_orIn_inCone {n : ℕ} {C : Circuit}
    (hMono : Monotone2 C) (hRB : ReadsBack n C)
    (hNoAnd : ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone n C i j)
    {g : ℕ} (hgop : (gateAt C g).op = GateOp.and)
    (inp : List Bool) (hlen : inp.length = n) :
    ∀ w : ℕ, (w < n ∨ (n ≤ w ∧ InCone n C (w - n) g)) →
      ((C.wires inp).getD w false = true ↔ ∃ i ∈ orIn n C w, inp.getD i.val false = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases hw with hlt | ⟨hnw, hcone⟩
    · rw [wires_getD_input C inp (hlen.symm ▸ hlt)]
      have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
      rw [heq]
      simp
    · set k := w - n
      have hwk : w = n + k := by omega
      have hkt := inCone_lt hRB g k hcone
      have hk : k < C.gates.length := by omega
      have hkop : (gateAt C k).op = GateOp.or := by
        rcases gateOp_and_or hMono hk with hand | hor
        · exfalso
          exact hNoAnd ⟨k, g, hand, hgop, hcone⟩
        · exact hor
      rw [hwk, wires_getD_gate hRB inp hlen hk, hkop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
      constructor
      · rintro ⟨u, hu, hut⟩
        have hult : u < w := by
          have := hRB k hk u hu
          omega
        have hucond : u < n ∨ (n ≤ u ∧ InCone n C (u - n) g) := by
          by_cases h1 : u < n
          · exact Or.inl h1
          · right
            refine ⟨by omega, ?_⟩
            have hku : InCone n C (u - n) k :=
              (inCone_iff hRB (u - n) k).mpr ⟨hk, u, hu, by omega, Or.inl rfl⟩
            exact inCone_trans hRB g (u - n) k hku hcone
        rcases (ih u hult hucond).mp hut with ⟨i, hi, hit⟩
        exact ⟨i, (mem_orIn_or hRB hk hkop i).mpr ⟨u, hu, hi⟩, hit⟩
      · rintro ⟨i, hi, hit⟩
        rcases (mem_orIn_or hRB hk hkop i).mp hi with ⟨u, hu, hui⟩
        have hult : u < w := by
          have := hRB k hk u hu
          omega
        have hucond : u < n ∨ (n ≤ u ∧ InCone n C (u - n) g) := by
          by_cases h1 : u < n
          · exact Or.inl h1
          · right
            refine ⟨by omega, ?_⟩
            have hku : InCone n C (u - n) k :=
              (inCone_iff hRB (u - n) k).mpr ⟨hk, u, hu, by omega, Or.inl rfl⟩
            exact inCone_trans hRB g (u - n) k hku hcone
        exact ⟨u, hu, (ih u hult hucond).mpr ⟨i, hui, hit⟩⟩

private lemma and_gate_eval_iff {n : ℕ} {C : Circuit}
    (hMono : Monotone2 C) (hRB : ReadsBack n C)
    (hNoAnd : ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone n C i j)
    {g : ℕ} (hgop : (gateAt C g).op = GateOp.and)
    (inp : List Bool) (hlen : inp.length = n) :
    (C.wires inp).getD (n + g) false = true ↔
      ∀ w ∈ (gateAt C g).inputs, ∃ i ∈ orIn n C w, inp.getD i.val false = true := by
  have hg : g < C.gates.length := lt_gates_of_and hgop
  rw [wires_getD_gate hRB inp hlen hg, hgop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h w hw
    have hwcond : w < n ∨ (n ≤ w ∧ InCone n C (w - n) g) := by
      by_cases h1 : w < n
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, (inCone_iff hRB (w - n) g).mpr ⟨hg, w, hw, by omega, Or.inl rfl⟩⟩
    exact (wires_iff_orIn_inCone hMono hRB hNoAnd hgop inp hlen w hwcond).mp (h w hw)
  · intro h w hw
    have hwcond : w < n ∨ (n ≤ w ∧ InCone n C (w - n) g) := by
      by_cases h1 : w < n
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, (inCone_iff hRB (w - n) g).mpr ⟨hg, w, hw, by omega, Or.inl rfl⟩⟩
    exact (wires_iff_orIn_inCone hMono hRB hNoAnd hgop inp hlen w hwcond).mpr (h w hw)

private lemma append_bit_length (inp : List Bool) (bit : Bool) (h : inp.length = 26) :
    (inp ++ [bit]).length = 27 := by simp [h]

private lemma getD_append_bit_lt (inp : List Bool) (bit : Bool) {i : ℕ} (hi : i < inp.length) :
    (inp ++ [bit]).getD i false = inp.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_bit_last (inp : List Bool) (bit : Bool) (h : inp.length = 26) :
    (inp ++ [bit]).getD 26 false = bit := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), h]
  rfl

private lemma quad_on_active_bit (inp : List Bool) (bit : Bool) (hlen : inp.length = 26)
    (i : Fin 27) (hit : (inp ++ [bit]).getD i.val false = true) :
    ∃ Q, isQuad Q ∧ (pgQuadInput Q ++ [bit]).getD i.val false = true := by
  by_cases hi : i.val < 26
  · rcases quad_on_bit ⟨i.val, hi⟩ with ⟨Q, hQ, hget⟩
    exact ⟨Q, hQ, (getD_append_bit_lt _ _ (by rw [pgQuadInput_length]; exact hi)).trans hget⟩
  · have hv : i.val = 26 := by omega
    rw [hv, getD_append_bit_last _ _ hlen] at hit
    refine ⟨baseQuad 0, baseQuad_isQuad 0, ?_⟩
    rw [hv, getD_append_bit_last _ _ (pgQuadInput_length _)]
    exact hit

-- Project each OR cone onto the point and line inputs.
private def liveOrIn (C : Circuit) (w : ℕ) : Finset (Fin 26) :=
  Finset.univ.filter fun i : Fin 26 => i.castSucc ∈ orIn 27 C w

private lemma mem_liveOrIn {C : Circuit} {w : ℕ} {i : Fin 26} :
    i ∈ liveOrIn C w ↔ i.castSucc ∈ orIn 27 C w := by
  simp [liveOrIn]

private lemma mem_liveOrIn_or {C : Circuit} (hRB : ReadsBack 27 C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (u : Fin 26) :
    u ∈ liveOrIn C (27 + j) ↔ ∃ w ∈ (gateAt C j).inputs, u ∈ liveOrIn C w := by
  simpa only [mem_liveOrIn] using mem_orIn_or hRB hj hop u.castSucc

private lemma liveOrIn_subset {C : Circuit} (hRB : ReadsBack 27 C)
    {w g : ℕ} (hwg : OrReaches 27 C w g) : liveOrIn C (27 + g) ⊆ liveOrIn C w :=
  fun _ hu => mem_liveOrIn.mpr (orIn_subset_of_orReaches hRB hwg (mem_liveOrIn.mp hu))

private lemma liveOrIn_ge {C : Circuit} (hRB : ReadsBack 27 C) {w : ℕ}
    (hw : 27 + C.gates.length ≤ w) : liveOrIn C w = ∅ := by
  simp [liveOrIn, orIn_ge hRB hw]

private lemma liveOrIn_and {C : Circuit} (hRB : ReadsBack 27 C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    liveOrIn C (27 + j) = ∅ := by
  simp [liveOrIn, orIn_and hRB hj hop]

private lemma liveOrIn_card_le_one {C : Circuit} {w : ℕ} (hw : w < 27) :
    (liveOrIn C w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have h : orIn 27 C w = {⟨w, hw⟩} := orIn_input ⟨w, hw⟩
  rw [mem_liveOrIn, h, Finset.mem_singleton] at ha hb
  exact Fin.ext (congrArg (fun z : Fin 27 => z.val) (ha.trans hb.symm))

private lemma live_hit_extend {C : Circuit} {w : ℕ} {inp : List Bool} {bit : Bool}
    (hlen : inp.length = 26)
    (h : ∃ i ∈ liveOrIn C w, inp.getD i.val false = true) :
    ∃ i ∈ orIn 27 C w, (inp ++ [bit]).getD i.val false = true := by
  rcases h with ⟨i, hi, hit⟩
  exact ⟨i.castSucc, mem_liveOrIn.mp hi,
    (getD_append_bit_lt inp bit (by rw [hlen]; exact i.isLt)).trans hit⟩

private lemma live_hit_of_active {C : Circuit} {w : ℕ} {inp : List Bool} {bit : Bool}
    (hlen : inp.length = 26)
    (h : ∃ i ∈ orIn 27 C w, (inp ++ [bit]).getD i.val false = true)
    (hlive : ∀ i ∈ orIn 27 C w, (inp ++ [bit]).getD i.val false = true → i.val < 26) :
    ∃ i ∈ liveOrIn C w, inp.getD i.val false = true := by
  rcases h with ⟨i, hi, hit⟩
  have hi26 := hlive i hi hit
  let j : Fin 26 := ⟨i.val, hi26⟩
  have hj : j.castSucc = i := Fin.ext rfl
  refine ⟨j, mem_liveOrIn.mpr (hj ▸ hi), ?_⟩
  rw [getD_append_bit_lt inp bit (by omega : i.val < inp.length)] at hit
  exact hit

open Classical in
private noncomputable def bigOrReach (C : Circuit) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun g =>
    (gateAt C g).op = GateOp.or ∧ 2 ≤ (liveOrIn C (27 + g)).card ∧ ∃ w ∈ W, OrReaches 27 C w g

private lemma leaf_count_bound {C : Circuit} (hMono : Monotone2 C) (hRB : ReadsBack 27 C) :
    ∀ k : ℕ, ∀ W : Finset ℕ, (bigOrReach C W).card = k →
      (W.biUnion (liveOrIn C)).card ≤ W.card + k := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W hk
    by_cases hne : (bigOrReach C W).Nonempty
    · set M := bigOrReach C W
      set m := M.max' hne
      have hmM : m ∈ M := Finset.max'_mem M hne
      have hm_props : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
          2 ≤ (liveOrIn C (27 + m)).card ∧ ∃ w ∈ W, OrReaches 27 C w m := by
        simpa [M, bigOrReach, Finset.mem_filter, Finset.mem_range] using hmM
      have hmax_unique : ∀ w ∈ W, OrReaches 27 C w m → w = 27 + m := by
        intro w hw hwm
        have hle := orReaches_le hRB w m hwm
        rw [orReaches_iff hRB] at hwm
        rcases hwm with ⟨j, hj, rfl, hcase⟩
        by_contra hne_w
        have hmj : m ≠ j := fun h => hne_w (by omega)
        rcases hcase with hEq | ⟨hjop, u, hu, hug⟩
        · exact hmj hEq
        · have hjM : j ∈ M := by
            simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
            refine ⟨hj, hjop, ?_, 27 + j, hw, orReaches_self hRB hj⟩
            have hsub : liveOrIn C (27 + m) ⊆ liveOrIn C (27 + j) :=
              liveOrIn_subset hRB
                ((orReaches_iff hRB (27 + j) m).mpr ⟨j, hj, rfl, Or.inr ⟨hjop, u, hu, hug⟩⟩)
            exact le_trans hm_props.2.2.1 (Finset.card_le_card hsub)
          have hjle : j ≤ m := Finset.le_max' M j hjM
          omega
      have hnmW : 27 + m ∈ W := by
        rcases hm_props.2.2.2 with ⟨w, hw, hwm⟩
        rwa [hmax_unique w hw hwm] at hw
      set W' : Finset ℕ := (gateAt C m).inputs.toFinset ∪ (W.erase (27 + m))
      have hbi : W.biUnion (liveOrIn C) ⊆ W'.biUnion (liveOrIn C) := by
        intro u hu
        rw [Finset.mem_biUnion] at hu ⊢
        rcases hu with ⟨w, hw, huw⟩
        by_cases hwm : w = 27 + m
        · subst hwm
          rcases (mem_liveOrIn_or hRB hm_props.1 hm_props.2.1 u).mp huw with ⟨v, hv, huv⟩
          exact ⟨v, Finset.mem_union_left _ (List.mem_toFinset.mpr hv), huv⟩
        · exact ⟨w, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hwm, hw⟩), huw⟩
      have hW'card : W'.card ≤ W.card + 1 := by
        have h1 : W'.card ≤ (gateAt C m).inputs.toFinset.card + (W.erase (27 + m)).card :=
          Finset.card_union_le _ _
        have h2 : (gateAt C m).inputs.toFinset.card ≤ (gateAt C m).inputs.length :=
          List.toFinset_card_le _
        have h3 : (gateAt C m).inputs.length ≤ 2 := gate_inputs_len_le hMono hm_props.1
        have h4 : (W.erase (27 + m)).card + 1 = W.card := Finset.card_erase_add_one hnmW
        omega
      have hM'sub : bigOrReach C W' ⊆ M.erase m := by
        intro g hg
        simp only [bigOrReach, Finset.mem_filter, Finset.mem_range] at hg
        rcases hg with ⟨hglt, hgop, hgcard, w', hw', hw'g⟩
        rw [Finset.mem_erase]
        have hgM : g ∈ M := by
          simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
          refine ⟨hglt, hgop, hgcard, ?_⟩
          rw [Finset.mem_union] at hw'
          rcases hw' with hmem | herase
          · rw [List.mem_toFinset] at hmem
            exact ⟨27 + m, hnmW,
              (orReaches_iff hRB (27 + m) g).mpr ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, w', hmem, hw'g⟩⟩⟩
          · exact ⟨w', (Finset.mem_erase.mp herase).2, hw'g⟩
        refine ⟨?_, hgM⟩
        intro hgm
        subst hgm
        rw [Finset.mem_union] at hw'
        rcases hw' with hmem | herase
        · rw [List.mem_toFinset] at hmem
          have hle := (orReaches_le hRB _ _ hw'g).1
          have hlt := hRB m hm_props.1 w' hmem
          omega
        · rcases Finset.mem_erase.mp herase with ⟨hne', hw'W⟩
          exact hne' (hmax_unique w' hw'W hw'g)
      have hM'card_le : (bigOrReach C W').card ≤ (M.erase m).card :=
        Finset.card_le_card hM'sub
      have hMerase : (M.erase m).card + 1 = k := by
        rw [Finset.card_erase_add_one hmM, hk]
      have hM'lt : (bigOrReach C W').card < k := by omega
      have hrec := ih _ hM'lt W' rfl
      have hbi_card : (W.biUnion (liveOrIn C)).card ≤ (W'.biUnion (liveOrIn C)).card :=
        Finset.card_le_card hbi
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hle1 : ∀ w ∈ W, (liveOrIn C w).card ≤ 1 := by
        intro w hw
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ (liveOrIn C w).card := hgt
        by_cases hlt : w < 27
        · have hle := liveOrIn_card_le_one (C := C) (w := w) hlt
          omega
        · by_cases hge : 27 + C.gates.length ≤ w
          · rw [liveOrIn_ge hRB hge, Finset.card_empty] at hge2
            omega
          · set j := w - 27
            have hwEq : w = 27 + j := by omega
            have hj : j < C.gates.length := by omega
            rw [hwEq] at hge2 hw
            rcases gateOp_and_or hMono hj with hop | hop
            · rw [liveOrIn_and hRB hj hop, Finset.card_empty] at hge2
              omega
            · have hjM : j ∈ bigOrReach C W := by
                simp only [bigOrReach, Finset.mem_filter, Finset.mem_range]
                exact ⟨hj, hop, hge2, 27 + j, hw, orReaches_self hRB hj⟩
              rw [hne] at hjM
              simp at hjM
      have hbi : (W.biUnion (liveOrIn C)).card ≤ ∑ w ∈ W, (liveOrIn C w).card :=
        Finset.card_biUnion_le
      have hsum : ∑ w ∈ W, (liveOrIn C w).card ≤ ∑ _w ∈ W, 1 :=
        Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      omega

private lemma clean_and_structure {C : Circuit} {bit : Bool}
    (hMono : Monotone2 C) (hRB : ReadsBack 27 C)
    (hNoAnd : ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 27 C i j)
    {g : ℕ} (hgop : (gateAt C g).op = GateOp.and)
    (hquad : ∀ Q : Finset (Fin 13), isQuad Q → (C.wires (pgQuadInput Q ++ [bit])).getD (27 + g) false = false)
    (hpos : ∃ p l : Fin 13, p - l ∈ pgD ∧ (C.wires (pgPairInput p l ++ [bit])).getD (27 + g) false = true) :
    ∃ (c : Fin 26) (w : ℕ), w ∈ (gateAt C g).inputs ∧
      (∀ u ∈ liveOrIn C w, adj26 c u) ∧
      (∀ p l : Fin 13, (C.wires (pgPairInput p l ++ [bit])).getD (27 + g) false = true →
        (c = toPt p ∧ toLn l ∈ liveOrIn C w) ∨ (c = toLn l ∧ toPt p ∈ liveOrIn C w)) := by
  have hg : g < C.gates.length := lt_gates_of_and hgop
  have hlen : (gateAt C g).inputs.length ≤ 2 := gate_inputs_len_le hMono hg

  have eval_quad_false : ∀ Q : Finset (Fin 13), isQuad Q →
      ¬ ∀ w ∈ (gateAt C g).inputs, ∃ i ∈ orIn 27 C w,
        (pgQuadInput Q ++ [bit]).getD i.val false = true := by
    intro Q hQ hall
    have ht := (and_gate_eval_iff hMono hRB hNoAnd hgop _ (append_bit_length _ _ (pgQuadInput_length Q))).mpr hall
    have hf := hquad Q hQ
    rw [ht] at hf
    cases hf
  rcases h : (gateAt C g).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · exfalso
    apply eval_quad_false (baseQuad 0) (baseQuad_isQuad 0)
    intro w hw
    rw [h] at hw
    cases hw
  · exfalso
    rcases hpos with ⟨p0, l0, _, hpt⟩
    have ha := (and_gate_eval_iff hMono hRB hNoAnd hgop _ (append_bit_length _ _ (pgPairInput_length p0 l0))).mp hpt
    rw [h] at ha
    rcases ha a (List.mem_singleton_self a) with ⟨i, hi, hit⟩
    rcases quad_on_active_bit _ _ (pgPairInput_length p0 l0) i hit with ⟨Q, hQ, hQi⟩
    apply eval_quad_false Q hQ
    intro w hw
    rw [h, List.mem_singleton] at hw
    subst hw
    exact ⟨i, hi, hQi⟩
  · have hquad_full : ∀ Q, isQuad Q →
        ¬ ((∃ i ∈ orIn 27 C a, (pgQuadInput Q ++ [bit]).getD i.val false = true) ∧
           (∃ j ∈ orIn 27 C b, (pgQuadInput Q ++ [bit]).getD j.val false = true)) := by
      intro Q hQ ⟨hi, hj⟩
      apply eval_quad_false Q hQ
      intro w hw
      rw [h] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hi
      · exact hj
    have hquad_ab : ∀ Q, isQuad Q →
        ¬ ((∃ i ∈ liveOrIn C a, (pgQuadInput Q).getD i.val false = true) ∧
           (∃ j ∈ liveOrIn C b, (pgQuadInput Q).getD j.val false = true)) := by
      intro Q hQ ⟨hi, hj⟩
      exact hquad_full Q hQ
        ⟨live_hit_extend (pgQuadInput_length Q) hi, live_hit_extend (pgQuadInput_length Q) hj⟩
    have hpair_ab : ∀ p l : Fin 13, (C.wires (pgPairInput p l ++ [bit])).getD (27 + g) false = true ↔
        (∃ i ∈ liveOrIn C a, (pgPairInput p l).getD i.val false = true) ∧
        (∃ j ∈ liveOrIn C b, (pgPairInput p l).getD j.val false = true) := by
      intro p l
      rw [and_gate_eval_iff hMono hRB hNoAnd hgop _ (append_bit_length _ _ (pgPairInput_length p l)), h]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      constructor
      · rintro ⟨ha, hb⟩
        -- A true fixed input would also activate this operand on the other operand's rejecting test.
        have no_last : ∀ i : Fin 27, (pgPairInput p l ++ [bit]).getD i.val false = true →
            ¬ i.val < 26 → ∀ Q, (pgQuadInput Q ++ [bit]).getD i.val false = true := by
          intro i hit hi Q
          have hv : i.val = 26 := by omega
          rw [hv, getD_append_bit_last _ _ (pgPairInput_length p l)] at hit
          rw [hv, getD_append_bit_last _ _ (pgQuadInput_length Q)]
          exact hit
        refine ⟨live_hit_of_active (pgPairInput_length p l) ha ?_,
          live_hit_of_active (pgPairInput_length p l) hb ?_⟩
        · intro i hi hit
          by_contra hlast
          rcases hb with ⟨j, hj, hjt⟩
          rcases quad_on_active_bit _ _ (pgPairInput_length p l) j hjt with ⟨Q, hQ, hQj⟩
          exact hquad_full Q hQ ⟨⟨i, hi, no_last i hit hlast Q⟩, ⟨j, hj, hQj⟩⟩
        · intro j hj hjt
          by_contra hlast
          rcases ha with ⟨i, hi, hit⟩
          rcases quad_on_active_bit _ _ (pgPairInput_length p l) i hit with ⟨Q, hQ, hQi⟩
          exact hquad_full Q hQ ⟨⟨i, hi, hQi⟩, ⟨j, hj, no_last j hjt hlast Q⟩⟩
      · rintro ⟨ha, hb⟩
        exact ⟨live_hit_extend (pgPairInput_length p l) ha, live_hit_extend (pgPairInput_length p l) hb⟩
    have hne : (liveOrIn C a).Nonempty ∧ (liveOrIn C b).Nonempty := by
      rcases hpos with ⟨p0, l0, _, hpt⟩
      rcases (hpair_ab p0 l0).mp hpt with ⟨⟨i, hi, _⟩, ⟨j, hj, _⟩⟩
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have hno_two_pts : ∀ p1 p2 : Fin 13, toPt p1 ∈ liveOrIn C a → toPt p2 ∈ liveOrIn C b → False := by
      intro p1 p2 hp1 hp2
      by_cases heq : p1 = p2
      · subst heq
        rcases quad_has_pt p1 with ⟨Q, hQ, hmem⟩
        apply hquad_ab Q hQ
        have hv : (pgQuadInput Q).getD (toPt p1).val false = true := by
          rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem
        exact ⟨⟨toPt p1, hp1, hv⟩, ⟨toPt p1, hp2, hv⟩⟩
      · rcases quad_has_two_pts heq with ⟨Q, hQ, hmem1, hmem2⟩
        apply hquad_ab Q hQ
        have hv1 : (pgQuadInput Q).getD (toPt p1).val false = true := by
          rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem1
        have hv2 : (pgQuadInput Q).getD (toPt p2).val false = true := by
          rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem2
        exact ⟨⟨toPt p1, hp1, hv1⟩, ⟨toPt p2, hp2, hv2⟩⟩
    have hno_two_lns : ∀ l1 l2 : Fin 13, toLn l1 ∈ liveOrIn C a → toLn l2 ∈ liveOrIn C b → False := by
      intro l1 l2 hl1 hl2
      by_cases heq : l1 = l2
      · subst heq
        rcases quad_misses_line l1 with ⟨Q, hQ, hm⟩
        apply hquad_ab Q hQ
        have hv : (pgQuadInput Q).getD (toLn l1).val false = true := by
          rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm
        exact ⟨⟨toLn l1, hl1, hv⟩, ⟨toLn l1, hl2, hv⟩⟩
      · rcases quad_misses_two_lines heq with ⟨Q, hQ, hm1, hm2⟩
        apply hquad_ab Q hQ
        have hv1 : (pgQuadInput Q).getD (toLn l1).val false = true := by
          rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm1
        have hv2 : (pgQuadInput Q).getD (toLn l2).val false = true := by
          rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm2
        exact ⟨⟨toLn l1, hl1, hv1⟩, ⟨toLn l2, hl2, hv2⟩⟩
    have hcross_adj : ∀ i ∈ liveOrIn C a, ∀ j ∈ liveOrIn C b, adj26 i j := by
      intro i hi j hj
      by_cases h1 : i.val < 13
      · have hiEq : i = toPt ⟨i.val, h1⟩ := Fin.ext rfl
        rw [hiEq] at hi ⊢
        by_cases h2 : j.val < 13
        · have hjEq : j = toPt ⟨j.val, h2⟩ := Fin.ext rfl
          rw [hjEq] at hj
          exact False.elim (hno_two_pts _ _ hi hj)
        · have hjEq : j = toLn ⟨j.val - 13, by omega⟩ := by
            apply Fin.ext; rw [toLn_val]; dsimp; omega
          rw [hjEq] at hj ⊢
          have hinc : ⟨i.val, h1⟩ - ⟨j.val - 13, by omega⟩ ∈ pgD := by
            by_contra hni
            rcases quad_noninc hni with ⟨Q, hQ, hmem, hm⟩
            apply hquad_ab Q hQ
            have hv1 : (pgQuadInput Q).getD (toPt ⟨i.val, h1⟩).val false = true := by
              rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem
            have hv2 : (pgQuadInput Q).getD (toLn ⟨j.val - 13, by omega⟩).val false = true := by
              rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm
            exact ⟨⟨toPt ⟨i.val, h1⟩, hi, hv1⟩, ⟨toLn ⟨j.val - 13, by omega⟩, hj, hv2⟩⟩
          exact ⟨⟨i.val, h1⟩, ⟨j.val - 13, by omega⟩, hinc, Or.inl ⟨rfl, rfl⟩⟩
      · have hiEq : i = toLn ⟨i.val - 13, by omega⟩ := by
          apply Fin.ext; rw [toLn_val]; dsimp; omega
        rw [hiEq] at hi ⊢
        by_cases h2 : j.val < 13
        · have hjEq : j = toPt ⟨j.val, h2⟩ := Fin.ext rfl
          rw [hjEq] at hj ⊢
          have hinc : ⟨j.val, h2⟩ - ⟨i.val - 13, by omega⟩ ∈ pgD := by
            by_contra hni
            rcases quad_noninc hni with ⟨Q, hQ, hmem, hm⟩
            apply hquad_ab Q hQ
            have hv1 : (pgQuadInput Q).getD (toLn ⟨i.val - 13, by omega⟩).val false = true := by
              rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm
            have hv2 : (pgQuadInput Q).getD (toPt ⟨j.val, h2⟩).val false = true := by
              rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem
            exact ⟨⟨toLn ⟨i.val - 13, by omega⟩, hi, hv1⟩, ⟨toPt ⟨j.val, h2⟩, hj, hv2⟩⟩
          exact ⟨⟨j.val, h2⟩, ⟨i.val - 13, by omega⟩, hinc, Or.inr ⟨rfl, rfl⟩⟩
        · have hjEq : j = toLn ⟨j.val - 13, by omega⟩ := by
            apply Fin.ext; rw [toLn_val]; dsimp; omega
          rw [hjEq] at hj
          exact False.elim (hno_two_lns _ _ hi hj)
    have hcard_one : (liveOrIn C a).card = 1 ∨ (liveOrIn C b).card = 1 := by
      by_contra hboth
      push Not at hboth
      have h1a : 1 < (liveOrIn C a).card := by
        have hposa := Finset.card_pos.mpr hne.1
        omega
      have h1b : 1 < (liveOrIn C b).card := by
        have hposb := Finset.card_pos.mpr hne.2
        omega
      rcases Finset.one_lt_card.mp h1a with ⟨u1, hu1, u2, hu2, hune⟩
      rcases Finset.one_lt_card.mp h1b with ⟨v1, hv1, v2, hv2, hvne⟩
      exact adj26_no_c4 hune hvne (hcross_adj u1 hu1 v1 hv1) (hcross_adj u1 hu1 v2 hv2)
        (hcross_adj u2 hu2 v1 hv1) (hcross_adj u2 hu2 v2 hv2)
    have hpair_getD : ∀ (p l : Fin 13) (i : Fin 26),
        (pgPairInput p l).getD i.val false = true → i = toPt p ∨ i = toLn l := by
      intro p l i hi
      by_cases hlt : i.val < 13
      · left
        have hget := pgPairInput_getD_pt p l ⟨i.val, hlt⟩
        rw [hi] at hget
        have heq : (⟨i.val, hlt⟩ : Fin 13) = p := of_decide_eq_true hget.symm
        have hval : i.val = p.val := congrArg Fin.val heq
        exact Fin.ext hval
      · right
        have hget := pgPairInput_getD_ln p l ⟨i.val - 13, by omega⟩
        have heqv : 13 + (i.val - 13) = i.val := by omega
        rw [heqv, hi] at hget
        have heq : (⟨i.val - 13, by omega⟩ : Fin 13) = l := of_decide_eq_true hget.symm
        apply Fin.ext
        rw [toLn_val]
        have := congrArg Fin.val heq
        dsimp at this
        omega
    rcases hcard_one with ha1 | hb1
    · rcases Finset.card_eq_one.mp ha1 with ⟨c, hc⟩
      refine ⟨c, b, by simp, ?_, ?_⟩
      · intro u hu
        exact hcross_adj c (by rw [hc]; exact Finset.mem_singleton_self c) u hu
      · intro p l hpl
        rcases (hpair_ab p l).mp hpl with ⟨⟨i, hi, hit⟩, ⟨j, hj, hjt⟩⟩
        rw [hc, Finset.mem_singleton] at hi
        rcases hi with rfl
        have hci : i = toPt p ∨ i = toLn l := hpair_getD p l i hit
        have hjj : j = toPt p ∨ j = toLn l := hpair_getD p l j hjt
        rcases hci with hpt | hln <;> rcases hjj with rfl | rfl
        · exfalso
          rw [hpt] at hc
          exact hno_two_pts p p (by rw [hc]; exact Finset.mem_singleton_self _) hj
        · exact Or.inl ⟨hpt, hj⟩
        · exact Or.inr ⟨hln, hj⟩
        · exfalso
          rw [hln] at hc
          exact hno_two_lns l l (by rw [hc]; exact Finset.mem_singleton_self _) hj
    · rcases Finset.card_eq_one.mp hb1 with ⟨c, hc⟩
      refine ⟨c, a, by simp, ?_, ?_⟩
      · intro u hu
        have hadj := hcross_adj u hu c (by rw [hc]; exact Finset.mem_singleton_self c)
        rcases hadj with ⟨p, l, hd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨p, l, hd, Or.inr ⟨rfl, rfl⟩⟩
        · exact ⟨p, l, hd, Or.inl ⟨rfl, rfl⟩⟩
      · intro p l hpl
        rcases (hpair_ab p l).mp hpl with ⟨⟨i, hi, hit⟩, ⟨j, hj, hjt⟩⟩
        rw [hc, Finset.mem_singleton] at hj
        rcases hj with rfl
        have hcj : j = toPt p ∨ j = toLn l := hpair_getD p l j hjt
        have hii : i = toPt p ∨ i = toLn l := hpair_getD p l i hit
        rcases hcj with hpt | hln <;> rcases hii with rfl | rfl
        · exfalso
          rw [hpt] at hc
          exact hno_two_pts p p hi (by rw [hc]; exact Finset.mem_singleton_self _)
        · exact Or.inl ⟨hpt, hi⟩
        · exact Or.inr ⟨hln, hi⟩
        · exfalso
          rw [hln] at hc
          exact hno_two_lns l l hi (by rw [hc]; exact Finset.mem_singleton_self _)
  · simp [h] at hlen

private lemma main_bound (p0 l0 : Fin 13) (C : Circuit) (bit : Bool)
    (hMono : Monotone2 C) (hRB : ReadsBack 27 C)

    (hPos : ∀ p l : Fin 13, p - l ∈ pgD → p ≠ p0 ∨ l ≠ l0 →
      C.eval (pgPairInput p l ++ [bit]) = true)
    (hQuad : ∀ Q : Finset (Fin 13), isQuad Q →
      C.eval (pgQuadInput Q ++ [bit]) = false)
    (hNoAnd : ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 27 C i j) :
    63 ≤ C.size := by
  classical
  have hCov : ∀ p l : Fin 13, p - l ∈ pgD → (p ≠ p0 ∨ l ≠ l0) → ∃ g : ℕ,
      ((gateAt C g).op = GateOp.and ∧
        OrReaches 27 C C.output g ∧
        ∀ Q : Finset (Fin 13), isQuad Q → (C.wires (pgQuadInput Q ++ [bit])).getD (27 + g) false = false) ∧
      (C.wires (pgPairInput p l ++ [bit])).getD (27 + g) false = true := by
    intro p l hinc hne
    have hpos := hPos p l hinc hne
    have hplen := append_bit_length (pgPairInput p l) bit (pgPairInput_length p l)
    rcases wires_true_decomp hMono hRB _ hplen C.output hpos with
      ⟨i, hi, hit⟩ | ⟨g, hgop, hreach, hgt⟩
    · rcases quad_on_active_bit _ _ (pgPairInput_length p l) i hit with ⟨Q, hQ, hQi⟩
      have ht : C.eval (pgQuadInput Q ++ [bit]) = true :=
        wires_true_of_mem_orIn hRB _ (append_bit_length _ _ (pgQuadInput_length Q)) hi hQi
      rw [hQuad Q hQ] at ht
      cases ht
    · refine ⟨g, ⟨hgop, hreach, fun Q hQ => ?_⟩, hgt⟩
      cases hval : (C.wires (pgQuadInput Q ++ [bit])).getD (27 + g) false
      · rfl
      · exfalso
        have ht : C.eval (pgQuadInput Q ++ [bit]) = true :=
          wires_true_of_orReaches hRB _ (append_bit_length _ _ (pgQuadInput_length Q)) C.output g hreach hval
        rw [hQuad Q hQ] at ht
        cases ht
  let good : ℕ → Prop := fun g =>
    (gateAt C g).op = GateOp.and ∧
    OrReaches 27 C C.output g ∧
    (∀ Q : Finset (Fin 13), isQuad Q → (C.wires (pgQuadInput Q ++ [bit])).getD (27 + g) false = false) ∧
    (∃ p l : Fin 13, p - l ∈ pgD ∧ (C.wires (pgPairInput p l ++ [bit])).getD (27 + g) false = true)
  let A : Finset ℕ := (Finset.range C.gates.length).filter good
  let OrTop : Finset ℕ := (Finset.range C.gates.length).filter fun h =>
    (gateAt C h).op = GateOp.or ∧
    OrReaches 27 C C.output h ∧
    ∃ g ∈ A, OrReaches 27 C (27 + h) g
  let OrBot : Finset ℕ := (Finset.range C.gates.length).filter fun h =>
    (gateAt C h).op = GateOp.or ∧
    ∃ g ∈ A, InCone 27 C h g
  have hA_prop : ∀ g ∈ A, g < C.gates.length ∧ good g := by
    intro g hg
    simpa [A, Finset.mem_filter, Finset.mem_range] using hg
  have hA_struct : ∀ g ∈ A, ∃ (c : Fin 26) (w : ℕ), w ∈ (gateAt C g).inputs ∧
      (∀ u ∈ liveOrIn C w, adj26 c u) ∧
      (∀ p l : Fin 13, (C.wires (pgPairInput p l ++ [bit])).getD (27 + g) false = true →
        (c = toPt p ∧ toLn l ∈ liveOrIn C w) ∨ (c = toLn l ∧ toPt p ∈ liveOrIn C w)) := by
    intro g hg
    rcases hA_prop g hg with ⟨_, hgop, _, hquad, hpos⟩
    exact clean_and_structure hMono hRB hNoAnd hgop hquad hpos
  let ctr : ℕ → Fin 26 := fun g =>
    if h : g ∈ A then (hA_struct g h).choose else 0
  let leafOpnd : ℕ → ℕ := fun g =>
    if h : g ∈ A then (hA_struct g h).choose_spec.choose else 0
  have hspec : ∀ g (hg : g ∈ A),
      leafOpnd g ∈ (gateAt C g).inputs ∧
      (∀ u ∈ liveOrIn C (leafOpnd g), adj26 (ctr g) u) ∧
      (∀ p l : Fin 13, (C.wires (pgPairInput p l ++ [bit])).getD (27 + g) false = true →
        (ctr g = toPt p ∧ toLn l ∈ liveOrIn C (leafOpnd g)) ∨
        (ctr g = toLn l ∧ toPt p ∈ liveOrIn C (leafOpnd g))) := by
    intro g hg
    simpa [ctr, leafOpnd, hg] using (hA_struct g hg).choose_spec.choose_spec
  have hdisj_A_Top : Disjoint A OrTop := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have h1 := (hA_prop g hg1).2.1
    have h2 : (gateAt C g).op = GateOp.or := (Finset.mem_filter.mp hg2).2.1
    rw [h1] at h2
    cases h2
  have hdisj_A_Bot : Disjoint A OrBot := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have h1 := (hA_prop g hg1).2.1
    have h2 : (gateAt C g).op = GateOp.or := (Finset.mem_filter.mp hg2).2.1
    rw [h1] at h2
    cases h2
  have hdisj_Top_Bot : Disjoint OrTop OrBot := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    have htop := (Finset.mem_filter.mp h1).2
    have hbot := (Finset.mem_filter.mp h2).2
    rcases htop.2.2 with ⟨g1, hg1, hreach⟩
    rcases hbot.2 with ⟨g2, hg2, hcone2⟩
    have hg1op := (hA_prop g1 hg1).2.1
    have hg2op := (hA_prop g2 hg2).2.1
    have hne : g1 ≠ h := by
      intro heq
      subst heq
      rw [hg1op] at htop
      cases htop.1
    have hcone1 : InCone 27 C g1 h := inCone_of_orReaches_ne hRB h g1 hreach hne
    exact hNoAnd ⟨g1, g2, hg1op, hg2op, inCone_trans hRB g2 g1 h hcone1 hcone2⟩
  have htotal : A.card + OrTop.card + OrBot.card ≤ C.gates.length := by
    have hdisj1 : Disjoint (A ∪ OrTop) OrBot :=
      Finset.disjoint_union_left.mpr ⟨hdisj_A_Bot, hdisj_Top_Bot⟩
    rw [← Finset.card_union_of_disjoint hdisj_A_Top, ← Finset.card_union_of_disjoint hdisj1]
    calc (A ∪ OrTop ∪ OrBot).card
        ≤ (Finset.range C.gates.length).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_union] at hx
          rcases hx with (hx | hx) | hx
          · exact (Finset.mem_filter.mp hx).1
          · exact (Finset.mem_filter.mp hx).1
          · exact (Finset.mem_filter.mp hx).1
      _ = C.gates.length := Finset.card_range _
  -- A cyclic perfect matching avoiding the omitted edge requires thirteen distinct star centres.
  have h13_le_A : 13 ≤ A.card := by
    let S : Finset (Fin 26) := A.image ctr

    let d0 : Fin 13 := if p0 - l0 = 0 then 1 else 0
    have hd0 : d0 ∈ pgD := by
      dsimp only [d0]
      split_ifs
      · exact pg_one_mem_D
      · exact pg_zero_mem_D
    have hdne : d0 ≠ p0 - l0 := by
      dsimp only [d0]
      split_ifs with h
      · rw [h]
        decide
      · exact Ne.symm h
    have hcover : ∀ i : Fin 13, toPt i ∈ S ∨ toLn (i - d0) ∈ S := by
      intro i
      have heq : i - (i - d0) = d0 := by abel
      have hiD : i - (i - d0) ∈ pgD := by rw [heq]; exact hd0
      have hne : i ≠ p0 ∨ i - d0 ≠ l0 := by
        by_contra h
        push Not at h
        rw [h.2, h.1] at heq
        exact hdne heq.symm
      rcases hCov i (i - d0) hiD hne with ⟨g, ⟨hgop, hreach, hquad⟩, hval⟩
      have hgA : g ∈ A := by
        simp only [A, good, Finset.mem_filter, Finset.mem_range]
        exact ⟨lt_gates_of_and hgop, hgop, hreach, hquad, ⟨i, i - d0, hiD, hval⟩⟩
      rcases (hspec g hgA).2.2 i (i - d0) hval with ⟨hctr, _⟩ | ⟨hctr, _⟩
      · left; exact Finset.mem_image.mpr ⟨g, hgA, hctr⟩
      · right; exact Finset.mem_image.mpr ⟨g, hgA, hctr⟩
    let f : Fin 13 → Fin 26 := fun i => if toPt i ∈ S then toPt i else toLn (i - d0)
    have hfinj : Function.Injective f := by
      intro i j hij
      dsimp only [f] at hij
      split_ifs at hij with h1 h2 h2
      · exact toPt_inj hij
      · exact False.elim (toPt_ne_toLn i (j - d0) hij)
      · exact False.elim (toPt_ne_toLn j (i - d0) hij.symm)
      · exact sub_left_inj.mp (toLn_inj hij)
    have hfmem : (Finset.univ : Finset (Fin 13)).image f ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      dsimp only [f]
      split_ifs with h1
      · exact h1
      · rcases hcover i with hpt | hln
        · exact absurd hpt h1
        · exact hln
    calc 13 = (Finset.univ : Finset (Fin 13)).card := by simp
      _ = ((Finset.univ : Finset (Fin 13)).image f).card :=
          (Finset.card_image_of_injective _ hfinj).symm
      _ ≤ S.card := Finset.card_le_card hfmem
      _ ≤ A.card := Finset.card_image_le
  have hA_le_Top : A.card ≤ OrTop.card + 1 := by
    let U : Finset ℕ := (A ∪ OrTop).image (fun j => 27 + j)
    let U' : Finset ℕ := U.erase C.output
    have hUcard : U.card = A.card + OrTop.card := by
      rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
      exact Finset.card_union_of_disjoint hdisj_A_Top
    have hU'card : U.card ≤ U'.card + 1 := by
      by_cases hm : C.output ∈ U
      · rw [Finset.card_erase_add_one hm]
      · simp only [U', Finset.erase_eq_of_notMem hm]; omega
    have hU'sub : U' ⊆ OrTop.biUnion (fun h => (gateAt C h).inputs.toFinset) := by
      intro u hu
      have huOut : u ≠ C.output := (Finset.mem_erase.mp hu).1
      have huU : u ∈ U := (Finset.mem_erase.mp hu).2
      rcases Finset.mem_image.mp huU with ⟨j, hj, rfl⟩
      have hreach_top : OrReaches 27 C C.output j := by
        rw [Finset.mem_union] at hj
        rcases hj with hjA | hjT
        · exact (hA_prop j hjA).2.2.1
        · exact (Finset.mem_filter.mp hjT).2.2.1
      have hreach_A : ∃ g ∈ A, OrReaches 27 C (27 + j) g := by
        rw [Finset.mem_union] at hj
        rcases hj with hjA | hjT
        · exact ⟨j, hjA, orReaches_self hRB (hA_prop j hjA).1⟩
        · exact (Finset.mem_filter.mp hjT).2.2.2
      rcases hreach_A with ⟨g, hgA, hjg⟩
      rcases orReaches_parent hRB C.output j hreach_top with hEq | ⟨h, hh, hhop, hrh, hmem⟩
      · exact absurd hEq.symm huOut
      · rw [Finset.mem_biUnion]
        refine ⟨h, ?_, List.mem_toFinset.mpr hmem⟩
        simp only [OrTop, Finset.mem_filter, Finset.mem_range]
        exact ⟨hh, hhop, hrh, g, hgA,
          (orReaches_iff hRB (27 + h) g).mpr ⟨h, hh, rfl, Or.inr ⟨hhop, 27 + j, hmem, hjg⟩⟩⟩
    have hU'le : U'.card ≤ 2 * OrTop.card := by
      calc U'.card
          ≤ (OrTop.biUnion (fun h => (gateAt C h).inputs.toFinset)).card := Finset.card_le_card hU'sub
        _ ≤ ∑ h ∈ OrTop, (gateAt C h).inputs.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ h ∈ OrTop, (gateAt C h).inputs.length :=
            Finset.sum_le_sum fun h _ => List.toFinset_card_le _
        _ ≤ ∑ _h ∈ OrTop, 2 :=
            Finset.sum_le_sum fun h hh =>
              gate_inputs_len_le hMono (Finset.mem_range.mp (Finset.mem_filter.mp hh).1)
        _ = OrTop.card * 2 := by simp
        _ = 2 * OrTop.card := Nat.mul_comm _ _
    omega
  -- Each shared OR with at least two leaves belongs to at most one star centre.
  have h51_le_AB : 51 ≤ A.card + OrBot.card := by
    let Kc : Fin 26 → Finset ℕ := fun c => A.filter fun g => ctr g = c
    let Wc : Fin 26 → Finset ℕ := fun c => (Kc c).image leafOpnd
    let Lc : Fin 26 → Finset (Fin 26) := fun c => (Wc c).biUnion (liveOrIn C)
    let Mc : Fin 26 → Finset ℕ := fun c => bigOrReach C (Wc c)
    let Eall : Finset (Fin 13 × Fin 13) := Finset.univ.filter fun e => e.1 - e.2 ∈ pgD
    let E : Finset (Fin 13 × Fin 13) := Eall.erase (p0, l0)
    let F : Finset (Fin 13 × Fin 13) :=
      (Finset.univ : Finset (Fin 26)).biUnion fun c => (Lc c).image (mkEdge c)
    have hEF : E ⊆ F := by
      intro e he
      rcases Finset.mem_erase.mp he with ⟨hnePair, heAll⟩
      rcases Finset.mem_filter.mp heAll with ⟨_, hinc⟩
      have hne : e.1 ≠ p0 ∨ e.2 ≠ l0 := by
        by_contra hboth
        push Not at hboth
        exact hnePair (Prod.ext hboth.1 hboth.2)
      rcases hCov e.1 e.2 hinc hne with ⟨g, ⟨hgop, hreach, hquad⟩, hval⟩
      have hgA : g ∈ A := by
        simp only [A, good, Finset.mem_filter, Finset.mem_range]
        exact ⟨lt_gates_of_and hgop, hgop, hreach, hquad, ⟨e.1, e.2, hinc, hval⟩⟩
      have hgK : g ∈ Kc (ctr g) := Finset.mem_filter.mpr ⟨hgA, rfl⟩
      have hwW : leafOpnd g ∈ Wc (ctr g) := Finset.mem_image.mpr ⟨g, hgK, rfl⟩
      rcases (hspec g hgA).2.2 e.1 e.2 hval with ⟨hctr, hleaf⟩ | ⟨hctr, hleaf⟩
      · rw [Finset.mem_biUnion]
        refine ⟨ctr g, Finset.mem_univ _, Finset.mem_image.mpr ⟨toLn e.2, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨leafOpnd g, hwW, hleaf⟩
        · rw [hctr, mkEdge_pt_ln]
      · rw [Finset.mem_biUnion]
        refine ⟨ctr g, Finset.mem_univ _, Finset.mem_image.mpr ⟨toPt e.1, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨leafOpnd g, hwW, hleaf⟩
        · rw [hctr, mkEdge_ln_pt]
    have h51_F : 51 ≤ F.card := by
      have hEall : Eall.card = 52 := pg_edges_card
      have hEcard : Eall.card ≤ E.card + 1 := by
        by_cases hm : (p0, l0) ∈ Eall
        · rw [Finset.card_erase_add_one hm]
        · simp only [E, Finset.erase_eq_of_notMem hm]; omega
      have hle := Finset.card_le_card hEF
      omega
    have hF_le : F.card ≤ ∑ c : Fin 26, (Lc c).card := by
      calc F.card ≤ ∑ c : Fin 26, ((Lc c).image (mkEdge c)).card := Finset.card_biUnion_le
        _ ≤ ∑ c : Fin 26, (Lc c).card := Finset.sum_le_sum fun c _ => Finset.card_image_le
    have hLc_le : ∀ c : Fin 26, (Lc c).card ≤ (Kc c).card + (Mc c).card := by
      intro c
      have h1 := leaf_count_bound hMono hRB (Mc c).card (Wc c) rfl
      have h2 : (Wc c).card ≤ (Kc c).card := Finset.card_image_le
      exact le_trans h1 (Nat.add_le_add_right h2 _)
    have hsum_L : ∑ c : Fin 26, (Lc c).card ≤
        (∑ c : Fin 26, (Kc c).card) + ∑ c : Fin 26, (Mc c).card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun c _ => hLc_le c
    have hK_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin 26)) Kc := by
      intro c1 _ c2 _ hcne
      change Disjoint (Kc c1) (Kc c2)
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      have h1 := (Finset.mem_filter.mp hg1).2
      have h2 := (Finset.mem_filter.mp hg2).2
      exact hcne (h1.symm.trans h2)
    have hsum_K : ∑ c : Fin 26, (Kc c).card ≤ A.card := by
      rw [← Finset.card_biUnion (by intro a _ b _ hab; exact hK_disj (by simp) (by simp) hab)]
      apply Finset.card_le_card
      intro g hg
      rcases Finset.mem_biUnion.mp hg with ⟨c, _, hgc⟩
      exact (Finset.mem_filter.mp hgc).1
    have hM_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin 26)) Mc := by
      intro c1 _ c2 _ hcne
      change Disjoint (Mc c1) (Mc c2)
      rw [Finset.disjoint_left]
      intro h hh1 hh2
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hh1 hh2
      rcases hh1 with ⟨_, _, hhcard, w1, hw1, hw1h⟩
      rcases hh2 with ⟨_, _, _, w2, hw2, hw2h⟩
      rcases Finset.mem_image.mp hw1 with ⟨g1, hg1, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨g2, hg2, rfl⟩
      rcases Finset.mem_filter.mp hg1 with ⟨hg1A, hctr1⟩
      rcases Finset.mem_filter.mp hg2 with ⟨hg2A, hctr2⟩
      have hlt : 1 < (liveOrIn C (27 + h)).card := by omega
      rcases Finset.one_lt_card.mp hlt with ⟨u1, hu1, u2, hu2, hune⟩
      have hsub1 : liveOrIn C (27 + h) ⊆ liveOrIn C (leafOpnd g1) :=
        liveOrIn_subset hRB hw1h
      have hsub2 : liveOrIn C (27 + h) ⊆ liveOrIn C (leafOpnd g2) :=
        liveOrIn_subset hRB hw2h
      have ha11 := (hspec g1 hg1A).2.1 u1 (hsub1 hu1)
      have ha12 := (hspec g1 hg1A).2.1 u2 (hsub1 hu2)
      have ha21 := (hspec g2 hg2A).2.1 u1 (hsub2 hu1)
      have ha22 := (hspec g2 hg2A).2.1 u2 (hsub2 hu2)
      rw [hctr1] at ha11 ha12
      rw [hctr2] at ha21 ha22
      exact adj26_no_c4 hcne hune ha11 ha12 ha21 ha22
    have hsum_M : ∑ c : Fin 26, (Mc c).card ≤ OrBot.card := by
      rw [← Finset.card_biUnion (by intro a _ b _ hab; exact hM_disj (by simp) (by simp) hab)]
      apply Finset.card_le_card
      intro h hh
      rcases Finset.mem_biUnion.mp hh with ⟨c, _, hhc⟩
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hhc
      rcases hhc with ⟨hhlt, hhop, _, w, hw, hwh⟩
      rcases Finset.mem_image.mp hw with ⟨g, hg, rfl⟩
      rcases Finset.mem_filter.mp hg with ⟨hgA, _⟩
      simp only [OrBot, Finset.mem_filter, Finset.mem_range]
      exact ⟨hhlt, hhop, g, hgA,
        inCone_of_input_orReaches hRB (hA_prop g hgA).1 (hspec g hgA).1 hwh⟩
    omega
  change 63 ≤ C.gates.length
  omega

private lemma no_and_cone {C : Circuit} (h : andPairs 27 C = 0) :
    ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 27 C i j := by
  rintro ⟨i, j, hi, hj, hc⟩
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold andPairs at h
  have hm : (i, j) ∈ ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      fun (p : ℕ × ℕ) => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 27 C p.1 p.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (lt_gates_of_and hi), Finset.mem_range.mpr (lt_gates_of_and hj)⟩, hi, hj, hc⟩
  rw [Finset.card_eq_zero.mp h] at hm
  exact Finset.notMem_empty _ hm

private def pgInput (A B : Finset (Fin 13)) (bit : Bool) : List Bool :=
  ((List.ofFn fun i : Fin 13 => decide (i ∈ A)) ++
    List.ofFn fun i : Fin 13 => decide (i ∈ B)) ++ [bit]

private lemma pgInput_pair (p l : Fin 13) (bit : Bool) :
    pgInput {p} {l} bit = pgPairInput p l ++ [bit] := by
  unfold pgInput pgPairInput
  apply congrArg (· ++ [bit])
  exact congrArg₂ (· ++ ·)
    (congrArg List.ofFn (funext fun _ => decide_eq_decide.mpr Finset.mem_singleton))
    (congrArg List.ofFn (funext fun _ => decide_eq_decide.mpr Finset.mem_singleton))

private lemma pgInput_quad (Q : Finset (Fin 13)) (bit : Bool) :
    pgInput Q {l : Fin 13 | ∀ p ∈ Q, p - l ∉ pgD} bit = pgQuadInput Q ++ [bit] := by
  unfold pgInput pgQuadInput
  apply congrArg (· ++ [bit])
  apply congrArg ((List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ ·)
  exact congrArg List.ofFn (funext fun _ => decide_eq_decide.mpr (by simp))

end PEqualNP.Outside.L_meta_5809

theorem PEqualNP.Outside.L_meta_5809 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →       PEqualNP.TopForm.andPairs (27 : ℕ) x1 = (0 : ℕ) →         have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];         (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) → (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C p0 l0 bit hMono hRB hPairs x8 x9 hPos hQuad _
  apply PEqualNP.Outside.L_meta_5809.main_bound p0 l0 C bit hMono hRB _ _
    (PEqualNP.Outside.L_meta_5809.no_and_cone hPairs)
  · intro p l hinc hne
    rw [← PEqualNP.Outside.L_meta_5809.pgInput_pair]
    exact hPos p l hinc hne
  · intro Q hQ
    rw [← PEqualNP.Outside.L_meta_5809.pgInput_quad]
    exact hQuad Q hQ.1 hQ.2


namespace PEqualNP.Outside.L_meta_5811

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

private def pgD : Finset (Fin 13) := {0, 1, 3, 9}

private def pgPairInput (p l : Fin 13) : List Bool :=
  (List.ofFn fun x : Fin 13 => Decidable.decide (x = p)) ++
    List.ofFn fun x : Fin 13 => Decidable.decide (x = l)

private def pgQuadInput (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun x : Fin 13 => Decidable.decide (x ∈ Q)) ++
    List.ofFn fun x : Fin 13 => Decidable.decide (∀ q ∈ Q, q - x ∉ pgD)

private abbrev isQuad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin 13, {q ∈ Q | q - l ∈ pgD}.card ≤ 2

private abbrev missesLine (Q : Finset (Fin 13)) (l : Fin 13) : Prop :=
  ∀ q ∈ Q, q - l ∉ pgD

private def shiftQuad (t : Fin 13) (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Q.image (· + t)

private def baseQuad : Fin 6 → Finset (Fin 13)
  | 0 => {0, 1, 4, 6}
  | 1 => {0, 1, 2, 5}
  | 2 => {0, 1, 2, 6}
  | 3 => {0, 1, 4, 8}
  | 4 => {0, 2, 3, 4}
  | 5 => {0, 3, 5, 6}

private lemma pg_edges_card :
    (Finset.univ.filter fun e : Fin 13 × Fin 13 => e.1 - e.2 ∈ pgD).card = 52 := by
  decide

private lemma baseQuad_isQuad : ∀ b : Fin 6, isQuad (baseQuad b) := by
  decide

private lemma baseQuad_mem_zero : ∀ b : Fin 6, (0 : Fin 13) ∈ baseQuad b := by
  decide

private lemma baseQuad_zero_misses_two : missesLine (baseQuad 0) 2 := by
  decide

private lemma baseQuad_pt_diff :
    ∀ d : Fin 13, d ≠ 0 → ∃ b : Fin 6, ∃ a ∈ baseQuad b, a + d ∈ baseQuad b := by
  decide

-- For each nonzero offset, a quadrangle and a line such that both lines miss the quadrangle.
private def lineWitness : Fin 13 → Fin 6 × Fin 13 :=
  ![(0, 0), (1, 7), (0, 7), (3, 6), (1, 3), (0, 2), (0, 9),
    (0, 2), (0, 7), (1, 7), (3, 9), (0, 9), (1, 8)]

private lemma lineWitness_spec : ∀ d : Fin 13, d ≠ 0 →
    missesLine (baseQuad (lineWitness d).1) (lineWitness d).2 ∧
    missesLine (baseQuad (lineWitness d).1) ((lineWitness d).2 + d) := by
  decide

private lemma baseQuad_line_diff :
    ∀ d : Fin 13, d ≠ 0 → ∃ b : Fin 6, ∃ l : Fin 13,
      missesLine (baseQuad b) l ∧ missesLine (baseQuad b) (l + d) :=
  fun d hd => ⟨(lineWitness d).1, (lineWitness d).2, lineWitness_spec d hd⟩

private def nonincWitness : Fin 13 → Fin 6 :=
  ![0, 5, 0, 1, 0, 4, 3, 0, 1, 0, 0, 4, 0]

private lemma nonincWitness_spec : ∀ d : Fin 13, (0 - d) ∉ pgD →
    missesLine (baseQuad (nonincWitness d)) d := by
  decide

private lemma baseQuad_noninc :
    ∀ d : Fin 13, (0 - d) ∉ pgD → ∃ b : Fin 6, missesLine (baseQuad b) d :=
  fun d hd => ⟨nonincWitness d, nonincWitness_spec d hd⟩

private lemma isQuad_shift (t : Fin 13) {Q : Finset (Fin 13)} (hQ : isQuad Q) :
    isQuad (shiftQuad t Q) := by
  refine ⟨?_, ?_⟩
  · unfold shiftQuad
    rw [Finset.card_image_of_injective Q (fun a b h => add_right_cancel h)]
    exact hQ.1
  · intro l
    have hbij : {q ∈ shiftQuad t Q | q - l ∈ pgD} =
        ({q ∈ Q | q - (l - t) ∈ pgD}).image (· + t) := by
      ext x
      simp only [shiftQuad, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hmem⟩
        refine ⟨a, ⟨ha, ?_⟩, rfl⟩
        have heq : a - (l - t) = a + t - l := by abel
        rwa [heq]
      · rintro ⟨a, ⟨ha, hmem⟩, rfl⟩
        refine ⟨⟨a, ha, rfl⟩, ?_⟩
        have heq : a + t - l = a - (l - t) := by abel
        rwa [heq]
    rw [hbij, Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
    exact hQ.2 (l - t)

private lemma missesLine_shift (t : Fin 13) {Q : Finset (Fin 13)} {l : Fin 13}
    (hm : missesLine Q l) : missesLine (shiftQuad t Q) (l + t) := by
  intro q hq
  simp only [shiftQuad, Finset.mem_image] at hq
  rcases hq with ⟨a, ha, rfl⟩
  have heq : a + t - (l + t) = a - l := by abel
  rw [heq]
  exact hm a ha

private lemma quad_has_pt (p : Fin 13) : ∃ Q : Finset (Fin 13), isQuad Q ∧ p ∈ Q := by
  refine ⟨shiftQuad p (baseQuad 0), isQuad_shift p (baseQuad_isQuad 0), ?_⟩
  simp only [shiftQuad, Finset.mem_image]
  exact ⟨0, baseQuad_mem_zero 0, zero_add p⟩

private lemma quad_misses_line (l : Fin 13) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ missesLine Q l := by
  refine ⟨shiftQuad (l - 2) (baseQuad 0), isQuad_shift (l - 2) (baseQuad_isQuad 0), ?_⟩
  have h := missesLine_shift (l - 2) baseQuad_zero_misses_two
  have heq : (2 : Fin 13) + (l - 2) = l := by abel
  rwa [heq] at h

private lemma quad_has_two_pts {p1 p2 : Fin 13} (hne : p1 ≠ p2) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ p1 ∈ Q ∧ p2 ∈ Q := by
  have hd : p2 - p1 ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases baseQuad_pt_diff (p2 - p1) hd with ⟨b, a, ha, had⟩
  refine ⟨shiftQuad (p1 - a) (baseQuad b), isQuad_shift (p1 - a) (baseQuad_isQuad b), ?_, ?_⟩
  · simp only [shiftQuad, Finset.mem_image]
    exact ⟨a, ha, by abel⟩
  · simp only [shiftQuad, Finset.mem_image]
    exact ⟨a + (p2 - p1), had, by abel⟩

private lemma quad_misses_two_lines {l1 l2 : Fin 13} (hne : l1 ≠ l2) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ missesLine Q l1 ∧ missesLine Q l2 := by
  have hd : l2 - l1 ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases baseQuad_line_diff (l2 - l1) hd with ⟨b, l, hm1, hm2⟩
  refine ⟨shiftQuad (l1 - l) (baseQuad b), isQuad_shift (l1 - l) (baseQuad_isQuad b), ?_, ?_⟩
  · have h := missesLine_shift (l1 - l) hm1
    have heq : l + (l1 - l) = l1 := by abel
    rwa [heq] at h
  · have h := missesLine_shift (l1 - l) hm2
    have heq : l + (l2 - l1) + (l1 - l) = l2 := by abel
    rwa [heq] at h

private lemma quad_noninc {p l : Fin 13} (hni : p - l ∉ pgD) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ p ∈ Q ∧ missesLine Q l := by
  have hni' : (0 : Fin 13) - (l - p) ∉ pgD := by
    have heq : (0 : Fin 13) - (l - p) = p - l := by abel
    rwa [heq]
  rcases baseQuad_noninc (l - p) hni' with ⟨b, hm⟩
  refine ⟨shiftQuad p (baseQuad b), isQuad_shift p (baseQuad_isQuad b), ?_, ?_⟩
  · simp only [shiftQuad, Finset.mem_image]
    exact ⟨0, baseQuad_mem_zero b, zero_add p⟩
  · have h := missesLine_shift p hm
    have heq : l - p + p = l := by abel
    rwa [heq] at h

private lemma pgPairInput_length (p l : Fin 13) : (pgPairInput p l).length = 26 := by
  unfold pgPairInput
  rw [List.length_append, List.length_ofFn, List.length_ofFn]

private lemma pgQuadInput_length (Q : Finset (Fin 13)) : (pgQuadInput Q).length = 26 := by
  unfold pgQuadInput
  rw [List.length_append, List.length_ofFn, List.length_ofFn]

private lemma pgPairInput_getD_pt (p l x : Fin 13) :
    (pgPairInput p l).getD x.val false = Decidable.decide (x = p) := by
  unfold pgPairInput
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (y = p)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hx, List.getElem?_eq_getElem hx,
    Option.getD_some, List.getElem_ofFn]

private lemma pgPairInput_getD_ln (p l x : Fin 13) :
    (pgPairInput p l).getD (13 + x.val) false = Decidable.decide (x = l) := by
  unfold pgPairInput
  have h1 : (List.ofFn fun y : Fin 13 => Decidable.decide (y = p)).length = 13 :=
    List.length_ofFn
  have hge : (List.ofFn fun y : Fin 13 => Decidable.decide (y = p)).length ≤ 13 + x.val := by
    omega
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (y = l)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, h1, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hx, Option.getD_some, List.getElem_ofFn]

private lemma pgQuadInput_getD_pt (Q : Finset (Fin 13)) (x : Fin 13) :
    (pgQuadInput Q).getD x.val false = Decidable.decide (x ∈ Q) := by
  unfold pgQuadInput
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (y ∈ Q)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hx, List.getElem?_eq_getElem hx,
    Option.getD_some, List.getElem_ofFn]

private lemma pgQuadInput_getD_ln (Q : Finset (Fin 13)) (x : Fin 13) :
    (pgQuadInput Q).getD (13 + x.val) false = Decidable.decide (∀ q ∈ Q, q - x ∉ pgD) := by
  unfold pgQuadInput
  have h1 : (List.ofFn fun y : Fin 13 => Decidable.decide (y ∈ Q)).length = 13 :=
    List.length_ofFn
  have hge : (List.ofFn fun y : Fin 13 => Decidable.decide (y ∈ Q)).length ≤ 13 + x.val := by
    omega
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (∀ q ∈ Q, q - y ∉ pgD)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, h1, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hx, Option.getD_some, List.getElem_ofFn]

private lemma quad_on_bit (i : Fin 26) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ (pgQuadInput Q).getD i.val false = true := by
  by_cases hi : i.val < 13
  · rcases quad_has_pt ⟨i.val, hi⟩ with ⟨Q, hQ, hp⟩
    refine ⟨Q, hQ, ?_⟩
    have hget := pgQuadInput_getD_pt Q ⟨i.val, hi⟩
    simpa [hp] using hget
  · have hl : i.val - 13 < 13 := by omega
    rcases quad_misses_line ⟨i.val - 13, hl⟩ with ⟨Q, hQ, hm⟩
    refine ⟨Q, hQ, ?_⟩
    have hget := pgQuadInput_getD_ln Q ⟨i.val - 13, hl⟩
    have heq : 13 + (i.val - 13) = i.val := by omega
    rw [heq] at hget
    rw [hget]
    exact decide_eq_true hm

private def toPt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p

private def toLn (l : Fin 13) : Fin 26 := Fin.natAdd 13 l

private lemma toPt_val (p : Fin 13) : (toPt p).val = p.val := rfl

private lemma toLn_val (l : Fin 13) : (toLn l).val = 13 + l.val := by
  simp [toLn]
  omega

private def mkEdge (c u : Fin 26) : Fin 13 × Fin 13 :=
  if h : c.val < 13 then
    (⟨c.val, h⟩, ⟨u.val % 13, Nat.mod_lt _ (by decide)⟩)
  else
    (⟨u.val % 13, Nat.mod_lt _ (by decide)⟩, ⟨c.val % 13, Nat.mod_lt _ (by decide)⟩)

private lemma mkEdge_pt_ln (p l : Fin 13) : mkEdge (toPt p) (toLn l) = (p, l) := by
  unfold mkEdge
  have hp : (toPt p).val < 13 := p.isLt
  simp only [hp, ↓reduceDIte]
  apply Prod.ext
  · exact Fin.ext rfl
  · apply Fin.ext
    change (13 + l.val) % 13 = l.val
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt l.isLt

private lemma mkEdge_ln_pt (l p : Fin 13) : mkEdge (toLn l) (toPt p) = (p, l) := by
  unfold mkEdge
  have hl : ¬ (toLn l).val < 13 := by rw [toLn_val]; omega
  simp only [hl, ↓reduceDIte]
  apply Prod.ext
  · apply Fin.ext
    change p.val % 13 = p.val
    exact Nat.mod_eq_of_lt p.isLt
  · apply Fin.ext
    change (13 + l.val) % 13 = l.val
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt l.isLt

private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

private lemma lt_gates_of_and {C : Circuit} {j : ℕ} (hop : (gateAt C j).op = GateOp.and) :
    j < C.gates.length := by
  by_contra hge
  push Not at hge
  have hdef : gateAt C j = ⟨GateOp.or, []⟩ := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl
  rw [hdef] at hop
  cases hop

private lemma gateOp_and_or {C : Circuit} (hMono : Monotone2 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  have h := (hMono (gateAt C j) (gateAt_mem hj)).1
  simpa using h

private lemma gate_inputs_len_le {C : Circuit} (hMono : Monotone2 C) {j : ℕ}
    (hj : j < C.gates.length) :
    (gateAt C j).inputs.length ≤ 2 :=
  (hMono (gateAt C j) (gateAt_mem hj)).2

private lemma wires_length (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_append_length _ C.gates inp

private lemma wires_getD_ge (C : Circuit) (inp : List Bool) {w : ℕ}
    (hw : inp.length + C.gates.length ≤ w) :
    (C.wires inp).getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wires_length]; exact hw

private lemma wires_getD_input (C : Circuit) (inp : List Bool) {w : ℕ} (hw : w < inp.length) :
    (C.wires inp).getD w false = inp.getD w false := by
  unfold Circuit.wires
  exact foldl_append_getD_lt _ C.gates inp false w hw

private lemma wires_getD_gate {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    (inp : List Bool) (hlen : inp.length = n) {j : ℕ} (hj : j < C.gates.length) :
    (C.wires inp).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => (C.wires inp).getD w false) := by
  unfold Circuit.wires
  have hgate := foldl_append_getD_gate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates inp false j hj ⟨GateOp.or, []⟩
  rw [hlen] at hgate
  rw [hgate]
  change (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          inp).getD i false) =
    (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          inp).getD i false)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < inp.length + j := by
    rw [hlen]
    exact hRB j hj i hi
  exact foldl_append_take_getD _ C.gates inp false j i (Nat.le_of_lt hj) hilt

private lemma orSets_length (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  rw [foldl_append_length]
  simp

private lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [orSets_length]; exact hj

private lemma orSets_getD_lt_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = _
  rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
  congr 1
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma orSets_getD_lt_not_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = [j]
  rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]

private lemma orReaches_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ u ∈ (gateAt C j).inputs, OrReaches n C u g)) := by
  constructor
  · rintro ⟨hnw, hmem⟩
    have hlt : w - n < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [orSets_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨w - n, hlt, by omega, ?_⟩
    by_cases hop : (gateAt C (w - n)).op = GateOp.or
    · rw [orSets_getD_lt_or n C hlt hop, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨u, hu, hgu⟩
        rw [List.mem_filter, decide_eq_true_eq] at hu
        exact ⟨hop, u, hu.1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, u, hu, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨u, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨hu, hnu, hRB j hj u hu⟩

private lemma orReaches_self {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hRB (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

private lemma orReaches_le {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, u, hu, hug⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : u < n + j := hRB j hj u hu
      have hrec := ih _ hlt g hug
      exact ⟨by omega, hrec.2⟩

private lemma orReaches_trans {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ w g h : ℕ, OrReaches n C w g → OrReaches n C (n + g) h → OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g h hwg hgh
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
    · exact hgh
    · have hrec := ih _ (hRB j hj u hu) g h hug hgh
      exact (orReaches_iff hRB (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, u, hu, hrec⟩⟩

private lemma orReaches_parent {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      w = n + g ∨
        ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧ OrReaches n C w h ∧
          n + g ∈ (gateAt C h).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
    · exact Or.inl rfl
    · right
      rcases ih _ (hRB j hj u hu) g hug with rfl | ⟨h, hh, hhop, hreach, hmem⟩
      · exact ⟨j, hj, hop, orReaches_self hRB hj, hu⟩
      · exact ⟨h, hh, hhop,
          (orReaches_iff hRB (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, u, hu, hreach⟩⟩, hmem⟩

private lemma wires_true_of_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    (inp : List Bool) (hlen : inp.length = n) :
    ∀ w g : ℕ, OrReaches n C w g →
      (C.wires inp).getD (n + g) false = true → (C.wires inp).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg hg
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
    · exact hg
    · have hut : (C.wires inp).getD u false = true := ih u (hRB j hj u hu) g hug hg
      rw [wires_getD_gate hRB inp hlen hj, hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
      exact ⟨u, hu, hut⟩

private lemma cones_length (n : ℕ) (C : Circuit) :
    (cones n C).length = C.gates.length := by
  unfold cones coneStep
  rw [foldl_append_length]
  simp

private lemma cones_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (cones n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [cones_length]; exact hj

private lemma cones_getD_lt (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  unfold cones coneStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) =>
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change (((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
      (fun w => (w - n) :: pre.getD (w - n) [])) = _
  rw [hprelen]
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  congr 1
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma inCone_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (i j : ℕ) :
    InCone n C i j ↔
      j < C.gates.length ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  constructor
  · intro hmem
    have hj : j < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [cones_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨hj, ?_⟩
    rw [cones_getD_lt n C hj, List.mem_flatMap] at hmem
    rcases hmem with ⟨w, hw, hiw⟩
    rw [List.mem_filter, decide_eq_true_eq] at hw
    rw [List.mem_cons] at hiw
    exact ⟨w, hw.1, hw.2.1, hiw⟩
  · rintro ⟨hj, w, hw, hnw, hiw⟩
    rw [cones_getD_lt n C hj, List.mem_flatMap]
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨hw, hnw, hRB j hj w hw⟩
    · rw [List.mem_cons]
      exact hiw

private lemma inCone_lt {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ j i : ℕ, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hij
    rw [inCone_iff hRB] at hij
    rcases hij with ⟨hj, w, hw, hnw, rfl | hrec⟩
    · have hwlt := hRB j hj w hw
      exact ⟨by omega, hj⟩
    · have hwlt := hRB j hj w hw
      have hsub := ih (w - n) (by omega) i hrec
      exact ⟨by omega, hj⟩

private lemma inCone_of_orReaches_ne {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ j i : ℕ, OrReaches n C (n + j) i → i ≠ j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hji hne
    rw [orReaches_iff hRB] at hji
    rcases hji with ⟨j', hj', heq, rfl | ⟨_, u, hu, hui⟩⟩
    · exact absurd (by omega) hne
    · rcases (by omega : j = j') with rfl
      have hnu : n ≤ u := hui.1
      have hult : u < n + j := hRB j hj' u hu
      by_cases hiu : i = u - n
      · exact (inCone_iff hRB i j).mpr ⟨hj', u, hu, hnu, Or.inl hiu⟩
      · have hui' : OrReaches n C (n + (u - n)) i := by
          have : n + (u - n) = u := by omega
          rwa [this]
        have hsub := ih (u - n) (by omega) i hui' hiu
        exact (inCone_iff hRB i j).mpr ⟨hj', u, hu, hnu, Or.inr hsub⟩

private lemma inCone_of_input_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    {j w i : ℕ} (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs)
    (hwi : OrReaches n C w i) :
    InCone n C i j := by
  have hnw : n ≤ w := hwi.1
  by_cases hiw : i = w - n
  · exact (inCone_iff hRB i j).mpr ⟨hj, w, hw, hnw, Or.inl hiw⟩
  · have hwi' : OrReaches n C (n + (w - n)) i := by
      have : n + (w - n) = w := by omega
      rwa [this]
    exact (inCone_iff hRB i j).mpr ⟨hj, w, hw, hnw, Or.inr (inCone_of_orReaches_ne hRB (w - n) i hwi' hiw)⟩

private lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) :
    orIn n C i.val = {i} := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (hu | ⟨k, _, ⟨hni, _⟩, _, _⟩)
    · exact Fin.ext hu
    · omega
  · rintro rfl
    exact Or.inl rfl

private lemma orIn_ge {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hRB] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

private lemma orIn_and {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hRB] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

private lemma mem_orIn_or {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (u : Fin n) :
    u ∈ orIn n C (n + j) ↔ ∃ w ∈ (gateAt C j).inputs, u ∈ orIn n C w := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hRB] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, w, hw, hwk⟩
      · exact ⟨u.val, huk, Or.inl rfl⟩
      · exact ⟨w, hw, Or.inr ⟨k, hk, hwk, hkop, huk⟩⟩
  · rintro ⟨w, hw, hEq | ⟨k, hk, hwk, hkop, huk⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hRB hj, hop, ?_⟩
      rwa [hEq]
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hRB (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, w, hw, hwk⟩⟩

private lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    {w g : ℕ} (hwg : OrReaches n C w g) :
    orIn n C (n + g) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hEq | ⟨k, hk, hgk, hkop, huk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans hRB w g k hwg hgk, hkop, huk⟩

private lemma wires_true_of_mem_orIn {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    (inp : List Bool) (hlen : inp.length = n) {w : ℕ} {i : Fin n}
    (hi : i ∈ orIn n C w) (hit : inp.getD i.val false = true) :
    (C.wires inp).getD w false = true := by
  unfold orIn at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with rfl | ⟨k, hk, hwk, hkop, hik⟩
  · rw [wires_getD_input C inp (hlen.symm ▸ i.isLt)]
    exact hit
  · apply wires_true_of_orReaches hRB inp hlen w k hwk
    rw [wires_getD_gate hRB inp hlen hk, hkop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    refine ⟨i.val, hik, ?_⟩
    rw [wires_getD_input C inp (hlen.symm ▸ i.isLt)]
    exact hit

private lemma wires_true_decomp {n : ℕ} {C : Circuit}
    (hMono : Monotone2 C) (hRB : ReadsBack n C)
    (inp : List Bool) (hlen : inp.length = n) :
    ∀ w : ℕ, (C.wires inp).getD w false = true →
      (∃ i ∈ orIn n C w, inp.getD i.val false = true) ∨
      (∃ g : ℕ, (gateAt C g).op = GateOp.and ∧ OrReaches n C w g ∧
        (C.wires inp).getD (n + g) false = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwt
    by_cases hlt : w < n
    · left
      refine ⟨⟨w, hlt⟩, ?_, ?_⟩
      · rw [orIn_input ⟨w, hlt⟩]; exact Finset.mem_singleton_self _
      · rwa [wires_getD_input C inp (hlen.symm ▸ hlt)] at hwt
    · by_cases hge : n + C.gates.length ≤ w
      · exfalso
        have hf : (C.wires inp).getD w false = false :=
          wires_getD_ge C inp (by omega)
        rw [hf] at hwt
        cases hwt
      · set j := w - n
        have hwj : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hwj] at hwt ⊢
        rcases gateOp_and_or hMono hj with hand | hor
        · exact Or.inr ⟨j, hand, orReaches_self hRB hj, hwt⟩
        · rw [wires_getD_gate hRB inp hlen hj, hor] at hwt
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and] at hwt
          rcases hwt with ⟨u, hu, hut⟩
          have hult : u < w := by
            have := hRB j hj u hu
            omega
          rcases ih u hult hut with ⟨i, hi, hit⟩ | ⟨g, hgop, hug, hgt⟩
          · exact Or.inl ⟨i, (mem_orIn_or hRB hj hor i).mpr ⟨u, hu, hi⟩, hit⟩
          · exact Or.inr ⟨g, hgop, (orReaches_iff hRB (n + j) g).mpr
              ⟨j, hj, rfl, Or.inr ⟨hor, u, hu, hug⟩⟩, hgt⟩

private lemma append_bit_length (inp : List Bool) (bit : Bool) (h : inp.length = 26) :
    (inp ++ [bit]).length = 27 := by simp [h]

private lemma getD_append_bit_lt (inp : List Bool) (bit : Bool) {i : ℕ} (hi : i < inp.length) :
    (inp ++ [bit]).getD i false = inp.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_bit_last (inp : List Bool) (bit : Bool) (h : inp.length = 26) :
    (inp ++ [bit]).getD 26 false = bit := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), h]
  rfl

private def pt (p : Fin 13) : Fin 27 := (toPt p).castSucc
private def ln (l : Fin 13) : Fin 27 := (toLn l).castSucc

private def near (u v : Fin 27) : Prop :=
  if hu : u.val < 13 then
    if hv : 13 ≤ v.val ∧ v.val < 26 then
      (⟨u.val, hu⟩ : Fin 13) - ⟨v.val - 13, by omega⟩ ∈ pgD
    else False
  else if hv : v.val < 13 then
    if hu' : u.val < 26 then
      (⟨v.val, hv⟩ : Fin 13) - ⟨u.val - 13, by omega⟩ ∈ pgD
    else False
  else False

private abbrev nearDec : DecidableRel near := fun u v => by
  unfold near
  infer_instance

private lemma near_iff {u v : Fin 27} :
    near u v ↔ ∃ p l : Fin 13, p - l ∈ pgD ∧
      ((u = pt p ∧ v = ln l) ∨ (u = ln l ∧ v = pt p)) := by
  constructor
  · intro h
    unfold near at h
    split at h
    next hu =>
      split at h
      next hv =>
        exact ⟨⟨u.val, hu⟩, ⟨v.val - 13, by omega⟩, h, Or.inl
          ⟨Fin.ext rfl, Fin.ext (by change v.val = (toLn _).val; rw [toLn_val]; dsimp; omega)⟩⟩
      next => contradiction
    next hu =>
      split at h
      next hv =>
        split at h
        next hu' =>
          exact ⟨⟨v.val, hv⟩, ⟨u.val - 13, by omega⟩, h, Or.inr
            ⟨Fin.ext (by change u.val = (toLn _).val; rw [toLn_val]; dsimp; omega), Fin.ext rfl⟩⟩
        next => contradiction
      next => contradiction
  · rintro ⟨p, l, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    all_goals
      have hpl : (pt p).val < 13 := p.isLt
      have hl : (ln l).val = 13 + l.val := toLn_val l
      have hll : 13 ≤ (ln l).val ∧ (ln l).val < 26 := by omega
      unfold near
      simp only [dite_eq_left hpl, dite_eq_left hll, dite_eq_right (not_lt.mpr hll.1), dite_eq_left hll.2]
      have heq : (⟨(ln l).val - 13, by omega⟩ : Fin 13) = l := Fin.ext (by dsimp; omega)
      rw [heq]
      exact h

private lemma near_symm {u v : Fin 27} (h : near u v) : near v u := by
  rcases near_iff.mp h with ⟨p, l, h, h'⟩
  exact near_iff.mpr ⟨p, l, h, h'.elim (fun h => Or.inr ⟨h.2, h.1⟩)
    (fun h => Or.inl ⟨h.2, h.1⟩)⟩

private lemma near_bip : ∀ u v : Fin 27, near u v → (u.val < 13) ≠ (v.val < 13) := by
  let _ := nearDec
  decide

private lemma near_irrefl (u : Fin 27) : ¬ near u u :=
  fun h => near_bip u u h rfl

private def nbr (c : Fin 27) : Finset (Fin 27) :=
  letI := nearDec
  Finset.univ.filter (near c)

private lemma mem_nbr {c u : Fin 27} : u ∈ nbr c ↔ near c u := by simp [nbr]

private lemma nbr_le : ∀ c : Fin 27, (nbr c).card ≤ 4 := by decide

private lemma common_le : ∀ c d : Fin 27, c ≠ d → (nbr c ∩ nbr d).card ≤ 1 := by decide

private lemma no_triangle {c u v : Fin 27} (hu : near c u) (hv : near c v) : ¬ near u v := by
  have h₁ := near_bip _ _ hu
  have h₂ := near_bip _ _ hv
  intro h
  have h₃ := near_bip _ _ h
  by_cases hc : c.val < 13
  · have hn₁ : ¬ u.val < 13 := fun h => h₁ (propext (by simp [hc, h]))
    have hn₂ : ¬ v.val < 13 := fun h => h₂ (propext (by simp [hc, h]))
    exact h₃ (propext (by simp [hn₁, hn₂]))
  · have hn₁ : u.val < 13 := by
      by_contra h
      exact h₁ (propext (by simp [hc, h]))
    have hn₂ : v.val < 13 := by
      by_contra h
      exact h₂ (propext (by simp [hc, h]))
    exact h₃ (propext (by simp [hn₁, hn₂]))

private def atoms (C : Circuit) (bit : Bool) (w : ℕ) : Finset (Fin 27) :=
  (orIn 27 C w).filter fun i => i.val < 26 ∨ bit = true

private def hit (inp : List Bool) (S : Finset (Fin 27)) : Prop :=
  ∃ i ∈ S, inp.getD i.val false = true

private lemma atoms_hit {C : Circuit} {inp : List Bool} {bit : Bool}
    (hlen : inp.length = 26) (w : ℕ) :
    hit (inp ++ [bit]) (atoms C bit w) ↔ hit (inp ++ [bit]) (orIn 27 C w) := by
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, (Finset.mem_filter.mp hi).1, h⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩, h⟩
    by_cases hlt : i.val < 26
    · exact Or.inl hlt
    · right
      have hv : i.val = 26 := by omega
      rwa [hv, getD_append_bit_last _ _ hlen] at h

private lemma atoms_or {C : Circuit} {bit : Bool} (hr : ReadsBack 27 C) {j : ℕ}
    (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or) (i : Fin 27) :
    i ∈ atoms C bit (27 + j) ↔ ∃ w ∈ (gateAt C j).inputs, i ∈ atoms C bit w := by
  simp only [atoms, Finset.mem_filter, mem_orIn_or hr hj ho]
  constructor
  · rintro ⟨⟨w, hw, hi⟩, hbit⟩
    exact ⟨w, hw, hi, hbit⟩
  · rintro ⟨w, hw, hi, hbit⟩
    exact ⟨⟨w, hw, hi⟩, hbit⟩

private lemma atoms_reach {C : Circuit} {bit : Bool} (hr : ReadsBack 27 C) {w j : ℕ}
    (h : OrReaches 27 C w j) : atoms C bit (27 + j) ⊆ atoms C bit w := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨orIn_subset_of_orReaches hr h (Finset.mem_filter.mp hi).1,
    (Finset.mem_filter.mp hi).2⟩

private lemma atoms_quad {C : Circuit} {bit : Bool} {w : ℕ} {i : Fin 27}
    (hi : i ∈ atoms C bit w) :
    ∃ Q, isQuad Q ∧ (pgQuadInput Q ++ [bit]).getD i.val false = true := by
  rcases (Finset.mem_filter.mp hi).2 with hlt | hb
  · obtain ⟨Q, hQ, hget⟩ := quad_on_bit ⟨i.val, hlt⟩
    exact ⟨Q, hQ, (getD_append_bit_lt _ _ (by rw [pgQuadInput_length]; exact hlt)).trans hget⟩
  · by_cases hlt : i.val < 26
    · obtain ⟨Q, hQ, hget⟩ := quad_on_bit ⟨i.val, hlt⟩
      exact ⟨Q, hQ, (getD_append_bit_lt _ _ (by rw [pgQuadInput_length]; exact hlt)).trans hget⟩
    · have hv : i.val = 26 := by omega
      exact ⟨baseQuad 0, baseQuad_isQuad 0, by rw [hv, getD_append_bit_last _ _ (pgQuadInput_length _)]; exact hb⟩

private def active (bit : Bool) (i : Fin 27) : Prop := i.val < 26 ∨ bit = true

private lemma active_quad {bit : Bool} {i : Fin 27} (hi : active bit i) :
    ∃ Q, isQuad Q ∧ (pgQuadInput Q ++ [bit]).getD i.val false = true := by
  apply atoms_quad (C := ⟨[], 0⟩) (w := i.val)
  exact Finset.mem_filter.mpr ⟨by rw [orIn_input]; exact Finset.mem_singleton_self _, hi⟩

private lemma two_vertices_quad {bit : Bool} {i j : Fin 27}
    (hi : active bit i) (hj : active bit j) (hn : ¬ near i j) :
    ∃ Q, isQuad Q ∧ (pgQuadInput Q ++ [bit]).getD i.val false = true ∧
      (pgQuadInput Q ++ [bit]).getD j.val false = true := by
  have pts (p : Fin 13) (Q : Finset (Fin 13)) (hp : p ∈ Q) :
      (pgQuadInput Q ++ [bit]).getD (pt p).val false = true := by
    change (pgQuadInput Q ++ [bit]).getD p.val false = true
    rw [getD_append_bit_lt _ _ (by rw [pgQuadInput_length]; omega), pgQuadInput_getD_pt]
    exact decide_eq_true hp
  have lns (l : Fin 13) (Q : Finset (Fin 13)) (hl : missesLine Q l) :
      (pgQuadInput Q ++ [bit]).getD (ln l).val false = true := by
    change (pgQuadInput Q ++ [bit]).getD (toLn l).val false = true
    rw [toLn_val, getD_append_bit_lt _ _ (by rw [pgQuadInput_length]; omega), pgQuadInput_getD_ln]
    exact decide_eq_true hl
  by_cases hit : i.val < 26
  · by_cases hjt : j.val < 26
    · by_cases hip : i.val < 13
      · have hei : i = pt ⟨i.val, hip⟩ := Fin.ext rfl
        rw [hei] at hn ⊢
        by_cases hjp : j.val < 13
        · have hej : j = pt ⟨j.val, hjp⟩ := Fin.ext rfl
          rw [hej]
          by_cases e : (⟨i.val, hip⟩ : Fin 13) = ⟨j.val, hjp⟩
          · obtain ⟨Q, hQ, hp⟩ := quad_has_pt ⟨i.val, hip⟩
            exact ⟨Q, hQ, pts _ _ hp, pts _ _ (e ▸ hp)⟩
          · obtain ⟨Q, hQ, hp, hp'⟩ := quad_has_two_pts e
            exact ⟨Q, hQ, pts _ _ hp, pts _ _ hp'⟩
        · let l : Fin 13 := ⟨j.val - 13, by omega⟩
          have hej : j = ln l := Fin.ext (by change j.val = (toLn l).val; rw [toLn_val]; dsimp [l]; omega)
          rw [hej] at hn ⊢
          obtain ⟨Q, hQ, hp, hl⟩ := quad_noninc (p := ⟨i.val, hip⟩) (l := l)
            (fun h => hn (near_iff.mpr ⟨_, _, h, Or.inl ⟨rfl, rfl⟩⟩))
          exact ⟨Q, hQ, pts _ _ hp, lns _ _ hl⟩
      · let l : Fin 13 := ⟨i.val - 13, by omega⟩
        have hei : i = ln l := Fin.ext (by change i.val = (toLn l).val; rw [toLn_val]; dsimp [l]; omega)
        rw [hei] at hn ⊢
        by_cases hjp : j.val < 13
        · have hej : j = pt ⟨j.val, hjp⟩ := Fin.ext rfl
          rw [hej] at hn ⊢
          obtain ⟨Q, hQ, hp, hl⟩ := quad_noninc (p := ⟨j.val, hjp⟩) (l := l)
            (fun h => hn (near_iff.mpr ⟨_, _, h, Or.inr ⟨rfl, rfl⟩⟩))
          exact ⟨Q, hQ, lns _ _ hl, pts _ _ hp⟩
        · let l' : Fin 13 := ⟨j.val - 13, by omega⟩
          have hej : j = ln l' := Fin.ext (by change j.val = (toLn l').val; rw [toLn_val]; dsimp [l']; omega)
          rw [hej]
          by_cases e : l = l'
          · obtain ⟨Q, hQ, hl⟩ := quad_misses_line l
            exact ⟨Q, hQ, lns _ _ hl, lns _ _ (e ▸ hl)⟩
          · obtain ⟨Q, hQ, hl, hl'⟩ := quad_misses_two_lines e
            exact ⟨Q, hQ, lns _ _ hl, lns _ _ hl'⟩
    · obtain ⟨Q, hQ, h⟩ := active_quad hi
      have hv : j.val = 26 := by omega
      exact ⟨Q, hQ, h, by rw [hv, getD_append_bit_last _ _ (pgQuadInput_length _)]; exact hj.resolve_left hjt⟩
  · obtain ⟨Q, hQ, h⟩ := active_quad hj
    have hv : i.val = 26 := by omega
    exact ⟨Q, hQ, by rw [hv, getD_append_bit_last _ _ (pgQuadInput_length _)]; exact hi.resolve_left hit, h⟩
private abbrev Ed := Fin 13 × Fin 13

private def evalWire (C : Circuit) (inp : List Bool) (w : ℕ) : Prop :=
  (C.wires inp).getD w false = true

private lemma wire_hit_or_and {C : Circuit} (hm : Monotone2 C) (hr : ReadsBack 27 C)
    {inp : List Bool} {bit : Bool} (hl : inp.length = 26) (w : ℕ) :
    evalWire C (inp ++ [bit]) w ↔
      hit (inp ++ [bit]) (atoms C bit w) ∨
      ∃ g, (gateAt C g).op = GateOp.and ∧ OrReaches 27 C w g ∧ evalWire C (inp ++ [bit]) (27 + g) := by
  have hlen := append_bit_length inp bit hl
  constructor
  · intro h
    rcases wires_true_decomp hm hr _ hlen w h with h' | h'
    · exact Or.inl ((atoms_hit hl w).mpr h')
    · exact Or.inr h'
  · rintro (⟨i, hi, h⟩ | ⟨g, _, hrw, h⟩)
    · exact wires_true_of_mem_orIn hr _ hlen (Finset.mem_filter.mp hi).1 h
    · exact wires_true_of_orReaches hr _ hlen w g hrw h

private lemma and_eval_all {C : Circuit} (hr : ReadsBack 27 C) {g : ℕ}
    (hg : (gateAt C g).op = GateOp.and)
    {inp : List Bool} (hl : inp.length = 27) :
    evalWire C inp (27 + g) ↔ ∀ w ∈ (gateAt C g).inputs, evalWire C inp w := by
  unfold evalWire
  rw [wires_getD_gate hr inp hl (lt_gates_of_and hg), hg]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

private lemma inputs_two {C : Circuit} (hm : Monotone2 C) {g : ℕ}
    (hg : (gateAt C g).op = GateOp.and) :
    (gateAt C g).inputs = [] ∨ ∃ a b,
      a ∈ (gateAt C g).inputs ∧ b ∈ (gateAt C g).inputs ∧
      ∀ P : ℕ → Prop, (∀ w ∈ (gateAt C g).inputs, P w) ↔ P a ∧ P b := by
  have h := gate_inputs_len_le hm (lt_gates_of_and hg)
  rcases he : (gateAt C g).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨a, a, by simp, by simp, by simp⟩
  · exact Or.inr ⟨a, b, by simp, by simp, by simp⟩
  · simp [he] at h

private def Rect (A B : Finset (Fin 27)) : Prop := ∀ a ∈ A, ∀ b ∈ B, near a b

private lemma Rect.symm {A B : Finset (Fin 27)} (h : Rect A B) : Rect B A :=
  fun _ hb _ ha => near_symm (h _ ha _ hb)

private lemma Rect.sub {A B A' B' : Finset (Fin 27)} (h : Rect A B)
    (ha : A' ⊆ A) (hb : B' ⊆ B) : Rect A' B' :=
  fun _ ha' _ hb' => h _ (ha ha') _ (hb hb')

private lemma mem_adj {a : Fin 27} {B A : Finset (Fin 27)} (h : Rect A B) (ha : a ∈ A) :
    B ⊆ nbr a := fun _ hb => mem_nbr.mpr (h a ha _ hb)

private lemma rect_small_left {A B : Finset (Fin 27)} (h : Rect A B) (hb : 1 < B.card) :
    A.card ≤ 1 := by
  obtain ⟨u, hu, v, hv, hne⟩ := Finset.one_lt_card.mp hb
  have hs : A ⊆ nbr u ∩ nbr v := fun _ ha => Finset.mem_inter.mpr
    ⟨mem_adj h.symm hu ha, mem_adj h.symm hv ha⟩
  exact (Finset.card_le_card hs).trans (common_le _ _ hne)

private lemma singleton_of_small {A : Finset (Fin 27)} {c : Fin 27}
    (hc : c ∈ A) (h : A.card ≤ 1) : A = {c} :=
  Finset.eq_singleton_iff_unique_mem.mpr ⟨hc, fun _ hx => Finset.card_le_one.mp h _ hx _ hc⟩

private lemma pair_hit_atoms {C : Circuit} {bit : Bool} {w : ℕ} (p l : Fin 13) :
    hit (pgPairInput p l ++ [bit]) (atoms C bit w) ↔
      pt p ∈ atoms C bit w ∨ ln l ∈ atoms C bit w ∨
        ((26 : Fin 27) ∈ atoms C bit w) := by
  have hpt : (pgPairInput p l ++ [bit]).getD (pt p).val false = true := by
    change (pgPairInput p l ++ [bit]).getD p.val false = true
    rw [getD_append_bit_lt _ _ (by rw [pgPairInput_length]; omega), pgPairInput_getD_pt]
    simp
  have hln : (pgPairInput p l ++ [bit]).getD (ln l).val false = true := by
    change (pgPairInput p l ++ [bit]).getD (toLn l).val false = true
    rw [toLn_val, getD_append_bit_lt _ _ (by rw [pgPairInput_length]; omega), pgPairInput_getD_ln]
    simp
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hp : i.val < 13
    · have heq := pgPairInput_getD_pt p l ⟨i.val, hp⟩
      rw [← getD_append_bit_lt _ bit (by rw [pgPairInput_length]; omega), h] at heq
      have e : (⟨i.val, hp⟩ : Fin 13) = p := of_decide_eq_true heq.symm
      have ei : i = pt p := Fin.ext (congrArg (fun x : Fin 13 => x.val) e)
      exact Or.inl (ei ▸ hi)
    · by_cases hl : i.val < 26
      · let b : Fin 13 := ⟨i.val - 13, by omega⟩
        have ei : i = ln b := Fin.ext (by change i.val = (toLn b).val; rw [toLn_val]; dsimp [b]; omega)
        have heq := pgPairInput_getD_ln p l b
        have hval : 13 + b.val = i.val := by dsimp [b]; omega
        rw [hval, ← getD_append_bit_lt _ bit (by rw [pgPairInput_length]; omega), h] at heq
        have e : b = l := of_decide_eq_true heq.symm
        exact Or.inr (Or.inl ((ei.trans (congrArg ln e)) ▸ hi))
      · have e : i = (26 : Fin 27) := Fin.ext (by change i.val = 26; omega)
        exact Or.inr (Or.inr (e ▸ hi))
  · rintro (h | h | h)
    · exact ⟨pt p, h, hpt⟩
    · exact ⟨ln l, h, hln⟩
    · refine ⟨26, h, ?_⟩
      change (pgPairInput p l ++ [bit]).getD 26 false = true
      rw [getD_append_bit_last _ _ (pgPairInput_length _ _)]
      exact (Finset.mem_filter.mp h).2.resolve_left (by decide)

private def pairHit (e : Ed) (S : Finset (Fin 27)) : Prop :=
  pt e.1 ∈ S ∨ ln e.2 ∈ S ∨ (26 : Fin 27) ∈ S

private lemma hit_pair {C : Circuit} {bit : Bool} {w : ℕ} {e : Ed} :
    hit (pgPairInput e.1 e.2 ++ [bit]) (atoms C bit w) ↔ pairHit e (atoms C bit w) :=
  pair_hit_atoms e.1 e.2

private lemma rect_pair {A B : Finset (Fin 27)} {e : Ed}
    (h : Rect A B) (ha : pairHit e A) (hb : pairHit e B) :
    (pt e.1 ∈ A ∧ ln e.2 ∈ B) ∨ (ln e.2 ∈ A ∧ pt e.1 ∈ B) := by
  have hno (u : Fin 27) : ¬ near (26 : Fin 27) u := by
    intro h
    obtain ⟨p, l, _, ⟨hp, _⟩ | ⟨hl, _⟩⟩ := near_iff.mp h
    · have hv := congrArg Fin.val hp
      change 26 = p.val at hv
      omega
    · have hv := congrArg Fin.val hl
      change 26 = (toLn l).val at hv
      rw [toLn_val] at hv
      omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · exact (near_irrefl _ (h _ ha _ hb)).elim
  · exact Or.inl ⟨ha, hb⟩
  · exact (hno _ (near_symm (h _ ha _ hb))).elim
  · exact Or.inr ⟨ha, hb⟩
  · exact (near_irrefl _ (h _ ha _ hb)).elim
  · exact (hno _ (near_symm (h _ ha _ hb))).elim
  · exact (hno _ (h _ ha _ hb)).elim
  · exact (hno _ (h _ ha _ hb)).elim
  · exact (hno _ (h _ ha _ hb)).elim

private lemma pair_split_three {A B Y : Finset (Fin 27)} {e : Ed}
    (hA : (26 : Fin 27) ∉ A) (hB : (26 : Fin 27) ∉ B) (hY : (26 : Fin 27) ∉ Y)
    (ha : pairHit e A) (hb : pairHit e B) (hy : pairHit e Y) :
    (pairHit e (A ∩ B) ∧ pairHit e Y) ∨
      (pairHit e (A ∩ Y) ∧ pairHit e B) ∨ (pairHit e (B ∩ Y) ∧ pairHit e A) := by
  have ha' := ha
  have hb' := hb
  have hy' := hy
  simp only [pairHit, hA, hB, hY, or_false] at ha' hb' hy'
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rcases hy' with hy' | hy'
  all_goals first
    | exact Or.inl ⟨Or.inl (Finset.mem_inter.mpr ⟨ha', hb'⟩), hy⟩
    | exact Or.inl ⟨Or.inr (Or.inl (Finset.mem_inter.mpr ⟨ha', hb'⟩)), hy⟩
    | exact Or.inr (Or.inl ⟨Or.inl (Finset.mem_inter.mpr ⟨ha', hy'⟩), hb⟩)
    | exact Or.inr (Or.inl ⟨Or.inr (Or.inl (Finset.mem_inter.mpr ⟨ha', hy'⟩)), hb⟩)
    | exact Or.inr (Or.inr ⟨Or.inl (Finset.mem_inter.mpr ⟨hb', hy'⟩), ha⟩)
    | exact Or.inr (Or.inr ⟨Or.inr (Or.inl (Finset.mem_inter.mpr ⟨hb', hy'⟩)), ha⟩)

private def down (u : Fin 27) : Fin 26 := ⟨u.val % 26, Nat.mod_lt _ (by decide)⟩

private lemma down_pt (p : Fin 13) : down (pt p) = toPt p :=
  Fin.ext (Nat.mod_eq_of_lt (toPt p).isLt)

private lemma down_ln (l : Fin 13) : down (ln l) = toLn l :=
  Fin.ext (Nat.mod_eq_of_lt (toLn l).isLt)

private def star (c : Fin 27) (L : Finset (Fin 27)) : Finset Ed :=
  L.image (fun u => mkEdge (down c) (down u))

private lemma star_mono {c : Fin 27} {L M : Finset (Fin 27)} (h : L ⊆ M) :
    star c L ⊆ star c M := Finset.image_subset_image h

private lemma mem_star_pt {e : Ed} {L : Finset (Fin 27)} (h : ln e.2 ∈ L) :
    e ∈ star (pt e.1) L :=
  Finset.mem_image.mpr ⟨ln e.2, h, by simp [down_pt, down_ln, mkEdge_pt_ln]⟩

private lemma mem_star_ln {e : Ed} {L : Finset (Fin 27)} (h : pt e.1 ∈ L) :
    e ∈ star (ln e.2) L :=
  Finset.mem_image.mpr ⟨pt e.1, h, by simp [down_pt, down_ln, mkEdge_ln_pt]⟩

private lemma rect_star {c : Fin 27} {L : Finset (Fin 27)} {e : Ed}
    (h : Rect {c} L) (hc : pairHit e {c}) (hl : pairHit e L) :
    e ∈ star c L := by
  rcases rect_pair h hc hl with ⟨hc', hl'⟩ | ⟨hc', hl'⟩
  · have he := Finset.mem_singleton.mp hc'
    rw [← he]; exact mem_star_pt hl'
  · have he := Finset.mem_singleton.mp hc'
    rw [← he]; exact mem_star_ln hl'

private abbrev Root := Fin 27 × ℕ

private def leaves (C : Circuit) (bit : Bool) (c : Fin 27) (w : ℕ) : Finset (Fin 27) :=
  atoms C bit w ∩ nbr c

private def covered (C : Circuit) (bit : Bool) (R : Finset Root) : Finset Ed :=
  R.biUnion (fun r => star r.1 (leaves C bit r.1 r.2))

private lemma covered_mono {C : Circuit} {bit : Bool} {R S : Finset Root} (h : R ⊆ S) :
    covered C bit R ⊆ covered C bit S := Finset.biUnion_subset_biUnion_of_subset_left _ h

private lemma covered_insert {C : Circuit} {bit : Bool} {r : Root} {R : Finset Root} :
    covered C bit (insert r R) = star r.1 (leaves C bit r.1 r.2) ∪ covered C bit R := by
  ext e
  simp only [covered, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨x, rfl | hx, he⟩
    · exact Or.inl he
    · exact Or.inr ⟨x, hx, he⟩
  · rintro (he | ⟨x, hx, he⟩)
    · exact ⟨r, Or.inl rfl, he⟩
    · exact ⟨x, Or.inr hx, he⟩

private lemma covered_single {C : Circuit} {bit : Bool} {r : Root} :
    covered C bit {r} = star r.1 (leaves C bit r.1 r.2) := by
  ext e
  simp [covered]

private lemma covered_empty (C : Circuit) (bit : Bool) :
    covered C bit ∅ = ∅ := by simp [covered]

private lemma covered_card {C : Circuit} {bit : Bool} {R : Finset Root} :
    (covered C bit R).card ≤ 4 * R.card := by
  calc
    _ ≤ ∑ r ∈ R, (star r.1 (leaves C bit r.1 r.2)).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ R, 4 := Finset.sum_le_sum fun r _ =>
      Finset.card_image_le.trans ((Finset.card_le_card Finset.inter_subset_right).trans (nbr_le r.1))
    _ = _ := by simp [Nat.mul_comm]

private lemma leaves_subset {C : Circuit} {bit : Bool} {c : Fin 27} {w : ℕ} {L : Finset (Fin 27)}
    (h1 : L ⊆ atoms C bit w) (h2 : L ⊆ nbr c) : L ⊆ leaves C bit c w :=
  fun _ h => Finset.mem_inter.mpr ⟨h1 h, h2 h⟩

private lemma rect_root {C : Circuit} {bit : Bool} {c : Fin 27} {w : ℕ} {e : Ed}
    {L : Finset (Fin 27)} (hs : L ⊆ atoms C bit w)
    (h : Rect {c} L) (hc : pairHit e {c}) (hl : pairHit e L) :
    e ∈ star c (leaves C bit c w) :=
  star_mono (leaves_subset hs (mem_adj h (Finset.mem_singleton_self c))) (rect_star h hc hl)

private lemma rect_cover {C : Circuit} {bit : Bool} {a b : ℕ} (hr : ReadsBack 27 C)
    (h : Rect (atoms C bit a) (atoms C bit b)) :
    ∃ r : Root, atoms C bit r.2 ⊆ nbr r.1 ∧
      ∀ e : Ed, pairHit e (atoms C bit a) → pairHit e (atoms C bit b) →
        e ∈ star r.1 (leaves C bit r.1 r.2) := by
  by_cases ha : (atoms C bit a).Nonempty
  · by_cases hb : (atoms C bit b).Nonempty
    · obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      by_cases hs : (atoms C bit a).card ≤ 1
      · have he := singleton_of_small hc hs
        refine ⟨(c, b), mem_adj h hc, fun e hea heb => rect_root (Finset.Subset.refl _) ?_ ?_ heb⟩
        · rwa [he] at h
        · rwa [he] at hea
      · have he := singleton_of_small hd (rect_small_left h.symm (by omega))
        refine ⟨(d, a), mem_adj h.symm hd, fun e hea heb => rect_root (Finset.Subset.refl _) ?_ ?_ hea⟩
        · have h' := h.symm
          rwa [he] at h'
        · rwa [he] at heb
    · refine ⟨(0, 27 + C.gates.length), ?_, ?_⟩
      · intro i hi
        simp [atoms, orIn_ge hr (Nat.le_refl _)] at hi
      · intro e _ he
        rw [Finset.not_nonempty_iff_eq_empty.mp hb] at he
        simp [pairHit] at he
  · refine ⟨(0, 27 + C.gates.length), ?_, ?_⟩
    · intro i hi
      simp [atoms, orIn_ge hr (Nat.le_refl _)] at hi
    · intro e he
      rw [Finset.not_nonempty_iff_eq_empty.mp ha] at he
      simp [pairHit] at he

private def spare (C : Circuit) (bit : Bool) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
    (atoms C bit (27 + j)).Nonempty ∧
    ((atoms C bit (27 + j)).card ≤ 1 ∨
      ∃ i ∈ atoms C bit (27 + j), ∃ k ∈ atoms C bit (27 + j), near i k)

private lemma spare_of_mixed {C : Circuit} {bit : Bool}
    (hm : Monotone2 C) (hr : ReadsBack 27 C) {w : ℕ} {i k : Fin 27}
    (hi : i ∈ atoms C bit w) (hk : k ∈ atoms C bit w) (hik : near i k) :
    ∃ j, spare C bit j := by
  have hn : ¬ w < 27 := by
    intro hl
    have hh : orIn 27 C w = {⟨w, hl⟩} := orIn_input ⟨w, hl⟩
    have hi' := (Finset.mem_filter.mp hi).1
    have hk' := (Finset.mem_filter.mp hk).1
    rw [hh, Finset.mem_singleton] at hi' hk'
    exact near_irrefl i ((hk'.trans hi'.symm) ▸ hik)
  have hu : w < 27 + C.gates.length := by
    by_contra h
    have hi' := (Finset.mem_filter.mp hi).1
    rw [orIn_ge hr (by omega)] at hi'
    exact Finset.notMem_empty _ hi'
  let j := w - 27
  have he : 27 + j = w := by dsimp [j]; omega
  have hj : j < C.gates.length := by dsimp [j]; omega
  rcases gateOp_and_or hm hj with h | h
  · have hi' := (Finset.mem_filter.mp hi).1
    rw [← he, orIn_and hr hj h] at hi'
    exact (Finset.notMem_empty _ hi').elim
  · rw [← he] at hi hk
    exact ⟨j, hj, h, ⟨i, hi⟩, Or.inr ⟨i, hi, k, hk, hik⟩⟩

private lemma spare_of_singleton_path {C : Circuit} {bit : Bool}
    (hr : ReadsBack 27 C) {w lo : ℕ} {i : Fin 27}
    (hw : OrReaches 27 C w lo) (hlo : (gateAt C lo).op = GateOp.and)
    (h : atoms C bit w = {i}) :
    ∃ j, spare C bit j := by
  obtain ⟨j, hj, rfl, he | ⟨hor, u, hu, hur⟩⟩ := (orReaches_iff hr _ _).mp hw
  · subst lo
    have hn : i ∈ atoms C bit (27 + j) := h ▸ Finset.mem_singleton_self i
    have hn' := (Finset.mem_filter.mp hn).1
    rw [orIn_and hr hj hlo] at hn'
    exact (Finset.notMem_empty _ hn').elim
  · exact ⟨j, hj, hor, by rw [h]; exact Finset.singleton_nonempty _, Or.inl (by rw [h]; simp)⟩

private def PureRoots (C : Circuit) (bit : Bool) (R : Finset Root) : Prop :=
  ∀ r ∈ R, atoms C bit r.2 ⊆ nbr r.1

private def Coherent (C : Circuit) (bit : Bool) (R : Finset Root) : Prop :=
  ∃ c : Fin 27, ∀ r ∈ R, r.1 ≠ c → atoms C bit r.2 ⊆ nbr r.1

private def Limits (C : Circuit) (bit : Bool) (R : Finset Root) : Prop :=
  (covered C bit R).card ≤ 5 ∨
    (PureRoots C bit R ∧ ∃ j, spare C bit j)

private lemma pure_coherent {C : Circuit} {bit : Bool} {R : Finset Root} (h : PureRoots C bit R) :
    Coherent C bit R := ⟨0, fun r hr _ => h r hr⟩

private lemma singleton_coherent (C : Circuit) (bit : Bool) (r : Root) : Coherent C bit {r} := by
  refine ⟨r.1, ?_⟩
  intro x hx hn
  rw [Finset.mem_singleton.mp hx] at hn
  exact (hn rfl).elim

private lemma same_center_small {C : Circuit} {bit : Bool} {c : Fin 27} {R : Finset Root}
    (hc : ∀ r ∈ R, r.1 = c) : (covered C bit R).card ≤ 5 := by
  have hs : covered C bit R ⊆ star c (nbr c) := by
    intro e he
    obtain ⟨r, hr, he⟩ := Finset.mem_biUnion.mp he
    have he' := star_mono Finset.inter_subset_right he
    rwa [hc r hr] at he'
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans ((nbr_le c).trans (by decide)))
private def Box (U V : Finset (Fin 27)) (e : Ed) : Prop := pairHit e U ∧ pairHit e V

private def Plan (C : Circuit) (bit : Bool) (k : ℕ) (Q : Ed → Prop) : Prop :=
  ∃ R : Finset Root, R.card ≤ k ∧ Coherent C bit R ∧ Limits C bit R ∧
    ∀ e, Q e → e ∈ covered C bit R

private lemma plan_imp {C : Circuit} {bit : Bool} {k : ℕ} {P Q : Ed → Prop}
    (h : Plan C bit k Q) (hPQ : ∀ e, P e → Q e) : Plan C bit k P := by
  obtain ⟨R, hk, hc, hl, hh⟩ := h
  exact ⟨R, hk, hc, hl, fun e he => hh e (hPQ e he)⟩

private lemma plan_one {C : Circuit} {bit : Bool} {Q : Ed → Prop} {k : ℕ} (hk : 1 ≤ k)
    (r : Root) (h : ∀ e, Q e → e ∈ star r.1 (leaves C bit r.1 r.2)) : Plan C bit k Q := by
  refine ⟨{r}, by simpa, singleton_coherent C bit r, Or.inl ?_, ?_⟩
  · exact (covered_card (R := {r})).trans (by simp)
  · intro e he
    rw [covered_single]
    exact h e he

private lemma plan_none {C : Circuit} {bit : Bool} {Q : Ed → Prop} {k : ℕ}
    (h : ∀ e, ¬ Q e) : Plan C bit k Q := by
  exact ⟨∅, by simp, pure_coherent (by simp [PureRoots]), Or.inl (by simp [covered_empty]),
    fun e he => (h e he).elim⟩

private lemma plan_box {C : Circuit} {bit : Bool} {a b k : ℕ} (hr : ReadsBack 27 C) (hk : 1 ≤ k)
    (h : Rect (atoms C bit a) (atoms C bit b)) :
    Plan C bit k (Box (atoms C bit a) (atoms C bit b)) := by
  obtain ⟨r, _, hr⟩ := rect_cover hr h
  exact plan_one hk r (fun e he => hr e he.1 he.2)

private lemma plan_two {C : Circuit} {bit : Bool} {P : Ed → Prop} (r s : Root)
    (hc : Coherent C bit {r, s}) (hl : Limits C bit {r, s})
    (h : ∀ e, P e → e ∈ star r.1 (leaves C bit r.1 r.2) ∨
      e ∈ star s.1 (leaves C bit s.1 s.2)) : Plan C bit 2 P := by
  refine ⟨{r, s}, (Finset.card_insert_le _ _).trans (by simp), hc, hl, ?_⟩
  intro e he
  rw [covered_insert, covered_single, Finset.mem_union]
  exact h e he

private lemma plan_same_center {C : Circuit} {bit : Bool} {P : Ed → Prop}
    (c : Fin 27) (a b : ℕ)
    (h : ∀ e, P e → e ∈ star c (leaves C bit c a) ∨ e ∈ star c (leaves C bit c b)) :
    Plan C bit 2 P := by
  have hc : ∀ r ∈ ({(c, a), (c, b)} : Finset Root), r.1 = c := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | h'
    · rfl
    · rw [Finset.mem_singleton.mp h']
  exact plan_two (c, a) (c, b) ⟨c, fun r hr hn => (hn (hc r hr)).elim⟩
    (Or.inl (same_center_small hc)) h

private lemma pure_insert {C : Circuit} {bit : Bool} {p q : Root}
    (hp : atoms C bit p.2 ⊆ nbr p.1) (hq : atoms C bit q.2 ⊆ nbr q.1) :
    PureRoots C bit {p, q} := by
  intro r hr
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact hp
  · rwa [Finset.mem_singleton.mp hr]

private lemma pairHit_empty (e : Ed) : ¬ pairHit e ∅ := by simp [pairHit]

private lemma pairHit_union {e : Ed} {A B : Finset (Fin 27)} :
    pairHit e (A ∪ B) ↔ pairHit e A ∨ pairHit e B := by
  simp only [pairHit, Finset.mem_union]
  tauto

private lemma rect_singleton_right {C : Circuit} {bit : Bool} {U V : Finset (Fin 27)}
    {c : Fin 27} {w : ℕ} {e : Ed} (heq : V = {c}) (h : Rect U V)
    (hs : U ⊆ atoms C bit w) (he : Box U V e) : e ∈ star c (leaves C bit c w) := by
  have h' := h.symm
  rw [heq] at h'
  exact rect_root hs h' (heq ▸ he.2) he.1

private lemma rect_singleton_left {C : Circuit} {bit : Bool} {U V : Finset (Fin 27)}
    {c : Fin 27} {w : ℕ} {e : Ed} (heq : U = {c}) (h : Rect U V)
    (hs : V ⊆ atoms C bit w) (he : Box U V e) : e ∈ star c (leaves C bit c w) :=
  rect_singleton_right heq h.symm hs ⟨he.2, he.1⟩

private lemma shifted_root {C : Circuit} {bit : Bool} {u : Fin 27} (ha : active bit u) :
    atoms C bit u.val = {u} := by
  unfold atoms
  rw [orIn_input]
  ext v
  simp only [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨And.left, fun h => ⟨h, h.symm ▸ ha⟩⟩

private lemma plan_union_product {C : Circuit} {bit : Bool} {x b y : ℕ}
    (h : Rect (atoms C bit x ∪ atoms C bit b) (atoms C bit y)) :
    Plan C bit 2 (Box (atoms C bit x ∪ atoms C bit b) (atoms C bit y)) := by
  by_cases hY : (atoms C bit y).Nonempty
  · obtain ⟨c, hc⟩ := hY
    by_cases hSmall : (atoms C bit y).card ≤ 1
    · have heq := singleton_of_small hc hSmall
      apply plan_same_center c x b
      intro e he
      rcases pairHit_union.mp he.1 with hx | hb
      · exact Or.inl (rect_singleton_right heq (h.sub Finset.subset_union_left (Finset.Subset.refl _))
          (Finset.Subset.refl _) ⟨hx, he.2⟩)
      · exact Or.inr (rect_singleton_right heq (h.sub Finset.subset_union_right (Finset.Subset.refl _))
          (Finset.Subset.refl _) ⟨hb, he.2⟩)
    · by_cases hX : (atoms C bit x ∪ atoms C bit b).Nonempty
      · obtain ⟨u, hu⟩ := hX
        have heq := singleton_of_small hu (rect_small_left h (by omega))
        exact plan_one (by decide) (u, y) (fun _ he =>
          rect_singleton_left heq h (Finset.Subset.refl _) he)
      · exact plan_none (fun e he => pairHit_empty e
          (Finset.not_nonempty_iff_eq_empty.mp hX ▸ he.1))
  · exact plan_none (fun e he => pairHit_empty e
      (Finset.not_nonempty_iff_eq_empty.mp hY ▸ he.2))

private lemma plan_both_products {C : Circuit} {bit : Bool} {lo a b x y : ℕ}
    (hlo : (gateAt C lo).op = GateOp.and) (hr : ReadsBack 27 C)
    (hx : OrReaches 27 C x lo) (hy : OrReaches 27 C y lo)
    (h₁ : Rect (atoms C bit a) (atoms C bit b))
    (h₂ : Rect (atoms C bit x) (atoms C bit y)) :
    Plan C bit 2 (fun e => Box (atoms C bit a) (atoms C bit b) e ∨
      Box (atoms C bit x) (atoms C bit y) e) := by
  by_cases hX : (atoms C bit x).Nonempty
  · by_cases hY : (atoms C bit y).Nonempty
    · obtain ⟨r, hrp, hrc⟩ := rect_cover hr h₁
      obtain ⟨s, hsp, hsc⟩ := rect_cover hr h₂
      have hs : ∃ j, spare C bit j := by
        by_cases h : (atoms C bit x).card ≤ 1
        · obtain ⟨i, hi⟩ := hX
          exact spare_of_singleton_path hr hx hlo (singleton_of_small hi h)
        · obtain ⟨i, hi⟩ := hY
          exact spare_of_singleton_path hr hy hlo
            (singleton_of_small hi (rect_small_left h₂.symm (by omega)))
      exact plan_two r s (pure_coherent (pure_insert hrp hsp)) (Or.inr ⟨pure_insert hrp hsp, hs⟩)
        (fun e h => h.elim (fun h => Or.inl (hrc e h.1 h.2)) (fun h => Or.inr (hsc e h.1 h.2)))
    · apply plan_imp (plan_box hr (by decide : 1 ≤ 2) h₁)
      rintro e (he | he)
      · exact he
      · exact (pairHit_empty e (Finset.not_nonempty_iff_eq_empty.mp hY ▸ he.2)).elim
  · apply plan_imp (plan_box hr (by decide : 1 ≤ 2) h₁)
    rintro e (he | he)
    · exact he
    · exact (pairHit_empty e (Finset.not_nonempty_iff_eq_empty.mp hX ▸ he.1)).elim
private lemma singleton_Y_plan {C : Circuit} {bit : Bool} {a b x y : ℕ} {c : Fin 27}
    (hy : atoms C bit y = {c})
    (hD : Rect (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)) (atoms C bit y))
    (hE : Rect (atoms C bit a ∩ atoms C bit y) (atoms C bit b))
    (hF : Rect (atoms C bit b ∩ atoms C bit y) (atoms C bit a)) :
    Plan C bit 2 (fun e =>
      Box (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)) (atoms C bit y) e ∨
      Box (atoms C bit a ∩ atoms C bit y) (atoms C bit b) e ∨
      Box (atoms C bit b ∩ atoms C bit y) (atoms C bit a) e) := by
  have hd (e : Ed) (he : Box (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)) (atoms C bit y) e) :
      e ∈ star c (leaves C bit c x) ∨ pairHit e (atoms C bit a ∩ atoms C bit b) := by
    rcases pairHit_union.mp he.1 with hx | hab
    · exact Or.inl (rect_singleton_right hy
        (hD.sub Finset.subset_union_left (Finset.Subset.refl _)) (Finset.Subset.refl _) ⟨hx, he.2⟩)
    · exact Or.inr hab
  have hfin : c ∈ atoms C bit y := hy ▸ Finset.mem_singleton_self c
  by_cases ha : c ∈ atoms C bit a
  · have hb : c ∉ atoms C bit b :=
      fun h => near_irrefl _ (hE _ (Finset.mem_inter.mpr ⟨ha, hfin⟩) _ h)
    apply plan_same_center c x b
    rintro e (he | he | he)
    · rcases hd e he with h | h
      · exact Or.inl h
      · exact Or.inr (rect_singleton_right hy
          (hD.sub Finset.subset_union_right (Finset.Subset.refl _)) Finset.inter_subset_right ⟨h, he.2⟩)
    · have heq := singleton_of_small (Finset.mem_inter.mpr ⟨ha, hfin⟩)
          ((Finset.card_le_card (Finset.inter_subset_right : _ ⊆ atoms C bit y)).trans (by simp [hy]))
      exact Or.inr (rect_singleton_left heq hE (Finset.Subset.refl _) he)
    · exfalso
      have hzero : atoms C bit b ∩ atoms C bit y = ∅ := by simp [hy, hb]
      exact pairHit_empty e (hzero ▸ he.1)
  · apply plan_same_center c x a
    rintro e (he | he | he)
    · rcases hd e he with h | h
      · exact Or.inl h
      · exact Or.inr (rect_singleton_right hy
          (hD.sub Finset.subset_union_right (Finset.Subset.refl _)) Finset.inter_subset_left ⟨h, he.2⟩)
    · exfalso
      have hzero : atoms C bit a ∩ atoms C bit y = ∅ := by simp [hy, ha]
      exact pairHit_empty e (hzero ▸ he.1)
    · have hb : c ∈ atoms C bit b := by
        by_contra hn
        have hzero : atoms C bit b ∩ atoms C bit y = ∅ := by simp [hy, hn]
        exact pairHit_empty e (hzero ▸ he.1)
      have heq := singleton_of_small (Finset.mem_inter.mpr ⟨hb, hfin⟩)
          ((Finset.card_le_card (Finset.inter_subset_right : _ ⊆ atoms C bit y)).trans (by simp [hy]))
      exact Or.inr (rect_singleton_left heq hF (Finset.Subset.refl _) he)

private lemma plan_two_intersections {C : Circuit} {bit : Bool} {a b x y : ℕ}
    (hm : Monotone2 C) (hr : ReadsBack 27 C)
    (hD : Rect (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)) (atoms C bit y))
    (hE : Rect (atoms C bit a ∩ atoms C bit y) (atoms C bit b))
    (hF : Rect (atoms C bit b ∩ atoms C bit y) (atoms C bit a))
    {p l : Fin 27} (hp : p ∈ atoms C bit a ∩ atoms C bit y)
    (hl : l ∈ atoms C bit b ∩ atoms C bit y) :
    Plan C bit 2 (fun e =>
      Box (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)) (atoms C bit y) e ∨
      Box (atoms C bit a ∩ atoms C bit y) (atoms C bit b) e ∨
      Box (atoms C bit b ∩ atoms C bit y) (atoms C bit a) e) := by
  have hp' := Finset.mem_inter.mp hp
  have hl' := Finset.mem_inter.mp hl
  have hpl := hE _ hp _ hl'.1
  have hD0 : atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact no_triangle (hD _ hq _ hp'.2) (hD _ hq _ hl'.2) hpl
  have h₁ := mem_adj hE hp
  have h₂ := mem_adj hF hl
  have hpr : PureRoots C bit {(p, b), (l, a)} := pure_insert h₁ h₂
  have hrE {u v : ℕ} {s t : Fin 27} (he : Rect (atoms C bit u ∩ atoms C bit y) (atoms C bit v))
      (hs : s ∈ atoms C bit u ∩ atoms C bit y) (ht : t ∈ atoms C bit v)
      (e : Ed) (h : Box (atoms C bit u ∩ atoms C bit y) (atoms C bit v) e) :
      e ∈ star s (leaves C bit s v) ∨ e ∈ star t (leaves C bit t u) := by
    by_cases hcard : (atoms C bit v).card ≤ 1
    · exact Or.inr (rect_singleton_right (singleton_of_small ht hcard) he Finset.inter_subset_left h)
    · exact Or.inl (rect_singleton_left (singleton_of_small hs (rect_small_left he (by omega)))
        he (Finset.Subset.refl _) h)
  apply plan_two (p, b) (l, a) (pure_coherent hpr)
    (Or.inr ⟨hpr, spare_of_mixed hm hr hp'.2 hl'.2 hpl⟩)
  rintro e (he | he | he)
  · exact (pairHit_empty e (hD0 ▸ he.1)).elim
  · exact hrE hE hp hl'.1 e he
  · exact (hrE hF hl hp'.1 e he).symm

private lemma plan_one_intersection {C : Circuit} {bit : Bool} {lo a b x y : ℕ}
    (hm : Monotone2 C) (hr : ReadsBack 27 C) (hlo : (gateAt C lo).op = GateOp.and)
    (hx : OrReaches 27 C x lo)
    (hD : Rect (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)) (atoms C bit y))
    (hE : Rect (atoms C bit a ∩ atoms C bit y) (atoms C bit b)) (hy : 1 < (atoms C bit y).card) :
    Plan C bit 2 (fun e =>
      Box (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)) (atoms C bit y) e ∨
      Box (atoms C bit a ∩ atoms C bit y) (atoms C bit b) e) := by
  have noneD : ¬(atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)).Nonempty →
      ∀ e, ¬ Box (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)) (atoms C bit y) e :=
    fun h e he => pairHit_empty e (Finset.not_nonempty_iff_eq_empty.mp h ▸ he.1)
  by_cases hE' : (atoms C bit a ∩ atoms C bit y).Nonempty ∧ (atoms C bit b).Nonempty
  · obtain ⟨⟨p, hp⟩, ⟨l, hl⟩⟩ := hE'
    by_cases hD' : (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)).Nonempty
    · obtain ⟨q, hq⟩ := hD'
      have heq := singleton_of_small hq (rect_small_left hD hy)
      have hyq := mem_adj hD hq
      have d (e : Ed) (he : Box (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)) (atoms C bit y) e) :
          e ∈ star q (leaves C bit q y) :=
        rect_singleton_left heq hD (Finset.Subset.refl _) he
      by_cases hb : (atoms C bit b).card ≤ 1
      · have hB := singleton_of_small hl hb
        by_cases hql : q = l
        · subst l
          exact plan_one (by decide) (q, y) (fun e he => he.elim (d e)
            (rect_singleton_right hB hE Finset.inter_subset_right))
        · have hsub : atoms C bit a ∩ atoms C bit y ⊆ nbr q ∩ nbr l :=
            fun _ hu => Finset.mem_inter.mpr ⟨hyq (Finset.mem_inter.mp hu).2, mem_adj hE.symm hl hu⟩
          have hAp := singleton_of_small hp ((Finset.card_le_card hsub).trans (common_le _ _ hql))
          have hat : atoms C bit p.val = {p} := shifted_root (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2
          have hpr : PureRoots C bit {(q, y), (l, p.val)} := pure_insert hyq (by
            rw [hat, ← hAp]
            exact mem_adj hE.symm hl)
          refine plan_two (q, y) (l, p.val) (pure_coherent hpr) (Or.inl ?_) ?_
          · rw [covered_insert, covered_single]
            have h₁ : (star q (leaves C bit q y)).card ≤ 4 :=
              Finset.card_image_le.trans ((Finset.card_le_card Finset.inter_subset_right).trans (nbr_le q))
            have h₂ : (star l (leaves C bit l p.val)).card ≤ 1 := by
              apply Finset.card_image_le.trans
              exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp [hat])
            exact (Finset.card_union_le _ _).trans (Nat.add_le_add h₁ h₂)
          · rintro e (he | he)
            · exact Or.inl (d e he)
            · exact Or.inr (rect_singleton_right hB hE (by rw [hat, hAp]) he)
      · have hAp := singleton_of_small hp (rect_small_left hE (by omega))
        have hpr : PureRoots C bit {(q, y), (p, b)} := pure_insert hyq (mem_adj hE hp)
        have hex : ∃ j, spare C bit j := by
          rcases Finset.mem_union.mp hq with hq | hq
          · have hX : atoms C bit x = {q} := by
              apply singleton_of_small hq
              exact (Finset.card_le_card (Finset.subset_union_left :
                atoms C bit x ⊆ atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b))).trans (by simp [heq])
            exact spare_of_singleton_path hr hx hlo hX
          · exact spare_of_mixed hm hr (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hq).1
              (hD _ (Finset.mem_union_right _ hq) _ (Finset.mem_inter.mp hp).2 |> near_symm)
        exact plan_two (q, y) (p, b) (pure_coherent hpr) (Or.inr ⟨hpr, hex⟩) (fun e he =>
          he.elim (fun h => Or.inl (d e h)) (fun h =>
            Or.inr (rect_singleton_left hAp hE (Finset.Subset.refl _) h)))
    · by_cases hb : (atoms C bit b).card ≤ 1
      · exact plan_one (by decide) (l, y) (fun e he => he.elim
          (fun h => (noneD hD' e h).elim)
          (rect_singleton_right (singleton_of_small hl hb) hE Finset.inter_subset_right))
      · exact plan_one (by decide) (p, b) (fun e he => he.elim
          (fun h => (noneD hD' e h).elim)
          (rect_singleton_left (singleton_of_small hp (rect_small_left hE (by omega)))
            hE (Finset.Subset.refl _)))
  · by_cases hD' : (atoms C bit x ∪ (atoms C bit a ∩ atoms C bit b)).Nonempty
    · obtain ⟨q, hq⟩ := hD'
      have heq := singleton_of_small hq (rect_small_left hD hy)
      apply plan_one (by decide) (q, y)
      rintro e (he | he)
      · exact rect_singleton_left heq hD (Finset.Subset.refl _) he
      · exfalso
        apply hE'
        constructor
        · by_contra h
          exact pairHit_empty e (Finset.not_nonempty_iff_eq_empty.mp h ▸ he.1)
        · by_contra h
          exact pairHit_empty e (Finset.not_nonempty_iff_eq_empty.mp h ▸ he.2)
    · apply plan_none
      rintro e (he | he)
      · exact noneD hD' e he
      · apply hE'
        constructor
        · by_contra h
          exact pairHit_empty e (Finset.not_nonempty_iff_eq_empty.mp h ▸ he.1)
        · by_contra h
          exact pairHit_empty e (Finset.not_nonempty_iff_eq_empty.mp h ▸ he.2)
private lemma quad_rect {bit : Bool} {U V : Finset (Fin 27)}
    (hu : ∀ u ∈ U, active bit u) (hv : ∀ v ∈ V, active bit v)
    (h : ∀ Q, isQuad Q → hit (pgQuadInput Q ++ [bit]) U → ¬ hit (pgQuadInput Q ++ [bit]) V) :
    Rect U V := by
  intro u hum v hvm
  by_contra hn
  obtain ⟨Q, hQ, hqu, hqv⟩ := two_vertices_quad (hu _ hum) (hv _ hvm) hn
  exact h Q hQ ⟨u, hum, hqu⟩ ⟨v, hvm, hqv⟩

private lemma active_atoms {C : Circuit} {bit : Bool} {w : ℕ} : ∀ u ∈ atoms C bit w, active bit u :=
  fun _ h => (Finset.mem_filter.mp h).2

private lemma hit_sub {inp : List Bool} {U V : Finset (Fin 27)} (h : U ⊆ V) : hit inp U → hit inp V :=
  fun ⟨i, hi, hv⟩ => ⟨i, h hi, hv⟩

private lemma hit_union {inp : List Bool} {U V : Finset (Fin 27)} :
    hit inp (U ∪ V) ↔ hit inp U ∨ hit inp V := by
  constructor
  · rintro ⟨i, hi, hv⟩
    exact (Finset.mem_union.mp hi).elim (fun h => Or.inl ⟨i, h, hv⟩) (fun h => Or.inr ⟨i, h, hv⟩)
  · exact fun h => h.elim (hit_sub Finset.subset_union_left) (hit_sub Finset.subset_union_right)

private lemma hit_fixed {C : Circuit} {bit : Bool} {w : ℕ} {inp : List Bool}
    (hlen : inp.length = 26) (h : (26 : Fin 27) ∈ atoms C bit w) :
    hit (inp ++ [bit]) (atoms C bit w) := by
  refine ⟨26, h, ?_⟩
  change (inp ++ [bit]).getD 26 false = true
  rw [getD_append_bit_last _ _ hlen]
  exact (Finset.mem_filter.mp h).2.resolve_left (by decide)

private lemma main_one_reach {C : Circuit} {bit : Bool} {lo a b x y : ℕ}
    (hm : Monotone2 C) (hr : ReadsBack 27 C) (hlo : (gateAt C lo).op = GateOp.and)
    (hx : OrReaches 27 C x lo)
    (hs : ∀ Q, isQuad Q → let inp := pgQuadInput Q ++ [bit];
      ¬ ((hit inp (atoms C bit x) ∨ (hit inp (atoms C bit a) ∧ hit inp (atoms C bit b))) ∧
        hit inp (atoms C bit y))) :
    Plan C bit 2 (fun e => (pairHit e (atoms C bit x) ∨
      (pairHit e (atoms C bit a) ∧ pairHit e (atoms C bit b))) ∧ pairHit e (atoms C bit y)) := by
  let A := atoms C bit a
  let B := atoms C bit b
  let X := atoms C bit x
  let Y := atoms C bit y
  let f : Fin 27 := 26
  by_cases hYf : f ∈ Y
  · have hYQ (Q : Finset (Fin 13)) : hit (pgQuadInput Q ++ [bit]) Y :=
      hit_fixed (pgQuadInput_length Q) hYf
    have hX : X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨Q, hQ, hqu⟩ := atoms_quad hu
      exact hs Q hQ ⟨Or.inl ⟨u, hu, hqu⟩, hYQ Q⟩
    have hab : Rect A B := quad_rect active_atoms active_atoms
      (fun Q hQ ha hb => hs Q hQ ⟨Or.inr ⟨ha, hb⟩, hYQ Q⟩)
    apply plan_imp (plan_box hr (by decide : 1 ≤ 2) hab)
    rintro e ⟨he | he, _⟩
    · exact (pairHit_empty e (hX ▸ he)).elim
    · exact he
  · by_cases hAf : f ∈ A
    · have h : Rect (X ∪ B) Y := by
        apply quad_rect (fun i hi => (Finset.mem_union.mp hi).elim (active_atoms i) (active_atoms i))
          active_atoms
        intro Q hQ hxb hy'
        exact hs Q hQ ⟨(hit_union.mp hxb).imp id (fun hb =>
          ⟨hit_fixed (pgQuadInput_length Q) hAf, hb⟩), hy'⟩
      exact plan_imp (plan_union_product h) (fun e he =>
        ⟨pairHit_union.mpr (he.1.imp id And.right), he.2⟩)
    · by_cases hBf : f ∈ B
      · have h : Rect (X ∪ A) Y := by
          apply quad_rect (fun i hi => (Finset.mem_union.mp hi).elim (active_atoms i) (active_atoms i))
            active_atoms
          intro Q hQ hxa hy'
          exact hs Q hQ ⟨(hit_union.mp hxa).imp id (fun ha =>
            ⟨ha, hit_fixed (pgQuadInput_length Q) hBf⟩), hy'⟩
        exact plan_imp (plan_union_product h) (fun e he =>
          ⟨pairHit_union.mpr (he.1.imp id And.left), he.2⟩)
      · have hD : Rect (X ∪ (A ∩ B)) Y := by
          apply quad_rect
            (fun i hi => (Finset.mem_union.mp hi).elim (active_atoms i)
              (fun hi => active_atoms i (Finset.mem_inter.mp hi).1))
            active_atoms
          intro Q hQ hxy hy'
          exact hs Q hQ ⟨(hit_union.mp hxy).imp id (fun h =>
            ⟨hit_sub Finset.inter_subset_left h, hit_sub Finset.inter_subset_right h⟩), hy'⟩
        have hE : Rect (A ∩ Y) B := by
          apply quad_rect (fun i hi => active_atoms i (Finset.mem_inter.mp hi).1) active_atoms
          intro Q hQ hay hb
          exact hs Q hQ ⟨Or.inr ⟨hit_sub Finset.inter_subset_left hay, hb⟩, hit_sub Finset.inter_subset_right hay⟩
        have hF : Rect (B ∩ Y) A := by
          apply quad_rect (fun i hi => active_atoms i (Finset.mem_inter.mp hi).1) active_atoms
          intro Q hQ hby ha
          exact hs Q hQ ⟨Or.inr ⟨ha, hit_sub Finset.inter_subset_left hby⟩, hit_sub Finset.inter_subset_right hby⟩
        have hpart (e : Ed) (he : (pairHit e X ∨ (pairHit e A ∧ pairHit e B)) ∧ pairHit e Y) :
            Box (X ∪ (A ∩ B)) Y e ∨ Box (A ∩ Y) B e ∨ Box (B ∩ Y) A e := by
          rcases he with ⟨hx' | ⟨ha, hb⟩, hy'⟩
          · exact Or.inl ⟨pairHit_union.mpr (Or.inl hx'), hy'⟩
          · rcases pair_split_three hAf hBf hYf ha hb hy' with h | h | h
            · exact Or.inl ⟨pairHit_union.mpr (Or.inr h.1), h.2⟩
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        apply plan_imp ?_ hpart
        by_cases hYn : Y.Nonempty
        · by_cases hy : Y.card ≤ 1
          · obtain ⟨c, hc⟩ := hYn
            exact singleton_Y_plan (singleton_of_small hc hy) hD hE hF
          · have hy' : 1 < (atoms C bit y).card := Nat.lt_of_not_ge hy
            by_cases hE' : (A ∩ Y).Nonempty
            · by_cases hF' : (B ∩ Y).Nonempty
              · exact plan_two_intersections hm hr hD hE hF hE'.choose_spec hF'.choose_spec
              · refine plan_imp (plan_one_intersection hm hr hlo hx hD hE hy') ?_
                rintro e (h | h | h)
                · exact Or.inl h
                · exact Or.inr h
                · exact (pairHit_empty e (Finset.not_nonempty_iff_eq_empty.mp hF' ▸ h.1)).elim
            · have hD' : Rect (X ∪ (B ∩ A)) Y := by simpa [Finset.inter_comm] using hD
              refine plan_imp (plan_one_intersection hm hr hlo hx hD' hF hy') ?_
              rintro e (h | h | h)
              · simpa [Finset.inter_comm] using (Or.inl h : Box (X ∪ (A ∩ B)) Y e ∨ Box (B ∩ Y) A e)
              · exact (pairHit_empty e (Finset.not_nonempty_iff_eq_empty.mp hE' ▸ h.1)).elim
              · exact Or.inr h
        · apply plan_none
          have he := Finset.not_nonempty_iff_eq_empty.mp hYn
          rintro e (h | h | h)
          · exact pairHit_empty e (he ▸ h.2)
          · exact pairHit_empty e (by simpa [he] using h.1)
          · exact pairHit_empty e (by simpa [he] using h.1)

private lemma unique_and_cone {C : Circuit} (h : andPairs 27 C = 1) :
    ∃ lo hi : ℕ, (gateAt C lo).op = GateOp.and ∧ (gateAt C hi).op = GateOp.and ∧
      InCone 27 C lo hi ∧
      ∀ i j, (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
        InCone 27 C i j → i = lo ∧ j = hi := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold andPairs at h
  obtain ⟨⟨lo, hi⟩, he⟩ := Finset.card_eq_one.mp h
  have hm : (lo, hi) ∈ ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      fun (p : ℕ × ℕ) => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 27 C p.1 p.2) := by
    rw [he]
    exact Finset.mem_singleton_self _
  have hf := (Finset.mem_filter.mp hm).2
  refine ⟨lo, hi, hf.1, hf.2.1, hf.2.2, ?_⟩
  intro i j hi' hj' hcone
  have hm' : (i, j) ∈ ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      fun (p : ℕ × ℕ) => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 27 C p.1 p.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (lt_gates_of_and hi'), Finset.mem_range.mpr (lt_gates_of_and hj')⟩, hi', hj', hcone⟩
  rw [he, Finset.mem_singleton, Prod.mk.injEq] at hm'
  exact hm'

private lemma eval_Pure {C : Circuit} {bit : Bool} {lo hi g w : ℕ}
    (hm : Monotone2 C) (hr : ReadsBack 27 C)
    (hu : ∀ i j, (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
      InCone 27 C i j → i = lo ∧ j = hi)
    (hg : (gateAt C g).op = GateOp.and) (hw : w ∈ (gateAt C g).inputs) (hne : g ≠ hi)
    {inp : List Bool} (hl : inp.length = 26) :
    evalWire C (inp ++ [bit]) w ↔ hit (inp ++ [bit]) (atoms C bit w) := by
  rw [wire_hit_or_and hm hr hl]
  exact or_iff_left_of_imp (fun ⟨j, hj, hjr, _⟩ =>
    (hne (hu j g hj hg (inCone_of_input_orReaches hr (lt_gates_of_and hg) hw hjr)).2).elim)

private lemma eval_Mixed {C : Circuit} {bit : Bool} {lo hi w : ℕ}
    (hm : Monotone2 C) (hr : ReadsBack 27 C)
    (hu : ∀ i j, (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
      InCone 27 C i j → i = lo ∧ j = hi)
    (hlo : (gateAt C lo).op = GateOp.and)
    (hhi : (gateAt C hi).op = GateOp.and) (hw : w ∈ (gateAt C hi).inputs)
    {inp : List Bool} (hl : inp.length = 26) :
    evalWire C (inp ++ [bit]) w ↔ hit (inp ++ [bit]) (atoms C bit w) ∨
      (OrReaches 27 C w lo ∧ evalWire C (inp ++ [bit]) (27 + lo)) := by
  rw [wire_hit_or_and hm hr hl]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨j, hj, hjr, h⟩
    have he := (hu j hi hj hhi (inCone_of_input_orReaches hr (lt_gates_of_and hhi) hw hjr)).1
    subst j
    exact ⟨hjr, h⟩
  · exact fun ⟨h, he⟩ => ⟨lo, hlo, h, he⟩
private lemma ordinary_root {C : Circuit} {bit : Bool} {lo hi g : ℕ}
    (hm : Monotone2 C) (hr : ReadsBack 27 C)
    (hu : ∀ i j, (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
      InCone 27 C i j → i = lo ∧ j = hi)
    (hg : (gateAt C g).op = GateOp.and) (hne : g ≠ hi)
    (hs : ∀ Q, isQuad Q → ¬ evalWire C (pgQuadInput Q ++ [bit]) (27 + g)) :
    ∃ r : Root, atoms C bit r.2 ⊆ nbr r.1 ∧ ∀ e : Ed,
      evalWire C (pgPairInput e.1 e.2 ++ [bit]) (27 + g) → e ∈ star r.1 (leaves C bit r.1 r.2) := by
  rcases inputs_two hm hg with hz | ⟨a, b, ha, hb, hab⟩
  · exfalso
    apply hs (baseQuad 0) (baseQuad_isQuad 0)
    apply (and_eval_all hr hg (append_bit_length _ _ (pgQuadInput_length _))).mpr
    simp [hz]
  · have hcalc (s : List Bool) (hs : s.length = 26) :
        evalWire C (s ++ [bit]) (27 + g) ↔
          hit (s ++ [bit]) (atoms C bit a) ∧ hit (s ++ [bit]) (atoms C bit b) := by
        rw [and_eval_all hr hg (append_bit_length _ _ hs), hab,
          eval_Pure hm hr hu hg ha hne hs, eval_Pure hm hr hu hg hb hne hs]
    have hrect : Rect (atoms C bit a) (atoms C bit b) :=
      quad_rect active_atoms active_atoms (fun Q hQ h₁ h₂ =>
        hs Q hQ ((hcalc _ (pgQuadInput_length Q)).mpr ⟨h₁, h₂⟩))
    obtain ⟨r, hp, hc⟩ := rect_cover hr hrect
    refine ⟨r, hp, fun e he => ?_⟩
    have h := (hcalc _ (pgPairInput_length e.1 e.2)).mp he
    exact hc e (hit_pair.mp h.1) (hit_pair.mp h.2)

private lemma exception_plan {C : Circuit} {bit : Bool} {lo hi : ℕ}
    (hm : Monotone2 C) (hr : ReadsBack 27 C)
    (hu : ∀ i j, (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
      InCone 27 C i j → i = lo ∧ j = hi)
    (hlo : (gateAt C lo).op = GateOp.and) (hhi : (gateAt C hi).op = GateOp.and)
    (hne : lo ≠ hi)
    (hs : ∀ Q, isQuad Q → ¬ evalWire C (pgQuadInput Q ++ [bit]) (27 + hi)) :
    let exposed := OrReaches 27 C C.output lo
    Plan C bit (if exposed then 1 else 2) (fun e =>
      let inp := pgPairInput e.1 e.2 ++ [bit]
      evalWire C inp (27 + hi) ∧ (exposed → ¬ evalWire C inp (27 + lo))) := by
  classical
  dsimp only
  rcases inputs_two hm hhi with hz | ⟨x, y, hx, hy, hxy⟩
  · exfalso
    apply hs (baseQuad 0) (baseQuad_isQuad 0)
    apply (and_eval_all hr hhi (append_bit_length _ _ (pgQuadInput_length _))).mpr
    simp [hz]
  · have hcalc (s : List Bool) (hlen : s.length = 26) :
        let inp := s ++ [bit]
        evalWire C inp (27 + hi) ↔
          (hit inp (atoms C bit x) ∨ (OrReaches 27 C x lo ∧ evalWire C inp (27 + lo))) ∧
          (hit inp (atoms C bit y) ∨ (OrReaches 27 C y lo ∧ evalWire C inp (27 + lo))) := by
        dsimp only
        rw [and_eval_all hr hhi (append_bit_length _ _ hlen), hxy, eval_Mixed hm hr hu hlo hhi hx hlen,
          eval_Mixed hm hr hu hlo hhi hy hlen]
    have hrect : Rect (atoms C bit x) (atoms C bit y) :=
      quad_rect active_atoms active_atoms (fun Q hQ h₁ h₂ =>
        hs Q hQ ((hcalc _ (pgQuadInput_length Q)).mpr ⟨Or.inl h₁, Or.inl h₂⟩))
    by_cases he : OrReaches 27 C C.output lo
    · rw [ite_eq_left he]
      refine plan_imp (plan_box hr (by decide : 1 ≤ 1) hrect) ?_
      intro e h
      have hs' := (hcalc _ (pgPairInput_length e.1 e.2)).mp h.1
      exact ⟨hit_pair.mp (hs'.1.resolve_right (fun h' => h.2 he h'.2)),
        hit_pair.mp (hs'.2.resolve_right (fun h' => h.2 he h'.2))⟩
    · rw [ite_eq_right he]
      have hStep (u v : ℕ) (hu' : OrReaches 27 C u lo) (_hv' : ¬ OrReaches 27 C v lo)
          (hUV : ∀ s : List Bool, s.length = 26 →
            let inp := s ++ [bit];
            evalWire C inp (27 + hi) ↔ (hit inp (atoms C bit u) ∨ evalWire C inp (27 + lo)) ∧
              hit inp (atoms C bit v)) :
          Plan C bit 2 (fun e => let inp := pgPairInput e.1 e.2 ++ [bit];
            evalWire C inp (27 + hi) ∧ (OrReaches 27 C C.output lo → ¬ evalWire C inp (27 + lo))) := by
        rcases inputs_two hm hlo with hz | ⟨a, b, ha, hb, hab⟩
        · have hconst (s : List Bool) (hlen : s.length = 26) : evalWire C (s ++ [bit]) (27 + lo) := by
            apply (and_eval_all hr hlo (append_bit_length _ _ hlen)).mpr
            simp [hz]
          apply plan_none
          intro e h
          obtain ⟨i, him, _⟩ := ((hUV _ (pgPairInput_length e.1 e.2)).mp h.1).2
          obtain ⟨Q, hQ, hqi⟩ := atoms_quad him
          exact hs Q hQ ((hUV _ (pgQuadInput_length Q)).mpr ⟨Or.inr (hconst _ (pgQuadInput_length Q)),
            i, him, hqi⟩)
        · have hlow (s : List Bool) (hlen : s.length = 26) :
              evalWire C (s ++ [bit]) (27 + lo) ↔
                hit (s ++ [bit]) (atoms C bit a) ∧ hit (s ++ [bit]) (atoms C bit b) := by
              rw [and_eval_all hr hlo (append_bit_length _ _ hlen), hab, eval_Pure hm hr hu hlo ha hne hlen,
                eval_Pure hm hr hu hlo hb hne hlen]
          refine plan_imp (main_one_reach (a := a) (b := b) (y := v) hm hr hlo hu' ?_) ?_
          · intro Q hQ
            dsimp only
            intro hq
            exact hs Q hQ ((hUV _ (pgQuadInput_length Q)).mpr
              ⟨hq.1.imp id (hlow _ (pgQuadInput_length Q)).mpr, hq.2⟩)
          · intro e h
            have hp := (hUV _ (pgPairInput_length e.1 e.2)).mp h.1
            exact ⟨hp.1.imp hit_pair.mp (fun ht =>
              let h' := (hlow _ (pgPairInput_length e.1 e.2)).mp ht
              ⟨hit_pair.mp h'.1, hit_pair.mp h'.2⟩), hit_pair.mp hp.2⟩
      by_cases hx' : OrReaches 27 C x lo
      · by_cases hy' : OrReaches 27 C y lo
        · rcases inputs_two hm hlo with hz | ⟨a, b, ha, hb, hab⟩
          · exfalso
            let Q := baseQuad 0
            have hf : evalWire C (pgQuadInput Q ++ [bit]) (27 + lo) := by
              apply (and_eval_all hr hlo (append_bit_length _ _ (pgQuadInput_length Q))).mpr
              simp [hz]
            exact hs Q (baseQuad_isQuad 0) ((hcalc _ (pgQuadInput_length Q)).mpr
              ⟨Or.inr ⟨hx', hf⟩, Or.inr ⟨hy', hf⟩⟩)
          · have hlow (s : List Bool) (hlen : s.length = 26) :
                evalWire C (s ++ [bit]) (27 + lo) ↔
                  hit (s ++ [bit]) (atoms C bit a) ∧ hit (s ++ [bit]) (atoms C bit b) := by
                rw [and_eval_all hr hlo (append_bit_length _ _ hlen), hab, eval_Pure hm hr hu hlo ha hne hlen,
                  eval_Pure hm hr hu hlo hb hne hlen]
            have habr : Rect (atoms C bit a) (atoms C bit b) := by
              apply quad_rect active_atoms active_atoms
              intro Q hQ ha' hb'
              have ht := (hlow _ (pgQuadInput_length Q)).mpr ⟨ha', hb'⟩
              exact hs Q hQ ((hcalc _ (pgQuadInput_length Q)).mpr ⟨Or.inr ⟨hx', ht⟩, Or.inr ⟨hy', ht⟩⟩)
            refine plan_imp (plan_both_products hlo hr hx' hy' habr hrect) ?_
            intro e ht
            have h := (hcalc _ (pgPairInput_length e.1 e.2)).mp ht.1
            by_cases hl : evalWire C (pgPairInput e.1 e.2 ++ [bit]) (27 + lo)
            · have hs' := (hlow _ (pgPairInput_length e.1 e.2)).mp hl
              exact Or.inl ⟨hit_pair.mp hs'.1, hit_pair.mp hs'.2⟩
            · exact Or.inr ⟨hit_pair.mp (h.1.resolve_right (fun h' => hl h'.2)),
                hit_pair.mp (h.2.resolve_right (fun h' => hl h'.2))⟩
        · apply hStep x y hx' hy'
          intro s hlen
          simpa only [hx', hy', true_and, false_and, or_false] using hcalc s hlen
      · by_cases hy' : OrReaches 27 C y lo
        · apply hStep y x hy' hx'
          intro s hlen
          simpa only [hx', hy', true_and, false_and, or_false, and_comm] using hcalc s hlen
        · refine plan_imp (plan_box hr (by decide : 1 ≤ 2) hrect) ?_
          intro e h
          have hs' := (hcalc _ (pgPairInput_length e.1 e.2)).mp h.1
          exact ⟨hit_pair.mp (hs'.1.resolve_right (fun h' => hx' h'.1)),
            hit_pair.mp (hs'.2.resolve_right (fun h' => hy' h'.1))⟩
private lemma leaves_or {C : Circuit} {bit : Bool} {c : Fin 27} (hr : ReadsBack 27 C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (u : Fin 27) :
    u ∈ leaves C bit c (27 + j) ↔ ∃ w ∈ (gateAt C j).inputs, u ∈ leaves C bit c w := by
  simp only [leaves, Finset.mem_inter, atoms_or hr hj hop]
  constructor
  · rintro ⟨⟨w, hw, hu⟩, hn⟩
    exact ⟨w, hw, hu, hn⟩
  · rintro ⟨w, hw, hu, hn⟩
    exact ⟨⟨w, hw, hu⟩, hn⟩

private lemma leaves_reach {C : Circuit} {bit : Bool} {c : Fin 27} (hr : ReadsBack 27 C)
    {w j : ℕ} (h : OrReaches 27 C w j) : leaves C bit c (27 + j) ⊆ leaves C bit c w :=
by
  intro i hi
  obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hi
  exact Finset.mem_inter.mpr ⟨atoms_reach hr h ha, hb⟩

private lemma leaves_ge {C : Circuit} {bit : Bool} {c : Fin 27} (hr : ReadsBack 27 C)
    {w : ℕ} (h : 27 + C.gates.length ≤ w) : leaves C bit c w = ∅ := by
  simp [leaves, atoms, orIn_ge hr h]

private lemma leaves_and {C : Circuit} {bit : Bool} {c : Fin 27} (hr : ReadsBack 27 C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    leaves C bit c (27 + j) = ∅ := by
  simp [leaves, atoms, orIn_and hr hj hop]

private lemma leaves_card_le_one {C : Circuit} {bit : Bool} {c : Fin 27} {w : ℕ} (hw : w < 27) :
    (leaves C bit c w).card ≤ 1 := by
  have h : orIn 27 C w = {⟨w, hw⟩} := orIn_input ⟨w, hw⟩
  have hs : leaves C bit c w ⊆ orIn 27 C w :=
    fun _ h => (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).1
  exact (Finset.card_le_card hs).trans (by simp [h])
open Classical in
private noncomputable def bigOrReach (C : Circuit) (bit : Bool) (c : Fin 27) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun g =>
    (gateAt C g).op = GateOp.or ∧ 2 ≤ (leaves C bit c (27 + g)).card ∧ ∃ w ∈ W, OrReaches 27 C w g

private lemma leaf_count_bound {C : Circuit} {bit : Bool} {c : Fin 27} (hMono : Monotone2 C) (hRB : ReadsBack 27 C) :
    ∀ k : ℕ, ∀ W : Finset ℕ, (bigOrReach C bit c W).card = k →
      (W.biUnion (leaves C bit c)).card ≤ W.card + k := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W hk
    by_cases hne : (bigOrReach C bit c W).Nonempty
    · set M := bigOrReach C bit c W
      set m := M.max' hne
      have hmM : m ∈ M := Finset.max'_mem M hne
      have hm_props : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
          2 ≤ (leaves C bit c (27 + m)).card ∧ ∃ w ∈ W, OrReaches 27 C w m := by
        simpa [M, bigOrReach, Finset.mem_filter, Finset.mem_range] using hmM
      have hmax_unique : ∀ w ∈ W, OrReaches 27 C w m → w = 27 + m := by
        intro w hw hwm
        have hle := orReaches_le hRB w m hwm
        rw [orReaches_iff hRB] at hwm
        rcases hwm with ⟨j, hj, rfl, hcase⟩
        by_contra hne_w
        have hmj : m ≠ j := fun h => hne_w (by omega)
        rcases hcase with hEq | ⟨hjop, u, hu, hug⟩
        · exact hmj hEq
        · have hjM : j ∈ M := by
            simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
            refine ⟨hj, hjop, ?_, 27 + j, hw, orReaches_self hRB hj⟩
            have hsub : leaves C bit c (27 + m) ⊆ leaves C bit c (27 + j) :=
              leaves_reach hRB
                ((orReaches_iff hRB (27 + j) m).mpr ⟨j, hj, rfl, Or.inr ⟨hjop, u, hu, hug⟩⟩)
            exact le_trans hm_props.2.2.1 (Finset.card_le_card hsub)
          have hjle : j ≤ m := Finset.le_max' M j hjM
          omega
      have hnmW : 27 + m ∈ W := by
        rcases hm_props.2.2.2 with ⟨w, hw, hwm⟩
        rwa [hmax_unique w hw hwm] at hw
      set W' : Finset ℕ := (gateAt C m).inputs.toFinset ∪ (W.erase (27 + m))
      have hbi : W.biUnion (leaves C bit c) ⊆ W'.biUnion (leaves C bit c) := by
        intro u hu
        rw [Finset.mem_biUnion] at hu ⊢
        rcases hu with ⟨w, hw, huw⟩
        by_cases hwm : w = 27 + m
        · subst hwm
          rcases (leaves_or hRB hm_props.1 hm_props.2.1 u).mp huw with ⟨v, hv, huv⟩
          exact ⟨v, Finset.mem_union_left _ (List.mem_toFinset.mpr hv), huv⟩
        · exact ⟨w, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hwm, hw⟩), huw⟩
      have hW'card : W'.card ≤ W.card + 1 := by
        have h1 : W'.card ≤ (gateAt C m).inputs.toFinset.card + (W.erase (27 + m)).card :=
          Finset.card_union_le _ _
        have h2 : (gateAt C m).inputs.toFinset.card ≤ (gateAt C m).inputs.length :=
          List.toFinset_card_le _
        have h3 : (gateAt C m).inputs.length ≤ 2 := gate_inputs_len_le hMono hm_props.1
        have h4 : (W.erase (27 + m)).card + 1 = W.card := Finset.card_erase_add_one hnmW
        omega
      have hM'sub : bigOrReach C bit c W' ⊆ M.erase m := by
        intro g hg
        simp only [bigOrReach, Finset.mem_filter, Finset.mem_range] at hg
        rcases hg with ⟨hglt, hgop, hgcard, w', hw', hw'g⟩
        rw [Finset.mem_erase]
        have hgM : g ∈ M := by
          simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
          refine ⟨hglt, hgop, hgcard, ?_⟩
          rw [Finset.mem_union] at hw'
          rcases hw' with hmem | herase
          · rw [List.mem_toFinset] at hmem
            exact ⟨27 + m, hnmW,
              (orReaches_iff hRB (27 + m) g).mpr ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, w', hmem, hw'g⟩⟩⟩
          · exact ⟨w', (Finset.mem_erase.mp herase).2, hw'g⟩
        refine ⟨?_, hgM⟩
        intro hgm
        subst hgm
        rw [Finset.mem_union] at hw'
        rcases hw' with hmem | herase
        · rw [List.mem_toFinset] at hmem
          have hle := (orReaches_le hRB _ _ hw'g).1
          have hlt := hRB m hm_props.1 w' hmem
          omega
        · rcases Finset.mem_erase.mp herase with ⟨hne', hw'W⟩
          exact hne' (hmax_unique w' hw'W hw'g)
      have hM'card_le : (bigOrReach C bit c W').card ≤ (M.erase m).card :=
        Finset.card_le_card hM'sub
      have hMerase : (M.erase m).card + 1 = k := by
        rw [Finset.card_erase_add_one hmM, hk]
      have hM'lt : (bigOrReach C bit c W').card < k := by omega
      have hrec := ih _ hM'lt W' rfl
      have hbi_card : (W.biUnion (leaves C bit c)).card ≤ (W'.biUnion (leaves C bit c)).card :=
        Finset.card_le_card hbi
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hle1 : ∀ w ∈ W, (leaves C bit c w).card ≤ 1 := by
        intro w hw
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ (leaves C bit c w).card := hgt
        by_cases hlt : w < 27
        · have hle := leaves_card_le_one (C := C) (bit := bit) (c := c) (w := w) hlt
          omega
        · by_cases hge : 27 + C.gates.length ≤ w
          · rw [leaves_ge hRB hge, Finset.card_empty] at hge2
            omega
          · set j := w - 27
            have hwEq : w = 27 + j := by omega
            have hj : j < C.gates.length := by omega
            rw [hwEq] at hge2 hw
            rcases gateOp_and_or hMono hj with hop | hop
            · rw [leaves_and hRB hj hop, Finset.card_empty] at hge2
              omega
            · have hjM : j ∈ bigOrReach C bit c W := by
                simp only [bigOrReach, Finset.mem_filter, Finset.mem_range]
                exact ⟨hj, hop, hge2, 27 + j, hw, orReaches_self hRB hj⟩
              rw [hne] at hjM
              simp at hjM
      have hbi : (W.biUnion (leaves C bit c)).card ≤ ∑ w ∈ W, (leaves C bit c w).card :=
        Finset.card_biUnion_le
      have hsum : ∑ w ∈ W, (leaves C bit c w).card ≤ ∑ _w ∈ W, 1 :=
        Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      omega
open Classical in
private noncomputable def topOr (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ OrReaches 27 C C.output j

private lemma top_empty {C : Circuit} {bit : Bool} (hr : ReadsBack 27 C)
    (hs : ∀ Q, isQuad Q → ¬ evalWire C (pgQuadInput Q ++ [bit]) C.output)
    {j : ℕ} (hj : j ∈ topOr C) : atoms C bit (27 + j) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hreach := (Finset.mem_filter.mp hj).2.2
  obtain ⟨Q, hQ, hqi⟩ := atoms_quad hi
  have hi' := (Finset.mem_filter.mp (atoms_reach hr hreach hi)).1
  exact hs Q hQ (wires_true_of_mem_orIn hr _ (append_bit_length _ _ (pgQuadInput_length Q)) hi' hqi)

private lemma top_count {C : Circuit} (hm : Monotone2 C) (hr : ReadsBack 27 C)
    (T : Finset ℕ) (hT : ∀ j ∈ T, (gateAt C j).op = GateOp.and ∧ OrReaches 27 C C.output j) :
    T.card ≤ (topOr C).card + 1 := by
  classical
  have hd : Disjoint T (topOr C) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    have ht := (Finset.mem_filter.mp hj').2.1
    rw [(hT j hj).1] at ht
    cases ht
  let U : Finset ℕ := (T ∪ topOr C).image (fun j => 27 + j)
  let V : Finset ℕ := U.erase C.output
  have hu : U.card = T.card + (topOr C).card := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_union_of_disjoint hd]
  have hv : U.card ≤ V.card + 1 := by
    by_cases hmem : C.output ∈ U
    · exact (Finset.card_erase_add_one hmem).ge
    · simp [V, Finset.erase_eq_of_notMem hmem]
  have hsub : V ⊆ (topOr C).biUnion (fun j => (gateAt C j).inputs.toFinset) := by
    intro w hw
    obtain ⟨hneq, hw⟩ := Finset.mem_erase.mp hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    have hreach : OrReaches 27 C C.output j :=
      (Finset.mem_union.mp hj).elim (fun h => (hT j h).2) (fun h => (Finset.mem_filter.mp h).2.2)
    rcases orReaches_parent hr C.output j hreach with h | ⟨k, hk, hko, hkr, hkm⟩
    · exact (hneq h.symm).elim
    · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hko, hkr⟩,
        List.mem_toFinset.mpr hkm⟩
  have hv' : V.card ≤ 2 * (topOr C).card := by
    calc
      _ ≤ ((topOr C).biUnion (fun j => (gateAt C j).inputs.toFinset)).card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ topOr C, (gateAt C j).inputs.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ topOr C, 2 := Finset.sum_le_sum (fun j hj =>
        (List.toFinset_card_le _).trans (gate_inputs_len_le hm (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)))
      _ = _ := by simp [Nat.mul_comm]
  omega

open Classical in
private noncomputable def rootOr (C : Circuit) (bit : Bool) (R : Finset Root) : Finset ℕ :=
  (Finset.univ : Finset (Fin 27)).biUnion fun c =>
    bigOrReach C bit c ((R.filter fun r => r.1 = c).image Prod.snd)

private lemma cover_cost {C : Circuit} {bit : Bool} (hm : Monotone2 C) (hr : ReadsBack 27 C)
    (R : Finset Root) (hcoh : Coherent C bit R) :
    (covered C bit R).card ≤ R.card + (rootOr C bit R).card := by
  classical
  let K := fun c : Fin 27 => R.filter (fun r => r.1 = c)
  let W := fun c => (K c).image Prod.snd
  let L := fun c => (W c).biUnion (leaves C bit c)
  let M := fun c => bigOrReach C bit c (W c)
  have he : covered C bit R ⊆ (Finset.univ : Finset (Fin 27)).biUnion (fun c => star c (L c)) := by
    intro e he
    obtain ⟨⟨c, w⟩, hr, he⟩ := Finset.mem_biUnion.mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ _, star_mono ?_ he⟩
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_image.mpr
      ⟨(c, w), Finset.mem_filter.mpr ⟨hr, rfl⟩, rfl⟩, hu⟩
  have hK : ∑ c : Fin 27, (K c).card ≤ R.card := by
    rw [← Finset.card_biUnion]
    · apply Finset.card_le_card
      rintro r hr
      obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hr
      exact (Finset.mem_filter.mp hc).1
    · intro c _ d _ hne
      change Disjoint (K c) (K d)
      rw [Finset.disjoint_left]
      intro r hc hd
      exact hne ((Finset.mem_filter.mp hc).2.symm.trans (Finset.mem_filter.mp hd).2)
  have hM : ∑ c : Fin 27, (M c).card = (rootOr C bit R).card := by
    unfold rootOr
    apply Eq.symm
    apply Finset.card_biUnion
    intro c _ d _ hne
    change Disjoint (M c) (M d)
    rw [Finset.disjoint_left]
    intro j hc hd
    simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range] at hc hd
    obtain ⟨c0, hc0⟩ := hcoh
    have hbad {u v : Fin 27} (hn : u ≠ v) (hv : v ≠ c0)
        (huC : 2 ≤ (leaves C bit u (27 + j)).card)
        (hvC : ∃ w ∈ W v, OrReaches 27 C w j) : False := by
      obtain ⟨w, hw, hwj⟩ := hvC
      obtain ⟨r, hkr, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hrr, hr'⟩ := Finset.mem_filter.mp hkr
      have hsup : atoms C bit r.2 ⊆ nbr v := by
        rw [← hr']
        exact hc0 r hrr (fun h => hv (hr'.symm.trans h))
      have hsub : leaves C bit u (27 + j) ⊆ nbr u ∩ nbr v := by
        intro x hx
        obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hx
        exact Finset.mem_inter.mpr ⟨hb, hsup (atoms_reach hr hwj ha)⟩
      have hcard := (Finset.card_le_card hsub).trans (common_le _ _ hn)
      omega
    by_cases h : d = c0
    · exact hbad hne.symm (fun h' => hne (h'.trans h.symm)) hd.2.2.1 hc.2.2.2
    · exact hbad hne h hc.2.2.1 hd.2.2.2
  have hL : ∑ c : Fin 27, (L c).card ≤
      (∑ c : Fin 27, (K c).card) + ∑ c : Fin 27, (M c).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun c _ =>
      (leaf_count_bound hm hr (M c).card (W c) rfl).trans
        (Nat.add_le_add_right Finset.card_image_le _))
  have hc' : (covered C bit R).card ≤ ∑ c : Fin 27, (L c).card :=
    (Finset.card_le_card he).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_image_le)))
  omega

private lemma extra_not_rootOr {C : Circuit} {bit : Bool} {R : Finset Root} {j : ℕ}
    (hr : ReadsBack 27 C) (hp : PureRoots C bit R) (he : spare C bit j) :
    j ∉ rootOr C bit R := by
  intro hj
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hj
  simp only [bigOrReach, Finset.mem_filter, Finset.mem_range] at hc
  rcases he.2.2.2 with h | ⟨i, hi, k, hk, hik⟩
  · have hl : (leaves C bit c (27 + j)).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans h
    omega
  · obtain ⟨w, hw, hwj⟩ := hc.2.2.2
    obtain ⟨r, hr', rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hm, heq⟩ := Finset.mem_filter.mp hr'
    have hsub := (atoms_reach hr hwj).trans (hp r hm)
    exact no_triangle (mem_nbr.mp (hsub hi)) (mem_nbr.mp (hsub hk)) hik
open Classical in
private noncomputable def allAnd (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j => (gateAt C j).op = GateOp.and

private lemma count_gates {C : Circuit} {bit : Bool} (hr : ReadsBack 27 C)
    (hs : ∀ Q, isQuad Q → ¬ evalWire C (pgQuadInput Q ++ [bit]) C.output)
    (R : Finset Root) :
    (allAnd C).card + (topOr C).card + (rootOr C bit R).card ≤ C.gates.length ∧
    (PureRoots C bit R → (∃ j, spare C bit j) →
      (allAnd C).card + (topOr C).card + (rootOr C bit R).card + 1 ≤ C.gates.length) := by
  classical
  let N := allAnd C
  let T := topOr C
  let B := rootOr C bit R
  have hd₁ : Disjoint N T := by
    rw [Finset.disjoint_left]
    intro j hj ht
    have hand := (Finset.mem_filter.mp hj).2
    have hor := (Finset.mem_filter.mp ht).2.1
    rw [hand] at hor
    cases hor
  have hB (j : ℕ) (hj : j ∈ B) :
      j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ (atoms C bit (27 + j)).Nonempty := by
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hj
    simp only [bigOrReach, Finset.mem_filter, Finset.mem_range] at hc
    refine ⟨hc.1, hc.2.1, ?_⟩
    have hpos : 0 < (leaves C bit c (27 + j)).card := by have := hc.2.2.1; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_inter.mp hi).1⟩
  have hd₂ : Disjoint (N ∪ T) B := by
    rw [Finset.disjoint_left]
    intro j hj hb
    obtain ⟨_, ho, hn⟩ := hB j hb
    rcases Finset.mem_union.mp hj with hj | hj
    · rw [(Finset.mem_filter.mp hj).2] at ho
      cases ho
    · rw [top_empty hr hs hj] at hn
      exact Finset.not_nonempty_empty hn
  have heq : (N ∪ T ∪ B).card = N.card + T.card + B.card := by
    rw [Finset.card_union_of_disjoint hd₂, Finset.card_union_of_disjoint hd₁]
  have hsub : N ∪ T ∪ B ⊆ Finset.range C.gates.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with ht | hb
    · rcases Finset.mem_union.mp ht with hn | ht
      · exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp ht).1
    · exact Finset.mem_range.mpr (hB j hb).1
  constructor
  · rw [← heq, ← Finset.card_range C.gates.length]
    exact Finset.card_le_card hsub
  · rintro hp ⟨j, hj⟩
    have hnot : j ∉ N ∪ T ∪ B := by
      intro hm
      rcases Finset.mem_union.mp hm with ht | hb
      · rcases Finset.mem_union.mp ht with hn | ht
        · have ho := hj.2.1
          rw [(Finset.mem_filter.mp hn).2] at ho
          cases ho
        · have he := top_empty hr hs ht
          exact Finset.not_nonempty_empty (he ▸ hj.2.2.1)
      · exact extra_not_rootOr hr hp hj hb
    have hsub' : insert j (N ∪ T ∪ B) ⊆ Finset.range C.gates.length := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact Finset.mem_range.mpr hj.1
      · exact hsub hk
    rw [← heq, ← Finset.card_insert_of_notMem hnot, ← Finset.card_range C.gates.length]
    exact Finset.card_le_card hsub'

private lemma root_union_cover {C : Circuit} {bit : Bool} {A R : Finset Root} :
    covered C bit (A ∪ R) = covered C bit A ∪ covered C bit R := by
  ext e
  simp only [covered, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨r, hr | hr, he⟩
    · exact Or.inl ⟨r, hr, he⟩
    · exact Or.inr ⟨r, hr, he⟩
  · rintro (⟨r, hr, he⟩ | ⟨r, hr, he⟩)
    · exact ⟨r, Or.inl hr, he⟩
    · exact ⟨r, Or.inr hr, he⟩

private lemma main_bound (p0 l0 : Fin 13) (C : Circuit) (bit : Bool)
    (hm : Monotone2 C) (hr : ReadsBack 27 C) (hPairs : andPairs 27 C = 1)
    (hPos : ∀ p l : Fin 13, p - l ∈ pgD → p ≠ p0 ∨ l ≠ l0 →
      C.eval (pgPairInput p l ++ [bit]) = true)
    (hQuad : ∀ Q : Finset (Fin 13), isQuad Q →
      C.eval (pgQuadInput Q ++ [bit]) = false) :
    63 ≤ C.size := by
  classical
  obtain ⟨lo, hi, hlo, hhi, hcone, hu⟩ := unique_and_cone hPairs
  have hne : lo ≠ hi := (inCone_lt hr hi lo hcone).1.ne
  have houtQ : ∀ Q, isQuad Q → ¬ evalWire C (pgQuadInput Q ++ [bit]) C.output := by
    intro Q hQ hh
    change C.eval _ = true at hh
    rw [hQuad Q hQ] at hh
    cases hh
  have hs (g : ℕ) (hg : OrReaches 27 C C.output g) :
      ∀ Q, isQuad Q → ¬ evalWire C (pgQuadInput Q ++ [bit]) (27 + g) := by
    intro Q hQ he
    exact houtQ Q hQ (wires_true_of_orReaches hr _ (append_bit_length _ _ (pgQuadInput_length Q))
      C.output g hg he)
  let T : Finset ℕ := (allAnd C).filter fun j => OrReaches 27 C C.output j
  let A := T.erase hi
  have ht (j : ℕ) (hj : j ∈ T) : (gateAt C j).op = GateOp.and ∧ OrReaches 27 C C.output j :=
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2, (Finset.mem_filter.mp hj).2⟩
  have ha (j : ℕ) (hj : j ∈ A) : (gateAt C j).op = GateOp.and ∧ OrReaches 27 C C.output j :=
    ht j (Finset.mem_erase.mp hj).2
  have hx (j : ℕ) (hj : j ∈ A) : ∃ r : Root, atoms C bit r.2 ⊆ nbr r.1 ∧
      ∀ e : Ed, evalWire C (pgPairInput e.1 e.2 ++ [bit]) (27 + j) →
        e ∈ star r.1 (leaves C bit r.1 r.2) :=
    ordinary_root hm hr hu (ha j hj).1 (Finset.mem_erase.mp hj).1 (hs j (ha j hj).2)
  let f : ℕ → Root := fun j => if h : j ∈ A then (hx j h).choose else (0, 0)
  let S := A.image f
  have hSc : S.card ≤ A.card := Finset.card_image_le
  have hS : PureRoots C bit S := by
    rintro r hr'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr'
    simpa [f, hj] using (hx j hj).choose_spec.1
  have hScover (j : ℕ) (hj : j ∈ A) (e : Ed)
      (he : evalWire C (pgPairInput e.1 e.2 ++ [bit]) (27 + j)) : e ∈ covered C bit S := by
    refine Finset.mem_biUnion.mpr ⟨f j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
    simpa [f, hj] using (hx j hj).choose_spec.2 e he
  have hloN : lo ∈ allAnd C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_gates_of_and hlo), hlo⟩
  have hhiN : hi ∈ allAnd C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_gates_of_and hhi), hhi⟩
  have hAt : A ⊆ allAnd C := fun _ h => (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).1
  let E0 : Finset Ed := Finset.univ.filter fun e => e.1 - e.2 ∈ pgD
  let E : Finset Ed := E0.erase (p0, l0)
  have hEc : 51 ≤ E.card := by
    have hE0 : E0.card = 52 := pg_edges_card
    by_cases hmem : (p0, l0) ∈ E0
    · have heq := Finset.card_erase_add_one hmem
      change E.card + 1 = E0.card at heq
      omega
    · simp [E, Finset.erase_eq_of_notMem hmem, hE0]
  have hE (e : Ed) (he : e ∈ E) :
      ∃ j ∈ T, evalWire C (pgPairInput e.1 e.2 ++ [bit]) (27 + j) := by
    obtain ⟨hne, he0⟩ := Finset.mem_erase.mp he
    have hn : e.1 ≠ p0 ∨ e.2 ≠ l0 := by
      by_contra h
      push Not at h
      exact hne (Prod.ext h.1 h.2)
    have hpos : evalWire C (pgPairInput e.1 e.2 ++ [bit]) C.output :=
      hPos e.1 e.2 (Finset.mem_filter.mp he0).2 hn
    rcases (wire_hit_or_and hm hr (pgPairInput_length e.1 e.2) C.output).mp hpos with
      ⟨i, hi', _⟩ | ⟨j, hj, hjr, hv⟩
    · obtain ⟨Q, hQ, hqi⟩ := atoms_quad hi'
      exact (houtQ Q hQ (wires_true_of_mem_orIn hr _ (append_bit_length _ _ (pgQuadInput_length Q))
        (Finset.mem_filter.mp hi').1 hqi)).elim
    · refine ⟨j, Finset.mem_filter.mpr ⟨?_, hjr⟩, hv⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_gates_of_and hj), hj⟩
  have hTop := top_count hm hr T ht
  change 63 ≤ C.gates.length
  by_cases hOut : OrReaches 27 C C.output hi
  · have hhiT : hi ∈ T := Finset.mem_filter.mpr ⟨hhiN, hOut⟩
    have hTA : A.card + 1 = T.card := Finset.card_erase_add_one hhiT
    obtain ⟨R, hRc, hcoh, hlim, hcov⟩ := exception_plan hm hr hu hlo hhi hne (hs hi hOut)
    let U := S ∪ R
    have hsU : S ⊆ U := Finset.subset_union_left
    have hrU : R ⊆ U := Finset.subset_union_right
    have hE' : E ⊆ covered C bit U := by
      intro e he
      obtain ⟨j, hj, hv⟩ := hE e he
      by_cases h : j = hi
      · subst j
        by_cases hlow : OrReaches 27 C C.output lo ∧
            evalWire C (pgPairInput e.1 e.2 ++ [bit]) (27 + lo)
        · have hloT : lo ∈ T := Finset.mem_filter.mpr ⟨hloN, hlow.1⟩
          exact covered_mono hsU (hScover lo (Finset.mem_erase.mpr ⟨hne, hloT⟩) e hlow.2)
        · exact covered_mono hrU (hcov e ⟨hv, fun hr' hv' => hlow ⟨hr', hv'⟩⟩)
      · exact covered_mono hsU (hScover j (Finset.mem_erase.mpr ⟨h, hj⟩) e hv)
    obtain ⟨c, hc⟩ := hcoh
    have hUC : Coherent C bit U := by
      refine ⟨c, ?_⟩
      intro r hr' hn
      exact (Finset.mem_union.mp hr').elim (fun h => hS r h) (fun h => hc r h hn)
    have hUcard : U.card ≤ (allAnd C).card := by
      have hcard : U.card ≤ S.card + R.card := Finset.card_union_le _ _
      have hAhi : hi ∉ A := Finset.notMem_erase _ _
      by_cases hlo' : OrReaches 27 C C.output lo
      · rw [ite_eq_left hlo'] at hRc
        have ha' : insert hi A ⊆ allAnd C := Finset.insert_subset_iff.mpr ⟨hhiN, hAt⟩
        have hle := Finset.card_le_card ha'
        rw [Finset.card_insert_of_notMem hAhi] at hle
        omega
      · rw [ite_eq_right hlo'] at hRc
        have ha' : insert lo (insert hi A) ⊆ allAnd C :=
          Finset.insert_subset_iff.mpr ⟨hloN, Finset.insert_subset_iff.mpr ⟨hhiN, hAt⟩⟩
        have hn : lo ∉ insert hi A := by
          intro hj
          rcases Finset.mem_insert.mp hj with h | h
          · exact hne h
          · exact hlo' (ha lo h).2
        have hle := Finset.card_le_card ha'
        rw [Finset.card_insert_of_notMem hn, Finset.card_insert_of_notMem hAhi] at hle
        omega
    have hEcost := (Finset.card_le_card hE').trans (cover_cost hm hr U hUC)
    have hG := count_gates hr houtQ U
    have hEdgeCap (k : ℕ) (hk : (covered C bit R).card ≤ k) : 51 ≤ 4 * A.card + k := by
      have hle := Finset.card_le_card hE'
      rw [show U = S ∪ R by rfl, root_union_cover] at hle
      have hUnion := Finset.card_union_le (covered C bit S) (covered C bit R)
      have hS4 := covered_card (C := C) (bit := bit) (R := S)
      omega
    rcases hlim with hSmall | ⟨hP, hExtra⟩
    · have h51 := hEdgeCap 5 hSmall
      have hG' := hG.1
      omega
    · have hr2 : R.card ≤ 2 := by
        by_cases h : OrReaches 27 C C.output lo
        · rw [ite_eq_left h] at hRc
          omega
        · rwa [ite_eq_right h] at hRc
      have hR8 := covered_card (C := C) (bit := bit) (R := R)
      have h51 := hEdgeCap 8 (by omega)
      have hPU : PureRoots C bit U := fun r hr' =>
        (Finset.mem_union.mp hr').elim (hS r) (hP r)
      have hG' := hG.2 hPU hExtra
      omega
  · have heq : A = T := Finset.erase_eq_of_notMem (fun h => hOut (ht hi h).2)
    have hE' : E ⊆ covered C bit S := by
      intro e he
      obtain ⟨j, hj, hv⟩ := hE e he
      exact hScover j (heq ▸ hj) e hv
    have hEdge := Finset.card_le_card hE'
    have hS4 := covered_card (C := C) (bit := bit) (R := S)
    have hCost := hEdge.trans (cover_cost hm hr S (pure_coherent hS))
    have hG := (count_gates hr houtQ S).1
    have hN := Finset.card_le_card hAt
    rw [heq] at hSc hN
    omega
private def pgInput (A B : Finset (Fin 13)) (bit : Bool) : List Bool :=
  ((List.ofFn fun i : Fin 13 => decide (i ∈ A)) ++
    List.ofFn fun i : Fin 13 => decide (i ∈ B)) ++ [bit]

private lemma pgInput_pair (p l : Fin 13) (bit : Bool) :
    pgInput {p} {l} bit = pgPairInput p l ++ [bit] := by
  unfold pgInput pgPairInput
  apply congrArg (· ++ [bit])
  exact congrArg₂ (· ++ ·)
    (congrArg List.ofFn (funext fun _ => decide_eq_decide.mpr Finset.mem_singleton))
    (congrArg List.ofFn (funext fun _ => decide_eq_decide.mpr Finset.mem_singleton))

private lemma pgInput_quad (Q : Finset (Fin 13)) (bit : Bool) :
    pgInput Q {l : Fin 13 | ∀ p ∈ Q, p - l ∉ pgD} bit = pgQuadInput Q ++ [bit] := by
  unfold pgInput pgQuadInput
  apply congrArg (· ++ [bit])
  apply congrArg ((List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ ·)
  exact congrArg List.ofFn (funext fun _ => decide_eq_decide.mpr (by simp))

end PEqualNP.Outside.L_meta_5811

theorem PEqualNP.Outside.L_meta_5811 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →       PEqualNP.TopForm.andPairs (27 : ℕ) x1 = (1 : ℕ) →         have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];         (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) → (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C p0 l0 bit hMono hRB hPairs x8 x9 hPos hQuad _
  apply PEqualNP.Outside.L_meta_5811.main_bound p0 l0 C bit hMono hRB hPairs
  · intro p l hinc hne
    rw [← PEqualNP.Outside.L_meta_5811.pgInput_pair]
    exact hPos p l hinc hne
  · intro Q hQ
    rw [← PEqualNP.Outside.L_meta_5811.pgInput_quad]
    exact hQuad Q hQ.1 hQ.2
namespace Plane17147

open PEqualNP.HeptadCover

lemma sL_card : ∀ l : Fin 13, (singerLines3 l).card = 4 := by decide

lemma sL_inter_eq_one : ∀ l1 l2 : Fin 13, l1 ≠ l2 → (singerLines3 l1 ∩ singerLines3 l2).card = 1 := by
  decide

lemma unique_line_of_ne :
    ∀ a b : Fin 13, a ≠ b → ∃ l : Fin 13, a ∈ singerLines3 l ∧ b ∈ singerLines3 l ∧
      ∀ l' : Fin 13, a ∈ singerLines3 l' → b ∈ singerLines3 l' → l' = l := by
  decide

lemma card_union_three_lines (l1 l2 l3 : Fin 13)
    (h12 : l1 ≠ l2) (h13 : l1 ≠ l3) (h23 : l2 ≠ l3)
    (hnc : ∀ p : Fin 13, ¬(p ∈ singerLines3 l1 ∧ p ∈ singerLines3 l2 ∧ p ∈ singerLines3 l3)) :
    (singerLines3 l1 ∪ singerLines3 l2 ∪ singerLines3 l3).card = 9 := by
  have c1 := sL_card l1
  have c2 := sL_card l2
  have c3 := sL_card l3
  have i12 := sL_inter_eq_one l1 l2 h12
  have i13 := sL_inter_eq_one l1 l3 h13
  have i23 := sL_inter_eq_one l2 l3 h23
  have h12u : (singerLines3 l1 ∪ singerLines3 l2).card = 7 := by
    have := Finset.card_union_add_card_inter (singerLines3 l1) (singerLines3 l2)
    omega
  have hdisj : Disjoint (singerLines3 l1 ∩ singerLines3 l3) (singerLines3 l2 ∩ singerLines3 l3) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_inter] at hp1 hp2
    exact hnc p ⟨hp1.1, hp2.1, hp1.2⟩
  have hi123 : ((singerLines3 l1 ∪ singerLines3 l2) ∩ singerLines3 l3).card = 2 := by
    rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hdisj, i13, i23]
  have := Finset.card_union_add_card_inter (singerLines3 l1 ∪ singerLines3 l2) (singerLines3 l3)
  omega

lemma card_biUnion_lines_le (x2 : Finset (Fin 13))
    (hcard : x2.card ≤ 3)
    (hnc : ∀ p : Fin 13, (x2.filter (fun l => p ∈ singerLines3 l)).card ≤ 2) :
    (x2.biUnion singerLines3).card ≤ 9 := by
  by_cases h0 : x2.card = 0
  · rw [Finset.card_eq_zero.mp h0]; simp
  by_cases h1 : x2.card = 1
  · obtain ⟨l1, rfl⟩ := Finset.card_eq_one.mp h1
    simp [sL_card]
  by_cases h2 : x2.card = 2
  · obtain ⟨l1, l2, hne, rfl⟩ := Finset.card_eq_two.mp h2
    have hbi : ({l1, l2} : Finset (Fin 13)).biUnion singerLines3 = singerLines3 l1 ∪ singerLines3 l2 := by
      ext p; simp
    rw [hbi]
    have := Finset.card_union_add_card_inter (singerLines3 l1) (singerLines3 l2)
    have := sL_card l1; have := sL_card l2; have := sL_inter_eq_one l1 l2 hne
    omega
  · have h3 : x2.card = 3 := by omega
    obtain ⟨l1, l2, l3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp h3
    have hbi : ({l1, l2, l3} : Finset (Fin 13)).biUnion singerLines3 =
        singerLines3 l1 ∪ singerLines3 l2 ∪ singerLines3 l3 := by
      ext p; simp [or_assoc]
    rw [hbi]
    have hnc3 : ∀ p : Fin 13, ¬(p ∈ singerLines3 l1 ∧ p ∈ singerLines3 l2 ∧ p ∈ singerLines3 l3) := by
      intro p ⟨hp1, hp2, hp3⟩
      have hsub : ({l1, l2, l3} : Finset (Fin 13)) ⊆
          ({l1, l2, l3} : Finset (Fin 13)).filter (fun l => p ∈ singerLines3 l) := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
        rcases hl with rfl | rfl | rfl
        · exact ⟨Or.inl rfl, hp1⟩
        · exact ⟨Or.inr (Or.inl rfl), hp2⟩
        · exact ⟨Or.inr (Or.inr rfl), hp3⟩
      have hc := Finset.card_le_card hsub
      have h3c : ({l1, l2, l3} : Finset (Fin 13)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
      have hle2 := hnc p
      omega
    rw [card_union_three_lines l1 l2 l3 h12 h13 h23 hnc3]

lemma mem_missLines_iff (X : Finset (Fin 13)) (l : Fin 13) :
    l ∈ missLines singerLines3 X ↔ ∀ p ∈ X, p ∉ singerLines3 l := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  exact ⟨fun h p hp hpl => h hpl hp, fun h p hpl hp => h p hp hpl⟩

lemma extend_one (x1 x2 : Finset (Fin 13))
    (h1 : x1.card ≤ 3) (h2 : x2.card ≤ 3)
    (hcol : ∀ l : Fin 13, (x1 ∩ singerLines3 l).card ≤ 2)
    (hcon : ∀ p : Fin 13, (x2.filter (fun l => p ∈ singerLines3 l)).card ≤ 2)
    (hmiss : x2 ⊆ missLines singerLines3 x1) :
    ∃ p : Fin 13, p ∉ x1 ∧
      (∀ l : Fin 13, (insert p x1 ∩ singerLines3 l).card ≤ 2) ∧
      x2 ⊆ missLines singerLines3 (insert p x1) := by
  let U := x2.biUnion singerLines3
  have hU9 : U.card ≤ 9 := card_biUnion_lines_le x2 h2 hcon
  have hU_miss : ∀ p : Fin 13, p ∉ U → x2 ⊆ missLines singerLines3 (insert p x1) := by
    intro p hpU l hl
    rw [mem_missLines_iff]
    intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hqx1
    · intro hpl
      exact hpU (Finset.mem_biUnion.mpr ⟨l, hl, hpl⟩)
    · exact (mem_missLines_iff x1 l).mp (hmiss hl) q hqx1
  by_cases hc0 : x1.card = 0
  · have hx1 : x1 = ∅ := Finset.card_eq_zero.mp hc0
    subst hx1
    have hlt : U.card < (Finset.univ : Finset (Fin 13)).card := by simp; omega
    obtain ⟨p, _, hpU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨p, by simp, ?_, hU_miss p hpU⟩
    intro l
    change ({p} ∩ singerLines3 l).card ≤ 2
    have hle : ({p} ∩ singerLines3 l).card ≤ ({p} : Finset (Fin 13)).card := Finset.card_le_card Finset.inter_subset_left
    rw [Finset.card_singleton] at hle
    omega
  by_cases hc1 : x1.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
    have hlt : (insert a U).card < (Finset.univ : Finset (Fin 13)).card := by
      have := Finset.card_insert_le a U; simp; omega
    obtain ⟨p, _, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, not_or] at hp
    refine ⟨p, by simp [hp.1], ?_, hU_miss p hp.2⟩
    intro l
    have hle : (insert p {a} ∩ singerLines3 l).card ≤ (insert p {a} : Finset (Fin 13)).card :=
      Finset.card_le_card Finset.inter_subset_left
    have hle2 : (insert p {a} : Finset (Fin 13)).card ≤ 2 := by
      have := Finset.card_insert_le p ({a} : Finset (Fin 13)); simp at this; omega
    omega
  by_cases hc2 : x1.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc2
    obtain ⟨lab, halab, hblab, hlab_uniq⟩ := unique_line_of_ne a b hab
    let F := singerLines3 lab ∪ U
    have hFlt : F.card < (Finset.univ : Finset (Fin 13)).card := by
      by_cases hx2e : x2 = ∅
      · have hUe : U = ∅ := by simp [U, hx2e]
        simp [F, hUe, sL_card]
      · obtain ⟨l0, hl0⟩ := Finset.nonempty_iff_ne_empty.mpr hx2e
        have hl0_ne : l0 ≠ lab := by
          intro heq; subst heq
          exact (mem_missLines_iff {a, b} l0).mp (hmiss hl0) a (by simp) halab
        have hi : (singerLines3 lab ∩ singerLines3 l0).card = 1 := sL_inter_eq_one lab l0 hl0_ne.symm
        have hsub : singerLines3 lab ∩ singerLines3 l0 ⊆ singerLines3 lab ∩ U := by
          intro q hq
          simp only [Finset.mem_inter] at hq ⊢
          exact ⟨hq.1, Finset.mem_biUnion.mpr ⟨l0, hl0, hq.2⟩⟩
        have hiU : 1 ≤ (singerLines3 lab ∩ U).card := by
          have := Finset.card_le_card hsub; omega
        have huc := Finset.card_union_add_card_inter (singerLines3 lab) U
        have hlc := sL_card lab
        change (singerLines3 lab ∪ U).card < (Finset.univ : Finset (Fin 13)).card
        rw [Finset.card_univ, Fintype.card_fin]
        omega
    obtain ⟨p, _, hpF⟩ := Finset.exists_mem_notMem_of_card_lt_card hFlt
    simp only [F, Finset.mem_union, not_or] at hpF
    have hpa : p ≠ a := fun h => hpF.1 (h ▸ halab)
    have hpb : p ≠ b := fun h => hpF.1 (h ▸ hblab)
    refine ⟨p, by simp [hpa, hpb], ?_, hU_miss p hpF.2⟩
    intro l
    by_cases hpl : p ∈ singerLines3 l
    · have hlne : l ≠ lab := fun h => hpF.1 (h ▸ hpl)
      have hnotboth : ¬(a ∈ singerLines3 l ∧ b ∈ singerLines3 l) := fun ⟨ha, hb⟩ => hlne (hlab_uniq l ha hb)
      have hsub : insert p {a, b} ∩ singerLines3 l ⊆ insert p ({a, b} ∩ singerLines3 l) := by
        intro q hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq.1 with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨Or.inl rfl, hq.2⟩
        · exact Or.inr ⟨Or.inr rfl, hq.2⟩
      have hc1' : ({a, b} ∩ singerLines3 l).card ≤ 1 := by
        by_cases ha : a ∈ singerLines3 l
        · have hb : b ∉ singerLines3 l := fun hb => hnotboth ⟨ha, hb⟩
          have heq : ({a, b} : Finset (Fin 13)) ∩ singerLines3 l = {a} := by
            ext q; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hq⟩
              · rfl
              · exact (hb hq).elim
            · rintro rfl; exact ⟨Or.inl rfl, ha⟩
          rw [heq]; simp
        · have hsubb : ({a, b} : Finset (Fin 13)) ∩ singerLines3 l ⊆ {b} := by
            intro q hq
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
            rcases hq.1 with rfl | rfl
            · exact (ha hq.2).elim
            · rfl
          exact Nat.le_trans (Finset.card_le_card hsubb) (by simp)
      have := Finset.card_le_card hsub
      have := Finset.card_insert_le p ({a, b} ∩ singerLines3 l)
      omega
    · have heq : insert p {a, b} ∩ singerLines3 l = {a, b} ∩ singerLines3 l := by
        ext q; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hq, hql⟩
          · exact (hpl hql).elim
          · exact ⟨hq, hql⟩
        · rintro ⟨hq, hql⟩; exact ⟨Or.inr hq, hql⟩
      rw [heq]
      exact hcol l
  · have hc3 : x1.card = 3 := by omega
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc3
    obtain ⟨l1, ha1, hb1, h1uniq⟩ := unique_line_of_ne a b hab
    obtain ⟨l2, hb2, hc2', h2uniq⟩ := unique_line_of_ne b c hbc
    obtain ⟨l3, ha3, hc3', h3uniq⟩ := unique_line_of_ne a c hac
    have hnotcol : ∀ l : Fin 13, ¬(a ∈ singerLines3 l ∧ b ∈ singerLines3 l ∧ c ∈ singerLines3 l) := by
      intro l ⟨ha, hb, hc⟩
      have hsub : ({a, b, c} : Finset (Fin 13)) ⊆ ({a, b, c} : Finset (Fin 13)) ∩ singerLines3 l := by
        intro q hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq with rfl | rfl | rfl
        · exact ⟨Or.inl rfl, ha⟩
        · exact ⟨Or.inr (Or.inl rfl), hb⟩
        · exact ⟨Or.inr (Or.inr rfl), hc⟩
      have hle := hcol l
      have h3c : ({a, b, c} : Finset (Fin 13)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
      have := Finset.card_le_card hsub
      omega
    have hl12 : l1 ≠ l2 := fun h => hnotcol l1 ⟨ha1, hb1, h ▸ hc2'⟩
    have hl13 : l1 ≠ l3 := fun h => hnotcol l1 ⟨ha1, hb1, h ▸ hc3'⟩
    have hl23 : l2 ≠ l3 := fun h => hnotcol l2 ⟨h ▸ ha3, hb2, hc2'⟩
    have hnc_tri : ∀ p : Fin 13, ¬(p ∈ singerLines3 l1 ∧ p ∈ singerLines3 l2 ∧ p ∈ singerLines3 l3) := by
      intro p ⟨hp1, hp2, hp3⟩
      have hpb : p = b := by
        by_contra hne
        exact hl12 ((h1uniq l2 (by
          -- wait: b is in both l1 and l2; unique point of l1 cap l2 is b!
          exfalso
          have hsub : ({p, b} : Finset (Fin 13)) ⊆ singerLines3 l1 ∩ singerLines3 l2 := by
            intro q hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hp1, hp2⟩
            · exact Finset.mem_inter.mpr ⟨hb1, hb2⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_pair hne, sL_inter_eq_one l1 l2 hl12] at hc
          omega) hb2).symm)
      subst hpb
      exact hnotcol l3 ⟨ha3, hp3, hc3'⟩
    let T := singerLines3 l1 ∪ singerLines3 l2 ∪ singerLines3 l3
    have hTcard : T.card = 9 := card_union_three_lines l1 l2 l3 hl12 hl13 hl23 hnc_tri
    let R := Finset.univ \ T
    have hRcard : R.card = 4 := by
      dsimp only [R]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hTcard]
    have hline_R : ∀ l ∈ x2, (R ∩ singerLines3 l).card ≤ 1 := by
      intro l hl
      have ha_not : a ∉ singerLines3 l := (mem_missLines_iff _ l).mp (hmiss hl) a (by simp)
      have hb_not : b ∉ singerLines3 l := (mem_missLines_iff _ l).mp (hmiss hl) b (by simp)
      have hc_not : c ∉ singerLines3 l := (mem_missLines_iff _ l).mp (hmiss hl) c (by simp)
      have hll1 : l ≠ l1 := fun h => ha_not (h ▸ ha1)
      have hll2 : l ≠ l2 := fun h => hb_not (h ▸ hb2)
      have hll3 : l ≠ l3 := fun h => hc_not (h ▸ hc3')
      obtain ⟨p1, hp1⟩ := Finset.card_pos.mp (by rw [sL_inter_eq_one l l1 hll1]; omega)
      obtain ⟨p2, hp2⟩ := Finset.card_pos.mp (by rw [sL_inter_eq_one l l2 hll2]; omega)
      obtain ⟨p3, hp3⟩ := Finset.card_pos.mp (by rw [sL_inter_eq_one l l3 hll3]; omega)
      simp only [Finset.mem_inter] at hp1 hp2 hp3
      have hp12 : p1 ≠ p2 := by
        intro heq; subst heq
        have hsub : ({p1, b} : Finset (Fin 13)) ⊆ singerLines3 l1 ∩ singerLines3 l2 := by
          intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp1.2, hp2.2⟩
          · exact Finset.mem_inter.mpr ⟨hb1, hb2⟩
        have hne : p1 ≠ b := fun h => hb_not (h ▸ hp1.1)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, sL_inter_eq_one l1 l2 hl12] at hc; omega
      have hp13 : p1 ≠ p3 := by
        intro heq; subst heq
        have hsub : ({p1, a} : Finset (Fin 13)) ⊆ singerLines3 l1 ∩ singerLines3 l3 := by
          intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp1.2, hp3.2⟩
          · exact Finset.mem_inter.mpr ⟨ha1, ha3⟩
        have hne : p1 ≠ a := fun h => ha_not (h ▸ hp1.1)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, sL_inter_eq_one l1 l3 hl13] at hc; omega
      have hp23 : p2 ≠ p3 := by
        intro heq; subst heq
        have hsub : ({p2, c} : Finset (Fin 13)) ⊆ singerLines3 l2 ∩ singerLines3 l3 := by
          intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp2.2, hp3.2⟩
          · exact Finset.mem_inter.mpr ⟨hc2', hc3'⟩
        have hne : p2 ≠ c := fun h => hc_not (h ▸ hp2.1)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, sL_inter_eq_one l2 l3 hl23] at hc; omega
      have hsubT : ({p1, p2, p3} : Finset (Fin 13)) ⊆ T ∩ singerLines3 l := by
        intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hp1.2), hp1.1⟩
        · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hp2.2), hp2.1⟩
        · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hp3.2, hp3.1⟩
      have h3in : 3 ≤ (T ∩ singerLines3 l).card := by
        have h3c : ({p1, p2, p3} : Finset (Fin 13)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hp12, hp13]),
            Finset.card_insert_of_notMem (by simp [hp23]), Finset.card_singleton]
        have := Finset.card_le_card hsubT; omega
      have hdisjRT : Disjoint (R ∩ singerLines3 l) (T ∩ singerLines3 l) := by
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        simp only [R, Finset.mem_inter, Finset.mem_sdiff] at hq1 hq2
        exact hq1.1.2 hq2.1
      have hunion_sub : (R ∩ singerLines3 l) ∪ (T ∩ singerLines3 l) ⊆ singerLines3 l :=
        Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
      have hle4 := Finset.card_le_card hunion_sub
      rw [Finset.card_union_of_disjoint hdisjRT, sL_card l] at hle4
      omega
    have hRU_le : (R ∩ U).card ≤ 3 := by
      have hsub : R ∩ U ⊆ x2.biUnion (fun l => R ∩ singerLines3 l) := by
        intro q hq
        simp only [U, Finset.mem_inter, Finset.mem_biUnion] at hq ⊢
        rcases hq.2 with ⟨l, hl, hql⟩
        exact ⟨l, hl, hq.1, hql⟩
      calc (R ∩ U).card
          ≤ (x2.biUnion (fun l => R ∩ singerLines3 l)).card := Finset.card_le_card hsub
        _ ≤ ∑ l ∈ x2, (R ∩ singerLines3 l).card := Finset.card_biUnion_le
        _ ≤ ∑ _l ∈ x2, 1 := Finset.sum_le_sum hline_R
        _ = x2.card := by simp
        _ ≤ 3 := h2
    have hlt : (R ∩ U).card < R.card := by omega
    obtain ⟨p, hpR, hpnotRU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hpU : p ∉ U := fun h => hpnotRU (Finset.mem_inter.mpr ⟨hpR, h⟩)
    have hpT : p ∉ T := (Finset.mem_sdiff.mp hpR).2
    have hpa : p ≠ a := fun h => hpT (h ▸ Finset.mem_union_left _ (Finset.mem_union_left _ ha1))
    have hpb : p ≠ b := fun h => hpT (h ▸ Finset.mem_union_left _ (Finset.mem_union_left _ hb1))
    have hpc : p ≠ c := fun h => hpT (h ▸ Finset.mem_union_left _ (Finset.mem_union_right _ hc2'))
    refine ⟨p, by simp [hpa, hpb, hpc], ?_, hU_miss p hpU⟩
    intro l
    by_cases hpl : p ∈ singerLines3 l
    · have hlne1 : l ≠ l1 := fun h => hpT (Finset.mem_union_left _ (Finset.mem_union_left _ (h ▸ hpl)))
      have hlne2 : l ≠ l2 := fun h => hpT (Finset.mem_union_left _ (Finset.mem_union_right _ (h ▸ hpl)))
      have hlne3 : l ≠ l3 := fun h => hpT (Finset.mem_union_right _ (h ▸ hpl))
      have h1_le : ({a, b, c} ∩ singerLines3 l).card ≤ 1 := by
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ ({a, b, c} ∩ singerLines3 l).card := by omega
        obtain ⟨u, v, huv, huvsub⟩ : ∃ u v, u ≠ v ∧ u ∈ ({a, b, c} ∩ singerLines3 l) ∧ v ∈ ({a, b, c} ∩ singerLines3 l) := by
          obtain ⟨S2, hS2sub, hS2card⟩ := Finset.exists_subset_card_eq hge2
          obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hS2card
          exact ⟨u, v, huv, hS2sub (by simp), hS2sub (by simp)⟩
        rcases huvsub with ⟨hu, hv⟩
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu.1 with rfl | rfl | rfl <;> rcases hv.1 with rfl | rfl | rfl
        · exact huv rfl
        · exact hlne1 (h1uniq l hu.2 hv.2)
        · exact hlne3 (h3uniq l hu.2 hv.2)
        · exact hlne1 (h1uniq l hv.2 hu.2)
        · exact huv rfl
        · exact hlne2 (h2uniq l hu.2 hv.2)
        · exact hlne3 (h3uniq l hv.2 hu.2)
        · exact hlne2 (h2uniq l hv.2 hu.2)
        · exact huv rfl
      have hsub : insert p {a, b, c} ∩ singerLines3 l ⊆ insert p ({a, b, c} ∩ singerLines3 l) := by
        intro q hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq.1 with rfl | hq'
        · exact Or.inl rfl
        · exact Or.inr ⟨hq', hq.2⟩
      have := Finset.card_le_card hsub
      have := Finset.card_insert_le p ({a, b, c} ∩ singerLines3 l)
      omega
    · have heq : insert p {a, b, c} ∩ singerLines3 l = {a, b, c} ∩ singerLines3 l := by
        ext q; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hq, hql⟩
          · exact (hpl hql).elim
          · exact ⟨hq, hql⟩
        · rintro ⟨hq, hql⟩; exact ⟨Or.inr hq, hql⟩
      rw [heq]
      exact hcol l

lemma extend_to_quad :
    ∀ k : ℕ, ∀ x1 x2 : Finset (Fin 13),
      4 - x1.card = k → x1.card ≤ 4 → x2.card ≤ 3 →
      (∀ l : Fin 13, (x1 ∩ singerLines3 l).card ≤ 2) →
      (∀ p : Fin 13, (x2.filter (fun l => p ∈ singerLines3 l)).card ≤ 2) →
      x2 ⊆ missLines singerLines3 x1 →
      ∃ Q ∈ quadrangles singerLines3, x1 ⊆ Q ∧ x2 ⊆ missLines singerLines3 Q := by
  intro k
  induction k with
  | zero =>
    intro x1 x2 hk h1 _ hcol _ hmiss
    have h4 : x1.card = 4 := by omega
    refine ⟨x1, ?_, Finset.Subset.refl x1, hmiss⟩
    simp only [quadrangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact ⟨h4, hcol⟩
  | succ k ih =>
    intro x1 x2 hk h1 h2 hcol hcon hmiss
    have hle3 : x1.card ≤ 3 := by omega
    obtain ⟨p, hpnot, hcol', hmiss'⟩ := extend_one x1 x2 hle3 h2 hcol hcon hmiss
    have hcard' : (insert p x1).card = x1.card + 1 := Finset.card_insert_of_notMem hpnot
    obtain ⟨Q, hQ, hsubQ, hmissQ⟩ := ih (insert p x1) x2 (by omega) (by omega) h2 hcol' hcon hmiss'
    exact ⟨Q, hQ, Finset.Subset.trans (Finset.subset_insert p x1) hsubQ, hmissQ⟩

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.GenericRejection

abbrev I := Fin 13
abbrev lines := singerLines3

def D : Finset I := {0,1,3,9}
theorem incid : ∀p l:I,p∈lines l ↔ p-l∈D := by decide +kernel
def X (P L:Finset I) (b:Bool) := incidenceInput P L ++ [b]
def Pos (C:Circuit) (ex:I) (b:Bool) := ∀p l:I,p-l∈D → p≠0 ∨ l≠ex → C.eval (X {p} {l} b)=true
def Neg (C:Circuit) (b:Bool) := ∀Q∈quadrangles lines,C.eval (X Q (missLines lines Q) b)=false

theorem upBit (C:Circuit) (mc:Monotone2 C) (b:Bool) {P L P' L':Finset I}
    (pp:P⊆P') (ll:L⊆L') : C.eval (X P L b)=true → C.eval (X P' L' b)=true := by
  let wire (P L:Finset I) := Fin.append (fun p:I=>decide (p∈P)) (fun l:I=>decide (l∈L))
  have wrap (P L:Finset I) : List.ofFn (Fin.append (wire P L) (fun _ : Fin 1=>b))=X P L b := by
    rw [List.ofFn_fin_append]
    simp [X,incidenceInput,wire,List.ofFn_fin_append,List.ofFn_succ]
  rw [←wrap P L,←wrap P' L']
  apply cmono C mc
  intro i
  induction i using Fin.addCases with
  | right k => simp
  | left k =>
    simp only [Fin.append,Fin.addCases_left]
    induction k using Fin.addCases with
    | left p =>
      change decide (p∈P) ≤ decide (p∈P')
      by_cases h:p∈P
      · simp [h,pp h]
      · simp [h]
    | right l =>
      change decide (l∈L) ≤ decide (l∈L')
      by_cases h:l∈L
      · simp [h,ll h]
      · simp [h]

theorem negativeSmall (C:Circuit) (mc:Monotone2 C) (b:Bool) (no:Neg C b) (P L:Finset I)
    (pc:P.card≤4) (lc:L.card≤3) (pa:∀l,(P∩lines l).card≤2)
    (la:∀p,(L.filter fun l=>p∈lines l).card≤2) (free:L⊆missLines lines P) :
    C.eval (X P L b)=false := by
  obtain ⟨Q,hq,ps,ls⟩ := extend_to_quad (4-P.card) P L rfl pc lc pa la free
  cases hv:C.eval (X P L b) with
  | false=>rfl
  | true => exact Bool.noConfusion ((no Q hq).symm.trans (upBit C mc b ps ls hv))

theorem dyads (C:Circuit) (mc:Monotone2 C) (b:Bool) (no:Neg C b)
    (p q l k:I) (a:p-l∉D) (a':p-k∉D) (r:q-l∉D) (r':q-k∉D) :
    C.eval (X {p,q} {l,k} b)=false := by
  have c (u v:I):({u,v}:Finset I).card≤2 := by
    by_cases h:u=v
    · subst v;simp
    · simp [h]
  refine negativeSmall C mc b no _ _ ((c p q).trans (by decide)) ((c l k).trans (by decide))
    (fun x=>(Finset.card_le_card Finset.inter_subset_left).trans (c p q))
    (fun x=>(Finset.card_filter_le _ _).trans (c l k)) ?_
  intro x hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,Finset.disjoint_left.mpr ?_⟩
  intro y hy hh
  have hxy := (incid y x).mp hy
  rcases (show x=l ∨ x=k by simpa using hx) with rfl|rfl <;>
    rcases (show y=p ∨ y=q by simpa using hh) with rfl|rfl <;> contradiction

theorem missEq (Q:Finset I) : {l: I | ∀p∈Q,p-l∉D}=missLines lines Q := by
  ext l
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,missLines,Finset.disjoint_left]
  constructor
  · intro h p hi hp;exact h p hp ((incid p l).mp hi)
  · intro h p hp hi;exact h ((incid p l).mpr hi) hp

theorem flatBound (C:Circuit) (ex:I) (b:Bool) (mc:Monotone2 C)
    (back:PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 C) (yes:Pos C ex b) (no:Neg C b)
    (few:PEqualNP.TopForm.andPairs 27 C≤1) : 63≤C.size := by
  have n' (Q:Finset I) (sz:Q.card=4) (arc:∀l:I,(Q.filter fun p=>p-l∈D).card≤2) :
      C.eval (X Q {l:I | ∀p∈Q,p-l∉D} b)=false := by
    rw [missEq]; apply no
    simp only [quadrangles,Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and]
    refine ⟨sz,fun l=>?_⟩
    have e : Q∩lines l=Q.filter (fun p=>p-l∈D) := by ext p;simp only [Finset.mem_inter,Finset.mem_filter,incid]
    rw [e]; exact arc l
  rcases (show PEqualNP.TopForm.andPairs 27 C=0 ∨ PEqualNP.TopForm.andPairs 27 C=1 by omega) with h|h
  · exact PEqualNP.Outside.L_meta_5809 C 0 ex b mc back h yes n' (dyads C mc b no)
  · exact PEqualNP.Outside.L_meta_5811 C 0 ex b mc back h yes n' (dyads C mc b no)

end Plane17147
