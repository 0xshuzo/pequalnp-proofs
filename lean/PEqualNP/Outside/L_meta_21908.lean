import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21908_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · exact List.getD_append _ _ _ _ hi
    · simp [stepW]; omega

private def effInputs (N : ℕ) (C : Circuit) (k : ℕ) : List ℕ :=
  let g := C.gates.getD k ⟨GateOp.or, []⟩
  let raw := match g.op with
    | GateOp.not => g.inputs.take 1
    | _ => g.inputs
  raw.filter fun i => decide (i < N + k)

private lemma effInputs_lt (N : ℕ) (C : Circuit) (k i : ℕ) (hi : i ∈ effInputs N C k) :
    i < N + k := by
  simp only [effInputs, List.mem_filter, decide_eq_true_eq] at hi
  exact hi.2

private def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma effInputs_len (N : ℕ) (C : Circuit) (hF : FanInTwo C) (k : ℕ) (hk : k < C.gates.length) :
    (effInputs N C k).length ≤ if isNot C.gates[k].op then 1 else 2 := by
  have hg : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hk
  have hlen : C.gates[k].inputs.length ≤ 2 := (hF _ (List.getElem_mem hk)).2
  simp only [effInputs, hg]
  cases hop : C.gates[k].op <;> simp only [isNot, Bool.false_eq_true, ↓reduceIte]
  · exact le_trans (List.length_filter_le _ _) hlen
  · exact le_trans (List.length_filter_le _ _) hlen
  · exact le_trans (List.length_filter_le _ _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  · exact le_trans (List.length_filter_le _ _) hlen
  · exact le_trans (List.length_filter_le _ _) hlen

private def reachAux (N : ℕ) (C : Circuit) : ℕ → Finset ℕ → Finset ℕ
  | 0, acc => acc
  | m + 1, acc =>
    let acc' :=
      if m < C.gates.length ∧ N + m ∈ acc then acc ∪ (effInputs N C m).toFinset else acc
    reachAux N C m acc'

private lemma reachAux_sub (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ) :
    acc ⊆ reachAux N C m acc := by
  induction m generalizing acc with
  | zero => exact Finset.Subset.rfl
  | succ m ih =>
    dsimp [reachAux]
    split_ifs
    · exact Finset.Subset.trans Finset.subset_union_left (ih _)
    · exact ih _

private lemma reachAux_le (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ) (M : ℕ)
    (hacc : ∀ w ∈ acc, w ≤ M) : ∀ w ∈ reachAux N C m acc, w ≤ M := by
  induction m generalizing acc with
  | zero => exact hacc
  | succ m ih =>
    dsimp [reachAux]
    apply ih
    intro w hw
    split_ifs at hw with h
    · rcases Finset.mem_union.mp hw with ha | hi
      · exact hacc w ha
      · have hlt := effInputs_lt N C m w (List.mem_toFinset.mp hi)
        have hle := hacc (N + m) h.2
        omega
    · exact hacc w hw

private lemma reachAux_closed (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ)
    (hhi : ∀ k, m ≤ k → k < C.gates.length → N + k ∈ acc → ∀ i ∈ effInputs N C k, i ∈ acc) :
    ∀ k, k < C.gates.length → N + k ∈ reachAux N C m acc → ∀ i ∈ effInputs N C k, i ∈ reachAux N C m acc := by
  induction m generalizing acc with
  | zero =>
    intro k hk hmem i hi
    exact hhi k (Nat.zero_le k) hk hmem i hi
  | succ m ih =>
    let acc' := if m < C.gates.length ∧ N + m ∈ acc then acc ∪ (effInputs N C m).toFinset else acc
    have hstep : reachAux N C (m + 1) acc = reachAux N C m acc' := rfl
    rw [hstep]
    apply ih acc'
    intro k hmk hk hmem i hi
    by_cases heq : k = m
    · subst heq
      have hmem_acc : N + k ∈ acc := by
        dsimp [acc'] at hmem
        split_ifs at hmem with h
        · exact h.2
        · exact hmem
      have hsub : (effInputs N C k).toFinset ⊆ acc' := by
        dsimp [acc']
        simp only [hk, hmem_acc, and_self, ↓reduceIte]
        exact Finset.subset_union_right
      exact hsub (List.mem_toFinset.mpr hi)
    · have hlt : m + 1 ≤ k := by omega
      have hmem_acc : N + k ∈ acc := by
        dsimp [acc'] at hmem
        split_ifs at hmem with h
        · rcases Finset.mem_union.mp hmem with ha | hin
          · exact ha
          · have := effInputs_lt N C m (N + k) (List.mem_toFinset.mp hin)
            omega
        · exact hmem
      have hsub : acc ⊆ acc' := by
        dsimp [acc']; split_ifs
        · exact Finset.subset_union_left
        · exact Finset.Subset.rfl
      exact hsub (hhi k hlt hk hmem_acc i hi)

private lemma reachAux_bound (N : ℕ) (C : Circuit) (m : ℕ) (acc : Finset ℕ) :
    reachAux N C m acc ⊆ acc ∪
      ((Finset.range m).filter fun k => k < C.gates.length ∧ N + k ∈ reachAux N C m acc).biUnion
        (fun k => (effInputs N C k).toFinset) := by
  induction m generalizing acc with
  | zero => dsimp [reachAux]; exact Finset.subset_union_left
  | succ m ih =>
    let acc' := if m < C.gates.length ∧ N + m ∈ acc then acc ∪ (effInputs N C m).toFinset else acc
    have hstep : reachAux N C (m + 1) acc = reachAux N C m acc' := rfl
    intro w hw
    have h1 := ih acc' (hstep ▸ hw)
    rcases Finset.mem_union.mp h1 with hacc' | hbi
    · dsimp [acc'] at hacc'
      split_ifs at hacc' with h
      · rcases Finset.mem_union.mp hacc' with ha | hin
        · exact Finset.mem_union_left _ ha
        · apply Finset.mem_union_right
          rw [Finset.mem_biUnion]
          refine ⟨m, ?_, hin⟩
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.lt_succ_self m, h.1, ?_⟩
          rw [hstep]
          apply reachAux_sub
          dsimp [acc']
          simp only [h.1, h.2, and_self, ↓reduceIte]
          exact Finset.mem_union_left _ h.2
      · exact Finset.mem_union_left _ hacc'
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion] at hbi ⊢
      obtain ⟨k, hk, hwk⟩ := hbi
      rw [Finset.mem_filter, Finset.mem_range] at hk
      refine ⟨k, ?_, hwk⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_lt hk.1, hk.2.1, hstep.symm ▸ hk.2.2⟩

private def subW (N : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  reachAux N C C.gates.length {w}

private lemma self_mem_subW (N : ℕ) (C : Circuit) (w : ℕ) : w ∈ subW N C w :=
  reachAux_sub N C C.gates.length {w} (Finset.mem_singleton_self w)

private lemma subW_le (N : ℕ) (C : Circuit) (w u : ℕ) (hu : u ∈ subW N C w) : u ≤ w :=
  reachAux_le N C C.gates.length {w} w (fun z hz => by rw [Finset.mem_singleton.mp hz]) u hu

private lemma subW_closed (N : ℕ) (C : Circuit) (w k : ℕ) (hk : k < C.gates.length)
    (hmem : N + k ∈ subW N C w) (i : ℕ) (hi : i ∈ effInputs N C k) : i ∈ subW N C w :=
  reachAux_closed N C C.gates.length {w} (fun _ h1 h2 => by omega) k hk hmem i hi

private lemma subW_sub_of_mem (N : ℕ) (C : Circuit) (w1 w2 : ℕ) (h : w1 ∈ subW N C w2) :
    subW N C w1 ⊆ subW N C w2 := by
  have haux : ∀ m (acc : Finset ℕ), acc ⊆ subW N C w2 → reachAux N C m acc ⊆ subW N C w2 := by
    intro m
    induction m with
    | zero => intro acc hacc; exact hacc
    | succ m ih =>
      intro acc hacc
      dsimp [reachAux]
      apply ih
      split_ifs with hm
      · refine Finset.union_subset hacc ?_
        intro i hi
        exact subW_closed N C w2 m hm.1 (hacc hm.2) i (List.mem_toFinset.mp hi)
      · exact hacc
  exact haux C.gates.length {w1} (Finset.singleton_subset_iff.mpr h)

private lemma subW_parent (N : ℕ) (C : Circuit) (w u : ℕ) (hu : u ∈ subW N C w) (hne : u ≠ w) :
    ∃ k < C.gates.length, N + k ∈ subW N C w ∧ u ∈ effInputs N C k := by
  have hb := reachAux_bound N C C.gates.length {w} hu
  rcases Finset.mem_union.mp hb with hsing | hbi
  · exact absurd (Finset.mem_singleton.mp hsing) hne
  · obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hbi
    rw [Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨k, hk.2.1, hk.2.2, List.mem_toFinset.mp huk⟩

private lemma wire_getD_input (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (i : ℕ) (hi : i < N) :
    (C.wires x).getD i false = x.getD i false := by
  change (C.gates.foldl stepW x).getD i false = x.getD i false
  exact foldl_getD_lt C.gates x i (by omega)

private lemma wire_getD_gate (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (N + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => if i < N + k then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ, List.take_append_drop]
  change (C.gates.foldl stepW x).getD (N + k) false = _
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen1 : ((C.gates.take k).foldl stepW x).length = N + k := by
    rw [foldl_len, hx, List.length_take]; omega
  have hlt : N + k < (stepW ((C.gates.take k).foldl stepW x) C.gates[k]).length := by
    simp only [stepW, List.length_append, List.length_singleton, hlen1]; omega
  rw [foldl_getD_lt _ _ _ hlt]
  simp only [stepW]
  have hget : ((C.gates.take k).foldl stepW x ++
      [C.gates[k].op.eval (C.gates[k].inputs.map fun i => ((C.gates.take k).foldl stepW x).getD i false)]).getD (N + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => ((C.gates.take k).foldl stepW x).getD i false) := by
    rw [← hlen1]
    simp [List.getD_eq_getElem?_getD]
  rw [hget]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < N + k
  · simp only [hi, ↓reduceIte]
    have hsplit2 : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    change ((C.gates.take k).foldl stepW x).getD i false = (C.gates.foldl stepW x).getD i false
    conv_rhs => rw [hsplit2]
    rw [List.foldl_append]
    exact (foldl_getD_lt _ _ i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

private lemma eval_gate_eff (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.gates[k].op = GateOp.and → (C.wires x).getD (N + k) false =
      (if C.gates[k].inputs.all (fun i => decide (i < N + k)) then (effInputs N C k).all (fun i => (C.wires x).getD i false) else false)) ∧
    (C.gates[k].op = GateOp.or → (C.wires x).getD (N + k) false = (effInputs N C k).any (fun i => (C.wires x).getD i false)) ∧
    (C.gates[k].op = GateOp.not → (C.wires x).getD (N + k) false =
      match effInputs N C k with | a :: _ => !((C.wires x).getD a false) | [] => true) := by
  have hgk : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hk
  refine ⟨?_, ?_, ?_⟩
  · intro hop
    rw [wire_getD_gate N C x hx k hk, hop]
    simp only [effInputs, hgk, hop, GateOp.eval, List.all_map]
    by_cases hall : C.gates[k].inputs.all (fun i => decide (i < N + k)) = true
    · simp only [hall, ↓reduceIte]
      have hfilt : C.gates[k].inputs.filter (fun i => decide (i < N + k)) = C.gates[k].inputs :=
        List.filter_eq_self.mpr (fun i hi => List.all_eq_true.mp hall i hi)
      rw [hfilt]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp_apply, id_eq]
      constructor
      · intro h i hi
        have hlt : i < N + k := decide_eq_true_eq.mp (List.all_eq_true.mp hall i hi)
        simpa [hlt] using h i hi
      · intro h i hi
        have hlt : i < N + k := decide_eq_true_eq.mp (List.all_eq_true.mp hall i hi)
        simpa [hlt] using h i hi
    · simp only [hall, Bool.false_eq_true, ↓reduceIte]
      have hex : ∃ i ∈ C.gates[k].inputs, ¬ i < N + k := by
        by_contra hno
        push Not at hno
        exact hall (List.all_eq_true.mpr (fun i hi => decide_eq_true (hno i hi)))
      obtain ⟨i, hi, hnot⟩ := hex
      rw [Bool.eq_false_iff]
      intro ht
      have := List.all_eq_true.mp ht i hi
      simp [hnot] at this
  · intro hop
    rw [wire_getD_gate N C x hx k hk, hop]
    simp only [effInputs, hgk, hop, GateOp.eval, List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, hv⟩
      by_cases hlt : i < N + k
      · simp only [hlt, ↓reduceIte] at hv
        exact ⟨i, ⟨hi, hlt⟩, hv⟩
      · simp [hlt] at hv
    · rintro ⟨i, ⟨hi, hlt⟩, hv⟩
      exact ⟨i, hi, by simp only [hlt, ↓reduceIte]; exact hv⟩
  · intro hop
    rw [wire_getD_gate N C x hx k hk, hop]
    simp only [effInputs, hgk, hop, GateOp.eval]
    cases hin : C.gates[k].inputs with
    | nil => rfl
    | cons a rest =>
      simp only [List.take_succ_cons, List.take_zero, List.filter_cons, List.filter_nil, List.map_cons, List.headD_cons]
      by_cases ha : a < N + k
      · simp [ha]
      · simp [ha]

private lemma wires_agree_of_subW (N : ℕ) (C : Circuit) (hF : FanInTwo C) (w0 : ℕ)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, i < N → i ∈ subW N C w0 → x.getD i false = y.getD i false) :
    ∀ w, w ∈ subW N C w0 → (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < N
    · rw [wire_getD_input N C x hx w hwn, wire_getD_input N C y hy w hwn]
      exact hxy w hwn hw
    · by_cases hwg : w < N + C.gates.length
      · have hk : w - N < C.gates.length := by omega
        have hweq : w = N + (w - N) := by omega
        rw [hweq] at hw ⊢
        obtain ⟨hand, hor, hnot⟩ := eval_gate_eff N C x hx (w - N) hk
        obtain ⟨hand', hor', hnot'⟩ := eval_gate_eff N C y hy (w - N) hk
        have hop := (hF _ (List.getElem_mem hk)).1
        have hrec : ∀ i ∈ effInputs N C (w - N), (C.wires x).getD i false = (C.wires y).getD i false := by
          intro i hi
          have hilt := effInputs_lt N C (w - N) i hi
          exact ih i (by omega) (subW_closed N C w0 (w - N) hk hw i hi)
        rcases Set.mem_insert_iff.mp hop with h1 | h2
        · rw [hand h1, hand' h1]
          split_ifs
          · apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
            constructor <;> intro h i hi
            · rw [← hrec i hi]; exact h i hi
            · rw [hrec i hi]; exact h i hi
          · rfl
        · rcases Set.mem_insert_iff.mp h2 with h2 | h3
          · rw [hor h2, hor' h2]
            apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true]
            constructor <;> rintro ⟨i, hi, hv⟩
            · exact ⟨i, hi, hrec i hi ▸ hv⟩
            · exact ⟨i, hi, (hrec i hi).symm ▸ hv⟩
          · have h3' : C.gates[w - N].op = GateOp.not := Set.mem_singleton_iff.mp h3
            rw [hnot h3', hnot' h3']
            cases heff : effInputs N C (w - N) with
            | nil => rfl
            | cons a rest =>
              have ha : a ∈ effInputs N C (w - N) := by rw [heff]; simp
              dsimp only
              rw [hrec a ha]
      · have hlx : (C.wires x).length = N + C.gates.length := by
          change (C.gates.foldl stepW x).length = N + C.gates.length; rw [foldl_len, hx]
        have hly : (C.wires y).length = N + C.gates.length := by
          change (C.gates.foldl stepW y).length = N + C.gates.length; rw [foldl_len, hy]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private lemma mono_of_no_not (N : ℕ) (C : Circuit) (hF : FanInTwo C)
    (hnonot : ∀ k, (hk : k < C.gates.length) → N + k ∈ subW N C C.output → C.gates[k].op ≠ GateOp.not)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, i < N → i ∈ subW N C C.output → x.getD i false = true → y.getD i false = true) :
    ∀ w, w ∈ subW N C C.output → (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hvx
    by_cases hwn : w < N
    · rw [wire_getD_input N C x hx w hwn] at hvx
      rw [wire_getD_input N C y hy w hwn]
      exact hxy w hwn hw hvx
    · by_cases hwg : w < N + C.gates.length
      · have hk : w - N < C.gates.length := by omega
        have hweq : w = N + (w - N) := by omega
        rw [hweq] at hw hvx ⊢
        obtain ⟨hand, hor, _⟩ := eval_gate_eff N C x hx (w - N) hk
        obtain ⟨hand', hor', _⟩ := eval_gate_eff N C y hy (w - N) hk
        have hop := (hF _ (List.getElem_mem hk)).1
        have hrec : ∀ i ∈ effInputs N C (w - N), (C.wires x).getD i false = true → (C.wires y).getD i false = true := by
          intro i hi
          have hilt := effInputs_lt N C (w - N) i hi
          exact ih i (by omega) (subW_closed N C C.output (w - N) hk hw i hi)
        rcases Set.mem_insert_iff.mp hop with h1 | h2
        · rw [hand h1] at hvx; rw [hand' h1]
          split_ifs at hvx ⊢
          · rw [List.all_eq_true] at hvx ⊢
            intro i hi; exact hrec i hi (hvx i hi)
        · rcases Set.mem_insert_iff.mp h2 with h2 | h3
          · rw [hor h2] at hvx; rw [hor' h2]
            rw [List.any_eq_true] at hvx ⊢
            obtain ⟨i, hi, hv⟩ := hvx
            exact ⟨i, hi, hrec i hi hv⟩
          · exact absurd (Set.mem_singleton_iff.mp h3) (hnonot (w - N) hk hw)
      · have hlx : (C.wires x).length = N + C.gates.length := by
          change (C.gates.foldl stepW x).length = N + C.gates.length; rw [foldl_len, hx]
        rw [List.getD_eq_default _ _ (by omega)] at hvx
        exact Bool.noConfusion hvx

private lemma repInput_len {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma repInput_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n + m) :
    (oneEach u v).getD i false =
      if h : i < n then decide (⟨i, h⟩ = u) else decide (⟨i - n, by omega⟩ = v) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · simp only [h, ↓reduceDIte]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
    simp [h]
  · simp only [h, ↓reduceDIte]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getElem?_ofFn]
    simp [show i - n < m by omega]

theorem mono_bound {n m s minR minC : ℕ} (A : Fin n → Fin m → Bool)
    (hminR : (Finset.univ.filter fun u : Fin n => ∀ u' v, A u v = true → A u' v = true).card ≤ minR)
    (hminC : (Finset.univ.filter fun v : Fin m => ∀ v' u, A u v = true → A u v' = true).card ≤ minC)
    (hrep : RepSizeAtMost A s) : (n - minR) + (m - minC) ≤ s + 1 := by
  classical
  obtain ⟨C, hM, hsz, hRep⟩ := hrep
  have hF : FanInTwo C := by
    intro g hg
    obtain ⟨hop,har⟩ := hM g hg
    refine ⟨?_,har⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    tauto
  let N := n + m
  let W : Finset ℕ := subW N C C.output
  let R : Finset ℕ := (Finset.range C.gates.length).filter fun k => N + k ∈ W
  let Rnot : Finset ℕ := R.filter fun k => (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.not
  let Win : Finset ℕ := W.filter fun i => i < N
  let Wgate : Finset ℕ := R.image fun k => N + k
  have hRle : R.card ≤ C.size := by
    calc R.card ≤ (Finset.range C.gates.length).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = C.size := Finset.card_range _
  have hdisj : Disjoint Win Wgate := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have hw1 : w < N := (Finset.mem_filter.mp h1).2
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h2
    omega
  have hsubW : Win ∪ Wgate ⊆ W := by
    intro w hw
    rcases Finset.mem_union.mp hw with h1 | h2
    · exact (Finset.mem_filter.mp h1).1
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h2
      exact (Finset.mem_filter.mp hk).2
  have hWgate_card : Wgate.card = R.card := Finset.card_image_of_injective R (fun a b h => by omega)
  have hWcard : Win.card + R.card ≤ W.card := by
    calc Win.card + R.card = Win.card + Wgate.card := by rw [hWgate_card]
      _ = (Win ∪ Wgate).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ W.card := Finset.card_le_card hsubW
  let inDeg : ℕ → ℕ := fun u => ∑ k ∈ R, (effInputs N C k).count u
  have htotal_eq : ∑ u ∈ W, inDeg u = ∑ k ∈ R, (effInputs N C k).length := by
    dsimp [inDeg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hkW : N + k ∈ W := (Finset.mem_filter.mp hk).2
    have hsub : (effInputs N C k).toFinset ⊆ W := fun i hi =>
      subW_closed N C C.output k hklt hkW i (List.mem_toFinset.mp hi)
    have hlen : ∀ l : List ℕ, l.toFinset ⊆ W → ∑ u ∈ W, l.count u = l.length := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a tl ih =>
        intro htl
        have haW : a ∈ W := htl (by simp)
        have htlW : tl.toFinset ⊆ W := fun i hi => htl (by simp [List.mem_toFinset.mp hi])
        simp only [List.count_cons, List.length_cons]
        rw [Finset.sum_add_distrib, ih htlW]
        have h1 : ∑ u ∈ W, (if a == u then 1 else 0) = 1 := by
          simp [beq_iff_eq, haW]
        omega
    exact hlen (effInputs N C k) hsub
  have htotal_le : ∑ k ∈ R, (effInputs N C k).length + Rnot.card ≤ 2 * R.card := by
    have hsplit : ∑ k ∈ R, ((effInputs N C k).length + if (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.not then 1 else 0) ≤
        ∑ _k ∈ R, 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hgk : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hklt
      have hlen := effInputs_len N C hF k hklt
      rw [hgk]
      cases hop : C.gates[k].op <;> simp only [hop, isNot, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hlen ⊢ <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at hsplit
    simp only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] at hsplit
    exact hsplit
  have hdeg_pos : ∀ u ∈ W.erase C.output, 1 ≤ inDeg u := by
    intro u hu
    have hne : u ≠ C.output := (Finset.mem_erase.mp hu).1
    have huW : u ∈ W := (Finset.mem_erase.mp hu).2
    obtain ⟨k, hk, hkW, huk⟩ := subW_parent N C C.output u huW hne
    have hkR : k ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkW⟩
    exact le_trans (List.count_pos_iff.mpr huk)
      (Finset.single_le_sum (f := fun j => (effInputs N C j).count u) (fun _ _ => Nat.zero_le _) hkR)
  have houtW : C.output ∈ W := self_mem_subW N C C.output
  have herase_card : (W.erase C.output).card + 1 = W.card := by
    rw [Finset.card_erase_of_mem houtW]
    have := Finset.card_pos.mpr ⟨C.output, houtW⟩
    omega
  let Ur : Finset (Fin n) := Finset.univ.filter fun u : Fin n => u.val ∉ W
  let Uc : Finset (Fin m) := Finset.univ.filter fun v : Fin m => n + v.val ∉ W
  have hWin_card : (n - Ur.card) + (m - Uc.card) ≤ Win.card := by
    let Rw : Finset (Fin n) := Finset.univ.filter fun u : Fin n => u.val ∈ W
    let Cw : Finset (Fin m) := Finset.univ.filter fun v : Fin m => n + v.val ∈ W
    have hRsum : Rw.card + Ur.card = n := by
      simpa [Rw, Ur] using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun u : Fin n => u.val ∈ W)
    have hCsum : Cw.card + Uc.card = m := by
      simpa [Cw, Uc] using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun v : Fin m => n + v.val ∈ W)
    let Sr : Finset ℕ := Rw.image Fin.val
    let Sc : Finset ℕ := Cw.image (fun v : Fin m => n + v.val)
    have hdisjRC : Disjoint Sr Sc := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h2
      omega
    have hsubRC : Sr ∪ Sc ⊆ Win := by
      intro w hw
      rcases Finset.mem_union.mp hw with h1 | h2
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h1
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).2, by omega⟩
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2, by omega⟩
    have hSr : Sr.card = Rw.card := Finset.card_image_of_injective _ Fin.val_injective
    have hSc : Sc.card = Cw.card := Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
    have hle : Rw.card + Cw.card ≤ Win.card := by
      calc Rw.card + Cw.card = Sr.card + Sc.card := by rw [hSr, hSc]
        _ = (Sr ∪ Sc).card := (Finset.card_union_of_disjoint hdisjRC).symm
        _ ≤ Win.card := Finset.card_le_card hsubRC
    omega
  have hnonot : ∀ k, (hk : k < C.gates.length) → N + k ∈ W → C.gates[k].op ≠ GateOp.not := by
    intro k hk _ hnot
    have h := (hM _ (List.getElem_mem hk)).1
    simp [hnot] at h
  have hUr_le : Ur.card ≤ minR := by
    refine le_trans (Finset.card_le_card ?_) hminR
    intro u hu
    have huW : u.val ∉ W := (Finset.mem_filter.mp hu).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u' v hAuv => ?_⟩
    rw [← hRep u v] at hAuv; rw [← hRep u' v]
    apply mono_of_no_not N C hF hnonot _ _ (repInput_len u v) (repInput_len u' v) _ C.output houtW hAuv
    intro i hi hiW hx
    rw [repInput_getD u v i hi] at hx
    rw [repInput_getD u' v i hi]
    split_ifs at hx ⊢ with h1
    · have heq : (⟨i, h1⟩ : Fin n) = u := decide_eq_true_eq.mp hx
      exact absurd (congrArg Fin.val heq ▸ hiW) huW
    · exact hx
  have hUc_le : Uc.card ≤ minC := by
    refine le_trans (Finset.card_le_card ?_) hminC
    intro v hv
    have hvW : n + v.val ∉ W := (Finset.mem_filter.mp hv).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v' u hAuv => ?_⟩
    rw [← hRep u v] at hAuv; rw [← hRep u v']
    apply mono_of_no_not N C hF hnonot _ _ (repInput_len u v) (repInput_len u v') _ C.output houtW hAuv
    intro i hi hiW hx
    rw [repInput_getD u v i hi] at hx
    rw [repInput_getD u v' i hi]
    split_ifs at hx ⊢ with h1
    · exact hx
    · have heq : (⟨i - n, by omega⟩ : Fin m) = v := decide_eq_true_eq.mp hx
      have hi_eq : i = n + v.val := by have := congrArg Fin.val heq; dsimp at this; omega
      exact absurd (hi_eq ▸ hiW) hvW
  have hsum_ge : W.card - 1 ≤ ∑ u ∈ W, inDeg u := by
    calc W.card - 1 = (W.erase C.output).card := by omega
      _ = ∑ _u ∈ W.erase C.output, 1 := by simp
      _ ≤ ∑ u ∈ W.erase C.output, inDeg u := Finset.sum_le_sum hdeg_pos
      _ ≤ ∑ u ∈ W, inDeg u := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  omega

theorem three_levels : ∀ n k a b : ℕ, k = 3 → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) s → 2 * n + k - 4 - a - b ≤ s := by
  intro n k a b hk t ht _ _ ha hb s hs
  let A : Fin n → Fin n → Bool := fun u v => decide (v.val < t u)
  have hr : (Finset.univ.filter fun u : Fin n => ∀ u' v, A u v = true → A u' v = true).card ≤ a := by
    rw [← ha]
    apply Finset.card_le_card
    intro u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u' => ?_⟩
    have h := (Finset.mem_filter.mp hu).2
    by_contra! hlt
    let v : Fin n := ⟨t u', lt_of_lt_of_le hlt (ht u).2⟩
    have hbad := h u' v (by simpa [A,v] using hlt)
    simp [A,v] at hbad
  have hc : (Finset.univ.filter fun v : Fin n => ∀ v' u, A u v = true → A u v' = true).card ≤ b := by
    rw [← hb]
    apply Finset.card_le_card
    intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v' => Finset.card_le_card ?_⟩
    intro u hu
    have h := (Finset.mem_filter.mp hv).2 v' u
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [A] using h (by simpa [A] using (Finset.mem_filter.mp hu).2)⟩
  have h := mono_bound A hr hc hs
  omega

end PEqualNP.Outside.L_meta_21908_aux

theorem PEqualNP.Outside.L_meta_21908 : ∀ n k a b : ℕ, k = 3 → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) s → 2 * n + k - 4 - a - b ≤ s :=
  PEqualNP.Outside.L_meta_21908_aux.three_levels
