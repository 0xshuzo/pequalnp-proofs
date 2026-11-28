import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_18769.Column
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

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this


theorem app_mono (A A' B B' : List Bool) (hA : A.length = A'.length)
    (ha : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hb : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hA ▸ hi)]; exact ha i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hA]
    exact hb _


def val (C : Circuit) (n : ℕ) (l : Fin n) (Z : Finset (Fin n)) (w : ℕ) : Bool :=
  (C.wires (PEqualNP.GenericRejection.incidenceInput Z ({l} : Finset (Fin n)))).getD w false

theorem inc_len (n : ℕ) (Z Y : Finset (Fin n)) :
    (PEqualNP.GenericRejection.incidenceInput Z Y).length = n + n := by
  simp [PEqualNP.GenericRejection.incidenceInput]

theorem val_mono (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (Z Z' : Finset (Fin n)) (h : Z ⊆ Z') (w : ℕ) :
    val C n l Z w = true → val C n l Z' w = true := by
  obtain ⟨hao, _, h2⟩ := hC
  have hleg : ∀ g' ∈ C.gates, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => ⟨hao g' hg', le_of_eq (h2 g' hg')⟩
  refine mono2 C.gates hleg _ _ (by rw [inc_len, inc_len]) ?_ w
  refine app_mono _ _ _ _ (by simp) ?_ (fun _ => id)
  exact ofFn_mono n _ _ (fun v hv => by simp only [decide_eq_true_eq] at hv ⊢; exact h hv)

theorem val_input (C : Circuit) (n : ℕ) (l : Fin n) (Z Z' : Finset (Fin n)) (w : ℕ)
    (hw : w < n + n) (hn : n ≤ w) : val C n l Z w = val C n l Z' w := by
  unfold val
  show (wf C.gates _).getD w false = (wf C.gates _).getD w false
  rw [wf_keep _ _ _ (by rw [inc_len]; exact hw), wf_keep _ _ _ (by rw [inc_len]; exact hw)]
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
  simp

theorem val_point (C : Circuit) (n : ℕ) (l : Fin n) (p : Fin n) (w : ℕ)
    (hw : w < n) : val C n l {p} w = true → p.val = w := by
  unfold val
  show (wf C.gates _).getD w false = true → _
  rw [wf_keep _ _ _ (by rw [inc_len]; omega)]
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw]
  intro h
  simp at h
  rw [← h]

theorem val_gate (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (k : ℕ) (hk : k < C.size) :
    ∃ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] ∧
      a < n + n + k ∧ b < n + n + k ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or) ∧
      ∀ Z, val C n l Z (n + n + k) =
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op.eval [val C n l Z a, val C n l Z b] := by
  obtain ⟨hao, hrb, h2⟩ := hC
  have hk' : k < C.gates.length := hk
  have hG : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk']
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk'
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (h2 _ hmem)
  have hlt : ∀ i ∈ [a, b], i < n + n + k := by
    intro i hi
    have := hrb k hk' i
    rw [hG, hin] at this
    exact this hi
  refine ⟨a, b, by rw [hG, hin], hlt a (by simp), hlt b (by simp), by rw [hG]; exact hao _ hmem, ?_⟩
  intro Z
  have hlen := inc_len n Z ({l} : Finset (Fin n))
  have g1 := gate_val C.gates (PEqualNP.GenericRejection.incidenceInput Z ({l} : Finset (Fin n))) k hk'
  rw [hlen, hin] at g1
  unfold val
  show (wf C.gates _).getD (n + n + k) false = _
  rw [g1, hG]
  show _ = C.gates[k].op.eval [(wf C.gates _).getD a false, (wf C.gates _).getD b false]
  rw [wire_take C.gates _ k a (by rw [hlen]; exact hlt a (by simp)) (le_of_lt hk'),
    wire_take C.gates _ k b (by rw [hlen]; exact hlt b (by simp)) (le_of_lt hk')]
  simp

open Finset in
theorem colors {n} (f : Nat → Fin n × Fin n) (S : Finset Nat) :
    ∃ c : Fin n → Fin n, (∀ j∈S,c (f j).1=c (f j).2) ∧
      n≤S.card+(univ.image c).card := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨id,by simp,by simp⟩
  | @insert j S hj ih =>
    obtain ⟨c,ok,cnt⟩ := ih
    let a := c (f j).1
    let b := c (f j).2
    let up := fun z : Fin n => if z=a then b else z
    let d := up ∘ c
    refine ⟨d,?_,?_⟩
    · intro k hk
      rcases mem_insert.mp hk with rfl|hh
      · change up a=up b
        simp [up]
      · exact congrArg up (ok k hh)
    · have sub : univ.image c ⊆ insert a (univ.image d) := by
        intro t ht
        obtain ⟨u,_,rfl⟩ := mem_image.mp ht
        by_cases eq : c u=a
        · exact mem_insert.mpr (.inl eq)
        · exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_univ _,by simp [d,up,eq]⟩)
      have h := (card_le_card sub).trans (card_insert_le _ _)
      rw [card_insert_of_notMem hj]
      omega

open Finset in
theorem graph_count {n : ℕ} (S : Finset ℕ) (f : ℕ → Fin n × Fin n) (X : Finset (Fin n))
    (hX : ∀ c : Fin n → Fin n, (∀ j∈S,c (f j).1=c (f j).2) →
      ∀ u ∈ X, ∀ v ∈ X, c u=c v) : X.card≤S.card+1 := by
  classical
  rcases X.eq_empty_or_nonempty with rfl|⟨v,hv⟩
  · simp
  obtain ⟨c,ok,hc⟩ := colors f S
  have sub : univ.image c⊆insert (c v) ((univ\X).image c) := by
    intro t ht
    obtain ⟨u,_,rfl⟩ := mem_image.mp ht
    by_cases hu : u∈X
    · exact mem_insert.mpr (.inl (hX c ok u hu v hv))
    · exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_sdiff.mpr ⟨mem_univ _,hu⟩,rfl⟩)
  have hc' := (card_le_card sub).trans (card_insert_le _ _)
  have imgs : ((univ\X).image c).card≤(univ\X).card := card_image_le
  have add := card_sdiff_add_card_eq_card (subset_univ X)
  simp only [card_univ,Fintype.card_fin] at add
  omega

theorem reach (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (color : Fin n → Fin n) (Zb : Finset (Fin n))
    (hedge : ∀ k < C.size, ∀ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or →
      val C n l Zb (n + n + k) = false → ∀ u v : Fin n, u ≠ v →
      val C n l {u} a = true → val C n l {v} b = true →
      ∃ u' v', val C n l {u'} a = true ∧ val C n l {v'} b = true ∧ color u'=color v') :
    ∀ w, w < n + n + C.size → val C n l Zb w = false → ∀ u v : Fin n,
      val C n l {u} w = true → val C n l {v} w = true → color u=color v := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hgood u v hu hv
  by_cases h1 : w < n
  · have e1 := val_point C n l u w h1 hu
    have e2 := val_point C n l v w h1 hv
    have : u = v := Fin.ext (by omega)
    rw [this]
  by_cases h2 : w < n + n
  · rw [val_input C n l {u} Zb w h2 (by omega)] at hu
    rw [hu] at hgood
    exact absurd hgood (by simp)
  obtain ⟨k, rfl⟩ : ∃ k, w = n + n + k := ⟨w - (n + n), by omega⟩
  have hk : k < C.size := by omega
  obtain ⟨a, b, hin, ha, hb, hop, hval⟩ := val_gate C n l hC k hk
  rw [hval] at hgood hu hv
  rcases hop with hop | hop
  · rw [hop] at hgood hu hv
    simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true,
      Bool.and_eq_false_iff] at hgood hu hv
    rcases hgood with hg | hg
    · exact ih a ha (by omega) hg u v hu.1 hv.1
    · exact ih b hb (by omega) hg u v hu.2 hv.2
  · have hop' := hop
    rw [hop] at hgood hu hv
    simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true,
      Bool.or_eq_false_iff] at hgood hu hv
    have hgw : val C n l Zb (n + n + k) = false := by
      rw [hval, hop]; simp [GateOp.eval, hgood.1, hgood.2]
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact ih a ha (by omega) hgood.1 u v hu hv
    · by_cases huv : u = v
      · rw [huv]
      obtain ⟨u', v', hu', hv', hr⟩ := hedge k hk a b hin hop' hgw u v huv hu hv
      exact ((ih a ha (by omega) hgood.1 u u' hu hu').trans hr).trans
        (ih b hb (by omega) hgood.2 v' v hv' hv)
    · by_cases huv : v = u
      · rw [huv]
      obtain ⟨u', v', hu', hv', hr⟩ := hedge k hk a b hin hop' hgw v u huv hv hu
      exact (((ih a ha (by omega) hgood.1 v u' hv hu').trans hr).trans
        (ih b hb (by omega) hgood.2 v' u hv' hu)).symm
    · exact ih b hb (by omega) hgood.2 u v hu hv

end PEqualNP.Outside.L_meta_18769.Column

open PEqualNP.Outside.L_meta_18769.Column PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18769.Column : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  intro n C X l hC hout hacc hrej
  classical
  have hrej' : val C n l Xᶜ C.output = false := hrej
  have hacc' : ∀ p ∈ X, val C n l {p} C.output = true := hacc
  have hsub : ∀ w, val C n l Xᶜ w = false → ∀ p : Fin n, val C n l {p} w = true → p ∈ X := by
    intro w hw p hp
    by_contra hpX
    have := val_mono C n l hC {p} Xᶜ (by simpa using hpX) w hp
    rw [hw] at this
    exact absurd this (by simp)
  refine ⟨(Finset.range C.size).filter (fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true),
    ?_, ?_⟩
  · rcases X.eq_empty_or_nonempty with hX | ⟨p0, _⟩
    · rw [hX]; simp
    let A : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0
    let B : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0
    let f : ℕ → Fin n × Fin n := fun j =>
      if h : ∃ u v : Fin n, u ≠ v ∧ val C n l {u} (A j) = true ∧ val C n l {v} (B j) = true
      then (h.choose, h.choose_spec.choose) else (p0, p0)
    apply graph_count _ f X
    intro color glued u hu v hv
    refine reach C n l hC color Xᶜ ?_ C.output hout hrej' u v (hacc' u hu) (hacc' v hv)
    intro k hk a b hin hop hgood u v huv hua hvb
    have hAk : A k = a := by simp [A, hin]
    have hBk : B k = b := by simp [B, hin]
    have hex : ∃ u v : Fin n, u ≠ v ∧ val C n l {u} (A k) = true ∧ val C n l {v} (B k) = true :=
      ⟨u, v, huv, hAk ▸ hua, hBk ▸ hvb⟩
    obtain ⟨a', b', hin', _, _, _, hval⟩ := val_gate C n l hC k hk
    rw [hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    obtain ⟨rfl, rfl⟩ := hin'
    have hk9 : k ∈ (Finset.range C.size).filter (fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hgood, u, v, huv, ?_, ?_⟩
      · rw [hval, hop]; simp [GateOp.eval, hua]
      · rw [hval, hop]; simp [GateOp.eval, hvb]
    have hfk : f k = (hex.choose, hex.choose_spec.choose) := by
      simp only [f, hex, dite_true]
    obtain ⟨hne, h1, h2⟩ := hex.choose_spec.choose_spec
    refine ⟨hex.choose, hex.choose_spec.choose, hAk ▸ h1, hBk ▸ h2, ?_⟩
    simpa only [hfk] using glued k hk9
  · intro j hj
    obtain ⟨hjr, hop, hgood, p, q, hpq, hp, hq⟩ := Finset.mem_filter.mp hj
    refine ⟨Finset.mem_range.mp hjr, hop, ?_⟩
    show val C n l Xᶜ (n + n + j) = false ∧
      (∃ (x13 : Fin n) (x14 : Fin n), x13 ≠ x14 ∧ val C n l {x13} (n + n + j) = true ∧
        val C n l {x14} (n + n + j) = true) ∧
      ∀ (x13 : Fin n), val C n l {x13} (n + n + j) = true → x13 ∈ X
    exact ⟨hgood, ⟨p, q, hpq, hp, hq⟩, hsub _ hgood⟩



namespace PEqualNP.Outside.L_meta_18769.Column
open PEqualNP.CircuitLowerBounds Finset
theorem color_ports {n} (S : Finset Nat) (f : Nat → Fin n × Fin n) (X : Finset (Fin n))
    (ports : Finset Nat) (hit : Nat → Fin n → Prop)
    (coverage : ∀p∈X,∃w∈ports,hit w p)
    (agree : ∀c : Fin n → Fin n, (∀j∈S,c (f j).1=c (f j).2) →
      ∀w∈ports,∀u v,hit w u → hit w v → c u=c v) : X.card≤S.card+ports.card := by
  classical
  obtain ⟨c,hc,num⟩ := colors f S
  let pick (w : Nat) := if h : ∃u,hit w u then {c h.choose} else (∅ : Finset (Fin n))
  have one (w : Nat) : (pick w).card≤1 := by unfold pick;split <;>simp
  have sub : univ.image c ⊆ ((univ\X).image c) ∪ ports.biUnion pick := by
    intro z hz
    obtain ⟨u,_,rfl⟩ := mem_image.mp hz
    by_cases hh : u∈X
    · obtain ⟨w,hw,hu⟩ := coverage u hh
      have h : ∃v,hit w v := ⟨u,hu⟩
      apply mem_union_right
      apply mem_biUnion.mpr
      exact ⟨w,hw,by simpa only [pick,dif_pos h,mem_singleton] using agree c hc w hw u _ hu h.choose_spec⟩
    · exact mem_union_left _ (mem_image.mpr ⟨u,mem_sdiff.mpr ⟨mem_univ _,hh⟩,rfl⟩)
  have u := (card_le_card sub).trans (card_union_le _ _)
  have v : (ports.biUnion pick).card≤ports.card*1 := card_biUnion_le_card_mul _ _ _ (fun w _=>one w)
  have img : ((univ\X).image c).card≤(univ\X).card := card_image_le
  have diff := card_sdiff_add_card_eq_card (subset_univ X)
  simp only [card_univ,Fintype.card_fin] at diff
  omega

theorem multi (n : Nat) (C : Circuit) (X : Finset (Fin n)) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n+n) C)
    (ports : Finset Nat) (st : ∀w∈ports,w<n+n+C.size ∧ val C n l Xᶜ w=false)
    (coverage : ∀p∈X,∃w∈ports,val C n l {p} w=true) :
    ∃ T : Finset Nat,X.card≤T.card+ports.card ∧ ∀j∈T,j<C.size ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op=GateOp.or ∧
      val C n l Xᶜ (n+n+j)=false ∧
      (∃p q : Fin n,p≠q ∧ val C n l {p} (n+n+j)=true ∧ val C n l {q} (n+n+j)=true) ∧
      ∀p,val C n l {p} (n+n+j)=true → p∈X := by
  classical
  have hsub : ∀ w, val C n l Xᶜ w = false → ∀ p : Fin n, val C n l {p} w = true → p ∈ X := by
    intro w hw p hp
    by_contra hpX
    have := val_mono C n l hC {p} Xᶜ (by simpa using hpX) w hp
    rw [hw] at this
    exact absurd this (by simp)
  refine ⟨(Finset.range C.size).filter (fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true),
    ?_, ?_⟩
  · rcases X.eq_empty_or_nonempty with hX | ⟨p0, _⟩
    · rw [hX]; simp
    let A : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0
    let B : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0
    let f : ℕ → Fin n × Fin n := fun j =>
      if h : ∃ u v : Fin n, u ≠ v ∧ val C n l {u} (A j) = true ∧ val C n l {v} (B j) = true
      then (h.choose, h.choose_spec.choose) else (p0, p0)
    apply color_ports _ f X ports (fun w u=>val C n l {u} w=true) coverage
    intro color glued w hw u v hu hv
    refine reach C n l hC color Xᶜ ?_ w (st w hw).1 (st w hw).2 u v hu hv
    intro k hk a b hin hop hgood u v huv hua hvb
    have hAk : A k = a := by simp [A, hin]
    have hBk : B k = b := by simp [B, hin]
    have hex : ∃ u v : Fin n, u ≠ v ∧ val C n l {u} (A k) = true ∧ val C n l {v} (B k) = true :=
      ⟨u, v, huv, hAk ▸ hua, hBk ▸ hvb⟩
    obtain ⟨a', b', hin', _, _, _, hval⟩ := val_gate C n l hC k hk
    rw [hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    obtain ⟨rfl, rfl⟩ := hin'
    have hk9 : k ∈ (Finset.range C.size).filter (fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hgood, u, v, huv, ?_, ?_⟩
      · rw [hval, hop]; simp [GateOp.eval, hua]
      · rw [hval, hop]; simp [GateOp.eval, hvb]
    have hfk : f k = (hex.choose, hex.choose_spec.choose) := by
      simp only [f, hex, dite_true]
    obtain ⟨hne, h1, h2⟩ := hex.choose_spec.choose_spec
    refine ⟨hex.choose, hex.choose_spec.choose, hAk ▸ h1, hBk ▸ h2, ?_⟩
    simpa only [hfk] using glued k hk9
  · intro j hj
    obtain ⟨hjr, hop, hgood, p, q, hpq, hp, hq⟩ := Finset.mem_filter.mp hj
    refine ⟨Finset.mem_range.mp hjr, hop, ?_⟩
    show val C n l Xᶜ (n + n + j) = false ∧
      (∃ (x13 : Fin n) (x14 : Fin n), x13 ≠ x14 ∧ val C n l {x13} (n + n + j) = true ∧
        val C n l {x14} (n + n + j) = true) ∧
      ∀ (x13 : Fin n), val C n l {x13} (n + n + j) = true → x13 ∈ X
    exact ⟨hgood, ⟨p, q, hpq, hp, hq⟩, hsub _ hgood⟩


end PEqualNP.Outside.L_meta_18769.Column
namespace PEqualNP.Outside.L_meta_18769.Bank
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.GenericRejection
open Finset
abbrev I := Fin 12
abbrev L := Fin 13
def idx (p : I) : L := ⟨p.val+1,by omega⟩
def nbr (p : I) : Finset L := univ.filter (fun l => idx p=l ∨ idx p=l+1 ∨ idx p=l+3 ∨ idx p=l+9)
theorem deg : ∀ p,(nbr p).card=4 := by decide +kernel
theorem loyal : ∀ p q : I,∀ l k : L, l≠k → l∈nbr p → l∈nbr q → k∈nbr p → k∈nbr q → p=q := by decide +kernel
def wave (gs : List Gate) (w : Nat) (S : Finset L) := (Column.wf gs (incidenceInput S ({0} : Finset L))).getD w false
def Marks (gs : List Gate) (out : I → Nat) := ∀ p,
    out p<26+gs.length ∧ (∀ l∈nbr p,wave gs (out p) {l}=true) ∧ wave gs (out p) (nbr p)ᶜ=false
open Classical in
theorem required (gs : List Gate) (ao : IsAO2 26 ⟨gs,0⟩) (out : I → Nat) (mark : Marks gs out) :
    36≤((range gs.length).filter (fun j => (gateAt ⟨gs,0⟩ j).op=GateOp.or)).card := by
  classical
  let Good (p : I) (j : Nat) := j<gs.length ∧ (gateAt ⟨gs,0⟩ j).op=GateOp.or ∧
    (∃ l k : L,l≠k ∧ wave gs (26+j) {l}=true ∧ wave gs (26+j) {k}=true) ∧
    ∀ l : L,wave gs (26+j) {l}=true → l∈nbr p
  have rows (p : I) : ∃ T : Finset Nat, 3≤T.card ∧ ∀ j∈T,Good p j := by
    let C : Circuit := ⟨gs,out p⟩
    have ca : IsAO2 26 C := ao
    obtain ⟨T,size,ok⟩ := PEqualNP.Outside.L_meta_18769.Column 13 C (nbr p) 0 ca
      (mark p).1 (mark p).2.1 (mark p).2.2
    refine ⟨T,by rw [deg] at size; omega,?_⟩
    intro j hj
    obtain ⟨lt,op,_,pair,sub⟩ := ok j hj
    exact ⟨lt,op,pair,sub⟩
  choose T count valid using rows
  have apart : ∀ p : I,p∈univ → ∀ q : I,q∈univ → p≠q → Disjoint (T p) (T q) := by
    intro p _ q _ ne
    apply disjoint_left.mpr
    intro j hp hq
    obtain ⟨_,_,⟨l,k,lk,hl,hk⟩,lp⟩ := valid p j hp
    have lq := (valid q j hq).2.2.2
    exact ne (loyal p q l k lk (lp l hl) (lq l hl) (lp k hk) (lq k hk))
  have big : (∑ p : I,3) ≤ ∑ p : I,(T p).card := sum_le_sum (fun p _ => count p)
  have incl : (univ.biUnion T) ⊆ ((range gs.length).filter (fun j => (gateAt ⟨gs,0⟩ j).op=GateOp.or)) := by
    intro j hj
    obtain ⟨p,_,mem⟩ := mem_biUnion.mp hj
    exact mem_filter.mpr ⟨mem_range.mpr (valid p j mem).1,(valid p j mem).2.1⟩
  have lim := card_le_card incl
  rw [card_biUnion (fun p hp q hq ne => apart p hp q hq ne)] at lim
  simpa using big.trans lim
open Classical in
theorem priced_ports (gs : List Gate) (ao : IsAO2 26 ⟨gs,0⟩) (ports : I → Finset Nat)
    (safe : ∀p,∀w∈ports p,w<26+gs.length ∧ wave gs w (nbr p)ᶜ=false)
    (cover : ∀p,∀l∈nbr p,∃w∈ports p,wave gs w {l}=true) :
    48≤(∑ p : I,(ports p).card)+((range gs.length).filter (fun j => (gateAt ⟨gs,0⟩ j).op=GateOp.or)).card := by
  classical
  let Good (p : I) (j : Nat) := j<gs.length ∧ (gateAt ⟨gs,0⟩ j).op=GateOp.or ∧
    (∃ l k : L,l≠k ∧ wave gs (26+j) {l}=true ∧ wave gs (26+j) {k}=true) ∧
    ∀ l : L,wave gs (26+j) {l}=true → l∈nbr p
  have rows (p : I) : ∃ T : Finset Nat, 4≤T.card+(ports p).card ∧ ∀ j∈T,Good p j := by
    let C : Circuit := ⟨gs,0⟩
    obtain ⟨T,size,ok⟩ := Column.multi 13 C (nbr p) 0 ao (ports p) (safe p) (cover p)
    refine ⟨T,by simpa only [deg] using size,?_⟩
    intro j hj
    obtain ⟨lt,op,_,pair,sub⟩ := ok j hj
    exact ⟨lt,op,pair,sub⟩
  choose T count valid using rows
  have apart : ∀ p : I,p∈univ → ∀ q : I,q∈univ → p≠q → Disjoint (T p) (T q) := by
    intro p _ q _ ne
    apply disjoint_left.mpr
    intro j hp hq
    obtain ⟨_,_,⟨l,k,lk,hl,hk⟩,lp⟩ := valid p j hp
    have lq := (valid q j hq).2.2.2
    exact ne (loyal p q l k lk (lp l hl) (lq l hl) (lp k hk) (lq k hk))
  have big : (∑ p : I,4) ≤ ∑ p : I,((T p).card+(ports p).card) := sum_le_sum (fun p _ => count p)
  have incl : (univ.biUnion T) ⊆ ((range gs.length).filter (fun j => (gateAt ⟨gs,0⟩ j).op=GateOp.or)) := by
    intro j hj
    obtain ⟨p,_,mem⟩ := mem_biUnion.mp hj
    exact mem_filter.mpr ⟨mem_range.mpr (valid p j mem).1,(valid p j mem).2.1⟩
  have lim := card_le_card incl
  rw [card_biUnion (fun p hp q hq ne => apart p hp q hq ne)] at lim
  rw [sum_add_distrib] at big
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at big
  omega
end PEqualNP.Outside.L_meta_18769.Bank
namespace PEqualNP.Outside.L_meta_18769.Filters
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open Bank Finset
inductive Tree
  | point (p : I)
  | join (a b : Tree)
  | keep (w : ℕ) (a : Tree)
namespace Tree
def paths : Tree → List (I × Finset ℕ)
  | .point p => [(p,∅)]
  | .join a b => a.paths++b.paths
  | .keep w a => a.paths.map (fun v => (v.1,insert w v.2))
def eval (read : ℕ → Bool) (P : Finset I) : Tree → Bool
  | .point p => decide (p∈P)
  | .join a b => eval read P a || eval read P b
  | .keep w a => read w && eval read P a
def used : Tree → Finset Nat
  | .point _ => ∅
  | .join a b => a.used∪b.used
  | .keep w a => insert w a.used
def guards : Tree → Nat
  | .point _ => 0
  | .join a b => a.guards+b.guards
  | .keep _ a => a.guards+1
def cost : Tree → Nat
  | .point _ => 0
  | .join a b => a.cost+b.cost+1
  | .keep _ a => a.cost+1
theorem small_used (t : Tree) : t.used.card≤t.guards := by
  induction t with
  | point _ => simp [used,guards]
  | join a b h k => exact (card_union_le _ _).trans (Nat.add_le_add h k)
  | keep w a h => exact (card_insert_le _ _).trans (Nat.add_le_add_right h 1)
theorem count (t : Tree) : t.paths.length+t.guards=t.cost+1 := by
  induction t with
  | point _ => rfl
  | join a b h k => simp only [paths,List.length_append,guards,cost];omega
  | keep w a h => simp only [paths,List.length_map,guards,cost];omega
theorem paid {t : Tree} {v : I × Finset ℕ} (mem : v∈t.paths) : v.2⊆t.used := by
  induction t generalizing v with
  | point p => simp only [paths,List.mem_singleton] at mem;subst v;exact empty_subset _
  | join a b h k =>
    rcases List.mem_append.mp mem with ha|hb
    · exact (h ha).trans subset_union_left
    · exact (k hb).trans subset_union_right
  | keep w a h =>
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp mem
    exact insert_subset_insert (h hv)
theorem explain (r : ℕ → Bool) (P : Finset I) (t : Tree) : eval r P t=true ↔
    ∃v∈t.paths,v.1∈P ∧ ∀w∈v.2,r w=true := by
  induction t with
  | point p => simp [eval,paths]
  | join a b h k =>
    simp only [eval,Bool.or_eq_true,paths,List.mem_append,h,k]
    constructor
    · rintro (⟨v,m,q,n⟩|⟨v,m,q,n⟩)
      · exact ⟨v,.inl m,q,n⟩
      · exact ⟨v,.inr m,q,n⟩
    · rintro ⟨v,m,q,n⟩
      exact m.elim (fun z=>.inl ⟨v,z,q,n⟩) (fun z=>.inr ⟨v,z,q,n⟩)
  | keep w a h =>
    simp only [eval,Bool.and_eq_true,paths,h]
    constructor
    · rintro ⟨rw',v,m,q,n⟩
      exact ⟨_,List.mem_map.mpr ⟨v,m,rfl⟩,q,fun i hi=>(mem_insert.mp hi).elim (fun eq=>eq ▸ rw') (n _)⟩
    · rintro ⟨v,m,q,n⟩
      obtain ⟨o,om,rfl⟩ := List.mem_map.mp m
      exact ⟨n _ (mem_insert_self _ _),o,om,q,fun i hi=>n i (mem_insert_of_mem hi)⟩
end Tree
def Flag (P : Finset I) (Z : Finset L) := ∃p∈P,∃l∈Z,l∈nbr p

theorem price (gs : List Gate) (ao : IsAO2 26 ⟨gs,0⟩) (t : Tree)
    (good : ∀ w∈t.used,w<26+gs.length)
    (ok : ∀ P Z,Tree.eval (fun w=>wave gs w Z) P t=true ↔ Flag P Z) :
    59≤gs.length+t.cost := by
  classical
  let K := Fin t.paths.length
  let label (i : K) := (t.paths.get i).1
  let tests (i : K) := (t.paths.get i).2
  have mem (i : K) : t.paths.get i∈t.paths := List.get_mem _ _
  have offtest (i : K) : ∃w∈tests i,wave gs w (nbr (label i))ᶜ=false := by
    by_contra! no
    have on := (t.explain (fun w=>wave gs w (nbr (label i))ᶜ) {label i}).mpr
      ⟨_,mem i,mem_singleton_self _,fun w hw=>by simpa using no w hw⟩
    obtain ⟨p,hp,l,hl,hh⟩ := (ok _ _).mp on
    exact (mem_compl.mp hl) (mem_singleton.mp hp ▸ hh)
  choose f fm ff using offtest
  let fiber (p : I) := univ.filter (fun i : K=>label i=p)
  let ports (p : I) := (fiber p).image f
  have safe (p) (w) (hw : w∈ports p) : w<26+gs.length ∧ wave gs w (nbr p)ᶜ=false := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hw
    exact ⟨good _ (Tree.paid (mem i) (fm i)),(mem_filter.mp hi).2 ▸ ff i⟩
  have cover (p) (l) (hl : l∈nbr p) : ∃w∈ports p,wave gs w {l}=true := by
    have on := (ok {p} {l}).mpr ⟨p,mem_singleton_self _,l,mem_singleton_self _,hl⟩
    obtain ⟨v,hv,hp,hs⟩ := (t.explain _ _).mp on
    obtain ⟨i,e⟩ := List.mem_iff_get.mp hv
    have lp : label i=p := by simpa only [label,e] using mem_singleton.mp hp
    have vmem : f i∈v.2 := by simpa only [tests,e] using fm i
    exact ⟨f i,mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,lp⟩,rfl⟩,hs _ vmem⟩
  have rent := Bank.priced_ports gs ao ports safe cover
  have disj : ∀p : I,p∈univ → ∀q : I,q∈univ → p≠q → Disjoint (fiber p) (fiber q) := by
    intro p _ q _ ne
    exact disjoint_left.mpr (fun i a b=>ne ((mem_filter.mp a).2.symm.trans (mem_filter.mp b).2))
  have lim : (∑ p : I,(ports p).card)≤t.paths.length := by
    have a : (∑ p : I,(ports p).card)≤ ∑p : I,(fiber p).card := sum_le_sum (fun _ _=>card_image_le)
    rw [←card_biUnion disj] at a
    exact a.trans (by simpa only [Fintype.card_fin] using (card_le_univ (univ.biUnion fiber)))
  have ore := card_le_card (filter_subset (fun j=>(PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs,0⟩ j).op=GateOp.or) (range gs.length))
  simp only [card_range] at ore
  have hit (p : I) : idx p∈nbr p := mem_filter.mpr ⟨mem_univ _,Or.inl rfl⟩
  choose r rm rh using fun p=>cover p (idx p) (hit p)
  have ri : Function.Injective r := by
    intro p q er
    by_contra ne
    have support (a : I) {l : L} (hl : wave gs (r a) {l}=true) : l∈nbr a := by
      by_contra nil
      have pos := Column.val_mono (⟨gs,0⟩ : Circuit) 13 0 ao {l} (nbr a)ᶜ
        (singleton_subset_iff.mpr (mem_compl.mpr nil)) (r a) hl
      exact Bool.noConfusion (pos.symm.trans (safe _ _ (rm a)).2)
    have apart : idx p≠idx q := by intro eq;apply ne;apply Fin.ext;have z:=congrArg Fin.val eq;simp [idx] at z;omega
    exact ne (loyal p q _ _ apart (hit _) (support q (er ▸ rh p)) (support p (er.symm ▸ rh q)) (hit _))
  have occ (p : I) : r p∈t.used := by
    obtain ⟨i,_,e⟩ := mem_image.mp (rm p)
    exact e ▸ Tree.paid (mem i) (fm i)
  have lower : 12≤t.used.card := by simpa using card_le_card_of_injOn (s:=(univ : Finset I)) (t:=t.used) r (fun p _=>occ p) ri.injOn
  have := t.small_used
  have := t.count
  omega
end PEqualNP.Outside.L_meta_18769.Filters
