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
end PEqualNP.Outside.L_meta_18769.Bank

namespace PEqualNP.Outside.L_meta_18769.Suffix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs++[g]) w=step (run gs w) g := by simp [run,List.foldl_append]
theorem length_run (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [step,ih]; omega
theorem snoc_other (w : List Bool) (v : Bool) (q : Nat) (ne : q≠w.length) :
    (w++[v]).getD q false=w.getD q false := by
  by_cases h : q<w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem snoc_last (w : List Bool) (v : Bool) : (w++[v]).getD w.length false=v := by simp


def sep (A B : List Bool) (w : Nat) := A.getD w false=true ∧ B.getD w false=false
def separates {J : Type} (X Y : J→List Bool) (S : Finset Nat) := ∀ i,∃ w∈S,sep (X i) (Y i) w

theorem gate_step (g : Gate) (h : g.op=.and ∨ g.op=.or) (A B : List Bool)
    (ha : g.op.eval (g.inputs.map fun i => A.getD i false)=true)
    (hb : g.op.eval (g.inputs.map fun i => B.getD i false)=false) :
    ∃ t∈g.inputs,sep A B t := by
  by_contra! bad
  have lift (t : Nat) (ht : t∈g.inputs) (on : A.getD t false=true) : B.getD t false=true := by
    cases e : B.getD t false with
    | true => rfl
    | false => exact (bad t ht ⟨on,e⟩).elim
  rcases h with h|h
  · simp only [h,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at ha
    have all : (g.inputs.map fun i => B.getD i false).all id=true := List.all_eq_true.mpr (by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
      exact lift i hi (ha i hi))
    rw [h] at hb
    change (g.inputs.map fun i=>B.getD i false).all id=false at hb
    exact Bool.noConfusion (all.symm.trans hb)
  · simp only [h,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at ha
    obtain ⟨i,hi,v⟩ := ha
    have any : (g.inputs.map fun j => B.getD j false).any id=true := List.any_eq_true.mpr
      ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,lift i hi v⟩
    rw [h] at hb
    change (g.inputs.map fun i=>B.getD i false).any id=false at hb
    exact Bool.noConfusion (any.symm.trans hb)

theorem sources {J : Type} (m : Nat) (X Y : J→List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m) (gs : List Gate)
    (legal : ∀g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (S : Finset Nat) (h : separates (fun i=>run gs (X i)) (fun i=>run gs (Y i)) S) :
    ∃ T : Finset Nat,separates X Y T ∧ T.card≤S.card+gs.length := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,h,by simp⟩
  | append_singleton gs g ih =>
    let last := m+gs.length
    let V := fun i => run gs (X i)
    let W := fun i => run gs (Y i)
    have vl (i) : (V i).length=last := by rw [show V i=run gs (X i) by rfl,length_run,(lens i).1]
    have wl (i) : (W i).length=last := by rw [show W i=run gs (Y i) by rfl,length_run,(lens i).2]
    have stay (i : J) (w : Nat) (ne : w≠last) :
        sep (run (gs++[g]) (X i)) (run (gs++[g]) (Y i)) w → sep (V i) (W i) w := by
      rw [run_snoc,run_snoc]
      change ((V i++[_]).getD w false=true ∧ (W i++[_]).getD w false=false) → _
      rw [snoc_other _ _ w (by rwa [vl]),snoc_other _ _ w (by rwa [wl])]
      exact id
    have gl := legal g (by simp)
    have old := fun a (ha : a∈gs) => legal a (by simp [ha])
    by_cases mem : last∈S
    · let R := S.erase last ∪ g.inputs.toFinset
      have ok : separates V W R := by
        intro i
        obtain ⟨w,ws,diff⟩ := h i
        by_cases eq : w=last
        · subst w
          change sep (run (gs++[g]) (X i)) (run (gs++[g]) (Y i)) last at diff
          rw [run_snoc,run_snoc] at diff
          change (V i++[g.op.eval _]).getD last false=true ∧ (W i++[g.op.eval _]).getD last false=false at diff
          rw [←vl i,snoc_last,vl i,←wl i,snoc_last] at diff
          obtain ⟨t,ht,sep⟩ := gate_step g gl.1 (V i) (W i) diff.1 diff.2
          exact ⟨t,Finset.mem_union_right _ (List.mem_toFinset.mpr ht),sep⟩
        · exact ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ws⟩),stay i w eq diff⟩
      obtain ⟨T,ht,sz⟩ := ih old R ok
      have u : R.card ≤ (S.erase last).card + g.inputs.toFinset.card := Finset.card_union_le _ _
      have e := Finset.card_erase_add_one mem
      have k := List.toFinset_card_le g.inputs
      refine ⟨T,ht,?_⟩
      simp only [List.length_append,List.length_singleton]
      omega
    · have ok : separates V W S := by
        intro i
        obtain ⟨w,ws,diff⟩ := h i
        exact ⟨w,ws,stay i w (fun eq => mem (eq ▸ ws)) diff⟩
      obtain ⟨T,ht,sz⟩ := ih old S ok
      exact ⟨T,ht,by simp; omega⟩

open Finset
abbrev I := Fin 12
abbrev L := Fin 13
def idx (p : I) : L := ⟨p.val+1,by omega⟩
def nbr (p : I) : Finset L := univ.filter (fun l => idx p=l ∨ idx p=l+1 ∨ idx p=l+3 ∨ idx p=l+9)
theorem deg : ∀ p,(nbr p).card=4 := by decide +kernel
theorem loyal : ∀ p q : I,∀ l k : L, l≠k → l∈nbr p → l∈nbr q → k∈nbr p → k∈nbr q → p=q := by decide +kernel

theorem crosses : ∀ p q : I,p≠q → idx p∉nbr q ∨ idx q∉nbr p := by decide +kernel
abbrev Index := I × Bool
def posP (i : Index) : Finset I := {i.1}
def negP (i : Index) : Finset I := if i.2 then {i.1} else ∅
def posL (i : Index) : Finset L := {idx i.1}
def negL (i : Index) : Finset L := if i.2 then (nbr i.1)ᶜ else {idx i.1}
def initial (X Y : Index→List Bool) := ∀w,
  (∃p : I,∀i, (X i).getD w false=decide (p∈posP i) ∧ (Y i).getD w false=decide (p∈negP i)) ∨
  (∃ f : Finset L → Bool,(∀ a b,a⊆b → f a=true → f b=true) ∧
     ∀ i,(X i).getD w false=f (posL i) ∧ (Y i).getD w false=f (negL i))
theorem exclusive {X Y w} (bank : initial X Y) (i j : Index)
    (hi : sep (X i) (Y i) w) (hj : sep (X j) (Y j) w) : i=j := by
  rcases i with ⟨i,b⟩
  rcases j with ⟨j,c⟩
  rcases bank w with ⟨p,spec⟩ | ⟨f,mono,spec⟩
  · rw [sep,(spec _).1,(spec _).2] at hi hj
    cases b <;> cases c <;> simp_all [posP,negP]
  · rw [sep,(spec _).1,(spec _).2] at hi hj
    cases b <;> cases c <;> simp only [posL,negL,Bool.false_eq_true,if_false,if_true] at hi hj
    all_goals try grind
    by_contra ne
    have ij : i≠j := fun e => ne (congrArg (fun p : I => (p,true)) e)
    rcases crosses i j ij with m|m
    · have a := mono _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr m)) hi.1
      exact Bool.noConfusion (a.symm.trans hj.2)
    · have a := mono _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr m)) hj.1
      exact Bool.noConfusion (a.symm.trans hi.2)
theorem decoder (m : Nat) (X Y : Index→List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m) (bank : initial X Y)
    (gs : List Gate) (legal : ∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (o : Nat) (correct : ∀i,sep (run gs (X i)) (run gs (Y i)) o) : 23≤gs.length := by
  classical
  obtain ⟨T,ht,lim⟩ := sources m X Y lens gs legal {o} (fun i=>⟨o,mem_singleton_self _,correct i⟩)
  choose f hf hv using ht
  have inj : Set.InjOn f (univ : Finset Index) := fun i _ j _ eq =>
    exclusive bank i j (eq ▸ hv i) (hv j)
  have card := card_le_card_of_injOn f (fun i _ => hf i) inj
  simp only [card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at card
  simp only [card_singleton] at lim
  omega
end PEqualNP.Outside.L_meta_18769.Suffix

namespace PEqualNP.Outside.L_meta_18769.Rigid
open Finset
abbrev I := Fin 12
abbrev L := Fin 13
def idx (p : I) : L := ⟨p.val+1,by omega⟩
def nbr (p : I) : Finset L := univ.filter (fun l => idx p=l ∨ idx p=l+1 ∨ idx p=l+3 ∨ idx p=l+9)
theorem deg : ∀ p,(nbr p).card=4 := by decide +kernel
theorem loyal : ∀ p q : I,∀ l k : L, l≠k → l∈nbr p → l∈nbr q → k∈nbr p → k∈nbr q → p=q := by decide +kernel
def matching (l : L) (p : I) : L := (([[11, 12, 2, 1, 4, 10, 6, 5, 9, 7, 8, 3],[11, 2, 7, 4, 9, 5, 6, 12, 0, 10, 8, 3],[5, 12, 0, 1, 4, 6, 11, 8, 9, 7, 10, 3],[11, 12, 0, 1, 4, 10, 6, 5, 8, 7, 2, 9],[11, 2, 0, 8, 9, 5, 7, 12, 6, 1, 10, 3],[11, 12, 0, 1, 2, 6, 4, 7, 9, 10, 8, 3],[0, 12, 2, 4, 9, 5, 11, 7, 8, 1, 10, 3],[11, 12, 0, 1, 2, 10, 4, 5, 6, 9, 8, 3],[0, 12, 7, 1, 2, 10, 4, 5, 6, 9, 11, 3],[11, 12, 0, 1, 2, 10, 4, 5, 6, 7, 8, 3],[11, 12, 0, 1, 2, 5, 4, 7, 6, 9, 8, 3],[5, 12, 0, 1, 2, 10, 4, 7, 6, 9, 8, 3],[0, 2, 7, 1, 4, 10, 11, 5, 6, 9, 8, 3]] : List (List L)).getD l.val []).getD p.val 0

theorem avoids : ∀ l : L,(∀ p : I,matching l p∈nbr p ∧ matching l p≠l) ∧ Function.Injective (matching l) := by
  have facts : ∀ l : L,(∀ p : I,matching l p∈nbr p ∧ matching l p≠l) ∧
      (∀ p q : I,matching l p=matching l q → p=q) := by decide +kernel
  exact fun l => ⟨(facts l).1,fun _ _ => (facts l).2 _ _⟩
theorem cardinal12 {α : Type} [Fintype α] (A : α → Finset I) (B : α → Finset L)
    (valid : ∀a,∀p∈A a,∀l∈B a,l∈nbr p)
    (cover : ∀p,∀l∈nbr p,∃a,p∈A a ∧ l∈B a) :
    12≤Fintype.card α := by
  classical
  choose f hp hl using fun p => cover p (matching 0 p) ((avoids 0).1 p).1
  have inj : Function.Injective f := by
    intro p q eq
    by_contra ne
    have d : matching 0 p ≠ matching 0 q := fun h=>ne ((avoids 0).2 h)
    have pq : p∈A (f q) := eq ▸ hp p
    have lp : matching 0 p∈B (f q) := eq ▸ hl p
    exact ne (loyal p q _ _ d (valid _ p pq _ lp) (valid _ q (hp q) _ lp)
        (valid _ p pq _ (hl q)) (valid _ q (hp q) _ (hl q)))
  simpa using Fintype.card_le_of_injective f inj

theorem rigid {α : Type} [Fintype α] (A : α → Finset I) (B : α → Finset L)
    (valid : ∀a,∀p∈A a,∀l∈B a,l∈nbr p)
    (cover : ∀p,∀l∈nbr p,∃a,p∈A a ∧ l∈B a)
    (small : Fintype.card α≤12) :
    ∃ f : I → α,Function.Bijective f ∧ ∀p,A (f p)={p} ∧ B (f p)=nbr p := by
  classical
  have card : Fintype.card α=12 := le_antisymm small (cardinal12 A B valid cover)
  have hits (l : L) (a : α) : ∃ k∈B a,k≠l := by
    choose f hp hl using fun p => cover p (matching l p) ((avoids l).1 p).1
    have inj : Function.Injective f := by
      intro p q eq
      by_contra ne
      have d : matching l p ≠ matching l q := fun h=>ne ((avoids l).2 h)
      have pq : p∈A (f q) := eq ▸ hp p
      have lp : matching l p∈B (f q) := eq ▸ hl p
      exact ne (loyal p q _ _ d (valid _ p pq _ lp) (valid _ q (hp q) _ lp)
          (valid _ p pq _ (hl q)) (valid _ q (hp q) _ (hl q)))
    obtain ⟨p,rfl⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simp [card]⟩).2 a
    exact ⟨_,hl p,((avoids l).1 p).2⟩
  have single (a : α) {p q : I} (hp : p∈A a) (hq : q∈A a) : p=q := by
    obtain ⟨u,hu,_⟩ := hits 0 a
    obtain ⟨v,hv,vu⟩ := hits u a
    exact loyal p q v u vu (valid _ _ hp _ hv) (valid _ _ hq _ hv) (valid _ _ hp _ hu) (valid _ _ hq _ hu)
  choose f hp hl using fun p => cover p (matching 0 p) ((avoids 0).1 p).1
  have inj : Function.Injective f := fun p q eq=>single (f q) (eq ▸ hp p) (hp q)
  have bij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simp [card]⟩
  refine ⟨f,bij,fun p=>⟨?_,?_⟩⟩
  · ext q
    exact ⟨fun h=>mem_singleton.mpr (single _ h (hp p)),fun h=>by rw [mem_singleton.mp h]; exact hp p⟩
  · apply Finset.Subset.antisymm
    · exact fun l h => valid _ _ (hp p) _ h
    · intro l hh
      obtain ⟨a,pa,la⟩ := cover p l hh
      obtain ⟨q,rfl⟩ := bij.2 a
      obtain rfl := single _ pa (hp q)
      exact la
end PEqualNP.Outside.L_meta_18769.Rigid
namespace PEqualNP.Outside.L_meta_18769.Critical
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection
open Finset Bank
def input (P : Finset I) (Z : Finset L) := incidenceInput Z (insert 0 (P.image idx))
def state (pre : List Gate) (P : Finset I) (Z : Finset L) := Suffix.run pre (input P Z)
def W (pre : List Gate) (P : Finset I) (Z : Finset L) (w : ℕ) := (state pre P Z).getD w false
def Pt (pre : List Gate) (w : ℕ) := ∃p : I,∀ P Z,W pre P Z w=decide (p∈P)
def Pure (pre : List Gate) := ∀ w, Pt pre w ∨ ∀ P Z,W pre P Z w=W pre ∅ Z w
def flag (P : Finset I) (Z : Finset L) := ∃ p∈P,∃ l∈Z,l∈nbr p
abbrev Flag := {t : I × L // t.2∈nbr t.1}
abbrev J := Sum I Flag
def posP : J → Finset I | .inl p => {p} | .inr e => {e.val.1}
def negP : J → Finset I | .inl _ => ∅ | .inr e => {e.val.1}
def posL : J → Finset L | .inl p => {idx p} | .inr e => {e.val.2}
def negL : J → Finset L | .inl p => {idx p} | .inr e => (nbr e.val.1)ᶜ
theorem positive (j : J) : flag (posP j) (posL j) := by
  cases j with
  | inl p => exact ⟨p,mem_singleton_self _,idx p,mem_singleton_self _,mem_filter.mpr ⟨mem_univ _,Or.inl rfl⟩⟩
  | inr e => exact ⟨e.val.1,mem_singleton_self _,e.val.2,mem_singleton_self _,e.property⟩
theorem negative (j : J) : ¬flag (negP j) (negL j) := by
  cases j with
  | inl p => simp [flag,negP]
  | inr e =>
    rintro ⟨p,hp,l,hl,hh⟩
    have eq : p=e.val.1 := mem_singleton.mp hp
    exact (mem_compl.mp hl) (eq ▸ hh)
theorem len (pre) (P : Finset I) (Z : Finset L) : (state pre P Z).length=26+pre.length := by
  simp [state,Suffix.length_run,input,incidenceInput]
theorem wave_empty (pre) (Z : Finset L) (w) : W pre ∅ Z w=wave pre w Z := by
  simp only [W,state,input,Finset.image_empty]
  rfl

theorem physical {pre post : List Gate} {o : ℕ} (ha : IsAO2 26 ⟨pre,0⟩)
    (legal : ∀g∈post,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (pure : Pure pre)
    (ok : ∀P Z,(Circuit.mk (pre++post) o).eval (input P Z)=true ↔ flag P Z)
    (short : post.length≤23) : 36≤pre.length ∧ 23≤post.length := by
  classical
  let X (j : J) := state pre (posP j) (posL j)
  let Y (j : J) := state pre (negP j) (negL j)
  have faithful (j : J) : Suffix.sep (Suffix.run post (X j)) (Suffix.run post (Y j)) o := by
    have sim (raw : List Bool) : Suffix.run post (Suffix.run pre raw)=Column.wf (pre++post) raw := by
      unfold Suffix.run Column.wf
      rw [List.foldl_append]
      rfl
    change (Suffix.run post (Suffix.run pre _)).getD o false=true ∧ (Suffix.run post (Suffix.run pre _)).getD o false=false
    rw [sim,sim]
    refine ⟨(ok _ _).mpr (positive j),?_⟩
    change (Circuit.mk (pre++post) o).eval (input (negP j) (negL j))=false
    cases eq : (Circuit.mk (pre++post) o).eval (input (negP j) (negL j)) with
    | false => rfl
    | true => exact (negative j ((ok _ _).mp eq)).elim
  obtain ⟨T,hit,ub⟩ := Suffix.sources (26+pre.length) X Y (fun j=>⟨len pre _ _,len pre _ _⟩)
    post legal {o} (fun i=>⟨o,mem_singleton_self _,faithful i⟩)
  simp only [card_singleton] at ub
  let PR := T.filter (Pt pre)
  let LR := T.filter (fun w=>¬Pt pre w)
  have sizes : PR.card+LR.card=T.card := Finset.card_filter_add_card_filter_not _
  have piv (p : I) : ∃ w∈PR,∀ P Z,W pre P Z w=decide (p∈P) := by
    obtain ⟨w,mem,hi,lo⟩ := hit (Sum.inl p)
    change W pre {p} {idx p} w=true at hi
    change W pre ∅ {idx p} w=false at lo
    rcases pure w with typ|fixed
    · obtain ⟨q,h⟩ := typ
      have eq : q=p := mem_singleton.mp (of_decide_eq_true ((h _ _).symm.trans hi))
      subst q
      exact ⟨w,mem_filter.mpr ⟨mem,⟨p,h⟩⟩,h⟩
    · exact False.elim (Bool.noConfusion (hi.symm.trans ((fixed _ _).trans lo)))
  choose g gm gp using piv
  have ginj : Function.Injective g := by
    intro p q eq
    have hp : W pre {p} ∅ (g p)=true := by rw [gp];simp
    rw [eq,gp] at hp
    exact (mem_singleton.mp (of_decide_eq_true hp)).symm
  have pc : 12≤PR.card := by simpa using card_le_card_of_injOn (s:=(univ : Finset I)) (t:=PR) g (fun i _=>gm i) ginj.injOn
  let A (w : ↥LR) := univ.filter (fun p : I=>wave pre w.val (nbr p)ᶜ=false)
  let B (w : ↥LR) := univ.filter (fun l : L=>wave pre w.val {l}=true)
  have valid (w : ↥LR) (p) (hp : p∈A w) (l) (hl : l∈B w) : l∈nbr p := by
    have o1 := (mem_filter.mp hp).2
    have o2 := (mem_filter.mp hl).2
    by_contra miss
    have bump := Column.val_mono (⟨pre,0⟩ : Circuit) 13 0 ha {l} (nbr p)ᶜ
      (singleton_subset_iff.mpr (mem_compl.mpr miss)) w.val o2
    exact Bool.noConfusion (bump.symm.trans o1)
  have covered (p) (l) (h : l∈nbr p) : ∃w,p∈A w ∧ l∈B w := by
    obtain ⟨w,mem,hi,lo⟩ := hit (Sum.inr (⟨(p,l),h⟩ : Flag))
    change W pre {p} {l} w=true at hi
    change W pre {p} (nbr p)ᶜ w=false at lo
    have notPoint : ¬Pt pre w := by
      rintro ⟨q,qp⟩
      exact Bool.noConfusion (hi.symm.trans ((qp _ _).trans ((qp _ _).symm.trans lo)))
    have dep := (pure w).resolve_left notPoint
    refine ⟨⟨w,mem_filter.mpr ⟨mem,notPoint⟩⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    · exact (wave_empty pre _ _).symm.trans ((dep _ _).symm.trans lo)
    · exact (wave_empty pre _ _).symm.trans ((dep _ _).symm.trans hi)
  have lc := Rigid.cardinal12 A B valid covered
  have cap : Fintype.card ↥LR ≤12 := by simpa only [Fintype.card_coe] using (show LR.card≤12 by omega)
  obtain ⟨f,_,shape⟩ := Rigid.rigid A B valid covered cap
  let co := fun p=> (f p).val
  have marks : Marks pre co := by
    intro p
    have bp (l : L) (hl : l∈nbr p) : wave pre (co p) {l}=true :=
      (mem_filter.mp (show l∈B (f p) by rw [(shape p).2];exact hl)).2
    have op : wave pre (co p) (nbr p)ᶜ=false :=
      (mem_filter.mp (show p∈A (f p) by rw [(shape p).1];simp)).2
    have self : idx p∈nbr p := mem_filter.mpr ⟨mem_univ _,Or.inl rfl⟩
    have hl := bp (idx p) self
    have bound : co p<26+pre.length := by
      by_contra! ge
      change (Column.wf pre (incidenceInput _ _)).getD (co p) false =true at hl
      rw [List.getD_eq_default _ _ (by simpa only [Column.wf_len,Column.inc_len] using ge)] at hl
      contradiction
    exact ⟨bound,bp,op⟩
  have k := Bank.required pre ha co marks
  have sup := card_le_card (filter_subset (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨pre,0⟩ j).op=GateOp.or) (range pre.length))
  simp only [card_range] at sup
  simp only [Fintype.card_coe] at lc
  exact ⟨k.trans sup,by omega⟩
theorem failure {pre post : List Gate} {o : ℕ} (ha : IsAO2 26 ⟨pre,0⟩)
    (legal : ∀g∈post,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (pure : Pure pre)
    (ok : ∀P Z,(Circuit.mk (pre++post) o).eval (input P Z)=true ↔ flag P Z)
    (small : (pre++post).length≤58) : pre.length≤34 ∧ 24≤post.length := by
  simp only [List.length_append] at small
  by_cases short : post.length≤23
  · obtain ⟨a,b⟩ := physical ha legal pure ok short
    omega
  · omega
end PEqualNP.Outside.L_meta_18769.Critical
