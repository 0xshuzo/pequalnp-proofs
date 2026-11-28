import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_8869.Column
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

def splitAt (C : Circuit) (n : Nat) (l : Fin n) (j : Nat) :=
  ∃ a b : Nat, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs=[a,b] ∧
    (∃ p, val C n l {p} a=true) ∧ (∃ r, val C n l {r} b=true) ∧
    ¬∃ p, val C n l {p} a=true ∧ val C n l {p} b=true

theorem reach (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (color : Fin n → Fin n) (Zb : Finset (Fin n))
    (hedge : ∀ k < C.size, ∀ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or →
      val C n l Zb (n + n + k) = false → (¬∃ z, val C n l {z} a=true ∧ val C n l {z} b=true) → ∀ u v : Fin n, u ≠ v →
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
      by_cases both : ∃ z, val C n l {z} a=true ∧ val C n l {z} b=true
      · obtain ⟨z,za,zb⟩ := both
        exact (ih a ha (by omega) hgood.1 u z hu za).trans (ih b hb (by omega) hgood.2 z v zb hv)
      obtain ⟨u', v', hu', hv', hr⟩ := hedge k hk a b hin hop' hgw both u v huv hu hv
      exact ((ih a ha (by omega) hgood.1 u u' hu hu').trans hr).trans
        (ih b hb (by omega) hgood.2 v' v hv' hv)
    · by_cases huv : v = u
      · rw [huv]
      by_cases both : ∃ z, val C n l {z} a=true ∧ val C n l {z} b=true
      · obtain ⟨z,za,zb⟩ := both
        exact (ih b hb (by omega) hgood.2 u z hu zb).trans (ih a ha (by omega) hgood.1 z v za hv)
      obtain ⟨u', v', hu', hv', hr⟩ := hedge k hk a b hin hop' hgw both v u huv hv hu
      exact (((ih a ha (by omega) hgood.1 v u' hv hu').trans hr).trans
        (ih b hb (by omega) hgood.2 v' u hv' hu)).symm
    · exact ih b hb (by omega) hgood.2 u v hu hv

end PEqualNP.Outside.L_meta_8869.Column

open PEqualNP.Outside.L_meta_8869.Column PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8869.Column : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 accepted : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ accepted, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             accepted.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     splitAt x2 x1 x4 x10 ∧ x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  intro n C X accepted l hC hout hacc hrej
  classical
  have hrej' : val C n l Xᶜ C.output = false := hrej
  have hacc' : ∀ p ∈ accepted, val C n l {p} C.output = true := hacc
  have hsub : ∀ w, val C n l Xᶜ w = false → ∀ p : Fin n, val C n l {p} w = true → p ∈ X := by
    intro w hw p hp
    by_contra hpX
    have := val_mono C n l hC {p} Xᶜ (by simpa using hpX) w hp
    rw [hw] at this
    exact absurd this (by simp)
  refine ⟨(Finset.range C.size).filter (fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      splitAt C n l j ∧ val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true),
    ?_, ?_⟩
  · rcases accepted.eq_empty_or_nonempty with hX | ⟨p0, _⟩
    · rw [hX]; simp
    let A : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0
    let B : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0
    let f : ℕ → Fin n × Fin n := fun j =>
      if h : ∃ u v : Fin n, u ≠ v ∧ val C n l {u} (A j) = true ∧ val C n l {v} (B j) = true
      then (h.choose, h.choose_spec.choose) else (p0, p0)
    apply graph_count _ f accepted
    intro color glued u hu v hv
    refine reach C n l hC color Xᶜ ?_ C.output hout hrej' u v (hacc' u hu) (hacc' v hv)
    intro k hk a b hin hop hgood apart u v huv hua hvb
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
      splitAt C n l j ∧ val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, ⟨a,b,hin,⟨u,hua⟩,⟨v,hvb⟩,apart⟩, hgood, u, v, huv, ?_, ?_⟩
      · rw [hval, hop]; simp [GateOp.eval, hua]
      · rw [hval, hop]; simp [GateOp.eval, hvb]
    have hfk : f k = (hex.choose, hex.choose_spec.choose) := by
      simp only [f, hex, dite_true]
    obtain ⟨hne, h1, h2⟩ := hex.choose_spec.choose_spec
    refine ⟨hex.choose, hex.choose_spec.choose, hAk ▸ h1, hBk ▸ h2, ?_⟩
    simpa only [hfk] using glued k hk9
  · intro j hj
    obtain ⟨hjr, hop, sp, hgood, p, q, hpq, hp, hq⟩ := Finset.mem_filter.mp hj
    refine ⟨Finset.mem_range.mp hjr, hop, ?_⟩
    show splitAt C n l j ∧ val C n l Xᶜ (n + n + j) = false ∧
      (∃ (x13 : Fin n) (x14 : Fin n), x13 ≠ x14 ∧ val C n l {x13} (n + n + j) = true ∧
        val C n l {x14} (n + n + j) = true) ∧
      ∀ (x13 : Fin n), val C n l {x13} (n + n + j) = true → x13 ∈ X
    exact ⟨sp, hgood, ⟨p, q, hpq, hp, hq⟩, hsub _ hgood⟩

namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection
open Finset
open Classical in
def Good {n} (C : Circuit) (S : Fin n → Finset (Fin n)) (j : Nat) (l : Fin n) : Prop :=
  (gateAt C j).op=.or ∧ Column.splitAt C n l j ∧ wireValue C (incidenceInput (S l)ᶜ {l}) (n+n+j)=false ∧
  (∃ p r : Fin n, p≠r ∧ wireValue C (incidenceInput {p} {l}) (n+n+j)=true ∧
    wireValue C (incidenceInput {r} {l}) (n+n+j)=true) ∧
  (∀ p, wireValue C (incidenceInput {p} {l}) (n+n+j)=true → p∈S l)
open Classical in
theorem accepted_mass {n : Nat} (C : Circuit) (S : Fin n → Finset (Fin n)) (E : Finset (Fin n × Fin n))
    (ao : IsAO2 (n+n) C) (valid : C.output<n+n+C.size)
    (hit : ∀ e∈E,C.eval (incidenceInput {e.1} {e.2})=true)
    (off : ∀ l,C.eval (incidenceInput (S l)ᶜ {l})=false) :
    E.card ≤ (E.image Prod.snd).card +
       ∑ j∈range C.size, ((E.image Prod.snd).filter (fun l => Good C S j l)).card := by
  classical
  let Y := E.image Prod.snd
  let F (l : Fin n) := univ.filter (fun p : Fin n => (p,l)∈E)
  have row (l : Fin n) : (F l).card≤1+((range C.size).filter (fun j => Good C S j l)).card := by
    obtain ⟨J,sz,ok⟩ := Column n C (S l) (F l) l ao valid (fun p hp => hit (p,l) (mem_filter.mp hp).2) (off l)
    have incl : J⊆(range C.size).filter (fun j => Good C S j l) := by
      intro j hj
      obtain ⟨bound,op,data⟩ := ok j hj
      exact mem_filter.mpr ⟨mem_range.mpr bound,op,data⟩
    have num := card_le_card incl
    omega
  have sumcard := Finset.card_eq_sum_card_fiberwise (s:=E) (t:=Y) (f:=Prod.snd)
    (fun e he => mem_image_of_mem _ he)
  have fiber (l : Fin n) : (E.filter (fun e => e.2=l)).card=(F l).card := by
    let W := E.filter (fun e => e.2=l)
    have image : W.image Prod.fst=F l := by
      ext p
      simp only [W,F,mem_image,Prod.exists,mem_filter,mem_univ,true_and]
      aesop
    rw [←image,Finset.card_image_of_injOn]
    rintro ⟨a,b⟩ h ⟨a',b'⟩ h' eq
    exact Prod.ext eq ((mem_filter.mp h).2.trans (mem_filter.mp h').2.symm)
  simp_rw [fiber] at sumcard
  have sum := sum_le_sum (s:=Y) (fun l _ => row l)
  simp only [sum_add_distrib,sum_const,smul_eq_mul,Nat.mul_one] at sum
  have exchange : (∑ l∈Y, ((range C.size).filter (fun j => Good C S j l)).card) =
      ∑ j∈range C.size, (Y.filter (fun l => Good C S j l)).card := by
    simp only [card_filter]
    rw [sum_comm]
  rw [sumcard]
  change _ ≤ Y.card+ _
  rw [←exchange]
  exact sum

open Classical in
theorem seven_load {n : Nat} (C : Circuit) (S : Fin n → Finset (Fin n)) (E : Finset (Fin n × Fin n))
    (ao : IsAO2 (n+n) C) (valid : C.output<n+n+C.size)
    (hit : ∀ e∈E,C.eval (incidenceInput {e.1} {e.2})=true)
    (off : ∀ l,C.eval (incidenceInput (S l)ᶜ {l})=false)
    (active : (E.image Prod.snd).card≤C.size)
    (load7 : ∀ j<C.size, ((E.image Prod.snd).filter (fun l => Good C S j l)).card≤7) : E.card≤8*C.size := by
  classical
  have price := accepted_mass C S E ao valid hit off
  have charge := sum_le_sum (s:=range C.size) (fun j hj => load7 j (mem_range.mp hj))
  simp only [sum_const,card_range,smul_eq_mul] at charge
  omega
end PEqualNP.Outside.L_meta_8869
