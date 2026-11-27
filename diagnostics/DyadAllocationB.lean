import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_7290

namespace PlaneOrdered
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

theorem ordered (n : ℕ) (D : Circuit) (h : PEqualNP.TopForm.IsAO2 n D) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (D.wires (List.ofFn x)).getD w false) := by
  let C : Circuit := ⟨D.gates,w⟩
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    exact ⟨h.1 g hg,by have eq := h.2.2 g hg; omega⟩
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  exact cmono C hm n x y hxy

end PlaneOrdered



namespace Dyads3791

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

private lemma no_four_cycle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hNoC4 : NoFourCycle G) {a b w1 w2 : Fin n} (hab : a ≠ b) (hw : w1 ≠ w2)
    (haw1 : G.Adj a w1) (haw2 : G.Adj a w2) (hbw1 : G.Adj b w1) (hbw2 : G.Adj b w2) : False := by
  have hle : (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1 := hNoC4 a b hab
  have h1 : w1 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw1, hbw1]
  have h2 : w2 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw2, hbw2]
  have hgt : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card :=
    Finset.one_lt_card.mpr ⟨w1, h1, w2, h2, hw⟩
  omega

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

private lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  unfold opnd
  rcases h : (gateAt C j).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

private lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

private lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

private lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  unfold Circuit.wires
  rw [foldl_append_length, List.length_ofFn]

private lemma wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal Circuit.wires
  have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
  rw [foldl_append_getD_lt _ C.gates (List.ofFn x) false i.val hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

private lemma wireVal_ge {n : ℕ} (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wires_length]; exact hw

private lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => wireVal n C w x) := by
  unfold wireVal Circuit.wires
  have hgate := foldl_append_getD_gate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x) false j hj ⟨GateOp.or, []⟩
  rw [List.length_ofFn] at hgate
  rw [hgate]
  change (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false) =
    (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < (List.ofFn x).length + j := by
    rw [List.length_ofFn]
    exact hAO.2.1 j hj i hi
  exact foldl_append_take_getD _ C.gates (List.ofFn x) false j i (Nat.le_of_lt hj) hilt

private lemma wireVal_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma wireVal_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma circuitFun_eq_wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireVal n C C.output x := rfl

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

private lemma orReaches_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ b : Fin 2, OrReaches n C (opnd C j b) g)) := by
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
        rw [inputs_eq_pair hAO hlt] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu.1 with rfl | rfl
        · exact ⟨hop, 0, hu.2.1, hgu⟩
        · exact ⟨hop, 1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, b, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨opnd C j b, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨opnd_mem_inputs hAO hj b, hnu, opnd_lt hAO hj b⟩

private lemma orReaches_self {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hAO (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

private lemma orReaches_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, b, hb⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : opnd C j b < n + j := opnd_lt hAO hj b
      have hrec := ih _ hlt g hb
      exact ⟨by omega, hrec.2⟩

private lemma orReaches_trans {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g h : ℕ, OrReaches n C w g → OrReaches n C (n + g) h → OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g h hwg hgh
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact hgh
    · have hrec := ih _ (opnd_lt hAO hj b) g h hb hgh
      exact (orReaches_iff hAO (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, b, hrec⟩⟩

private lemma orReaches_parent {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      w = n + g ∨
        ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧ OrReaches n C w h ∧
          ∃ b : Fin 2, opnd C h b = n + g := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact Or.inl rfl
    · right
      rcases ih _ (opnd_lt hAO hj b) g hb with hEq | ⟨h, hh, hhop, hreach, b', hb'⟩
      · exact ⟨j, hj, hop, orReaches_self hAO hj, b, hEq⟩
      · exact ⟨h, hh, hhop, (orReaches_iff hAO (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, b, hreach⟩⟩, b', hb'⟩

private lemma wireVal_of_orReaches {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      ∀ x : Fin n → Bool, wireVal n C (n + g) x = true → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg x hxg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact hxg
    · have hsub := ih _ (opnd_lt hAO hj b) g hb x hxg
      rw [wireVal_or hAO hj hop, Bool.or_eq_true]
      fin_cases b
      · exact Or.inl hsub
      · exact Or.inr hsub

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

private lemma orIn_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

private lemma orIn_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

private lemma orIn_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  unfold orIn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hAO] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, b, hb⟩
      · rw [inputs_eq_pair hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · fin_cases b
        · exact Or.inl (Or.inr ⟨k, hk, hb, hkop, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hb, hkop, huk⟩)
  · rintro ((h0 | ⟨k, hk, h0k, hkop, huk⟩) | (h1 | ⟨k, hk, h1k, hkop, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h0]
      exact opnd_mem_inputs hAO hj 0
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 0, h0k⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h1]
      exact opnd_mem_inputs hAO hj 1
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 1, h1k⟩⟩

private lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {w g : ℕ} (hwg : OrReaches n C w g) :
    orIn n C (n + g) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hEq | ⟨k, hk, hgk, hkop, huk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans hAO w g k hwg hgk, hkop, huk⟩

private lemma wireVal_true_of_mem_orIn {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i : Fin n} {x : Fin n → Bool} (hxi : x i = true) :
    ∀ w : ℕ, i ∈ orIn n C w → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hi
    by_cases hlt : w < n
    · have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
      rw [heq, Finset.mem_singleton] at hi
      subst hi
      exact (wireVal_input C ⟨w, hlt⟩ x).trans hxi
    · by_cases hge : n + C.gates.length ≤ w
      · rw [orIn_ge hAO hge] at hi
        simp at hi
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hi ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [orIn_and hAO hj hop] at hi
          simp at hi
        · rw [orIn_or hAO hj hop, Finset.mem_union] at hi
          rw [wireVal_or hAO hj hop, Bool.or_eq_true]
          rcases hi with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

open Classical in
private noncomputable def bigOrReach (n : ℕ) (C : Circuit) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun g =>
    (gateAt C g).op = GateOp.or ∧ 2 ≤ (orIn n C (n + g)).card ∧ ∃ w ∈ W, OrReaches n C w g

private lemma leaf_count_bound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ k : ℕ, ∀ W : Finset ℕ, (bigOrReach n C W).card = k →
      (W.biUnion (orIn n C)).card ≤ W.card + k := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W hk
    by_cases hne : (bigOrReach n C W).Nonempty
    · set M := bigOrReach n C W
      set m := M.max' hne
      have hmM : m ∈ M := Finset.max'_mem M hne
      have hm_props : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
          2 ≤ (orIn n C (n + m)).card ∧ ∃ w ∈ W, OrReaches n C w m := by
        simpa [M, bigOrReach, Finset.mem_filter, Finset.mem_range] using hmM
      have hmax_unique : ∀ w ∈ W, OrReaches n C w m → w = n + m := by
        intro w hw hwm
        have hle := orReaches_le hAO w m hwm
        rw [orReaches_iff hAO] at hwm
        rcases hwm with ⟨j, hj, rfl, hcase⟩
        by_contra hne_w
        have hmj : m ≠ j := fun h => hne_w (by omega)
        rcases hcase with hEq | ⟨hjop, b, hb⟩
        · exact hmj hEq
        · have hjM : j ∈ M := by
            simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
            refine ⟨hj, hjop, ?_, n + j, hw, orReaches_self hAO hj⟩
            have hsub : orIn n C (n + m) ⊆ orIn n C (n + j) :=
              orIn_subset_of_orReaches hAO
                ((orReaches_iff hAO (n + j) m).mpr ⟨j, hj, rfl, Or.inr ⟨hjop, b, hb⟩⟩)
            exact le_trans hm_props.2.2.1 (Finset.card_le_card hsub)
          have hjle : j ≤ m := Finset.le_max' M j hjM
          omega
      have hnmW : n + m ∈ W := by
        rcases hm_props.2.2.2 with ⟨w, hw, hwm⟩
        rwa [hmax_unique w hw hwm] at hw
      set W' : Finset ℕ := insert (opnd C m 0) (insert (opnd C m 1) (W.erase (n + m)))
      have hbi : W.biUnion (orIn n C) ⊆ W'.biUnion (orIn n C) := by
        intro u hu
        rw [Finset.mem_biUnion] at hu ⊢
        rcases hu with ⟨w, hw, huw⟩
        by_cases hwm : w = n + m
        · subst hwm
          rw [orIn_or hAO hm_props.1 hm_props.2.1, Finset.mem_union] at huw
          rcases huw with h0 | h1
          · exact ⟨opnd C m 0, by simp [W'], h0⟩
          · exact ⟨opnd C m 1, by simp [W'], h1⟩
        · exact ⟨w, by simp [W', hw, hwm], huw⟩
      have hW'card : W'.card ≤ W.card + 1 := by
        have h1 : W'.card ≤ (insert (opnd C m 1) (W.erase (n + m))).card + 1 :=
          Finset.card_insert_le _ _
        have h2 : (insert (opnd C m 1) (W.erase (n + m))).card ≤ (W.erase (n + m)).card + 1 :=
          Finset.card_insert_le _ _
        have h3 : (W.erase (n + m)).card + 1 = W.card := Finset.card_erase_add_one hnmW
        omega
      have hM'sub : bigOrReach n C W' ⊆ M.erase m := by
        intro g hg
        simp only [bigOrReach, Finset.mem_filter, Finset.mem_range] at hg
        rcases hg with ⟨hglt, hgop, hgcard, w', hw', hw'g⟩
        rw [Finset.mem_erase]
        have hgM : g ∈ M := by
          simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
          refine ⟨hglt, hgop, hgcard, ?_⟩
          simp only [W', Finset.mem_insert, Finset.mem_erase] at hw'
          rcases hw' with rfl | rfl | ⟨_, hw'W⟩
          · exact ⟨n + m, hnmW,
              (orReaches_iff hAO (n + m) g).mpr ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, 0, hw'g⟩⟩⟩
          · exact ⟨n + m, hnmW,
              (orReaches_iff hAO (n + m) g).mpr ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, 1, hw'g⟩⟩⟩
          · exact ⟨w', hw'W, hw'g⟩
        refine ⟨?_, hgM⟩
        intro hgm
        subst hgm
        simp only [W', Finset.mem_insert, Finset.mem_erase] at hw'
        rcases hw' with rfl | rfl | ⟨hne', hw'W⟩
        · have hle := (orReaches_le hAO _ _ hw'g).1
          have hlt := opnd_lt hAO hm_props.1 0
          omega
        · have hle := (orReaches_le hAO _ _ hw'g).1
          have hlt := opnd_lt hAO hm_props.1 1
          omega
        · exact hne' (hmax_unique w' hw'W hw'g)
      have hM'card_le : (bigOrReach n C W').card ≤ (M.erase m).card :=
        Finset.card_le_card hM'sub
      have hMerase : (M.erase m).card + 1 = k := by
        rw [Finset.card_erase_add_one hmM, hk]
      have hM'lt : (bigOrReach n C W').card < k := by omega
      have hrec := ih _ hM'lt W' rfl
      have hbi_card : (W.biUnion (orIn n C)).card ≤ (W'.biUnion (orIn n C)).card :=
        Finset.card_le_card hbi
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hle1 : ∀ w ∈ W, (orIn n C w).card ≤ 1 := by
        intro w hw
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ (orIn n C w).card := hgt
        by_cases hlt : w < n
        · have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
          rw [heq, Finset.card_singleton] at hge2
          omega
        · by_cases hge : n + C.gates.length ≤ w
          · rw [orIn_ge hAO hge, Finset.card_empty] at hge2
            omega
          · set j := w - n
            have hwEq : w = n + j := by omega
            have hj : j < C.gates.length := by omega
            have hmem : gateAt C j ∈ C.gates := by
              unfold gateAt
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
              exact List.getElem_mem hj
            rw [hwEq] at hge2 hw
            rcases hAO.1 _ hmem with hop | hop
            · rw [orIn_and hAO hj hop, Finset.card_empty] at hge2
              omega
            · have hjM : j ∈ bigOrReach n C W := by
                simp only [bigOrReach, Finset.mem_filter, Finset.mem_range]
                exact ⟨hj, hop, hge2, n + j, hw, orReaches_self hAO hj⟩
              rw [hne] at hjM
              simp at hjM
      have hbi : (W.biUnion (orIn n C)).card ≤ ∑ w ∈ W, (orIn n C w).card :=
        Finset.card_biUnion_le
      have hsum : ∑ w ∈ W, (orIn n C w).card ≤ ∑ _w ∈ W, 1 :=
        Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      omega

private lemma mem_insertNew {A : List (List ℕ)} {u v : List ℕ} :
    v ∈ insertNew A u ↔ v ∈ A ∨ v = u := by
  unfold insertNew
  split_ifs with h
  · constructor
    · intro hv; exact Or.inl hv
    · rintro (hv | rfl)
      · exact hv
      · exact h
  · simp

private lemma mem_foldl_insertNew {l acc : List (List ℕ)} {v : List ℕ} :
    v ∈ l.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih, mem_insertNew]
    tauto

private lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {v : List ℕ} :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, w, hw, rfl⟩
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, w, hw, rfl⟩

private lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  unfold readVectors
  rw [foldl_append_length, List.length_map, List.length_range]

private lemma readVectors_getD_ge (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ)
    {w : ℕ} (hw : n + C.gates.length ≤ w) :
    (readVectors C n S k).getD w [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [readVectors_length]; exact hw

private lemma readVectors_getD_lt (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ)
    {w : ℕ} (hw : w < n) :
    (readVectors C n S k).getD w [] = leafVectors S k w := by
  unfold readVectors
  have hlt : w < ((List.range n).map (leafVectors S k)).length := by
    rw [List.length_map, List.length_range]; exact hw
  rw [foldl_append_getD_lt _ C.gates ((List.range n).map (leafVectors S k)) [] w hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  simp

private lemma readVectors_getD_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length) :
    (readVectors C n S k).getD (n + j) [] =
      let ins := (gateAt C j).inputs.map fun i => (readVectors C n S k).getD i []
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
      | _ => [] := by
  let step : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    match g.op with
    | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
    | _ => []
  have hrv : readVectors C n S k =
      C.gates.foldl (fun R g => R ++ [step R g]) ((List.range n).map (leafVectors S k)) := rfl
  rw [hrv]
  have hgate := foldl_append_getD_gate step
    C.gates ((List.range n).map (leafVectors S k)) [] j hj ⟨GateOp.or, []⟩
  rw [List.length_map, List.length_range] at hgate
  rw [hgate]
  have hmap :
      (gateAt C j).inputs.map (fun i =>
        ((C.gates.take j).foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) =
      (gateAt C j).inputs.map (fun i =>
        (C.gates.foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) := by
    apply List.map_congr_left
    intro i hi
    have hilt : i < ((List.range n).map (leafVectors S k)).length + j := by
      rw [List.length_map, List.length_range]
      exact hAO.2.1 j hj i hi
    exact foldl_append_take_getD step C.gates ((List.range n).map (leafVectors S k)) [] j i
      (Nat.le_of_lt hj) hilt
  change (match (gateAt C j).op with
    | GateOp.or =>
      ((gateAt C j).inputs.map fun i => _).foldl (fun acc (A : List (List ℕ)) => A.foldl insertNew acc) []
    | GateOp.and =>
      ((gateAt C j).inputs.map fun i => _).foldl (andStep k) [S.map fun _ => 0]
    | _ => []) = _
  rw [hmap]

private lemma mem_readVectors_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (v : List ℕ) :
    v ∈ (readVectors C n S k).getD (n + j) [] ↔
      v ∈ (readVectors C n S k).getD (opnd C j 0) [] ∨
      v ∈ (readVectors C n S k).getD (opnd C j 1) [] := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

private lemma mem_readVectors_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (v : List ℕ) :
    v ∈ (readVectors C n S k).getD (n + j) [] ↔
      ∃ u0 ∈ (readVectors C n S k).getD (opnd C j 0) [],
      ∃ u1 ∈ (readVectors C n S k).getD (opnd C j 1) [],
        v = capAdd k (capAdd k (S.map fun _ => 0) u0) u1 := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨t, ht, u1, hu1, rfl⟩
    rw [mem_andStep] at ht
    rcases ht with ⟨z, hz, u0, hu0, rfl⟩
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u0, hu0, u1, hu1, rfl⟩
  · rintro ⟨u0, hu0, u1, hu1, rfl⟩
    refine ⟨capAdd k (S.map fun _ => 0) u0, ?_, u1, hu1, rfl⟩
    rw [mem_andStep]
    exact ⟨S.map fun _ => 0, List.mem_singleton_self _, u0, hu0, rfl⟩

private lemma readVectors_pair_inv {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, ∀ v ∈ (readVectors C n [p.val, q.val] 1).getD w [],
      ∃ a b : ℕ, v = [a, b] ∧ a ≤ 2 ∧ b ≤ 2 ∧ 1 ≤ a + b := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · have hne : q.val ≠ p.val := fun h => hpq (Fin.ext h.symm)
          simp only [ite_true, hne, ite_false] at hv
          exact ⟨1, 0, hv, by omega, by omega, by omega⟩
        · have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
          simp only [hne, ite_false, ite_true] at hv
          exact ⟨0, 1, hv, by omega, by omega, by omega⟩
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, rfl⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 0) u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 1) u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          refine ⟨min (min (0 + a0) 2 + a1) 2, min (min (0 + b0) 2 + b1) 2, ?_,
            Nat.min_le_right _ _, Nat.min_le_right _ _, by omega⟩
          simp [capAdd]
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with h0 | h1
          · exact ih _ (hw ▸ opnd_lt hAO hj 0) v h0
          · exact ih _ (hw ▸ opnd_lt hAO hj 1) v h1

private lemma readVectors_unit_left {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, [1, 0] ∈ (readVectors C n [p.val, q.val] 1).getD w [] → p ∈ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · rw [orIn_input p]; exact Finset.mem_singleton_self p
        · have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
          simp [hne] at hv
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, heq⟩
          rcases readVectors_pair_inv hAO hpq _ u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases readVectors_pair_inv hAO hpq _ u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          simp only [capAdd, List.map_cons, List.map_nil, List.zipWith_cons_cons,
            List.zipWith_nil_right, List.cons.injEq, and_true] at heq
          omega
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rw [orIn_or hAO hj hop, Finset.mem_union]
          rcases hv with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

private lemma readVectors_unit_right {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, [0, 1] ∈ (readVectors C n [p.val, q.val] 1).getD w [] → q ∈ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · have hne : q.val ≠ p.val := fun h => hpq (Fin.ext h.symm)
          simp [hne] at hv
        · rw [orIn_input q]; exact Finset.mem_singleton_self q
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, heq⟩
          rcases readVectors_pair_inv hAO hpq _ u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases readVectors_pair_inv hAO hpq _ u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          simp only [capAdd, List.map_cons, List.map_nil, List.zipWith_cons_cons,
            List.zipWith_nil_right, List.cons.injEq, and_true] at heq
          omega
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rw [orIn_or hAO hj hop, Finset.mem_union]
          rcases hv with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

private lemma readVectors_pair_extract {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, [1, 1] ∈ (readVectors C n [p.val, q.val] 1).getD w [] →
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C w a ∧
        ((p ∈ side C a 0 ∧ q ∈ side C a 1) ∨ (q ∈ side C a 0 ∧ p ∈ side C a 1)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · have hne : q.val ≠ p.val := fun h => hpq (Fin.ext h.symm)
          simp [hne] at hv
        · have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
          simp [hne] at hv
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, heq⟩
          rcases readVectors_pair_inv hAO hpq _ u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases readVectors_pair_inv hAO hpq _ u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          simp only [capAdd, List.map_cons, List.map_nil, List.zipWith_cons_cons,
            List.zipWith_nil_right, List.cons.injEq, and_true] at heq
          refine ⟨j, hj, hop, orReaches_self hAO hj, ?_⟩
          have hcases : (a0 = 1 ∧ b0 = 0 ∧ a1 = 0 ∧ b1 = 1) ∨
              (a0 = 0 ∧ b0 = 1 ∧ a1 = 1 ∧ b1 = 0) := by omega
          rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
          · exact Or.inl ⟨readVectors_unit_left hAO hpq _ hu0, readVectors_unit_right hAO hpq _ hu1⟩
          · exact Or.inr ⟨readVectors_unit_right hAO hpq _ hu0, readVectors_unit_left hAO hpq _ hu1⟩
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with h0 | h1
          · rcases ih _ (hw ▸ opnd_lt hAO hj 0) h0 with ⟨a, ha, haop, hreach, hside⟩
            exact ⟨a, ha, haop,
              (orReaches_iff hAO (n + j) a).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 0, hreach⟩⟩, hside⟩
          · rcases ih _ (hw ▸ opnd_lt hAO hj 1) h1 with ⟨a, ha, haop, hreach, hside⟩
            exact ⟨a, ha, haop,
              (orReaches_iff hAO (n + j) a).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 1, hreach⟩⟩, hside⟩

private lemma pairwise_lt_pair_eq {n : ℕ} {p q : Fin n} (hpq : p < q)
    {l : List (Fin n)} (hpw : l.Pairwise (· < ·))
    (hmem : ∀ x : Fin n, x ∈ l ↔ x = p ∨ x = q) :
    l = [p, q] := by
  cases l with
  | nil =>
    have hp := (hmem p).mpr (Or.inl rfl)
    simp at hp
  | cons a t =>
    rw [List.pairwise_cons] at hpw
    have ha : a = p ∨ a = q := (hmem a).mp List.mem_cons_self
    have hap : a = p := by
      rcases ha with h1 | h2
      · exact h1
      · have hp : p ∈ a :: t := (hmem p).mpr (Or.inl rfl)
        rw [List.mem_cons] at hp
        rcases hp with hEq | hpt
        · exact absurd (hEq.trans h2) (ne_of_lt hpq)
        · have hlt : a < p := hpw.1 p hpt
          rw [h2] at hlt
          exact absurd hlt (not_lt_of_gt hpq)
    subst a
    cases t with
    | nil =>
      have hq : q ∈ [p] := (hmem q).mpr (Or.inr rfl)
      rw [List.mem_singleton] at hq
      exact absurd hq (ne_of_gt hpq)
    | cons b t' =>
      rw [List.pairwise_cons] at hpw
      have hb : b = p ∨ b = q := (hmem b).mp (List.mem_cons_of_mem p List.mem_cons_self)
      have hpb : p < b := hpw.1 b List.mem_cons_self
      have hbq : b = q := by
        rcases hb with h1 | h2
        · rw [h1] at hpb
          exact absurd hpb (lt_irrefl p)
        · exact h2
      subst b
      cases t' with
      | nil => rfl
      | cons c t'' =>
        have hqc : q < c := hpw.2.1 c List.mem_cons_self
        have hc : c = p ∨ c = q :=
          (hmem c).mp (List.mem_cons_of_mem p (List.mem_cons_of_mem q List.mem_cons_self))
        rcases hc with h1 | h2
        · rw [h1] at hqc
          exact absurd (lt_trans hpq hqc) (lt_irrefl p)
        · rw [h2] at hqc
          exact absurd hqc (lt_irrefl q)

private lemma setList_pair {n : ℕ} {p q : Fin n} (hpq : p < q) :
    setList ({p, q} : Finset (Fin n)) = [p.val, q.val] := by
  unfold setList
  have hpw : ((List.finRange n).filter fun i => decide (i ∈ ({p, q} : Finset (Fin n)))).Pairwise (· < ·) := by
    apply List.Pairwise.filter
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp [hij]
  have hmem : ∀ x : Fin n,
      x ∈ (List.finRange n).filter (fun i => decide (i ∈ ({p, q} : Finset (Fin n)))) ↔
        x = p ∨ x = q := by
    intro x
    simp
  rw [pairwise_lt_pair_eq hpq hpw hmem]
  simp

def ExactPairs {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  ∀ u v : Fin n, circuitFun n C (pairInput u v)=decide (G.Adj u v)
def SimpleFlags {n : Nat} (G : SimpleGraph (Fin n)) (C : Circuit) :=
  ∀ p q : Fin n, G.Adj p q → p<q → readsAtMost C n [p.val,q.val] 1=true

private lemma edge_has_and_gate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (hcomp : ExactPairs G C)
    (hR1 : SimpleFlags G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
      ((u ∈ side C a 0 ∧ v ∈ side C a 1) ∨ (v ∈ side C a 0 ∧ u ∈ side C a 1)) := by
  suffices hord : ∀ p q : Fin n, G.Adj p q → p < q →
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
        ((p ∈ side C a 0 ∧ q ∈ side C a 1) ∨ (q ∈ side C a 0 ∧ p ∈ side C a 1)) by
    rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
    · exact hord u v hadj hlt
    · rcases hord v u hadj.symm hgt with ⟨a, ha, hop, hreach, hside⟩
      exact ⟨a, ha, hop, hreach, hside.symm⟩
  intro p q hpq_adj hpq_lt
  have hpq : p ≠ q := ne_of_lt hpq_lt
  have hrm := hR1 p q hpq_adj hpq_lt
  unfold readsAtMost at hrm
  rw [List.any_eq_true] at hrm
  rcases hrm with ⟨vec, hvec_mem, hvec_all⟩
  rcases readVectors_pair_inv hAO hpq C.output vec hvec_mem with ⟨a, b, rfl, ha2, hb2, hab1⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hvec_all
  have hcases : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hp_in : p ∈ orIn n C C.output := readVectors_unit_left hAO hpq C.output hvec_mem
    have hval : wireVal n C C.output (fun i => decide (i = p)) = true :=
      wireVal_true_of_mem_orIn hAO (by simp) C.output hp_in
    have hcf : circuitFun n C (fun i => decide (i = p)) = true := hval
    have eval := hcomp p p
    have same : pairInput p p=(fun i => decide (i=p)) := by funext i; simp only [pairInput,or_self]
    rw [same,hcf] at eval
    exact False.elim ((G.ne_of_adj (of_decide_eq_true eval.symm)) rfl)
  · have hq_in : q ∈ orIn n C C.output := readVectors_unit_right hAO hpq C.output hvec_mem
    have hval : wireVal n C C.output (fun i => decide (i = q)) = true :=
      wireVal_true_of_mem_orIn hAO (by simp) C.output hq_in
    have hcf : circuitFun n C (fun i => decide (i = q)) = true := hval
    have eval := hcomp q q
    have same : pairInput q q=(fun i => decide (i=q)) := by funext i; simp only [pairInput,or_self]
    rw [same,hcf] at eval
    exact False.elim ((G.ne_of_adj (of_decide_eq_true eval.symm)) rfl)
  · exact readVectors_pair_extract hAO hpq C.output hvec_mem

private def BelowG (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) : Prop :=
  ∀ u v : Fin n, wireVal n C (n+g) (pairInput u v)=true → G.Adj u v

private lemma belowG_of_orReaches {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (hcomp : ExactPairs G C)
    {g : ℕ} (hreach : OrReaches n C C.output g) :
    BelowG n G C g := by
  intro u v hv
  have hout : circuitFun n C (pairInput u v)=true := wireVal_of_orReaches hAO C.output g hreach (pairInput u v) hv
  exact of_decide_eq_true ((hcomp u v).symm.trans hout)

private lemma adj_of_and_orReaches {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (hcomp : ExactPairs G C)
    {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hreach : OrReaches n C C.output a) {u v : Fin n}
    (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) :
    G.Adj u v := by
  have h0 : wireVal n C (opnd C a 0) (pairInput u v) = true :=
    wireVal_true_of_mem_orIn hAO (by simp [pairInput]) _ hu
  have h1 : wireVal n C (opnd C a 1) (pairInput u v) = true :=
    wireVal_true_of_mem_orIn hAO (by simp [pairInput]) _ hv
  have ha_val : wireVal n C (n + a) (pairInput u v) = true := by
    rw [wireVal_and hAO ha hop, Bool.and_eq_true]
    exact ⟨h0, h1⟩
  exact belowG_of_orReaches hAO hcomp hreach u v ha_val

theorem count_dyads (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hNoC4 : NoFourCycle G) (hAO : IsAO2 n C)
    (hcomp : ExactPairs G C)
    (hR1 : SimpleFlags G C) :
    ∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧
      G.edgeFinset.card + S.card ≤ C.size + 1 := by
  classical
  by_cases hempty : G.edgeFinset = ∅
  · refine ⟨∅, ?_, ?_⟩
    · intro u v huv
      have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      rw [hempty] at hmem
      simp at hmem
    · rw [hempty]
      simp
  · have hne_edges : G.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases hne_edges with ⟨e0, he0⟩
    have hn_pos : 0 < n := by
      rcases e0 with ⟨u0, v0⟩
      exact Fin.pos u0
    let v0 : Fin n := ⟨0, hn_pos⟩
    let A_used : Finset ℕ := (Finset.range C.gates.length).filter fun a =>
      (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
      (side (n := n) C a 0).Nonempty ∧ (side (n := n) C a 1).Nonempty
    let OrTop : Finset ℕ := (Finset.range C.gates.length).filter fun g =>
      (gateAt C g).op = GateOp.or ∧ OrReaches n C C.output g
    let OrBot : Finset ℕ := (Finset.range C.gates.length).filter fun g =>
      (gateAt C g).op = GateOp.or ∧ ¬ BelowG n G C g
    have hA_star : ∀ a ∈ A_used, (side (n := n) C a 0).card = 1 ∨ (side (n := n) C a 1).card = 1 := by
      intro a ha
      simp only [A_used, Finset.mem_filter, Finset.mem_range] at ha
      rcases ha with ⟨halt, haop, hreach, hne0, hne1⟩
      by_contra hboth
      push Not at hboth
      have hpos0 : 0 < (side (n := n) C a 0).card := Finset.Nonempty.card_pos hne0
      have hpos1 : 0 < (side (n := n) C a 1).card := Finset.Nonempty.card_pos hne1
      have hgt0 : 1 < (side (n := n) C a 0).card := by omega
      have hgt1 : 1 < (side (n := n) C a 1).card := by omega
      rcases Finset.one_lt_card.mp hgt0 with ⟨u1, hu1, u2, hu2, hune⟩
      rcases Finset.one_lt_card.mp hgt1 with ⟨w1, hw1, w2, hw2, hwne⟩
      exact no_four_cycle hNoC4 hune hwne
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu1 hw1)
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu1 hw2)
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu2 hw1)
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu2 hw2)
    let ctrSide : ℕ → Fin 2 := fun a => if (side (n := n) C a 0).card = 1 then 0 else 1
    let leafSide : ℕ → Fin 2 := fun a => 1 - ctrSide a
    let ctr : ℕ → Fin n := fun a =>
      if h : (side (n := n) C a (ctrSide a)).Nonempty then h.choose else v0
    have hctr_eq : ∀ a ∈ A_used, side (n := n) C a (ctrSide a) = {ctr a} := by
      intro a ha
      have hcard1 : (side (n := n) C a (ctrSide a)).card = 1 := by
        simp only [ctrSide]
        split_ifs with h0
        · exact h0
        · exact (hA_star a ha).resolve_left h0
      have hne_c : (side (n := n) C a (ctrSide a)).Nonempty :=
        Finset.card_pos.mp (by omega)
      have hmem_c : ctr a ∈ side (n := n) C a (ctrSide a) := by
        simp only [ctr, hne_c, ↓reduceDIte]
        exact hne_c.choose_spec
      rcases Finset.card_eq_one.mp hcard1 with ⟨c, hc⟩
      rw [hc, Finset.mem_singleton] at hmem_c
      rw [hc, hmem_c]
    have hctr_adj : ∀ a ∈ A_used, ∀ u ∈ side (n := n) C a (leafSide a), G.Adj (ctr a) u := by
      intro a ha u hu
      have hA_mem := ha
      simp only [A_used, Finset.mem_filter, Finset.mem_range] at hA_mem
      rcases hA_mem with ⟨halt, haop, hreach, _, _⟩
      have hc_mem : ctr a ∈ side (n := n) C a (ctrSide a) := by
        rw [hctr_eq a ha]; exact Finset.mem_singleton_self _
      have hcs : ctrSide a = 0 ∨ ctrSide a = 1 := by simp only [ctrSide]; split_ifs <;> simp
      rcases hcs with h0 | h1
      · have hl : leafSide a = 1 := by simp [leafSide, h0]
        rw [h0] at hc_mem
        rw [hl] at hu
        exact adj_of_and_orReaches hAO hcomp halt haop hreach hc_mem hu
      · have hl : leafSide a = 0 := by simp [leafSide, h1]
        rw [h1] at hc_mem
        rw [hl] at hu
        exact (adj_of_and_orReaches hAO hcomp halt haop hreach hu hc_mem).symm
    let S : Finset (Fin n) := A_used.image ctr
    have hS_le : S.card ≤ A_used.card := Finset.card_image_le
    have hS_cover : ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S := by
      intro u v huv
      rcases edge_has_and_gate hAO hcomp hR1 huv with ⟨a, ha, hop, hreach, hside⟩
      have haA : a ∈ A_used := by
        simp only [A_used, Finset.mem_filter, Finset.mem_range]
        rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
        · exact ⟨ha, hop, hreach, ⟨u, hu0⟩, ⟨v, hv1⟩⟩
        · exact ⟨ha, hop, hreach, ⟨v, hv0⟩, ⟨u, hu1⟩⟩
      have hcs : ctrSide a = 0 ∨ ctrSide a = 1 := by simp only [ctrSide]; split_ifs <;> simp
      have hceq := hctr_eq a haA
      rcases hcs with h0 | h1
      · rw [h0] at hceq
        rcases hside with ⟨hu0, _⟩ | ⟨hv0, _⟩
        · rw [hceq, Finset.mem_singleton] at hu0
          exact Or.inl (Finset.mem_image.mpr ⟨a, haA, hu0.symm⟩)
        · rw [hceq, Finset.mem_singleton] at hv0
          exact Or.inr (Finset.mem_image.mpr ⟨a, haA, hv0.symm⟩)
      · rw [h1] at hceq
        rcases hside with ⟨_, hv1⟩ | ⟨_, hu1⟩
        · rw [hceq, Finset.mem_singleton] at hv1
          exact Or.inr (Finset.mem_image.mpr ⟨a, haA, hv1.symm⟩)
        · rw [hceq, Finset.mem_singleton] at hu1
          exact Or.inl (Finset.mem_image.mpr ⟨a, haA, hu1.symm⟩)
    have hdisj_A_OrTop : Disjoint A_used OrTop := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [A_used, OrTop, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      rw [hg1.2.1] at hg2
      cases hg2.2.1
    have hdisj_A_OrBot : Disjoint A_used OrBot := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [A_used, OrBot, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      rw [hg1.2.1] at hg2
      cases hg2.2.1
    have hdisj_OrTop_OrBot : Disjoint OrTop OrBot := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [OrTop, OrBot, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      exact hg2.2.2 (belowG_of_orReaches hAO hcomp hg1.2.2)
    have hsum_gates : A_used.card + OrTop.card + OrBot.card ≤ C.gates.length := by
      have hdisj1 : Disjoint (A_used ∪ OrTop) OrBot :=
        Finset.disjoint_union_left.mpr ⟨hdisj_A_OrBot, hdisj_OrTop_OrBot⟩
      have hcard_u : (A_used ∪ OrTop ∪ OrBot).card = A_used.card + OrTop.card + OrBot.card := by
        rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj_A_OrTop]
      rw [← hcard_u]
      calc (A_used ∪ OrTop ∪ OrBot).card
          ≤ (Finset.range C.gates.length).card := by
            apply Finset.card_le_card
            intro g hg
            simp only [A_used, OrTop, OrBot, Finset.mem_union, Finset.mem_filter,
              Finset.mem_range] at hg ⊢
            omega
        _ = C.gates.length := Finset.card_range _
    have hA_le_OrTop : A_used.card ≤ OrTop.card + 1 := by
      let U : Finset ℕ := A_used ∪ OrTop
      let V : Finset ℕ := U.image fun g => n + g
      have hV_card : V.card = A_used.card + OrTop.card := by
        have hinj : Function.Injective (fun g : ℕ => n + g) := add_right_injective n
        rw [Finset.card_image_of_injective U hinj, Finset.card_union_of_disjoint hdisj_A_OrTop]
      have hV_sub : V ⊆ insert C.output
          ((OrTop ×ˢ (Finset.univ : Finset (Fin 2))).image fun p => opnd C p.1 p.2) := by
        intro w hw
        simp only [V, Finset.mem_image] at hw
        rcases hw with ⟨g, hgU, rfl⟩
        have hreach : OrReaches n C C.output g := by
          simp only [U, A_used, OrTop, Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hgU
          rcases hgU with hgA | hgO
          · exact hgA.2.2.1
          · exact hgO.2.2
        rw [Finset.mem_insert]
        rcases orReaches_parent hAO C.output g hreach with hEq | ⟨h, hh, hhop, hhreach, b, hb⟩
        · exact Or.inl hEq.symm
        · right
          rw [Finset.mem_image]
          refine ⟨(h, b), ?_, hb⟩
          rw [Finset.mem_product]
          refine ⟨?_, Finset.mem_univ b⟩
          simp only [OrTop, Finset.mem_filter, Finset.mem_range]
          exact ⟨hh, hhop, hhreach⟩
      have hcard_le : V.card ≤ OrTop.card * 2 + 1 := by
        calc V.card
            ≤ (insert C.output
                ((OrTop ×ˢ (Finset.univ : Finset (Fin 2))).image fun p => opnd C p.1 p.2)).card :=
              Finset.card_le_card hV_sub
          _ ≤ ((OrTop ×ˢ (Finset.univ : Finset (Fin 2))).image fun p => opnd C p.1 p.2).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ (OrTop ×ˢ (Finset.univ : Finset (Fin 2))).card + 1 :=
              Nat.add_le_add_right Finset.card_image_le 1
          _ = OrTop.card * 2 + 1 := by simp [Finset.card_product]
      omega
    let Kc : Fin n → Finset ℕ := fun c => A_used.filter fun a => ctr a = c
    let Wc : Fin n → Finset ℕ := fun c => (Kc c).image fun a => opnd C a (leafSide a)
    let Lc : Fin n → Finset (Fin n) := fun c => (Wc c).biUnion (orIn n C)
    let Mc : Fin n → Finset ℕ := fun c => bigOrReach n C (Wc c)
    have hE_sub : G.edgeFinset ⊆ S.biUnion fun c => (Lc c).image fun u => s(c, u) := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        rcases edge_has_and_gate hAO hcomp hR1 huv with ⟨a, ha, hop, hreach, hside⟩
        have haA : a ∈ A_used := by
          simp only [A_used, Finset.mem_filter, Finset.mem_range]
          rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
          · exact ⟨ha, hop, hreach, ⟨u, hu0⟩, ⟨v, hv1⟩⟩
          · exact ⟨ha, hop, hreach, ⟨v, hv0⟩, ⟨u, hu1⟩⟩
        have hcS : ctr a ∈ S := Finset.mem_image.mpr ⟨a, haA, rfl⟩
        have haK : a ∈ Kc (ctr a) := by
          simp [Kc, haA]
        have hwW : opnd C a (leafSide a) ∈ Wc (ctr a) :=
          Finset.mem_image.mpr ⟨a, haK, rfl⟩
        rw [Finset.mem_biUnion]
        refine ⟨ctr a, hcS, ?_⟩
        rw [Finset.mem_image]
        have hcs : ctrSide a = 0 ∨ ctrSide a = 1 := by simp only [ctrSide]; split_ifs <;> simp
        have hceq := hctr_eq a haA
        rcases hcs with h0 | h1
        · have hl : leafSide a = 1 := by simp [leafSide, h0]
          rw [h0] at hceq
          rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
          · rw [hceq, Finset.mem_singleton] at hu0
            refine ⟨v, ?_, by rw [hu0]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hv1⟩
          · rw [hceq, Finset.mem_singleton] at hv0
            refine ⟨u, ?_, by rw [hv0, Sym2.eq_swap]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hu1⟩
        · have hl : leafSide a = 0 := by simp [leafSide, h1]
          rw [h1] at hceq
          rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
          · rw [hceq, Finset.mem_singleton] at hv1
            refine ⟨u, ?_, by rw [hv1, Sym2.eq_swap]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hu0⟩
          · rw [hceq, Finset.mem_singleton] at hu1
            refine ⟨v, ?_, by rw [hu1]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hv0⟩
    have hE_le : G.edgeFinset.card ≤ ∑ c ∈ S, (Lc c).card := by
      calc G.edgeFinset.card
          ≤ (S.biUnion fun c => (Lc c).image fun u => s(c, u)).card := Finset.card_le_card hE_sub
        _ ≤ ∑ c ∈ S, ((Lc c).image fun u => s(c, u)).card := Finset.card_biUnion_le
        _ ≤ ∑ c ∈ S, (Lc c).card := Finset.sum_le_sum fun c _ => Finset.card_image_le
    have hLc_le : ∀ c ∈ S, (Lc c).card ≤ (Kc c).card + (Mc c).card := by
      intro c _
      have h1 := leaf_count_bound hAO (Mc c).card (Wc c) rfl
      have h2 : (Wc c).card ≤ (Kc c).card := Finset.card_image_le
      exact le_trans h1 (Nat.add_le_add_right h2 _)
    have hK_disj : Set.PairwiseDisjoint (S : Set (Fin n)) Kc := by
      intro c1 _ c2 _ hne
      change Disjoint (Kc c1) (Kc c2)
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      simp only [Kc, Finset.mem_filter] at ha1 ha2
      exact hne (ha1.2.symm.trans ha2.2)
    have hsum_K : ∑ c ∈ S, (Kc c).card ≤ A_used.card := by
      rw [← Finset.card_biUnion hK_disj]
      apply Finset.card_le_card
      intro a ha
      rw [Finset.mem_biUnion] at ha
      rcases ha with ⟨c, _, hac⟩
      exact (Finset.mem_filter.mp hac).1
    have hM_sub : ∀ c ∈ S, Mc c ⊆ OrBot := by
      intro c _ g hg
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hg
      rcases hg with ⟨hglt, hgop, hgcard, _, _, _⟩
      simp only [OrBot, Finset.mem_filter, Finset.mem_range]
      refine ⟨hglt, hgop, ?_⟩
      intro hbelow
      have hne_g : (orIn n C (n + g)).Nonempty := Finset.card_pos.mp (by omega)
      rcases hne_g with ⟨u, hu⟩
      have hval : wireVal n C (n + g) (fun i => decide (i = u)) = true :=
        wireVal_true_of_mem_orIn hAO (by simp) (n + g) hu
      have hh : pairInput u u=(fun i => decide (i=u)) := by funext i; simp only [pairInput,or_self]
      exact (G.ne_of_adj (hbelow u u (hh.symm ▸ hval))) rfl
    have hM_disj : Set.PairwiseDisjoint (S : Set (Fin n)) Mc := by
      intro c1 _ c2 _ hne
      change Disjoint (Mc c1) (Mc c2)
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      rcases hg1 with ⟨_, _, hgcard, w1, hw1, hw1g⟩
      rcases hg2 with ⟨_, _, _, w2, hw2, hw2g⟩
      simp only [Wc, Finset.mem_image] at hw1 hw2
      rcases hw1 with ⟨a1, ha1, rfl⟩
      rcases hw2 with ⟨a2, ha2, rfl⟩
      simp only [Kc, Finset.mem_filter] at ha1 ha2
      have hgt1 : 1 < (orIn n C (n + g)).card := by omega
      rcases Finset.one_lt_card.mp hgt1 with ⟨u1, hu1, u2, hu2, hune⟩
      have hsub1 : orIn n C (n + g) ⊆ side C a1 (leafSide a1) := orIn_subset_of_orReaches hAO hw1g
      have hsub2 : orIn n C (n + g) ⊆ side C a2 (leafSide a2) := orIn_subset_of_orReaches hAO hw2g
      have h1u1 : G.Adj c1 u1 := ha1.2 ▸ hctr_adj a1 ha1.1 u1 (hsub1 hu1)
      have h1u2 : G.Adj c1 u2 := ha1.2 ▸ hctr_adj a1 ha1.1 u2 (hsub1 hu2)
      have h2u1 : G.Adj c2 u1 := ha2.2 ▸ hctr_adj a2 ha2.1 u1 (hsub2 hu1)
      have h2u2 : G.Adj c2 u2 := ha2.2 ▸ hctr_adj a2 ha2.1 u2 (hsub2 hu2)
      exact no_four_cycle hNoC4 hne hune h1u1 h1u2 h2u1 h2u2
    have hsum_M : ∑ c ∈ S, (Mc c).card ≤ OrBot.card := by
      rw [← Finset.card_biUnion hM_disj]
      apply Finset.card_le_card
      intro g hg
      rw [Finset.mem_biUnion] at hg
      rcases hg with ⟨c, hcS, hgc⟩
      exact hM_sub c hcS hgc
    have hE_bound : G.edgeFinset.card ≤ A_used.card + OrBot.card := by
      calc G.edgeFinset.card
          ≤ ∑ c ∈ S, (Lc c).card := hE_le
        _ ≤ ∑ c ∈ S, ((Kc c).card + (Mc c).card) := Finset.sum_le_sum hLc_le
        _ = (∑ c ∈ S, (Kc c).card) + ∑ c ∈ S, (Mc c).card := Finset.sum_add_distrib
        _ ≤ A_used.card + OrBot.card := Nat.add_le_add hsum_K hsum_M
    refine ⟨S, hS_cover, ?_⟩
    change G.edgeFinset.card + S.card ≤ C.gates.length + 1
    omega

private lemma subset_gate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (singletonOff : ∀ i : Fin n,circuitFun n C (fun k => decide (k=i))=false)
    (hR1 : SimpleFlags G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
      ((u ∈ side C a 0 ∧ v ∈ side C a 1) ∨ (v ∈ side C a 0 ∧ u ∈ side C a 1)) := by
  suffices hord : ∀ p q : Fin n, G.Adj p q → p < q →
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
        ((p ∈ side C a 0 ∧ q ∈ side C a 1) ∨ (q ∈ side C a 0 ∧ p ∈ side C a 1)) by
    rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
    · exact hord u v hadj hlt
    · rcases hord v u hadj.symm hgt with ⟨a, ha, hop, hreach, hside⟩
      exact ⟨a, ha, hop, hreach, hside.symm⟩
  intro p q hpq_adj hpq_lt
  have hpq : p ≠ q := ne_of_lt hpq_lt
  have hrm := hR1 p q hpq_adj hpq_lt
  unfold readsAtMost at hrm
  rw [List.any_eq_true] at hrm
  rcases hrm with ⟨vec, hvec_mem, hvec_all⟩
  rcases readVectors_pair_inv hAO hpq C.output vec hvec_mem with ⟨a, b, rfl, ha2, hb2, hab1⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hvec_all
  have hcases : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hp_in : p ∈ orIn n C C.output := readVectors_unit_left hAO hpq C.output hvec_mem
    have hval : wireVal n C C.output (fun i => decide (i = p)) = true :=
      wireVal_true_of_mem_orIn hAO (by simp) C.output hp_in
    have hcf : circuitFun n C (fun i => decide (i = p)) = true := hval
    exact False.elim (Bool.noConfusion (hcf.symm.trans (singletonOff p)))
  · have hq_in : q ∈ orIn n C C.output := readVectors_unit_right hAO hpq C.output hvec_mem
    have hval : wireVal n C C.output (fun i => decide (i = q)) = true :=
      wireVal_true_of_mem_orIn hAO (by simp) C.output hq_in
    have hcf : circuitFun n C (fun i => decide (i = q)) = true := hval
    exact False.elim (Bool.noConfusion (hcf.symm.trans (singletonOff q)))
  · exact readVectors_pair_extract hAO hpq C.output hvec_mem

open Classical in
noncomputable def unusedAND (n : Nat) (C : Circuit) := (Finset.range C.gates.length).filter fun a =>
  (gateAt C a).op=GateOp.and ∧ ¬(OrReaches n C C.output a ∧
    (side (n:=n) C a 0).Nonempty ∧ (side (n:=n) C a 1).Nonempty)
def Routed (n : Nat) (C : Circuit) (p q : Fin n) : Prop :=
  ∃ j<C.gates.length,(gateAt C j).op=GateOp.and ∧ OrReaches n C C.output j ∧
    ((p∈side C j 0 ∧ q∈side C j 1) ∨ (q∈side C j 0 ∧ p∈side C j 1))

theorem unrouted_reader {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (ao : IsAO2 n C) (eq : ExactPairs G C) (p q : Fin n) (edge : G.Adj p q)
    (bad : ¬Routed n C p q) :
    ∃ j∈unusedAND n C,wireVal n C (n+j) (pairInput p q)=true := by
  classical
  by_contra! none
  have singleOff (i : Fin n) : wireVal n C C.output (fun k => decide (k=i))=false := by
    have h := eq i i
    have same : pairInput i i=(fun k => decide (k=i)) := by funext k; simp only [pairInput,or_self]
    rw [same,decide_eq_false (fun hi => G.ne_of_adj hi rfl)] at h
    exact h
  have back : ∀ w : Nat,wireVal n C w (pairInput p q)=true →
      ∃ k∈orIn n C w,k=p ∨ k=q := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro active
      by_cases small : w<n
      · let i : Fin n := ⟨w,small⟩
        have val : pairInput p q i=true := (wireVal_input C i _).symm.trans active
        exact ⟨i,by rw [show orIn n C w={i} from orIn_input i]; simp,of_decide_eq_true val⟩
      · by_cases high : n+C.gates.length≤w
        · exact False.elim (Bool.noConfusion (active.symm.trans (wireVal_ge C high _)))
        · let j := w-n
          have hw : w=n+j := by dsimp [j]; omega
          have hj : j<C.gates.length := by dsimp [j]; omega
          have mem : gateAt C j∈C.gates := by
            unfold gateAt
            rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
            exact List.getElem_mem hj
          rw [hw] at active ⊢
          rcases ao.1 _ mem with andOp|orOp
          · have vals := active
            rw [wireVal_and ao hj andOp,Bool.and_eq_true] at vals
            obtain ⟨u,hu,up⟩ := ih _ (hw ▸ opnd_lt ao hj 0) vals.1
            obtain ⟨v,hv,vp⟩ := ih _ (hw ▸ opnd_lt ao hj 1) vals.2
            have reach : OrReaches n C C.output j := by
              by_contra nc
              have unused : j∈unusedAND n C := Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr hj,andOp,fun h => nc h.1⟩
              exact (by simpa using none j unused : wireVal n C (n+j) (pairInput p q)≠true) active
            have un : u≠v := by
              rintro rfl
              let x : Fin n→Bool := fun k => decide (k=u)
              have yy : wireVal n C (n+j) x=true := by
                rw [wireVal_and ao hj andOp,Bool.and_eq_true]
                exact ⟨wireVal_true_of_mem_orIn ao (by simp [x]) _ hu,
                  wireVal_true_of_mem_orIn ao (by simp [x]) _ hv⟩
              exact Bool.noConfusion ((wireVal_of_orReaches ao C.output j reach x yy).symm.trans (singleOff u))
            exfalso
            apply bad
            refine ⟨j,hj,andOp,reach,?_⟩
            rcases up with rfl|rfl <;> rcases vp with rfl|rfl
            · contradiction
            · exact Or.inl ⟨hu,hv⟩
            · exact Or.inr ⟨hu,hv⟩
            · contradiction
          · rw [wireVal_or ao hj orOp,Bool.or_eq_true] at active
            rw [orIn_or ao hj orOp]
            rcases active with l|r
            · obtain ⟨u,hu,src⟩ := ih _ (hw ▸ opnd_lt ao hj 0) l
              exact ⟨u,Finset.mem_union_left _ hu,src⟩
            · obtain ⟨u,hu,src⟩ := ih _ (hw ▸ opnd_lt ao hj 1) r
              exact ⟨u,Finset.mem_union_right _ hu,src⟩
  have on : wireVal n C C.output (pairInput p q)=true := (eq p q).trans (decide_eq_true edge)
  obtain ⟨u,hu,_⟩ := back C.output on
  have pos := wireVal_true_of_mem_orIn (C:=C) ao (i:=u) (x:=fun k => decide (k=u)) (by simp) C.output hu
  exact Bool.noConfusion (pos.symm.trans (singleOff u))
theorem count_subgraph (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (C : Circuit) (hNoC4 : NoFourCycle G) (hAO : IsAO2 n C)
    (hcomp : ExactPairs G C)
    (hR1 : ∀u v,H.Adj u v → Routed n C u v) :
    ∃ S : Finset (Fin n), (∀ u v : Fin n, H.Adj u v → u ∈ S ∨ v ∈ S) ∧
      H.edgeFinset.card + S.card + (unusedAND n C).card ≤ C.size + 1 := by
  classical
  have singletonOff (i : Fin n) : circuitFun n C (fun k => decide (k=i))=false := by
    have eq : pairInput i i=(fun k => decide (k=i)) := by funext k; simp only [pairInput,or_self]
    rw [←eq,hcomp]
    apply decide_eq_false
    exact fun a => G.ne_of_adj a rfl
  have unusedSub : unusedAND n C ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
  by_cases hempty : H.edgeFinset = ∅
  · refine ⟨∅, ?_, ?_⟩
    · intro u v huv
      have hmem : s(u, v) ∈ H.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      rw [hempty] at hmem
      simp at hmem
    · have lim := Finset.card_le_card unusedSub
      rw [Finset.card_range] at lim
      simp only [hempty,Finset.card_empty,Nat.zero_add]
      change _≤C.gates.length+1
      omega
  · have hne_edges : H.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases hne_edges with ⟨e0, he0⟩
    have hn_pos : 0 < n := by
      rcases e0 with ⟨u0, v0⟩
      exact Fin.pos u0
    let v0 : Fin n := ⟨0, hn_pos⟩
    let A_used : Finset ℕ := (Finset.range C.gates.length).filter fun a =>
      (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
      (side (n := n) C a 0).Nonempty ∧ (side (n := n) C a 1).Nonempty
    let OrTop : Finset ℕ := (Finset.range C.gates.length).filter fun g =>
      (gateAt C g).op = GateOp.or ∧ OrReaches n C C.output g
    let OrBot : Finset ℕ := (Finset.range C.gates.length).filter fun g =>
      (gateAt C g).op = GateOp.or ∧ ¬ BelowG n G C g
    have hA_star : ∀ a ∈ A_used, (side (n := n) C a 0).card = 1 ∨ (side (n := n) C a 1).card = 1 := by
      intro a ha
      simp only [A_used, Finset.mem_filter, Finset.mem_range] at ha
      rcases ha with ⟨halt, haop, hreach, hne0, hne1⟩
      by_contra hboth
      push Not at hboth
      have hpos0 : 0 < (side (n := n) C a 0).card := Finset.Nonempty.card_pos hne0
      have hpos1 : 0 < (side (n := n) C a 1).card := Finset.Nonempty.card_pos hne1
      have hgt0 : 1 < (side (n := n) C a 0).card := by omega
      have hgt1 : 1 < (side (n := n) C a 1).card := by omega
      rcases Finset.one_lt_card.mp hgt0 with ⟨u1, hu1, u2, hu2, hune⟩
      rcases Finset.one_lt_card.mp hgt1 with ⟨w1, hw1, w2, hw2, hwne⟩
      exact no_four_cycle hNoC4 hune hwne
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu1 hw1)
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu1 hw2)
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu2 hw1)
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu2 hw2)
    let ctrSide : ℕ → Fin 2 := fun a => if (side (n := n) C a 0).card = 1 then 0 else 1
    let leafSide : ℕ → Fin 2 := fun a => 1 - ctrSide a
    let ctr : ℕ → Fin n := fun a =>
      if h : (side (n := n) C a (ctrSide a)).Nonempty then h.choose else v0
    have hctr_eq : ∀ a ∈ A_used, side (n := n) C a (ctrSide a) = {ctr a} := by
      intro a ha
      have hcard1 : (side (n := n) C a (ctrSide a)).card = 1 := by
        simp only [ctrSide]
        split_ifs with h0
        · exact h0
        · exact (hA_star a ha).resolve_left h0
      have hne_c : (side (n := n) C a (ctrSide a)).Nonempty :=
        Finset.card_pos.mp (by omega)
      have hmem_c : ctr a ∈ side (n := n) C a (ctrSide a) := by
        simp only [ctr, hne_c, ↓reduceDIte]
        exact hne_c.choose_spec
      rcases Finset.card_eq_one.mp hcard1 with ⟨c, hc⟩
      rw [hc, Finset.mem_singleton] at hmem_c
      rw [hc, hmem_c]
    have hctr_adj : ∀ a ∈ A_used, ∀ u ∈ side (n := n) C a (leafSide a), G.Adj (ctr a) u := by
      intro a ha u hu
      have hA_mem := ha
      simp only [A_used, Finset.mem_filter, Finset.mem_range] at hA_mem
      rcases hA_mem with ⟨halt, haop, hreach, _, _⟩
      have hc_mem : ctr a ∈ side (n := n) C a (ctrSide a) := by
        rw [hctr_eq a ha]; exact Finset.mem_singleton_self _
      have hcs : ctrSide a = 0 ∨ ctrSide a = 1 := by simp only [ctrSide]; split_ifs <;> simp
      rcases hcs with h0 | h1
      · have hl : leafSide a = 1 := by simp [leafSide, h0]
        rw [h0] at hc_mem
        rw [hl] at hu
        exact adj_of_and_orReaches hAO hcomp halt haop hreach hc_mem hu
      · have hl : leafSide a = 0 := by simp [leafSide, h1]
        rw [h1] at hc_mem
        rw [hl] at hu
        exact (adj_of_and_orReaches hAO hcomp halt haop hreach hu hc_mem).symm
    let S : Finset (Fin n) := A_used.image ctr
    have hS_le : S.card ≤ A_used.card := Finset.card_image_le
    have hS_cover : ∀ u v : Fin n, H.Adj u v → u ∈ S ∨ v ∈ S := by
      intro u v huv
      rcases hR1 _ _ huv with ⟨a, ha, hop, hreach, hside⟩
      have haA : a ∈ A_used := by
        simp only [A_used, Finset.mem_filter, Finset.mem_range]
        rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
        · exact ⟨ha, hop, hreach, ⟨u, hu0⟩, ⟨v, hv1⟩⟩
        · exact ⟨ha, hop, hreach, ⟨v, hv0⟩, ⟨u, hu1⟩⟩
      have hcs : ctrSide a = 0 ∨ ctrSide a = 1 := by simp only [ctrSide]; split_ifs <;> simp
      have hceq := hctr_eq a haA
      rcases hcs with h0 | h1
      · rw [h0] at hceq
        rcases hside with ⟨hu0, _⟩ | ⟨hv0, _⟩
        · rw [hceq, Finset.mem_singleton] at hu0
          exact Or.inl (Finset.mem_image.mpr ⟨a, haA, hu0.symm⟩)
        · rw [hceq, Finset.mem_singleton] at hv0
          exact Or.inr (Finset.mem_image.mpr ⟨a, haA, hv0.symm⟩)
      · rw [h1] at hceq
        rcases hside with ⟨_, hv1⟩ | ⟨_, hu1⟩
        · rw [hceq, Finset.mem_singleton] at hv1
          exact Or.inr (Finset.mem_image.mpr ⟨a, haA, hv1.symm⟩)
        · rw [hceq, Finset.mem_singleton] at hu1
          exact Or.inl (Finset.mem_image.mpr ⟨a, haA, hu1.symm⟩)
    have hdisj_A_OrTop : Disjoint A_used OrTop := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [A_used, OrTop, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      rw [hg1.2.1] at hg2
      cases hg2.2.1
    have hdisj_A_OrBot : Disjoint A_used OrBot := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [A_used, OrBot, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      rw [hg1.2.1] at hg2
      cases hg2.2.1
    have hdisj_OrTop_OrBot : Disjoint OrTop OrBot := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [OrTop, OrBot, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      exact hg2.2.2 (belowG_of_orReaches hAO hcomp hg1.2.2)
    have hsum_gates : A_used.card + OrTop.card + OrBot.card + (unusedAND n C).card ≤ C.gates.length := by
      have hdisj1 : Disjoint (A_used ∪ OrTop) OrBot :=
        Finset.disjoint_union_left.mpr ⟨hdisj_A_OrBot, hdisj_OrTop_OrBot⟩
      have hcard_u : (A_used ∪ OrTop ∪ OrBot).card = A_used.card + OrTop.card + OrBot.card := by
        rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj_A_OrTop]
      let U := A_used ∪ OrTop ∪ OrBot
      have sep : Disjoint U (unusedAND n C) := by
        apply Finset.disjoint_left.mpr
        intro j inU inJ
        obtain ⟨_,isAnd,notStar⟩ := Finset.mem_filter.mp inJ
        rcases Finset.mem_union.mp inU with left|bottom
        · rcases Finset.mem_union.mp left with star|top
          · exact notStar (Finset.mem_filter.mp star).2.2
          · have isOr := (Finset.mem_filter.mp top).2.1
            rw [isAnd] at isOr
            contradiction
        · have isOr := (Finset.mem_filter.mp bottom).2.1
          rw [isAnd] at isOr
          contradiction
      have incl : U ∪ unusedAND n C ⊆ Finset.range C.gates.length := by
        intro j hj
        rcases Finset.mem_union.mp hj with m|m
        · rcases Finset.mem_union.mp m with m|m
          · rcases Finset.mem_union.mp m with m|m <;> exact (Finset.mem_filter.mp m).1
          · exact (Finset.mem_filter.mp m).1
        · exact unusedSub m
      have bound := Finset.card_le_card incl
      rw [Finset.card_union_of_disjoint sep,Finset.card_range] at bound
      simpa only [U,hcard_u] using bound
    have hA_le_OrTop : A_used.card ≤ OrTop.card + 1 := by
      let U : Finset ℕ := A_used ∪ OrTop
      let V : Finset ℕ := U.image fun g => n + g
      have hV_card : V.card = A_used.card + OrTop.card := by
        have hinj : Function.Injective (fun g : ℕ => n + g) := add_right_injective n
        rw [Finset.card_image_of_injective U hinj, Finset.card_union_of_disjoint hdisj_A_OrTop]
      have hV_sub : V ⊆ insert C.output
          ((OrTop ×ˢ (Finset.univ : Finset (Fin 2))).image fun p => opnd C p.1 p.2) := by
        intro w hw
        simp only [V, Finset.mem_image] at hw
        rcases hw with ⟨g, hgU, rfl⟩
        have hreach : OrReaches n C C.output g := by
          simp only [U, A_used, OrTop, Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hgU
          rcases hgU with hgA | hgO
          · exact hgA.2.2.1
          · exact hgO.2.2
        rw [Finset.mem_insert]
        rcases orReaches_parent hAO C.output g hreach with hEq | ⟨h, hh, hhop, hhreach, b, hb⟩
        · exact Or.inl hEq.symm
        · right
          rw [Finset.mem_image]
          refine ⟨(h, b), ?_, hb⟩
          rw [Finset.mem_product]
          refine ⟨?_, Finset.mem_univ b⟩
          simp only [OrTop, Finset.mem_filter, Finset.mem_range]
          exact ⟨hh, hhop, hhreach⟩
      have hcard_le : V.card ≤ OrTop.card * 2 + 1 := by
        calc V.card
            ≤ (insert C.output
                ((OrTop ×ˢ (Finset.univ : Finset (Fin 2))).image fun p => opnd C p.1 p.2)).card :=
              Finset.card_le_card hV_sub
          _ ≤ ((OrTop ×ˢ (Finset.univ : Finset (Fin 2))).image fun p => opnd C p.1 p.2).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ (OrTop ×ˢ (Finset.univ : Finset (Fin 2))).card + 1 :=
              Nat.add_le_add_right Finset.card_image_le 1
          _ = OrTop.card * 2 + 1 := by simp [Finset.card_product]
      omega
    let Kc : Fin n → Finset ℕ := fun c => A_used.filter fun a => ctr a = c
    let Wc : Fin n → Finset ℕ := fun c => (Kc c).image fun a => opnd C a (leafSide a)
    let Lc : Fin n → Finset (Fin n) := fun c => (Wc c).biUnion (orIn n C)
    let Mc : Fin n → Finset ℕ := fun c => bigOrReach n C (Wc c)
    have hE_sub : H.edgeFinset ⊆ S.biUnion fun c => (Lc c).image fun u => s(c, u) := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        rcases hR1 _ _ huv with ⟨a, ha, hop, hreach, hside⟩
        have haA : a ∈ A_used := by
          simp only [A_used, Finset.mem_filter, Finset.mem_range]
          rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
          · exact ⟨ha, hop, hreach, ⟨u, hu0⟩, ⟨v, hv1⟩⟩
          · exact ⟨ha, hop, hreach, ⟨v, hv0⟩, ⟨u, hu1⟩⟩
        have hcS : ctr a ∈ S := Finset.mem_image.mpr ⟨a, haA, rfl⟩
        have haK : a ∈ Kc (ctr a) := by
          simp [Kc, haA]
        have hwW : opnd C a (leafSide a) ∈ Wc (ctr a) :=
          Finset.mem_image.mpr ⟨a, haK, rfl⟩
        rw [Finset.mem_biUnion]
        refine ⟨ctr a, hcS, ?_⟩
        rw [Finset.mem_image]
        have hcs : ctrSide a = 0 ∨ ctrSide a = 1 := by simp only [ctrSide]; split_ifs <;> simp
        have hceq := hctr_eq a haA
        rcases hcs with h0 | h1
        · have hl : leafSide a = 1 := by simp [leafSide, h0]
          rw [h0] at hceq
          rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
          · rw [hceq, Finset.mem_singleton] at hu0
            refine ⟨v, ?_, by rw [hu0]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hv1⟩
          · rw [hceq, Finset.mem_singleton] at hv0
            refine ⟨u, ?_, by rw [hv0, Sym2.eq_swap]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hu1⟩
        · have hl : leafSide a = 0 := by simp [leafSide, h1]
          rw [h1] at hceq
          rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
          · rw [hceq, Finset.mem_singleton] at hv1
            refine ⟨u, ?_, by rw [hv1, Sym2.eq_swap]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hu0⟩
          · rw [hceq, Finset.mem_singleton] at hu1
            refine ⟨v, ?_, by rw [hu1]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hv0⟩
    have hE_le : H.edgeFinset.card ≤ ∑ c ∈ S, (Lc c).card := by
      calc H.edgeFinset.card
          ≤ (S.biUnion fun c => (Lc c).image fun u => s(c, u)).card := Finset.card_le_card hE_sub
        _ ≤ ∑ c ∈ S, ((Lc c).image fun u => s(c, u)).card := Finset.card_biUnion_le
        _ ≤ ∑ c ∈ S, (Lc c).card := Finset.sum_le_sum fun c _ => Finset.card_image_le
    have hLc_le : ∀ c ∈ S, (Lc c).card ≤ (Kc c).card + (Mc c).card := by
      intro c _
      have h1 := leaf_count_bound hAO (Mc c).card (Wc c) rfl
      have h2 : (Wc c).card ≤ (Kc c).card := Finset.card_image_le
      exact le_trans h1 (Nat.add_le_add_right h2 _)
    have hK_disj : Set.PairwiseDisjoint (S : Set (Fin n)) Kc := by
      intro c1 _ c2 _ hne
      change Disjoint (Kc c1) (Kc c2)
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      simp only [Kc, Finset.mem_filter] at ha1 ha2
      exact hne (ha1.2.symm.trans ha2.2)
    have hsum_K : ∑ c ∈ S, (Kc c).card ≤ A_used.card := by
      rw [← Finset.card_biUnion hK_disj]
      apply Finset.card_le_card
      intro a ha
      rw [Finset.mem_biUnion] at ha
      rcases ha with ⟨c, _, hac⟩
      exact (Finset.mem_filter.mp hac).1
    have hM_sub : ∀ c ∈ S, Mc c ⊆ OrBot := by
      intro c _ g hg
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hg
      rcases hg with ⟨hglt, hgop, hgcard, _, _, _⟩
      simp only [OrBot, Finset.mem_filter, Finset.mem_range]
      refine ⟨hglt, hgop, ?_⟩
      intro hbelow
      have hne_g : (orIn n C (n + g)).Nonempty := Finset.card_pos.mp (by omega)
      rcases hne_g with ⟨u, hu⟩
      have hval : wireVal n C (n + g) (fun i => decide (i = u)) = true :=
        wireVal_true_of_mem_orIn hAO (by simp) (n + g) hu
      have hh : pairInput u u=(fun i => decide (i=u)) := by funext i; simp only [pairInput,or_self]
      exact (G.ne_of_adj (hbelow u u (hh.symm ▸ hval))) rfl
    have hM_disj : Set.PairwiseDisjoint (S : Set (Fin n)) Mc := by
      intro c1 _ c2 _ hne
      change Disjoint (Mc c1) (Mc c2)
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      rcases hg1 with ⟨_, _, hgcard, w1, hw1, hw1g⟩
      rcases hg2 with ⟨_, _, _, w2, hw2, hw2g⟩
      simp only [Wc, Finset.mem_image] at hw1 hw2
      rcases hw1 with ⟨a1, ha1, rfl⟩
      rcases hw2 with ⟨a2, ha2, rfl⟩
      simp only [Kc, Finset.mem_filter] at ha1 ha2
      have hgt1 : 1 < (orIn n C (n + g)).card := by omega
      rcases Finset.one_lt_card.mp hgt1 with ⟨u1, hu1, u2, hu2, hune⟩
      have hsub1 : orIn n C (n + g) ⊆ side C a1 (leafSide a1) := orIn_subset_of_orReaches hAO hw1g
      have hsub2 : orIn n C (n + g) ⊆ side C a2 (leafSide a2) := orIn_subset_of_orReaches hAO hw2g
      have h1u1 : G.Adj c1 u1 := ha1.2 ▸ hctr_adj a1 ha1.1 u1 (hsub1 hu1)
      have h1u2 : G.Adj c1 u2 := ha1.2 ▸ hctr_adj a1 ha1.1 u2 (hsub1 hu2)
      have h2u1 : G.Adj c2 u1 := ha2.2 ▸ hctr_adj a2 ha2.1 u1 (hsub2 hu1)
      have h2u2 : G.Adj c2 u2 := ha2.2 ▸ hctr_adj a2 ha2.1 u2 (hsub2 hu2)
      exact no_four_cycle hNoC4 hne hune h1u1 h1u2 h2u1 h2u2
    have hsum_M : ∑ c ∈ S, (Mc c).card ≤ OrBot.card := by
      rw [← Finset.card_biUnion hM_disj]
      apply Finset.card_le_card
      intro g hg
      rw [Finset.mem_biUnion] at hg
      rcases hg with ⟨c, hcS, hgc⟩
      exact hM_sub c hcS hgc
    have hE_bound : H.edgeFinset.card ≤ A_used.card + OrBot.card := by
      calc H.edgeFinset.card
          ≤ ∑ c ∈ S, (Lc c).card := hE_le
        _ ≤ ∑ c ∈ S, ((Kc c).card + (Mc c).card) := Finset.sum_le_sum hLc_le
        _ = (∑ c ∈ S, (Kc c).card) + ∑ c ∈ S, (Mc c).card := Finset.sum_add_distrib
        _ ≤ A_used.card + OrBot.card := Nat.add_le_add hsum_K hsum_M
    refine ⟨S, hS_cover, ?_⟩
    change H.edgeFinset.card + S.card + (unusedAND n C).card ≤ C.gates.length + 1
    omega

end Dyads3791

namespace Normalize3791

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

private abbrev bank {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  (Circuit.mk gs 0).wires (List.ofFn x)

private theorem bankLength {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (bank gs x).length = n + gs.length := by
  have len (l : List Bool) (q : List Gate) :
      ((Circuit.mk q 0).wires l).length = l.length + q.length := by
    induction q generalizing l with
    | nil => simp [Circuit.wires]
    | cons g q ih =>
      simp only [Circuit.wires, List.foldl_cons] at ih ⊢
      rw [ih]
      simp
      omega
  simpa using len (List.ofFn x) gs

private theorem bankSnoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    bank (gs ++ [g]) x = bank gs x ++
      [g.op.eval (g.inputs.map fun j => (bank gs x).getD j false)] := by
  simp [Circuit.wires, List.foldl_append]

private abbrev Fits {n : ℕ} (gs : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ b, ∀ x, f x = b) ∨
    ∃ i < n + gs.length, ∀ x, f x = (bank gs x).getD i false

private theorem extend {n : ℕ} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (g : Gate) (h : Fits gs f) : Fits (gs ++ [g]) f := by
  rcases h with h | ⟨i, hi, he⟩
  · exact Or.inl h
  · refine Or.inr ⟨i, by simp; omega, fun x => ?_⟩
    rw [bankSnoc, List.getD_append _ _ _ _ (by simpa only [bankLength] using hi)]
    exact he x

private theorem addGate {n : ℕ} (gs : List Gate) (g : Gate)
    (hs : IsAO2 n (Circuit.mk gs 0))
    (ho : g.op = .and ∨ g.op = .or) (hq : g.inputs.length = 2)
    (hr : ∀ i ∈ g.inputs, i < n + gs.length) :
    IsAO2 n (Circuit.mk (gs ++ [g]) 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hs.1 a ha
    · rwa [List.mem_singleton.mp ha]
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD] at hi
    by_cases h : j < gs.length
    · apply hs.2.1 j h
      simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_append_left h] using hi
    · have he : j = gs.length := by simp at hj; omega
      subst j
      have hi' : i ∈ g.inputs := by simpa using hi
      exact hr i hi'
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hs.2.2 a ha
    · rwa [List.mem_singleton.mp ha]

private theorem combine {n : ℕ} (gs : List Gate) (hs : IsAO2 n (Circuit.mk gs 0))
    (op : GateOp) (ho : op = .and ∨ op = .or)
    (a b : (Fin n → Bool) → Bool) (ha : Fits gs a) (hb : Fits gs b) :
    ∃ extra : List Gate, extra.length ≤ 1 ∧
      IsAO2 n (Circuit.mk (gs ++ extra) 0) ∧ Fits (gs ++ extra) (fun x => op.eval [a x, b x]) := by
  have reuse (f : (Fin n → Bool) → Bool) (hf : Fits gs f)
      (he : ∀ x, op.eval [a x, b x] = f x) :
      ∃ extra : List Gate, extra.length ≤ 1 ∧ IsAO2 n (Circuit.mk (gs ++ extra) 0) ∧
        Fits (gs ++ extra) (fun x => op.eval [a x, b x]) := by
    refine ⟨[], by simp, by simpa using hs, ?_⟩
    simpa only [List.append_nil, funext he] using hf
  have constant (v : Bool) : Fits gs (fun _ : Fin n → Bool => v) := Or.inl ⟨v, fun _ => rfl⟩
  rcases ha with ⟨u, hu⟩ | ⟨i, hi, hai⟩
  · rcases ho with rfl | rfl <;> cases u
    · exact reuse _ (constant false) fun x => by simp [GateOp.eval, hu]
    · exact reuse b hb fun x => by simp [GateOp.eval, hu]
    · exact reuse b hb fun x => by simp [GateOp.eval, hu]
    · exact reuse _ (constant true) fun x => by simp [GateOp.eval, hu]
  · rcases hb with ⟨v, hv⟩ | ⟨j, hj, hbj⟩
    · have ha : Fits gs a := Or.inr ⟨i, hi, hai⟩
      rcases ho with rfl | rfl <;> cases v
      · exact reuse _ (constant false) fun x => by simp [GateOp.eval, hv]
      · exact reuse a ha fun x => by simp [GateOp.eval, hv]
      · exact reuse a ha fun x => by simp [GateOp.eval, hv]
      · exact reuse _ (constant true) fun x => by simp [GateOp.eval, hv]
    · let g : Gate := ⟨op, [i, j]⟩
      refine ⟨[g], by simp, addGate gs g hs ho rfl ?_, Or.inr ⟨n + gs.length, by simp, ?_⟩⟩
      · intro k hk
        simp [g] at hk
        rcases hk with rfl | rfl <;> assumption
      · intro x
        rw [bankSnoc, ← bankLength gs x, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
        simp [g, hai, hbj]

private theorem normalize (n : ℕ) (source : List Gate) (hsource : Monotone2 (Circuit.mk source 0)) :
    ∃ target : List Gate, IsAO2 n (Circuit.mk target 0) ∧ target.length ≤ source.length ∧
      ∀ j, Fits target (fun x : Fin n → Bool => (bank source x).getD j false) := by
  have empty : IsAO2 n (Circuit.mk [] 0) :=
    ⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly], by simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack],
      by simp⟩
  induction source using List.reverseRecOn with
  | nil =>
    refine ⟨[], empty, le_rfl, fun j => ?_⟩
    by_cases h : j < n
    · exact Or.inr ⟨j, by simpa using h, fun _ => rfl⟩
    · refine Or.inl ⟨false, fun x => List.getD_eq_default _ _ ?_⟩
      rw [bankLength]; simp; omega
  | append_singleton gs g ih =>
    obtain ⟨ds, hd, hs, rep⟩ := ih (fun q hq => hsource q (List.mem_append_left _ hq))
    have hGate := hsource g (List.mem_append_right _ (by simp))
    have hop : g.op = .and ∨ g.op = .or := by simpa using hGate.1
    have add : ∃ extra : List Gate, extra.length ≤ 1 ∧ IsAO2 n (Circuit.mk (ds ++ extra) 0) ∧
        Fits (ds ++ extra) (fun x : Fin n → Bool => g.op.eval (g.inputs.map fun j => (bank gs x).getD j false)) := by
      have hlen := hGate.2
      match hin : g.inputs, hlen with
      | [], _ => exact ⟨[], by simp, by simpa using hd, Or.inl ⟨g.op.eval [], fun x => by simp [hin]⟩⟩
      | [a], _ =>
        refine ⟨[], by simp, by simpa using hd, ?_⟩
        rcases hop with ho | ho <;> simpa [hin, ho, GateOp.eval] using rep a
      | [a, b], _ => simpa [hin] using combine ds hd g.op hop _ _ (rep a) (rep b)
    obtain ⟨extra, he, ho, hr⟩ := add
    refine ⟨ds ++ extra, ho, by simp; omega, fun j => ?_⟩
    by_cases h : j < n + gs.length
    · have e (x : Fin n → Bool) : (bank (gs ++ [g]) x).getD j false = (bank gs x).getD j false := by
        rw [bankSnoc, List.getD_append _ _ _ _ (by simpa only [bankLength] using h)]
      simp only [e]
      match extra, he with
      | [], _ => simpa using rep j
      | [q], _ => exact extend q (rep j)
    · by_cases eq : j = n + gs.length
      · have e (x : Fin n → Bool) : (bank (gs ++ [g]) x).getD j false =
            g.op.eval (g.inputs.map fun k => (bank gs x).getD k false) := by
          rw [bankSnoc, eq, ← bankLength gs x, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
          rfl
        simpa only [e] using hr
      · apply Or.inl
        refine ⟨false, fun x => List.getD_eq_default _ _ ?_⟩
        rw [bankLength]; simp; omega

theorem result (n : ℕ) (C : Circuit) (hC : Monotone2 C) :
    (∃ b, ∀ x : Fin n → Bool, circuitFun n C x = b) ∨
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C x := by
  obtain ⟨gs, h, hs, rep⟩ := normalize n C.gates hC
  rcases rep C.output with hc | ⟨i, _, hi⟩
  · exact Or.inl hc
  · exact Or.inr ⟨⟨gs, i⟩, h, hs, fun x => (hi x).symm⟩

end Normalize3791

namespace Quad3791
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
set_option maxRecDepth 32768
set_option maxHeartbeats 0
abbrev V := Fin 26
def edges : List (Nat × Nat) := [(0, 13), (0, 17), (0, 23), (0, 25), (1, 13), (1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 13), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 13), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)]
def rel (a b : V) := (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges
instance (a b : V) : Decidable (rel a b) := by unfold rel; infer_instance
def G : SimpleGraph V where
  Adj := rel
  symm := ⟨fun a b h => Or.symm h⟩
  loopless := by
    have h : ∀ a : V, ¬rel a a := by decide +kernel
    exact ⟨h⟩
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (rel a b))
theorem c4 : NoFourCycle G := by decide +kernel
theorem edgeCount : G.edgeFinset.card = 52 := by decide +kernel
def leftPoint (i : Fin 13) : V :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List V).getD i.val 0

def rightLine (i : Fin 13) : V := ⟨13+i.val,by omega⟩

private theorem matched : ∀ i : Fin 13, G.Adj (leftPoint i) (rightLine i) := by decide +kernel

private theorem apart : ∀ i j : Fin 13, i ≠ j →
    leftPoint i ≠ leftPoint j ∧ leftPoint i ≠ rightLine j ∧
    rightLine i ≠ leftPoint j ∧ rightLine i ≠ rightLine j := by decide +kernel

theorem coverCount (S : Finset V) (covers : ∀ a b : V, G.Adj a b → a ∈ S ∨ b ∈ S) :
    13 ≤ S.card := by
  let pick (i : Fin 13) : V := if leftPoint i ∈ S then leftPoint i else rightLine i
  have chosen (i : Fin 13) : pick i ∈ S := by
    by_cases h : leftPoint i ∈ S
    · simpa [pick,h] using h
    · simpa [pick,h] using (covers _ _ (matched i)).resolve_left h
  have injective : Function.Injective pick := by
    intro i j eq
    by_contra ne
    obtain ⟨hll,hlr,hrl,hrr⟩ := apart i j ne
    by_cases hi : leftPoint i ∈ S <;> by_cases hj : leftPoint j ∈ S <;>
      simp only [pick,hi,hj,ite_true,ite_false] at eq
    · exact hll eq
    · exact hlr eq
    · exact hrl eq
    · exact hrr eq
  let f (i : Fin 13) : {v // v ∈ S} := ⟨pick i,chosen i⟩
  have bound := Fintype.card_le_of_injective f (fun i j eq =>
    injective (congrArg Subtype.val eq))
  simpa using bound


abbrev I := Fin 13
def D : Finset I := {0,1,3,9}
def flag (p l : I) := (List.ofFn fun t : I => decide (t=p)) ++ List.ofFn fun t : I => decide (t=l)
def pnum (a b : V) : I := Fin.ofNat 13 (min a.val b.val)
def lnum (a b : V) : I := Fin.ofNat 13 (max a.val b.val-13)
theorem hit : ∀ a b : V,G.Adj a b → pnum a b-lnum a b∈D ∧
    List.ofFn (pairInput a b)=flag (pnum a b) (lnum a b) := by decide +kernel
def avoidance : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 4, 2, 3, 2, 2, 2, 2, 2, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 5, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 4, 2, 2, 2, 4, 2, 2, 2, 2, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1]

def board (p q l m : I) : List Bool :=
  (List.ofFn fun i : I => decide (i=p ∨ i=q)) ++ List.ofFn fun i : I => decide (i=l ∨ i=m)
def score (p q l m : I) := decide (p-l∈D ∨ p-m∈D ∨ q-l∈D ∨ q-m∈D)
def avoid (a b : V) : I := Fin.ofNat 13
  ((avoidance : List Nat).getD (min a.val b.val * 26 + max a.val b.val) 0)
def point (a b : V) : I := if a.val<13 then Fin.ofNat 13 a.val else if b.val<13 then Fin.ofNat 13 b.val else avoid a b
def line (a b : V) : I := if 13≤a.val then Fin.ofNat 13 (a.val-13) else if 13≤b.val then Fin.ofNat 13 (b.val-13) else avoid a b
def filler (a b : V) := board (point a b) (point b a) (line a b) (line b a)
theorem avoids : ∀ a b : V, ¬ G.Adj a b →
    score (point a b) (point b a) (line a b) (line b a) = false ∧
    (filler a b).getD a.val false = true ∧ (filler a b).getD b.val false = true := by decide +kernel
def join (C : Circuit) (a b : Nat) : Circuit := ⟨C.gates++[⟨.or,[a,b]⟩],26+C.size⟩
theorem join_read (C : Circuit) (a b : Nat) (x : List Bool) (len : x.length=26) :
    (join C a b).eval x = ((C.wires x).getD a false || (C.wires x).getD b false) := by
  let u := PlaneOrdered.wf C.gates x
  have sz : u.length=26+C.size := by simp [u,PlaneOrdered.wf_len,Circuit.size,len]
  change (PlaneOrdered.wf (C.gates++[⟨GateOp.or,[a,b]⟩]) x).getD (26+C.size) false=_
  unfold PlaneOrdered.wf
  rw [List.foldl_append]
  change (u++[_]).getD (26+C.size) false=_
  rw [←sz,PlaneOrdered.getD_snoc_eq]
  simp [GateOp.eval,u,PlaneOrdered.wf,Circuit.wires]

def Tests (C : Circuit) (a b : Nat) := ∀ p q l m : I,
    ((C.wires (board p q l m)).getD a false || (C.wires (board p q l m)).getD b false) = score p q l m

theorem pair_exact (C : Circuit) (a b : Nat) (mono : Monotone2 C) (h : Tests C a b) :
    Dyads3791.ExactPairs G (join C a b) := by
  intro i j
  change (join C a b).eval (List.ofFn (pairInput i j))=_
  rw [join_read _ _ _ _ (by simp)]
  by_cases inc : G.Adj i j
  · obtain ⟨member,eq⟩ := hit i j inc
    rw [eq,decide_eq_true inc]
    simpa [board, flag, score, member] using h (pnum i j) (pnum i j) (lnum i j) (lnum i j)
  · rw [decide_eq_false inc,Bool.or_eq_false_iff]
    obtain ⟨zero,pi,pj⟩ := avoids i j inc
    have wh := h (point i j) (point j i) (line i j) (line j i)
    rw [zero] at wh
    have no := Bool.or_eq_false_iff.mp wh
    have lift (w : Nat) : (C.wires (List.ofFn (pairInput i j))).getD w false=true →
        (C.wires (filler i j)).getD w false=true := by
      apply PlaneOrdered.mono2 C.gates (fun g hg => by simpa using mono g hg)
      · simp [filler,board]
      · intro k on
        by_cases lt : k<26
        · have hh : (⟨k,lt⟩ : V)=i ∨ (⟨k,lt⟩ : V)=j := by
            simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos lt,Option.getD_some,
              pairInput,decide_eq_true_eq] using on
          rcases hh with hi | hj
          · have eq : k=i.val := congrArg Fin.val hi
            rw [eq]
            exact pi
          · have eq : k=j.val := congrArg Fin.val hj
            rw [eq]
            exact pj
        · rw [List.getD_eq_default _ _ (by simp; omega)] at on
          contradiction
    exact ⟨Bool.eq_false_iff.mpr (fun y => Bool.noConfusion ((lift a y).symm.trans no.1)),
      Bool.eq_false_iff.mpr (fun y => Bool.noConfusion ((lift b y).symm.trans no.2))⟩

theorem simple_flags_bound (C : Circuit) (a b : Nat) (mono : Monotone2 C) (h : Tests C a b)
    (ao : IsAO2 26 (join C a b)) (simple : Dyads3791.SimpleFlags G (join C a b)) : 63≤C.size := by
  obtain ⟨S,covers,price⟩ := Dyads3791.count_dyads 26 G (join C a b) c4 ao (pair_exact C a b mono h) simple
  have c := coverCount S covers
  have sz : (join C a b).size=C.size+1 := by simp [join,Circuit.size]
  rw [edgeCount,sz] at price
  omega
theorem partial_edges_price (C : Circuit) (a b : Nat) (mono : Monotone2 C) (tests : Tests C a b)
    (ao : IsAO2 26 (join C a b)) (H : SimpleGraph V) [DecidableRel H.Adj]
    (simple : ∀u v,H.Adj u v → Dyads3791.Routed 26 (join C a b) u v) :
    ∃ S : Finset V,(∀ u v,H.Adj u v → u∈S ∨ v∈S) ∧
      H.edgeFinset.card+S.card+(Dyads3791.unusedAND 26 (join C a b)).card≤C.size+2 := by
  obtain ⟨S,covers,bound⟩ := Dyads3791.count_subgraph 26 G H (join C a b) c4 ao (pair_exact C a b mono tests) simple
  refine ⟨S,covers,?_⟩
  have sz : (join C a b).size=C.size+1 := by simp [join,Circuit.size]
  rw [sz] at bound
  omega
theorem direct_symm (n : Nat) (C : Circuit) (p q : Fin n) :
    Dyads3791.Routed n C p q → Dyads3791.Routed n C q p := by
  rintro ⟨j,hj,op,reaches,side⟩
  exact ⟨j,hj,op,reaches,side.symm⟩

def directGraph (T : Circuit) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ Dyads3791.Routed 26 T u v
  symm := ⟨fun u v h => ⟨Or.symm h.1,direct_symm _ _ _ _ h.2⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

noncomputable instance (T : Circuit) : DecidableRel (directGraph T).Adj :=
  fun _ _ => Classical.propDecidable _

def Carries (T : Circuit) (j : ℕ) (e : Sym2 V) : Prop :=
  ∃ p q : V, e=s(p,q) ∧ wireVal 26 T (26+j) (pairInput p q)=true

noncomputable def missing (T : Circuit) := G.edgeFinset \ (directGraph T).edgeFinset

theorem edge_charge (T : Circuit) (ao : IsAO2 26 T) (eq : Dyads3791.ExactPairs G T) :
    (missing T).card ≤ (Dyads3791.unusedAND 26 T).card ∨
    ∃ j∈Dyads3791.unusedAND 26 T, ∃ e∈missing T, ∃ f∈missing T,
      e ≠ f ∧ Carries T j e ∧ Carries T j f := by
  classical
  have chooseGate (e : {e // e∈missing T}) :
      ∃ j : {j // j∈Dyads3791.unusedAND 26 T}, Carries T j.val e.val := by
    obtain ⟨e,he⟩ := e
    induction e using Sym2.ind with
    | _ p q =>
      obtain ⟨edge,abs⟩ := Finset.mem_sdiff.mp he
      have inc := SimpleGraph.mem_edgeFinset.mp edge
      have bad : ¬Dyads3791.Routed 26 T p q := fun yes =>
        abs (SimpleGraph.mem_edgeFinset.mpr (show (directGraph T).Adj p q from ⟨inc,yes⟩))
      obtain ⟨j,hj,on⟩ := Dyads3791.unrouted_reader ao eq p q inc bad
      exact ⟨⟨j,hj⟩,p,q,rfl,on⟩
  let f (e : {e // e∈missing T}) := Classical.choose (chooseGate e)
  have active (e : {e // e∈missing T}) : Carries T (f e).val e.val :=
    Classical.choose_spec (chooseGate e)
  by_cases inj : Function.Injective f
  · exact Or.inl (by simpa using Fintype.card_le_of_injective f inj)
  · apply Or.inr
    unfold Function.Injective at inj
    push_neg at inj
    obtain ⟨e,k,same,diff⟩ := inj
    refine ⟨(f e).val,(f e).property,e.val,e.property,k.val,k.property,
      fun h => diff (Subtype.ext h),active e,?_⟩
    rw [same]
    exact active k

theorem matching_or_shared (C : Circuit) (a b : Nat) (mono : Monotone2 C) (tests : Tests C a b)
    (ao : IsAO2 26 (join C a b)) (small : C.size≤62) :
    let T := join C a b
    (∃ S : Finset V, S.card≤12 ∧ ∀p q,(directGraph T).Adj p q → p∈S ∨ q∈S) ∨
    ∃ j∈Dyads3791.unusedAND 26 T, ∃ e∈missing T, ∃ f∈missing T,
      e ≠ f ∧ Carries T j e ∧ Carries T j f := by
  classical
  let T := join C a b
  change (∃ S : Finset V, S.card≤12 ∧ ∀p q,(directGraph T).Adj p q → p∈S ∨ q∈S) ∨ _
  have sub : (directGraph T).edgeFinset ⊆ G.edgeFinset := by
    intro e h
    induction e using Sym2.ind with
    | _ u v => exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.mem_edgeFinset.mp h).1
  have total : (missing T).card+(directGraph T).edgeFinset.card=52 := by
    have le := Finset.card_le_card sub
    rw [edgeCount] at le
    rw [missing,Finset.card_sdiff_of_subset sub,edgeCount]
    omega
  rcases edge_charge T ao (pair_exact _ _ _ mono tests) with low|coll
  · obtain ⟨S,cov,price⟩ := partial_edges_price C a b mono tests ao (directGraph T)
        (fun _ _ h => h.2)
    refine Or.inl ⟨S,?_,cov⟩
    change (directGraph T).edgeFinset.card + S.card + (Dyads3791.unusedAND 26 T).card ≤ C.size+2 at price
    omega
  · exact Or.inr coll

def touch (v : V) := G.edgeFinset.filter fun e => v ∈ e
theorem touch_four : ∀ v : V, (touch v).card=4 := by decide +kernel

theorem degree_budget (T : Circuit) (S : Finset V) (cov : ∀p q,(directGraph T).Adj p q → p∈S ∨ q∈S) :
    (directGraph T).edgeFinset.card ≤ S.card*4 := by
  classical
  have inc : (directGraph T).edgeFinset ⊆ S.biUnion touch := by
    intro e he
    induction e using Sym2.ind with
    | _ p q =>
      have adj := SimpleGraph.mem_edgeFinset.mp he
      have mem : s(p,q) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr adj.1
      rcases cov p q adj with hp|hq
      · exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨mem,by simp⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨q,hq,Finset.mem_filter.mpr ⟨mem,by simp⟩⟩
  calc
    _ ≤ (S.biUnion touch).card := Finset.card_le_card inc
    _ ≤ ∑ v∈S,(touch v).card := Finset.card_biUnion_le
    _ = _ := by simp [touch_four]

def collision (T : Circuit) : Prop :=
    ∃ j∈Dyads3791.unusedAND 26 T, ∃ e∈missing T, ∃ f∈missing T,
      e ≠ f ∧ Carries T j e ∧ Carries T j f

theorem physical_obstruction (T : Circuit) (ao : IsAO2 26 T)
    (eq : Dyads3791.ExactPairs G T) (small : T.size≤63) :
    (4≤(missing T).card ∧ ∃ S : Finset V,S.card≤12 ∧
      ∀p q,(directGraph T).Adj p q → p∈S ∨ q∈S) ∨ collision T := by
  classical
  have sub : (directGraph T).edgeFinset ⊆ G.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ p q => exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.mem_edgeFinset.mp he).1
  have total : (missing T).card+(directGraph T).edgeFinset.card=52 := by
    have le := Finset.card_le_card sub
    rw [edgeCount] at le
    rw [missing, Finset.card_sdiff_of_subset sub,edgeCount]
    omega
  rcases edge_charge T ao eq with low|coll
  · obtain ⟨S,cov,price⟩ := Dyads3791.count_subgraph 26 G (directGraph T) T c4 ao eq
      (fun _ _ h => h.2)
    have budget := degree_budget T S cov
    exact Or.inl ⟨by omega,S,by omega,cov⟩
  · exact Or.inr coll

theorem normalized_obstruction (C : Circuit) (a b : Nat) (mono : Monotone2 C)
    (tests : Tests C a b) (small : C.size≤62) :
    ∃ T : Circuit, IsAO2 26 T ∧ T.size≤C.size+1 ∧
      (∀ x : V→Bool, circuitFun 26 T x=circuitFun 26 (join C a b) x) ∧
      ((4≤(missing T).card ∧ ∃ S : Finset V,S.card≤12 ∧
        ∀p q,(directGraph T).Adj p q → p∈S ∨ q∈S) ∨ collision T) := by
  have mo : Monotone2 (join C a b) := by
    intro g mem
    change g∈C.gates++[⟨GateOp.or,[a,b]⟩] at mem
    rcases List.mem_append.mp mem with old|last
    · exact mono g old
    · rcases List.mem_singleton.mp last with rfl
      exact ⟨by simp, by change 2 ≤ 2; exact le_rfl⟩
  have eq := pair_exact C a b mono tests
  rcases Normalize3791.result 26 (join C a b) mo with ⟨k,constant⟩|⟨T,ao,sz,same⟩
  · have on := matched 0
    have pos := eq (leftPoint 0) (rightLine 0)
    have neg := eq (leftPoint 0) (leftPoint 0)
    rw [decide_eq_true on,constant] at pos
    rw [decide_eq_false (fun h => G.ne_of_adj h rfl),constant] at neg
    exact False.elim (Bool.noConfusion (pos.symm.trans neg))
  · have size : (join C a b).size=C.size+1 := by simp [join,Circuit.size]
    rw [size] at sz
    refine ⟨T,ao,sz,same,physical_obstruction T ao ?_ (by omega)⟩
    intro p q
    exact (same _).trans (eq p q)

theorem two_unrouted (T : Circuit) (ao : IsAO2 26 T)
    (eq : Dyads3791.ExactPairs G T) (small : T.size≤63) : 2≤(missing T).card := by
  rcases physical_obstruction T ao eq small with ⟨h,_⟩|⟨_,_,e,he,f,hf,ne,_⟩
  · omega
  · exact Finset.one_lt_card.mpr ⟨e,he,f,hf,ne⟩

end Quad3791

end PEqualNP.Outside.L_meta_7290
