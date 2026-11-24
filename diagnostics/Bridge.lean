import Mathlib
import PEqualNP.Defs

namespace PEqualNP.MetaComplexity.ReadTwoBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.ReadK

/-! ## Folds that append one entry per gate -/

theorem foldl_snoc_prefix {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_prefix {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_init {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d
      = init.getD i d :=
  getD_of_prefix (foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _) hi d

theorem foldl_snoc_beyond {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : init.length + gs.length ≤ i) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d = d := by
  apply List.getD_eq_default
  rw [foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
  exact hi

theorem foldl_snoc_gate {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < init.length + j) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD
        (init.length + j) d
      = G (gs[j].inputs.map fun i =>
          (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d)
          gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init
    with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
    simp; omega
  have hpre : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]) <+:
      gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _
  have hpre2 := (List.prefix_append P _).trans hpre
  rw [getD_of_prefix hpre (by simp; omega)]
  have e1 : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]).getD (init.length + j) d
      = G (gs[j].inputs.map fun i => P.getD i d) gs[j] := by
    rw [← hPl]; simp
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_of_prefix hpre2 (by rw [hPl]; exact hrb i hi)]

/-! ## The two folds of the root, in that form -/

/-- The gate step of `readVectors`, as a function of the input sets. -/
def rvG (S : List ℕ) (k : ℕ) (ins : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

theorem rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl
      (fun R g => R ++ [rvG S k (g.inputs.map fun i => R.getD i []) g])
      ((List.range n).map (leafVectors S k)) := rfl

theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl
      (fun R g => R ++ [(fun ins (g : Gate) => g.op.eval ins) (g.inputs.map fun i => R.getD i false) g])
      x := rfl

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

/-! ## Per-wire facts -/

section Wires

variable (C : Circuit) (n : ℕ)

/-- The vector set of wire `x` for the list `S`, at cap `k = 2`. -/
abbrev A (S : List ℕ) (x : ℕ) : List (List ℕ) := (readVectors C n S 2).getD x []

theorem A_input (S : List ℕ) (x : ℕ) (hx : x < n) : A C n S x = leafVectors S 2 x := by
  unfold A
  rw [rv_eq, foldl_snoc_init _ _ _ _ _ (by simpa using hx)]
  simp [List.getD_eq_getElem?_getD, hx]

theorem A_beyond (S : List ℕ) (x : ℕ) (hx : n + C.gates.length ≤ x) : A C n S x = [] := by
  unfold A
  rw [rv_eq, foldl_snoc_beyond _ _ _ _ _ (by simpa using hx)]

theorem A_gate (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    A C n S (n + j) = rvG S 2 ((gateAt C j).inputs.map (A C n S)) (gateAt C j) := by
  unfold A
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (rvG S 2) [] ((List.range n).map (leafVectors S 2)) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_map, List.length_range] at this
  rw [rv_eq, this]

/-- The value of wire `i` on input `x`. -/
abbrev W (x : Fin n → Bool) (i : ℕ) : Bool := (C.wires (List.ofFn x)).getD i false

theorem W_input (x : Fin n → Bool) (i : ℕ) (hi : i < n) : W C n x i = x ⟨i, hi⟩ := by
  unfold W
  rw [wires_eq, foldl_snoc_init (fun ins (g : Gate) => g.op.eval ins) false _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem W_gate (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    W C n x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C n x)) := by
  unfold W
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (fun ins (g : Gate) => g.op.eval ins) false (List.ofFn x) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_ofFn] at this
  rw [wires_eq, this]

end Wires

/-! ## Membership in the root's set operations -/

theorem mem_insertNew {B : List (List ℕ)} {v a : List ℕ} :
    v ∈ insertNew B a ↔ v ∈ B ∨ v = a := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h' | rfl) <;> assumption
  · simp

theorem mem_foldl_insertNew (l acc : List (List ℕ)) (v : List ℕ) :
    v ∈ l.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, mem_insertNew]; simp; tauto

theorem mem_orFold (ins : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ) :
    v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ B ∈ ins, v ∈ B := by
  induction ins generalizing acc with
  | nil => simp
  | cons B ins ih => rw [List.foldl_cons, ih, mem_foldl_insertNew]; simp; tauto

theorem mem_andStep (k : ℕ) (P Q : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k P Q ↔ ∃ a ∈ P, ∃ b ∈ Q, v = capAdd k a b := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

/-! ## Skeleton trees as an inductive predicate -/

section Trees

variable (C : Circuit) (n : ℕ)

/-- OR-only upward paths, exactly the relation of the statement. -/
def Rr : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs)

/-- The trees of the statement's `T`, as an inductive predicate. -/
inductive Tr : ℕ → List (ℕ × ℕ) → Prop
  | leaf (qv qt : ℕ) : qv < n → Rr C n qv qt → Tr qt [(qt, qv)]
  | node (qj qt : ℕ) (L1 L2 : List (ℕ × ℕ)) : qj < C.gates.length →
      (gateAt C qj).op = GateOp.and → Rr C n (n + qj) qt →
      Tr ((gateAt C qj).inputs.getD 0 0) L1 → Tr ((gateAt C qj).inputs.getD 1 0) L2 →
      Tr qt (L1 ++ L2)

theorem Tr.toT {t : ℕ} {L : List (ℕ × ℕ)} (h : Tr C n t L) (Q : ℕ → List (ℕ × ℕ) → Prop)
    (hl : ∀ (qv qt : ℕ), qv < n → Rr C n qv qt → Q qt [(qt, qv)])
    (hn : ∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
      (gateAt C qj).op = GateOp.and → Rr C n (n + qj) qt →
      Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
      Q qt (qL1 ++ qL2)) : Q t L := by
  induction h with
  | leaf qv qt hv hr => exact hl qv qt hv hr
  | node qj qt L1 L2 hj ha hr _ _ ih1 ih2 => exact hn qj qt L1 L2 hj ha hr ih1 ih2

theorem Tr.lift {t t' : ℕ} {L : List (ℕ × ℕ)} (h : Tr C n t L) (hr : Rr C n t t') :
    ∃ L', Tr C n t' L' ∧ L'.map Prod.snd = L.map Prod.snd := by
  cases h with
  | leaf qv _ hv hr0 => exact ⟨_, Tr.leaf qv t' hv (hr0.trans hr), rfl⟩
  | node qj _ L1 L2 hj ha hr0 h1 h2 => exact ⟨_, Tr.node qj t' L1 L2 hj ha (hr0.trans hr) h1 h2, rfl⟩

end Trees

/-! ## Realization: every vector of a wire is the capped leaf count of a tree hanging from it -/

theorem realize (C : Circuit) (n u w : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ x, ∀ v ∈ A C n [u, w] x, ∃ L, Tr C n x L ∧ (∀ a ∈ L.map Prod.snd, a = u ∨ a = w) ∧
      v = [min ((L.map Prod.snd).count u) 3, min ((L.map Prod.snd).count w) 3] := by
  obtain ⟨hao, hrb, h2⟩ := hC
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro v hv
  by_cases hxn : x < n
  · rw [A_input C n _ x hxn] at hv
    simp only [leafVectors] at hv
    split_ifs at hv with hmem
    · simp only [List.mem_singleton] at hv
      refine ⟨[(x, x)], Tr.leaf x x hxn Relation.ReflTransGen.refl, ?_, ?_⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton]
        rintro a rfl
        simpa using hmem
      · subst hv
        simp only [List.map_cons, List.map_nil, List.count_singleton]
        by_cases hu : u = x
        · subst hu
          by_cases hw : w = u
          · subst hw; simp
          · simp [hw, Ne.symm hw]
        · by_cases hw : w = x
          · subst hw; simp [hu, Ne.symm hu]
          · simp [hu, hw, Ne.symm hu, Ne.symm hw]
    · simp at hv
  · obtain ⟨j, rfl⟩ : ∃ j, x = n + j := ⟨x - n, by omega⟩
    by_cases hj : j < C.gates.length
    swap
    · rw [A_beyond C n _ _ (by omega)] at hv; simp at hv
    have hrbj := hrb j hj
    rw [A_gate C n _ j hj hrbj] at hv
    have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hj]; exact List.getElem_mem hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ hg)
    have ha : a < n + j := hrbj a (by simp [hab])
    have hb : b < n + j := hrbj b (by simp [hab])
    rcases hao _ hg with hop | hop
    · -- AND
      simp only [rvG, hop, hab, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
        List.map_cons, List.map_nil] at hv
      rw [mem_andStep] at hv
      obtain ⟨p, hp, q, hq, rfl⟩ := hv
      rw [mem_andStep] at hp
      obtain ⟨z, hz, p0, hp0, rfl⟩ := hp
      simp only [List.mem_singleton] at hz
      subst hz
      obtain ⟨L1, hT1, hl1, rfl⟩ := ih a ha p0 hp0
      obtain ⟨L2, hT2, hl2, rfl⟩ := ih b hb q hq
      refine ⟨L1 ++ L2, Tr.node j (n + j) L1 L2 hj hop Relation.ReflTransGen.refl
        (by simpa [hab] using hT1) (by simpa [hab] using hT2), ?_, ?_⟩
      · intro c hc
        simp only [List.map_append, List.mem_append] at hc
        rcases hc with hc | hc
        · exact hl1 c hc
        · exact hl2 c hc
      · simp only [capAdd, List.map_append, List.count_append, List.zipWith_cons_cons,
          List.zipWith_nil_right, List.cons.injEq, and_true]
        constructor <;> omega
    · -- OR
      simp only [rvG, hop, hab, List.map_cons, List.map_nil] at hv
      rw [mem_orFold] at hv
      simp only [false_or, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left] at hv
      have step : ∀ c, c < n + j → c ∈ (gateAt C j).inputs → Rr C n c (n + j) := fun c hc hci =>
        Relation.ReflTransGen.single ⟨hc, j, rfl, hj, hop, hci⟩
      rcases hv with hv | hv
      · obtain ⟨L, hT, hl, rfl⟩ := ih a ha v hv
        obtain ⟨L', hT', hm⟩ := hT.lift C n (step a ha (by simp [hab]))
        exact ⟨L', hT', by rw [hm]; exact hl, by rw [hm]⟩
      · obtain ⟨L, hT, hl, rfl⟩ := ih b hb v hv
        obtain ⟨L', hT', hm⟩ := hT.lift C n (step b hb (by simp [hab]))
        exact ⟨L', hT', by rw [hm]; exact hl, by rw [hm]⟩

theorem realize_len2 (C : Circuit) (n u w : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) (x : ℕ)
    (v : List ℕ) (hv : v ∈ A C n [u, w] x) : ∃ c d, v = [c, d] := by
  obtain ⟨L, -, -, rfl⟩ := realize C n u w hC x v hv
  exact ⟨_, _, rfl⟩

/-! ## Soundness: a tree whose leaves are true makes its wire true -/

theorem Rr.val (C : Circuit) (n : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool)
    {a b : ℕ} (h : Rr C n a b) (ha : W C n x a = true) : W C n x b = true := by
  induction h with
  | refl => exact ha
  | tail _ hst ih =>
    obtain ⟨_, rj, rfl, hj, hop, hmem⟩ := hst
    rw [W_gate C n x rj hj (hC.2.1 rj hj), hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    exact ⟨_, ⟨_, hmem, rfl⟩, ih⟩

theorem Tr.val (C : Circuit) (n : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool)
    {t : ℕ} {L : List (ℕ × ℕ)} (h : Tr C n t L) (hL : ∀ e ∈ L, W C n x e.2 = true) :
    W C n x t = true := by
  induction h with
  | leaf qv qt hv hr => exact Rr.val C n hC x hr (hL _ (List.mem_singleton_self _))
  | node qj qt L1 L2 hj ha hr _ _ ih1 ih2 =>
    apply Rr.val C n hC x hr
    have hg : gateAt C qj ∈ C.gates := by rw [gateAt_eq C qj hj]; exact List.getElem_mem hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ hg)
    have h1 := ih1 (fun e he => hL e (List.mem_append_left _ he))
    have h2 := ih2 (fun e he => hL e (List.mem_append_right _ he))
    rw [hab] at h1 h2
    rw [W_gate C n x qj hj (hC.2.1 qj hj), ha, hab]
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, h1, h2,
      Bool.and_true]

/-! ## The swap: the vectors for `[w, u]` are the reversed vectors for `[u, w]` -/

theorem swap (C : Circuit) (n u w : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ x, ∀ v, v ∈ A C n [w, u] x ↔ v.reverse ∈ A C n [u, w] x := by
  have hC' := hC
  obtain ⟨hao, hrb, h2⟩ := hC'
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro v
  by_cases hxn : x < n
  · rw [A_input C n _ x hxn, A_input C n _ x hxn]
    simp only [leafVectors]
    split_ifs with h1 h3 h3
    · simp only [List.map_cons, List.map_nil, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · intro h'; rw [← List.reverse_reverse v, h']; simp
    · exfalso; simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h3; tauto
    · exfalso; simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h3; tauto
    · simp
  · obtain ⟨j, rfl⟩ : ∃ j, x = n + j := ⟨x - n, by omega⟩
    by_cases hj : j < C.gates.length
    swap
    · rw [A_beyond C n _ _ (by omega), A_beyond C n _ _ (by omega)]; simp
    have hrbj := hrb j hj
    rw [A_gate C n _ j hj hrbj, A_gate C n _ j hj hrbj]
    have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hj]; exact List.getElem_mem hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ hg)
    have ha : a < n + j := hrbj a (by simp [hab])
    have hb : b < n + j := hrbj b (by simp [hab])
    rcases hao _ hg with hop | hop
    · -- AND
      simp only [rvG, hop, hab, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [mem_andStep, mem_andStep]
      constructor
      · rintro ⟨p, hp, q, hq, rfl⟩
        rw [mem_andStep] at hp
        obtain ⟨z, hz, p0, hp0, rfl⟩ := hp
        simp only [List.mem_singleton] at hz
        subst hz
        obtain ⟨c, d, rfl⟩ := realize_len2 C n w u hC a p0 hp0
        obtain ⟨e, f, rfl⟩ := realize_len2 C n w u hC b q hq
        refine ⟨capAdd 2 [0, 0] [d, c], (mem_andStep _ _ _ _).mpr
          ⟨[0, 0], by simp, [d, c], by simpa using (ih a ha _).mp hp0, rfl⟩,
          [f, e], by simpa using (ih b hb _).mp hq, ?_⟩
        simp [capAdd]
      · rintro ⟨p, hp, q, hq, hv⟩
        rw [mem_andStep] at hp
        obtain ⟨z, hz, p0, hp0, rfl⟩ := hp
        simp only [List.mem_singleton] at hz
        subst hz
        obtain ⟨c, d, rfl⟩ := realize_len2 C n u w hC a p0 hp0
        obtain ⟨e, f, rfl⟩ := realize_len2 C n u w hC b q hq
        refine ⟨capAdd 2 [0, 0] [d, c], (mem_andStep _ _ _ _).mpr
          ⟨[0, 0], by simp, [d, c], (ih a ha _).mpr (by simpa using hp0), rfl⟩,
          [f, e], (ih b hb _).mpr (by simpa using hq), ?_⟩
        rw [← List.reverse_reverse v, hv]
        simp [capAdd]
    · -- OR
      simp only [rvG, hop, hab, List.map_cons, List.map_nil]
      rw [mem_orFold, mem_orFold]
      simp only [false_or, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left]
      rw [ih a ha, ih b hb]

theorem cnt_eq (L : List (ℕ × ℕ)) (a : ℕ) :
    (L.filter (fun e => decide (e.2 = a))).length = (L.map Prod.snd).count a := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.filter_cons, List.map_cons, List.count_cons]
    split_ifs with h <;> simp_all

/-! ## The bridge -/

/-- L-meta-2350 (conjecture until checked): the read-2 test on `[u, w]` agrees with the test on
`[w, u]`, and when it accepts, an AND-rooted skeleton tree hangs from the output with every leaf
`u` or `w`, each read once or twice. -/
theorem readTwo_bridge : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → PEqualNP.MetaComplexity.circuitFun n C (fun k1 : Fin n => decide (k1.val = u)) = false → PEqualNP.MetaComplexity.circuitFun n C (fun k2 : Fin n => decide (k2.val = w)) = false → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = PEqualNP.ReadK.readsAtMost C n [w, u] 2) ∧ (PEqualNP.ReadK.readsAtMost C n [u, w] 2 = true → ∃ L : List (ℕ × ℕ), (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = u ∨ gv.2 = w) ∧ (L.filter (fun e1 => decide (e1.2 = u))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = w))).length ∈ ({1, 2} : Finset ℕ)) := by
  intro n C u w hC hu hw huw hfu hfw R hR T hT
  subst hR hT
  have hsw := swap C n u w hC
  refine ⟨?_, ?_⟩
  · unfold readsAtMost
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨v, hv, hall⟩
      exact ⟨v.reverse, (hsw _ _).mpr (by simpa using hv), by simpa using hall⟩
    · rintro ⟨v, hv, hall⟩
      exact ⟨v.reverse, (hsw _ _).mp hv, by simpa using hall⟩
  · intro hacc
    unfold readsAtMost at hacc
    rw [List.any_eq_true] at hacc
    obtain ⟨v, hv, hall⟩ := hacc
    obtain ⟨L, hTL, hl, rfl⟩ := realize C n u w hC _ v hv
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hall
    obtain ⟨hcu, hcw⟩ := hall
    have pos : ∀ a b, a < n → (a = u ∨ a = w) → (b = u ∨ b = w) → a ≠ b →
        circuitFun n C (fun k : Fin n => decide (k.val = a)) = false →
        1 ≤ (L.map Prod.snd).count b := by
      intro a b ha hab hbb hne hf
      by_contra h0
      have h0' : (L.map Prod.snd).count b = 0 := by omega
      rw [List.count_eq_zero] at h0'
      have hall : ∀ e ∈ L, e.2 = a := by
        intro e he
        have hm : e.2 ∈ L.map Prod.snd := List.mem_map.mpr ⟨e, he, rfl⟩
        rcases hl _ hm with h | h <;> rcases hab with rfl | rfl <;> rcases hbb with rfl | rfl <;>
          first | exact h | exact absurd rfl hne | exact absurd (h ▸ hm) h0'
      have := Tr.val C n hC (fun k : Fin n => decide (k.val = a)) hTL (by
        intro e he
        rw [hall e he, W_input C n _ a ha]
        simp)
      have hc : circuitFun n C (fun k : Fin n => decide (k.val = a)) =
          W C n (fun k : Fin n => decide (k.val = a)) C.output := rfl
      rw [hc, this] at hf
      exact Bool.noConfusion hf
    have hw1 := pos u w hu (Or.inl rfl) (Or.inr rfl) huw hfu
    have hu1 := pos w u hw (Or.inr rfl) (Or.inl rfl) (Ne.symm huw) hfw
    cases hTL with
    | leaf qv _ hv hr =>
      exfalso
      simp only [List.map_cons, List.map_nil, List.count_singleton] at hw1 hu1
      split_ifs at hw1 hu1 with h1 h2 <;> simp_all
    | node qj _ L1 L2 hj ha hr h1 h2 =>
      refine ⟨L1 ++ L2, ⟨qj, L1, L2, hj, ha, hr, fun Q hl hn => h1.toT C n Q hl hn,
        fun Q hl hn => h2.toT C n Q hl hn, rfl⟩, ?_, ?_, ?_⟩
      · intro gv hgv
        exact hl _ (List.mem_map.mpr ⟨gv, hgv, rfl⟩)
      · rw [cnt_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · rw [cnt_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega

end PEqualNP.MetaComplexity.ReadTwoBridge

/-!
# Helpers for L-meta-3145: the leaf bound of a core

For a core `j` of an `IsAO2` circuit, the input wires read by the gates of the cone of `j` give a
vertex set holding both ends of every edge `j` accepts, of size at most the number of gates of the
cone. The count: the `2m` operand slots of the `m` cone gates name every cone gate but `j` and
every read input, so at most `m + 1` inputs are read, with `m + 1` only if no wire is named by two
slots; in that case two operands of a cone gate never reach a common wire, every count vector at
cap 1 has entries at most 1, and `j` is READ-1 on each pair it accepts, against the core's
read-twice edge.
-/

namespace PEqualNP.MetaComplexity.LeafBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.ReadK PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.MetaComplexity.ReadTwoBridge

section Basic

variable (n : ℕ) (C : Circuit)

/-- One downward step: from the wire of a gate to a wire it reads. -/
def Step (a b : ℕ) : Prop := ∃ g < C.gates.length, a = n + g ∧ b ∈ (gateAt C g).inputs

/-- Downward reachability among wires. -/
abbrev Reach : ℕ → ℕ → Prop := Relation.ReflTransGen (Step n C)

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_prefix hpre (by simp; omega), ← hPl]
  simp

/-- The gate step of `cones`. -/
def coneF (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])

theorem cones_eq : cones n C = C.gates.foldl (fun R g => R ++ [coneF n R g]) [] := rfl

theorem flatMap_congr' {α β : Type _} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem cone_getD {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] = ((gateAt C j).inputs.filter
      (fun w => decide (n ≤ w ∧ w < n + j))).flatMap (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  obtain ⟨h1, h2, h3⟩ := foldl_snoc_split (coneF n) C.gates [] j hj []
  simp only [List.length_nil, zero_add] at h1 h3
  rw [← cones_eq] at h1 h2
  generalize (C.gates.take j).foldl (fun R g => R ++ [coneF n R g]) [] = P at h1 h2 h3
  rw [h1, gateAt_eq C j hj]
  unfold coneF
  rw [h3]
  apply flatMap_congr'
  intro w hw
  rw [List.mem_filter] at hw
  have : w - n < j := by simp at hw; omega
  rw [getD_of_prefix h2 (by rw [h3]; exact this)]

theorem inCone_iff (hrb : ReadsBack n C) {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔ ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ (w - n = i ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cone_getD n C hj]
  constructor
  · intro h
    obtain ⟨w, hw, hi⟩ := List.mem_flatMap.1 h
    rw [List.mem_filter] at hw
    simp only [decide_eq_true_eq] at hw
    rcases List.mem_cons.1 hi with h' | h'
    · exact ⟨w, hw.1, hw.2.1, Or.inl h'.symm⟩
    · exact ⟨w, hw.1, hw.2.1, Or.inr h'⟩
  · rintro ⟨w, hw, hnw, h⟩
    refine List.mem_flatMap.2 ⟨w, List.mem_filter.2 ⟨hw, ?_⟩, ?_⟩
    · simp only [decide_eq_true_eq]; exact ⟨hnw, hrb j hj w hw⟩
    · rcases h with h | h
      · exact List.mem_cons.2 (Or.inl h.symm)
      · exact List.mem_cons.2 (Or.inr h)

theorem inCone_iff_trans (hrb : ReadsBack n C) (i : ℕ) :
    ∀ j, j < C.gates.length → (InCone n C i j ↔ Relation.TransGen (Step n C) (n + j) (n + i)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  rw [inCone_iff n C hrb hj]
  constructor
  · rintro ⟨w, hw, hnw, h⟩
    have hwl : w < n + j := hrb j hj w hw
    have hst : Step n C (n + j) w := ⟨j, hj, rfl, hw⟩
    rcases h with h | h
    · have : w = n + i := by omega
      subst this
      exact Relation.TransGen.single hst
    · have hlt : w - n < j := by omega
      have := (ih (w - n) hlt (by omega)).1 h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at this
      exact Relation.TransGen.head hst this
  · intro h
    obtain ⟨c, ⟨g, hg, hjg, hc⟩, hr⟩ := Relation.TransGen.head'_iff.1 h
    have hgj : g = j := by omega
    subst hgj
    have hcl : c < n + g := hrb g hg c hc
    rcases Relation.ReflTransGen.cases_head hr with hci | ⟨d, ⟨g', hg', hcg', _⟩, hr'⟩
    · exact ⟨c, hc, by omega, Or.inl (by omega)⟩
    · refine ⟨c, hc, by omega, Or.inr ?_⟩
      have hlt : c - n < g := by omega
      refine (ih (c - n) hlt (by omega)).2 ?_
      have hcn : n + (c - n) = c := by omega
      rw [hcn]
      exact Relation.TransGen.head' ⟨g', hg', hcg', by assumption⟩ hr'

theorem mem_coneSet (hrb : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length) (g : ℕ) :
    g ∈ PEqualNP.Core.coneSet n C j ↔ g < C.gates.length ∧ Reach n C (n + j) (n + g) := by
  unfold PEqualNP.Core.coneSet
  rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨hg, hc⟩)
    · exact ⟨hj, Relation.ReflTransGen.refl⟩
    · exact ⟨hg, ((inCone_iff_trans n C hrb g j hj).1 hc).to_reflTransGen⟩
  · rintro ⟨hg, hr⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
    · left; omega
    · right; exact ⟨hg, (inCone_iff_trans n C hrb g j hj).2 h⟩

theorem reach_le (hrb : ReadsBack n C) {a b : ℕ} (h : Reach n C a b) : b ≤ a := by
  induction h with
  | refl => exact le_refl _
  | tail _ hst ih =>
    obtain ⟨g, hg, rfl, hc⟩ := hst
    have := hrb g hg _ hc
    omega

end Basic


section AO

variable {n : ℕ} {C : Circuit}

theorem list_two {l : List ℕ} (h : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  match l, h with
  | [a, b], _ => rfl

theorem ao_inputs (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) :
    (gateAt C g).inputs = [opnd C g 0, opnd C g 1] := by
  have hl : (gateAt C g).inputs.length = 2 := by
    rw [gateAt_eq C g hg]; exact hC.2.2 _ (List.getElem_mem hg)
  exact list_two hl

theorem ao_op (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) :
    (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := by
  rw [gateAt_eq C g hg]; exact hC.1 _ (List.getElem_mem hg)

theorem opnd_mem (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    opnd C g b ∈ (gateAt C g).inputs := by
  rw [ao_inputs hC hg]; fin_cases b <;> simp

theorem opnd_lt (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    opnd C g b < n + g := hC.2.1 g hg _ (opnd_mem hC hg b)

theorem step_opnd (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    Step n C (n + g) (opnd C g b) := ⟨g, hg, rfl, opnd_mem hC hg b⟩

theorem step_inv (hC : IsAO2 n C) {a c : ℕ} (h : Step n C a c) :
    ∃ g < C.gates.length, a = n + g ∧ ∃ b : Fin 2, c = opnd C g b := by
  obtain ⟨g, hg, rfl, hc⟩ := h
  rw [ao_inputs hC hg] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc
  · exact ⟨g, hg, rfl, 0, hc⟩
  · exact ⟨g, hg, rfl, 1, hc⟩

variable {j : ℕ}

theorem K_lt (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) : g < C.gates.length :=
  ((mem_coneSet n C hC.2.1 hj g).1 hK).1

theorem K_reach (hC : IsAO2 n C) (hj : j < C.gates.length) {g g' : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (hr : Reach n C (n + g) (n + g'))
    (hg' : g' < C.gates.length) : g' ∈ PEqualNP.Core.coneSet n C j := by
  rw [mem_coneSet n C hC.2.1 hj] at hK ⊢
  exact ⟨hg', hK.2.trans hr⟩

theorem K_opnd (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (b : Fin 2) (hge : n ≤ opnd C g b) :
    opnd C g b - n ∈ PEqualNP.Core.coneSet n C j ∧ opnd C g b - n < g := by
  have hg := K_lt hC hj hK
  have hlt := opnd_lt hC hg b
  refine ⟨K_reach hC hj hK ?_ (by omega), by omega⟩
  have : n + (opnd C g b - n) = opnd C g b := by omega
  rw [this]
  exact Relation.ReflTransGen.single (step_opnd hC hg b)

theorem K_cover (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (hne : g ≠ j) :
    ∃ h ∈ PEqualNP.Core.coneSet n C j, ∃ b : Fin 2, opnd C h b = n + g := by
  have hr := ((mem_coneSet n C hC.2.1 hj g).1 hK).2
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
  · exact absurd (by omega) hne
  · obtain ⟨c, hrc, hst⟩ := Relation.TransGen.tail'_iff.1 h
    obtain ⟨h', hh', rfl, b, hb⟩ := step_inv hC hst
    refine ⟨h', ?_, b, hb.symm⟩
    rw [mem_coneSet n C hC.2.1 hj]
    exact ⟨hh', hrc⟩

/-- The operand slots of the cone of `j`. -/
def slots (n : ℕ) (C : Circuit) (j : ℕ) : Finset (ℕ × Fin 2) :=
  PEqualNP.Core.coneSet n C j ×ˢ (Finset.univ : Finset (Fin 2))

/-- The wire a slot names. -/
def slotW (C : Circuit) (p : ℕ × Fin 2) : ℕ := opnd C p.1 p.2

/-- A wire `z ≠ a` reached from an operand `a` of a cone gate is named by a slot of a cone gate
reached from `a`. -/
theorem below_named (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (β : Fin 2) {z : ℕ}
    (hr : Reach n C (opnd C g β) z) (hz : z ≠ opnd C g β) :
    ∃ h ∈ PEqualNP.Core.coneSet n C j, ∃ b : Fin 2, opnd C h b = z ∧
      Reach n C (opnd C g β) (n + h) := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
  · exact absurd h hz
  · obtain ⟨c, hrc, hst⟩ := Relation.TransGen.tail'_iff.1 h
    obtain ⟨h', hh', rfl, b, hb⟩ := step_inv hC hst
    refine ⟨h', K_reach hC hj hK ?_ hh', b, hb.symm, hrc⟩
    exact Relation.ReflTransGen.head (step_opnd hC (K_lt hC hj hK) β) hrc

/-- With no wire named by two slots, the two operands of a cone gate reach no common wire. -/
theorem no_common (hC : IsAO2 n C) (hj : j < C.gates.length)
    (hinj : Set.InjOn (slotW C) (slots n C j)) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) {x : ℕ} (hx : x < n + C.gates.length)
    (h0 : Reach n C (opnd C g 0) x) (h1 : Reach n C (opnd C g 1) x) : False := by
  classical
  have hrb := hC.2.1
  have hg := K_lt hC hj hK
  have hsl : ∀ h ∈ PEqualNP.Core.coneSet n C j, ∀ b : Fin 2, ((h, b) : ℕ × Fin 2) ∈ slots n C j :=
    fun h hh b => Finset.mem_product.2 ⟨hh, Finset.mem_univ _⟩
  have inj : ∀ h ∈ PEqualNP.Core.coneSet n C j, ∀ b : Fin 2, ∀ h' ∈ PEqualNP.Core.coneSet n C j,
      ∀ b' : Fin 2, opnd C h b = opnd C h' b' → h = h' ∧ b = b' := by
    intro h hh b h' hh' b' he
    have := hinj (hsl h hh b) (hsl h' hh' b') he
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  set Z := (Finset.range (n + C.gates.length)).filter
    (fun z => Reach n C (opnd C g 0) z ∧ Reach n C (opnd C g 1) z) with hZ
  have hxZ : x ∈ Z := Finset.mem_filter.2 ⟨Finset.mem_range.2 hx, h0, h1⟩
  obtain ⟨z, hzZ, hmax⟩ := Finset.exists_max_image Z id ⟨x, hxZ⟩
  rw [Finset.mem_filter] at hzZ
  obtain ⟨_, hz0, hz1⟩ := hzZ
  have hl0 := opnd_lt hC hg 0
  have hl1 := opnd_lt hC hg 1
  by_cases ha : z = opnd C g 0
  · by_cases hab : opnd C g 1 = opnd C g 0
    · have := (inj g hK 1 g hK 0 hab).2
      exact absurd this (by decide)
    · have hzb : z ≠ opnd C g 1 := fun h => hab (h ▸ ha)
      obtain ⟨h, hh, b, hb, hr⟩ := below_named hC hj hK 1 hz1 hzb
      obtain ⟨rfl, rfl⟩ := inj h hh b g hK 0 (hb.trans ha)
      have := reach_le n C hrb hr
      omega
  · by_cases hb' : z = opnd C g 1
    · obtain ⟨h, hh, b, hb, hr⟩ := below_named hC hj hK 0 hz0 ha
      obtain ⟨rfl, rfl⟩ := inj h hh b g hK 1 (hb.trans hb')
      have := reach_le n C hrb hr
      omega
    · obtain ⟨h1', hh1, b1, hb1, hr1⟩ := below_named hC hj hK 0 hz0 ha
      obtain ⟨h2', hh2, b2, hb2, hr2⟩ := below_named hC hj hK 1 hz1 hb'
      obtain ⟨rfl, rfl⟩ := inj h1' hh1 b1 h2' hh2 b2 (hb1.trans hb2.symm)
      have hlt1 := K_lt hC hj hh1
      have hin : n + h1' ∈ Z := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hr1, hr2⟩
      have := hmax _ hin
      have := opnd_lt hC hlt1 b1
      simp only [id] at *
      omega

end AO


section Vectors

variable {n : ℕ} {C : Circuit}

/-- The vector set of wire `x` for the list `S`, at cap `k`. -/
abbrev AV (n : ℕ) (C : Circuit) (k : ℕ) (S : List ℕ) (x : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD x []

theorem AV_input (k : ℕ) (S : List ℕ) (x : ℕ) (hx : x < n) :
    AV n C k S x = leafVectors S k x := by
  unfold AV
  rw [rv_eq, foldl_snoc_init _ _ _ _ _ (by simpa using hx)]
  simp [List.getD_eq_getElem?_getD, hx]

theorem AV_gate (k : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    AV n C k S (n + j) = rvG S k ((gateAt C j).inputs.map (AV n C k S)) (gateAt C j) := by
  unfold AV
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (rvG S k) [] ((List.range n).map (leafVectors S k)) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_map, List.length_range] at this
  rw [rv_eq, this]

theorem capAdd_le (k : ℕ) (u v : List ℕ) (i : ℕ) :
    (capAdd k u v).getD i 0 ≤ u.getD i 0 + v.getD i 0 := by
  unfold capAdd
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  cases u[i]? <;> cases v[i]? <;> simp

theorem leaf_getD (p q w i : ℕ) (v : List ℕ) (hv : v ∈ leafVectors [p, q] 1 w) :
    v.getD i 0 ≤ 1 ∧ (v.getD i 0 ≠ 0 → [p, q].getD i 0 = w) := by
  unfold leafVectors at hv
  split_ifs at hv
  · simp only [List.mem_singleton] at hv
    subst hv
    rcases i with _ | _ | i
    · by_cases h : p = w <;> simp [h]
    · by_cases h : q = w <;> simp [h]
    · simp
  · simp at hv

theorem leaf_ne (p q w : ℕ) (hw : w = p ∨ w = q) : leafVectors [p, q] 1 w ≠ [] := by
  unfold leafVectors
  rw [if_pos (by simp; tauto)]
  simp

/-- The two gate shapes of `rvG` on two operands. -/
theorem mem_rvG_or (S : List ℕ) (k : ℕ) (A B : List (List ℕ)) (g : Gate) (hg : g.op = GateOp.or)
    (v : List ℕ) : v ∈ rvG S k [A, B] g ↔ v ∈ A ∨ v ∈ B := by
  unfold rvG
  rw [hg]
  simp only
  rw [mem_orFold]
  simp

theorem mem_rvG_and (S : List ℕ) (k : ℕ) (A B : List (List ℕ)) (g : Gate) (hg : g.op = GateOp.and)
    (v : List ℕ) : v ∈ rvG S k [A, B] g ↔
      ∃ a ∈ A, ∃ b ∈ B, v = capAdd k (capAdd k (S.map fun _ => 0) a) b := by
  unfold rvG
  rw [hg]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨c, hc, b, hb, rfl⟩
    rw [mem_andStep] at hc
    obtain ⟨z, hz, a, ha, rfl⟩ := hc
    simp only [List.mem_singleton] at hz
    subst hz
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, (mem_andStep _ _ _ _).2 ⟨_, List.mem_singleton_self _, a, ha, rfl⟩, b, hb, rfl⟩

theorem zero_getD (S : List ℕ) (i : ℕ) : (S.map fun _ => 0).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases S[i]? <;> simp

theorem and_getD_le (k : ℕ) (S : List ℕ) (a b : List ℕ) (i : ℕ) :
    (capAdd k (capAdd k (S.map fun _ => 0) a) b).getD i 0 ≤ a.getD i 0 + b.getD i 0 := by
  have h1 := capAdd_le k (capAdd k (S.map fun _ => 0) a) b i
  have h2 := capAdd_le k (S.map fun _ => 0) a i
  rw [zero_getD] at h2
  omega

theorem gate_vec (hC : IsAO2 n C) (k : ℕ) (S : List ℕ) {g : ℕ} (hg : g < C.gates.length) (v : List ℕ) :
    v ∈ AV n C k S (n + g) ↔
      ((gateAt C g).op = GateOp.or ∧ (v ∈ AV n C k S (opnd C g 0) ∨ v ∈ AV n C k S (opnd C g 1))) ∨
      ((gateAt C g).op = GateOp.and ∧ ∃ a ∈ AV n C k S (opnd C g 0), ∃ b ∈ AV n C k S (opnd C g 1),
        v = capAdd k (capAdd k (S.map fun _ => 0) a) b) := by
  rw [AV_gate k S g hg (hC.2.1 g hg), ao_inputs hC hg]
  simp only [List.map_cons, List.map_nil]
  rcases ao_op hC hg with h | h
  · rw [mem_rvG_and _ _ _ _ _ h]; simp [h]
  · rw [mem_rvG_or _ _ _ _ _ h]; simp [h]

/-- A nonzero entry of a vector of wire `w` names a wire reached from `w`. -/
theorem vec_reach (hC : IsAO2 n C) (p q : ℕ) (i : ℕ) :
    ∀ w, ∀ v ∈ AV n C 1 [p, q] w, v.getD i 0 ≠ 0 → Reach n C w ([p, q].getD i 0) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro v hv hne
  by_cases hwn : w < n
  · rw [AV_input 1 _ w hwn] at hv
    rw [(leaf_getD p q w i v hv).2 hne]
  · by_cases hwl : w < n + C.gates.length
    · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
      have hg : g < C.gates.length := by omega
      rcases (gate_vec hC 1 _ hg v).1 hv with ⟨_, h | h⟩ | ⟨_, a, ha, b, hb, rfl⟩
      · exact Relation.ReflTransGen.head (step_opnd hC hg 0)
          (ih _ (opnd_lt hC hg 0) v h hne)
      · exact Relation.ReflTransGen.head (step_opnd hC hg 1)
          (ih _ (opnd_lt hC hg 1) v h hne)
      · have := and_getD_le 1 [p, q] a b i
        by_cases ha0 : a.getD i 0 = 0
        · exact Relation.ReflTransGen.head (step_opnd hC hg 1)
            (ih _ (opnd_lt hC hg 1) b hb (by omega))
        · exact Relation.ReflTransGen.head (step_opnd hC hg 0)
            (ih _ (opnd_lt hC hg 0) a ha ha0)
    · have : AV n C 1 [p, q] w = [] := by
        unfold AV
        rw [rv_eq, foldl_snoc_beyond _ _ _ _ _ (by simp; omega)]
      rw [this] at hv
      simp at hv

/-- A wire true at `1_uv` carries some vector for `[u, v]`. -/
theorem vec_ne (hC : IsAO2 n C) (u v : Fin n) :
    ∀ w, w < n + C.gates.length → W C n (pairInput u v) w = true →
      AV n C 1 [u.val, v.val] w ≠ [] := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hwl hW
  by_cases hwn : w < n
  · rw [AV_input 1 _ w hwn]
    rw [W_input C n _ w hwn] at hW
    unfold pairInput at hW
    simp only [decide_eq_true_eq] at hW
    apply leaf_ne
    rcases hW with h | h
    · left; rw [← h]
    · right; rw [← h]
  · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
    have hg : g < C.gates.length := by omega
    rw [W_gate C n _ g hg (hC.2.1 g hg), ao_inputs hC hg] at hW
    have l0 := opnd_lt hC hg 0
    have l1 := opnd_lt hC hg 1
    rcases ao_op hC hg with h | h
    · rw [h] at hW
      simp [GateOp.eval] at hW
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (ih _ l0 (by omega) hW.1)
      obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (ih _ l1 (by omega) hW.2)
      exact List.ne_nil_of_mem ((gate_vec hC 1 _ hg _).2 (Or.inr ⟨h, a, ha, b, hb, rfl⟩))
    · rw [h] at hW
      simp [GateOp.eval] at hW
      rcases hW with hW | hW
      · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (ih _ l0 (by omega) hW)
        exact List.ne_nil_of_mem ((gate_vec hC 1 _ hg _).2 (Or.inl ⟨h, Or.inl ha⟩))
      · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (ih _ l1 (by omega) hW)
        exact List.ne_nil_of_mem ((gate_vec hC 1 _ hg _).2 (Or.inl ⟨h, Or.inr ha⟩))

/-- With no wire named by two slots, every vector of a cone gate has entries at most 1. -/
theorem vec_le_one (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hinj : Set.InjOn (slotW C) (slots n C j)) (p q : ℕ) (hp : p < n) (hq : q < n) :
    ∀ g ∈ PEqualNP.Core.coneSet n C j, ∀ v ∈ AV n C 1 [p, q] (n + g), ∀ i, v.getD i 0 ≤ 1 := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro hK v hv i
  have hg := K_lt hC hj hK
  have hop : ∀ b : Fin 2, ∀ v ∈ AV n C 1 [p, q] (opnd C g b), v.getD i 0 ≤ 1 := by
    intro b v hv
    by_cases hn : opnd C g b < n
    · rw [AV_input 1 _ _ hn] at hv
      exact (leaf_getD p q _ i v hv).1
    · obtain ⟨hK', hlt⟩ := K_opnd hC hj hK b (by omega)
      have he : n + (opnd C g b - n) = opnd C g b := by omega
      rw [← he] at hv
      exact ih _ hlt hK' v hv i
  rcases (gate_vec hC 1 _ hg v).1 hv with ⟨_, h | h⟩ | ⟨_, a, ha, b, hb, rfl⟩
  · exact hop 0 v h
  · exact hop 1 v h
  · have hle := and_getD_le 1 [p, q] a b i
    have ha1 := hop 0 a ha
    have hb1 := hop 1 b hb
    by_cases ha0 : a.getD i 0 = 0
    · omega
    · by_cases hb0 : b.getD i 0 = 0
      · omega
      · exfalso
        have hx : [p, q].getD i 0 < n + C.gates.length := by
          rcases i with _ | _ | i <;> simp <;> omega
        exact no_common hC hj hinj hK hx (vec_reach hC p q i _ a ha ha0)
          (vec_reach hC p q i _ b hb hb0)

end Vectors

section Main

variable {n : ℕ} {C : Circuit}

/-- The cone of a gate reads only the slot wires: inputs agreeing there give the same value. -/
theorem agree (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (x y : Fin n → Bool)
    (hxy : ∀ i (hi : i < n), i ∈ (slots n C j).image (slotW C) → x ⟨i, hi⟩ = y ⟨i, hi⟩) :
    ∀ g ∈ PEqualNP.Core.coneSet n C j, W C n x (n + g) = W C n y (n + g) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro hK
  have hg := K_lt hC hj hK
  have hop : ∀ b : Fin 2, W C n x (opnd C g b) = W C n y (opnd C g b) := by
    intro b
    by_cases hn : opnd C g b < n
    · rw [W_input C n x _ hn, W_input C n y _ hn]
      apply hxy
      exact Finset.mem_image.2 ⟨(g, b), Finset.mem_product.2 ⟨hK, Finset.mem_univ _⟩, rfl⟩
    · obtain ⟨hK', hlt⟩ := K_opnd hC hj hK b (by omega)
      have he : n + (opnd C g b - n) = opnd C g b := by omega
      rw [← he]
      exact ih _ hlt hK'
  rw [W_gate C n x g hg (hC.2.1 g hg), W_gate C n y g hg (hC.2.1 g hg), ao_inputs hC hg]
  simp only [List.map_cons, List.map_nil, hop 0, hop 1]

theorem pairInput_comm (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w; unfold pairInput; simp [or_comm]

/-- An end of an edge accepted by an implicant gate `j` is a slot wire of the cone of `j`. -/
theorem end_mem (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hC : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hbelow : BelowF G C j) {u v : Fin n} (huv : G.Adj u v)
    (hacc : gateVal n C j (pairInput u v) = true) :
    u.val ∈ (slots n C j).image (slotW C) := by
  by_contra hu
  have hjK : j ∈ PEqualNP.Core.coneSet n C j := Finset.mem_insert_self _ _
  have hag := agree hC hj (pairInput u v) (fun w => decide (w = v)) (by
    intro i hi hI
    have hne : (⟨i, hi⟩ : Fin n) ≠ u := by
      rintro rfl; exact hu hI
    unfold pairInput
    simp [hne]) j hjK
  have hy : gateVal n C j (fun w => decide (w = v)) = true := by
    have e1 : gateVal n C j (fun w => decide (w = v)) = W C n (fun w => decide (w = v)) (n + j) := rfl
    have e2 : gateVal n C j (pairInput u v) = W C n (pairInput u v) (n + j) := rfl
    rw [e1, ← hag, ← e2]; exact hacc
  have := hbelow _ hy
  unfold graphFun at this
  simp at this

theorem leaf_bound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), PEqualNP.TopForm.IsAO2 n C →
    PEqualNP.Core.IsCore G C j → ∃ S : Finset (Fin n),
      S.card ≤ (PEqualNP.Core.coneSet n C j).card ∧
      ∀ e ∈ PEqualNP.TopForm.gammaE G C j, ∀ v ∈ e, v ∈ S := by
  intro n G _ C j hC hcore
  classical
  obtain ⟨hj, ⟨hbelow, _⟩, _, u0, v0, huv0, hacc0, hrt⟩ := hcore
  set K := PEqualNP.Core.coneSet n C j with hKdef
  set I := (slots n C j).image (slotW C) with hIdef
  refine ⟨Finset.univ.filter (fun w : Fin n => w.val ∈ I), ?_, ?_⟩
  · -- the count
    have hjK : j ∈ K := Finset.mem_insert_self _ _
    have hS : (Finset.univ.filter (fun w : Fin n => w.val ∈ I)).card ≤
        (I.filter (fun w => w < n)).card := by
      apply Finset.card_le_card_of_injOn (fun w : Fin n => w.val)
      · intro w hw
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
        simp only [Finset.coe_filter, Set.mem_ofPred_eq]
        exact ⟨hw, w.isLt⟩
      · intro a _ b _ h; exact Fin.ext h
    have hG : (K.erase j).card ≤ (I.filter (fun w => ¬ w < n)).card := by
      apply Finset.card_le_card_of_injOn (fun g => n + g)
      · intro g hg
        simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hg
        obtain ⟨h, hh, b, hb⟩ := K_cover hC hj hg.1 hg.2
        simp only [Finset.coe_filter, Set.mem_ofPred_eq]
        refine ⟨Finset.mem_image.2 ⟨(h, b), Finset.mem_product.2 ⟨hh, Finset.mem_univ _⟩, hb⟩, ?_⟩
        omega
      · intro a _ b _ h; simp only at h; omega
    have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun w => w < n)
    have hslots : (slots n C j).card = K.card * 2 := by
      unfold slots; rw [Finset.card_product]; simp [hKdef]
    have hnotinj : ¬ Set.InjOn (slotW C) (slots n C j) := by
      intro hinj
      have hjK' : j ∈ PEqualNP.Core.coneSet n C j := hjK
      have hne := vec_ne hC u0 v0 (n + j) (by omega) hacc0
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
      have hle := vec_le_one hC hj hinj u0.val v0.val u0.isLt v0.isLt j hjK' w hw
      apply absurd hrt
      unfold PEqualNP.Core.ReadTwiceAt readsAtMost
      simp only [Bool.not_eq_false]
      rw [List.any_eq_true]
      refine ⟨w, hw, ?_⟩
      rw [List.all_eq_true]
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
      have := hle i
      rw [List.getD_eq_getElem _ _ hi] at this
      simpa using this
    have hlt : I.card < (slots n C j).card :=
      lt_of_le_of_ne Finset.card_image_le (fun h => hnotinj (Finset.card_image_iff.1 h))
    have herase := Finset.card_erase_of_mem hjK
    have hpos : 0 < K.card := Finset.card_pos.2 ⟨j, hjK⟩
    omega
  · intro e he w hw
    unfold gammaE at he
    rw [Finset.mem_filter] at he
    obtain ⟨heG, u, v, rfl, hacc⟩ := he
    have huv : G.Adj u v := by simpa using heG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Sym2.mem_iff.1 hw with rfl | rfl
    · exact end_mem G hC hj hbelow huv hacc
    · exact end_mem G hC hj hbelow huv.symm (by rw [pairInput_comm]; exact hacc)

end Main

end PEqualNP.MetaComplexity.LeafBound
namespace Pilot2963

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Core PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.LeafBound

section Prune

variable {α : Type}

/-- The fold behind `Circuit.wires` and `Circuit.lineDegrees`, for any value type. -/
def d3r1Fold (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [Φ g.op (g.inputs.map fun i => w.getD i δ)]) init

theorem d3r1Fold_snoc (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (g : Gate)
    (init : List α) :
    d3r1Fold δ Φ (gs ++ [g]) init = d3r1Fold δ Φ gs init ++
      [Φ g.op (g.inputs.map fun i => (d3r1Fold δ Φ gs init).getD i δ)] := by
  simp only [d3r1Fold, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem d3r1Fold_length (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
    (d3r1Fold δ Φ gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih => rw [d3r1Fold_snoc]; simp [ih]; omega

theorem d3r1Fold_lt (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : i < init.length) : (d3r1Fold δ Φ gs init).getD i δ = init.getD i δ := by
  induction gs using List.reverseRecOn with
  | nil => simp [d3r1Fold]
  | append_singleton gs g ih =>
    rw [d3r1Fold_snoc, List.getD_append _ _ _ _ (by rw [d3r1Fold_length]; omega), ih]

theorem d3r1Fold_ge (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α)
    (i : ℕ) (h : init.length + gs.length ≤ i) : (d3r1Fold δ Φ gs init).getD i δ = δ := by
  rw [List.getD_eq_default _ _ (by rw [d3r1Fold_length]; exact h)]

theorem d3r1Fold_gate (δ : α) (Φ : GateOp → List α → α) (gs : List Gate) (init : List α) :
    ∀ (j : ℕ) (hj : j < gs.length), (d3r1Fold δ Φ gs init).getD (init.length + j) δ =
      Φ gs[j].op (gs[j].inputs.map fun i =>
        if i < init.length + j then (d3r1Fold δ Φ gs init).getD i δ else δ) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hl := d3r1Fold_length δ Φ gs init
    rw [d3r1Fold_snoc]
    by_cases hjl : j < gs.length
    · rw [List.getD_append _ _ _ _ (by omega), ih j hjl]
      simp only [List.getElem_append_left hjl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length + j
      · rw [if_pos hi, if_pos hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, if_false]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [List.getElem_append_right (Nat.le_refl _), hl, Nat.sub_self,
        List.getD_cons_zero, List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length + gs.length
      · rw [if_pos hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, if_false]
        rw [List.getD_eq_default _ _ (by omega)]

end Prune

/-- The number of indices below `t` kept by `κ`. -/
def d3r1Rank (κ : ℕ → Bool) (t : ℕ) : ℕ := ((List.range t).filter κ).length

theorem d3r1_range_split (κ : ℕ → Bool) (s t : ℕ) (h : s ≤ t) :
    (List.range t).filter κ = (List.range s).filter κ ++ (List.range' s (t - s)).filter κ := by
  rw [← List.filter_append]
  congr 1
  rw [List.range_eq_range', List.range_eq_range']
  have := @List.range'_append_1 0 s (t - s)
  simp only [Nat.zero_add] at this
  rw [this]
  congr 1
  omega

theorem d3r1_rank_lt (κ : ℕ → Bool) (s t : ℕ) (hst : s < t) (hs : κ s = true) :
    d3r1Rank κ s < d3r1Rank κ t := by
  unfold d3r1Rank
  rw [d3r1_range_split κ s t hst.le, List.length_append]
  obtain ⟨m, hm⟩ : ∃ m, t - s = m + 1 := ⟨t - s - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hs]
  simp

theorem d3r1_L_get (κ : ℕ → Bool) (len t : ℕ) (ht : t < len) (hk : κ t = true) :
    ((List.range len).filter κ)[d3r1Rank κ t]? = some t := by
  rw [d3r1_range_split κ t len ht.le]
  unfold d3r1Rank
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, len - t = m + 1 := ⟨len - t - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hk]
  simp

theorem d3r1_L_back (κ : ℕ → Bool) (len r : ℕ) (hr : r < ((List.range len).filter κ).length) :
    κ ((List.range len).filter κ)[r] = true ∧ ((List.range len).filter κ)[r] < len ∧
      d3r1Rank κ ((List.range len).filter κ)[r] = r := by
  have hm : ((List.range len).filter κ)[r] ∈ (List.range len).filter κ := List.getElem_mem hr
  have hm2 := List.mem_filter.mp hm
  have hlt := List.mem_range.mp hm2.1
  refine ⟨hm2.2, hlt, ?_⟩
  have hg := d3r1_L_get κ len _ hlt hm2.2
  rw [List.getElem?_eq_some_iff] at hg
  obtain ⟨hb, he⟩ := hg
  have hnd : ((List.range len).filter κ).Nodup := (List.nodup_range).filter _
  exact (hnd.getElem_inj_iff).mp he

/-- The new index of a wire after pruning. -/
def d3r1New (n : ℕ) (κ : ℕ → Bool) (top u : ℕ) : ℕ :=
  if u < n then u else if κ (u - n) then n + d3r1Rank κ (u - n) else n + top

/-- The number of kept gates. -/
def d3r1Top (κ : ℕ → Bool) (gs : List Gate) : ℕ := ((List.range gs.length).filter κ).length

/-- The gate `t` after pruning: reads below it are renumbered, a read at or above it reads itself
(the value `false` and degree `0`, as before). -/
def d3r1PGate (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) : Gate :=
  { op := (gs.getD t ⟨GateOp.and, []⟩).op,
    inputs := (gs.getD t ⟨GateOp.and, []⟩).inputs.map fun a =>
      if a < n + t then d3r1New n κ (d3r1Top κ gs) a else n + d3r1Rank κ t }

/-- The kept gates, in order. -/
def d3r1Pruned (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) : List Gate :=
  ((List.range gs.length).filter κ).map (d3r1PGate n κ gs)

theorem d3r1_pruned_length (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) :
    (d3r1Pruned n κ gs).length = d3r1Top κ gs := by
  simp [d3r1Pruned, d3r1Top]

theorem d3r1_pruned_get (n : ℕ) (κ : ℕ → Bool) (gs : List Gate) (t : ℕ) (ht : t < gs.length)
    (hk : κ t = true) : ∃ h : d3r1Rank κ t < (d3r1Pruned n κ gs).length,
      (d3r1Pruned n κ gs)[d3r1Rank κ t] = d3r1PGate n κ gs t := by
  have hg := d3r1_L_get κ gs.length t ht hk
  rw [List.getElem?_eq_some_iff] at hg
  obtain ⟨hb, he⟩ := hg
  refine ⟨by simpa [d3r1Pruned] using hb, ?_⟩
  simp [d3r1Pruned, he]

theorem d3r1_new_lt (n : ℕ) (κ : ℕ → Bool) (top a t : ℕ) (hat : a < n + t)
    (ha : a < n ∨ κ (a - n) = true) : d3r1New n κ top a < n + d3r1Rank κ t := by
  unfold d3r1New
  by_cases han : a < n
  · rw [if_pos han]; omega
  · have hk := ha.resolve_left han
    rw [if_neg han, if_pos hk]
    have := d3r1_rank_lt κ (a - n) t (by omega) hk
    omega

/-- Pruning keeps the value of every kept wire, for any fold of the shape of `Circuit.wires`. -/
theorem d3r1_prune_val {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
    (hn : init.length = n) (gs : List Gate) (κ : ℕ → Bool)
    (hκ : ∀ t, κ t = true → t < gs.length)
    (hcl : ∀ (t : ℕ) (ht : t < gs.length), κ t = true → ∀ a ∈ gs[t].inputs, n ≤ a → a < n + t →
      κ (a - n) = true) :
    ∀ u, (u < n ∨ κ (u - n) = true) →
      (d3r1Fold δ Φ (d3r1Pruned n κ gs) init).getD (d3r1New n κ (d3r1Top κ gs) u) δ =
        (d3r1Fold δ Φ gs init).getD u δ := by
  subst hn
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < init.length
    · simp only [d3r1New, hun, if_true]
      rw [d3r1Fold_lt _ _ _ _ _ hun, d3r1Fold_lt _ _ _ _ _ hun]
    · have hk : κ (u - init.length) = true := hu.resolve_left hun
      obtain ⟨t, rfl⟩ : ∃ t, u = init.length + t := ⟨u - init.length, by omega⟩
      simp only [Nat.add_sub_cancel_left] at hk
      have ht := hκ t hk
      have hnew : d3r1New init.length κ (d3r1Top κ gs) (init.length + t) =
          init.length + d3r1Rank κ t := by
        simp [d3r1New, hk]
      obtain ⟨hb, hpr⟩ := d3r1_pruned_get init.length κ gs t ht hk
      rw [hnew, d3r1Fold_gate _ _ _ _ _ hb, d3r1Fold_gate _ _ _ _ t ht, hpr]
      have hg : gs.getD t ⟨GateOp.and, []⟩ = gs[t] := List.getD_eq_getElem _ _ ht
      simp only [d3r1PGate, hg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      simp only [Function.comp]
      by_cases hat : a < init.length + t
      · have hA : a < init.length ∨ κ (a - init.length) = true := by
          by_cases han : a < init.length
          · exact Or.inl han
          · exact Or.inr (hcl t ht hk a ha (by omega) hat)
        rw [if_pos hat, if_pos (d3r1_new_lt _ _ _ a t hat hA), if_pos hat]
        exact ih a hat hA
      · simp only [hat, if_false, lt_irrefl]

/-- The value at the output wire is kept, whether or not that wire is a kept gate. -/
theorem d3r1_prune_out {α : Type} (δ : α) (Φ : GateOp → List α → α) (init : List α) (n : ℕ)
    (hn : init.length = n) (gs : List Gate) (κ : ℕ → Bool) (o : ℕ)
    (hκ : ∀ t, κ t = true → t < gs.length)
    (hcl : ∀ (t : ℕ) (ht : t < gs.length), κ t = true → ∀ a ∈ gs[t].inputs, n ≤ a → a < n + t →
      κ (a - n) = true)
    (ho : n ≤ o → o < n + gs.length → κ (o - n) = true) :
    (d3r1Fold δ Φ (d3r1Pruned n κ gs) init).getD (d3r1New n κ (d3r1Top κ gs) o) δ =
      (d3r1Fold δ Φ gs init).getD o δ := by
  by_cases hA : o < n ∨ κ (o - n) = true
  · exact d3r1_prune_val δ Φ init n hn gs κ hκ hcl o hA
  · have hon : n ≤ o := by omega
    have hk : κ (o - n) = false := by simpa using (fun h => hA (Or.inr h))
    have hol : n + gs.length ≤ o := by
      by_contra h
      rw [ho hon (by omega)] at hk
      exact Bool.noConfusion hk
    have hnew : d3r1New n κ (d3r1Top κ gs) o = n + d3r1Top κ gs := by
      simp [d3r1New, hk, show ¬ o < n by omega]
    rw [hnew, d3r1Fold_ge _ _ _ _ _ (by rw [hn, d3r1_pruned_length]),
      d3r1Fold_ge _ _ _ _ _ (by omega)]

theorem packCones {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (R : Finset ℕ)
    (roots : ∀ j∈R, j < C.gates.length) :
    let U := R.biUnion (coneSet n C)
    ∃ K : Circuit, ∃ ren : ℕ → ℕ, Monotone2 K ∧ K.size = U.card ∧
      ∀ j∈R, ∀ x : Fin n → Bool, (K.wires (List.ofFn x)).getD (ren j) false =
        gateVal n C j x := by
  classical
  intro U
  let κ (t : ℕ) := decide (t∈U)
  have valU (t : ℕ) (ht : t∈U) : t < C.gates.length := by
    obtain ⟨j,hj,hK⟩ := Finset.mem_biUnion.mp ht
    exact K_lt ao (roots j hj) hK
  have keep (t : ℕ) : κ t = true ↔ t∈U := by simp [κ]
  have bounded : ∀ t, κ t = true → t < C.gates.length := fun t ht => valU t ((keep t).mp ht)
  have closed : ∀ t (ht : t < C.gates.length), κ t = true → ∀ a ∈ C.gates[t].inputs,
      n ≤ a → a < n+t → κ (a-n) = true := by
    intro t ht kt a ha hn _
    obtain ⟨j,hj,hK⟩ := Finset.mem_biUnion.mp ((keep t).mp kt)
    have gateEq : gateAt C t = C.gates[t] := List.getD_eq_getElem _ _ ht
    have hmem : a ∈ (gateAt C t).inputs := gateEq.symm ▸ ha
    rw [ao_inputs ao ht] at hmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    apply (keep _).mpr
    rcases hmem with h | h
    · rw [h] at hn ⊢
      exact Finset.mem_biUnion.mpr ⟨j,hj,(K_opnd ao (roots j hj) hK 0 hn).1⟩
    · rw [h] at hn ⊢
      exact Finset.mem_biUnion.mpr ⟨j,hj,(K_opnd ao (roots j hj) hK 1 hn).1⟩
  let gs := d3r1Pruned n κ C.gates
  let ren (j : ℕ) := d3r1New n κ (d3r1Top κ C.gates) (n+j)
  refine ⟨⟨gs,0⟩,ren,?_,?_,?_⟩
  · intro g hg
    change g ∈ d3r1Pruned n κ C.gates at hg
    simp only [d3r1Pruned,List.mem_map,List.mem_filter,List.mem_range] at hg
    obtain ⟨t,⟨ht,_⟩,rfl⟩ := hg
    simp only [d3r1PGate,List.length_map,List.getD_eq_getElem _ _ ht]
    have op := ao.1 _ (List.getElem_mem ht)
    exact ⟨op,le_of_eq (ao.2.2 _ (List.getElem_mem ht))⟩
  · change (d3r1Pruned n κ C.gates).length = U.card
    rw [d3r1_pruned_length]
    let L := (List.range C.gates.length).filter κ
    have nodup : L.Nodup := (List.nodup_range).filter _
    have eq : L.toFinset=U := by
      ext t
      simp only [L,List.mem_toFinset,List.mem_filter,List.mem_range,keep]
      exact ⟨fun h => h.2,fun h => ⟨valU t h,h⟩⟩
    exact (List.toFinset_card_of_nodup nodup).symm.trans (congrArg Finset.card eq)
  · intro j hj x
    have own : j∈U := Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_insert_self _ _⟩
    have kept : n ≤ n+j → n+j < n+C.gates.length → κ (n+j-n)=true := by
      intro _ _
      simpa using (keep j).mpr own
    change (d3r1Fold false GateOp.eval gs (List.ofFn x)).getD (ren j) false =
        (d3r1Fold false GateOp.eval C.gates (List.ofFn x)).getD (n+j) false
    exact d3r1_prune_out false GateOp.eval _ n (by simp) C.gates κ (n+j) bounded closed kept

end Pilot2963
namespace Semantic2963
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.SplitCount PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun idx => w.getD idx false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [gt.op.eval (gt.inputs.map fun idx => acc.getD idx false)]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [List.getD, List.getElem?_append_left hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlen]
  simp [List.getD, hi]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) (gateAt_mem hj)
  unfold opnd
  cases hl : (gateAt C j).inputs with
  | nil => simp [hl] at hlen
  | cons a l =>
    cases l with
    | nil => simp [hl] at hlen
    | cons b l' =>
      cases l' with
      | nil => simp [hl]
      | cons c l'' => simp [hl] at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set step : List Bool → Gate → List Bool :=
    fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]
  set pre := (C.gates.take j).foldl step (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    have h1 := foldl_wires_len (C.gates.take j) (List.ofFn x)
    simp only [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl step (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ i < n + j, (C.gates.foldl step (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [h_eq]
    have hi1 : i < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ i hi1]
    simp only [step]
    have hi2 : i < pre.length := by omega
    simp [List.getD, List.getElem?_append_left hi2]
  have h_nj : (C.gates.foldl step (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [h_eq]
    have hlt : n + j < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ (n + j) hlt]
    simp only [step]
    have hle : pre.length ≤ n + j := by omega
    simp [List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_nj, gate_inputs_eq hAO hj]
  have h0 := h_pre_get (opnd C j 0) (opnd_lt hAO hj 0)
  have h1 := h_pre_get (opnd C j 1) (opnd_lt hAO hj 1)
  simp only [List.map_cons, List.map_nil, ← h0, ← h1]

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by
    rw [wires_length, List.length_ofFn]
    exact hw
  exact List.getD_eq_default _ _ hlen

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input C _ w hlt]
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn]
      have h0 : opnd C (w - n) 0 < w := by
        have := opnd_lt hAO hj 0
        omega
      have h1 : opnd C (w - n) 1 < w := by
        have := opnd_lt hAO hj 1
        omega
      have hv0 := ih (opnd C (w - n) 0) h0 (by omega)
      have hv1 := ih (opnd C (w - n) 1) h1 (by omega)
      rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
      · rw [wval_gate_and hAO _ hj hop, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hop, hv0, hv1]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hx
    by_cases hlt : w < n
    · rw [wval_input C x w hlt] at hx
      rw [wval_input C y w hlt]
      exact hxy ⟨w, hlt⟩ hx
    · by_cases hw : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hwn : w = n + (w - n) := by omega
        rw [hwn] at hx ⊢
        have h0 : opnd C (w - n) 0 < w := by
          have := opnd_lt hAO hj 0
          omega
        have h1 : opnd C (w - n) 1 < w := by
          have := opnd_lt hAO hj 1
          omega
        rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
        · rw [wval_gate_and hAO x hj hop, Bool.and_eq_true] at hx
          rw [wval_gate_and hAO y hj hop, Bool.and_eq_true]
          exact ⟨ih _ h0 hx.1, ih _ h1 hx.2⟩
        · rw [wval_gate_or hAO x hj hop, Bool.or_eq_true] at hx
          rw [wval_gate_or hAO y hj hop, Bool.or_eq_true]
          exact hx.elim (fun h => Or.inl (ih _ h0 h)) (fun h => Or.inr (ih _ h1 h))
      · rw [wval_ge_len C x (by omega)] at hx
        cases hx

theorem coreSplit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (R : Finset ℕ) (imp : ∀ j∈R, BelowF G C j)
    (x : Fin n → Bool) :
    let D := R.biUnion (gammaE G C)
    graphFun G ∅ x = true ↔
      (∃ j∈R, gateVal n C j x = true) ∨ graphFun (G.deleteEdges (D : Set _)) ∅ x = true := by
  classical
  intro D
  have edge (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
      graphFun H ∅ x = true ↔ ∃ u v, H.Adj u v ∧ x u=true ∧ x v=true := by
    simp [graphFun]
  constructor
  · intro yes
    obtain ⟨u,v,uv,xu,xv⟩ := (edge G).mp yes
    by_cases covered : s(u,v) ∈ D
    · left
      obtain ⟨j,hj,hmem⟩ := Finset.mem_biUnion.mp covered
      obtain ⟨_,a,b,eq,acc⟩ := Finset.mem_filter.mp hmem
      have pair : gateVal n C j (pairInput u v) = true := by
        rcases Sym2.eq_iff.mp eq with ⟨e,f⟩ | ⟨e,f⟩
        · simpa only [e,f] using acc
        · have comm : pairInput u v = pairInput a b := by
            funext t
            simp [pairInput,e,f,or_comm]
          rwa [comm]
      refine ⟨j,hj,wval_mono ao (x := pairInput u v) (y := x) ?_ (n+j) pair⟩
      intro t ht
      change decide (t=u ∨ t=v) = true at ht
      rcases of_decide_eq_true ht with rfl | rfl
      · exact xu
      · exact xv
    · right
      exact (edge _).mpr ⟨u,v,SimpleGraph.deleteEdges_adj.mpr ⟨uv,covered⟩,xu,xv⟩
  · rintro (⟨j,hj,val⟩ | rest)
    · exact imp j hj x val
    · obtain ⟨u,v,uv,xu,xv⟩ := (edge _).mp rest
      exact (edge G).mpr ⟨u,v,(SimpleGraph.deleteEdges_adj.mp uv).1,xu,xv⟩

end Semantic2963
namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp


end PEqualNP.MetaComplexity.Helpers
namespace PEqualNP.MetaComplexity.Helpers.EdgeUpperMono

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

/-- `F` is built with at most `s` gates after any wire list of length `m ≥ n` whose first `n`
wires are the inputs. -/
def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ (∀ g ∈ gs, g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, nn1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, nn2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact nn1 g hg
    · exact nn2 g hg
    · subst hg; rcases hop with h | h <;> simp [h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

/-- A built function is computed by a fan-in-two circuit with no NOT gate and at most `s`
gates. -/
theorem bld_circuit {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ GateOp.not) ∧
      circuitFun n D = F ∧ D.size ≤ s := by
  obtain ⟨gs, out, ok, nn, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, nn, ?_, len⟩
  funext x
  have e := ev (List.ofFn x) (by simp)
  simp only [circuitFun, Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

/-- The OR of the inputs in a nonempty list. -/
theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

/-- The OR of the inputs in a nonempty finset `S`, with `|S| - 1` gates. -/
theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in
/-- The edge function of a nonempty set of edges `E` with a cover `T`. -/
theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    -- the star at `t`
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp


end PEqualNP.MetaComplexity.Helpers.EdgeUpperMono
namespace Assemble2963
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.EdgeUpperMono

theorem appendBuilder {n s : ℕ} (K : Circuit) (mono : Monotone2 K)
    (F : (Fin (n+K.size) → Bool) → Bool) (h : Bld (n+K.size) F s) :
    ∃ Q : Circuit, Monotone2 Q ∧ Q.size ≤ K.size+s ∧ ∀ x : Fin n → Bool,
      circuitFun n Q x = F (fun i => (K.wires (List.ofFn x)).getD i.val false) := by
  obtain ⟨gs,out,ok,nn,len,_,ev⟩ := h (n+K.size) le_rfl
  refine ⟨⟨K.gates++gs,out⟩,?_,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hk | hh
    · exact mono g hk
    · obtain ⟨op,two⟩ := ok g hh
      refine ⟨?_,two⟩
      rcases op with a | b | c
      · exact Or.inl a
      · exact Or.inr b
      · exact False.elim (nn g hh c)
  · change (K.gates++gs).length ≤ K.gates.length+s
    rw [List.length_append]
    omega
  · intro x
    change (wiresFrom (K.gates++gs) (List.ofFn x)).getD out false = _
    rw [wiresFrom_append]
    apply ev
    simp [length_wiresFrom,Circuit.size]

theorem liftB {n m s : ℕ} (le : n ≤ m) (F : (Fin n → Bool) → Bool)
    (h : Bld n F s) :
    Bld m (fun x => F (fun i => x ⟨i.val,lt_of_lt_of_le i.isLt le⟩)) s := by
  intro len hl
  exact h len (le.trans hl)

theorem graphB {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hc : G.IsVertexCover (T : Set _)) (he : G.edgeFinset.Nonempty) :
    Bld n (graphFun G ∅) (G.edgeFinset.card+T.card-1) := by
  classical
  have cov : ∀ e∈G.edgeFinset, ∃ t∈T, t∈e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro h
    have adj : G.Adj a b := by simpa using h
    rcases hc adj with aT | bT
    · exact ⟨a,aT,Sym2.mem_mk_left _ _⟩
    · exact ⟨b,bT,Sym2.mem_mk_right _ _⟩
  apply bld_congr (bld_edges n T G.edgeFinset he cov)
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
    decide_eq_true_iff]
  constructor
  · rintro ⟨e,he,on⟩
    revert he on
    refine Sym2.ind (fun a b => ?_) e
    intro hit on
    exact ⟨a,b,by simpa using hit,on a (Sym2.mem_mk_left _ _),on b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨a,b,hit,ha,hb⟩
    exact ⟨s(a,b),by simpa using hit,fun v hv => (Sym2.mem_iff.mp hv).elim
      (fun e => by simpa only [e] using ha) (fun e => by simpa only [e] using hb)⟩

theorem complete {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (T : Finset (Fin n)) (cover : H.IsVertexCover (T : Set _)) (K : Circuit) (mono : Monotone2 K)
    (L : Finset (Fin (n+K.size))) (ne : L.Nonempty)
    (meaning : ∀ x, graphFun G ∅ x = true ↔
      (∃ i∈L, (K.wires (List.ofFn x)).getD i.val false = true) ∨ graphFun H ∅ x = true) :
    ∃ Q : Circuit, Monotone2 Q ∧ circuitFun n Q = graphFun G ∅ ∧
      Q.size+1 ≤ K.size+L.card+H.edgeFinset.card+T.card := by
  classical
  let m := n+K.size
  let taps (y : Fin m → Bool) := decide (∃ i∈L, y i = true)
  have b : Bld m taps (L.card-1) := bld_anyFinset L ne
  have lp := ne.card_pos
  have raw (x : Fin n → Bool) : (fun i : Fin n => (K.wires (List.ofFn x)).getD i.val false)=x := by
    funext i
    rw [wires_eq,getD_wiresFrom _ _ _ (by simpa using i.isLt)]
    simp
  by_cases he : H.edgeFinset.Nonempty
  · let rest (y : Fin m → Bool) := graphFun H ∅ (fun i => y ⟨i.val,by dsimp [m]; omega⟩)
    have brest : Bld m rest (H.edgeFinset.card+T.card-1) :=
      liftB (by dsimp [m]; omega) _ (graphB H T cover he)
    obtain ⟨Q,hQ,size,val⟩ := appendBuilder K mono _ (bld_or b brest)
    refine ⟨Q,hQ,?_,by have := he.card_pos; omega⟩
    funext x
    rw [val,Bool.eq_iff_iff]
    change (taps _ || graphFun H ∅ (fun i => (K.wires (List.ofFn x)).getD i.val false))=true ↔ _
    rw [raw]
    simpa [taps] using (meaning x).symm
  · obtain ⟨Q,hQ,size,val⟩ := appendBuilder K mono _ b
    refine ⟨Q,hQ,?_,by omega⟩
    funext x
    rw [val,Bool.eq_iff_iff]
    have off : graphFun H ∅ x = false := by
      simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
        decide_eq_false_iff_not]
      rintro ⟨a,b,adj,_,_⟩
      exact he ⟨s(a,b),by simpa using adj⟩
    simpa [taps,off] using (meaning x).symm
end Assemble2963
namespace Bridge2963
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Core PEqualNP.TopForm PEqualNP.EdgeOwnership
theorem assembleCores {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (R : Finset ℕ) (nonempty : R.Nonempty) (core : ∀ j∈R, IsCore G C j)
    (T' : Finset (Fin n)) :
    let U := R.biUnion (coneSet n C)
    let D := R.biUnion (gammaE G C)
    let H := G.deleteEdges (D : Set _)
    H.IsVertexCover (T' : Set _) →
    ∃ Q : Circuit, Monotone2 Q ∧ circuitFun n Q = graphFun G ∅ ∧
      Q.size+1 ≤ U.card+R.card+H.edgeFinset.card+T'.card := by
  classical
  intro U D H cover
  obtain ⟨K,ren,mono,size,sem⟩ := Pilot2963.packCones C ao R (fun j hj => (core j hj).1)
  have bound (j : ℕ) (hj : j∈R) : ren j < n+K.size := by
    by_contra! wrong
    obtain ⟨x,hx⟩ := (core j hj).2.1.2
    have same := sem j hj x
    have sz : (K.wires (List.ofFn x)).length=n+K.size := by
      rw [PEqualNP.MetaComplexity.Helpers.wires_eq,PEqualNP.MetaComplexity.Helpers.length_wiresFrom]
      simp [Circuit.size]
    rw [List.getD_eq_default _ _ (by omega),hx] at same
    contradiction
  let tap (j : {i // i∈R}) : Fin (n+K.size) := ⟨ren j.val,bound j.val j.property⟩
  let L := R.attach.image tap
  have lne : L.Nonempty := by
    obtain ⟨j,hj⟩ := nonempty
    exact ⟨tap ⟨j,hj⟩,Finset.mem_image.mpr ⟨⟨j,hj⟩,Finset.mem_attach _ _,rfl⟩⟩
  have small : L.card ≤ R.card := (Finset.card_image_le).trans (by simp)
  have meaning (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      (∃ i∈L, (K.wires (List.ofFn x)).getD i.val false = true) ∨ graphFun H ∅ x = true := by
    have e : graphFun G ∅ x = true ↔ (∃ j∈R, gateVal n C j x = true) ∨ graphFun H ∅ x = true :=
      Semantic2963.coreSplit G C ao R (fun j hj => (core j hj).2.1.1) x
    rw [e]
    refine or_congr ?_ Iff.rfl
    constructor
    · rintro ⟨j,hj,hon⟩
      exact ⟨tap ⟨j,hj⟩,Finset.mem_image.mpr ⟨⟨j,hj⟩,Finset.mem_attach _ _,rfl⟩,(sem j hj x).trans hon⟩
    · rintro ⟨i,hi,hon⟩
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j.val,j.property,(sem j.val j.property x).symm.trans hon⟩
  obtain ⟨Q,hQ,eval,cost⟩ := Assemble2963.complete G H T' cover K mono L lne meaning
  refine ⟨Q,hQ,eval,?_⟩
  change K.size=U.card at size
  omega

theorem subcanonical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (T T' : Finset (Fin n)) (ht : IsMinCover G T) :
    let R := maximalCores G C
    let D := R.biUnion (gammaE G C)
    let U := R.biUnion (coneSet n C)
    let H := G.deleteEdges (D : Set _)
    IsMinCover H T' → U.card+R.card+T'.card < D.card+T.card →
    ∃ Q : Circuit, Monotone2 Q ∧ circuitFun n Q = graphFun G ∅ ∧ Q.size+1 < G.edgeFinset.card+T.card := by
  classical
  intro R D U H rest bad
  have ne : R.Nonempty := by
    by_contra hn
    have hempty : R=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have ed : D=∅ := by simp [D,hempty]
    have hG : H=G := by simp [H,ed]
    have lower := ht.2 T' (hG ▸ rest.1)
    simp [ed,hempty] at bad
    omega
  have core : ∀ j∈R, IsCore G C j := fun j hj => (Finset.mem_filter.mp hj).2.1
  obtain ⟨Q,hQ,eval,cost⟩ := assembleCores G C ao R ne core T' rest.1
  have sub : D ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hj).1
  have remain : H.edgeFinset=G.edgeFinset \ D := by
    ext e
    refine Sym2.ind (fun u v => ?_) e
    simp [H,SimpleGraph.deleteEdges_adj,Finset.mem_sdiff]
  have cnt := Finset.card_sdiff_add_card_eq_card sub
  change Q.size+1 ≤ U.card+R.card+H.edgeFinset.card+T'.card at cost
  rw [←remain] at cnt
  exact ⟨Q,hQ,eval,by omega⟩
end Bridge2963
