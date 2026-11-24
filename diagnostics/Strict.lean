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

theorem endpointUnionStrict {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hC : IsAO2 n C) (R : Finset ℕ) (rn : R.Nonempty) (core : ∀ j∈R, IsCore G C j) :
    let D := R.biUnion (gammaE G C)
    let U := R.biUnion (coneSet n C)
    let V := Finset.univ.filter (fun v : Fin n => ∃ e∈D, v∈e)
    V.card+1 ≤ U.card+R.card := by
  classical
  intro D U V
  let S := U ×ˢ (Finset.univ : Finset (Fin 2))
  let I := S.image (slotW C)
  have rootSub : R⊆U := by
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_insert_self _ _⟩
  have named {j : ℕ} (hj : j ∈ R) {w : ℕ} (hw : w ∈ (slots n C j).image (slotW C)) :
      w ∈ I := by
    obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hw
    have hK := (Finset.mem_product.mp hab).1
    exact Finset.mem_image.mpr ⟨ab,Finset.mem_product.mpr
      ⟨Finset.mem_biUnion.mpr ⟨j,hj,hK⟩,Finset.mem_univ _⟩,rfl⟩
  have hV : V.card ≤ (I.filter (fun w => w < n)).card := by
    apply Finset.card_le_card_of_injOn (fun v : Fin n => v.val)
    · intro v hv
      obtain ⟨e,he,ve⟩ := (Finset.mem_filter.mp hv).2
      obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨heG,u,r,rfl,acc⟩ := Finset.mem_filter.mp he
      have adj : G.Adj u r := by simpa using heG
      have h := core j hj
      rcases Sym2.mem_iff.mp ve with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨named hj (end_mem G hC h.1 h.2.1.1 adj acc),Fin.is_lt _⟩
      · exact Finset.mem_filter.mpr ⟨named hj (end_mem G hC h.1 h.2.1.1 adj.symm
          (by rw [pairInput_comm]; exact acc)),Fin.is_lt _⟩
    · exact fun _ _ _ _ eq => Fin.ext eq
  have hInt : (U \ R).card ≤ (I.filter (fun w => ¬ w < n)).card := by
    apply Finset.card_le_card_of_injOn (fun g => n+g)
    · intro g hg
      obtain ⟨hU,notR⟩ := Finset.mem_sdiff.mp hg
      obtain ⟨j,hj,hK⟩ := Finset.mem_biUnion.mp hU
      have ne : g≠j := fun eq => notR (eq ▸ hj)
      obtain ⟨a,ha,b,eq⟩ := K_cover hC (core j hj).1 hK ne
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨j,hj,ha⟩,Finset.mem_univ _⟩,eq⟩,by change ¬ n+g < n; omega⟩
    · intro g _ h _ eq
      exact Nat.add_left_cancel eq
  have parts := Finset.card_filter_add_card_filter_not (s := I) (fun w => w < n)
  have count : S.card=U.card*2 := by simp [S]
  have image : I.card < S.card := by
    apply lt_of_le_of_ne Finset.card_image_le
    intro eq
    obtain ⟨j,hjR⟩ := rn
    obtain ⟨hj, _, _, u0, v0, _, hacc0, hrt⟩ := core j hjR
    have allInj : Set.InjOn (slotW C) S := Finset.card_image_iff.mp eq
    have hinj : Set.InjOn (slotW C) (slots n C j) := by
      apply allInj.mono
      intro p hp
      exact Finset.mem_product.mpr ⟨Finset.mem_biUnion.mpr
        ⟨j,hjR,(Finset.mem_product.mp hp).1⟩,Finset.mem_univ _⟩
    have hjK' : j ∈ coneSet n C j := Finset.mem_insert_self _ _
    have hne := vec_ne hC u0 v0 (n + j) (by omega) hacc0
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
    have hle := vec_le_one hC hj hinj u0.val v0.val u0.isLt v0.isLt j hjK' w hw
    apply absurd hrt
    unfold PEqualNP.Core.ReadTwiceAt PEqualNP.ReadK.readsAtMost
    simp only [Bool.not_eq_false]
    rw [List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [List.all_eq_true]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    have := hle i
    rw [List.getD_eq_getElem _ _ hi] at this
    simpa using this
  have diff := Finset.card_sdiff_add_card_eq_card rootSub
  omega


end Pilot2963
