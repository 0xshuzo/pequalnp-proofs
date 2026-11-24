import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace Extract3503

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

theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl
      (fun R g => R ++ [(fun ins (g : Gate) => g.op.eval ins) (g.inputs.map fun i => R.getD i false) g])
      x := rfl

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

variable (C : Circuit) (n : ℕ)

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

section
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

end

theorem colorize : ∀ (n m : ℕ) (C : Circuit) (U : Finset ℕ), let N := n+m
      IsAO2 N C → (∀ w ∈ U, w < N ∨ ∃ j < C.gates.length, w = N+j ∧ (gateAt C j).op = GateOp.or ∧
         ∀ a ∈ (gateAt C j).inputs, a ∈ U) → (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ a ∈ (gateAt C j).inputs, a ∈ U) → (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ t : Bool,
       gateVal N C j (fun i => decide (i.val < n) == t) = false) → ∃ S : Bool → Finset ℕ,
      (∀ t w, w ∈ S t → (w < N ∧ decide (w < n) = t) ∨
        ∃ j < C.gates.length, w = N+j ∧ (gateAt C j).op = GateOp.or ∧ ∀ a ∈ (gateAt C j).inputs, a ∈ S t) ∧
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ a b t, (gateAt C j).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t) := by
  intro n m C U N ao closed under zeros
  let bits (t : Bool) (i : Fin N) := decide (i.val < n) == t
  let v (t : Bool) (w : ℕ) := W C N (bits t) w
  have raw (t : Bool) (w : ℕ) (hw : w < N) : v t w = (decide (w < n) == t) :=
    W_input C N (bits t) w hw
  have disj (j : ℕ) (hj : j < C.gates.length) (op : (gateAt C j).op = GateOp.or) (t : Bool) :
      v t (N+j) = (v t (opnd C j 0) || v t (opnd C j 1)) := by
    change W C N (bits t) (N+j) = _
    rw [W_gate C N (bits t) j hj (ao.2.1 j hj),ao_inputs ao hj,op]
    simp [GateOp.eval,v]
  have conj (j : ℕ) (hj : j < C.gates.length) (op : (gateAt C j).op = GateOp.and) (t : Bool) :
      (v t (opnd C j 0) && v t (opnd C j 1)) = false := by
    have h := zeros j hj op t
    change W C N (bits t) (N+j) = false at h
    rw [W_gate C N (bits t) j hj (ao.2.1 j hj),ao_inputs ao hj,op] at h
    simpa [GateOp.eval,v] using h
  have active (w : ℕ) : w ∈ U → ∃ t, v t w = true := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      rcases closed w hw with left | ⟨j,hj,rfl,op,ins⟩
      · exact ⟨decide (w<n),by rw [raw _ w left]; simp⟩
      · obtain ⟨t,ht⟩ := ih (opnd C j 0) (opnd_lt ao hj 0) (ins _ (opnd_mem ao hj 0))
        exact ⟨t,by rw [disj j hj op t,ht]; rfl⟩
  have present (w : ℕ) (h : w ∈ U) : (v false w || v true w) = true := by
    obtain ⟨s,hs⟩ := active w h
    cases s with
    | false => exact Bool.or_eq_true_iff.mpr (Or.inl hs)
    | true => exact Bool.or_eq_true_iff.mpr (Or.inr hs)
  have palette : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
      (a && c) = false → (b && d) = false → (b = false ∧ c = false) ∨ (a = false ∧ d = false) := by decide
  have color : ∀ q t : Bool, (q == !t) = false → q = t := by decide
  let S (t : Bool) := U.filter fun w => v (!t) w = false
  refine ⟨S,?_,?_⟩
  · intro t w hw
    obtain ⟨hu,hv⟩ := Finset.mem_filter.mp hw
    rcases closed w hu with left | ⟨j,hj,rfl,op,ins⟩
    · exact Or.inl ⟨left,color _ t ((raw (!t) w left).symm.trans hv)⟩
    · have sides : v (!t) (opnd C j 0) = false ∧ v (!t) (opnd C j 1) = false := by
        rw [disj j hj op (!t)] at hv
        exact Bool.or_eq_false_iff.mp hv
      refine Or.inr ⟨j,hj,rfl,op,?_⟩
      intro a ha
      apply Finset.mem_filter.mpr
      refine ⟨ins a ha,?_⟩
      rw [ao_inputs ao hj] at ha
      rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using ha :
        a = opnd C j 0 ∨ a = opnd C j 1) with rfl | rfl
      · exact sides.1
      · exact sides.2
  · intro j hj op
    let a := opnd C j 0
    let b := opnd C j 1
    have ha : a ∈ U := under j hj op a (opnd_mem ao hj 0)
    have hb : b ∈ U := under j hj op b (opnd_mem ao hj 1)
    rcases palette _ _ _ _ (present a ha) (present b hb) (conj j hj op false) (conj j hj op true) with h | h
    · exact ⟨a,b,false,ao_inputs ao hj,Finset.mem_filter.mpr ⟨ha,h.1⟩,Finset.mem_filter.mpr ⟨hb,h.2⟩⟩
    · exact ⟨a,b,true,ao_inputs ao hj,Finset.mem_filter.mpr ⟨ha,h.1⟩,Finset.mem_filter.mpr ⟨hb,h.2⟩⟩

end Extract3503
