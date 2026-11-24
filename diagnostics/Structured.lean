import Mathlib
import PEqualNP.Defs

namespace B4895

-- The proof-word semantics and its count-vector equivalence are from L_meta_3756.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section Circuit
private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

private def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

private def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

private lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

private lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

private lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

private lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
    (k : Fin C.size) :
    (evalFrom d op C.gates xs).getD (outWire n k) d =
      op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
        (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
  let front := evalFrom d op (C.gates.take k.val) xs
  have hf : front.length = outWire n k := by
    have hk : k.val ≤ C.gates.length := k.isLt.le
    simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
  have hsplit : evalFrom d op C.gates xs =
      evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
    simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
      List.take_append_drop]
  have hread (i : ℕ) (hi : i < outWire n k) :
      (evalFrom d op C.gates xs).getD i d = front.getD i d := by
    rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
  change (evalFrom d op C.gates xs).getD (outWire n k) d = _
  rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
  rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hf, inputs_two h k]

private lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

private def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

private def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

private def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

private lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

private lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

private lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

private lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (w : ℕ) :
    circuitValue C z w = true ↔
      ∃ t ∈ words n C w, ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ z a = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [value_input C z hb, words_input C hb]
      constructor
      · intro ht
        exact ⟨[w], rfl, fun i hi => ⟨⟨w, hb⟩, by simpa only [List.mem_singleton, eq_comm] using hi, ht⟩⟩
      · rintro ⟨t, ht, hp⟩
        have ht' : t = [w] := ht
        obtain ⟨a, ha, hz⟩ := hp w (by simp [ht'])
        exact (Fin.ext ha : a = ⟨w, hb⟩) ▸ hz
    · have h1 := ih _ (earlier h k 0)
      have h2 := ih _ (earlier h k 1)
      rw [value_gate h z k, words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true, wordOp, Set.mem_ofPred_eq, h1, h2]
        constructor
        · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
          exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
            (List.mem_append.mp hi).elim (htz i) (huz i)⟩
        · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
          exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
            ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
      · rw [ho]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true, wordOp, Set.mem_union, h1, h2]
        exact ⟨fun h => h.elim (fun ⟨t, ht, ha⟩ => ⟨t, Or.inl ht, ha⟩)
          (fun ⟨t, ht, ha⟩ => ⟨t, Or.inr ht, ha⟩),
          fun ⟨t, ht, ha⟩ => ht.elim (fun h => Or.inl ⟨t, h, ha⟩) (fun h => Or.inr ⟨t, h, ha⟩)⟩
    · simp [value_missing C z hb, words_missing n C hb]

private lemma words_nonempty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) : t ≠ [] := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, _, rfl⟩ := ht
        exact fun hh => ih _ (earlier h k 0) hu (List.append_eq_nil_iff.mp hh).1
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hb] at ht

end Circuit

section ReadWitness

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

private lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

private lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

private lemma mem_andStep_one (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 1 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 1 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 2

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 1 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

private def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 1) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 1).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 1))).getD w [] :=
  rfl

private lemma leaf_encode (S : List ℕ) (w : ℕ) :
    S.map (fun j => if j = w then min 1 (1 + 1) else 0) = encode S [w] := by
  unfold encode
  apply List.map_congr_left
  intro a _
  by_cases hea : a = w
  · simp [hea]
  · simp [hea, Ne.symm hea]

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 1)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (1 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec, leaf_encode]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 1)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 1 (andStep 1 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_one _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_one _ _ _).mp hx
        obtain ⟨t, ht, rfl, hts⟩ := ih _ (earlier h k 0) _ hx'
        obtain ⟨u, hu, rfl, hus⟩ := ih _ (earlier h k 1) _ hy
        refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_, fun i hi =>
          (List.mem_append.mp hi).elim (hts i) (hus i)⟩
        have hz' : z = encode S [] := by simpa [encode_nil] using hz
        rw [hz', encode_append, List.nil_append, encode_append]
      · rw [ho] at hv ⊢
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hp | hp
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 0) _ hp
          exact ⟨t, Or.inl ht, he, hs⟩
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 1) _ hp
          exact ⟨t, Or.inr ht, he, hs⟩
    · rw [vec_eval, List.getD_eq_default _ _ (by
        simpa [evalFrom_length, Circuit.size] using hb)] at hv
      simp at hv

private lemma encode_complete {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (t : List ℕ) (ht : t ∈ words n C w) (hs : ∀ i ∈ t, i ∈ S) :
    encode S t ∈ vecs n C S w := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 1)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
      simp only [List.getElem_map, List.getElem_range]
      rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      subst ht'
      have hw : w ∈ S := hs w (by simp)
      simp only [leafVectors, hw, ite_true, List.mem_singleton]
      exact (leaf_encode S w).symm
    · have hlen : ((List.range n).map (leafVectors S 1)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec]
      rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht ⊢
        change encode S t ∈ andStep 1 (andStep 1 [S.map (fun _ => 0)]
          (vecs n C S (operand C k 0))) (vecs n C S (operand C k 1))
        obtain ⟨t1, ht1, t2, ht2, rfl⟩ := ht
        have h1 := ih _ (earlier h k 0) t1 ht1 (fun i hi => hs i (List.mem_append_left _ hi))
        have h2 := ih _ (earlier h k 1) t2 ht2 (fun i hi => hs i (List.mem_append_right _ hi))
        refine (mem_andStep_one _ _ _).mpr ⟨encode S t1, ?_, encode S t2, h2,
          (encode_append S t1 t2).symm⟩
        refine (mem_andStep_one _ _ _).mpr ⟨encode S [], by simp [encode_nil], encode S t1, h1, ?_⟩
        rw [encode_append, List.nil_append]
      · rw [ho] at ht ⊢
        change encode S t ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew [])
        rw [mem_fold_insertNew, mem_fold_insertNew]
        rcases ht with ht | ht
        · exact Or.inl (Or.inr (ih _ (earlier h k 0) t ht hs))
        · exact Or.inr (ih _ (earlier h k 1) t ht hs)
    · rw [words_missing n C hb] at ht
      exact absurd ht (Set.notMem_empty t)

private lemma read_iff {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (S : List ℕ) :
    readsAtMost C n S 1 = true ↔
      ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 1 := by
  constructor
  · intro r
    obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
    obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
    refine ⟨t, ht, hts, fun i hi => ?_⟩
    have hv : min (t.count i) 2 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
    have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
    omega
  · rintro ⟨t, ht, hts, hc⟩
    refine List.any_eq_true.mpr ⟨encode S t, encode_complete h S _ t ht hts, ?_⟩
    refine List.all_eq_true.mpr fun a ha => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have := hc j hj
    exact decide_eq_true (by omega)

end ReadWitness


open PEqualNP.ReadK PEqualNP.TopForm

theorem structured : ∀ (n m : ℕ) (D : Circuit) (S : Bool → Finset ℕ),
      IsAO2 (n+m) D →
      (∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
        ∃ i < D.size, w = n+m+i ∧ (NestedCover.gateAt D i).op = GateOp.or ∧
          ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ S t) →
      (∀ i < D.size, (NestedCover.gateAt D i).op = GateOp.and →
        ∃ a b, (NestedCover.gateAt D i).inputs = [a,b] ∧ a ∈ S false ∧ b ∈ S true) →
      PEqualNP.ReadK.IsReadK (n+m) D 1 := by
  intro n m D S ao closed cross
  have rowEq (k : Fin D.size) : gateAt D k.val = row D k :=
    List.getD_eq_getElem _ _ k.isLt
  have pureWord (w : ℕ) : ∀ (s : Bool), w ∈ S s → ∀ t ∈ words (n+m) D w,
      ∃ a : ℕ, t = [a] ∧ decide (n ≤ a) = s := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro s hw t ht
      rcases closed s w hw with ⟨hlt,hcolor⟩ | ⟨i,hi,rfl,hop,ins⟩
      · rw [words_input D hlt] at ht
        exact ⟨w, ht, hcolor⟩
      · let k : Fin D.size := ⟨i,hi⟩
        have rEq : gateAt D i = row D k := rowEq k
        have rop : (row D k).op = GateOp.or := by simpa only [rEq] using hop
        change t ∈ words (n+m) D (outWire (n+m) k) at ht
        rw [words_gate ao k, rop] at ht
        have child (b : Fin 2) : operand D k b ∈ S s := by
          apply ins
          rw [rEq, inputs_two ao k]
          fin_cases b <;> simp
        rcases ht with ht | ht
        · exact ih _ (earlier ao k 0) s (child 0) t ht
        · exact ih _ (earlier ao k 1) s (child 1) t ht
  have simple (w : ℕ) : ∀ t ∈ words (n+m) D w, t.Nodup := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro t ht
      rcases wire_cases (n+m) D.size w with hb | ⟨k, rfl⟩ | hb
      · rw [words_input D hb] at ht
        have e : t = [w] := ht
        simp [e]
      · rw [words_gate ao k] at ht
        rcases op_kind ao k with hop | hop
        · rw [hop] at ht
          obtain ⟨u, hu, v, hv, rfl⟩ := ht
          have hgo : (gateAt D k.val).op = GateOp.and := by simpa only [rowEq k] using hop
          obtain ⟨a,b,inputs,ha,hb⟩ := cross k.val k.isLt hgo
          rw [rowEq k] at inputs
          have first : operand D k 0 = a := by simp [operand, inputs]
          have second : operand D k 1 = b := by simp [operand, inputs]
          obtain ⟨x, rfl, hx⟩ := pureWord (operand D k 0) false (by simpa only [first] using ha) u hu
          obtain ⟨y, rfl, hy⟩ := pureWord (operand D k 1) true (by simpa only [second] using hb) v hv
          have hxy : x ≠ y := by intro e; subst y; exact Bool.false_ne_true (hx.symm.trans hy)
          simp [hxy]
        · rw [hop] at ht
          exact ht.elim (ih _ (earlier ao k 0) t) (ih _ (earlier ao k 1) t)
      · rw [words_missing (n+m) D hb] at ht
        exact False.elim (Set.notMem_empty t ht)
  intro X prime
  have active : circuitValue D (setInput X) D.output = true := prime.1
  obtain ⟨t, ht, support⟩ := (value_eq_terms ao (setInput X) D.output).mp active
  apply (read_iff ao (setList X)).2
  refine ⟨t, ht, ?_, fun i _ => List.nodup_iff_count_le_one.mp (simple _ t ht) i⟩
  intro i hi
  obtain ⟨a, rfl, ha⟩ := support i hi
  have hm : a ∈ X := of_decide_eq_true ha
  exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨by simp, decide_eq_true hm⟩, rfl⟩

end B4895
