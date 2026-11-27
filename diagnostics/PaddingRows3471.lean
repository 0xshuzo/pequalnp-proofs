import PEqualNP.Defs
namespace Padding3471


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


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def run (gs : List Gate) (xs : List Bool) : List Bool :=
  evalFrom false GateOp.eval gs xs

private lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, evalFrom, List.foldl_append]

private lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length :=
  evalFrom_length false GateOp.eval gs xs

private lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma essential_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  suffices hh : Finset.range n ⊆ S by
    have := Finset.card_le_card hh
    simp only [Finset.card_range] at this
    simp only [Finset.card_singleton] at hS
    unfold Circuit.size
    omega
  intro i hi
  by_contra hni
  let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := he a
  apply hne
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro e
    have he : j = i := congrArg Fin.val e
    exact hni (he ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

private lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

private def pair {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

private def point {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p)

private def line {N : ℕ} (l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.natAdd N l)

private def Thin {N : ℕ} (z : Fin (N+N) → Bool) : Prop :=
  ∀ l l' : Fin N, z (Fin.natAdd N l) = true → z (Fin.natAdd N l') = true → l = l'

private lemma thin_pair {N : ℕ} (p l : Fin N) : Thin (pair p l) := by
  intro i j hi hj
  simp only [pair,decide_eq_true_eq] at hi hj
  exact Fin.natAdd_injective _ _ ((hi.resolve_left (Ne.symm (cast_ne_nat p i))).trans (hj.resolve_left (Ne.symm (cast_ne_nat p j))).symm)

private lemma thin_point {N : ℕ} (p : Fin N) : Thin (point p) := by
  intro i j hi
  exact ((cast_ne_nat p i) (of_decide_eq_true hi).symm).elim

private lemma thin_line {N : ℕ} (l : Fin N) : Thin (line l) := by
  intro i j hi hj
  simp [line] at hi hj
  exact hi.trans hj.symm

private lemma plane_support (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hq2 : 2 ≤ q) : N + N ≤ C.size + 1 := by
  have htwo : 2 ≤ N := by nlinarith
  have hpair (p l : Fin N) (h : I p l) : circuitFun (N + N) C (pair p l) = true := by
    rw [hC _ (thin_pair p l), decide_eq_true_eq]
    exact ⟨p, l, h, by simp [pair], by simp [pair]⟩
  have hpoint (p : Fin N) : circuitFun (N + N) C (point p) = false := by
    rw [hC _ (thin_point p), decide_eq_false_iff_not]
    rintro ⟨_, l, _, _, h⟩
    exact cast_ne_nat p l (of_decide_eq_true h).symm
  have hline (l : Fin N) : circuitFun (N + N) C (line l) = false := by
    rw [hC _ (thin_line l), decide_eq_false_iff_not]
    rintro ⟨p, _, _, h, _⟩
    exact cast_ne_nat p l (of_decide_eq_true h)
  apply essential_bound C (fun g hg => (hAO.2.2 g hg).le)
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    have hex : ∃ p' : Fin N, p ≠ p' := by
      by_cases hz : p.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by have hh := congrArg Fin.val h; simp at hh; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => hz (congrArg Fin.val h)⟩
    obtain ⟨p', hn⟩ := hex
    obtain ⟨l, hi, _⟩ := hp p p' hn
    refine ⟨pair p l, line l, fun j hj => ?_, by rw [hpair p l hi.1, hline]; decide⟩
    simp [pair, line, hj]
  · intro l
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun p => I p l)).card by
      rw [hl]; omega)
    refine ⟨pair p l, point p, fun j hj => ?_,
      by rw [hpair p l (Finset.mem_filter.mp hp).2, hpoint]; decide⟩
    simp only [pair, point, hj, or_false]


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

private lemma mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 2 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 3

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 2 (encode S t) (encode S u) = encode S (t ++ u) := by
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
  | .and => ins.foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 2).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 2))).getD w [] :=
  rfl

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (2 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 2 (andStep 2 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_two _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_two _ _ _).mp hx
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

private lemma read_to_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (r : readsAtMost C n S 2 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 2 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 3 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega

end ReadWitness


section Degrees

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

private def on (N : ℕ) (X Y : Set (Fin N)) (w : ℕ) : Prop :=
  (∃ p ∈ X, (p : ℕ) = w) ∨ ∃ l ∈ Y, N + (l : ℕ) = w

private lemma on_point {N : ℕ} (X Y : Set (Fin N)) (p : Fin N) :
    on N X Y p.val ↔ p ∈ X := by
  constructor
  · rintro (⟨q, hq, hv⟩ | ⟨l, _, hv⟩)
    · exact (Fin.ext hv : q = p) ▸ hq
    · omega
  · exact fun hp => Or.inl ⟨p, hp, rfl⟩

private lemma on_line {N : ℕ} (X Y : Set (Fin N)) (l : Fin N) :
    on N X Y (N + l.val) ↔ l ∈ Y := by
  constructor
  · rintro (⟨p, _, hv⟩ | ⟨l', hl', hv⟩)
    · omega
    · exact (Fin.ext (Nat.add_left_cancel hv) : l' = l) ▸ hl'
  · exact fun hl => Or.inr ⟨l, hl, rfl⟩

private noncomputable def bits {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) : Bool := by
  classical
  exact decide (on N X Y i.val)

private lemma bits_true {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) :
    bits X Y i = true ↔ on N X Y i.val := by
  classical
  simp [bits]

private def pcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (w < N)).length
private def lcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (N ≤ w)).length

private lemma sum_counts (N : ℕ) (t : List ℕ) : pcount N t + lcount N t = t.length := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    by_cases h : a < N
    · have hn : ¬ N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega
    · have hn : N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega

private def Hom (N : ℕ) (C : Circuit) (w a b : ℕ) (X Y : Set (Fin N)) : Prop :=
  ∃ t ∈ words (N + N) C w, pcount N t = a ∧ lcount N t = b ∧ ∀ j ∈ t, on N X Y j

private lemma hom_mono {N : ℕ} {C : Circuit} {w a b : ℕ} {X X' Y Y' : Set (Fin N)}
    (hx : X ⊆ X') (hy : Y ⊆ Y') (h : Hom N C w a b X Y) : Hom N C w a b X' Y' := by
  obtain ⟨t, ht, ha, hb, hxy⟩ := h
  exact ⟨t, ht, ha, hb, fun j hj => (hxy j hj).imp
    (fun ⟨p, hp, he⟩ => ⟨p, hx hp, he⟩) (fun ⟨l, hl, he⟩ => ⟨l, hy hl, he⟩)⟩

private lemma hom_pure_x {N : ℕ} {C : Circuit} {w a : ℕ} {X Y : Set (Fin N)} :
    Hom N C w a 0 X Y ↔ Hom N C w a 0 X ∅ := by
  refine ⟨?_, hom_mono (fun _ h => h) (Set.empty_subset _)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with hp | ⟨l, _, hl⟩
  · exact Or.inl hp
  · have hn : N ≤ j := by omega
    have hmem : j ∈ t.filter (fun w => decide (N ≤ w)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold lcount at hb
    rw [List.length_eq_zero_iff.mp hb] at hmem
    simp at hmem

private lemma hom_pure_y {N : ℕ} {C : Circuit} {w b : ℕ} {X Y : Set (Fin N)} :
    Hom N C w 0 b X Y ↔ Hom N C w 0 b ∅ Y := by
  refine ⟨?_, hom_mono (Set.empty_subset _) (fun _ h => h)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, _, hp⟩ | hl
  · have hn : j < N := hp ▸ p.isLt
    have hmem : j ∈ t.filter (fun w => decide (w < N)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold pcount at ha
    rw [List.length_eq_zero_iff.mp ha] at hmem
    simp at hmem
  · exact Or.inr hl

private lemma hom_invalid {N : ℕ} {C : Circuit} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : N + N + C.size ≤ w) : ¬ Hom N C w a b X Y := by
  simp [Hom, words_missing _ _ hw]

private lemma hom_pos {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C w a b X Y) : 0 < a + b := by
  obtain ⟨t, ht, ha, hb, _⟩ := hh
  rw [← ha, ← hb, sum_counts]
  exact List.length_pos_iff.mpr (words_nonempty h ht)

private lemma hom_input {N : ℕ} {C : Circuit} {w a b : ℕ} {X Y : Set (Fin N)} (hw : w < N + N) :
    Hom N C w a b X Y ↔ on N X Y w ∧
      ((w < N ∧ a = 1 ∧ b = 0) ∨ (N ≤ w ∧ a = 0 ∧ b = 1)) := by
  unfold Hom
  rw [words_input C hw]
  by_cases h : w < N
  · have h' : ¬ N ≤ w := by omega
    simp [pcount, lcount, h, h', eq_comm, and_comm, and_left_comm, and_assoc]
  · have h' : N ≤ w := by omega
    simp [pcount, lcount, h, h', eq_comm, and_comm, and_left_comm, and_assoc]

private lemma hom_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {a b : ℕ} {X Y : Set (Fin N)} :
    Hom N C (outWire (N + N) k) a b X Y ↔
      ∃ i : Fin 2, Hom N C (operand C k i) a b X Y := by
  rw [Fin.exists_fin_two]
  unfold Hom
  rw [words_gate h k, ho]
  simp only [wordOp, Set.mem_union]
  exact ⟨fun ⟨t, hr, he⟩ => hr.imp (fun ht => ⟨t, ht, he⟩) (fun ht => ⟨t, ht, he⟩),
    fun h => h.elim (fun ⟨t, ht, he⟩ => ⟨t, Or.inl ht, he⟩) (fun ⟨t, ht, he⟩ => ⟨t, Or.inr ht, he⟩)⟩

private lemma hom_and {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {a b : ℕ} {X Y : Set (Fin N)} :
    Hom N C (outWire (N + N) k) a b X Y ↔
      ∃ a₀ b₀ a₁ b₁ : ℕ, a₀ + a₁ = a ∧ b₀ + b₁ = b ∧
        Hom N C (operand C k 0) a₀ b₀ X Y ∧ Hom N C (operand C k 1) a₁ b₁ X Y := by
  unfold Hom
  rw [words_gate h k, ho]
  constructor
  · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, ha, hb, hxy⟩
    exact ⟨pcount N t, lcount N t, pcount N u, lcount N u, by simpa [pcount] using ha,
      by simpa [lcount] using hb, ⟨t, ht, rfl, rfl, fun j hj => hxy j (List.mem_append_left _ hj)⟩,
      ⟨u, hu, rfl, rfl, fun j hj => hxy j (List.mem_append_right _ hj)⟩⟩
  · rintro ⟨a₀, b₀, a₁, b₁, ha, hb, ⟨t, ht, rfl, rfl, hxy⟩, ⟨u, hu, rfl, rfl, hxy'⟩⟩
    exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, by simpa [pcount] using ha,
      by simpa [lcount] using hb, fun j hj => (List.mem_append.mp hj).elim (hxy j) (hxy' j)⟩

private lemma hom_and_add {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) (i : Fin 2)
    {a b c d : ℕ} {X Y : Set (Fin N)}
    (h₁ : Hom N C (operand C k i) a b X Y)
    (h₂ : Hom N C (operand C k (1 - i)) c d X Y) :
    Hom N C (outWire (N + N) k) (a + c) (b + d) X Y := by
  apply (hom_and h ho).mpr
  fin_cases i
  · exact ⟨a, b, c, d, rfl, rfl, h₁, h₂⟩
  · exact ⟨c, d, a, b, Nat.add_comm _ _, Nat.add_comm _ _, h₂, h₁⟩

private lemma hom_sound {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C w a b X Y) :
    circuitValue C (bits X Y) w = true := by
  obtain ⟨t, ht, _, _, hxy⟩ := hh
  apply (value_eq_terms h _ _).mpr
  refine ⟨t, ht, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
  · exact ⟨Fin.castAdd N p, rfl, (bits_true _ _ _).mpr ((on_point X Y p).mpr hp)⟩
  · exact ⟨Fin.natAdd N l, rfl, (bits_true _ _ _).mpr ((on_line X Y l).mpr hl)⟩

end Degrees


open Finset

section Charging


variable {A B W E : Type*} [Fintype A] [Fintype B]
variable (I : A → B → Prop) [DecidableRel I]

private def fourFree : Prop :=
  ∀ ⦃c d : B⦄, c ≠ d → ∀ ⦃a b : A⦄, I a c → I a d → I b c → I b d → a = b

private noncomputable def single (f : Set A → Prop) : Finset A := by
  classical
  exact univ.filter (fun a => f {a})

private lemma mem_single (f : Set A → Prop) (a : A) : a ∈ single f ↔ f {a} := by
  classical
  simp [single]

private def clean (f : Set A → Prop) (c : B) : Prop :=
  ¬ f {a | ¬ I a c}

private lemma clean_single {f : Set A → Prop} (hm : Monotone f) {a : A} {c : B}
    (hc : clean I f c) (ha : a ∈ single f) : I a c := by
  by_contra hn
  exact hc (hm (Set.singleton_subset_iff.mpr hn) ((mem_single f a).mp ha))

private def almost (s : Finset A) (c : B) : Prop :=
  (s.filter fun a => ¬ I a c).card ≤ 1

private def approved (simple : Prop) (f : Set A → Prop) (c : B) : Prop :=
  (2 ≤ (single f).card ∧ clean I f c) ∨
    (simple ∧ 4 ≤ (single f).card ∧ almost I (single f) c)

private lemma almost_of_clean {f : Set A → Prop} (hm : Monotone f) {c : B}
    (hc : clean I f c) : almost I (single f) c := by
  classical
  have hzero : (single f).filter (fun a => ¬ I a c) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact (Finset.mem_filter.mp ha).2 (clean_single I hm hc (Finset.mem_filter.mp ha).1)
  simp [almost, hzero]

private lemma almost_mono {s t : Finset A} (hst : s ⊆ t) {c : B}
    (h : almost I t c) : almost I s c :=
  (Finset.card_le_card (Finset.filter_subset_filter _ hst)).trans h

private lemma almost_unique (hf : fourFree I) (s : Finset A) (hs : 4 ≤ s.card)
    {c d : B} (hc : almost I s c) (hd : almost I s d) : c = d := by
  classical
  by_contra hcd
  let good := s.filter (fun a => I a c ∧ I a d)
  have hgood : good.card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr ?_
    intro a b ha hb
    exact hf hcd (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
      (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb).2.2
  let badC := s.filter (fun a => ¬ I a c)
  let badD := s.filter (fun a => ¬ I a d)
  have hcover : s ⊆ good ∪ (badC ∪ badD) := by
    intro a ha
    by_cases h1 : I a c <;> by_cases h2 : I a d <;> simp [good, badC, badD, ha, h1, h2]
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le good (badC ∪ badD))
  have hbad := Finset.card_union_le badC badD
  change badC.card ≤ 1 at hc
  change badD.card ≤ 1 at hd
  omega

private lemma exact_unique (hf : fourFree I) {f : Set A → Prop} (hm : Monotone f)
    (hs : 2 ≤ (single f).card) {c d : B} (hc : clean I f c) (hd : clean I f d) : c = d := by
  classical
  by_contra hcd
  have hcard : (single f).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr ?_
    intro a b ha hb
    exact hf hcd (clean_single I hm hc ha) (clean_single I hm hd ha)
      (clean_single I hm hc hb) (clean_single I hm hd hb)
  omega

private lemma approved_unique (hf : fourFree I) {simple : Prop} {f : Set A → Prop}
    (hm : Monotone f) {c d : B} (hc : approved I simple f c) (hd : approved I simple f d) :
    c = d := by
  rcases hc with ⟨hs, hc⟩ | ⟨_, hs, hc⟩ <;> rcases hd with ⟨_, hd⟩ | ⟨_, hsd, hd⟩
  · exact exact_unique I hf hm hs hc hd
  · exact almost_unique I hf _ hsd (almost_of_clean I hm hc) hd
  · exact almost_unique I hf _ hs hc (almost_of_clean I hm hd)
  · exact almost_unique I hf _ hs hc hd

private lemma small_unapproved (simple : Prop) (f : Set A → Prop) (c : B)
    (simple_spec : simple → ∀ U, f U ↔ ∃ a ∈ single f, a ∈ U)
    (h : ¬ approved I simple f c)
    (ha : clean I f c ∨ simple ∧ almost I (single f) c) :
    ((single f).filter fun a => I a c).card ≤ 2 := by
  classical
  by_contra hbad
  have hs : 3 ≤ (single f).card := by
    have hcard := Finset.card_filter_le (single f) (fun a => I a c)
    omega
  rcases ha with hc | ⟨hsim, halm⟩
  · exact h (Or.inl ⟨by omega, hc⟩)
  by_cases h4 : 4 ≤ (single f).card
  · exact h (Or.inr ⟨hsim, h4, halm⟩)
  have hcard := Finset.card_filter_add_card_filter_not
    (s := single f) (p := fun a => I a c)
  have he : ((single f).filter fun a => ¬ I a c).card = 0 := by omega
  have hempty := Finset.card_eq_zero.mp he
  have hclean : clean I f c := by
    intro ht
    obtain ⟨a, ha, hni⟩ := (simple_spec hsim _).mp ht
    have hm' : a ∈ (single f).filter (fun a => ¬ I a c) := Finset.mem_filter.mpr ⟨ha, hni⟩
    simp [hempty] at hm'
  exact h (Or.inl ⟨by omega, hclean⟩)

private noncomputable def edgeCover (f : W → Set A → Prop) (simple : W → Prop) : Finset (A × B) := by
  classical
  exact univ.filter (fun p => I p.1 p.2 ∧ ∃ w, approved I (simple w) (f w) p.2 ∧
    p.1 ∈ single (f w))

private lemma cover_bound (hf : fourFree I) (f : W → Set A → Prop) (simple : W → Prop)
    (rank : W → ℕ) (arcs : Finset E) (src dst : E → W)
    (hm : ∀ w, Monotone (f w))
    (hs : ∀ w, simple w → ∀ U, f w U ↔ ∃ a ∈ single (f w), a ∈ U)
    (hr : ∀ w,
      (∀ c, ¬ approved I (simple w) (f w) c) ∨
      (∃ u v, rank u < rank w ∧ rank v < rank w ∧ ¬ simple w ∧
        ∀ U, f w U ↔ f u U ∧ f v U) ∨
      ((∀ e ∈ arcs, src e = w → rank (dst e) < rank w ∧ (simple w → simple (dst e))) ∧
        ∀ U, f w U ↔ ∃ e ∈ arcs, src e = w ∧ f (dst e) U)) :
    (edgeCover I f simple).card ≤ 2 * arcs.card := by
  classical
  let Pay (e : E) : Finset (A × B) := univ.filter fun p => I p.1 p.2 ∧
    approved I (simple (src e)) (f (src e)) p.2 ∧
    ¬ approved I (simple (dst e)) (f (dst e)) p.2 ∧
    (clean I (f (dst e)) p.2 ∨ simple (dst e) ∧ almost I (single (f (dst e))) p.2) ∧
    p.1 ∈ single (f (dst e))
  have pay_card (e : E) : (Pay e).card ≤ 2 := by
    by_cases hn : (Pay e).Nonempty
    · obtain ⟨p, hp⟩ := hn
      have hpv := (Finset.mem_filter.mp hp).2
      refine le_trans (Finset.card_le_card_of_injOn (t := (single (f (dst e))).filter (fun a => I a p.2)) Prod.fst ?_ ?_) ?_
      · intro q hq
        have hqv := (Finset.mem_filter.mp hq).2
        have he := approved_unique I hf (hm (src e)) hqv.2.1 hpv.2.1
        exact Finset.mem_filter.mpr ⟨hqv.2.2.2.2, he ▸ hqv.1⟩
      · intro q hq r hrr he
        exact Prod.ext he (approved_unique I hf (hm (src e))
          (Finset.mem_filter.mp hq).2.2.1 (Finset.mem_filter.mp hrr).2.2.1)
      · exact small_unapproved I _ _ _ (hs (dst e)) hpv.2.2.1 hpv.2.2.2.1
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have descend (w : W) (p : A × B) (hi : I p.1 p.2)
      (ha : approved I (simple w) (f w) p.2) (hsp : p.1 ∈ single (f w)) :
      ∃ e ∈ arcs, p ∈ Pay e := by
    induction ht : rank w using Nat.strong_induction_on generalizing w with
    | ind k ih =>
      rcases hr w with hl | ⟨u, v, hu, hv, hn, hmeet⟩ | ⟨hsub, hunion⟩
      · exact (hl _ ha).elim
      · have hw := (mem_single _ _).mp hsp
        obtain ⟨hpu, hpv⟩ := (hmeet _).mp hw
        obtain ⟨_, hc⟩ := ha.resolve_right (fun h => hn h.1)
        have hcu : clean I (f u) p.2 ∨ clean I (f v) p.2 := by
          by_cases hu : f u {a | ¬ I a p.2}
          · exact Or.inr (fun hv => hc ((hmeet _).mpr ⟨hu, hv⟩))
          · exact Or.inl hu
        have hSu : single (f w) ⊆ single (f u) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).1
        have hSv : single (f w) ⊆ single (f v) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).2
        have hs2 : 2 ≤ (single (f w)).card := (ha.resolve_right (fun h => hn h.1)).1
        rcases hcu with hcu | hcv
        · exact ih (rank u) (ht ▸ hu) u (Or.inl ⟨hs2.trans (Finset.card_le_card hSu), hcu⟩)
            ((mem_single _ _).mpr hpu) rfl
        · exact ih (rank v) (ht ▸ hv) v (Or.inl ⟨hs2.trans (Finset.card_le_card hSv), hcv⟩)
            ((mem_single _ _).mpr hpv) rfl
      · obtain ⟨e, he, hew, hep⟩ := (hunion _).mp ((mem_single _ _).mp hsp)
        have hsub' : single (f (dst e)) ⊆ single (f w) := by
          intro a ha'
          exact (mem_single _ _).mpr ((hunion _).mpr ⟨e, he, hew, (mem_single _ _).mp ha'⟩)
        have hnext : clean I (f (dst e)) p.2 ∨
            simple (dst e) ∧ almost I (single (f (dst e))) p.2 := by
          rcases ha with ⟨_, hc⟩ | ⟨hsw, _, hd⟩
          · exact Or.inl (fun hb => hc ((hunion _).mpr ⟨e, he, hew, hb⟩))
          · exact Or.inr ⟨(hsub e he hew).2 hsw, almost_mono I hsub' hd⟩
        by_cases hnext' : approved I (simple (dst e)) (f (dst e)) p.2
        · exact ih (rank (dst e)) (ht ▸ (hsub e he hew).1) _ hnext'
            ((mem_single _ _).mpr hep) rfl
        · refine ⟨e, he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ?_, hnext', hnext,
            (mem_single _ _).mpr hep⟩⟩
          simpa only [hew] using ha
  have hcover : edgeCover I f simple ⊆ arcs.biUnion Pay := by
    intro p hp
    obtain ⟨hi, w, ha, hsp⟩ := (Finset.mem_filter.mp hp).2
    exact Finset.mem_biUnion.mpr (descend w p hi ha hsp)
  calc
    _ ≤ (arcs.biUnion Pay).card := Finset.card_le_card hcover
    _ ≤ ∑ e ∈ arcs, (Pay e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ arcs, 2 := Finset.sum_le_sum (fun e _ => pay_card e)
    _ = _ := by simp [Nat.mul_comm]

end Charging


section Plane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private lemma plane_four_free
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) : fourFree I := by
  intro l l' hll p p' hp hpl' hp' hp'l'
  by_contra hpp
  obtain ⟨_, _, hunique⟩ := hu p p' hpp
  exact hll ((hunique l ⟨hp, hp'⟩).trans (hunique l' ⟨hpl', hp'l'⟩).symm)

private lemma pair_prime
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} (hi : I p l) :
    IsPrimeImplicant (N + N) C {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  have small (T : Finset (Fin (N+N))) (hT : T ⊆ {Fin.castAdd N p, Fin.natAdd N l}) :
      Thin (setInput T) := by
    intro i j hi hj
    have eqv (k : Fin N) (hk : setInput T (Fin.natAdd N k) = true) : k = l := by
      have hv := hT (of_decide_eq_true hk)
      exact Fin.natAdd_injective _ _ (Finset.mem_singleton.mp ((Finset.mem_insert.mp hv).resolve_left (Ne.symm (cast_ne_nat p k))))
    exact (eqv i hi).trans (eqv j hj).symm
  constructor
  · rw [hC _ (small _ (fun _ h => h)), decide_eq_true_eq]
    exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    have hT' := Finset.mem_ssubsets.mp hT
    rw [hC _ (small _ hT'.subset), decide_eq_false_iff_not]
    rintro ⟨p', l', _, hp, hl⟩
    have hp' : Fin.castAdd N p' ∈ T := of_decide_eq_true hp
    have hl' : Fin.natAdd N l' ∈ T := of_decide_eq_true hl
    have pe : Fin.castAdd N p' = Fin.castAdd N p := by
      have := Finset.mem_insert.mp (hT'.subset hp')
      exact this.resolve_right (fun hm => cast_ne_nat p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd N l' = Fin.natAdd N l := by
      have := Finset.mem_insert.mp (hT'.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => cast_ne_nat p l' e.symm))
    exact hT'.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

private lemma setList_pair {p l : Fin N} (j : ℕ) :
    j ∈ setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ↔
      j = p.val ∨ j = N + l.val := by
  simp only [setList, List.mem_map, List.mem_filter, decide_eq_true_eq, List.mem_finRange,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Fin.castAdd N p, Or.inl rfl, rfl⟩
    · exact ⟨Fin.natAdd N l, Or.inr rfl, rfl⟩

private lemma pair_counts {p l : Fin N} (t : List ℕ)
    (ht : ∀ a ∈ t, a = p.val ∨ a = N + l.val) :
    pcount N t = t.count p.val ∧ lcount N t = t.count (N + l.val) := by
  have hp : p.val < N := p.isLt
  have hne : p.val ≠ N + l.val := by omega
  have hl : ¬ N + l.val < N := by omega
  induction t with
  | nil => simp [pcount, lcount]
  | cons j t ih =>
    obtain ⟨h1, h2⟩ := ih (fun a ha => ht a (List.mem_cons_of_mem _ ha))
    change (t.filter _).length = _ at h1 h2
    rcases ht j (by simp) with rfl | rfl
    · have hpn : ¬ N ≤ p.val := by omega
      simp [pcount, lcount, hp, hpn, hne, Ne.symm hne, h1, h2, List.count_cons]
    · simp [pcount, lcount, hl, hne, Ne.symm hne, h1, h2, List.count_cons]

private lemma singleton_sound {N : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hC : ∀ z : Fin (N+N) → Bool, Thin z → circuitFun (N+N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {X Y : Set (Fin N)} {a b : ℕ} (hy : ∀ i ∈ Y, ∀ j ∈ Y, i = j)
    (hh : Hom N C C.output a b X Y) : ∃ p ∈ X, ∃ l ∈ Y, I p l := by
  have hv := hom_sound h hh
  change circuitFun (N+N) C (bits X Y) = true at hv
  have ly (i : Fin N) (hi : bits X Y (Fin.natAdd N i) = true) : i ∈ Y :=
    (on_line X Y i).mp ((bits_true _ _ _).mp hi)
  rw [hC _ (fun i j hi hj => hy i (ly i hi) j (ly j hj)), decide_eq_true_eq] at hv
  obtain ⟨p,l,hi,hp,hl⟩ := hv
  exact ⟨p,(on_point X Y p).mp ((bits_true _ _ _).mp hp),l,ly l hl,hi⟩

private lemma plane_read_cover
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} (hi : I p l) (hr : readsAtMost C (N+N) (setList {Fin.castAdd N p, Fin.natAdd N l}) 2 = true) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ 2 ∧ 1 ≤ b ∧ b ≤ 2 ∧ Hom N C C.output a b {p} {l} := by
  obtain ⟨t, ht, hs, hu⟩ := read_to_terms h _
    hr
  obtain ⟨hp, hl⟩ := pair_counts (p := p) (l := l) t
    (fun j hj => (setList_pair j).mp (hs j hj))
  have hh : Hom N C C.output (pcount N t) (lcount N t) {p} {l} := by
    refine ⟨t, ht, rfl, rfl, fun j hj => ?_⟩
    rcases (setList_pair j).mp (hs j hj) with rfl | rfl
    · exact (on_point _ _ p).mpr (by simp)
    · exact (on_line _ _ l).mpr (by simp)
  have hp1 : 1 ≤ pcount N t := by
    by_contra! hn
    have he : pcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨a, ha, _⟩ := singleton_sound I h hC (by simp) (hom_pure_y.mp hh)
    exact ha
  have hl1 : 1 ≤ lcount N t := by
    by_contra! hn
    have he : lcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨_, _, b, hb, _⟩ := singleton_sound I h hC (by simp) (hom_pure_x.mp hh)
    exact hb
  exact ⟨_, _, hp1, hp ▸ hu _ ((setList_pair _).mpr (Or.inl rfl)),
    hl1, hl ▸ hu _ ((setList_pair _).mpr (Or.inr rfl)), hh⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


end Plane

private def addGate (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op,[a,b]⟩], n + C.size⟩

private lemma addSize (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (addGate n C op a b).size = C.size + 1 := by simp [Circuit.size, addGate]

private lemma addAO {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : ℕ} (ha : a < n+C.size) (hb : b < n+C.size) :
    PEqualNP.TopForm.IsAO2 n (addGate n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.1 g hg
    · obtain rfl := List.mem_singleton.mp hg
      exact hop
  · intro j hj i hi
    change j < (C.gates ++ [_]).length at hj
    change i ∈ ((C.gates ++ [_]).getD j _).inputs at hi
    by_cases hj' : j < C.gates.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact h.2.1 j hj' i hi
    · simp only [List.length_append, List.length_singleton] at hj
      obtain rfl : j = C.gates.length := by omega
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.2.2 g hg
    · obtain rfl := List.mem_singleton.mp hg
      rfl

private lemma evalLast {α : Type} (d : α) (f : GateOp → List α → α) (xs : List α)
    {n : ℕ} (hx : xs.length = n) (C : Circuit) (op : GateOp) (a b i : ℕ) :
    (evalFrom d f (addGate n C op a b).gates xs).getD i d =
    if i = n+C.size then f op [(evalFrom d f C.gates xs).getD a d,(evalFrom d f C.gates xs).getD b d]
    else (evalFrom d f C.gates xs).getD i d := by
  let w := evalFrom d f C.gates xs
  have hl : w.length = n+C.size := by simp [w,evalFrom_length,hx,Circuit.size]
  change (evalFrom d f (C.gates ++ [_]) xs).getD i d = _
  simp only [evalFrom,List.foldl_append,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil]
  change (w ++ [f op [w.getD a d,w.getD b d]]).getD i d = if i = n+C.size then _ else w.getD i d
  rcases lt_trichotomy i (n+C.size) with hi | rfl | hi
  · rw [if_neg hi.ne,List.getD_append _ _ _ _ (by omega)]
  · rw [if_pos rfl,List.getD_append_right _ _ _ _ (by omega)]
    simp [hl] <;> rfl
  · rw [if_neg hi.ne',List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

private lemma wordLast (n : ℕ) (C : Circuit) (op : GateOp) (a b i : ℕ) :
    words n (addGate n C op a b) i = if i = n+C.size then
      wordOp op [words n C a,words n C b] else words n C i :=
  evalLast _ _ _ List.length_ofFn _ _ _ _ _

private lemma boolLast {n : ℕ} (C : Circuit) (z : Fin n → Bool) (op : GateOp) (a b i : ℕ) :
    circuitValue (addGate n C op a b) z i = if i = n+C.size then
      op.eval [circuitValue C z a,circuitValue C z b] else circuitValue C z i :=
  evalLast _ _ _ List.length_ofFn _ _ _ _ _

open PEqualNP.GenericRejection

private def activeP {N : ℕ} (z : Fin (N+N) → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun p => z (Fin.castAdd N p) = true

private def activeL {N : ℕ} (z : Fin (N+N) → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun l => z (Fin.natAdd N l) = true

private lemma inputRep {N : ℕ} (z : Fin (N+N) → Bool) :
    incidenceInput (activeP z) (activeL z) = List.ofFn z := by
  unfold incidenceInput
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [activeP]
  · intro l
    rw [Fin.append_right]
    simp [activeL]

private lemma thinCorrect {N q : ℕ} {S : Fin N → Finset (Fin N)} {C : Circuit}
    (hq : 1 ≤ q) (h : PEqualNP.TopForm.IsAO2 (N+N) C) (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    (z : Fin (N+N) → Bool) (hz : Thin z) :
    circuitFun (N+N) C z = decide (∃ p l : Fin N, p ∈ S l ∧
      z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  classical
  by_cases he : ∃ p l : Fin N, p ∈ S l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
  · rw [decide_eq_true he]
    obtain ⟨p,l,hi,hp,hl⟩ := he
    have hinput : List.ofFn (pair p l) = incidenceInput ({p} : Finset (Fin N)) ({l} : Finset (Fin N)) := by
      unfold incidenceInput
      rw [← List.ofFn_fin_append]
      congr 1
      funext k
      refine Fin.addCases ?_ ?_ k
      · intro i
        simp only [pair,Fin.append_left,Finset.mem_singleton,cast_ne_nat i l,or_false,
          EmbeddingLike.apply_eq_iff_eq]
        simp
      · intro i
        simp only [pair,Fin.append_right,Finset.mem_singleton,Ne.symm (cast_ne_nat p i),false_or]
        simp
    have hv : circuitValue C (pair p l) C.output = true := by
      change C.eval (List.ofFn (pair p l)) = true
      rw [hinput]
      exact hr l p hi
    obtain ⟨t,ht,ha⟩ := (value_eq_terms h _ _).mp hv
    apply (value_eq_terms h _ _).mpr
    refine ⟨t,ht,?_⟩
    intro j hj
    obtain ⟨i,hi,hb⟩ := ha j hj
    refine ⟨i,hi,?_⟩
    rcases (of_decide_eq_true hb : i = Fin.castAdd N p ∨ i = Fin.natAdd N l) with rfl | rfl
    · exact hp
    · exact hl
  · rw [decide_eq_false he]
    change C.eval (List.ofFn z) = false
    rw [← inputRep z]
    apply hf
    · apply le_trans _ hq
      exact Finset.card_le_one_iff.mpr (fun {i} {j} hi hj =>
        hz i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
    · intro l hl
      apply Finset.disjoint_left.mpr
      intro p hp hz
      exact he ⟨p,l,hp,(Finset.mem_filter.mp hz).2,(Finset.mem_filter.mp hl).2⟩


open PEqualNP.ReadK
private def rich (N : ℕ) (C : Circuit) (k : ℕ) : Prop :=
  ∀ (p l : Fin N) (t : List ℕ), t ∈ words (N+N) C C.output →
    (∀ j ∈ t, on N {p} {l} j) → k ≤ pcount N t ∧ k ≤ lcount N t

private def dup (n : ℕ) (C : Circuit) (op : GateOp) : Circuit := addGate n C op C.output C.output

private lemma dupOr {N : ℕ} (C : Circuit) (k : ℕ) (h : rich N C k) : rich N (dup (N+N) C .or) k := by
  intro p l t ht hfit
  change t ∈ words (N+N) (addGate (N+N) C .or C.output C.output) (N+N+C.size) at ht
  rw [wordLast,if_pos rfl] at ht
  exact h p l t (ht.elim id id) hfit

private lemma dupAnd {N : ℕ} (C : Circuit) (k : ℕ) (h : rich N C k) : rich N (dup (N+N) C .and) (k+k) := by
  intro p l t ht hfit
  change t ∈ words (N+N) (addGate (N+N) C .and C.output C.output) (N+N+C.size) at ht
  rw [wordLast,if_pos rfl] at ht
  obtain ⟨u,hu,v,hv,rfl⟩ := ht
  obtain ⟨p1,l1⟩ := h p l u hu (fun j hj => hfit j (List.mem_append_left _ hj))
  obtain ⟨p2,l2⟩ := h p l v hv (fun j hj => hfit j (List.mem_append_right _ hj))
  simpa [pcount,lcount] using
    And.intro (Nat.add_le_add p1 p2) (Nat.add_le_add l1 l2)

private lemma dupVal {n : ℕ} (C : Circuit) (op : GateOp) (hop : op=.and ∨ op=.or) (z : Fin n → Bool) :
    circuitFun n (dup n C op) z = circuitFun n C z := by
  change circuitValue (addGate n C op C.output C.output) z (n+C.size) = circuitValue C z C.output
  rw [boolLast,if_pos rfl]
  rcases hop with rfl|rfl <;> cases circuitValue C z C.output <;> rfl

theorem allHardWithThreeGates (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 1 ≤ q) (ao : PEqualNP.TopForm.IsAO2 (N+N) C) (ho : C.output<N+N+C.size)
    (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N+N) D ∧ D.size=C.size+3 ∧
      N+N ≤ D.output ∧ D.output < N+N+D.size ∧
      (∃ g, D.gates[D.output-(N+N)]?=some g ∧ g.op=GateOp.or) ∧
      circuitFun (N+N) D = circuitFun (N+N) C ∧
      ∀ p l : Fin N, p∈S l → readsAtMost D (N+N) (setList {Fin.castAdd N p,Fin.natAdd N l}) 2=false := by
  classical
  let I := fun p l : Fin N => p ∈ S l
  letI : DecidableRel I := fun p l => inferInstanceAs (Decidable (p ∈ S l))
  have thin := thinCorrect hq ao hr hf
  have initial : rich N C 1 := by
    intro p l t ht hfit
    have hh : Hom N C C.output (pcount N t) (lcount N t) {p} {l} := ⟨t,ht,rfl,rfl,hfit⟩
    constructor
    · by_contra! hn
      have e : pcount N t=0 := by omega
      rw [e] at hh
      obtain ⟨a,ha,_⟩ := singleton_sound I ao thin (by simp) (hom_pure_y.mp hh)
      exact ha
    · by_contra! hn
      have e : lcount N t=0 := by omega
      rw [e] at hh
      obtain ⟨_,_,b,hb,_⟩ := singleton_sound I ao thin (by simp) (hom_pure_x.mp hh)
      exact hb
  let A := dup (N+N) C .and
  let B := dup (N+N) A .and
  let D := dup (N+N) B .or
  have sa : A.size=C.size+1 := addSize .. 
  have sb : B.size=A.size+1 := addSize ..
  have sd : D.size=B.size+1 := addSize ..
  have ha : PEqualNP.TopForm.IsAO2 (N+N) A := addAO ao (Or.inl rfl) ho ho
  have oa : A.output<N+N+A.size := by change N+N+C.size < _; omega
  have hb : PEqualNP.TopForm.IsAO2 (N+N) B := addAO ha (Or.inl rfl) oa oa
  have ob : B.output<N+N+B.size := by change N+N+A.size < _; omega
  have hd : PEqualNP.TopForm.IsAO2 (N+N) D := addAO hb (Or.inr rfl) ob ob
  have output : D.output=N+N+B.size := rfl
  have semantics : circuitFun (N+N) D = circuitFun (N+N) C := by
    funext z
    exact (dupVal B .or (Or.inr rfl) z).trans ((dupVal A .and (Or.inl rfl) z).trans (dupVal C .and (Or.inl rfl) z))
  refine ⟨D,hd,by omega,by omega,by omega,?_,semantics,?_⟩
  · refine ⟨⟨.or,[B.output,B.output]⟩,?_,rfl⟩
    rw [output,Nat.add_sub_cancel_left]
    simp [D,dup,addGate,Circuit.size]
  · intro p l hi
    apply Bool.eq_false_iff.mpr
    intro low
    obtain ⟨a,b,-,a2,-,b2,t,ht,eq1,eq2,hfit⟩ := plane_read_cover I hd (by rw [semantics]; exact thin) hi low
    have heavy : rich N D 4 := dupOr B 4 (dupAnd A 2 (dupAnd C 1 initial))
    have wt := heavy p l t ht hfit
    omega

end Padding3471
