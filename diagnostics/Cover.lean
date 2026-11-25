import PEqualNP.Defs

-- The edge-coverage and cover-circuit proofs below are from L_meta_1599 and L_meta_5355.

namespace PEqualNP.Outside.L_meta_1599
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

/-- The value of wire `w` on input `x`. -/
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

/-- With every AND gate false at `x`, a wire true at `x` is true at a single true input of `x`. -/
theorem single (gates : List Gate) {n : ℕ} (x : Fin n → Bool)
    (hao : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hand : ∀ (k : ℕ) (hk : k < gates.length), gates[k].op = GateOp.and →
      val gates (n + k) x = false) :
    ∀ (b w : ℕ), w < b → val gates w x = true →
      ∃ i : Fin n, x i = true ∧ val gates w (fun r : Fin n => decide (r = i)) = true := by
  intro b
  induction b with
  | zero => intro w hw; omega
  | succ b ih =>
    intro w hw hx
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rw [val_input gates x w hwn] at hx; exact hx
      · rw [val_input gates _ w hwn]; simp
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at hx; exact absurd hx (by simp)
      · have hk : w - n < gates.length := by omega
        have hweq : w = n + (w - n) := by omega
        rw [hweq] at hx ⊢
        rcases hao gates[w - n] (List.getElem_mem hk) with hop | hop
        · rw [hand (w - n) hk hop] at hx; exact absurd hx (by simp)
        · obtain ⟨a, ha, halt, hax⟩ := (val_or gates x (w - n) hk hop).1 hx
          obtain ⟨i, hi, hai⟩ := ih a (by omega) hax
          exact ⟨i, hi, (val_or gates _ (w - n) hk hop).2 ⟨a, ha, halt, hai⟩⟩

end PEqualNP.Outside.L_meta_1599

open PEqualNP.Outside.L_meta_1599 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned n G C := by
  classical
  intro n G _ C hao hfun u v huv
  set x : Fin n → Bool := PEqualNP.EdgeOwnership.pairInput u v with hx
  have hgate : ∀ (k : ℕ) (hk : k < C.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    intro k hk
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hk]
  have hex : ∃ k, k < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and ∧
      PEqualNP.EdgeOwnership.gateVal n C k x = true := by
    by_contra hcon
    push_neg at hcon
    have hand : ∀ (k : ℕ) (hk : k < C.gates.length), C.gates[k].op = GateOp.and →
        val C.gates (n + k) x = false := by
      intro k hk hop
      have := hcon k hk (by rw [hgate k hk]; exact hop)
      have e : PEqualNP.EdgeOwnership.gateVal n C k x = val C.gates (n + k) x := rfl
      rw [e] at this
      simpa using this
    have hout : val C.gates C.output x = true := by
      have h1 := congrFun hfun x
      have e : PEqualNP.MetaComplexity.circuitFun n C x = val C.gates C.output x := rfl
      rw [e] at h1
      rw [h1]
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u, v, huv, by simp [hx, PEqualNP.EdgeOwnership.pairInput],
        by simp [hx, PEqualNP.EdgeOwnership.pairInput]⟩
    obtain ⟨i, _, hi⟩ := single C.gates x hao hand (C.output + 1) C.output (by omega) hout
    have h1 := congrFun hfun (fun r : Fin n => decide (r = i))
    have e : PEqualNP.MetaComplexity.circuitFun n C (fun r : Fin n => decide (r = i))
        = val C.gates C.output (fun r : Fin n => decide (r = i)) := rfl
    rw [e, hi] at h1
    have h2 := h1.symm
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
      decide_eq_true_eq] at h2
    rcases h2 with ⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩
    · simp at ha
    · rw [ha, hb] at hab
      exact G.loopless.irrefl i hab
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  refine ⟨j, hj.1, hj.1, hj.2.1, hj.2.2, ?_⟩
  intro i hi _ hop
  by_contra hne
  have hval : PEqualNP.EdgeOwnership.gateVal n C i x = true := by simpa using hne
  exact Nat.find_min hex hi ⟨lt_trans hi hj.1, hop, hval⟩

namespace PEqualNP.Outside.L_meta_5355

open PEqualNP.CircuitLowerBounds

-- A vertex cover circuit: for each cover vertex c (in increasing order) an OR chain of the
-- neighbours of c not already handled, ANDed with c; the AND gates are ORed together.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

def V {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ fs.map (fun f => f x)

def Sem {n : ℕ} (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ x : Fin n → Bool, wf gs (List.ofFn x) = V fs x

def Val {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (i : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  i < n + fs.length ∧ ∀ x, (V fs x).getD i false = F x

theorem V_append {n : ℕ} (fs fs' : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    V (fs ++ fs') x = V fs x ++ fs'.map (fun f => f x) := by
  simp [V]

theorem V_length {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    (V fs x).length = n + fs.length := by simp [V]

theorem V_read {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) (j : ℕ)
    (hj : j < fs.length) : (V fs x).getD (n + j) false = fs.getD j (fun _ => false) x := by
  simp only [V]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem val_ext {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ} {F : (Fin n → Bool) → Bool}
    (h : Val fs i F) (fs' : List ((Fin n → Bool) → Bool)) : Val (fs ++ fs') i F := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  rw [V_append, List.getD_append _ _ _ _ (by rw [V_length]; exact h.1)]
  exact h.2 x

theorem val_congr {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ}
    {F F' : (Fin n → Bool) → Bool} (h : Val fs i F) (e : ∀ x, F x = F' x) : Val fs i F' :=
  ⟨h.1, fun x => by rw [h.2 x, e x]⟩

theorem val_in {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (a : Fin n) :
    Val fs a.val (fun x => x a) := by
  refine ⟨by omega, fun x => ?_⟩
  simp only [V]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

theorem val_new {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool) :
    Val (fs ++ [f]) (n + fs.length) f := by
  refine ⟨by simp, fun x => ?_⟩
  rw [V_read _ _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem sem_snoc {n : ℕ} {gs : List Gate} {fs : List ((Fin n → Bool) → Bool)} (h : Sem gs fs)
    (op : GateOp) (a b : ℕ) (A B : (Fin n → Bool) → Bool) (ha : Val fs a A) (hb : Val fs b B) :
    Sem (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) := by
  intro x
  rw [wf_snoc, h x, V_append]
  simp only [List.map_cons, List.map_nil, ha.2 x, hb.2 x]

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def St {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (gs : List Gate)
    (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  Sem gs fs ∧ fs.length = gs.length ∧ Mono gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ l, P l ∧ ∀ x, fs.getD j (fun _ => false) x = true → x l = true) ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ c v : Fin n, G.Adj c v ∧
      fs.getD j (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = true ∧
      ∀ i < j, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false)

theorem st_nil {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) : St G P [] [] := by
  refine ⟨fun x => by simp [wf, V], rfl, by simp [Mono], ?_, ?_⟩ <;> simp

theorem st_weak {n : ℕ} {G : SimpleGraph (Fin n)} {P Q : Fin n → Prop} {gs fs}
    (h : St G P gs fs) (hPQ : ∀ l, P l → Q l) : St G Q gs fs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun j hj hand => ?_, h5⟩
  obtain ⟨l, hl, hl2⟩ := h4 j hj hand
  exact ⟨l, hPQ l hl, hl2⟩

theorem push {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} {gs : List Gate}
    {fs : List ((Fin n → Bool) → Bool)} (h : St G P gs fs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (A B : (Fin n → Bool) → Bool)
    (ha : Val fs a A) (hb : Val fs b B)
    (nA : op = GateOp.and → ∃ l, P l ∧ ∀ x, op.eval [A x, B x] = true → x l = true)
    (nB : op = GateOp.and → ∃ c v : Fin n, G.Adj c v ∧
      op.eval [A (PEqualNP.EdgeOwnership.pairInput c v), B (PEqualNP.EdgeOwnership.pairInput c v)]
        = true ∧
      ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false) :
    St G P (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) ∧
      Val (fs ++ [fun x => op.eval [A x, B x]]) (n + fs.length) (fun x => op.eval [A x, B x]) := by
  obtain ⟨hs, hl, hm, hA, hB⟩ := h
  refine ⟨⟨sem_snoc hs op a b A B ha hb, by simp [hl], ?_, ?_, ?_⟩, val_new _ _⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hm g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      rcases hop with e | e <;> simp [e]
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨l, hl1, hl2⟩ := hA j hj hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rwa [List.getD_append _ _ _ _ (by omega)] at hx
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨l, hl1, hl2⟩ := nA hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rw [← hl, List.getD_append_right _ _ _ _ le_rfl] at hx
      simpa using hx
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h1
      · rw [List.getD_append _ _ _ _ (by omega)] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := nB hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [← hl, List.getD_append_right _ _ _ _ le_rfl]
        simpa using h1
      · rw [List.getD_append _ _ _ _ hi] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'

theorem chain {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} :
    ∀ (rest : List (Fin n)) (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (a : ℕ)
      (A : (Fin n → Bool) → Bool), St G P gs fs → Val fs a A →
      ∃ gs' fs' o, St G P gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
        gs'.length = gs.length + rest.length ∧
        Val fs' o (fun x => A x || rest.any (fun w => x w))
  | [], gs, fs, a, A, h, ha => ⟨gs, fs, a, h, ⟨[], by simp⟩, by simp, by simpa using ha⟩
  | w :: rest, gs, fs, a, A, h, ha => by
    obtain ⟨h1, h2⟩ := push h GateOp.or (Or.inr rfl) a w.val A (fun x => x w) ha (val_in fs w)
      (fun e => by simp at e) (fun e => by simp at e)
    obtain ⟨gs', fs', o, h3, ⟨fsn, hfs⟩, hlen, hv⟩ := chain rest _ _ _ _ h1 h2
    refine ⟨gs', fs', o, h3, ⟨(fun x => GateOp.or.eval [A x, x w]) :: fsn, by rw [hfs]; simp⟩, ?_, ?_⟩
    · rw [hlen]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    refine ⟨hv.1, fun x => ?_⟩
    rw [hv.2 x]
    simp [GateOp.eval, Bool.or_assoc]

def N {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj c w ∧ ¬ (w ∈ C ∧ w < c))

def gad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n)
    (x : Fin n → Bool) : Bool :=
  x c && decide (∃ w ∈ N G C c, x w = true)

theorem gad_empty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {c : Fin n} (h : N G C c = ∅) (x : Fin n → Bool) : gad G C c x = false := by
  simp [gad, h]

theorem gadget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {P : Fin n → Prop} (c : Fin n) (hP : ∀ l, P l → l ∈ C ∧ l < c) (hne : (N G C c).Nonempty)
    (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (h : St G P gs fs) :
    ∃ gs' fs' o, St G (fun l => P l ∨ l = c) gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
      gs'.length = gs.length + (N G C c).card ∧ Val fs' o (gad G C c) := by
  have hL : (N G C c).toList ≠ [] := by
    rw [Ne, Finset.toList_eq_nil]; exact hne.ne_empty
  obtain ⟨w0, rest, hL⟩ := List.exists_cons_of_ne_nil hL
  have hw0 : w0 ∈ N G C c := by
    rw [← Finset.mem_toList, hL]; exact List.mem_cons_self
  have hcard : (N G C c).card = rest.length + 1 := by
    rw [← Finset.length_toList, hL]; simp
  have key : ∀ x : Fin n → Bool,
      (x w0 || rest.any (fun w => x w)) = decide (∃ w ∈ N G C c, x w = true) := by
    intro x
    have : (x w0 || rest.any (fun w => x w)) = (N G C c).toList.any (fun w => x w) := by
      rw [hL]; simp
    rw [this, Bool.eq_iff_iff]
    simp [List.any_eq_true, Finset.mem_toList]
  obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ :=
    chain rest gs fs w0.val (fun x => x w0) h (val_in fs w0)
  have hlab := h1.2.2.2.1
  have hl1 := h1.2.1
  obtain ⟨h2, hv2⟩ := push (st_weak (Q := fun l => P l ∨ l = c) h1 (fun l hl => Or.inl hl)) GateOp.and (Or.inl rfl) c.val o1
    (fun x => x c) _ (val_in fs1 c) hv1
    (fun _ => ⟨c, Or.inr rfl, fun x hx => by simp [GateOp.eval] at hx; exact hx.1⟩)
    (fun _ => ⟨c, w0, by
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0; exact hw0.1, by
        simp [GateOp.eval, PEqualNP.EdgeOwnership.pairInput], by
        intro i hi hand
        obtain ⟨l, hl, hl2⟩ := hlab i hi hand
        obtain ⟨hlC, hlc⟩ := hP l hl
        cases hval : fs1.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c w0) with
        | false => rfl
        | true =>
          exfalso
          have := hl2 _ hval
          simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at this
          rcases this with rfl | rfl
          · exact lt_irrefl _ hlc
          · simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
            exact hw0.2 ⟨hlC, hlc⟩⟩)
  refine ⟨_, _, n + fs1.length, h2, ⟨fsn ++ [fun x => GateOp.and.eval [x c, x w0 || rest.any fun w => x w]], by rw [hfs]; simp⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, hlen1, hcard]; omega
  refine val_congr hv2 (fun x => ?_)
  simp only [GateOp.eval, gad, ← key x]
  simp

theorem build {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (S : Finset (Fin n)) : S ⊆ C →
    ∃ gs fs, St G (fun l => l ∈ S) gs fs ∧
      ((gs = [] ∧ ∀ c ∈ S, N G C c = ∅) ∨
       ∃ o, Val fs o (fun x => decide (∃ c ∈ S, gad G C c x = true)) ∧
         gs.length + 1 ≤ (∑ c ∈ S, (N G C c).card) + S.card) := by
  induction S using Finset.induction_on_max with
  | empty => intro _; exact ⟨[], [], st_nil G _, Or.inl ⟨rfl, by simp⟩⟩
  | insert c S hlt ih =>
    intro hsub
    have hcS : c ∉ S := fun hc => lt_irrefl _ (hlt c hc)
    obtain ⟨gs, fs, h, hcase⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
    have hP : ∀ l, l ∈ S → l ∈ C ∧ l < c :=
      fun l hl => ⟨hsub (Finset.mem_insert_of_mem hl), hlt l hl⟩
    by_cases hN : N G C c = ∅
    · refine ⟨gs, fs, st_weak h (fun l hl => Finset.mem_insert_of_mem hl), ?_⟩
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · left
        refine ⟨hg, ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hN
        · exact hall c' hc'
      · right
        refine ⟨o, val_congr hv ?_, ?_⟩
        · intro x
          simp [Finset.mem_insert, gad_empty hN]
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]; omega
    · have hne : (N G C c).Nonempty := Finset.nonempty_iff_ne_empty.2 hN
      obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ := gadget c hP hne gs fs h
      have h1' : St G (fun l => l ∈ insert c S) gs1 fs1 := by
        refine st_weak h1 ?_
        intro l hl
        rcases hl with hl | rfl
        · exact Finset.mem_insert_of_mem hl
        · exact Finset.mem_insert_self _ _
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · refine ⟨gs1, fs1, h1', Or.inr ⟨o1, val_congr hv1 ?_, ?_⟩⟩
        · intro x
          have : ¬ ∃ c' ∈ S, gad G C c' x = true := by
            rintro ⟨c', hc', hg'⟩
            rw [gad_empty (hall c' hc')] at hg'
            exact Bool.false_ne_true hg'
          rw [Bool.eq_iff_iff]
          simp only [decide_eq_true_eq, Finset.mem_insert]
          constructor
          · intro hx; exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact hx
            · exact absurd ⟨c', hc', hx⟩ this
        · subst hg
          rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp at hlen1
          omega
      · obtain ⟨h2, hv2⟩ := push h1' GateOp.or (Or.inr rfl) o o1 _ _
          (by rw [hfs]; exact val_ext hv fsn) hv1 (fun e => by simp at e) (fun e => by simp at e)
        refine ⟨_, _, h2, Or.inr ⟨_, val_congr hv2 ?_, ?_⟩⟩
        · intro x
          rw [Bool.eq_iff_iff]
          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id,
            Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
          constructor
          · rintro (⟨c', hc', hx⟩ | hx)
            · exact ⟨c', Or.inr hc', hx⟩
            · exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact Or.inr hx
            · exact Or.inl ⟨c', hc', hx⟩
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp only [List.length_append, List.length_singleton]
          omega

theorem edge_N {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) {u v : Fin n} (h : G.Adj u v) :
    ∃ c ∈ C, ∃ w ∈ N G C c, (c = u ∧ w = v) ∨ (c = v ∧ w = u) := by
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hC u v h with hu | hv
  · by_cases hv' : v ∈ C ∧ v < u
    · refine ⟨v, hv'.1, u, ⟨h.symm, fun hh => lt_asymm hh.2 hv'.2⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨u, hu, v, ⟨h, hv'⟩, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases hu' : u ∈ C ∧ u < v
    · exact ⟨u, hu'.1, v, ⟨h, fun hh => lt_asymm hh.2 hu'.2⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, hv, u, ⟨h.symm, hu'⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem any_gad {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) (x : Fin n → Bool) :
    decide (∃ c ∈ C, gad G C c x = true) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := by
  rw [Bool.eq_iff_iff]
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, gad, decide_eq_true_eq,
    Bool.and_eq_true, Bool.or_eq_true, Finset.notMem_empty, false_and, exists_false,
    false_or]
  constructor
  · rintro ⟨c, -, hc, w, hw, hxw⟩
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨c, w, hw.1, hc, hxw⟩
  · rintro ⟨u, v, h, hu, hv⟩
    obtain ⟨c, hc, w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := edge_N hC h
    · exact ⟨c, hc, hu, w, hw, hv⟩
    · exact ⟨c, hc, hv, w, hw, hu⟩

theorem sumN_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) :
    ∑ c ∈ C, (N G C c).card ≤ G.edgeSet.ncard := by
  rw [← Finset.card_sigma]
  have : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [this]
  apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp.2.1
  · rintro ⟨c, w⟩ hp ⟨c', w'⟩ hq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; rfl
    · exfalso
      subst h1; subst h2
      have e1 : ¬ w < c := fun hl => hp.2.2 ⟨hq.1, hl⟩
      have e2 : ¬ c < w := fun hl => hq.2.2 ⟨hp.1, hl⟩
      have : c = w := le_antisymm (not_lt.1 e1) (not_lt.1 e2)
      subst this
      exact G.irrefl hp.2.1

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hC : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size ≤ G.edgeSet.ncard + C.card - 1 ∧
      ∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n D j u v := by
  have hC' : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C := hC
  obtain ⟨gs, fs, ⟨hs, hl, hm, -, hB⟩, hcase⟩ := build G C C (subset_refl _)
  rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
  · subst hg
    refine ⟨⟨[], n⟩, by simp [PEqualNP.MetaComplexity.Monotone2], ?_, by simp [Circuit.size], ?_⟩
    · funext x
      rw [← any_gad hC' x]
      have : ¬ ∃ c ∈ C, gad G C c x = true := by
        rintro ⟨c', hc', hg'⟩
        rw [gad_empty (hall c' hc')] at hg'
        exact Bool.false_ne_true hg'
      simp only [this, decide_false]
      show (wf [] (List.ofFn x)).getD n false = false
      simp only [wf, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp)
    · intro j hj
      simp [Circuit.size] at hj
  · refine ⟨⟨gs, o⟩, hm, ?_, ?_, ?_⟩
    · funext x
      show (wf gs (List.ofFn x)).getD o false = _
      rw [hs x, hv.2 x]
      exact any_gad hC' x
    · have h1 := sumN_le G C
      show gs.length ≤ _
      omega
    · intro j hj hand
      have hj' : j < gs.length := hj
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj' hand
      have gv : ∀ i, i < gs.length → ∀ y : Fin n → Bool,
          PEqualNP.EdgeOwnership.gateVal n ⟨gs, o⟩ i y = fs.getD i (fun _ => false) y := by
        intro i hi y
        show (wf gs (List.ofFn y)).getD (n + i) false = _
        rw [hs y, V_read _ _ _ (by omega)]
      refine ⟨c, v, hadj, hj', hand, by rw [gv j hj']; exact h1, ?_⟩
      intro i hi _ hand'
      rw [gv i (by omega)]
      exact h2 i hi hand'

end PEqualNP.Outside.L_meta_5355

theorem PEqualNP.Outside.L_meta_5355 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x4 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x6.size ≤ x2.edgeSet.ncard + x4.card - (1 : ℕ) ∧ ∀ x7 < x6.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro x1 x2 x3 x4 h
  exact PEqualNP.Outside.L_meta_5355.main x1 x2 x4 h
namespace PEqualNP.Outside.L_meta_2450_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
attribute [local instance] gateOpDecEq

noncomputable def owners (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => ∃ u v, G.Adj u v ∧ Owns n C j u v

theorem mem_owners {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {j : ℕ} :
    j ∈ owners n G C ↔ ∃ u v, G.Adj u v ∧ Owns n C j u v := by
  classical
  constructor
  · intro hj
    exact (Finset.mem_filter.mp hj).2
  · rintro ⟨u,v,adj,huv⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huv.1,u,v,adj,huv⟩

theorem centers {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (star : HasStarProfile n G C) (owned : EveryEdgeOwned n G C) :
    ∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧ T.card ≤ (owners n G C).card := by
  classical
  have hc (i : ↥(owners n G C)) : ∃ c : Fin n,
      ∀ u v, G.Adj u v → Owns n C i.val u v → u = c ∨ v = c := by
    obtain ⟨u,v,adj,huv⟩ := mem_owners.mp i.property
    rcases star i.val huv.1 huv.2.1 with no | yes
    · exact False.elim (no u v adj huv)
    · exact yes
  let center (i : ↥(owners n G C)) := Classical.choose (hc i)
  let T := Finset.univ.image center
  refine ⟨T, ?_, ?_⟩
  · intro u v adj
    obtain ⟨j,_,h⟩ := owned u v adj
    let i : ↥(owners n G C) := ⟨j,mem_owners.mpr ⟨u,v,adj,h⟩⟩
    have hi : center i ∈ T := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    rcases Classical.choose_spec (hc i) u v adj h with h1 | h2
    · exact Or.inl (h1.symm ▸ hi)
    · exact Or.inr (h2.symm ▸ hi)
  · calc
      T.card ≤ (Finset.univ : Finset ↥(owners n G C)).card := Finset.card_image_le
      _ = _ := by simp

theorem price {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hm : Monotone2 C) (hf : circuitFun n C = graphFun G ∅)
    (least : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (star : HasStarProfile n G C) (hne : C.gates.length ≠ 0) :
    ((Finset.range C.gates.length) \ owners n G C).card + 1 ≤ G.edgeSet.ncard := by
  classical
  have hao : AndOrOnly C := by
    intro g hg
    exact (Set.mem_insert_iff.mp (hm g hg).1).imp id Set.mem_singleton_iff.mp
  obtain ⟨T,hT,hcard⟩ := centers star (PEqualNP.Outside.L_meta_1599 n G C hao hf)
  obtain ⟨D, hD, hfun, hsz, _⟩ := PEqualNP.Outside.L_meta_5355 n G T hT
  have sizeD := least D hD hfun
  have sub : owners n G C ⊆ Finset.range C.gates.length := by
    intro i hi
    obtain ⟨u,v,_,h⟩ := mem_owners.mp hi
    exact Finset.mem_range.mpr h.1
  have card := Finset.card_sdiff_add_card_eq_card sub
  rw [Finset.card_range] at card
  change C.gates.length ≤ D.size at sizeD
  omega

noncomputable def ors (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = GateOp.or

theorem all_own_of_or_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hm : Monotone2 C) (hf : circuitFun n C = graphFun G ∅)
    (least : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (star : HasStarProfile n G C) (hor : G.edgeSet.ncard ≤ (ors C).card + 1) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n C j u v := by
  classical
  intro j hj hand
  by_contra hempty
  have bound := price G C hm hf least star (by omega)
  have sub : ors C ⊆ Finset.range C.gates.length \ owners n G C := by
    intro i hi
    obtain ⟨hi, hiop⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_sdiff.mpr
    refine ⟨hi, ?_⟩
    intro ho
    obtain ⟨_,_,_,h⟩ := mem_owners.mp ho
    have handI := h.2.1
    change (gateAt C i).op = GateOp.or at hiop
    rw [handI] at hiop
    cases hiop
  have hmissing : j ∈ Finset.range C.gates.length \ owners n G C :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj, fun h => hempty (mem_owners.mp h)⟩
  have hjnot : j ∉ ors C := by
    intro h
    have hw := (Finset.mem_filter.mp h).2
    change (gateAt C j).op = GateOp.or at hw
    rw [hand] at hw
    cases hw
  have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨sub, fun he => hjnot (he.symm ▸ hmissing)⟩)
  omega

end PEqualNP.Outside.L_meta_2450_aux
namespace PEqualNP.Outside.L_meta_5355
open PEqualNP.CircuitLowerBounds
theorem profiled (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hC : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size ≤ G.edgeSet.ncard + C.card - 1 ∧
      PEqualNP.EdgeOwnership.HasStarProfile n G D ∧
      ∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n D j u v := by
  have hC' : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C := hC
  obtain ⟨gs, fs, ⟨hs, hl, hm, hA, hB⟩, hcase⟩ := build G C C (subset_refl _)
  rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
  · subst hg
    refine ⟨⟨[], n⟩, by simp [PEqualNP.MetaComplexity.Monotone2], ?_, by simp [Circuit.size], ?_, ?_⟩
    · funext x
      rw [← any_gad hC' x]
      have : ¬ ∃ c ∈ C, gad G C c x = true := by
        rintro ⟨c', hc', hg'⟩
        rw [gad_empty (hall c' hc')] at hg'
        exact Bool.false_ne_true hg'
      simp only [this, decide_false]
      show (wf [] (List.ofFn x)).getD n false = false
      simp only [wf, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp)
    · intro j hj
      simp at hj
    · intro j hj
      simp [Circuit.size] at hj
  · refine ⟨⟨gs, o⟩, hm, ?_, ?_, ?_, ?_⟩
    · funext x
      show (wf gs (List.ofFn x)).getD o false = _
      rw [hs x, hv.2 x]
      exact any_gad hC' x
    · have h1 := sumN_le G C
      show gs.length ≤ _
      omega
    · intro j hj hand
      change j < gs.length at hj
      obtain ⟨l,_,hl⟩ := hA j hj hand
      right
      refine ⟨l,?_⟩
      intro u v _ huv
      have hv := huv.2.2.1
      change (wf gs (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD (n+j) false = true at hv
      rw [hs, V_read _ _ _ (by omega)] at hv
      have hp := hl (PEqualNP.EdgeOwnership.pairInput u v) hv
      change decide (l = u ∨ l = v) = true at hp
      exact (of_decide_eq_true hp).imp Eq.symm Eq.symm
    · intro j hj hand
      have hj' : j < gs.length := hj
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj' hand
      have gv : ∀ i, i < gs.length → ∀ y : Fin n → Bool,
          PEqualNP.EdgeOwnership.gateVal n ⟨gs, o⟩ i y = fs.getD i (fun _ => false) y := by
        intro i hi y
        show (wf gs (List.ofFn y)).getD (n + i) false = _
        rw [hs y, V_read _ _ _ (by omega)]
      refine ⟨c, v, hadj, hj', hand, by rw [gv j hj']; exact h1, ?_⟩
      intro i hi _ hand'
      rw [gv i (by omega)]
      exact h2 i hi hand'

end PEqualNP.Outside.L_meta_5355
namespace PEqualNP.Outside.L_meta_2450_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
attribute [local instance] gateOpDecEq

theorem or_deficit_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hm : Monotone2 C) (hf : circuitFun n C = graphFun G ∅) (star : HasStarProfile n G C)
    (hor : G.edgeSet.ncard ≤ (ors C).card + 2) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      HasStarProfile n G D ∧ ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∃ u v, G.Adj u v ∧ Owns n D j u v := by
  classical
  by_cases all : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ u v, G.Adj u v ∧ Owns n C j u v
  · exact ⟨C,hm,hf,le_rfl,star,all⟩
  push Not at all
  obtain ⟨j,hj,hand,hbad⟩ := all
  have hao : AndOrOnly C := fun g hg =>
    (Set.mem_insert_iff.mp (hm g hg).1).imp id Set.mem_singleton_iff.mp
  obtain ⟨T,hT,hcard⟩ := centers star (PEqualNP.Outside.L_meta_1599 n G C hao hf)
  obtain ⟨D,hD,hfun,hsz,profile,own⟩ :=
    PEqualNP.Outside.L_meta_5355.profiled n G T hT
  refine ⟨D,hD,hfun,?_,profile,own⟩
  let R := Finset.range C.gates.length \ owners n G C
  have hnot : j ∉ owners n G C := by
    intro hi
    obtain ⟨u,v,adj,h⟩ := mem_owners.mp hi
    exact hbad u v adj h
  have hR : j ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj,hnot⟩
  have hjnot : j ∉ ors C := by
    intro h
    have hw := (Finset.mem_filter.mp h).2
    change (gateAt C j).op = GateOp.or at hw
    rw [hand] at hw
    cases hw
  have sub : ors C ⊆ R := by
    intro i hi
    obtain ⟨hi,hiop⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_sdiff.mpr
    refine ⟨hi,?_⟩
    intro hp
    obtain ⟨_,_,_,h⟩ := mem_owners.mp hp
    change (gateAt C i).op = GateOp.or at hiop
    rw [h.2.1] at hiop
    cases hiop
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨sub, fun he => hjnot (he.symm ▸ hR)⟩)
  have hparts : R.card + (owners n G C).card = C.gates.length := by
    rw [← Finset.card_range C.gates.length]
    apply Finset.card_sdiff_add_card_eq_card
    intro i hi
    obtain ⟨_,_,_,h⟩ := mem_owners.mp hi
    exact Finset.mem_range.mpr h.1
  change D.size ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_2450_aux
