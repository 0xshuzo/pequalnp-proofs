import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18910.Boundary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
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


abbrev P := Fin 17
def E (p q : P) := ([33216,36352,61440,70208,74880,84224] : List Nat).getD p.val 0 |>.testBit q.val
def V (c : Circuit) (k : Nat) (x : P → Bool) := (c.wires (List.ofFn x)).getD k false
def c : Circuit := ⟨[⟨.or,[6,7]⟩,⟨.or,[17,8]⟩,⟨.or,[18,15]⟩,⟨.and,[0,19]⟩,⟨.or,[9,10]⟩,⟨.or,[21,11]⟩,⟨.or,[22,15]⟩,⟨.and,[1,23]⟩,⟨.or,[12,13]⟩,⟨.or,[25,14]⟩,⟨.or,[26,15]⟩,⟨.and,[2,27]⟩,⟨.or,[6,9]⟩,⟨.or,[29,12]⟩,⟨.or,[30,16]⟩,⟨.and,[3,31]⟩,⟨.or,[7,10]⟩,⟨.or,[33,13]⟩,⟨.or,[34,16]⟩,⟨.and,[4,35]⟩,⟨.or,[8,11]⟩,⟨.or,[37,14]⟩,⟨.or,[38,16]⟩,⟨.and,[5,39]⟩,⟨.or,[20,24]⟩,⟨.or,[41,28]⟩,⟨.or,[42,32]⟩,⟨.or,[43,36]⟩,⟨.or,[44,40]⟩,⟨.or,[15,16]⟩],45⟩
theorem legal : Monotone2 c := by
  intro g hg
  simp only [c,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
theorem edges : ∀ p q : P, E p q=true → c.eval (List.ofFn fun i => decide (i=p ∨ i=q))=true := by decide +kernel
theorem step_and (j a b : Nat) (hj : j<c.gates.length) (hop : c.gates[j].op=.and)
    (hin : c.gates[j].inputs=[a,b]) (ha : a<17+j) (hb : b<17+j) (x : P → Bool) :
    val c.gates (17+j) x = (val c.gates a x && val c.gates b x) := by
  apply Bool.eq_iff_iff.mpr
  simpa [hin,ha,hb] using val_and c.gates x j hj hop
theorem step_or (j a b : Nat) (hj : j<c.gates.length) (hop : c.gates[j].op=.or)
    (hin : c.gates[j].inputs=[a,b]) (ha : a<17+j) (hb : b<17+j) (x : P → Bool) :
    val c.gates (17+j) x = (val c.gates a x || val c.gates b x) := by
  apply Bool.eq_iff_iff.mpr
  simpa [hin,ha,hb] using val_or c.gates x j hj hop
theorem scalar (x : P → Bool) : V c 45 x = ((((((x 0 && (((x 6 || x 7) || x 8) || x 15)) || (x 1 && (((x 9 || x 10) || x 11) || x 15))) || (x 2 && (((x 12 || x 13) || x 14) || x 15))) || (x 3 && (((x 6 || x 9) || x 12) || x 16))) || (x 4 && (((x 7 || x 10) || x 13) || x 16))) || (x 5 && (((x 8 || x 11) || x 14) || x 16))) := by
  have h0 : val c.gates 0 x = x 0 := val_input _ _ _ (by decide)
  have h1 : val c.gates 1 x = x 1 := val_input _ _ _ (by decide)
  have h2 : val c.gates 2 x = x 2 := val_input _ _ _ (by decide)
  have h3 : val c.gates 3 x = x 3 := val_input _ _ _ (by decide)
  have h4 : val c.gates 4 x = x 4 := val_input _ _ _ (by decide)
  have h5 : val c.gates 5 x = x 5 := val_input _ _ _ (by decide)
  have h6 : val c.gates 6 x = x 6 := val_input _ _ _ (by decide)
  have h7 : val c.gates 7 x = x 7 := val_input _ _ _ (by decide)
  have h8 : val c.gates 8 x = x 8 := val_input _ _ _ (by decide)
  have h9 : val c.gates 9 x = x 9 := val_input _ _ _ (by decide)
  have h10 : val c.gates 10 x = x 10 := val_input _ _ _ (by decide)
  have h11 : val c.gates 11 x = x 11 := val_input _ _ _ (by decide)
  have h12 : val c.gates 12 x = x 12 := val_input _ _ _ (by decide)
  have h13 : val c.gates 13 x = x 13 := val_input _ _ _ (by decide)
  have h14 : val c.gates 14 x = x 14 := val_input _ _ _ (by decide)
  have h15 : val c.gates 15 x = x 15 := val_input _ _ _ (by decide)
  have h16 : val c.gates 16 x = x 16 := val_input _ _ _ (by decide)
  have h17 : val c.gates 17 x = (x 6 || x 7) := by
    rw [step_or 0 6 7 (by decide) rfl rfl (by decide) (by decide) x,h6,h7]
  have h18 : val c.gates 18 x = ((x 6 || x 7) || x 8) := by
    rw [step_or 1 17 8 (by decide) rfl rfl (by decide) (by decide) x,h17,h8]
  have h19 : val c.gates 19 x = (((x 6 || x 7) || x 8) || x 15) := by
    rw [step_or 2 18 15 (by decide) rfl rfl (by decide) (by decide) x,h18,h15]
  have h20 : val c.gates 20 x = (x 0 && (((x 6 || x 7) || x 8) || x 15)) := by
    rw [step_and 3 0 19 (by decide) rfl rfl (by decide) (by decide) x,h0,h19]
  have h21 : val c.gates 21 x = (x 9 || x 10) := by
    rw [step_or 4 9 10 (by decide) rfl rfl (by decide) (by decide) x,h9,h10]
  have h22 : val c.gates 22 x = ((x 9 || x 10) || x 11) := by
    rw [step_or 5 21 11 (by decide) rfl rfl (by decide) (by decide) x,h21,h11]
  have h23 : val c.gates 23 x = (((x 9 || x 10) || x 11) || x 15) := by
    rw [step_or 6 22 15 (by decide) rfl rfl (by decide) (by decide) x,h22,h15]
  have h24 : val c.gates 24 x = (x 1 && (((x 9 || x 10) || x 11) || x 15)) := by
    rw [step_and 7 1 23 (by decide) rfl rfl (by decide) (by decide) x,h1,h23]
  have h25 : val c.gates 25 x = (x 12 || x 13) := by
    rw [step_or 8 12 13 (by decide) rfl rfl (by decide) (by decide) x,h12,h13]
  have h26 : val c.gates 26 x = ((x 12 || x 13) || x 14) := by
    rw [step_or 9 25 14 (by decide) rfl rfl (by decide) (by decide) x,h25,h14]
  have h27 : val c.gates 27 x = (((x 12 || x 13) || x 14) || x 15) := by
    rw [step_or 10 26 15 (by decide) rfl rfl (by decide) (by decide) x,h26,h15]
  have h28 : val c.gates 28 x = (x 2 && (((x 12 || x 13) || x 14) || x 15)) := by
    rw [step_and 11 2 27 (by decide) rfl rfl (by decide) (by decide) x,h2,h27]
  have h29 : val c.gates 29 x = (x 6 || x 9) := by
    rw [step_or 12 6 9 (by decide) rfl rfl (by decide) (by decide) x,h6,h9]
  have h30 : val c.gates 30 x = ((x 6 || x 9) || x 12) := by
    rw [step_or 13 29 12 (by decide) rfl rfl (by decide) (by decide) x,h29,h12]
  have h31 : val c.gates 31 x = (((x 6 || x 9) || x 12) || x 16) := by
    rw [step_or 14 30 16 (by decide) rfl rfl (by decide) (by decide) x,h30,h16]
  have h32 : val c.gates 32 x = (x 3 && (((x 6 || x 9) || x 12) || x 16)) := by
    rw [step_and 15 3 31 (by decide) rfl rfl (by decide) (by decide) x,h3,h31]
  have h33 : val c.gates 33 x = (x 7 || x 10) := by
    rw [step_or 16 7 10 (by decide) rfl rfl (by decide) (by decide) x,h7,h10]
  have h34 : val c.gates 34 x = ((x 7 || x 10) || x 13) := by
    rw [step_or 17 33 13 (by decide) rfl rfl (by decide) (by decide) x,h33,h13]
  have h35 : val c.gates 35 x = (((x 7 || x 10) || x 13) || x 16) := by
    rw [step_or 18 34 16 (by decide) rfl rfl (by decide) (by decide) x,h34,h16]
  have h36 : val c.gates 36 x = (x 4 && (((x 7 || x 10) || x 13) || x 16)) := by
    rw [step_and 19 4 35 (by decide) rfl rfl (by decide) (by decide) x,h4,h35]
  have h37 : val c.gates 37 x = (x 8 || x 11) := by
    rw [step_or 20 8 11 (by decide) rfl rfl (by decide) (by decide) x,h8,h11]
  have h38 : val c.gates 38 x = ((x 8 || x 11) || x 14) := by
    rw [step_or 21 37 14 (by decide) rfl rfl (by decide) (by decide) x,h37,h14]
  have h39 : val c.gates 39 x = (((x 8 || x 11) || x 14) || x 16) := by
    rw [step_or 22 38 16 (by decide) rfl rfl (by decide) (by decide) x,h38,h16]
  have h40 : val c.gates 40 x = (x 5 && (((x 8 || x 11) || x 14) || x 16)) := by
    rw [step_and 23 5 39 (by decide) rfl rfl (by decide) (by decide) x,h5,h39]
  have h41 : val c.gates 41 x = ((x 0 && (((x 6 || x 7) || x 8) || x 15)) || (x 1 && (((x 9 || x 10) || x 11) || x 15))) := by
    rw [step_or 24 20 24 (by decide) rfl rfl (by decide) (by decide) x,h20,h24]
  have h42 : val c.gates 42 x = (((x 0 && (((x 6 || x 7) || x 8) || x 15)) || (x 1 && (((x 9 || x 10) || x 11) || x 15))) || (x 2 && (((x 12 || x 13) || x 14) || x 15))) := by
    rw [step_or 25 41 28 (by decide) rfl rfl (by decide) (by decide) x,h41,h28]
  have h43 : val c.gates 43 x = ((((x 0 && (((x 6 || x 7) || x 8) || x 15)) || (x 1 && (((x 9 || x 10) || x 11) || x 15))) || (x 2 && (((x 12 || x 13) || x 14) || x 15))) || (x 3 && (((x 6 || x 9) || x 12) || x 16))) := by
    rw [step_or 26 42 32 (by decide) rfl rfl (by decide) (by decide) x,h42,h32]
  have h44 : val c.gates 44 x = (((((x 0 && (((x 6 || x 7) || x 8) || x 15)) || (x 1 && (((x 9 || x 10) || x 11) || x 15))) || (x 2 && (((x 12 || x 13) || x 14) || x 15))) || (x 3 && (((x 6 || x 9) || x 12) || x 16))) || (x 4 && (((x 7 || x 10) || x 13) || x 16))) := by
    rw [step_or 27 43 36 (by decide) rfl rfl (by decide) (by decide) x,h43,h36]
  have h45 : val c.gates 45 x = ((((((x 0 && (((x 6 || x 7) || x 8) || x 15)) || (x 1 && (((x 9 || x 10) || x 11) || x 15))) || (x 2 && (((x 12 || x 13) || x 14) || x 15))) || (x 3 && (((x 6 || x 9) || x 12) || x 16))) || (x 4 && (((x 7 || x 10) || x 13) || x 16))) || (x 5 && (((x 8 || x 11) || x 14) || x 16))) := by
    rw [step_or 28 44 40 (by decide) rfl rfl (by decide) (by decide) x,h44,h40]
  exact h45
theorem mark (x : P → Bool) : V c 46 x = (x 15 || x 16) := by
  have h15 : val c.gates 15 x = x 15 := val_input _ _ _ (by decide)
  have h16 : val c.gates 16 x = x 16 := val_input _ _ _ (by decide)
  have h46 : val c.gates 46 x = (x 15 || x 16) := by
    rw [step_or 29 15 16 (by decide) rfl rfl (by decide) (by decide) x,h15,h16]
  exact h46
theorem safe (x : P → Bool) (h : ∀ p q : P, E p q=true → x p=true → x q=false) : V c 45 x=false := by
  rw [scalar]
  have f0 : (x 0 && (((x 6 || x 7) || x 8) || x 15))=false := by
    cases b : x 0 with
    | false => simp
    | true => simp [h 0 6 (by decide) b,h 0 7 (by decide) b,h 0 8 (by decide) b,h 0 15 (by decide) b]
  have f1 : (x 1 && (((x 9 || x 10) || x 11) || x 15))=false := by
    cases b : x 1 with
    | false => simp
    | true => simp [h 1 9 (by decide) b,h 1 10 (by decide) b,h 1 11 (by decide) b,h 1 15 (by decide) b]
  have f2 : (x 2 && (((x 12 || x 13) || x 14) || x 15))=false := by
    cases b : x 2 with
    | false => simp
    | true => simp [h 2 12 (by decide) b,h 2 13 (by decide) b,h 2 14 (by decide) b,h 2 15 (by decide) b]
  have f3 : (x 3 && (((x 6 || x 9) || x 12) || x 16))=false := by
    cases b : x 3 with
    | false => simp
    | true => simp [h 3 6 (by decide) b,h 3 9 (by decide) b,h 3 12 (by decide) b,h 3 16 (by decide) b]
  have f4 : (x 4 && (((x 7 || x 10) || x 13) || x 16))=false := by
    cases b : x 4 with
    | false => simp
    | true => simp [h 4 7 (by decide) b,h 4 10 (by decide) b,h 4 13 (by decide) b,h 4 16 (by decide) b]
  have f5 : (x 5 && (((x 8 || x 11) || x 14) || x 16))=false := by
    cases b : x 5 with
    | false => simp
    | true => simp [h 5 8 (by decide) b,h 5 11 (by decide) b,h 5 14 (by decide) b,h 5 16 (by decide) b]
  simp only [f0,f1,f2,f3,f4,f5,Bool.false_or]
theorem boundary : (have x1 : Fin (17 : ℕ) → Fin (17 : ℕ) → Bool := fun (x1 x2 : Fin (17 : ℕ)) => ([(33216 : ℕ), (36352 : ℕ), (61440 : ℕ), (70208 : ℕ), (74880 : ℕ), (84224 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑x2; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (30 : ℕ) ∧       x2.output < (17 : ℕ) + x2.size ∧         x3 < (17 : ℕ) + x2.size ∧           (∀ (x4 x5 : Fin (17 : ℕ)), x1 x4 x5 = Bool.true → x2.eval (List.ofFn fun (x7 : Fin (17 : ℕ)) => Decidable.decide (x7 = x4 ∨ x7 = x5)) = Bool.true) ∧             (∀ x4 ∈ [(15 : Fin (17 : ℕ)), (16 : Fin (17 : ℕ))], (x2.wires (List.ofFn fun (x6 : Fin (17 : ℕ)) => Decidable.decide (x6 = x4))).getD x3 Bool.false = Bool.true) ∧               ∀ (x4 : Bool) (x5 : Finset (Fin (17 : ℕ))),                 (∀ x6 ∈ x5, ↑x6 < (6 : ℕ)) →                   have x7 : Fin (17 : ℕ) → Prop := fun (x7 : Fin (17 : ℕ)) => (x4 = Bool.false ∨ ↑x7 < (15 : ℕ)) ∧ ∀ x8 ∈ x5, x1 x8 x7 = Bool.false;                   ∀ (x8 : Fin (17 : ℕ) → Bool), (∀ (x9 : Fin (17 : ℕ)), x8 x9 = Bool.true ↔ if ↑x9 < (6 : ℕ) then ∀ (x10 : Fin (17 : ℕ)), x1 x9 x10 = Bool.true → ¬x7 x10 else x7 x9) → (x2.wires (List.ofFn x8)).getD (if x4 = Bool.true then x3 else x2.output) Bool.false = Bool.false) := by
  refine ⟨c,46,legal,by decide,by decide,by decide,edges,?_,?_⟩
  · intro p hp
    have hh : p=(15 : P) ∨ p=(16 : P) := by simpa using hp
    rcases hh with rfl|rfl <;> decide +kernel
  · intro b S _
    dsimp only
    intro x hx
    let L (i : P) := (b=false ∨ i.val<15) ∧ ∀ p∈S, E p i=false
    have h (i : P) : x i=true ↔ if i.val<6 then ∀ j, E i j=true → ¬ L j else L i := hx i
    cases hb : b with
    | false =>
      change V c 45 x=false
      apply safe
      intro p q he hp
      have side : ∀ u v : P, E u v=true → u.val<6 ∧ 6≤v.val := by decide +kernel
      obtain ⟨a,d⟩ := side _ _ he
      have live := (h p).mp hp
      rw [if_pos a] at live
      apply Bool.eq_false_iff.mpr
      intro hq
      have off := (h q).mp hq
      rw [if_neg (Nat.not_lt.mpr d)] at off
      exact live q he off
    | true =>
      change V c 46 x=false
      rw [mark]
      have ff (i : P) (hi : (15 : Nat) ≤ i.val) : x i=false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        have m := (h i).mp yes
        rw [if_neg (by omega)] at m
        rcases m.1 with no|bad
        · simp [hb] at no
        · omega
      rw [ff 15 (by decide),ff 16 (by decide)]
      rfl

end PEqualNP.Outside.L_meta_18910.Boundary
