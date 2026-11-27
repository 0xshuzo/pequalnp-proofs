import PEqualNP.Defs

namespace ShoreTransport18757

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

abbrev V := Fin 42
abbrev inc (a b : V) : Prop :=
  a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
def adj (a b : V) : Bool := decide (inc a b ∨ inc b a)
def fixedRow (i : V) : Bool := decide (i.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List ℕ))

-- Simultaneous cyclic shift and point-line duality suffice to move any
-- independent pair into the given ten-vertex independent input.

def gen (g : Fin 2) (i : V) : V :=
  if g = 0 then Fin.ofNat 42 ((i.val / 21) * 21 + (i.val + 1) % 21)
  else Fin.ofNat 42 ((if i.val < 21 then 21 else 0) + (21 - i.val % 21) % 21)

-- Send the first member of an ordered pair to point zero.
def normal (i : V) : List (Fin 2) :=
  if i.val < 21 then List.replicate ((21 - i.val) % 21) 0
  else 1 :: List.replicate (i.val - 21) 0

-- With the first member fixed at point zero, this much simultaneous
-- rotation carries both members into the chosen independent row.
def amount : V → ℕ := ![0,0,0,18,2,1,0,1,0,18,8,18,6,8,8,6,2,1,0,2,1,0,2,1,0,6,0,6,0,2,1,0,1,0,18,2,1,0,0,6,18,0]
def peer (b : V) : List (Fin 2) := List.replicate (amount b) 0

def chain : List (Fin 2) → V → V
  | [], a => a
  | g::gs, a => chain gs (gen g a)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem genSurj : ∀ g : Fin 2, ∀ t : V, ∃ j : V, gen g j=t := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem genAdj : ∀ (g : Fin 2) (a b : V), adj (gen g a) (gen g b)=adj a b := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem normalOK : ∀ a : V, chain (normal a) a=0 := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem peerOK : ∀ b : V, adj 0 b=false →
    fixedRow (chain (peer b) 0)=true ∧ fixedRow (chain (peer b) b)=true := by decide +kernel

theorem chainSurj (gs : List (Fin 2)) : Function.Surjective (chain gs) := by
  induction gs with
  | nil => exact fun a => ⟨a,rfl⟩
  | cons g gs ih => exact ih.comp (genSurj g)

theorem chainAdj (gs : List (Fin 2)) (a b : V) : adj (chain gs a) (chain gs b)=adj a b := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih => exact (ih (gen g a) (gen g b)).trans (genAdj g a b)

theorem transportPair (a b : V) (missing : adj a b=false) :
    ∃ e : V → V, Function.Surjective e ∧ (∀ u v, adj (e u) (e v)=adj u v) ∧
      fixedRow (e a)=true ∧ fixedRow (e b)=true := by
  let g := chain (normal a)
  let h := chain (peer (g b))
  have gz : g a=0 := normalOK a
  have hn : adj 0 (g b)=false := by rw [← gz]; exact (chainAdj _ _ _).trans missing
  obtain ⟨hp,hq⟩ := peerOK (g b) hn
  exact ⟨h ∘ g,(chainSurj _).comp (chainSurj _),fun u v => (chainAdj _ _ _).trans (chainAdj _ _ _),
    by change fixedRow (h (g a))=true; rw [gz]; exact hp,hq⟩


def yes (x : V → Bool) : Prop := ∃ a b : V, inc a b ∧ x a=true ∧ x b=true
theorem yes_iff (x : V → Bool) : yes x ↔ ∃ a b : V, adj a b=true ∧ x a=true ∧ x b=true := by
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨a,b,decide_eq_true (Or.inl h : inc a b ∨ inc b a),ha,hb⟩
  · rintro ⟨a,b,h,ha,hb⟩
    obtain h|h : inc a b ∨ inc b a := of_decide_eq_true h
    · exact ⟨a,b,h,ha,hb⟩
    · exact ⟨b,a,h,hb,ha⟩
theorem yes_move (e : V → V) (onto : Function.Surjective e) (pres : ∀ u v, adj (e u) (e v)=adj u v)
    (x : V → Bool) : yes (x ∘ e) ↔ yes x := by
  rw [yes_iff,yes_iff]
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨e a,e b,(pres a b).trans h,ha,hb⟩
  · rintro ⟨p,l,h,hp,hl⟩
    obtain ⟨a,rfl⟩ := onto p
    obtain ⟨b,rfl⟩ := onto l
    exact ⟨a,b,(pres a b).symm.trans h,hp,hl⟩

def idx (e : V → V) (i : ℕ) : ℕ := if hi : i<42 then (e ⟨i,hi⟩).val else i
def changeGate (e : V → V) (g : Gate) : Gate := ⟨g.op,g.inputs.map (idx e)⟩
def changeC (e : V → V) (C : Circuit) : Circuit := ⟨C.gates.map (changeGate e),idx e C.output⟩
def trace (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

theorem read_change (e : V → V) (x : V → Bool) (extra : List Bool) (i : ℕ) :
    (List.ofFn x ++ extra).getD (idx e i) false = (List.ofFn (x ∘ e) ++ extra).getD i false := by
  by_cases hi : i<42
  · rw [List.getD_append _ _ _ _ (by simp [idx,hi]),
        List.getD_append _ _ _ _ (by simpa using hi)]
    rw [List.getD_eq_getElem _ _ (by simp [idx,hi]),
        List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn,idx,dite_eq_left hi,Function.comp_apply]
  · simp only [idx,dite_eq_right hi]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

theorem trace_change (e : V → V) (x : V → Bool) (gs : List Gate) :
    ∀ extra : List Bool, ∃ rest : List Bool,
      trace (gs.map (changeGate e)) (List.ofFn x ++ extra)=List.ofFn x ++ rest ∧
      trace gs (List.ofFn (x ∘ e) ++ extra)=List.ofFn (x ∘ e) ++ rest := by
  induction gs with
  | nil => exact fun extra => ⟨extra,rfl,rfl⟩
  | cons g gs ih =>
    intro extra
    let old := List.ofFn (x ∘ e) ++ extra
    let y := g.op.eval (g.inputs.map fun i => old.getD i false)
    have he : (changeGate e g).op.eval ((changeGate e g).inputs.map fun i =>
        (List.ofFn x ++ extra).getD i false)=y := by
      simp only [changeGate,List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _; exact read_change e x extra i
    obtain ⟨rest,hnew,hold⟩ := ih (extra ++ [y])
    refine ⟨rest,?_,?_⟩
    · change trace (gs.map (changeGate e)) ((List.ofFn x ++ extra) ++ [_]) = _
      rw [he,List.append_assoc]; exact hnew
    · change trace gs ((List.ofFn (x ∘ e) ++ extra) ++ [y]) = _
      rw [List.append_assoc]; exact hold

theorem lookup_change (e : V → V) (C : Circuit) (x : V → Bool) (i : ℕ) :
    ((changeC e C).wires (List.ofFn x)).getD (idx e i) false =
    (C.wires (List.ofFn (x ∘ e))).getD i false := by
  obtain ⟨rest,hnew,hold⟩ := trace_change e x C.gates []
  simp only [List.append_nil] at hnew hold
  change (trace (C.gates.map (changeGate e)) (List.ofFn x)).getD _ false =
    (trace C.gates (List.ofFn (x ∘ e))).getD _ false
  rw [hnew,hold]
  exact read_change e x rest i

-- The monotone fold argument is adapted from L-meta-1082.
def m1892_stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem m1892_eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl m1892_stp x).getD C.output false := rfl

theorem m1892_getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem m1892_ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl m1892_stp W1).getD i false = true → (gs.foldl m1892_stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (m1892_stp W1 g) (m1892_stp W2 g) (by simp [m1892_stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [m1892_stp, m1892_getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [m1892_ev_and g _ ha, m1892_ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [m1892_ev_or g _ ho, m1892_ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem m1892_all_idx (n : ℕ) (x y : List Bool) (hx : x.length = n)
    (H : ∀ i < n, x.getD i false = true → y.getD i false = true) :
    ∀ i, x.getD i false = true → y.getD i false = true := by
  intro i hi
  by_cases h : i < n
  · exact H i h hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    exact Bool.noConfusion hi

theorem evalMono1892 {N : ℕ} (gs : List Gate) (u : ℕ)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (hle : ∀ p, x p = true → y p = true) :
    (Circuit.mk gs u).eval (List.ofFn x) = true →
      (Circuit.mk gs u).eval (List.ofFn y) = true := by
  rw [m1892_eval_eq, m1892_eval_eq]
  apply m1892_mono gs _ _ (by simp) hop _ u
  apply m1892_all_idx N _ _ (by simp)
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
  simpa only [List.getElem_ofFn] using hle ⟨i, hi⟩



def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_ext (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    change run gs (w ++ [v]) = w ++ v :: t
    simp [ht]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_ext gs w
  rw [ht, List.length_append, hl]

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma prefix_read (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (run (gs.take k) w).getD i false =
      if i < w.length + k then (run gs w).getD i false else false := by
  have hlen : (run (gs.take k) w).length = w.length + k := by
    rw [run_length, List.length_take, min_eq_left hk]
  split_ifs with hi
  · conv_rhs => rw [← List.take_append_drop k gs, run_append]
    exact (run_input _ _ _ (by omega)).symm
  · exact List.getD_eq_default _ _ (by omega)

lemma run_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (run gs w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i =>
        if i < w.length + k then (run gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h
    exact h
  have hlen : (run (gs.take k) w).length = w.length + k := by
    rw [run_length, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : run gs w =
      run (gs.drop (k + 1)) (run (gs.take k) w ++
        [gs[k].op.eval (gs[k].inputs.map fun i => (run (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, run_append]
    rfl
  calc
    (run gs w).getD (w.length + k) false =
        gs[k].op.eval (gs[k].inputs.map fun i => (run (gs.take k) w).getD i false) := by
      rw [heq, run_input]
      · simp [← hlen]
      · simp [hlen]
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact prefix_read gs w k i (Nat.le_of_lt hk)

abbrev Input := Fin 42 → Bool

def wire (C : Circuit) (y : Input) (i : ℕ) : Bool :=
  (C.wires (List.ofFn y)).getD i false

def read (C : Circuit) (y : Input) (k i : ℕ) : Bool :=
  if i < 42 + k then wire C y i else false

lemma wire_input (C : Circuit) (y : Input) (i : Fin 42) : wire C y i.val = y i := by
  change (run C.gates (List.ofFn y)).getD i.val false = y i
  rw [run_input, List.getD_eq_getElem, List.getElem_ofFn]
  all_goals simp

lemma wire_outside (C : Circuit) (y : Input) {i : ℕ} (hi : 42 + C.gates.length ≤ i) :
    wire C y i = false := by
  change (run C.gates (List.ofFn y)).getD i false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hi)

lemma gate_sem (C : Circuit) (y : Input) {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) :
    wire C y (42 + k) = g.op.eval (g.inputs.map (read C y k)) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  change (run C.gates (List.ofFn y)).getD (42 + k) false = _
  have h := run_gate C.gates (List.ofFn y) k hk
  rw [List.length_ofFn] at h
  exact h

lemma and_sem (C : Circuit) (y : Input) {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) (ho : g.op = .and) :
    wire C y (42 + k) = true ↔ ∀ i ∈ g.inputs, read C y k i = true := by
  simp [gate_sem C y hg, ho, GateOp.eval, List.all_eq_true]

lemma or_sem (C : Circuit) (y : Input) {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) (ho : g.op = .or) :
    wire C y (42 + k) = true ↔ ∃ i ∈ g.inputs, read C y k i = true := by
  simp [gate_sem C y hg, ho, GateOp.eval, List.any_eq_true]

lemma gate_mono {C : Circuit} (hc : Monotone2 C) {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    hc _ (List.getElem_mem hk)

lemma inputs_cases (l : List ℕ) (hl : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a l =>
    cases l with
    | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
    | cons b l =>
      cases l with
      | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
      | cons c l => simp at hl


def hit (C : Circuit) (y : Input) : Prop :=
  ∃ k g, C.gates[k]? = some g ∧ g.op = .and ∧ wire C y (42 + k) = true

def tab (i : Fin 2) : List V := if i=0 then [0, 5, 1, 3, 19, 2, 8, 4, 14, 11, 18, 16, 10, 13, 6, 15, 9, 17, 12, 7, 20, 26, 22, 29, 24, 40, 28, 25, 21, 31, 39, 23, 36, 30, 34, 32, 35, 37, 38, 33, 27, 41] else [0, 5, 10, 1, 9, 11, 7, 12, 17, 2, 13, 18, 15, 4, 19, 14, 6, 3, 20, 8, 16, 26, 31, 27, 29, 37, 28, 33, 38, 22, 30, 39, 35, 32, 24, 40, 34, 23, 41, 25, 36, 21]
def tabgen (i : Fin 2) (v : V) : V := (tab i).getD v.val 0
def walk : List (Fin 2) → V → V
  | [], a => a
  | g::gs, a => walk gs (tabgen g a)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem tabSurj : ∀ g : Fin 2, ∀ t : V, ∃ j : V, tabgen g j=t := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem tabAdj : ∀ (g : Fin 2) (a b : V), adj (tabgen g a) (tabgen g b)=adj a b := by decide +kernel
theorem walkSurj (gs : List (Fin 2)) : Function.Surjective (walk gs) := by
  induction gs with
  | nil => exact fun a => ⟨a,rfl⟩
  | cons g gs ih => exact ih.comp (tabSurj g)

theorem walkAdj (gs : List (Fin 2)) (a b : V) : adj (walk gs a) (walk gs b)=adj a b := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih => exact (ih (tabgen g a) (tabgen g b)).trans (tabAdj g a b)

def words : List (List (Fin 2)) := [[], [], [0], [1], [1, 1, 0], [0, 0], [0, 1, 1, 1], [0, 1, 1, 0], [1, 1, 1], [1, 0], [1, 1, 1, 1, 0], [0, 0, 1, 0], [0, 1, 1, 1, 1, 0], [1, 1, 1, 0], [0, 0, 1, 1, 1], [1, 0, 0, 1, 1, 1], [0, 1, 0], [1, 1], [1, 1, 0, 1, 0], [1, 1, 1, 1], [1, 0, 1, 0]]
def baseRow (i : V) := decide (i=0 ∨ i=1)
abbrev Same (a b : V) := (a.val<21 ↔ b.val<21)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem normalPeer : ∀ a b : V, Same a b → (chain (normal a) b).val<21 := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem tabPeer : ∀ b : V, b.val<21 →
    baseRow (walk (words.getD b.val []) 0)=true ∧ baseRow (walk (words.getD b.val []) b)=true := by decide +kernel

theorem moveShore (a b : V) (h : Same a b) : ∃ e : V→V, Function.Surjective e ∧
    (∀ u v, adj (e u) (e v)=adj u v) ∧ baseRow (e a)=true ∧ baseRow (e b)=true := by
  let f := chain (normal a)
  let w := words.getD (f b).val []
  let g := walk w
  have fa : f a=0 := normalOK a
  obtain ⟨pa,pb⟩ := tabPeer (f b) (normalPeer a b h)
  refine ⟨g ∘ f,(walkSurj _).comp (chainSurj _),fun u v =>
    (walkAdj _ _ _).trans (chainAdj _ _ _),?_,pb⟩
  change baseRow (g (f a))=true
  rw [fa]
  exact pa

theorem transportShore (C : Circuit) (a b : V) (k : ℕ) (g : Gate)
    (model : Monotone2 C) (correct : ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ yes x)
    (miss : Same a b)
    (hk : C.gates[k]?=some g) (hop : g.op=GateOp.and)
    (hot : (C.wires (List.ofFn (pairInput a b))).getD (42+k) false=true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size=C.size ∧
      (∀ x : V → Bool, D.eval (List.ofFn x)=true ↔ yes x) ∧
      ∃ h : Gate, D.gates[k]?=some h ∧ h.op=GateOp.and ∧
        (D.wires (List.ofFn baseRow)).getD (42+k) false=true := by
  obtain ⟨e,onto,pres,ha,hb⟩ := moveShore a b miss
  let D := changeC e C
  refine ⟨D,?_,by simp [D,changeC,Circuit.size],?_,changeGate e g,?_,hop,?_⟩
  · intro q hq
    obtain ⟨t,ht,rfl⟩ := List.mem_map.1 hq
    exact ⟨(model t ht).1,by simpa [changeGate] using (model t ht).2⟩
  · intro x
    have eq : D.eval (List.ofFn x)=C.eval (List.ofFn (x ∘ e)) := lookup_change e C x C.output
    rw [eq,correct,yes_move e onto pres]
  · simp [D,changeC,List.getElem?_map,hk]
  · have ops (q : Gate) (hq : q ∈ C.gates) : q.op=GateOp.and ∨ q.op=GateOp.or :=
      (model q hq).1
    have grows : (⟨C.gates,42+k⟩ : Circuit).eval (List.ofFn (baseRow ∘ e))=true :=
      evalMono1892 C.gates (42+k) ops (pairInput a b) (baseRow ∘ e)
        (fun i hi => by
          obtain hi|hi : i=a ∨ i=b := by simpa [pairInput] using hi
          · simpa [hi,Function.comp] using ha
          · simpa [hi,Function.comp] using hb) hot
    have eq := lookup_change e C baseRow (42+k)
    simp only [idx,dite_eq_right (show ¬42+k<42 by omega)] at eq
    exact eq.trans grows

def shore (q : Bool) (i : V) : Bool :=
  if q then decide (i.val ≥ (21 : ℕ)) else decide (i.val < (21 : ℕ))
theorem peer_shore : ∀ (q : Bool) (i j : V), shore q i=true → shore q j=true → Same i j := by decide +kernel
theorem anchor_shore (q : Bool) : ∃ u : V, shore q u=true := by
  cases q
  · exact ⟨0,by decide⟩
  · exact ⟨21,by decide⟩
lemma before_first_and (face : Input) {C : Circuit} (hc : Monotone2 C) {k : ℕ} (hk : k < C.gates.length)
    (hfirst : ∀ j < k, ∀ g, C.gates[j]? = some g → g.op = .and →
      wire C face (42 + j) ≠ true) :
    ∀ w < 42 + k, wire C face w = true →
      ∃ i, face i=true ∧ ∀ y : Input, y i = true → wire C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hin : w < 42
    · let i : Fin 42 := ⟨w, hin⟩
      have hi := (wire_input C face i).symm.trans htrue
      exact ⟨i, hi, fun y hy => (wire_input C y i).trans hy⟩
    · let j := w - 42
      have he : w = 42 + j := by dsimp [j]; omega
      have hj : j < k := by omega
      have hj' : j < C.gates.length := by omega
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj'
      have ht : wire C face (42 + j) = true := he ▸ htrue
      have ho : g.op = .or := (gate_mono hc hg).1.resolve_left
        (fun ha => hfirst j hj g hg ha ht)
      obtain ⟨a, ha, hra⟩ := (or_sem C face hg ho).mp ht
      by_cases hlt : a < 42 + j
      · have hwa : wire C face a = true := by simpa [read, hlt] using hra
        obtain ⟨i, hi, hiw⟩ := ih a (by omega) (by omega) hwa
        refine ⟨i, hi, fun y hy => ?_⟩
        rw [he, or_sem C y hg ho]
        exact ⟨a, ha, by simpa [read, hlt] using hiw y hy⟩
      · simp [read, hlt] at hra

lemma first_and_transfer (q : Bool) {C : Circuit} (hc : Monotone2 C) (hh : hit C (shore q)) :
    ∃ i j : V, Same i j ∧ hit C (pairInput i j) := by
  classical
  let P := fun k => ∃ g, C.gates[k]? = some g ∧ g.op = .and ∧ wire C (shore q) (42 + k) = true
  have hex : ∃ k, P k := hh
  let k := Nat.find hex
  obtain ⟨g, hg, ho, ht⟩ := Nat.find_spec hex
  have hg' : C.gates[k]? = some g := hg
  have hk : k < C.gates.length := (List.getElem?_eq_some_iff.mp hg').choose
  have hfirst : ∀ j < k, ∀ g, C.gates[j]? = some g → g.op = .and →
      wire C (shore q) (42 + j) ≠ true := by
    intro j hj gate hgate hop hwire
    exact Nat.find_min hex hj ⟨gate, hgate, hop, hwire⟩
  have hread : ∀ a ∈ g.inputs, ∃ i, shore q i=true ∧ ∀ y : Input, y i = true → read C y k a = true := by
    intro a ha
    have hr := (and_sem C (shore q) hg' ho).mp ht a ha
    by_cases hlt : a < 42 + k
    · simpa [read, hlt] using before_first_and (shore q) hc hk hfirst a hlt (by simpa [read, hlt] using hr)
    · simp [read, hlt] at hr
  have hpair : ∃ i, shore q i=true ∧ ∃ j, shore q j=true ∧ ∀ y : Input, y i = true → y j = true →
      ∀ a ∈ g.inputs, read C y k a = true := by
    obtain ⟨anchor,hzero⟩ := anchor_shore q
    rcases inputs_cases _ (gate_mono hc hg').2 with he | ⟨a, he⟩ | ⟨a, b, he⟩
    · exact ⟨anchor, hzero, anchor, hzero, by simp [he]⟩
    · obtain ⟨i, hi, hp⟩ := hread a (by simp [he])
      refine ⟨i, hi, i, hi, fun y hy _ c hmem => ?_⟩
      have heq : c = a := by simpa [he] using hmem
      exact heq.symm ▸ hp y hy
    · obtain ⟨i, hi, hp⟩ := hread a (by simp [he])
      obtain ⟨j, hj, hq⟩ := hread b (by simp [he])
      refine ⟨i, hi, j, hj, fun y hy hz c hmem => ?_⟩
      simp only [he, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hp y hy
      · exact hq y hz
  obtain ⟨i, hi, j, hj, hp⟩ := hpair
  exact ⟨i,j,peer_shore q i j hi hj,k,g,hg',ho,(and_sem C _ hg' ho).mpr
    (hp (pairInput i j) (by simp [pairInput]) (by simp [pairInput]))⟩

theorem output_high {C : Circuit} (ok : ∀ x : Input, C.eval (List.ofFn x)=true ↔ yes x) : 42≤C.output := by
  by_contra! lo
  let v : V := ⟨C.output,lo⟩
  let x (t : V) := decide (t=v)
  have high : C.eval (List.ofFn x)=true := (wire_input C x v).trans (by simp [x])
  obtain ⟨a,b,⟨hp,hl,_⟩,xa,xb⟩ := (ok x).1 high
  have ea : a=v := of_decide_eq_true xa
  have eb : b=v := of_decide_eq_true xb
  rw [ea] at hp
  rw [eb] at hl
  omega

abbrev ShoreLaw := ∀ C : Circuit, Monotone2 C → C.size≤124 →
    (∀ x : Input, C.eval (List.ofFn x)=true ↔ yes x) → ∀ q : Bool, ¬hit C (shore q)

theorem faces_iff : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (42 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (1 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) ↔ ShoreLaw := by
  constructor
  · intro posted C mono budget ok q bad
    obtain ⟨i,j,same,k,g,hg,ho,on_⟩ := first_and_transfer q mono bad
    obtain ⟨D,dm,ds,dok,t,dt,top,hot⟩ := transportShore C i j k g mono ok same hg ho on_
    exact posted D (output_high dok) dm (ds.trans_le budget) dok ⟨k,t,dt,top,hot⟩
  · intro law C _ mono budget ok bad
    obtain ⟨k,g,hg,ho,hot⟩ := bad
    apply law C mono budget ok false
    refine ⟨k,g,hg,ho,?_⟩
    apply evalMono1892 C.gates (42+k) (fun t ht => (mono t ht).1) baseRow (shore false) _ hot
    intro v hv
    have choices : v=0 ∨ v=1 := of_decide_eq_true hv
    rcases choices with rfl | rfl <;> decide

end ShoreTransport18757
