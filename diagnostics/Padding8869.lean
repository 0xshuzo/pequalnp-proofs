import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8869.Donor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

end PEqualNP.Outside.L_meta_8869.Donor
namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

def push (n : Nat) (C : Circuit) (g : Gate) : Circuit := ⟨C.gates++[g],n+C.size⟩

theorem push_size (n : Nat) (C : Circuit) (g : Gate) : (push n C g).size=C.size+1 := by
  simp [push,Circuit.size]
theorem push_gate_old (n : Nat) (C : Circuit) (g : Gate) (i : Nat) (hi : i<C.size) :
    gateAt (push n C g) i=gateAt C i := by
  change i<C.gates.length at hi
  simp [push,gateAt,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem push_gate_new (n : Nat) (C : Circuit) (g : Gate) : gateAt (push n C g) C.size=g := by
  simp [push,gateAt,Circuit.size,List.getD_eq_getElem?_getD]

theorem push_model {n : Nat} {C : Circuit} {g : Gate} (h : IsAO2 n C)
    (op : g.op=GateOp.and ∨ g.op=GateOp.or) (len : g.inputs.length=2)
    (earlier : ∀ w∈g.inputs,w<n+C.size) : IsAO2 n (push n C g) := by
  refine ⟨?_,?_,?_⟩
  · intro p hp
    change p∈C.gates++[g] at hp
    rcases List.mem_append.mp hp with old|new
    · exact h.1 p old
    · obtain rfl : p=g := List.mem_singleton.mp new
      exact op
  · intro j hj w hw
    change j<(push n C g).size at hj
    rw [push_size] at hj
    by_cases old : j<C.size
    · rw [push_gate_old _ _ _ _ old] at hw
      exact h.2.1 _ old _ hw
    · obtain rfl : j=C.size := by omega
      rw [push_gate_new] at hw
      exact earlier _ hw
  · intro p hp
    change p∈C.gates++[g] at hp
    rcases List.mem_append.mp hp with old|new
    · exact h.2.2 p old
    · obtain rfl : p=g := List.mem_singleton.mp new
      exact len

theorem push_keep {n : Nat} (C : Circuit) (g : Gate) (x : Fin n → Bool) (w : Nat)
    (hw : w<n+C.size) : wireVal n (push n C g) w x = wireVal n C w x := by
  change Donor.val (push n C g) (List.ofFn x) w = Donor.val C (List.ofFn x) w
  unfold Donor.val
  rw [Donor.wires_eq_foldl,Donor.wires_eq_foldl]
  change ((C.gates++[g]).foldl Donor.stepWire (List.ofFn x)).getD w false=_
  rw [List.foldl_append]
  apply Donor.foldl_getD_lt
  rw [Donor.foldl_length]
  simpa only [List.length_ofFn] using hw

theorem push_value {n : Nat} (C : Circuit) (g : Gate) (x : Fin n → Bool)
    (earlier : ∀ w∈g.inputs,w<n+C.size) :
    wireVal n (push n C g) (n+C.size) x = g.op.eval (g.inputs.map (fun w => wireVal n C w x)) := by
  change Donor.val (push n C g) (List.ofFn x) (n+C.size)=_
  rw [Donor.val_gate (n:=n) (by simp) (by change C.size<(push n C g).size; rw [push_size]; omega),
    push_gate_new]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [if_pos (earlier w hw)]
  exact push_keep _ _ _ _ (earlier w hw)

def dup (w : Nat) : Gate := ⟨GateOp.and,[w,w]⟩
def join (u v : Nat) : Gate := ⟨GateOp.or,[u,v]⟩
def first (n : Nat) (C : Circuit) := push n C (dup C.output)
def second (n : Nat) (C : Circuit) := push n (first n C) (dup C.output)
def pad (n : Nat) (C : Circuit) := push n (second n C) (join (n+C.size) (n+(C.size+1)))

@[simp] theorem size_first (n : Nat) (C : Circuit) : (first n C).size=C.size+1 := push_size .. 
@[simp] theorem size_second (n : Nat) (C : Circuit) : (second n C).size=C.size+2 := by simp [second,push_size]
@[simp] theorem size_pad (n : Nat) (C : Circuit) : (pad n C).size=C.size+3 := by simp [pad,push_size]

theorem pad_model {n : Nat} {C : Circuit} (model : IsAO2 n C) (out : C.output<n+C.size) :
    IsAO2 n (pad n C) := by
  have a : IsAO2 n (first n C) := push_model model (Or.inl rfl) rfl (by simp [dup,out])
  have b : IsAO2 n (second n C) := push_model a (Or.inl rfl) rfl (by simp [dup]; omega)
  exact push_model b (Or.inr rfl) rfl (by simp [join]; omega)

end PEqualNP.Outside.L_meta_8869
