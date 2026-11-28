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
  simpa only [List.length_ofFn,Circuit.size] using hw

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
  exact push_model b (Or.inr rfl) rfl (by simp [join] <;> omega)

end PEqualNP.Outside.L_meta_8869
namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

theorem iter_gate (n : Nat) (C : Circuit) :
    gateAt (pad n C) C.size=dup C.output ∧ gateAt (pad n C) (C.size+1)=dup C.output ∧
    gateAt (pad n C) (C.size+2)=join (n+C.size) (n+(C.size+1)) := by
  constructor
  · unfold pad
    rw [push_gate_old _ _ _ _ (by simp)]
    unfold second
    rw [push_gate_old _ _ _ _ (by simp)]
    exact push_gate_new ..
  constructor
  · unfold pad
    rw [push_gate_old _ _ _ _ (by simp)]
    rw [←size_first n C]
    exact push_gate_new ..
  · rw [←size_second n C]
    exact push_gate_new ..

theorem iter_values {n : Nat} (C : Circuit) (out : C.output<n+C.size) (x : Fin n → Bool) :
    wireVal n (pad n C) C.output x=wireVal n C C.output x ∧
    wireVal n (pad n C) (n+C.size) x=wireVal n C C.output x ∧
    wireVal n (pad n C) (n+(C.size+1)) x=wireVal n C C.output x ∧
    wireVal n (pad n C) (pad n C).output x=wireVal n C C.output x := by
  let A := first n C
  let B := second n C
  have asize : A.size=C.size+1 := size_first ..
  have bsize : B.size=C.size+2 := size_second ..
  have aold : wireVal n A C.output x=wireVal n C C.output x := push_keep C _ x _ out
  have bold : wireVal n B C.output x=wireVal n A C.output x := push_keep A _ x _ (by omega)
  have pold : wireVal n (pad n C) C.output x=wireVal n B C.output x := push_keep B _ x _ (by omega)
  have firstVal : wireVal n A (n+C.size) x=wireVal n C C.output x := by
    rw [show A=push n C (dup C.output) from rfl,push_value _ _ _ (by simp [dup,out])]
    cases h : wireVal n C C.output x <;> simp [dup, GateOp.eval,h]
  have secondVal : wireVal n B (n+(C.size+1)) x=wireVal n A C.output x := by
    rw [←asize,show B=push n A (dup C.output) from rfl,push_value _ _ _ (by simp [dup]; omega)]
    cases h : wireVal n A C.output x <;> simp [dup,GateOp.eval,h]
  have bfirst : wireVal n B (n+C.size) x=wireVal n A (n+C.size) x := push_keep A _ x _ (by omega)
  have pfirst : wireVal n (pad n C) (n+C.size) x=wireVal n B (n+C.size) x := push_keep B _ x _ (by omega)
  have psecond : wireVal n (pad n C) (n+(C.size+1)) x=wireVal n B (n+(C.size+1)) x :=
    push_keep B _ x _ (by omega)
  refine ⟨pold.trans (bold.trans aold),pfirst.trans (bfirst.trans firstVal),psecond.trans (secondVal.trans aold),?_⟩
  change wireVal n (push n B (join (n+C.size) (n+(C.size+1)))) (n+B.size) x=_
  rw [push_value _ _ _ (by simp [join] <;> omega)]
  simp only [join,List.map_cons,List.map_nil,bfirst,firstVal,secondVal,aold]
  cases h : wireVal n C C.output x <;> rfl

theorem strict_cone (n : Nat) (C : Circuit) (i : Nat) : ∀ j, InCone n C i j → i<j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    obtain ⟨_,k,lt,_,rfl|pre⟩ := (Donor.inCone_iff n C i j).mp h
    · exact lt
    · exact lt_trans (ih k lt pre) lt

theorem separate {n : Nat} (C : Circuit) (out : C.output<n+C.size) :
    ¬InCone n (pad n C) C.size (C.size+1) ∧ ¬InCone n (pad n C) (C.size+1) C.size := by
  constructor
  · intro h
    obtain ⟨_,k,lt,inp,eq|pre⟩ := (Donor.inCone_iff ..).mp h
    · rw [(iter_gate n C).2.1] at inp
      simp [dup] at inp
      omega
    · have l := strict_cone _ _ _ _ pre
      omega
  · intro h
    have l := strict_cone _ _ _ _ h
    omega

abbrev step {n : Nat} (C : Circuit) (x : Fin n → Bool) (w w' : Nat) : Prop :=
  ∃ k<C.size,w'=n+k ∧ w∈(gateAt C k).inputs ∧ wireVal n C w x=true ∧ wireVal n C w' x=true

abbrev mark {n : Nat} (C : Circuit) (x : Fin n → Bool) (v : Fin n) (j : Nat) : Prop :=
  j<C.size ∧ (gateAt C j).op=GateOp.and ∧ Relation.ReflTransGen (step C x) (n+j) C.output ∧
  ∀ b : Fin 2,wireVal n C (opnd C j b) (fun r => decide (r=v))=false

theorem mark_both {n : Nat} (C : Circuit) (out : C.output<n+C.size) (x : Fin n → Bool)
    (on : wireVal n C C.output x=true) (v w : Fin n)
    (voff : wireVal n C C.output (fun r => decide (r=v))=false)
    (woff : wireVal n C C.output (fun r => decide (r=w))=false) :
    mark (pad n C) x v C.size ∧ mark (pad n C) x w (C.size+1) := by
  obtain ⟨g0,g1,g2⟩ := iter_gate n C
  obtain ⟨_,p0,p1,po⟩ := iter_values C out x
  have outIndex : (pad n C).output=n+(C.size+2) := by change n+(second n C).size=_; rw [size_second]
  have trace (j : Nat) (mem : n+j∈(gateAt (pad n C) (C.size+2)).inputs)
      (vj : wireVal n (pad n C) (n+j) x=true) :
      Relation.ReflTransGen (step (pad n C) x) (n+j) (pad n C).output := by
    exact Relation.ReflTransGen.single ⟨C.size+2,by rw [size_pad]; omega,outIndex,mem,vj,po.trans on⟩
  have operands (j : Nat) (gj : gateAt (pad n C) j=dup C.output) (b : Fin 2) :
      opnd (pad n C) j b=C.output := by fin_cases b <;> simp [opnd,gj,dup]
  constructor
  · refine ⟨by rw [size_pad]; omega,by rw [g0]; rfl,trace _ (by rw [g2]; simp [join]) (p0.trans on),?_⟩
    intro b
    rw [operands _ g0 b,(iter_values C out _).1,voff]
  · refine ⟨by rw [size_pad]; omega,by rw [g1]; rfl,trace _ (by rw [g2]; simp [join]) (p1.trans on),?_⟩
    intro b
    rw [operands _ g1 b,(iter_values C out _).1,woff]

end PEqualNP.Outside.L_meta_8869

namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge Finset

abbrev pair {n : Nat} (e : Fin n × Fin n) (r : Fin (n+n)) := decide (r=Fin.castAdd n e.1 ∨ r=Fin.natAdd n e.2)
abbrev quiet {n : Nat} (q : Nat) (R : Fin n → Fin n → Prop) (C : Circuit) := ∀ x : Fin (n+n) → Bool,
  Fintype.card {l : Fin n // x (Fin.natAdd n l)=true} ≤ q →
    (¬∃ p l,R p l ∧ x (Fin.castAdd n p)=true ∧ x (Fin.natAdd n l)=true) → wireVal (n+n) C C.output x=false

theorem single_off {n q : Nat} {R : Fin n → Fin n → Prop} {C : Circuit} (hq : 1≤q) (sound : quiet q R C)
    (v : Fin (n+n)) : wireVal (n+n) C C.output (fun r => decide (r=v))=false := by
  apply sound
  · apply le_trans _ hq
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor
    intro a b
    apply Subtype.ext
    exact Fin.natAdd_injective _ _ ((of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm)
  · rintro ⟨p,l,_,hv,hw⟩
    have eq := (of_decide_eq_true hv).trans (of_decide_eq_true hw).symm
    have h : p.val=n+l.val := congrArg Fin.val eq
    have := p.isLt
    omega

abbrev Posted : Prop := ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             have x12 : ℕ → (Fin (x2 + x2) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (x2 + x2) x5;             have x13 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (x2 + x2) x5;             have x14 : Fin x2 × Fin x2 → Fin (x2 + x2) → Bool := fun (x14 : Fin x2 × Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x14.1 ∨ x15 = Fin.natAdd x2 x14.2);             have x15 : Fin x2 × Fin x2 → Fin (x2 + x2) → ℕ → Prop := fun (x15 : Fin x2 × Fin x2) (x16 : Fin (x2 + x2)) (x17 : ℕ) => x17 < x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ Relation.ReflTransGen (fun (x18 x19 : ℕ) => ∃ x20 < x5.size, x19 = x2 + x2 + x20 ∧ x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x20).inputs ∧ x12 x18 (x14 x15) = Bool.true ∧ x12 x19 (x14 x15) = Bool.true) (x2 + x2 + x17) x5.output ∧ ∀ (x18 : Fin (2 : ℕ)), (x12 (PEqualNP.TopForm.opnd x5 x17 x18) fun (x19 : Fin (x2 + x2)) => Decidable.decide (x19 = x16)) = Bool.false;             (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → x12 x5.output x16 = Bool.false) → (∀ x17 ∈ x6, x3 x17.1 x17.2 ∧ x12 x5.output (x14 x17) = Bool.true ∧ ∃ (x19 : ℕ) (x20 : ℕ), x19 ≠ x20 ∧ ¬x13 x19 x20 ∧ ¬x13 x20 x19 ∧ x15 x17 (Fin.castAdd x2 x17.1) x19 ∧ x15 x17 (Fin.natAdd x2 x17.2) x20) → x6.card ≤ (8 : ℕ) * x5.size

abbrev Unrestricted (overhead : Nat) : Prop :=
  ∀ (q n : Nat) (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit) (E : Finset (Fin n × Fin n)),
    87≤q → n=q^2+q+1 → (∀ l,Fintype.card {p : Fin n // R p l}=q+1) →
    (∀ p t,p≠t → ∃! l,R p l ∧ R t l) → IsAO2 (n+n) C → quiet q R C →
    (∀ e∈E,R e.1 e.2 ∧ wireVal (n+n) C C.output (pair e)=true) →
    E.card≤8*(C.size+overhead)

theorem lower_implication (h : Posted) : Unrestricted 3 := by
  intro q n R _ C E hq hn line joinp model sound acc
  classical
  by_cases he : E.Nonempty
  · obtain ⟨e,ee⟩ := he
    have o : C.output<n+n+C.size := by
      by_contra! bad
      have z := Donor.val_ge (C:=C) (by simp : (List.ofFn (pair e)).length=n+n) bad
      have yes := (acc e ee).2
      change Donor.val C (List.ofFn (pair e)) C.output=true at yes
      rw [z] at yes
      cases yes
    have sn := single_off (by omega : 1≤q) sound
    have b := h q n R (pad (n+n) C) E hq hn line joinp (pad_model model o) (by
      intro x few nohit
      exact ((iter_values C o x).2.2.2).trans (sound x few nohit)) (by
      intro e mem
      obtain ⟨inc,on⟩ := acc e mem
      obtain ⟨one,two⟩ := mark_both C o (pair e) on (Fin.castAdd n e.1) (Fin.natAdd n e.2) (sn _) (sn _)
      exact ⟨inc,((iter_values C o (pair e)).2.2.2).trans on,C.size,C.size+1,by omega,
        (separate C o).1,(separate C o).2,one,two⟩)
    simpa only [size_pad] using b
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

theorem upper_implication (h : Unrestricted 0) : Posted := by
  intro q n R _ C E hq hn line joinp model
  dsimp only
  intro sound acc
  have b := h q n R C E hq hn line joinp model sound (fun e he => ⟨(acc e he).1,(acc e he).2.1⟩)
  simpa using b
end PEqualNP.Outside.L_meta_8869
