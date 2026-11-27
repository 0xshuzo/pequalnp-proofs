import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17948.Saturation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

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
lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
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
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
abbrev Wires (n : ℕ) := (Fin n → Bool) → ℕ → Bool
def Fixed {n : ℕ} (W : Wires n) (v : Fin n) (j : ℕ) : Prop :=
  ∃ b c : Bool, ∃ k < n+j, ∀ x, x v=false → W x (n+j)=(b && W x k || c)

structure Net (n : ℕ) where
  circuit : Circuit
  W : Wires n
  raw : ∀ x (i : Fin n), W x i.val=x i
  pair : ∀ j < circuit.size, ∃ (a b : ℕ) (meet : Bool),
    (gateAt circuit j).inputs=[a,b] ∧ a < n+j ∧ b < n+j ∧
    ∀ x, W x (n+j)=if meet then (W x a && W x b) else (W x a || W x b)

def readers {n : ℕ} (C : Net n) (i : ℕ) : Finset ℕ :=
  (Finset.range C.circuit.size).filter fun j => i∈(gateAt C.circuit j).inputs
def Winner {n : ℕ} (C : Net n) : Prop :=
  ∃ (v : Fin n) (J : Finset ℕ), 5≤J.card ∧ ∀ j∈J, j < C.circuit.size ∧ Fixed C.W v j
def Below {n : ℕ} (C : Net n) (v : Fin n) (u : ℕ) : Prop :=
  ∀ x, x v=false → C.W x u=false
def GlobalCopy {n : ℕ} (C : Net n) (j : ℕ) : Prop :=
  ∃ i<n+j, ∀ x, C.W x (n+j)=C.W x i

theorem read_spec {n : ℕ} (C : Net n) (i j : ℕ) :
    j∈readers C i ↔ j < C.circuit.size ∧ i∈(gateAt C.circuit j).inputs := by simp [readers]
def physical {n : ℕ} (C : Circuit) (legal : ∀ j (g : Gate), C.gates[j]?=some g →
    (g.op=.and ∨ g.op=.or) ∧ ∃ a b, g.inputs=[a,b] ∧ a≠b ∧ a < n+j ∧ b < n+j)
    (W : Wires n) (hw : ∀ x i, W x i=val C (List.ofFn x) i) : Net n where
  circuit := C
  W := W
  raw := fun x i => (hw x i).trans (val_ofFn C x i)
  pair := by
    intro j hj
    change j < C.gates.length at hj
    let g := gateAt C j
    have get : C.gates[j]?=some g := by simp [g,gateAt_eq hj,hj]
    obtain ⟨kind,a,b,hp,ne,ha,hb⟩ := legal j g get
    rcases kind with ka|ko
    · refine ⟨a,b,true,hp,ha,hb,?_⟩
      intro x
      rw [hw,val_gate (n:=n) (by simp) hj]
      change g.op.eval (g.inputs.map _) = _
      simp [ka,hp,GateOp.eval,hw,ha,hb]
    · refine ⟨a,b,false,hp,ha,hb,?_⟩
      intro x
      rw [hw,val_gate (n:=n) (by simp) hj]
      change g.op.eval (g.inputs.map _) = _
      simp [ko,hp,GateOp.eval,hw,ha,hb]
def twice (a b : Fin 26) (i : Fin 26) : Bool := decide (i=a ∨ i=b)
def State (x : Fin 26→Bool) : Prop := ∃ a b : Fin 13, (a=b ∨ a=b+1 ∨ a=b+3 ∨ a=b+9) ∧
    x (Fin.castAdd 13 a)=true ∧ x (Fin.natAdd 13 b)=true
instance (x : Fin 26→Bool) : Decidable (State x) := by unfold State; infer_instance
def chosen : Fin 26→Fin 26→Fin 26 := ![![0,17,13,17,13,13,13,13,13,17,13,13,13,17,13,13,13,13,13,13,13,13,13,13,13,13],![14,0,13,14,13,13,13,13,13,14,13,13,13,14,13,13,13,13,13,13,13,13,13,13,13,13],![14,15,0,14,15,14,14,14,14,14,15,14,14,14,15,14,14,14,14,14,14,14,14,14,14,14],![15,15,13,0,13,13,13,13,13,15,13,13,13,15,13,13,13,13,13,13,13,13,13,13,13,13],![14,16,16,14,0,14,14,14,14,14,16,14,14,14,16,14,14,14,14,14,14,14,14,14,14,14],![15,15,17,17,15,0,15,15,15,15,15,17,15,15,15,17,15,15,15,15,15,15,15,15,15,15],![16,16,16,18,18,16,0,16,16,16,16,16,18,16,16,16,18,16,16,16,16,16,16,16,16,16],![19,17,17,17,19,19,17,0,17,17,17,17,17,17,17,17,17,19,17,17,17,17,17,17,17,17],![18,20,18,18,18,20,20,18,0,18,18,18,18,18,18,18,18,18,20,18,18,18,18,18,18,18],![19,19,13,19,13,13,13,13,13,0,13,13,13,19,13,13,13,13,13,13,13,13,13,13,13,13],![14,20,20,14,20,14,14,14,14,14,0,14,14,14,20,14,14,14,14,14,14,14,14,14,14,14],![15,15,21,21,15,21,15,15,15,15,15,0,15,15,15,21,15,15,15,15,15,15,15,15,15,15],![16,16,16,22,22,16,22,16,16,16,16,16,0,16,16,16,22,16,16,16,16,16,16,16,16,16],![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,1],![1,2,1,1,1,1,1,1,1,1,1,1,1,2,0,1,1,1,2,1,1,1,1,1,2,1],![2,2,3,2,2,2,2,2,2,2,2,2,2,2,3,0,2,2,2,3,2,2,2,2,2,3],![3,3,3,4,3,3,3,3,3,3,3,3,3,4,3,4,0,3,3,3,4,3,3,3,3,3],![4,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,4,0,4],![1,5,1,1,1,1,1,1,1,1,1,1,1,5,5,1,1,1,0,1,1,1,1,1,5,1],![2,2,6,2,2,2,2,2,2,2,2,2,2,2,6,6,2,2,2,0,2,2,2,2,2,6],![3,3,3,7,3,3,3,3,3,3,3,3,3,7,3,7,7,3,3,3,0,3,3,3,3,3],![4,4,4,4,8,4,4,4,4,4,4,4,4,4,8,4,8,8,4,4,4,0,4,4,4,4],![5,5,5,5,5,9,5,5,5,5,5,5,5,5,5,9,5,9,9,5,5,5,0,5,5,5],![6,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,6,0,0,0,0,0,0,0,6],![1,7,1,1,1,1,1,1,1,1,1,1,1,7,7,1,1,1,7,1,1,1,1,1,0,1],![2,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0,0,0,0,2,0,0]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem chosen_spec : ∀ u v, u≠v → let z:=chosen u v
    z≠u ∧ z≠v ∧ State (twice u z) ∧ ¬State (twice v z) := by decide +kernel

theorem dominates (C : Net 26) (u v z : Fin 26) (uv : u≠v) (zu : z≠u) (zv : z≠v)
    (nested : readers C u.val ⊆ readers C v.val) :
    ∀ w, w < 26+C.circuit.size → w≠u.val → C.W (twice u z) w=true → C.W (twice v z) w=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro valid diff on
    by_cases raw : w<26
    · let i : Fin 26 := ⟨w,raw⟩
      have ne : i≠u := fun e => diff (congrArg Fin.val e)
      have hx : twice u z i=true := by rw [←C.raw]; exact on
      rw [show w=i.val from rfl,C.raw]
      simp [twice,ne] at hx
      simp [twice,hx]
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt raw)
    have jl : j < C.circuit.size := by omega
    obtain ⟨a,b,q,pins,al,bl,eq⟩ := C.pair j jl
    by_cases rd : j∈readers C u.val
    · have ua := ((read_spec C _ _).mp rd).2
      have va := ((read_spec C _ _).mp (nested rd)).2
      simp only [pins,List.mem_cons,List.not_mem_nil,or_false] at ua va
      have neq : u.val≠v.val := fun e => uv (Fin.ext e)
      have alt : (a=u.val ∧ b=v.val) ∨ (a=v.val ∧ b=u.val) := by grind
      rcases alt with ⟨a1,b1⟩|⟨a1,b1⟩ <;> cases q <;>
        simp [eq,a1,b1,C.raw,twice,uv,Ne.symm uv,Ne.symm zu,Ne.symm zv] at on ⊢
    · have anti : u.val∉[a,b] := fun h => rd ((read_spec C _ _).mpr ⟨jl,pins ▸ h⟩)
      have na : a≠u.val := fun h => anti (by simp [h])
      have nb : b≠u.val := fun h => anti (by simp [h])
      have ia := ih a al (by omega) na
      have ib := ih b bl (by omega) nb
      cases q with
      | true =>
        simp only [eq,ite_true,Bool.and_eq_true] at on ⊢
        exact ⟨ia on.1,ib on.2⟩
      | false =>
        simp only [eq,Bool.false_eq_true,ite_false,Bool.or_eq_true] at on ⊢
        exact on.imp ia ib

theorem separate (C : Net 26) (valid : C.circuit.output < 26+C.circuit.size)
    (spec : ∀ x, C.W x C.circuit.output=true ↔ State x) :
    ∀ u v : Fin 26, u≠v → ¬readers C u.val ⊆ readers C v.val := by
  intro u v uv nested
  let z := chosen u v
  obtain ⟨zu,zv,yes,no⟩ := chosen_spec u v uv
  have raw : C.circuit.output≠u.val := by
    intro eq
    have neg : ∀ i : Fin 26, ¬State (twice i i) := by decide +kernel
    have q : C.W (twice u u) C.circuit.output=true := by rw [eq,C.raw]; simp [twice]
    exact neg u ((spec _).mp q)
  exact no ((spec _).mp (dominates C u v z uv zu zv nested _ valid raw ((spec _).mpr yes)))

theorem single_reader {C : Net 26} (valid : C.circuit.output < 26+C.circuit.size)
    (spec : ∀ x, C.W x C.circuit.output=true ↔ State x)
    (u : Fin 26) (j : ℕ) (single : readers C u.val={j}) :
    ∀ v : Fin 26, v≠u → j∉readers C v.val := by
  intro v vu hv
  apply separate C valid spec u v vu.symm
  rw [single]; simpa using hv

theorem physical_valid (C : Circuit) (W : Wires 26) (hw : ∀ x i, W x i=val C (List.ofFn x) i)
    (spec : ∀ x, W x C.output=true ↔ State x) : C.output < 26+C.size := by
  by_contra! h
  have yes : State (twice 0 13) := by decide
  have pos := (spec _).mpr yes
  have z := val_ge (C:=C) (x:=List.ofFn (twice 0 13)) (n:=26) (by simp) h
  rw [hw,z] at pos
  contradiction

end PEqualNP.Outside.L_meta_17948.Saturation
