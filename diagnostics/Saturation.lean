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
theorem rawBelow {n : ℕ} (C : Net n) (v : Fin n) : Below C v v.val := by
  intro x hx
  rw [C.raw,hx]
theorem readsBelow {n : ℕ} (C : Net n) (v : Fin n) (u j : ℕ) (z : Below C v u)
    (hj : j∈readers C u) : Fixed C.W v j := by
  obtain ⟨ltj,mem⟩ := (read_spec C _ _).mp hj
  obtain ⟨a,b,meet,pins,ha,hb,eval⟩ := C.pair j ltj
  have casesU : u=a ∨ u=b := by simpa [pins] using mem
  rcases casesU with rfl|rfl
  · cases meet with
    | true => exact ⟨false,false,b,hb,fun x hx => by simp [eval,z x hx]⟩
    | false => exact ⟨true,false,b,hb,fun x hx => by simp [eval,z x hx]⟩
  · cases meet with
    | true => exact ⟨false,false,a,ha,fun x hx => by simp [eval,z x hx]⟩
    | false => exact ⟨true,false,a,ha,fun x hx => by simp [eval,z x hx]⟩

theorem fourth {n : ℕ} (C : Net n) (v : Fin n) (sat : 4≤(readers C v.val).card)
    (no : ¬Winner C) {j : ℕ} (hj : j<C.circuit.size) (fixed : Fixed C.W v j) : j∈readers C v.val := by
  by_contra outside
  apply no
  refine ⟨v,insert j (readers C v.val),?_,?_⟩
  · rw [Finset.card_insert_of_notMem outside]; omega
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|old
    · exact ⟨hj,fixed⟩
    · exact ⟨((read_spec C _ _).mp old).1,readsBelow C v _ _ (rawBelow C v) old⟩

theorem copy_for_pin {n : ℕ} (C : Net n) {j : ℕ} (dup : GlobalCopy C j) (v : Fin n) :
    Fixed C.W v j := by
  obtain ⟨k,hk,eq⟩ := dup
  exact ⟨true,false,k,hk,fun x _ => by simpa using eq x⟩

theorem three_rigid {n : ℕ} (C : Net n) (S : Finset (Fin n)) (big : 3≤S.card)
    (sat : ∀ v∈S, 4≤(readers C v.val).card) (no : ¬ Winner C) :
    ∀ j < C.circuit.size, ¬GlobalCopy C j := by
  intro j hj dupe
  have all (v : Fin n) (hv : v∈S) := fourth C v (sat v hv) no hj (copy_for_pin C dupe v)
  have inc : S.image Fin.val ⊆ (gateAt C.circuit j).inputs.toFinset := by
    intro k hk
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    exact List.mem_toFinset.mpr ((read_spec C _ _).mp (all v hv)).2
  have size := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ Fin.val_injective] at size
  obtain ⟨a,b,_,pair,_,_,_⟩ := C.pair j hj
  have bound := List.toFinset_card_le (gateAt C.circuit j).inputs
  rw [pair] at bound
  simp only [List.length_cons,List.length_nil] at bound
  rw [pair] at size
  omega

theorem absorbed {n : ℕ} (C : Net n) (v : Fin n) (w : ℕ) (diff : w≠v.val)
    (z : Below C v w) {j : ℕ} (hr : j∈readers C v.val) (hw : j∈readers C w) :
    GlobalCopy C j := by
  obtain ⟨hj,hv⟩ := (read_spec C _ _).mp hr
  have hm := ((read_spec C _ _).mp hw).2
  obtain ⟨a,b,meet,pins,ha,hb,ev⟩ := C.pair j hj
  simp only [pins,List.mem_cons,List.not_mem_nil,or_false] at hv hm
  have h_and (x) : C.W x w && C.W x v.val = C.W x w := by
    rw [C.raw]
    cases hx:x v with
    | false => simp [z x hx]
    | true => simp
  have h_or (x) : C.W x w || C.W x v.val = C.W x v.val := by
    rw [C.raw]
    cases hx:x v with
    | false => simp [z x hx]
    | true => simp
  have casesAB : (a=w ∧ b=v.val) ∨ (a=v.val ∧ b=w) := by grind
  rcases casesAB with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases meet
  · exact ⟨_,hb,fun x => by rw [ev]; simpa using h_or x⟩
  · exact ⟨_,ha,fun x => by rw [ev]; simpa using h_and x⟩
  · exact ⟨_,ha,fun x => by rw [ev]; simpa [Bool.or_comm] using h_or x⟩
  · exact ⟨_,hb,fun x => by rw [ev]; simpa [Bool.and_comm] using h_and x⟩

theorem saturated_dead {n : ℕ} (C : Net n) (v : Fin n) (sat : 4≤(readers C v.val).card)
    (no : ¬Winner C) (irred : ∀ j < C.circuit.size, ¬GlobalCopy C j)
    (w : ℕ) (diff : w≠v.val) (z : Below C v w) : readers C w=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j h
  have hj := ((read_spec C _ _).mp h).1
  have dir := fourth C v sat no hj (readsBelow C v w j z h)
  exact irred j hj (absorbed C v w diff z dir h)

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
end PEqualNP.Outside.L_meta_17948.Saturation
