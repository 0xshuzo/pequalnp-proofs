import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17948.Rank

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
def Slice {n : ℕ} (W : Wires n) (v : Fin n) (w : ℕ) : (Fin n → Bool) → Bool :=
  fun x => W (fun i => if i=v then false else x i) w

theorem fixed_iff {n : ℕ} (W : Wires n) (v : Fin n) (j : ℕ)
    (zero : ∀ w, W (fun _ => false) w=false)
    (raw : ∀ x, W x v.val=x v) :
    Fixed W v j ↔ ∃ k<n+j, Slice W v (n+j)=Slice W v k := by
  constructor
  · rintro ⟨b,c,k,hk,eq⟩
    have low := eq (fun _ => false) rfl
    rw [zero,zero] at low
    cases c with
    | true => cases b <;> contradiction
    | false =>
      cases b with
      | false =>
        refine ⟨v.val,by omega,?_⟩
        funext x
        unfold Slice
        rw [eq _ (by simp),raw]
        simp
      | true =>
        refine ⟨k,hk,?_⟩
        funext x
        unfold Slice
        rw [eq _ (by simp)]
        simp
  · rintro ⟨k,hk,eq⟩
    refine ⟨true,false,k,hk,?_⟩
    intro x hx
    have erase : (fun i => if i=v then false else x i)=x := by
      funext i
      by_cases e : i=v <;> simp [e,hx]
    have e := congrFun eq x
    unfold Slice at e
    rw [erase] at e
    simpa only [Bool.true_and,Bool.or_false] using e

def prior {α : Type*} [DecidableEq α] (s : ℕ → α) (n j : ℕ) : Bool :=
  (List.range (n+j)).any fun k => decide (s (n+j)=s k)

theorem prior_iff {α : Type*} [DecidableEq α] (s : ℕ → α) (n j : ℕ) :
    prior s n j = true ↔ ∃ k < n+j, s (n+j)=s k := by simp [prior,List.any_eq_true]

theorem rank_identity {α : Type*} [DecidableEq α] (s : ℕ → α) (n m : ℕ) :
    ((Finset.range (n+m)).image s).card + ((Finset.range m).filter (fun j => prior s n j=true)).card =
      ((Finset.range n).image s).card + m := by
  let old (j : ℕ) := prior s n j = true
  change ((Finset.range (n+m)).image s).card + ((Finset.range m).filter old).card = _
  induction m with
  | zero => simp
  | succ m ih =>
    have seen : s (n+m) ∈ (Finset.range (n+m)).image s ↔ old m := by
      simp only [old,prior_iff,Finset.mem_image,Finset.mem_range]
      constructor <;> rintro ⟨k,lt,eq⟩ <;> exact ⟨k,lt,eq.symm⟩
    rw [show n+(m+1) = (n+m)+1 by omega,Finset.range_add_one,Finset.image_insert,Finset.range_add_one]
    by_cases h : old m
    · rw [Finset.insert_eq_of_mem (seen.mpr h),Finset.filter_insert]
      simp only [ite_eq_left h,Finset.card_insert_of_notMem (by simp : m ∉ (Finset.range m).filter old)]
      omega
    · rw [Finset.card_insert_of_notMem (fun z => h (seen.mp z)),Finset.filter_insert]
      simp only [ite_eq_right h]
      omega

noncomputable def rank {n : ℕ} (W : Wires n) (v : Fin n) (length : ℕ) : ℕ := by
  classical
  exact ((Finset.range length).image (Slice W v)).card

theorem fixed_five {n : ℕ} (W : Wires n) (v : Fin n) (m : ℕ)
    (zero : ∀ w, W (fun _ => false) w=false) (raw : ∀ x, W x v.val=x v) :
    (∃ S : Finset ℕ, 5≤S.card ∧ ∀ j∈S, j < m ∧ Fixed W v j) ↔
      rank W v (n+m)+5≤rank W v n+m := by
  classical
  let s := Slice W v
  let old j := prior s n j = true
  let coll := (Finset.range m).filter old
  have eq := rank_identity s n m
  change rank W v (n+m)+coll.card=rank W v n+m at eq
  constructor
  · rintro ⟨S,big,all⟩
    have sub : S ⊆ coll := by
      intro j hj
      obtain ⟨jlt,hfix⟩ := all j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jlt,(prior_iff s n j).mpr ((fixed_iff W v j zero raw).mp hfix)⟩
    have h := Finset.card_le_card sub
    omega
  · intro small
    refine ⟨coll,by omega,?_⟩
    intro j hj
    obtain ⟨ltj,h⟩ := Finset.mem_filter.mp hj
    exact ⟨Finset.mem_range.mp ltj,(fixed_iff W v j zero raw).mpr ((prior_iff s n j).mp h)⟩

theorem physical_zero {n : ℕ} (C : Circuit) (legal : IsAO2 n C) :
    ∀ w, val C (List.ofFn (fun _ : Fin n => false)) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w<n
    · exact val_ofFn C (fun _ => false) ⟨w,hw⟩
    by_cases long : n+C.gates.length ≤ w
    · exact val_ge (n:=n) (by simp) long
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hw)
    have hj : j<C.gates.length := by omega
    let g := gateAt C j
    have mem := gateAt_mem (C:=C) hj
    have kind : g.op=GateOp.and ∨ g.op=GateOp.or := legal.1 g mem
    have pair : ∃ a b, g.inputs=[a,b] := by
      have len := legal.2.2 g mem
      rcases h:g.inputs with _ | ⟨a, _ | ⟨b, _ | t⟩⟩
      · simp [h] at len
      · simp [h] at len
      · exact ⟨a,b,rfl⟩
      · simp [h] at len
    obtain ⟨a,b,pins⟩ := pair
    rw [val_gate (n:=n) (by simp) hj]
    change g.op.eval (g.inputs.map _) = false
    rw [pins]
    have aa : (if a<n+j then val C (List.ofFn fun _ : Fin n => false) a else false)=false := by
      split_ifs with h
      · exact ih _ h
      · rfl
    have bb : (if b<n+j then val C (List.ofFn fun _ : Fin n => false) b else false)=false := by
      split_ifs with h
      · exact ih _ h
      · rfl
    rcases kind with ka|ko
    · simp [ka,GateOp.eval,aa,bb]
    · simp [ko,GateOp.eval,aa,bb]

end PEqualNP.Outside.L_meta_17948.Rank
