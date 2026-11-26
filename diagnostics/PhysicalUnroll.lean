import Mathlib
import PEqualNP.Defs

-- The clean-gate cover certificate below is adapted from the project’s L_meta_1602.
namespace Singleton5176

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

theorem singleton_protection : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (z : Fin n → Bool) (S : Set ℕ),
    PEqualNP.TopForm.IsAO2 n C →
    let w := fun k => (C.wires (List.ofFn z)).getD k false
    (∀ i : Fin n, ↑i ∈ S → z i = false) →
    (∀ j g, C.gates[j]? = some g → n+j ∈ S →
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i ∈ g.inputs, i ∈ S) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∃ i ∈ g.inputs, i ∈ S) ∨ ∀ i ∈ g.inputs, w i = false)) →
    ∀ k ∈ S, w k = false := by
  intro n C z S model _ raw closed
  let w := fun (k : ℕ) => (wiresFrom C.gates (List.ofFn z)).getD k false
  change ∀ k ∈ S, w k = false
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro mem
    by_cases hk : k<n
    · change (wiresFrom _ _).getD k false = false
      rw [getD_wiresFrom_lt _ _ _ (by simpa using hk)]
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
      exact raw ⟨k,hk⟩ mem
    by_cases hend : k<n+C.gates.length
    · let j := k-n
      have hj : j<C.gates.length := by dsimp [j]; omega
      have pos : k=n+j := by dsimp [j]; omega
      let g := C.gates[j]
      have hit : C.gates[j]?=some g := List.getElem?_eq_getElem hj
      have gin : g∈C.gates := List.mem_of_getElem? hit
      have prior (a) (ha : a∈g.inputs) : a<n+j := by
        apply model.2.1 j hj a
        change a∈(C.gates.getD j ⟨.or,[]⟩).inputs
        simpa only [List.getD_eq_getElem _ _ hj] using ha
      have eqv : w k = g.op.eval (g.inputs.map w) := by
        have h := getD_wiresFrom_gate C.gates (List.ofFn z) j hj
        rw [List.length_ofFn] at h
        rw [pos]
        change (wiresFrom C.gates _).getD (n+j) false = _
        refine h.trans ?_
        congr 1
        apply List.map_congr_left
        intro i hi
        exact if_pos (prior i hi)
      have stop := closed j g hit (pos ▸ mem)
      rw [eqv]
      rcases model.1 g gin with tag|tag
      · rw [tag]
        apply Bool.eq_false_iff.mpr
        intro all
        simp only [GateOp.eval, List.all_eq_true, id_eq] at all
        have accepts (i) (hi : i∈g.inputs) : w i=true := all _ (List.mem_map_of_mem hi)
        rcases stop.2 tag with ⟨i,hi,si⟩|none
        · exact Bool.noConfusion ((ih i (by have := prior i hi; omega) si).symm.trans (accepts i hi))
        · obtain ⟨i,hi⟩ : ∃ i, i∈g.inputs := List.exists_mem_of_ne_nil _ (by
            intro emp; have h := model.2.2 g gin; simp [emp] at h)
          exact Bool.noConfusion ((none i hi).symm.trans (accepts i hi))
      · rw [tag]
        apply Bool.eq_false_iff.mpr
        intro any
        simp only [GateOp.eval, List.any_eq_true, id_eq] at any
        obtain ⟨t,ht,vt⟩ := any
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
        exact Bool.noConfusion ((ih i (by have := prior i hi; omega) (stop.1 tag i hi)).symm.trans vt)
    · apply List.getD_eq_default
      rw [length_wiresFrom, List.length_ofFn]
      omega

end Singleton5176
namespace Occurrence5176
open PEqualNP.MetaComplexity

/-- Number of occurrences of the selected raw input in the unfolded circuit. -/
def copies {n} (t : Fin n) : DMFormula n → Nat
  | .lit v _ => if v=t then 1 else 0
  | .and a b | .or a b => copies t a + copies t b

/-- The linear trace for one raw input on the evaluation at `x`. -/
def trace {n} (t : Fin n) (x : Fin n → Bool) : DMFormula n → Bool
  | .lit v _ => decide (v=t)
  | .and a b => (trace t x a && b.eval x) || (a.eval x && trace t x b)
  | .or a b => trace t x a || trace t x b

private theorem unchanged {n} (t : Fin n) (x y : Fin n → Bool)
    (same : ∀ i, i≠t → x i=y i) (φ : DMFormula n) (h : copies t φ=0) : φ.eval x = φ.eval y := by
  induction φ with
  | lit v c =>
    have hv : v≠t := by rintro rfl; simp [copies] at h
    simp only [DMFormula.eval,same v hv]
  | and a b ha hb =>
    change copies t a+copies t b=0 at h
    rw [DMFormula.eval,DMFormula.eval,ha (by omega),hb (by omega)]
  | or a b ha hb =>
    change copies t a+copies t b=0 at h
    rw [DMFormula.eval,DMFormula.eval,ha (by omega),hb (by omega)]

theorem trace_of_unique {n} (t : Fin n) (x y : Fin n → Bool)
    (same : ∀ i, i≠t → x i=y i) (φ : DMFormula n) (h : copies t φ≤1)
    (off : φ.eval x=false) (on_ : φ.eval y=true) : trace t x φ=true := by
  induction φ with
  | lit v c =>
    by_cases hv : v=t
    · simp [trace,hv]
    · have z := unchanged t x y same (.lit v c) (by simp [copies,hv]); simp_all
  | and a b ha hb =>
    change copies t a+copies t b≤1 at h
    have yes := Bool.and_eq_true_iff.mp on_
    change (a.eval x && b.eval x)=false at off
    change ((trace t x a && b.eval x) || (a.eval x && trace t x b))=true
    by_cases nz : copies t a=0
    · have at_ := (unchanged t x y same a nz).trans yes.1
      have bf : b.eval x=false := by simpa [at_] using off
      simp [at_,hb (by omega) bf yes.2]
    · have bt := (unchanged t x y same b (by omega)).trans yes.2
      have af : a.eval x=false := by simpa [bt] using off
      simp [bt,ha (by omega) af yes.1]
  | or a b ha hb =>
    change copies t a+copies t b≤1 at h
    have no := Bool.or_eq_false_iff.mp off
    change (trace t x a || trace t x b)=true
    cases h1 : a.eval y with
    | true => simp [ha (by omega) no.1 h1]
    | false =>
      have h2 : b.eval y=true := by simpa [DMFormula.eval,h1] using on_
      simp [hb (by omega) no.2 h2]

end Occurrence5176
namespace Wires5176
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Singleton5176 Occurrence5176

abbrev F := DMFormula 26
abbrev raw0 : F := .lit 0 true

def tree (C : Circuit) (k : Nat) : F :=
  if h : k<26 then .lit ⟨k,h⟩ true else
    let g := C.gates.getD (k-26) ⟨.or,[]⟩
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    if ha : a<k then
      if hb : b<k then
        match g.op with
        | .and => .and (tree C a) (tree C b)
        | _ => .or (tree C a) (tree C b)
      else raw0
    else raw0
termination_by k

private theorem rawTree (C : Circuit) (i : Fin 26) : tree C i.val = .lit i true := by
  rw [tree]
  simp only [i.isLt, ↓reduceDIte]

private theorem childPrior {C : Circuit} (ao : IsAO2 26 C) {j : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) {i : Nat} (mem : i∈g.inputs) : i<26+j := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  apply ao.2.1 j hj i
  simpa only [List.getD_eq_getElem _ _ hj,hg] using mem

private theorem atGate {C : Circuit} (ao : IsAO2 26 C) {j a b : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) (ins : g.inputs=[a,b]) :
    (g.op=.and → tree C (26+j)=.and (tree C a) (tree C b)) ∧
    (g.op=.or → tree C (26+j)=.or (tree C a) (tree C b)) := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  have ga : a<26+j := childPrior ao hit (by simp [ins])
  have gb : b<26+j := childPrior ao hit (by simp [ins])
  have hget : C.gates.getD j ⟨.or,[]⟩=g := by rw [List.getD_eq_getElem _ _ hj,hg]
  constructor <;> intro op <;> rw [tree] <;> simp [hget,ins,op,ga,gb]

abbrev Positive (φ : F) := DMFormula.rec (motive:=fun _ : F => Prop)
    (fun _ c => c=true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

abbrev wire (C : Circuit) (x : Fin 26 → Bool) (k : Nat) := (C.wires (List.ofFn x)).getD k false

private theorem rawValue (C : Circuit) (x : Fin 26 → Bool) (i : Fin 26) : wire C x i.val=x i := by
  change (wiresFrom C.gates (List.ofFn x)).getD i.val false=_
  rw [getD_wiresFrom_lt _ _ _ (by simpa using i.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]

private theorem gateValue {C : Circuit} (ao : IsAO2 26 C) (x : Fin 26 → Bool) {j : Nat} {g : Gate}
    (hit : C.gates[j]?=some g) : wire C x (26+j)=g.op.eval (g.inputs.map (wire C x)) := by
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp hit
  have h := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn,hg] at h
  refine h.trans ?_
  congr 1
  apply List.map_congr_left
  intro i hi
  exact if_pos (childPrior ao hit hi)

theorem semantics {C : Circuit} (ao : IsAO2 26 C) (k : Nat) (valid : k<26+C.size) :
    Positive (tree C k) ∧ ∀ x, (tree C k).eval x=wire C x k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases raw : k<26
    · let i : Fin 26 := ⟨k,raw⟩
      change Positive (tree C i.val) ∧ _
      rw [rawTree]
      exact ⟨rfl,fun x => by simpa [DMFormula.eval] using (rawValue C x i).symm⟩
    let j := k-26
    have hj : j<C.gates.length := by change k<26+C.gates.length at valid; dsimp [j]; omega
    let g := C.gates[j]
    have hit : C.gates[j]?=some g := List.getElem?_eq_getElem hj
    have gin := List.mem_of_getElem? hit
    have pos : k=26+j := by dsimp [j]; omega
    obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 g gin)
    have ha := childPrior ao hit (i:=a) (by simp [ins])
    have hb := childPrior ao hit (i:=b) (by simp [ins])
    obtain ⟨pa,ea⟩ := ih a (by omega) (by omega)
    obtain ⟨pb,eb⟩ := ih b (by omega) (by omega)
    rw [pos]
    rcases ao.1 g gin with op|op
    · rw [(atGate ao hit ins).1 op]
      exact ⟨⟨pa,pb⟩,fun x => by simp [gateValue ao x hit,op,ins,GateOp.eval,DMFormula.eval,ea,eb]⟩
    · rw [(atGate ao hit ins).2 op]
      exact ⟨⟨pa,pb⟩,fun x => by simp [gateValue ao x hit,op,ins,GateOp.eval,DMFormula.eval,ea,eb]⟩

end Wires5176
