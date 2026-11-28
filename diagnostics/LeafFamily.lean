import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11094.Clone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

variable {n m : Nat}

def ref (ρ : Fin n → Fin m) (j u : Fin n) : Fin (m+1) :=
  if u=j then Fin.last m else (ρ u).castSucc

def folded (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (x : Fin m → Bool) (u : Fin n) : Bool :=
  if u=j then x (ρ j) || x b else x (ρ u)

def headGate (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) : Gate :=
  ⟨.or, [(ρ j).val,b.val]⟩

def lift (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (C : Circuit) : Circuit :=
  ⟨headGate ρ j b :: C.gates.map (relGate n (m+1) (ref ρ j)),
   wmap n (m+1) (ref ρ j) C.output⟩

theorem cost (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (C : Circuit) :
    (lift ρ j b C).size = C.size + 1 := by simp [Circuit.size,lift]

theorem mono (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) {C : Circuit} (h : Monotone2 C) :
    Monotone2 (lift ρ j b C) := by
  intro g hg
  change g ∈ headGate ρ j b :: C.gates.map _ at hg
  rcases List.mem_cons.mp hg with rfl|hg
  · simp [headGate]
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using h k hk

theorem evaluation (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (C : Circuit) (x : Fin m → Bool) :
    (lift ρ j b C).eval (List.ofFn x) = C.eval (List.ofFn (folded ρ j b x)) := by
  let y := x (ρ j) || x b
  have startWire : step (List.ofFn x) (headGate ρ j b) = List.ofFn x ++ [y] := by
    simp [step,headGate,y,GateOp.eval,List.getD_eq_getElem?_getD]
  have base : Rel n (m+1) (ref ρ j) (List.ofFn (folded ρ j b x)) (List.ofFn x ++ [y]) := by
    refine ⟨by simp,by simp <;> omega,?_⟩
    intro w
    by_cases h : w<n
    · let u : Fin n := ⟨w,h⟩
      have raw : (List.ofFn (folded ρ j b x)).getD w false = folded ρ j b x u := by
        simp [u,List.getD_eq_getElem?_getD,h]
      rw [raw,show wmap n (m+1) (ref ρ j) w=((ref ρ j) u).val by simp [wmap,h,u]]
      by_cases hu : u=j
      · simp [ref,hu,folded,y,List.getD_eq_getElem?_getD]
      · rw [show ((ref ρ j) u).val=(ρ u).val by simp [ref,hu],
          List.getD_append _ _ _ _ (by simp)]
        simp [folded,hu,List.getD_eq_getElem?_getD]
    · have newIndex : (List.ofFn x ++ [y]).length ≤ wmap n (m+1) (ref ρ j) w := by
        simp [wmap,h]
      rw [List.getD_eq_default _ _ newIndex,List.getD_eq_default _ _ (by simp <;> omega)]
  have finish := (rel_fold n (m+1) (ref ρ j) C.gates _ _ base).2.2 C.output
  change ((C.gates.map _).foldl step (step (List.ofFn x) (headGate ρ j b))).getD _ false = _
  rw [startWire]
  exact finish


open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge

def plain (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π),wmap n m π C.output⟩

theorem plain_eval (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (plain π C).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (π i))) := by
  have base : Rel n m π (List.ofFn (fun i => x (π i))) (List.ofFn x) := by
    refine ⟨by simp, by simp [Nat.add_comm], ?_⟩
    intro w
    by_cases h : w < n
    · simp [wmap,h,List.getD_eq_getElem?_getD]
    · have high : m ≤ wmap n m π w := by simp [wmap,h]
      rw [List.getD_eq_default _ _ (by simpa using high),List.getD_eq_default _ _ (by simp; omega)]
  exact (rel_fold n m π C.gates _ _ base).2.2 _

theorem gateAt_map (π : Fin n → Fin m) (C : Circuit) {i : Nat} (hi : i<C.gates.length) :
    gateAt (plain π C) i = relGate n m π (gateAt C i) := by
  simp [gateAt,plain,List.getD_eq_getElem?_getD,hi]

theorem mapped_earlier (π : Fin n → Fin m) {i w : Nat} (h : w<n+i) :
    wmap n m π w < m+i := by
  unfold wmap
  split
  next hw => have := (π ⟨w,hw⟩).isLt; omega
  next _ => omega

theorem plain_ao (π : Fin n → Fin m) {C : Circuit} (h : IsAO2 n C) : IsAO2 m (plain π C) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact h.1 a ha
  · intro i hi w hw
    have hi' : i<C.gates.length := by simpa [plain] using hi
    rw [gateAt_map π C hi'] at hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact mapped_earlier π (h.2.1 i hi' v hv)
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using h.2.2 a ha

theorem lift_ao (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) {C : Circuit} (h : IsAO2 n C) :
    IsAO2 m (lift ρ j b C) := by
  let p := ref ρ j
  have ho := plain_ao p h
  refine ⟨?_,?_,?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · exact Or.inr rfl
    · exact ho.1 g hg
  · intro i hi w hw
    cases i with
    | zero =>
      change w ∈ [(ρ j).val,b.val] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> simp
    | succ i =>
      have hi' : i < (plain p C).gates.length := by simpa [plain,lift] using hi
      change w ∈ (gateAt (plain p C) i).inputs at hw
      have hh := ho.2.1 i hi' w hw
      omega
  · intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · rfl
    · exact ho.2.2 g hg

def project (j : Fin n) : Fin (n+1) → Fin n := Fin.cases j id

def dup (G : SimpleGraph (Fin n)) (j : Fin n) : SimpleGraph (Fin (n+1)) :=
  G.comap (project j)

instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j : Fin n) :
    DecidableRel (dup G j).Adj := fun a b => inferInstanceAs (Decidable (G.Adj (project j a) (project j b)))

theorem folded_iff (j u : Fin n) (x : Fin (n+1) → Bool) :
    folded Fin.succ j 0 x u = true ↔ ∃ a, project j a = u ∧ x a = true := by
  constructor
  · intro ht
    by_cases h : u=j
    · subst u
      have ev : folded Fin.succ j 0 x j = (x j.succ || x 0) := by simp [folded]
      rw [ev] at ht
      have choices : x j.succ = true ∨ x 0 = true := by simpa only [Bool.or_eq_true] using ht
      rcases choices with h|h
      · exact ⟨j.succ,rfl,h⟩
      · exact ⟨0,rfl,h⟩
    · exact ⟨u.succ,rfl,by simpa [folded,h] using ht⟩
  · rintro ⟨a,ha,hx⟩
    subst u
    cases a using Fin.cases with
    | zero =>
      change folded Fin.succ j 0 x j = true
      simp [folded,hx]
    | succ a =>
      change folded Fin.succ j 0 x a = true
      by_cases h : a=j
      · subst a
        simp [folded,hx]
      · simpa [folded,h] using hx

theorem graph_fold (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j : Fin n)
    (x : Fin (n+1) → Bool) : graphFun (dup G j) ∅ x = graphFun G ∅ (folded Fin.succ j 0 x) := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
  congr 1
  apply propext
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    exact ⟨project j a,project j b,hab,(folded_iff _ _ _).mpr ⟨a,rfl,ha⟩,
      (folded_iff _ _ _).mpr ⟨b,rfl,hb⟩⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    obtain ⟨a,rfl,ha⟩ := (folded_iff _ _ _).mp hu
    obtain ⟨b,rfl,hb⟩ := (folded_iff _ _ _).mp hv
    exact ⟨a,b,huv,ha,hb⟩

theorem folded_pin (j : Fin n) (x : Fin (n+1) → Bool) :
    folded Fin.succ j 0 (Function.update x 0 false) = fun i => x i.succ := by
  funext i
  by_cases h : i=j <;> simp [folded,h]

theorem folded_pull (j : Fin n) (x : Fin n → Bool) :
    folded Fin.succ j 0 (fun v => x (project j v)) = x := by
  funext i
  by_cases h : i=j <;> simp [folded,h,project]

theorem lifted_dirty (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j : Fin n)
    (C : Circuit) (hd : (junk G C).Nonempty) :
    (junk (dup G j) (lift Fin.succ j 0 C)).Nonempty := by
  obtain ⟨i,hi⟩ := hd
  obtain ⟨hi,hg,hx⟩ := Finset.mem_filter.mp hi
  obtain ⟨_,x,hon,hoff⟩ := hx
  have hil : i<C.gates.length := Finset.mem_range.mp hi
  have newlen : i+1 < (lift Fin.succ j 0 C).gates.length := by simp [lift]; omega
  let y := fun v => x (project j v)
  have hf : folded Fin.succ j 0 y = x := folded_pull j x
  refine ⟨i+1,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr newlen,?_,newlen,y,?_,?_⟩⟩
  · change (gateAt (plain (ref Fin.succ j) C) i).op = .and
    rw [gateAt_map _ _ (Finset.mem_range.mp hi)]
    exact hg
  · have ev := evaluation Fin.succ j 0 (⟨C.gates,n+i⟩ : Circuit) y
    rw [hf] at ev
    have ix : wmap n ((n+1)+1) (ref Fin.succ j) (n+i) = (n+1)+(i+1) := by
      simp [wmap] <;> omega
    change ((lift Fin.succ j 0 C).wires (List.ofFn y)).getD ((n+1)+(i+1)) false = true
    rw [←ix]
    exact ev.trans hon
  · rw [graph_fold,hf]
    exact hoff

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 4096 in
theorem pinSource : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size = x3 → PEqualNP.TopForm.IsAO2 x1 x4 → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x4.eval (List.ofFn (Function.update x7 x2 Bool.false)) ≠ x4.eval (List.ofFn (Function.update x8 x2 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size ≤ x4.size ∧ ((∃ (x9 : Fin x1 → Bool), x4.eval (List.ofFn x9) ≠ x4.eval (List.ofFn (Function.update x9 x2 Bool.false))) → x8.size < x4.size) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval (List.ofFn (Function.update x9 x2 Bool.false)) := by
  classical
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp (config := {congrConsts := false})
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp (config := {congrConsts := false}) [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp (config := {congrConsts := false}) only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp (config := {congrConsts := false}) at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp (config := {congrConsts := false}) only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp (config := {congrConsts := false}) [stepWire]; omega)]
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa (config := {congrConsts := false}) using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp (config := {congrConsts := false}) [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp (config := {congrConsts := false}) only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have opMono_imp : OpMono (fun a b => a = true → b = true) := by
    intro op hop l f g h
    rcases hop with rfl | rfl
    · simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro h1 i hi; exact h i hi (h1 i hi)
    · simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

  have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
      val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2

  have val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
      (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
      (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      by_cases hun : u < n
      · rw [val_input hx hun, val_input hx hun]
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < m := by omega
        rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < n + k
        · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
        · rw [ite_eq_right hi, ite_eq_right hi]

  let aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

  let aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

  let bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
    ⟨(List.range (C.gates.length - 1)).map (fun k =>
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
      aliasWire (n + r) i C.output⟩

  have bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp (config := {congrConsts := false}) [bypass]

  have bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

  have gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      gateAt (bypass n C r i) k =
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp (config := {congrConsts := false}) [bypass]

  have bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
      (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
    apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
    intro k hk
    rw [gateAt_bypass (by omega), ite_eq_left hk]

  have aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp (config := {congrConsts := false}) [aliasWire]

  have aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

  have aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

  have bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
        R (val C x (n + r)) (val C x i)) :
      ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hne
      by_cases hlt : u < n + r
      · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
      · rw [aliasWire_gt_self (by omega)]
        by_cases hge : n + C.gates.length ≤ u
        · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
        · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
          have hk1 : k + 1 < C.gates.length := by omega
          have hkr : ¬ k < r := by omega
          have e : n + (k + 1) - 1 = n + k := by omega
          rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
            gateAt_bypass (by omega), ite_eq_right hkr]
          simp (config := {congrConsts := false}) only [aliasGate, List.map_map]
          refine hmono _ (hAO _ hk1) _ _ _ ?_
          intro i' hi'
          simp (config := {congrConsts := false}) only [Function.comp_apply]
          by_cases h1 : i' = n + r
          · subst h1
            rw [aliasWire_self, ite_eq_left (by omega)]
            have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
              rcases hi with hi | hi
              · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
              · rw [ite_eq_right (by omega), val_ge hx hi]
            rw [hgi]
            exact hR ⟨k + 1, hk1, hi'⟩
          · by_cases h2 : i' < n + r
            · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
                bypass_val_lt hx hr i' h2]
              exact hrefl _
            · by_cases h3 : i' < n + (k + 1)
              · have key := ih i' h3 h1
                rw [aliasWire_gt_self (by omega)] at key
                rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
                exact key
              · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
                exact hrefl _

  have bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : R (val C x (n + r)) (val C x i)) :
      R (C.eval x) ((bypass n C r i).eval x) := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    by_cases h : C.output = n + r
    · have hgi : val (bypass n C r i) x i = val C x i := by
        rcases hi with hi | hi
        · exact bypass_val_lt hx hr i hi
        · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
      rw [h, aliasWire_self, hgi]; exact hR
    · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

  have bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x :=
    (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

  have bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hout : C.output ≠ n + r)
      (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
      (bypass n C r i).eval x = C.eval x := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
      (fun h => h.elim fun k hk => absurd hk.2 (hno k hk.1)) _ hout).symm

  have bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
      ∀ k < (bypass n C r i).gates.length,
        (gateAt (bypass n C r i) k).op = GateOp.and ∨
          (gateAt (bypass n C r i) k).op = GateOp.or := by
    intro k hk
    rw [bypass_length] at hk
    rw [gateAt_bypass hk]
    split_ifs with h
    · exact hAO k (by omega)
    · exact hAO (k + 1) (by omega)

  have bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
        g.inputs.length = g'.inputs.length := by
    intro g hg
    simp (config := {congrConsts := false}) only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp (config := {congrConsts := false}) [aliasGate]⟩

  have aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
      aliasWire w i u < m := by
    unfold aliasWire; split_ifs <;> omega

  have bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
      (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
      ∀ k < (bypass n C r i).gates.length,
        ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
    intro k hk u hu
    rw [bypass_length] at hk
    rw [gateAt_bypass hk] at hu
    split_ifs at hu with h
    · exact hRB k (by omega) u hu
    · simp (config := {congrConsts := false}) only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      exact aliasWire_lt hi (by omega) (by omega)

  -- Erase gates one at a time on the zero restriction. Any false output of a
  -- removed gate can be redirected to the pinned input during this process.
  have pinZero (n : ℕ) (p : Fin n) : ∀ k (C : Circuit), C.size = k → IsAO2 n C →
      (∃ x y : Fin n → Bool, C.eval (List.ofFn (Function.update x p false)) ≠
        C.eval (List.ofFn (Function.update y p false))) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
        ((∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠
          C.eval (List.ofFn (Function.update x p false))) → D.size < C.size) ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x p false)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro C hk hC hn
      let row := fun (x : Fin n → Bool) => List.ofFn (Function.update x p false)
      have lengths (x : Fin n → Bool) : (row x).length = n := by simp (config := {congrConsts := false}) [row]
      have pinned (x : Fin n → Bool) : val C (row x) p.val = false := by
        rw [val_input (lengths x) p.isLt]
        change (List.ofFn (Function.update x p false)).getD p.val false = false
        rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false})),List.getElem_ofFn]
        simp (config := {congrConsts := false})
      have opGood : ∀ j < C.gates.length,
          (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
        fun j hj => hC.1 _ (gateAt_mem hj)
      have outNe : C.output ≠ p.val := by
        intro eq
        obtain ⟨x,y,hnxy⟩ := hn
        apply hnxy
        rw [eval_eq_val,eval_eq_val,eq,pinned,pinned]
      by_cases reads : ∃ j < C.gates.length, p.val ∈ (gateAt C j).inputs
      · obtain ⟨j,hj,hr⟩ := reads
        have canErase (u : ℕ) (hu : u < n+j)
            (eq : ∀ x : Fin n → Bool, val C (row x) (n+j) = val C (row x) u) :
            ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
              ((∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (row x)) → D.size < C.size) ∧
              ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (row x) := by
          let B := bypass n C j u
          have hlt : B.size < C.size := by
            change (bypass n C j u).gates.length < C.gates.length
            rw [bypass_length]
            omega
          have hB : IsAO2 n B := by
            refine ⟨?_,bypass_readsBack hu hC.2.1,?_⟩
            · intro g hg
              obtain ⟨g',hg',ho,_⟩ := bypass_mem g hg
              simpa (config := {congrConsts := false}) only [ho] using hC.1 g' hg'
            · intro g hg
              obtain ⟨g',hg',_,hl⟩ := bypass_mem g hg
              rw [hl]
              exact hC.2.2 g' hg'
          have same (x : Fin n → Bool) : B.eval (row x) = C.eval (row x) :=
            bypass_eval_eq (lengths x) opGood hj (Or.inl hu) (eq x)
          have hnB : ∃ x y : Fin n → Bool, B.eval (row x) ≠ B.eval (row y) := by
            obtain ⟨x,y,hxy⟩ := hn
            exact ⟨x,y,by rw [same,same]; exact hxy⟩
          obtain ⟨D,hD,hDsize,_,heval⟩ := ih B.size (by omega) B rfl hB hnB
          refine ⟨D,hD,by omega,fun _ => by omega,?_⟩
          intro x
          exact (heval x).trans (same x)
        rcases opGood j hj with hop | hop
        · refine canErase p.val (by have := p.isLt; omega) ?_
          intro x
          rw [pinned]
          apply Bool.eq_false_iff.mpr
          intro h
          have h' := ((val_and (lengths x) hj hop).mp h p.val hr).2
          rw [pinned] at h'
          cases h'
        · obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hC.2.2 _ (gateAt_mem hj))
          have ha : a < n+j := hC.2.1 j hj a (by simp (config := {congrConsts := false}) [hab])
          have hb : b < n+j := hC.2.1 j hj b (by simp (config := {congrConsts := false}) [hab])
          have hmem : p.val = a ∨ p.val = b := by simpa (config := {congrConsts := false}) [hab] using hr
          rcases hmem with h | h
          · refine canErase b hb ?_
            intro x
            rw [val_gate (lengths x) hj,hop,hab,List.map_cons,List.map_cons,ite_eq_left ha,ite_eq_left hb,← h,pinned]
            cases val C (row x) b <;> rfl
          · refine canErase a ha ?_
            intro x
            rw [val_gate (lengths x) hj,hop,hab,List.map_cons,List.map_cons,ite_eq_left ha,ite_eq_left hb,← h,pinned]
            cases val C (row x) a <;> rfl
      · have absent : ∀ j < C.gates.length, p.val ∉ (gateAt C j).inputs := by
          intro j hj hr
          exact reads ⟨j,hj,hr⟩
        have stable (x : Fin n → Bool) : ∀ w : ℕ, w ≠ p.val →
            val C (List.ofFn x) w = val C (row x) w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hi : w < n
            · rw [val_input (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) hi,val_input (lengths x) hi]
              change (List.ofFn x).getD w false =
                (List.ofFn (Function.update x p false)).getD w false
              rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hi]),List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hi]),
                List.getElem_ofFn,List.getElem_ofFn]
              exact (Function.update_of_ne (fun h => hw (congrArg Fin.val h)) _ _).symm
            · by_cases hl : w < n+C.gates.length
              · let j := w-n
                have hj : j < C.gates.length := by dsimp [j]; omega
                have eq : w = n+j := by dsimp [j]; omega
                rw [eq,val_gate (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) hj,val_gate (lengths x) hj]
                apply congrArg (gateAt C j).op.eval
                apply List.map_congr_left
                intro i hii
                have earlier := hC.2.1 j hj i hii
                rw [ite_eq_left earlier,ite_eq_left earlier]
                exact ih i (by omega) (fun h => absent j hj (h ▸ hii))
              · rw [val_ge (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) (by omega),val_ge (lengths x) (by omega)]
        have same (x : Fin n → Bool) : C.eval (List.ofFn x) = C.eval (row x) := stable x C.output outNe
        refine ⟨C,hC,le_rfl,?_,same⟩
        rintro ⟨x,hx⟩
        exact (hx (same x)).elim
  intro x1 x2 x3 x4 h1 h2 h3
  exact pinZero x1 x2 x3 x4 h1 h2 h3

lemma pair_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pair_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

theorem lifted_least (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {j v : Fin n}
    (edge : G.Adj j v) (C : Circuit) (h : IsLeastAO G C) :
    IsLeastAO (dup G j) (lift Fin.succ j 0 C) := by
  refine ⟨lift_ao _ _ _ h.1,?_,?_⟩
  · funext x
    change (lift _ _ _ _).eval (List.ofFn x) = _
    rw [evaluation,graph_fold]
    exact congrFun h.2.1 _
  · intro D hD hV
    have val (x : Fin (n+1) → Bool) : D.eval (List.ofFn x) = graphFun (dup G j) ∅ x := congrFun hV _
    have pin (x : Fin (n+1) → Bool) : D.eval (List.ofFn (Function.update x 0 false)) =
        graphFun G ∅ (fun i => x i.succ) := by rw [val,graph_fold,folded_pin]
    have yes := (graph_pair G j v).mpr edge
    have no := (graph_pair G v v).not.mpr (fun hh => G.irrefl hh)
    have nonconst : ∃ x y : Fin (n+1) → Bool,
        D.eval (List.ofFn (Function.update x 0 false)) ≠ D.eval (List.ofFn (Function.update y 0 false)) := by
      refine ⟨fun i => pairInput j v (project j i),fun i => pairInput v v (project j i),?_⟩
      rw [pin,pin]
      change graphFun G ∅ (pairInput j v) ≠ graphFun G ∅ (pairInput v v)
      rw [yes]
      exact Ne.symm no
    have essential : ∃ x : Fin (n+1) → Bool, D.eval (List.ofFn x) ≠
        D.eval (List.ofFn (Function.update x 0 false)) := by
      refine ⟨pairInput 0 v.succ,?_⟩
      have he : (dup G j).Adj 0 v.succ := edge
      have hp : (fun i : Fin n => pairInput 0 v.succ i.succ) = pairInput v v := by
        funext i
        simp [pairInput]
      rw [val,(graph_pair _ _ _).mpr he,pin,hp]
      exact Ne.symm no
    obtain ⟨D',hD',_,hlt,hout⟩ := pinSource (n+1) 0 D.size D rfl hD nonconst
    have eq : circuitFun n (plain (project j) D') = graphFun G ∅ := by
      funext x
      change (plain _ _).eval (List.ofFn x) = _
      rw [plain_eval,hout,pin] <;> rfl
    have le := h.2.2 _ (plain_ao (project j) hD') eq
    have sz : (plain (project j) D').size = D'.size := by simp [plain,Circuit.size]
    rw [sz] at le
    rw [cost]
    have := hlt essential
    omega

theorem more_edges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {j v : Fin n}
    (edge : G.Adj j v) : G.edgeFinset.card + 1 ≤ (dup G j).edgeFinset.card := by
  classical
  let M := G.edgeFinset.image (Sym2.map (Fin.succ : Fin n → Fin (n+1)))
  let e : Sym2 (Fin (n+1)) := s(0,v.succ)
  have miss : e ∉ M := by
    intro hm
    obtain ⟨q,_,he⟩ := Finset.mem_image.mp hm
    induction q using Sym2.ind with
    | _ a b =>
      change s(a.succ,b.succ) = s(0,v.succ) at he
      rcases Sym2.eq_iff.mp he with ⟨h,_⟩|⟨_,h⟩ <;> simp at h
  have sub : insert e M ⊆ (dup G j).edgeFinset := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl|hq
    · exact SimpleGraph.mem_edgeFinset.mpr edge
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
      induction z using Sym2.ind with
      | _ a b =>
        have hG : G.Adj a b := SimpleGraph.mem_edgeFinset.mp hz
        change s(a.succ,b.succ) ∈ (dup G j).edgeFinset
        exact SimpleGraph.mem_edgeFinset.mpr hG
  have hcard := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem miss] at hcard
  simpa [M,Finset.card_image_of_injective _ (Sym2.map.injective (Fin.succ_injective _))] using hcard

end PEqualNP.Outside.L_meta_11094.Clone


namespace PEqualNP.Outside.L_meta_11094.Seed

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 30

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 15 := ((x >>> 15) &&& ~~~x).setWidth 15

def cuts (ws : List W) : BitVec 15 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 15) ++ (0 : BitVec 15)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W := [16749129, 1057203346, 119294244, 939547501, 14708150]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 15) (w : W) : Prop :=
  w.getLsbD (15 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 15) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (15 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (15 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 15, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 15) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 30 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 15)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 30 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 30) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 30) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 30, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 30 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 30 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 30 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 30 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 30) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 30 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


def G : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun a b : Fin 5 =>
    ((a=0 ∧ b=1) ∨ (a=0 ∧ b=2) ∨ (a=0 ∧ b=4) ∨ (a=1 ∧ b=2) ∨ (a=1 ∧ b=3)))
instance : DecidableRel G.Adj := by unfold G; infer_instance
def A := PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
def Sample (k : Fin 30) : Fin 5 → Bool := fun i =>
  let r : Nat := if k.val < 15 then ([9, 18, 28] : List Nat).getD (k.val % 3) 0
    else ([3, 5, 17, 6, 10] : List Nat).getD ((k.val - 15) / 3) 0
  r.testBit i.val
theorem input_rows : ∀ k : Fin 30, rawInputs.map (bit k) = List.ofFn (Sample k) := by decide +kernel
theorem goal_rows : ∀ k : Fin 30, bit k goal = A (Sample k) := by decide +kernel
theorem rows_eval (C : Circuit) (hr : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = A x) (k : Fin 30) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (Sample k)
theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = A x) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
theorem knownRoots : inputs.sublists.all (fun l => (!(cuts l == -1) || !(optimized 5 (6-l.length) l))) = true := by decide +kernel
theorem lower (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 5)
    (hr : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = A x) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hs5 : live basicOps goal 5 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hrange := live_card hs5
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hrange
  have hmem : l∈inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have row := List.all_eq_true.mp knownRoots l hmem
  have hc := cuts_full (hlS ▸ hs5)
  have hyes := optimized_complete 5 l (6-l.length) hnd (by omega) (hlS ▸ hs5)
  simp [hc,hyes] at row

def seed : Circuit := ⟨[⟨.or,[0,3]⟩, ⟨.or,[1,4]⟩, ⟨.and,[5,6]⟩,
    ⟨.or,[2,7]⟩, ⟨.or,[0,1]⟩, ⟨.and,[8,9]⟩],10⟩
theorem seedAO : PEqualNP.TopForm.IsAO2 5 seed := by decide +kernel
theorem seedValue : ∀ x : Fin 5 → Bool, seed.eval (List.ofFn x) = A x := by decide +kernel
theorem seedPerfect : PEqualNP.TopForm.IsLeastAO G seed := by
  refine ⟨seedAO,funext seedValue,?_⟩
  intro D hD hv
  by_contra hs
  have m : Monotone2 D := by
    intro g hg
    exact ⟨hD.1 g hg,by have := hD.2.2 g hg; omega⟩
  exact lower D m (by change ¬6 ≤ D.size at hs; omega) (congrFun hv)
theorem seedTop : PEqualNP.TopForm.TopForm G seed := by decide +kernel
theorem dirtyWitness : 2 ∈ PEqualNP.TopForm.junk G seed := by decide +kernel
end PEqualNP.Outside.L_meta_11094.Seed


namespace PEqualNP.Outside.L_meta_11094.NormalForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma isAndOp_eq_true_iff (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

def andIndexSum (C : Circuit) : ℕ :=
  ∑ k ∈ (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true), k

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  exact foldl_wireStep_length C.gates x

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    wireVal n C (n + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n C u x) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, wireVal n C u x = acc.getD u false := by
    intro u hu
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : wireVal n C (n + k) x =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

lemma wireVal_append_lt (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    wireVal n ⟨C.gates ++ [g], out⟩ w x = wireVal n C w x := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD w false =
    (C.gates.foldl wireStep (List.ofFn x)).getD w false
  rw [List.foldl_append]
  have hw' : w < (C.gates.foldl wireStep (List.ofFn x)).length := by
    rw [foldl_wireStep_length, List.length_ofFn]
    exact hw
  exact foldl_wireStep_prefix [g] (C.gates.foldl wireStep (List.ofFn x)) w hw'

lemma wireVal_append_last (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool) :
    wireVal n ⟨C.gates ++ [g], out⟩ (n + C.gates.length) x =
      g.op.eval (g.inputs.map fun u => wireVal n C u x) := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set acc := C.gates.foldl wireStep (List.ofFn x) with hacc
  have hlen : acc.length = n + C.gates.length := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn]
  rw [List.getD_eq_getElem?_getD]
  simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + C.gates.length),
    hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rfl

lemma output_lt_of_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hE : G.edgeFinset.Nonempty) (hF : circuitFun n C = graphFun G ∅) :
    C.output < n + C.gates.length := by
  by_contra hge
  push Not at hge
  obtain ⟨e, he⟩ := hE
  induction e using Sym2.ind with
  | _ u v =>
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have htrue : graphFun G ∅ (fun _ => true) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_eq]
      exact ⟨u, v, hadj, rfl, rfl⟩
    have hfalse : circuitFun n C (fun _ => true) = false := by
      unfold circuitFun Circuit.eval
      rw [List.getD_eq_getElem?_getD]
      have hlen : (C.wires (List.ofFn (fun _ : Fin n => true))).length = n + C.gates.length := by
        rw [wires_length, List.length_ofFn]
      rw [List.getElem?_eq_none (by omega)]
      rfl
    have hEq := congrFun hF (fun _ => true)
    rw [hfalse, htrue] at hEq
    cases hEq

lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
    (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep n acc g) hj']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_left hj]

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
  have hacc_len : acc.length = j := by
    rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
    omega
  have hpref : ∀ k < j, (cones n C).getD k [] = acc.getD k [] := by
    intro k hk
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc k (by omega)
  have hstep : (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) []) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : j < (coneStep n acc C.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      gateAt_eq_getElem C j hj]
  unfold InCone
  rw [hstep, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
    rw [List.mem_cons] at hi
    refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      rw [hpref (w - n) (by omega)]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hw, by simpa using And.intro hnw hlt⟩
    · rw [List.mem_cons]
      rcases hi with rfl | hi
      · exact Or.inl rfl
      · right
        rw [← hpref (w - n) (by omega)]
        exact hi

lemma exists_direct_reader (n : ℕ) (C : Circuit) (i j : ℕ)
    (hj : j < C.gates.length) (h : InCone n C i j) :
    ∃ g, i < g ∧ g ≤ j ∧ g < C.gates.length ∧ n + i ∈ (gateAt C g).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [inCone_iff n C i j hj] at h
    obtain ⟨w, hw, hnw, hlt, hcase⟩ := h
    rcases hcase with rfl | hcone
    · refine ⟨j, by omega, le_refl j, hj, ?_⟩
      have heq : n + (w - n) = w := by omega
      rw [heq]
      exact hw
    · have hklt : w - n < j := by omega
      obtain ⟨g, hig, hgk, hglen, hmem⟩ := ih (w - n) hklt (by omega) hcone
      exact ⟨g, hig, by omega, hglen, hmem⟩

def remap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def origWire (n g w : ℕ) : ℕ :=
  if w < n + g then w else w + 1

def mapGate (f : ℕ → ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map f⟩

def delGate (n g r : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx g).map (mapGate (remap n g r)), remap n g r C.output⟩

lemma delGate_length (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length) :
    (delGate n g r C).gates.length = C.gates.length - 1 := by
  simp [delGate, List.length_eraseIdx_of_lt hg]

lemma delGate_gateAt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (delGate n g r C) k =
      mapGate (remap n g r) (gateAt C (if k < g then k else k + 1)) := by
  have hk' : k < (delGate n g r C).gates.length := by
    rw [delGate_length n g r C hg]; exact hk
  rw [gateAt_eq_getElem (delGate n g r C) k hk']
  have hk_e : k < (C.gates.eraseIdx g).length := by
    rw [List.length_eraseIdx_of_lt hg]; exact hk
  simp only [delGate, List.getElem_map]
  split_ifs with hkg
  · rw [List.getElem_eraseIdx_of_lt hk_e hkg, gateAt_eq_getElem C k (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hk_e (by omega), gateAt_eq_getElem C (k + 1) (by omega)]

lemma delGate_isAO2 (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delGate n g r C) := by
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    exact hAOOnly gt0 (List.mem_of_mem_eraseIdx hgt0)
  · intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap
      split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    simp only [mapGate, List.length_map]
    exact hLen2 gt0 (List.mem_of_mem_eraseIdx hgt0)

lemma delGate_output_lt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (hr : r < n + g) (hout : C.output < n + C.gates.length) :
    (delGate n g r C).output < n + (delGate n g r C).gates.length := by
  rw [delGate_length n g r C hg]
  simp only [delGate, remap]
  split_ifs <;> omega

lemma origWire_remap_ne (n g r u : ℕ) (hne : u ≠ n + g) :
    origWire n g (remap n g r u) = u := by
  unfold origWire remap
  split_ifs <;> omega

lemma origWire_remap_eq (n g r : ℕ) (hr : r < n + g) :
    origWire n g (remap n g r (n + g)) = r := by
  unfold origWire remap
  split_ifs <;> omega

lemma delGate_wireVal_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmatch : wireVal n C (n + g) x = wireVal n C r x) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n (delGate n g r C) w x = wireVal n C (origWire n g w) x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      have hih := ih (remap n g r u) (by omega) (by omega)
      simp only [Function.comp_apply, hih]
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr, hmatch]
      · rw [origWire_remap_ne n g r u hug]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hmono : ∀ p (hp1 : p < l1.length) (hp2 : p < l2.length), l1[p] = true → l2[p] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp2, rfl⟩ := hb
    have hp1 : p < l1.length := by omega
    exact hmono p hp1 hp2 (h1 l1[p] (List.getElem_mem hp1))
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp1, hbp⟩ := hb
    have hp2 : p < l2.length := by omega
    exact ⟨l2[p], List.getElem_mem hp2, hmono p hp1 hp2 hbp⟩

lemma delGate_wireVal_mono (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAOOnly : AndOrOnly C) (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmono_g : wireVal n C (n + g) x = true → wireVal n C r x = true) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n C (origWire n g w) x = true → wireVal n (delGate n g r C) w x = true := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn] at htrue
      exact htrue
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq] at htrue ⊢
      rw [wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB] at htrue
      simp only [mapGate, List.map_map]
      have hop : (gateAt C k0).op = GateOp.and ∨ (gateAt C k0).op = GateOp.or := by
        rw [gateAt_eq_getElem C k0 hk0_lt]
        exact hAOOnly C.gates[k0] (List.getElem_mem hk0_lt)
      apply gateOp_eval_mono (gateAt C k0).op hop _ _ (by simp) _ htrue
      intro p hp1 hp2 hv
      simp only [List.getElem_map, Function.comp_apply] at hv ⊢
      set u := (gateAt C k0).inputs[p]'(by simpa using hp1) with hu_def
      have hu_mem : u ∈ (gateAt C k0).inputs := List.getElem_mem (by simpa using hp1)
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu_mem, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      apply ih (remap n g r u) (by omega) (by omega)
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr]
        rw [hug] at hv
        exact hmono_g hv
      · rw [origWire_remap_ne n g r u hug]
        exact hv

lemma delGate_wireVal_prefix_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g) :
    ∀ w < n + g, wireVal n (delGate n g r C) w x = wireVal n C w x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hkg : k < g := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by
        rw [delGate_length n g r C hg]; omega
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k (by omega)]
      simp only [hkg, ↓reduceIte]
      rw [wireVal_gate n C x k (by omega) hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + k := hRB k (by omega) u hu
      have hrm : remap n g r u = u := by unfold remap; split_ifs <;> omega
      simp only [Function.comp_apply, hrm]
      exact ih u (by omega) (by omega)

lemma no_and_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i g : ℕ)
    (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hig : i < g) (hg : g < C.gates.length)
    (hBelow : BelowF G C i)
    (hgAnd : (gateAt C g).op = GateOp.and)
    (hmem : n + i ∈ (gateAt C g).inputs) : False := by
  rcases hL with ⟨hAO, hF, hMin⟩
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  have hout : C.output < n + C.gates.length := output_lt_of_nonempty G C hE hF
  set C' := delGate n g (n + i) C with hC'
  have hAO' : IsAO2 n C' := delGate_isAO2 n g (n + i) C ⟨hAOOnly, hRB, hLen2⟩ hg (by omega)
  have hout' : C'.output < n + C'.gates.length :=
    delGate_output_lt n g (n + i) C hg (by omega) hout
  have hF' : circuitFun n C' = graphFun G ∅ := by
    funext x
    have hmono_g : wireVal n C (n + g) x = true → wireVal n C (n + i) x = true := by
      intro hg_true
      rw [wireVal_gate n C x g hg hRB, hgAnd] at hg_true
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hg_true
      exact hg_true (wireVal n C (n + i) x) ⟨n + i, hmem, rfl⟩
    cases hgx : graphFun G ∅ x
    · have hi_false : wireVal n C (n + i) x = false := by
        cases hvi : wireVal n C (n + i) x with
        | false => rfl
        | true =>
          have := hBelow x hvi
          rw [hgx] at this
          cases this
      have hg_false : wireVal n C (n + g) x = false := by
        cases hvg : wireVal n C (n + g) x with
        | false => rfl
        | true =>
          have := hmono_g hvg
          rw [hi_false] at this
          cases this
      have hmatch : wireVal n C (n + g) x = wireVal n C (n + i) x := by
        rw [hg_false, hi_false]
      have hval := delGate_wireVal_eq n g (n + i) C x hRB hg (by omega) hmatch C'.output hout'
      have hcf : circuitFun n C' x = wireVal n C' C'.output x := rfl
      rw [hcf, hval]
      have hcfC : circuitFun n C x = false := by rw [hF, hgx]
      by_cases ho : C.output = n + g
      · simp only [hC', delGate]
        rw [ho, origWire_remap_eq n g (n + i) (by omega), ← hmatch]
        change wireVal n C (n + g) x = false
        rw [← ho]
        exact hcfC
      · simp only [hC', delGate]
        rw [origWire_remap_ne n g (n + i) C.output ho]
        exact hcfC
    · have hcfC : wireVal n C C.output x = true := by
        change circuitFun n C x = true
        rw [hF, hgx]
      have hval := delGate_wireVal_mono n g (n + i) C x hAOOnly hRB hg (by omega) hmono_g
        C'.output hout'
      change wireVal n C' C'.output x = true
      apply hval
      by_cases ho : C.output = n + g
      · simp only [hC', delGate]
        rw [ho, origWire_remap_eq n g (n + i) (by omega)]
        rw [ho] at hcfC
        exact hmono_g hcfC
      · simp only [hC', delGate]
        rw [origWire_remap_ne n g (n + i) C.output ho]
        exact hcfC
  have hle := hMin C' hAO' hF'
  have hsz : C'.size = C.size - 1 := delGate_length n g (n + i) C hg
  change C.gates.length ≤ C'.gates.length at hle
  rw [show C'.gates.length = C.gates.length - 1 from hsz] at hle
  omega

def pushOr (n g y i : ℕ) (C : Circuit) : Circuit :=
  let Cmid := delGate n g y C
  ⟨Cmid.gates ++ [⟨GateOp.or, [Cmid.output, n + i]⟩], n + Cmid.gates.length⟩

def shiftDown (g k : ℕ) : ℕ :=
  if k < g then k else k - 1

lemma pushOr_step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i g j : ℕ)
    (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hig : i < g) (hgj : g < j) (hj : j < C.gates.length)
    (hBelow : BelowF G C i)
    (hgOr : (gateAt C g).op = GateOp.or)
    (hjAnd : (gateAt C j).op = GateOp.and)
    (hmem : n + i ∈ (gateAt C g).inputs) :
    ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧
      (junk G C').card = (junk G C).card ∧ andIndexSum C' < andIndexSum C := by
  rcases hL with ⟨hAO, hF, hMin⟩
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  have hg : g < C.gates.length := by omega
  have hout : C.output < n + C.gates.length := output_lt_of_nonempty G C hE hF
  have hgin_len : (gateAt C g).inputs.length = 2 := by
    rw [gateAt_eq_getElem C g hg]
    exact hLen2 C.gates[g] (List.getElem_mem hg)
  rcases hgin : (gateAt C g).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [hgin] at hgin_len
  · simp [hgin] at hgin_len
  · have hmem' : n + i = a ∨ n + i = b := by
      simpa [hgin] using hmem
    set y := if a = n + i then b else a with hy_def
    have hy_mem : y ∈ (gateAt C g).inputs := by
      rw [hgin, hy_def]
      split_ifs <;> simp
    have hy_lt : y < n + g := hRB g hg y hy_mem
    have hg_eval : ∀ x : Fin n → Bool,
        wireVal n C (n + g) x = (wireVal n C (n + i) x || wireVal n C y x) := by
      intro x
      rw [wireVal_gate n C x g hg hRB, hgOr, hgin]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      rw [hy_def]
      split_ifs with ha
      · rw [ha]
      · rcases hmem' with rfl | rfl
        · exact absurd rfl ha
        · exact Bool.or_comm _ _
    set Cmid := delGate n g y C with hCmid
    set C' := pushOr n g y i C with hC'
    have hCmid_len : Cmid.gates.length = C.gates.length - 1 := delGate_length n g y C hg
    have hC'_len : C'.gates.length = C.gates.length := by
      simp only [hC', pushOr, List.length_append, List.length_singleton, ← hCmid, hCmid_len]
      omega
    have hCmid_AO : IsAO2 n Cmid := delGate_isAO2 n g y C ⟨hAOOnly, hRB, hLen2⟩ hg hy_lt
    have hCmid_out : Cmid.output < n + Cmid.gates.length :=
      delGate_output_lt n g y C hg hy_lt hout
    have hC'_AO : IsAO2 n C' := by
      rcases hCmid_AO with ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_⟩
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h1 gt hgt
        · exact Or.inr rfl
      · intro k hk w hw
        have hk' : k < Cmid.gates.length + 1 := by
          simpa [hC', pushOr, ← hCmid] using hk
        by_cases hkm : k < Cmid.gates.length
        · have hgat : gateAt C' k = gateAt Cmid k := by
            rw [gateAt_eq_getElem C' k hk, gateAt_eq_getElem Cmid k hkm]
            simp [hC', pushOr, ← hCmid, List.getElem_append_left hkm]
          rw [hgat] at hw
          exact h2 k hkm w hw
        · have hkeq : k = Cmid.gates.length := by omega
          have hgat : gateAt C' k = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
            rw [gateAt_eq_getElem C' k hk]
            simp [hC', pushOr, ← hCmid, hkeq]
          rw [hgat] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · omega
          · rw [hkeq, hCmid_len]; omega
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h3 gt hgt
        · rfl
    have hC'_F : circuitFun n C' = graphFun G ∅ := by
      funext x
      have hlast : circuitFun n C' x =
          (wireVal n Cmid Cmid.output x || wireVal n Cmid (n + i) x) := by
        change wireVal n C' (n + Cmid.gates.length) x = _
        have h := wireVal_append_last n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩
          (n + Cmid.gates.length) x
        simpa [hC', pushOr, ← hCmid, GateOp.eval] using h
      rw [hlast]
      have hni : wireVal n Cmid (n + i) x = wireVal n C (n + i) x :=
        delGate_wireVal_prefix_eq n g y C x hRB hg hy_lt (n + i) (by omega)
      rw [hni]
      cases hvi : wireVal n C (n + i) x
      · have hmatch : wireVal n C (n + g) x = wireVal n C y x := by
          rw [hg_eval x, hvi, Bool.false_or]
        have hval := delGate_wireVal_eq n g y C x hRB hg hy_lt hmatch Cmid.output hCmid_out
        rw [hval, Bool.or_false]
        have hcfC : wireVal n C C.output x = graphFun G ∅ x := congrFun hF x
        by_cases ho : C.output = n + g
        · simp only [hCmid, delGate]
          rw [ho, origWire_remap_eq n g y hy_lt, ← hmatch, ← ho]
          exact hcfC
        · simp only [hCmid, delGate]
          rw [origWire_remap_ne n g y C.output ho]
          exact hcfC
      · rw [Bool.or_true]
        exact (hBelow x hvi).symm
    have hC'_Least : IsLeastAO G C' := by
      refine ⟨hC'_AO, hC'_F, ?_⟩
      intro D hDAO hDF
      have hle := hMin D hDAO hDF
      change C'.gates.length ≤ D.gates.length
      rw [hC'_len]
      exact hle
    have hgateAt_lt : ∀ m < Cmid.gates.length,
        gateAt C' m = gateAt Cmid m := by
      intro m hm
      have hm' : m < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' m hm', gateAt_eq_getElem Cmid m hm]
      simp [hC', pushOr, ← hCmid, List.getElem_append_left hm]
    have hgateAt_last : gateAt C' Cmid.gates.length = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
      have hm' : Cmid.gates.length < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' Cmid.gates.length hm']
      simp [hC', pushOr, ← hCmid]
    have hop_shift : ∀ k < C.gates.length, k ≠ g →
        (gateAt C' (shiftDown g k)).op = (gateAt C k).op := by
      intro k hk hne
      have hsd : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      rw [hgateAt_lt (shiftDown g k) hsd]
      rw [hCmid, delGate_gateAt n g y C hg (shiftDown g k) (by omega)]
      simp only [mapGate]
      have hidx : (if shiftDown g k < g then shiftDown g k else shiftDown g k + 1) = k := by
        unfold shiftDown; split_ifs <;> omega
      rw [hidx]
    have hval_false : ∀ k < C.gates.length, k ≠ g → ∀ x : Fin n → Bool,
        graphFun G ∅ x = false →
        gateVal n C' (shiftDown g k) x = gateVal n C k x := by
      intro k hk hne x hgx
      have hsd : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      have hi_false : wireVal n C (n + i) x = false := by
        cases hvi : wireVal n C (n + i) x with
        | false => rfl
        | true =>
          have := hBelow x hvi
          rw [hgx] at this
          cases this
      have hmatch : wireVal n C (n + g) x = wireVal n C y x := by
        rw [hg_eval x, hi_false, Bool.false_or]
      have happ : wireVal n C' (n + shiftDown g k) x = wireVal n Cmid (n + shiftDown g k) x :=
        wireVal_append_lt n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩ (n + Cmid.gates.length) x
          (n + shiftDown g k) (by omega)
      have heq := delGate_wireVal_eq n g y C x hRB hg hy_lt hmatch
        (n + shiftDown g k) (by rw [← hCmid]; omega)
      have horig : origWire n g (n + shiftDown g k) = n + k := by
        unfold origWire shiftDown
        split_ifs <;> omega
      change wireVal n C' (n + shiftDown g k) x = wireVal n C (n + k) x
      rw [happ, hCmid, heq, horig]
    have hjunk : (junk G C').card = (junk G C).card := by
      symm
      apply Finset.card_bij (fun k _ => shiftDown g k)
      · intro k hk
        unfold junk gatesWhere at hk ⊢
        rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
        rcases hk with ⟨hk_lt, hk_and, _, x, hkx, hgx⟩
        have hkne : k ≠ g := by
          intro hEq; rw [hEq, hgOr] at hk_and; cases hk_and
        have hsd_lt : shiftDown g k < C'.gates.length := by
          unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
        refine ⟨hsd_lt, ?_, hsd_lt, x, ?_, hgx⟩
        · rw [hop_shift k hk_lt hkne]; exact hk_and
        · rw [hval_false k hk_lt hkne x hgx]; exact hkx
      · intro k1 hk1 k2 hk2 heq
        unfold junk gatesWhere at hk1 hk2
        rw [Finset.mem_filter, Finset.mem_range] at hk1 hk2
        have hne1 : k1 ≠ g := by
          intro hEq; have := hk1.2.1; rw [hEq, hgOr] at this; cases this
        have hne2 : k2 ≠ g := by
          intro hEq; have := hk2.2.1; rw [hEq, hgOr] at this; cases this
        unfold shiftDown at heq
        split_ifs at heq <;> omega
      · intro m hm
        unfold junk gatesWhere at hm
        rw [Finset.mem_filter, Finset.mem_range] at hm
        rcases hm with ⟨hm_lt, hm_and, _, x, hmx, hgx⟩
        have hm_ne : m ≠ Cmid.gates.length := by
          intro hEq; rw [hEq, hgateAt_last] at hm_and; cases hm_and
        have hm_mid : m < Cmid.gates.length := by
          rw [hC'_len] at hm_lt; omega
        set k := if m < g then m else m + 1 with hk_def
        have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
        have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
        have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
        refine ⟨k, ?_, hsd⟩
        unfold junk gatesWhere
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hk_lt, ?_, hk_lt, x, ?_, hgx⟩
        · rw [← hop_shift k hk_lt hkne, hsd]; exact hm_and
        · rw [← hval_false k hk_lt hkne x hgx, hsd]; exact hmx
    have hsum : andIndexSum C' < andIndexSum C := by
      unfold andIndexSum
      set A := (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true)
      set A' := (Finset.range C'.gates.length).filter (fun k => isAndOp (gateAt C' k).op = true)
      have hsum_eq : ∑ k ∈ A, shiftDown g k = ∑ m ∈ A', m := by
        apply Finset.sum_bij (fun k _ => shiftDown g k)
        · intro k hk
          simp only [A, A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk ⊢
          have hkne : k ≠ g := by
            intro hEq; rw [hEq, hgOr] at hk; cases hk.2
          have hsd_lt : shiftDown g k < C'.gates.length := by
            unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
          exact ⟨hsd_lt, by rw [hop_shift k hk.1 hkne]; exact hk.2⟩
        · intro k1 hk1 k2 hk2 heq
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk1 hk2
          have hne1 : k1 ≠ g := by intro hEq; rw [hEq, hgOr] at hk1; cases hk1.2
          have hne2 : k2 ≠ g := by intro hEq; rw [hEq, hgOr] at hk2; cases hk2.2
          unfold shiftDown at heq
          split_ifs at heq <;> omega
        · intro m hm
          simp only [A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hm
          have hm_ne : m ≠ Cmid.gates.length := by
            intro hEq; rw [hEq, hgateAt_last] at hm; cases hm.2
          have hm_mid : m < Cmid.gates.length := by rw [hC'_len] at hm; omega
          set k := if m < g then m else m + 1 with hk_def
          have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
          have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
          have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
          refine ⟨k, ?_, hsd⟩
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hk_lt, by rw [← hop_shift k hk_lt hkne, hsd]; exact hm.2⟩
        · intro _ _; rfl
      rw [← hsum_eq]
      apply Finset.sum_lt_sum
      · intro k _
        unfold shiftDown; split_ifs <;> omega
      · refine ⟨j, ?_, ?_⟩
        · simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hj, hjAnd⟩
        · unfold shiftDown; split_ifs <;> omega
    exact ⟨C', hC'_Least, hC'_len, hjunk, hsum⟩
  · simp [hgin] at hgin_len

lemma main_aux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) (m : ℕ) :
    ∀ C : Circuit, andIndexSum C = m → IsLeastAO G C →
      ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧
        (junk G C').card = (junk G C).card ∧ TopForm G C' := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro C hm hL
    by_cases hTF : TopForm G C
    · exact ⟨C, hL, rfl, rfl, hTF⟩
    · unfold TopForm at hTF
      push Not at hTF
      obtain ⟨i, hi, j, hj, hiAnd, hiBelow, hjAnd, hCone⟩ := hTF
      obtain ⟨g, hig, hgj, hglen, hmem⟩ := exists_direct_reader n C i j hj hCone
      have hgAO : (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := by
        rw [gateAt_eq_getElem C g hglen]
        exact hL.1.1 C.gates[g] (List.getElem_mem hglen)
      rcases hgAO with hgAnd | hgOr
      · exfalso
        exact no_and_reader G C i g hE hL hig hglen hiBelow hgAnd hmem
      · have hgj_lt : g < j := by
          by_contra hge
          have hEq : g = j := by omega
          rw [hEq, hjAnd] at hgOr
          cases hgOr
        obtain ⟨C1, hL1, hsz1, hjunk1, hsum1⟩ :=
          pushOr_step G C i g j hE hL hig hgj_lt hj hiBelow hgOr hjAnd hmem
        obtain ⟨C2, hL2, hsz2, hjunk2, hTF2⟩ :=
          ih (andIndexSum C1) (by omega) C1 rfl hL1
        exact ⟨C2, hL2, hsz2.trans hsz1, hjunk2.trans hjunk1, hTF2⟩

end PEqualNP.Outside.L_meta_11094.NormalForm

namespace PEqualNP.Outside.L_meta_11094

theorem NormalForm :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x7 ∧ x7.size = x4.size ∧ (PEqualNP.TopForm.junk x2 x7).card = (PEqualNP.TopForm.junk x2 x4).card ∧ PEqualNP.TopForm.TopForm x2 x7 := by
  intro n G _ C hE hL
  exact PEqualNP.Outside.L_meta_11094.NormalForm.main_aux G hE (PEqualNP.Outside.L_meta_11094.NormalForm.andIndexSum C) C rfl hL

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem clone_leaf {n : ℕ} (G : SimpleGraph (Fin n)) {j v : Fin n}
    (leaf : ∀ w, G.Adj j w → w = v) :
    ∀ w, (Clone.dup G j).Adj 0 w → w = v.succ := by
  intro w h
  cases w using Fin.cases with
  | zero => exact ((Clone.dup G j).irrefl h).elim
  | succ w => exact congrArg Fin.succ (leaf w h)

theorem as_succ {n : ℕ} (w : Fin (n+1)) (h : w ≠ 0) :
    ∃ z : Fin n, w = z.succ := by
  cases w using Fin.cases with
  | zero => exact (h rfl).elim
  | succ z => exact ⟨z,rfl⟩

theorem clone_leaf_no_four_cycle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {j v : Fin n} (leaf : ∀ w, G.Adj j w → w = v) (h4 : NoFourCycle G) :
    NoFourCycle (Clone.dup G j) := by
  have tip := clone_leaf G leaf
  intro p q hpq
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have A := (Finset.mem_filter.mp ha).2
  have B := (Finset.mem_filter.mp hb).2
  by_cases hp : p = 0
  · subst p
    exact (tip a A.1).trans (tip b B.1).symm
  by_cases hq : q = 0
  · subst q
    exact (tip a A.2).trans (tip b B.2).symm
  by_cases hA : a = 0
  · subst a
    exact (hpq ((tip p A.1.symm).trans (tip q A.2.symm).symm)).elim
  by_cases hB : b = 0
  · subst b
    exact (hpq ((tip p B.1.symm).trans (tip q B.2.symm).symm)).elim
  obtain ⟨p,rfl⟩ := as_succ p hp
  obtain ⟨q,rfl⟩ := as_succ q hq
  obtain ⟨a,rfl⟩ := as_succ a hA
  obtain ⟨b,rfl⟩ := as_succ b hB
  apply congrArg Fin.succ
  apply Finset.card_le_one.mp (h4 p q (fun h => hpq (congrArg Fin.succ h)))
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,A⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,B⟩

theorem leaf_family (t : Nat) : ∃ (G : SimpleGraph (Fin (5+t))) (d : DecidableRel G.Adj),
    letI := d
    ∃ (C : Circuit) (j v : Fin (5+t)), G.Adj j v ∧ IsLeastAO G C ∧
      (junk G C).Nonempty ∧ C.size = 6+t ∧ 5+t ≤ G.edgeFinset.card ∧
      (∀ w, G.Adj j w → w = v) ∧ NoFourCycle G ∧
      ∃ a b c, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a := by
  induction t with
  | zero =>
    refine ⟨Seed.G,inferInstance,Seed.seed,3,1,?_,Seed.seedPerfect,⟨2,Seed.dirtyWitness⟩,rfl,?_,?_,?_,0,1,2,?_⟩ <;>
      decide +kernel
  | succ t ih =>
    obtain ⟨G,d,h⟩ := ih
    letI := d
    obtain ⟨C,j,v,edge,l,dirt,cs,es,leaf,h4,a,b,c,tri⟩ := h
    let H := Clone.dup G j
    let D := Clone.lift Fin.succ j 0 C
    refine ⟨H,inferInstance,D,0,v.succ,edge,Clone.lifted_least G edge C l,
      Clone.lifted_dirty G j C dirt,?_,?_,clone_leaf G leaf,clone_leaf_no_four_cycle G leaf h4,
      a.succ,b.succ,c.succ,tri⟩
    · change (Clone.lift _ _ _ _).size = _
      rw [Clone.cost,cs]
      omega
    · have more := Clone.more_edges G edge
      change 5+t.succ ≤ (Clone.dup G j).edgeFinset.card
      omega

theorem breaks (K : Nat) : ∃ t : Nat, 6+t+1+K*(5+t+1).sqrt < (5+t)+(5+t) := by
  let b := 2*K+8
  refine ⟨b*b,?_⟩
  have h : 5+b*b+1 ≤ (b+1)*(b+1) := by dsimp [b]; nlinarith
  have s := Nat.sqrt_le_sqrt h
  simp only [Nat.sqrt_eq] at s
  have sk := Nat.mul_le_mul_left K s
  dsimp [b] at *
  nlinarith


end PEqualNP.Outside.L_meta_11094

open PEqualNP.Outside.L_meta_11094 PEqualNP.TopForm

theorem PEqualNP.Outside.L_meta_11094 : ¬ (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x3 → (∃ (x6 : Fin x2) (x7 : Fin x2), x3.Adj x6 x7) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → x3.edgeSet.ncard + x3.edgeSet.ncard ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt) := by
  rintro ⟨K,hK⟩
  obtain ⟨t,ht⟩ := breaks K
  obtain ⟨G,d,rest⟩ := leaf_family t
  letI := d
  obtain ⟨C,j,v,edge,l,dirty,hsize,hcard,_,hfour,_⟩ := rest
  have ge : G.edgeFinset.Nonempty := ⟨s(j,v),SimpleGraph.mem_edgeFinset.mpr edge⟩
  obtain ⟨T,tLeast,tCost,tJunk,tForm⟩ := NormalForm (5+t) G C ge l
  have td : (junk G T).Nonempty := Finset.card_pos.mp (by rw [tJunk]; exact Finset.card_pos.mpr dirty)
  have bad := hK (5+t) G T hfour ⟨j,v,edge⟩ tLeast tForm td
  rw [←SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset,tCost,hsize] at bad
  omega

