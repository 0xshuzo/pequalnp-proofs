import Mathlib
import PEqualNP.Defs

-- Wire bypass lemmas from the published L_meta_1485.
namespace PEqualNP.Outside.L_meta_3568.Bypass

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
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
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
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
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
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

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hk, hm⟩ => absurd hm (hno k hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
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

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

lemma isAO2_bypass {n : ℕ} {D : Circuit} {r i : ℕ} (hD : PEqualNP.TopForm.IsAO2 n D)
    (hi : i < n + r) : PEqualNP.TopForm.IsAO2 n (bypass n D r i) := by
  refine ⟨?_, bypass_readsBack hi hD.2.1, ?_⟩
  · intro g hg
    obtain ⟨g', hg', hop, _⟩ := bypass_mem g hg
    rw [hop]; exact hD.1 g' hg'
  · intro g hg
    obtain ⟨g', hg', _, hl⟩ := bypass_mem g hg
    rw [hl]; exact hD.2.2 g' hg'

end PEqualNP.Outside.L_meta_3568.Bypass

-- Slice compiler from the published L_meta_18145.
namespace PEqualNP.Outside.L_meta_3568.Slice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

private abbrev W (n : ℕ) (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  scan boolStep gs (List.ofFn x)

private theorem inputAt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (W n gs x).getD i false = x ⟨i,hi⟩ := by
  rw [scan_prefix boolStep _ _ _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]

private theorem wireAtGate {n : ℕ} (C : Circuit) (h : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    (W n C.gates x).getD (n+j) false = boolStep (W n C.gates x) C.gates[j] := by
  simpa only [List.length_ofFn] using
    (scan_gate boolStep C.gates (List.ofFn x) false j hj (fun r s he => by
      unfold boolStep
      congr 1
      apply List.map_congr_left
      intro i hi
      apply he
      have := h.2.1 j hj i (by rwa [gateAt_eq_getElem hj])
      simpa using this))

private def readOpt (w : List Bool) (ref : Option ℕ) : Bool :=
  (ref.map fun i => w.getD i false).getD false

private def validRef (lim : ℕ) (ref : Option ℕ) : Prop :=
  ∀ i, ref = some i → i < lim

private theorem optPrefix (w : List Bool) (v : Bool) (ref : Option ℕ) (ok : validRef w.length ref) :
    readOpt (w ++ [v]) ref = readOpt w ref := by
  cases ref with
  | none => rfl
  | some i => exact List.getD_append _ _ _ _ (ok i rfl)

private inductive Action where
  | reuse (ref : Option ℕ)
  | add (g : Gate)

private def Action.ref (lim : ℕ) : Action → Option ℕ
  | .reuse r => r
  | .add _ => some lim

private def Action.newGates : Action → List Gate
  | .reuse _ => []
  | .add g => [g]

private def Action.eval (w : List Bool) : Action → Bool
  | .reuse r => readOpt w r
  | .add g => boolStep w g

private def Action.Well (limit : ℕ) : Action → Prop
  | .reuse r => validRef limit r
  | .add g => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      ∀ i ∈ g.inputs, i < limit

private theorem newGatesSmall (act : Action) : act.newGates.length ≤ 1 := by cases act <;> simp [Action.newGates]

private def pick (op : GateOp) (a b : Option ℕ) : Action :=
  match a, b with
  | some i, some j => .add ⟨op,[i,j]⟩
  | none, v | v, none => .reuse (if op.eval [false,true] then v else none)

private theorem pickSound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Option ℕ) (w : List Bool) : (pick op a b).eval w =
      op.eval [readOpt w a,readOpt w b] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp [pick,Action.eval,readOpt,GateOp.eval,boolStep]

private theorem pickWell (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Option ℕ) (lim : ℕ) (va : validRef lim a) (vb : validRef lim b) :
    (pick op a b).Well lim := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [pick,Action.Well,validRef,GateOp.eval]

private theorem actionApply {n : ℕ} (gs : List Gate) (legal : IsAO2 n (⟨gs,0⟩ : Circuit))
    (act : Action) (well : act.Well (n+gs.length)) :
    IsAO2 n (⟨gs++act.newGates,0⟩ : Circuit) := by
  cases act with
  | reuse r => simpa [Action.newGates] using legal
  | add g =>
    obtain ⟨hop,hlen,back⟩ := well
    refine ⟨?_,?_,?_⟩
    · intro g' hm
      rcases List.mem_append.mp hm with h | h
      · exact legal.1 _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hop
    · intro j hj i hi
      change j < (gs ++ [g]).length at hj
      simp only [List.length_append,List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · have he : gateAt ⟨gs++[g],0⟩ j = gateAt ⟨gs,0⟩ j := by
          rw [gateAt,gateAt,List.getD_append _ _ _ _ hlt]
        exact legal.2.1 j hlt i (he ▸ hi)
      · have heq : j = gs.length := by omega
        subst j
        have he : gateAt ⟨gs++[g],0⟩ gs.length = g := by
          rw [gateAt,List.getD_append_right _ _ _ _ (by simp),Nat.sub_self,List.getD_cons_zero]
        exact back i (he ▸ hi)
    · intro g' hm
      rcases List.mem_append.mp hm with h | h
      · exact legal.2.2 _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hlen

private theorem oldSource (act : Action) (w : List Bool) (ref : Option ℕ)
    (vr : validRef w.length ref) :
    readOpt (scan boolStep act.newGates w) ref = readOpt w ref := by
  cases act with
  | reuse r => rfl
  | add g => exact optPrefix w _ ref vr

private theorem resultSource (act : Action) (w : List Bool) (ok : act.Well w.length) :
    readOpt (scan boolStep act.newGates w) (act.ref w.length) = act.eval w := by
  cases act with
  | reuse r => rfl
  | add g =>
    change (w ++ [boolStep w g]).getD w.length false = boolStep w g
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self,List.getD_cons_zero]

private theorem refAvailable (act : Action) (lim : ℕ) (hw : act.Well lim) :
    validRef (lim+act.newGates.length) (act.ref lim) := by
  cases act with
  | reuse r => simpa [Action.ref,Action.newGates,Action.Well] using hw
  | add g => simp [Action.ref,Action.newGates,validRef]

private theorem validEnlarge (ref : Option ℕ) {a b : ℕ} (h : a ≤ b) (vr : validRef a ref) : validRef b ref :=
  fun i hi => Nat.lt_of_lt_of_le (vr i hi) h

private abbrev fixed {n : ℕ} (x : Fin n → Bool) (p : Fin n) := Function.update x p false

private structure Prefix (n : ℕ) (C : Circuit) (p : Fin n) (S : Finset ℕ) (j : ℕ) where
  gs : List Gate
  f : ℕ → Option ℕ
  legal : IsAO2 n (⟨gs,0⟩ : Circuit)
  cost : gs.length + (S.filter (· < j)).card ≤ j
  valids : ∀ i < n+j, validRef (n+gs.length) (f i)
  sound : ∀ i < n+j, ∀ x : Fin n → Bool,
    readOpt (W n gs x) (f i) = (W n C.gates (fixed x p)).getD i false

private theorem countFilterStep (S : Finset ℕ) (j : ℕ) :
    (S.filter (· < j+1)).card = (S.filter (· < j)).card + if j ∈ S then 1 else 0 := by
  by_cases hm : j ∈ S
  · have e : S.filter (· < j+1) = insert j (S.filter (· < j)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hl⟩
        by_cases e : i = j
        · exact Or.inl e
        · exact Or.inr ⟨hi,by omega⟩
      · rintro (rfl | ⟨hi,hl⟩)
        · exact ⟨hm,by omega⟩
        · exact ⟨hi,by omega⟩
    rw [e,Finset.card_insert_of_notMem (by simp),ite_eq_left hm]
  · have e : S.filter (· < j+1) = S.filter (· < j) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi,hl⟩
        exact ⟨hi,by have hn : i ≠ j := fun eq => hm (eq ▸ hi); omega⟩
      · rintro ⟨hi,hl⟩; exact ⟨hi,by omega⟩
    rw [e,ite_eq_right hm,Nat.add_zero]

private def Prefix.step {n : ℕ} {C : Circuit} {p : Fin n} {S : Finset ℕ} {j : ℕ}
    (P : Prefix n C p S j) (act : Action) (hw : act.Well (n+P.gs.length))
    (hshort : act.newGates.length + (if j ∈ S then 1 else 0) ≤ 1)
    (ok : ∀ x : Fin n → Bool, act.eval (W n P.gs x) =
      (W n C.gates (fixed x p)).getD (n+j) false) : Prefix n C p S (j+1) := by
  let new := P.gs ++ act.newGates
  let ff (i : ℕ) := if i = n+j then act.ref (n+P.gs.length) else P.f i
  refine ⟨new,ff,actionApply P.gs P.legal act hw,?_,?_,?_⟩
  · have hc := P.cost
    rw [countFilterStep]
    simp only [new,List.length_append]
    omega
  · intro i hi
    by_cases he : i = n+j
    · simpa [ff,new,he,Nat.add_assoc] using refAvailable act (n+P.gs.length) hw
    · change validRef _ (if i = n+j then _ else P.f i)
      rw [ite_eq_right he]
      exact validEnlarge _ (by simp [new]) (P.valids _ (by omega))
  · intro i hi x
    have len : (W n P.gs x).length = n+P.gs.length := by rw [scan_length,List.length_ofFn]
    rw [show W n new x = scan boolStep act.newGates (W n P.gs x) by exact scan_append boolStep _ _ _]
    by_cases he : i = n+j
    · subst i
      simp only [ff,ite_true]
      rw [← len,resultSource _ _ (by rw [len]; exact hw)]
      exact ok x
    · simp only [ff,he,ite_false]
      rw [oldSource _ _ _ (by rw [len]; exact P.valids _ (by omega))]
      exact P.sound _ (by omega) x

private theorem build {n : ℕ} {C : Circuit} (p : Fin n) (S : Finset ℕ)
    (hC : IsAO2 n C)
    (aliases : ∀ j ∈ S, ∃ i < n+j, ∀ x : Fin n → Bool,
      (W n C.gates (fixed x p)).getD (n+j) false = (W n C.gates (fixed x p)).getD i false)
    (j : ℕ) (bound : j ≤ C.gates.length) : Nonempty (Prefix n C p S j) := by
  induction j with
  | zero =>
    refine ⟨⟨[],fun i => if i = p.val then none else some i,by simp [IsAO2,PEqualNP.EdgeOwnership.AndOrOnly,ReadsBack],by simp,?_,?_⟩⟩
    · intro i hi
      by_cases he : i = p.val
      · simp [he,validRef]
      · simpa [he,validRef] using hi
    · intro i hi x
      have hi' : i < n := by simpa using hi
      rw [inputAt C.gates _ i hi']
      by_cases he : i = p.val
      · have hp : (⟨i,hi'⟩ : Fin n) = p := Fin.ext he
        simp [he,readOpt,fixed]
      · have hp : (⟨i,hi'⟩ : Fin n) ≠ p := fun h => he (congrArg Fin.val h)
        simp only [he,ite_false,readOpt,Option.map_some,Option.getD_some]
        rw [inputAt [] x i hi']
        simp [fixed,Function.update_of_ne hp]
  | succ j ih =>
    obtain ⟨P⟩ := ih (by omega)
    have hj : j < C.gates.length := by omega
    by_cases hm : j ∈ S
    · obtain ⟨i,hi,he⟩ := aliases j hm
      refine ⟨P.step (.reuse (P.f i)) (P.valids i hi) (by simp [Action.newGates,hm]) (fun x => ?_)⟩
      exact (P.sound i hi x).trans (he x).symm
    · obtain ⟨hop,hin,ha,hb⟩ := ao2_gate_props hC hj
      let g := gateAt C j
      let a := opnd C j 0
      let b := opnd C j 1
      let act := pick g.op (P.f a) (P.f b)
      refine ⟨P.step act (pickWell _ hop _ _ _ (P.valids a ha) (P.valids b hb)) ?_ (fun x => ?_)⟩
      · simpa [hm] using newGatesSmall act
      · rw [wireAtGate C hC j hj,← gateAt_eq_getElem hj]
        rw [pickSound g.op hop, P.sound a ha, P.sound b hb]
        change g.op.eval [_ , _] = boolStep _ g
        rw [boolStep,show g.inputs = [a,b] from hin]
        rfl



theorem compile : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : Finset ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x4,         x6 < x2.size ∧           ∃ x8 < x1 + x6,             ∀ (x9 : Fin x1 → Bool),               have x10 : List Bool := x2.wires (List.ofFn (Function.update x9 x3 Bool.false));               x10.getD (x1 + x6) Bool.false = x10.getD x8 Bool.false) →       (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x2.eval (List.ofFn (Function.update x7 x3 Bool.false)) ≠ x2.eval (List.ofFn (Function.update x8 x3 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size + x4.card ≤ x2.size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x2.eval (List.ofFn (Function.update x9 x3 Bool.false))) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3568.Slice in
  intro n C p S hC hAlias nconst
  obtain ⟨P⟩ := build p S hC (fun j hj => (hAlias j hj).2) C.gates.length (Nat.le_refl _)
  have within : C.output < n + C.gates.length := by
    by_contra! h
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      change (W n C.gates (fixed z p)).getD C.output false = false
      apply List.getD_eq_default
      rwa [scan_length,List.length_ofFn]
    exact hn ((zero x).trans (zero y).symm)
  cases he : P.f C.output with
  | none =>
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      have hz := P.sound C.output within z
      rw [he] at hz
      exact hz.symm
    exact False.elim (hn ((zero x).trans (zero y).symm))
  | some o =>
    have hsize := P.cost
    have hs : S.filter (· < C.gates.length) = S := Finset.filter_true_of_mem (fun _ hi => (hAlias _ hi).1)
    rw [hs] at hsize
    refine ⟨⟨P.gs,o⟩,P.legal,hsize,?_⟩
    intro x
    change (W n P.gs x).getD o false = (W n C.gates (fixed x p)).getD C.output false
    simpa only [he,readOpt,Option.map_some,Option.getD_some] using P.sound C.output within x

end PEqualNP.Outside.L_meta_3568.Slice

namespace PEqualNP.Outside.L_meta_3568.Reader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

variable {n : Nat} {C : Circuit}

private abbrev V (C : Circuit) (x : Fin n → Bool) (w : Nat) :=
  (C.wires (List.ofFn x)).getD w false

private theorem vin (x : Fin n → Bool) (p : Fin n) : V C x p.val = x p := by
  change Bypass.val C (List.ofFn x) p.val = x p
  rw [Bypass.val_input (List.length_ofFn) p.isLt, List.getD_eq_getElem _ _ (by simpa using p.isLt)]
  simp

private theorem vgate (hao : IsAO2 n C) (j : Nat) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    V C x (n+j) = (gateAt C j).op.eval
      [V C x (opnd C j 0), V C x (opnd C j 1)] := by
  obtain ⟨_, hin, ha, hb⟩ := Slice.ao2_gate_props hao hj
  change Bypass.val C _ _ = _
  rw [Bypass.val_gate (List.length_ofFn) hj, hin]
  simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb]
  rfl

private theorem inputs_pair (hao : IsAO2 n C) {j w : Nat} (hj : j < C.gates.length)
    (hw : w ∈ (gateAt C j).inputs) :
    ∃ t < n+j, (opnd C j 0 = w ∧ opnd C j 1 = t) ∨
      (opnd C j 0 = t ∧ opnd C j 1 = w) := by
  obtain ⟨_, hi, ha, hb⟩ := Slice.ao2_gate_props hao hj
  rw [hi] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with h | h
  · exact ⟨_,hb,Or.inl ⟨h.symm,rfl⟩⟩
  · exact ⟨_,ha,Or.inr ⟨rfl,h.symm⟩⟩

private theorem vseparate (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) {j w : Nat} (hj : j < C.gates.length) (hw : w < n+j) :
    ¬ ∀ (x : Fin n → Bool), V C x (n+j) = V C x w := by
  intro same
  let D := Bypass.bypass n C j w
  have eqv : circuitFun n D = circuitFun n C := by
    funext x
    exact Bypass.bypass_eval_eq List.length_ofFn
      (fun k hk => (Slice.ao2_gate_props least.1 hk).1) hj (Or.inl hw) (same x)
  have le := least.2.2 D (Bypass.isAO2_bypass least.1 hw) (eqv.trans least.2.1)
  change C.gates.length ≤ (Bypass.bypass n C j w).gates.length at le
  rw [Bypass.bypass_length] at le
  omega

private theorem live (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n) {j : Nat} (hj : j < C.gates.length)
    (hout : C.output ≠ n+j) : ∃ k < C.gates.length, n+j ∈ (gateAt C k).inputs := by
  by_contra! h
  let D := Bypass.bypass n C j p.val
  have hp : p.val < n+j := by have := p.isLt; omega
  have eqv : circuitFun n D = circuitFun n C := by
    funext x
    exact Bypass.bypass_eval_unread List.length_ofFn
      (fun k hk => (Slice.ao2_gate_props least.1 hk).1) hj (Or.inl hp) hout h
  have le := least.2.2 D (Bypass.isAO2_bypass least.1 hp) (eqv.trans least.2.1)
  change C.gates.length ≤ (Bypass.bypass n C j p.val).gates.length at le
  rw [Bypass.bypass_length] at le
  omega

private def Zero (C : Circuit) (p : Fin n) (w : Nat) : Prop :=
  ∀ x : Fin n → Bool, x p = false → V C x w = false

private theorem inputZero (p : Fin n) : Zero C p p.val := by
  intro x hx
  simpa only [vin] using hx

private theorem zeroAnd (hao : IsAO2 n C) {p : Fin n} {j w : Nat}
    (hj : j < C.gates.length) (hand : (gateAt C j).op = .and)
    (hw : w ∈ (gateAt C j).inputs) (hz : Zero C p w) : Zero C p (n+j) := by
  obtain ⟨t,_,h | h⟩ := inputs_pair hao hj hw <;> intro x hx <;>
    rw [vgate hao j hj x, hand, h.1, h.2] <;> simp [GateOp.eval, hz x hx]

private theorem aliasOfZeroRead (hao : IsAO2 n C) {p : Fin n} {j w : Nat}
    (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs) (hz : Zero C p w) :
    ∃ i < n+j, ∀ (x : Fin n → Bool), x p = false → V C x (n+j) = V C x i := by
  rcases (Slice.ao2_gate_props hao hj).1 with hand | hor
  · exact ⟨p.val,by have := p.isLt; omega,fun x hx => (zeroAnd hao hj hand hw hz x hx).trans
      (by rw [vin,hx])⟩
  · obtain ⟨t,ht,h | h⟩ := inputs_pair hao hj hw <;> refine ⟨t,ht,?_⟩ <;> intro x hx <;>
      rw [vgate hao j hj x, hor, h.1, h.2] <;> simp [GateOp.eval, hz x hx]

private theorem noJointReader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n) {k j : Nat} (hk : k < C.gates.length)
    (pk : p.val ∈ (gateAt C k).inputs) (jk : n+j ∈ (gateAt C k).inputs)
    (hz : Zero C p (n+j)) : False := by
  obtain ⟨t,_,h | h⟩ := inputs_pair least.1 hk pk
  all_goals
    have ne : n+j ≠ p.val := by have := p.isLt; omega
    have hin := (Slice.ao2_gate_props least.1 hk).2.1
    rw [hin,h.1,h.2] at jk
    have ht : n+j = t := by simpa [ne] using jk
    subst t
    rcases (Slice.ao2_gate_props least.1 hk).1 with ha | ho
    · apply vseparate G least hk (w := n+j) (least.1.2.1 k hk _ (by rw [hin,h.1,h.2]; simp))
      intro x
      rw [vgate least.1 k hk x,ha,h.1,h.2,vin]
      cases hx : x p <;> simp [GateOp.eval,hz x,hx]
    · apply vseparate G least hk (w := p.val) (by have := p.isLt; omega)
      intro x
      rw [vgate least.1 k hk x,ho,h.1,h.2,vin]
      cases hx : x p <;> simp [GateOp.eval,hz x,hx]

noncomputable def direct (C : Circuit) (p : Fin n) : Finset Nat :=
  (Finset.range C.gates.length).filter fun j => p.val ∈ (gateAt C j).inputs

theorem count_direct_plus_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n)
    (hpos : ∃ x : Fin n → Bool, x p = false ∧ circuitFun n C x = true)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn (Function.update x p false)) ≠
      C.eval (List.ofFn (Function.update y p false)))
    (reader : ∃ j < C.gates.length, (gateAt C j).op = .and ∧ p.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + (direct C p).card + 1 ≤ C.size ∧
      ∀ x, circuitFun n D x = circuitFun n C (Function.update x p false) := by
  classical
  obtain ⟨j,hj,hand,hp⟩ := reader
  have hz := zeroAnd least.1 hj hand hp (inputZero p)
  obtain ⟨x,hx,hon⟩ := hpos
  have hout : C.output ≠ n+j := by
    intro eqv
    change V C x C.output = true at hon
    rw [eqv,hz x hx] at hon
    contradiction
  obtain ⟨k,hk,jk⟩ := live G least p hj hout
  have kn : k ∉ direct C p := by
    intro mem
    exact noJointReader G least p hk (Finset.mem_filter.mp mem).2 jk hz
  have alias (g : Nat) (hg : g ∈ insert k (direct C p)) :
      g < C.size ∧ ∃ i < n+g, ∀ x : Fin n → Bool,
        V C (Function.update x p false) (n+g) = V C (Function.update x p false) i := by
    have pack (hgt : g < C.gates.length) (w : Nat) (hw : w ∈ (gateAt C g).inputs)
        (zero : Zero C p w) : g < C.size ∧ ∃ i < n+g, ∀ x : Fin n → Bool,
          V C (Function.update x p false) (n+g) = V C (Function.update x p false) i := by
      obtain ⟨i,hi,he⟩ := aliasOfZeroRead least.1 hgt hw zero
      exact ⟨hgt,i,hi,fun x => he _ (by simp)⟩
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact pack hk _ jk hz
    · obtain ⟨hg,hread⟩ := Finset.mem_filter.mp hg
      exact pack (Finset.mem_range.mp hg) p.val hread (inputZero p)
  obtain ⟨D,hao,hle,hfun⟩ := Slice.compile n C p (insert k (direct C p)) least.1 alias hnc
  rw [Finset.card_insert_of_notMem kn] at hle
  exact ⟨D,hao,by omega,hfun⟩

end PEqualNP.Outside.L_meta_3568.Reader
