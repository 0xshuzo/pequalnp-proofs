import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8117
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
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

abbrev V := Fin 42
lemma lastWire {α : Type} (l : List α) (a d : α) : (l++[a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]
def ListImp (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma listImp_append {l r : List Bool} {a b : Bool} (h : ListImp l r)
    (hab : a = true → b = true) : ListImp (l ++ [a]) (r ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  rcases Nat.lt_trichotomy i l.length with hi | rfl | hi
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by rwa [← h.1])]
    exact h.2 i
  · rw [lastWire, h.1, lastWire]
    exact hab
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

lemma stepImp {g : Gate} {l r : List Bool} (hop : g.op = .and ∨ g.op = .or)
    (h : ListImp l r) : ListImp (stepWire l g) (stepWire r g) := by
  apply listImp_append h
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun ha i hi => h.2 i (ha i hi)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, h.2 i hv⟩

lemma runImp (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {l r : List Bool} (h : ListImp l r) : ListImp (gs.foldl stepWire l) (gs.foldl stepWire r) := by
  induction gs generalizing l r with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun q hq => hg q (List.mem_cons_of_mem _ hq)) (stepImp (hg g (by simp)) h)

lemma wire_mono {C : Circuit} (hm : Monotone2 C) {x y : V → Bool}
    (hxy : ∀ i, x i = true → y i = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn y)).getD i false = true := by
  have hh : ListImp (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, fun j => ?_⟩
    by_cases hj : j < 42
    · rw [List.getD_eq_getElem _ _ (by simpa using hj),
        List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn, List.getElem_ofFn]
      exact hxy ⟨j, hj⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp
  exact (runImp C.gates (fun g hg => by simpa using (hm g hg).1) hh).2 i

def direct (u v : V) : Prop :=
  u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ [0, 5, 7, 17, 20]

def flag (a b : V) (i : V) := decide (i=a ∨ i=b)
def one (v : V) (i : V) := decide (i=v)
def maximal (x : V → Bool) := ∀ u, x u=true ↔ ∀ w, x w=true → ¬(direct u w ∨ direct w u)
def spec (C : Circuit) :=
  Monotone2 C ∧ (∀ u v, direct u v → C.eval (List.ofFn (flag u v))=true) ∧
  ∀ x, maximal x → C.eval (List.ofFn x)=false
def least (C : Circuit) := ∀ A, spec A → C.size ≤ A.size

lemma typed {C : Circuit} (h : spec C) (k : ℕ) (hk : k<C.gates.length) :
    (gateAt C k).op = .and ∨ (gateAt C k).op = .or := by
  simpa using (h.1 _ (gateAt_mem hk)).1

lemma proper_bypass {C : Circuit} (h : spec C) (r i : ℕ) : Monotone2 (bypass 42 C r i) := by
  intro g hg
  obtain ⟨q,hq,eq,le⟩ := bypass_mem g hg
  simpa only [eq,le] using h.1 q hq

lemma cheaper {C : Circuit} (small : least C) {r i : ℕ} (hr : r < C.gates.length) :
    ¬spec (bypass 42 C r i) := by
  intro good
  have h := small _ good
  change C.gates.length ≤ (bypass 42 C r i).gates.length at h
  rw [bypass_length] at h
  omega

lemma rawVal (C : Circuit) (x : V → Bool) (v : V) : val C (List.ofFn x) v.val = x v := by
  rw [val_input (n:=42) List.length_ofFn v.isLt]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma carrier {C : Circuit} {r : ℕ} {v : V} (h : spec C)
    (lit : val C (List.ofFn (one v)) (42+r) = true) (x : V → Bool) (hv : x v=true) :
    val C (List.ofFn x) (42+r)=true := by
  apply wire_mono h.1 (x:=one v) (y:=x) _ _ lit
  intro i hi
  have e : i=v := of_decide_eq_true hi
  simpa [e] using hv

abbrev graph : SimpleGraph V where
  Adj u v := direct u v ∨ direct v u
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun u h => by
    rcases h with h | h <;> have := h.1 <;> have := h.2.1 <;> omega⟩

def hasEdge (x : V → Bool) : Prop :=
  ∃ u v, graph.Adj u v ∧ x u = true ∧ x v = true

lemma maxIndependent (x : V → Bool) (hx : ¬ hasEdge x) :
    ∃ y : V → Bool, (∀ u, x u = true → y u = true) ∧
      ∀ u, y u = true ↔ ∀ v, y v = true → ¬graph.Adj u v := by
  classical
  let independent : Set V → Prop := fun s =>
    ∀ ⦃u v⦄, u ∈ s → v ∈ s → ¬graph.Adj u v
  have hs : independent {u | x u = true} := fun {_ _} hu hv huv => hx ⟨_, _, huv, hu, hv⟩
  obtain ⟨t, hst, ht, hmax⟩ := Finite.exists_le_maximal hs
  refine ⟨fun u => decide (u ∈ t), ?_, ?_⟩
  · intro u hu
    exact decide_eq_true (hst hu)
  · intro u
    simp only [decide_eq_true_eq]
    refine ⟨fun hu v hv => ht hu hv, ?_⟩
    intro h
    have hi : independent (insert u t) := by
      intro a b ha hb hab
      have ha' : a = u ∨ a ∈ t := Set.mem_insert_iff.mp ha
      have hb' : b = u ∨ b ∈ t := Set.mem_insert_iff.mp hb
      rcases ha' with rfl | ha' <;> rcases hb' with rfl | hb'
      · exact graph.irrefl hab
      · exact h _ hb' hab
      · exact h _ ha' hab.symm
      · exact ht ha' hb' hab
    exact hmax hi (Set.subset_insert _ _) (Set.mem_insert _ _)

namespace Move
abbrev V := Fin 42
abbrev inc (a b : V) : Prop :=
  a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
def adj (a b : V) : Bool := decide (inc a b ∨ inc b a)
def gen (g : Fin 2) (i : V) : V :=
  if g = 0 then Fin.ofNat 42 ((i.val / 21) * 21 + (i.val + 1) % 21)
  else Fin.ofNat 42 ((if i.val < 21 then 21 else 0) + (21 - i.val % 21) % 21)

-- Send the first member of an ordered pair to point zero.
def normal (i : V) : List (Fin 2) :=
  if i.val < 21 then List.replicate ((21 - i.val) % 21) 0
  else 1 :: List.replicate (i.val - 21) 0

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
theorem chainSurj (gs : List (Fin 2)) : Function.Surjective (chain gs) := by
  induction gs with
  | nil => exact fun a => ⟨a,rfl⟩
  | cons g gs ih => exact ih.comp (genSurj g)

theorem chainAdj (gs : List (Fin 2)) (a b : V) : adj (chain gs a) (chain gs b)=adj a b := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih => exact (ih (gen g a) (gen g b)).trans (genAdj g a b)

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


end Move
lemma read_spec {C : Circuit} (hm : Monotone2 C) :
    spec C ↔ ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ Move.yes x := by
  constructor
  · intro hc x
    constructor
    · intro on
      by_contra no
      have ind : ¬hasEdge x := by
        rintro ⟨a,b,ab,xa,xb⟩
        rcases ab with ab|ba
        · exact no ⟨a,b,ab,xa,xb⟩
        · exact no ⟨b,a,ba,xb,xa⟩
      obtain ⟨y,xy,mxy⟩ := maxIndependent x ind
      have good := wire_mono hm xy C.output on
      change C.eval (List.ofFn y)=true at good
      rw [hc.2.2 y mxy] at good
      contradiction
    · rintro ⟨a,b,ab,xa,xb⟩
      apply wire_mono hm (x:=flag a b) (y:=x) _ C.output (hc.2.1 a b ab)
      intro i hi
      rcases (of_decide_eq_true hi : i=a ∨ i=b) with rfl|rfl <;> assumption
  · intro ok
    refine ⟨hm,fun a b hab => (ok _).2 ⟨a,b,hab,?_,?_⟩,?_⟩
    · simp [flag]
    · simp [flag]
    · intro x hx
      apply Bool.eq_false_iff.mpr
      intro on
      obtain ⟨a,b,hab,ha,hb⟩ := (ok x).1 on
      exact (hx a).1 ha b hb (Or.inl hab)

lemma named_output_high {C : Circuit} (h : spec C) : 42≤C.output := by
  by_contra! lo
  let v : V := ⟨C.output,lo⟩
  have on : C.eval (List.ofFn (one v))=true :=
    (rawVal C (one v) v).trans (by simp [one])
  obtain ⟨a,b,⟨hp,hl,_⟩,xa,xb⟩ := (((read_spec h.1).mp h) _).1 on
  have ea : a=v := of_decide_eq_true xa
  have eb : b=v := of_decide_eq_true xb
  rw [ea] at hp
  rw [eb] at hl
  omega

def marked (C : Circuit) (x : V→Bool) := ∃ k g, C.gates[k]?=some g ∧ g.op=.and ∧
    val C (List.ofFn x) (42+k)=true

theorem moveToZero {C : Circuit} (h : spec C) (v : V) (hot : marked C (one v)) :
    ∃ D : Circuit, spec D ∧ D.size=C.size ∧ marked D (one 0) := by
  obtain ⟨k,g,get,op,on⟩ := hot
  let e := Move.chain (Move.normal v)
  let D := Move.changeC e C
  have mono : Monotone2 D := by
    intro t ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    simpa [Move.changeGate] using h.1 s hs
  have ds : D.size=C.size := by simp [D,Move.changeC,Circuit.size]
  refine ⟨D,(read_spec mono).mpr ?_,ds,k,Move.changeGate e g,?_,op,?_⟩
  · intro x
    have eq : D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ e)) := Move.lookup_change e C x C.output
    rw [eq,((read_spec h.1).mp h),Move.yes_move e (Move.chainSurj _) (Move.chainAdj _)]
  · simp [D,Move.changeC,List.getElem?_map,get]
  · have grows : val C (List.ofFn ((one 0) ∘ e)) (42+k)=true := by
      apply wire_mono h.1 (x:=one v) (y:=(one 0) ∘ e) _ _ on
      intro i hi
      have ev : i=v := of_decide_eq_true hi
      change decide (e i=(0:V))=true
      rw [ev]
      exact decide_eq_true (Move.normalOK v)
    have eq := Move.lookup_change e C (one 0) (42+k)
    simp only [Move.idx,dite_eq_right (show ¬42+k<42 by omega)] at eq
    exact eq.trans grows

def ZeroLaw := ∀ C : Circuit, spec C → C.size≤124 → least C → ¬ marked C (one 0)
theorem zero_equiv : (have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ (∀ (x3 x4 : Fin (42 : ℕ)), x1 x3 x4 → x2.eval (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (x6 = x3 ∨ x6 = x4)) = Bool.true) ∧ ∀ (x3 : Fin (42 : ℕ) → Bool), (∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.true ↔ ∀ (x5 : Fin (42 : ℕ)), x3 x5 = Bool.true → ¬(x1 x4 x5 ∨ x1 x5 x4)) → x2.eval (List.ofFn x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → x3.size ≤ (124 : ℕ) → (∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 → x3.size ≤ x6.size) → (∃ (x7 : Fin (42 : ℕ)) (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x8]? = Option.some x9 ∧ x9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x10 : Fin (42 : ℕ)) => Decidable.decide (x10 = x7))).getD ((42 : ℕ) + x8) Bool.false = Bool.true) → False) ↔ ZeroLaw := by
  constructor
  · intro law C h size sm hot
    obtain ⟨k,g,get,op,on⟩:=hot
    exact law C h size sm ⟨0,k,g,get,op,on⟩
  · intro law
    dsimp only
    intro C h size sm bad
    obtain ⟨v,k,g,get,op,on⟩:=bad
    obtain ⟨D,dh,ds,hot⟩ := moveToZero h v ⟨k,g,get,op,on⟩
    exact law D dh (ds.le.trans size) (fun A ag=>ds.le.trans (sm A ag)) hot

theorem shore_implies : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (42 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (1 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) → (have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ (∀ (x3 x4 : Fin (42 : ℕ)), x1 x3 x4 → x2.eval (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (x6 = x3 ∨ x6 = x4)) = Bool.true) ∧ ∀ (x3 : Fin (42 : ℕ) → Bool), (∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.true ↔ ∀ (x5 : Fin (42 : ℕ)), x3 x5 = Bool.true → ¬(x1 x4 x5 ∨ x1 x5 x4)) → x2.eval (List.ofFn x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → x3.size ≤ (124 : ℕ) → (∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 → x3.size ≤ x6.size) → (∃ (x7 : Fin (42 : ℕ)) (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x8]? = Option.some x9 ∧ x9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x10 : Fin (42 : ℕ)) => Decidable.decide (x10 = x7))).getD ((42 : ℕ) + x8) Bool.false = Bool.true) → False) := by
  intro law
  apply zero_equiv.mpr
  intro C h size _ bad
  obtain ⟨k,g,get,op,on⟩:=bad
  have hot : val C (List.ofFn (flag 0 1)) (42+k)=true := by
    apply wire_mono h.1 (x:=one 0) (y:=flag 0 1) _ _ on
    intro i hi
    exact decide_eq_true (Or.inl (of_decide_eq_true hi))
  exact law C (named_output_high h) h.1 size ((read_spec h.1).mp h) ⟨k,g,get,op,hot⟩

end PEqualNP.Outside.L_meta_8117
