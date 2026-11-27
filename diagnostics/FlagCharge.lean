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

/-- A singleton-positive wire in a physical optimum is pivotal away from the singleton. -/
theorem criticalFlag {C : Circuit} {r : ℕ} {v : V} (h : spec C) (small : least C)
    (hr : r < C.gates.length) (lit : val C (List.ofFn (one v)) (42+r)=true) :
    ∃ a b : V, direct a b ∧ v≠a ∧ v≠b ∧
      val C (List.ofFn (flag a b)) (42+r)=true ∧
      (bypass 42 C r v.val).eval (List.ofFn (flag a b))=false := by
  let A := bypass 42 C r v.val
  have earlier : v.val<42+r := by have := v.isLt; omega
  have rev : OpMono (fun a b => b=true → a=true) :=
    fun op ho l f g h => opMono_imp op ho l g f h
  have down (x : V → Bool) : A.eval (List.ofFn x)=true → C.eval (List.ofFn x)=true := by
    apply bypass_eval_rel (fun _ h=>h) rev List.length_ofFn (typed h) hr (Or.inl earlier)
    rw [rawVal]
    exact carrier h lit x
  have bad : ∃ a b, direct a b ∧ A.eval (List.ofFn (flag a b))=false := by
    by_contra! no
    apply cheaper small (i:=v.val) hr
    refine ⟨proper_bypass h _ _,?_,?_⟩
    · intro a b hab
      cases e : A.eval (List.ofFn (flag a b)) <;> simp_all
    · intro x hx
      apply Bool.eq_false_iff.mpr
      intro on
      have orig := down x on
      rw [h.2.2 x hx] at orig
      contradiction
  obtain ⟨a,b,hab,fail⟩ := bad
  have diff : val C (List.ofFn (flag a b)) (42+r) ≠ flag a b v := by
    intro eq
    have old := h.2.1 a b hab
    have rr := bypass_eval_eq (C:=C) (n:=42) (x:=List.ofFn (flag a b))
      List.length_ofFn (typed h) hr (Or.inl earlier) (eq.trans (rawVal C _ v).symm)
    change A.eval (List.ofFn (flag a b)) = _ at rr
    rw [fail,old] at rr
    contradiction
  have off : flag a b v = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    exact diff ((carrier h lit _ hv).trans hv.symm)
  have on : val C (List.ofFn (flag a b)) (42+r)=true := by
    cases eq : val C (List.ofFn (flag a b)) (42+r) <;> simp_all
  have ne : ¬(v=a ∨ v=b) := by simpa [flag] using off
  exact ⟨a,b,hab,fun e=>ne (Or.inl e),fun e=>ne (Or.inr e),on,fail⟩

namespace Restore
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl


lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_two_new {m : ℕ} (gs : List Gate) (a b c : ℕ) (x : Fin m → Bool)
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    val (gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [c, m + gs.length]⟩]) x (m + gs.length + 1)
      = (val gs x c || (val gs x a && val gs x b)) := by
  have happ : gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate), ⟨GateOp.or, [c, m + gs.length]⟩]
      = (gs ++ [⟨GateOp.and, [a, b]⟩]) ++ [⟨GateOp.or, [c, m + gs.length]⟩] := by simp
  have hl1 : (gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length = gs.length + 1 := by simp
  rw [happ, val_snoc, if_pos (by omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false]
  rw [val_snoc, if_neg (by omega), val_snoc, if_pos rfl]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true]


def addFlag (K : Circuit) (e : V×V) : Circuit :=
  ⟨K.gates ++ [⟨.and,[e.1.val,e.2.val]⟩,⟨.or,[K.output,42+K.gates.length]⟩], 42+K.gates.length+1⟩

lemma add_eval (K : Circuit) (e : V×V) (hk : K.output<42+K.gates.length) (x : V→Bool) :
    (addFlag K e).eval (List.ofFn x)=(K.eval (List.ofFn x) || (x e.1 && x e.2)) := by
  have ha := e.1.isLt
  have hb := e.2.isLt
  have eq:=val_two_new K.gates e.1.val e.2.val K.output x (by omega) (by omega) hk
  rw [val_lt _ _ _ ha,val_lt _ _ _ hb] at eq
  exact eq

lemma add_mono {K : Circuit} (e : V×V) (hK : Monotone2 K) : Monotone2 (addFlag K e) := by
  intro g hg
  change g ∈ K.gates ++ [_,_] at hg
  rcases List.mem_append.mp hg with old | extra
  · exact hK _ old
  · have cases' : g=⟨.and,[e.1.val,e.2.val]⟩ ∨ g=⟨.or,[K.output,42+K.gates.length]⟩ := by
      simpa using extra
    rcases cases' with rfl|rfl <;> simp

def repair (K : Circuit) : List (V×V) → Circuit
  | [] => K
  | e::es => repair (addFlag K e) es

lemma audit (K : Circuit) (es : List (V×V)) (hk : K.output<42+K.gates.length) (mono : Monotone2 K) :
    (repair K es).size=K.size + 2*es.length ∧ Monotone2 (repair K es) ∧
      ∀ x : V→Bool, (repair K es).eval (List.ofFn x)=true ↔
        K.eval (List.ofFn x)=true ∨ ∃ e∈es,x e.1=true ∧ x e.2=true := by
  induction es generalizing K with
  | nil => simp [repair,mono]
  | cons e es ih =>
    have valid : (addFlag K e).output<42+(addFlag K e).gates.length := by
      simp [addFlag]
    obtain ⟨sz,hm,ev⟩:=ih (addFlag K e) valid (add_mono e mono)
    refine ⟨?_,hm,?_⟩
    · change (repair (addFlag K e) es).size=_
      rw [sz]
      simp [addFlag,Circuit.size,List.length_cons]
      <;> omega
    · intro x
      change (repair (addFlag K e) es).eval _=true ↔ _
      rw [ev,add_eval K e hk]
      simp only [Bool.or_eq_true,Bool.and_eq_true,List.mem_cons]
      grind

/-- Missing flags can pay for only two gates each, regardless of fanout beyond the cut.
    A single lost flag therefore rules out a three-gate saving on the rest of the network. -/
theorem repair_charge {C A : Circuit} (small : least C) (ok : Monotone2 A)
    (hA : A.output < 42+A.gates.length) (lost : List (V×V))
    (legal : ∀ e∈lost,direct e.1 e.2)
    (survive : ∀ a b, direct a b → A.eval (List.ofFn (flag a b))=true ∨ (a,b)∈lost)
    (noBad : ∀ x, maximal x → A.eval (List.ofFn x)=false) :
    C.size ≤ A.size + 2*lost.length := by
  obtain ⟨sz,hm,ev⟩ := audit A lost hA ok
  rw [←sz]
  apply small
  refine ⟨hm,?_,?_⟩
  · intro a b hab
    rcases survive a b hab with was | repaired
    · exact (ev _).2 (Or.inl was)
    · exact (ev _).2 (Or.inr ⟨(a,b),repaired,by simp [flag],by simp [flag]⟩)
  · intro x hx
    apply Bool.eq_false_iff.mpr
    intro hot
    rcases (ev x).1 hot with old | ⟨e,he,hp,hl⟩
    · rw [noBad x hx] at old
      contradiction
    · exact (hx e.1).1 hp e.2 hl (Or.inl (legal e he))
end Restore
end PEqualNP.Outside.L_meta_8117
