import PEqualNP.Defs

-- Wire bypass lemmas from the published L_meta_1485.
namespace PEqualNP.Outside.L_meta_20412.Pin

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

open PEqualNP.MetaComplexity

lemma reader_alias (op : GateOp) (xs : List Nat) (b j : Nat) (hj : j < b)
    (hm : op = .and ∨ op = .or) (len : xs.length ≤ 2) (mem : j ∈ xs) :
    ∃ k < b, ∀ v : Nat → Bool, v j = false →
      op.eval (xs.map fun t => if t<b then v t else false) = v k := by
  have shapes : xs=[j] ∨ ∃ t, xs=[j,t] ∨ xs=[t,j] := by
    cases xs with
    | nil => simp at mem
    | cons a tail =>
      cases tail with
      | nil =>
        have e : j=a := by simpa using mem
        exact Or.inl (by rw [e])
      | cons c rest =>
        cases rest with
        | nil =>
          simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
          rcases mem with rfl|rfl
          · exact Or.inr ⟨c,Or.inl rfl⟩
          · exact Or.inr ⟨a,Or.inr rfl⟩
        | cons z rest => simp only [List.length_cons] at len; omega
  rcases shapes with rfl|⟨t,ht⟩
  · refine ⟨j,hj,?_⟩
    intro v hv
    rcases hm with rfl|rfl <;> simp [GateOp.eval,hj,hv]
  · rcases hm with rfl|rfl
    · refine ⟨j,hj,?_⟩
      intro v hv
      rcases ht with rfl|rfl <;> simp [GateOp.eval,hj,hv]
    · by_cases h : t < b
      · refine ⟨t,h,?_⟩
        intro v hv
        rcases ht with rfl|rfl <;> simp [GateOp.eval,h,hj,hv]
      · refine ⟨j,hj,?_⟩
        intro v hv
        rcases ht with rfl|rfl <;> simp [GateOp.eval,h,hj,hv]

theorem deleteReader {n j r : Nat} {C : Circuit} (hC : Monotone2 C) (hj : j<n)
    (hr : r<C.gates.length) (hm : j ∈ (gateAt C r).inputs) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+1=C.size ∧
      ∀ x : List Bool, x.length=n → x.getD j false=false → D.eval x=C.eval x := by
  have ops (k : Nat) (hk : k<C.gates.length) :
      (gateAt C k).op=.and ∨ (gateAt C k).op=.or := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC _ (gateAt_mem hk)).1
  obtain ⟨k,hk,halias⟩ := reader_alias _ _ (n+r) j (by omega) (ops r hr)
    (hC _ (gateAt_mem hr)).2 hm
  refine ⟨bypass n C r k,?_,?_,?_⟩
  · intro g hg
    obtain ⟨g',hg',hop,hlen⟩ := bypass_mem hg
    rw [hop,hlen]
    exact hC g' hg'
  · change (bypass n C r k).gates.length+1=C.gates.length
    rw [bypass_length]; omega
  · intro x hx hfalse
    apply bypass_eval_eq hx ops hr (Or.inl hk)
    rw [val_gate hx hr]
    exact halias (val C x) (by rw [val_input hx hj,hfalse])

end PEqualNP.Outside.L_meta_20412.Pin


namespace PEqualNP.Outside.L_meta_20412.Shrink

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def route (n m : Nat) (π : Nat → Nat) (wire : Nat) : Nat :=
  if wire<n then π wire else wire-n+m

def replace (n m : Nat) (π : Nat → Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (route n m π)⟩

def Rel (n m : Nat) (π : Nat → Nat) (a b : List Bool) : Prop :=
  n ≤ a.length ∧ b.length+n=a.length+m ∧ ∀ t, b.getD (route n m π t) false=a.getD t false

theorem step_rel {n m S : Nat} {π : Nat → Nat} (valid : ∀ i<n, π i<m ∨ π i=S)
    {a b : List Bool} (rel : Rel n m π a b) (bound : b.length < S) (g : Gate) :
    Rel n m π (step a g) (step b (replace n m π g)) := by
  obtain ⟨ha,hb,hh⟩ := rel
  have hv : (replace n m π g).op.eval ((replace n m π g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [replace,List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hh i
  refine ⟨by simp [step]; omega,by simp [step]; omega,?_⟩
  intro t
  simp only [step,hv]
  rcases Nat.lt_trichotomy t a.length with h|h|h
  · rw [List.getD_append _ _ _ _ h]
    have loc : route n m π t < b.length ∨ route n m π t = S := by
      by_cases small : t<n
      · rw [route,if_pos small]
        rcases valid t small with hv|hv
        · exact Or.inl (by omega)
        · exact Or.inr hv
      · exact Or.inl (by simp [route,small]; omega)
    rcases loc with l|l
    · rw [List.getD_append _ _ _ _ l]; exact hh t
    · have k := hh t
      rw [l,List.getD_eq_default _ _ (by omega)] at k
      rw [l,List.getD_eq_default _ _ (by simp; omega)]
      exact k
  · have loc : route n m π t = b.length := by
      rw [route,if_neg (by omega)]; omega
    rw [loc,h]
    simp
  · have loc : b.length+1 ≤ route n m π t := by
      rw [route,if_neg (by omega)]; omega
    rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

theorem fold_rel {n m S : Nat} {π : Nat → Nat} (valid : ∀ i<n, π i<m ∨ π i=S) (gs : List Gate) :
    ∀ (a b : List Bool), Rel n m π a b → b.length+gs.length≤S →
      Rel n m π (gs.foldl step a) ((gs.map (replace n m π)).foldl step b) := by
  induction gs with
  | nil => intro a b h _; exact h
  | cons g gs ih =>
    intro a b h bound
    simp only [List.length_cons] at bound
    apply ih
    · exact step_rel valid h (by omega) g
    · simp [step]; omega

def reduced (n m : Nat) (π : Nat → Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (replace n m π),route n m π C.output⟩

theorem cost (n m : Nat) (π : Nat → Nat) (C : Circuit) : (reduced n m π C).size = C.size := by
  simp [Circuit.size,reduced]

theorem mono (n m : Nat) (π : Nat → Nat) {C : Circuit} (hm : Monotone2 C) :
    Monotone2 (reduced n m π C) := by
  intro g hg
  change g ∈ C.gates.map (replace n m π) at hg
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hg
  simpa [replace] using hm old ho

theorem evaluation {n m S : Nat} (π : Nat → Nat) (valid : ∀ i<n, π i<m ∨ π i=S)
    (C : Circuit) (cover : m+C.gates.length ≤ S) (a b : List Bool)
    (la : a.length=n) (lb : b.length=m)
    (hr : ∀ i<n, a.getD i false = b.getD (π i) false) :
    (reduced n m π C).eval b = C.eval a := by
  have r : Rel n m π a b := by
    refine ⟨by omega,by omega,?_⟩
    intro t
    by_cases h : t<n
    · simpa [route,h] using (hr t h).symm
    · rw [route,if_neg h,List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
  exact (fold_rel valid C.gates a b r (by omega)).2.2 C.output

def columns : Fin 3 → Fin 4 := ![0,1,3]
def fixedMap (s i : Nat) : Nat := if i<5 then i else if i=5 then s else i-1

theorem removeColumn {C : Circuit} (mc : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size=C.size ∧ ∀ (u v : Fin 3),
      D.eval (oneEach u v)=C.eval (oneEach u (columns v)) := by
  let S := 6+C.gates.length
  refine ⟨reduced 7 6 (fixedMap S) C,mono _ _ _ mc,cost _ _ _ C,?_⟩
  intro u v
  apply evaluation (S:=S) (π:=fixedMap S)
  · intro i hi; unfold fixedMap; split_ifs <;> omega
  · exact Nat.le_refl _
  · simp [oneEach]
  · simp [oneEach]
  · intro i hi
    have H : ∀ (u v : Fin 3) (i : Fin 7),
        (oneEach u (columns v)).getD i.val false =
        (oneEach u v).getD (fixedMap 6 i.val) false := by decide +kernel
    have a := H u v ⟨i,hi⟩
    simp only at a
    by_cases h : i=5
    · subst i
      have len : (oneEach u v).length=6 := by simp [oneEach]
      simpa [fixedMap,List.getD_eq_default _ _ (show (oneEach u v).length ≤ S by dsimp [S]; omega),
        List.getD_eq_default _ _ (show (oneEach u v).length ≤ 6 by omega)] using a
    · simpa [fixedMap,h] using a

end PEqualNP.Outside.L_meta_20412.Shrink


namespace PEqualNP.Outside.L_meta_20412.Contraction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open PEqualNP.Outside.L_meta_20412

def duplicate : Fin 4 → Fin 3 := ![0,1,1,2]

theorem contractReader {A : Fin 3 → Fin 3 → Bool} {C : Circuit} {r : Nat}
    (hm : Monotone2 C) (hr : r < C.gates.length) (used : 5 ∈ (gateAt C r).inputs)
    (works : Represents (fun u v => A u (duplicate v)) C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+1=C.size ∧ Represents A D := by
  obtain ⟨E,he,hcost,hpin⟩ := Pin.deleteReader (n:=7) hm (j:=5) (by decide) hr used
  obtain ⟨D,hd,dcost,hmove⟩ := Shrink.removeColumn he
  refine ⟨D,hd,by omega,?_⟩
  intro u v
  have zero : ∀ u v : Fin 3, (oneEach u (Shrink.columns v)).getD 5 false=false := by decide +kernel
  have proj : ∀ v : Fin 3, duplicate (Shrink.columns v)=v := by decide +kernel
  rw [hmove, hpin _ (by simp [oneEach]) (zero u v), works, proj]

end PEqualNP.Outside.L_meta_20412.Contraction

namespace PEqualNP.Outside.L_meta_20412.Contraction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open PEqualNP.Outside.L_meta_20412.Pin

theorem reader_of_order {C : Circuit} (hm : Monotone2 C) {n j : Nat} {x y : List Bool}
    (hx : x.length=n) (hy : y.length=n)
    (hxy : ∀ t, t≠j → x.getD t false=true → y.getD t false=true)
    (ho : C.output≠j) (px : C.eval x=true) (ny : C.eval y=false) :
    ∃ r, r<C.gates.length ∧ j ∈ (gateAt C r).inputs := by
  by_contra! none
  have order : ∀ i, i≠j → val C x i=true → val C y i=true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro ne good
      by_cases raw : i<n
      · rw [val_input hx raw] at good
        rw [val_input hy raw]
        exact hxy i ne good
      by_cases past : n+C.gates.length≤i
      · rw [val_ge hx past] at good; contradiction
      let k:=i-n
      have eq : i=n+k := by dsimp [k]; omega
      have hk : k<C.gates.length := by dsimp [k]; omega
      have ops : (gateAt C k).op=.and ∨ (gateAt C k).op=.or := by
        simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (hm _ (gateAt_mem hk)).1
      rw [eq,val_gate hx hk] at good
      rw [eq,val_gate hy hk]
      apply opMono_imp _ ops _ _ _ ?_ good
      intro t used
      by_cases lt : t<n+k
      · rw [if_pos lt,if_pos lt]
        apply ih t (by omega)
        intro hj
        exact none k hk (hj ▸ used)
      · simp [lt]
  have bad := order C.output ho px
  change C.eval y=true at bad
  rw [ny] at bad
  contradiction

theorem contractMixed {A : Fin 3 → Fin 3 → Bool} {C : Circuit}
    (hm : Monotone2 C) (works : Represents (fun u v => A u (duplicate v)) C)
    (mixed : ∃ u d, A u 1=true ∧ A u d=false) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+1=C.size ∧ Represents A D := by
  obtain ⟨u,d,hp,hn⟩ := mixed
  have eqcol : ∀ d : Fin 3, duplicate (Shrink.columns d)=d := by decide +kernel
  have p2 : C.eval (oneEach u (2 : Fin 4))=true := (works u 2).trans hp
  have p1 : C.eval (oneEach u (1 : Fin 4))=true := (works u 1).trans hp
  have neg : C.eval (oneEach u (Shrink.columns d))=false := by rw [works,eqcol,hn]
  have output : C.output≠5 := by
    intro h
    rw [eval_eq_val,h,val_input (n:=7) (by simp [oneEach]) (by decide)] at p1
    have H : ∀ v : Fin 3, (oneEach v (1 : Fin 4)).getD 5 false=false := by decide +kernel
    rw [H] at p1
    contradiction
  have cmp : ∀ t, t≠5 → (oneEach u (2 : Fin 4)).getD t false=true →
      (oneEach u (Shrink.columns d)).getD t false=true := by
    intro t ht
    by_cases lt : t<7
    · have F : ∀ (a d : Fin 3) (i : Fin 7), i.val≠5 →
          (oneEach a (2 : Fin 4)).getD i.val false=true →
          (oneEach a (Shrink.columns d)).getD i.val false=true := by decide +kernel
      exact F u d ⟨t,lt⟩ ht
    · rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      simp
  obtain ⟨r,hr,read⟩ := reader_of_order hm (n:=7) (by simp [oneEach]) (by simp [oneEach])
    cmp output p2 neg
  exact contractReader hm hr read works

end PEqualNP.Outside.L_meta_20412.Contraction
