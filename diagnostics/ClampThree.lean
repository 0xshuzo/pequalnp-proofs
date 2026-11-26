import PEqualNP.Defs
namespace Research5962.Clamp
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 1500000
def rstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runG (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl rstep x

lemma runG_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    runG (gs ++ [g]) x = runG gs x ++ [g.op.eval (g.inputs.map fun i => (runG gs x).getD i false)] := by
  simp [runG, rstep, List.foldl_append]

lemma runG_length (gs : List Gate) (x : List Bool) : (runG gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runG]
  | append_singleton gs g ih => rw [runG_snoc]; simp [ih]; omega

lemma getD_snoc_lt (l : List Bool) (b : Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma runG_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (runG (gs ++ hs) x).getD i false = (runG gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, runG_snoc, getD_snoc_lt _ _ _ (by rw [runG_length, List.length_append]; omega), ih]

lemma runG_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (runG gs x).getD i false = x.getD i false := by
  have := runG_prefix [] gs x i (by simpa using hi)
  simpa [runG] using this

def rval (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

lemma rval_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rval (runG (hs ++ e) y) r = rval (runG hs y) r := by
  rcases r with b | t
  · rfl
  · exact runG_prefix _ _ _ _ (h t rfl)

lemma emit_ao (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (r s : Bool ⊕ ℕ) (hr : ∀ t, r = .inr t → t < 14 + hs.length) (hs' : ∀ t, s = .inr t → t < 14 + hs.length) :
    ∃ (res : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧
      (∀ g ∈ e, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ t, res = .inr t → t < 14 + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = 14 →
        rval (runG (hs ++ e) y) res = op.eval [rval (runG hs y) r, rval (runG hs y) s] := by
  have keep : ∀ res : Bool ⊕ ℕ, (∀ t, res = .inr t → t < 14 + hs.length) →
      (∀ y : List Bool, y.length = 14 → rval (runG hs y) res = op.eval [rval (runG hs y) r, rval (runG hs y) s]) →
      ∃ (res : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧
        (∀ g ∈ e, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        (∀ t, res = .inr t → t < 14 + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = 14 →
          rval (runG (hs ++ e) y) res = op.eval [rval (runG hs y) r, rval (runG hs y) s] := by
    intro res h1 h2
    exact ⟨res, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ y : List Bool, y.length = 14 →
        g.op.eval (g.inputs.map fun i => (runG hs y).getD i false) = op.eval [rval (runG hs y) r, rval (runG hs y) s]) →
      ∃ (res : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧
        (∀ g ∈ e, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        (∀ t, res = .inr t → t < 14 + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = 14 →
          rval (runG (hs ++ e) y) res = op.eval [rval (runG hs y) r, rval (runG hs y) s] := by
    intro g h1 h2
    refine ⟨.inr (14 + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
    · intro t ht; cases ht; simp
    · have : 14 + hs.length = (runG hs y).length := by rw [runG_length, hy]
      simp only [rval]
      rw [runG_snoc, this, getD_snoc_at]
      exact h2 y hy
  rcases hop with rfl | rfl
  · rcases r with b | t
    · cases b
      · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rval])
      · exact keep s hs' (by intro y _; simp [GateOp.eval, rval])
    · rcases s with b | q
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rval])
        · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rval])
      · exact add ⟨GateOp.and, [t, q]⟩ ⟨Or.inl rfl, by simp⟩ (by intro y _; simp [GateOp.eval, rval])
  · rcases r with b | t
    · cases b
      · exact keep s hs' (by intro y _; simp [GateOp.eval, rval])
      · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rval])
    · rcases s with b | q
      · cases b
        · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rval])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rval])
      · exact add ⟨GateOp.or, [t, q]⟩ ⟨Or.inr rfl, by simp⟩ (by intro y _; simp [GateOp.eval, rval])

def patchRun (C : Circuit) (j0 : ℕ) (f0 : (Fin 14 → Bool) → Bool) (x : Fin 14 → Bool) : ℕ → List Bool
  | 0 => List.ofFn x
  | k + 1 =>
    let w := patchRun C j0 f0 x k
    w ++ [if k = j0 then f0 x else
      match C.gates[k]? with
      | some g => g.op.eval (g.inputs.map fun i => w.getD i false)
      | none => false]

lemma patchRun_len (C : Circuit) (j0 : ℕ) (f0 : (Fin 14 → Bool) → Bool) (x : Fin 14 → Bool) (k : ℕ) :
    (patchRun C j0 f0 x k).length = 14 + k := by
  induction k with
  | zero => simp [patchRun]
  | succ k ih => simp [patchRun, ih]; omega

lemma patchRun_prefix (C : Circuit) (j0 : ℕ) (f0 : (Fin 14 → Bool) → Bool) (x : Fin 14 → Bool)
    (k1 k2 : ℕ) (hle : k1 ≤ k2) (i : ℕ) (hi : i < 14 + k1) :
    (patchRun C j0 f0 x k2).getD i false = (patchRun C j0 f0 x k1).getD i false := by
  induction k2 with
  | zero =>
    have : k1 = 0 := by omega
    subst this; rfl
  | succ k2 ih =>
    by_cases h : k1 ≤ k2
    · rw [patchRun, getD_snoc_lt _ _ _ (by rw [patchRun_len]; omega), ih h]
    · have : k1 = k2 + 1 := by omega
      subst this; rfl

lemma patchRun_eq_orig (C : Circuit) (j0 : ℕ) (f0 : (Fin 14 → Bool) → Bool)
    (hshape : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j)
    (x : Fin 14 → Bool)
    (heq : f0 x = (runG C.gates (List.ofFn x)).getD (14 + j0) false) :
    ∀ k ≤ C.gates.length, ∀ i < 14 + k,
      (patchRun C j0 f0 x k).getD i false = (runG (C.gates.take k) (List.ofFn x)).getD i false := by
  intro k
  induction k with
  | zero => intro _ i _; simp [patchRun, runG]
  | succ k ih =>
    intro hk i hi
    have hklt : k < C.gates.length := by omega
    have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := List.take_succ_eq_append_getElem hklt
    rw [patchRun, htake, runG_snoc]
    by_cases hilt : i < 14 + k
    · rw [getD_snoc_lt _ _ _ (by rw [patchRun_len]; omega),
          getD_snoc_lt _ _ _ (by rw [runG_length, List.length_ofFn, List.length_take]; omega)]
      exact ih (by omega) i hilt
    · have hie : i = 14 + k := by omega
      subst hie
      rw [← patchRun_len C j0 f0 x k, getD_snoc_at]
      have hlenR : (runG (C.gates.take k) (List.ofFn x)).length = 14 + k := by
        rw [runG_length, List.length_ofFn, List.length_take]; omega
      rw [patchRun_len, ← hlenR, getD_snoc_at]
      by_cases hkj : k = j0
      · subst hkj
        rw [if_pos rfl, heq]
        have hpref : (runG C.gates (List.ofFn x)).getD (14 + k) false =
            (runG (C.gates.take (k + 1)) (List.ofFn x)).getD (14 + k) false := by
          conv_lhs => rw [← List.take_append_drop (k + 1) C.gates]
          exact runG_prefix _ _ _ _ (by rw [List.length_ofFn, List.length_take]; omega)
        rw [hpref, htake, runG_snoc, ← hlenR, getD_snoc_at]
      · rw [if_neg hkj, List.getElem?_eq_getElem hklt]
        dsimp only
        obtain ⟨_, a, b, hab, _, ha, hb⟩ := hshape k C.gates[k] (List.getElem?_eq_getElem hklt)
        rw [hab]
        simp only [List.map_cons, List.map_nil, ih (by omega) a ha, ih (by omega) b hb]

lemma patchRun_le_orig (C : Circuit) (j0 : ℕ) (f0 : (Fin 14 → Bool) → Bool)
    (hshape : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j)
    (x : Fin 14 → Bool)
    (hf0 : f0 x = false) :
    ∀ k ≤ C.gates.length, ∀ i < 14 + k,
      (patchRun C j0 f0 x k).getD i false = true → (runG (C.gates.take k) (List.ofFn x)).getD i false = true := by
  intro k
  induction k with
  | zero => intro _ i _ h; simpa [patchRun, runG] using h
  | succ k ih =>
    intro hk i hi htrue
    have hklt : k < C.gates.length := by omega
    have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := List.take_succ_eq_append_getElem hklt
    rw [patchRun] at htrue
    rw [htake, runG_snoc]
    by_cases hilt : i < 14 + k
    · rw [getD_snoc_lt _ _ _ (by rw [patchRun_len]; omega)] at htrue
      rw [getD_snoc_lt _ _ _ (by rw [runG_length, List.length_ofFn, List.length_take]; omega)]
      exact ih (by omega) i hilt htrue
    · have hie : i = 14 + k := by omega
      subst hie
      rw [← patchRun_len C j0 f0 x k, getD_snoc_at] at htrue
      have hlenR : (runG (C.gates.take k) (List.ofFn x)).length = 14 + k := by
        rw [runG_length, List.length_ofFn, List.length_take]; omega
      rw [← hlenR, getD_snoc_at]
      by_cases hkj : k = j0
      · rw [if_pos hkj, hf0] at htrue; cases htrue
      · rw [if_neg hkj, List.getElem?_eq_getElem hklt] at htrue
        dsimp only at htrue
        obtain ⟨hop, a, b, hab, _, ha, hb⟩ := hshape k C.gates[k] (List.getElem?_eq_getElem hklt)
        rw [hab] at htrue ⊢
        rcases hop with hop | hop <;> rw [hop] at htrue ⊢
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true] at htrue ⊢
          exact ⟨ih (by omega) a ha htrue.1, ih (by omega) b hb htrue.2⟩
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true] at htrue ⊢
          exact htrue.elim (fun h1 => Or.inl (ih (by omega) a ha h1)) (fun h2 => Or.inr (ih (by omega) b hb h2))

lemma orig_le_patchRun (C : Circuit) (j0 : ℕ) (f0 : (Fin 14 → Bool) → Bool)
    (hshape : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j)
    (x : Fin 14 → Bool)
    (hf0 : f0 x = true) :
    ∀ k ≤ C.gates.length, ∀ i < 14 + k,
      (runG (C.gates.take k) (List.ofFn x)).getD i false = true → (patchRun C j0 f0 x k).getD i false = true := by
  intro k
  induction k with
  | zero => intro _ i _ h; simpa [patchRun, runG] using h
  | succ k ih =>
    intro hk i hi htrue
    have hklt : k < C.gates.length := by omega
    have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := List.take_succ_eq_append_getElem hklt
    rw [htake, runG_snoc] at htrue
    rw [patchRun]
    by_cases hilt : i < 14 + k
    · rw [getD_snoc_lt _ _ _ (by rw [runG_length, List.length_ofFn, List.length_take]; omega)] at htrue
      rw [getD_snoc_lt _ _ _ (by rw [patchRun_len]; omega)]
      exact ih (by omega) i hilt htrue
    · have hie : i = 14 + k := by omega
      subst hie
      have hlenR : (runG (C.gates.take k) (List.ofFn x)).length = 14 + k := by
        rw [runG_length, List.length_ofFn, List.length_take]; omega
      rw [← hlenR, getD_snoc_at] at htrue
      rw [← patchRun_len C j0 f0 x k, getD_snoc_at]
      by_cases hkj : k = j0
      · rw [if_pos hkj, hf0]
      · rw [if_neg hkj, List.getElem?_eq_getElem hklt]
        dsimp only
        obtain ⟨hop, a, b, hab, _, ha, hb⟩ := hshape k C.gates[k] (List.getElem?_eq_getElem hklt)
        rw [hab] at htrue ⊢
        rcases hop with hop | hop <;> rw [hop] at htrue ⊢
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true] at htrue ⊢
          exact ⟨ih (by omega) a ha htrue.1, ih (by omega) b hb htrue.2⟩
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true] at htrue ⊢
          exact htrue.elim (fun h1 => Or.inl (ih (by omega) a ha h1)) (fun h2 => Or.inr (ih (by omega) b hb h2))

lemma emitZero (hs : List Gate) (op : GateOp) (h : op=.and ∨ op=.or)
    (r s : Bool ⊕ ℕ) (hr : ∀ t, r=.inr t → t<14+hs.length)
    (hs' : ∀ t, s=.inr t → t<14+hs.length) (pin : r=.inl false ∨ s=.inl false) :
    ∃ z : Bool ⊕ ℕ, (∀ t,z=.inr t → t<14+hs.length) ∧
      ∀ y : List Bool, y.length=14 → rval (runG hs y) z =
        op.eval [rval (runG hs y) r,rval (runG hs y) s] := by
  rcases h with rfl|rfl <;> rcases pin with rfl|rfl
  · exact ⟨.inl false,by simp,by simp [GateOp.eval,rval]⟩
  · exact ⟨.inl false,by simp,by simp [GateOp.eval,rval]⟩
  · exact ⟨s,hs',by simp [GateOp.eval,rval]⟩
  · exact ⟨r,hr,by simp [GateOp.eval,rval]⟩

lemma clamp_two (C : Circuit) (j0 j1 j2 : ℕ) (p01 : j0<j1) (p12 : j1<j2) (valid : j2<C.gates.length)
    (reads : ∀ k, k=j1 ∨ k=j2 → ∀ g, C.gates[k]?=some g → 14+j0 ∈ g.inputs)
    (hshape : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j)
    (hne : ∃ x y : Fin 14 → Bool,
      (patchRun C j0 (fun x => (false : Bool)) x C.gates.length).getD C.output false ≠
      (patchRun C j0 (fun x => (false : Bool)) y C.gates.length).getD C.output false)
    (hout : C.output < 14 + C.gates.length) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size - 3 ∧
      ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) =
        (patchRun C j0 (fun x => (false : Bool)) x C.gates.length).getD C.output false := by
  let f0 : (Fin 14 → Bool) → Bool := fun x => (false : Bool)
  let saved (k : ℕ) := (if j0<k then 1 else 0) + (if j1<k then 1 else 0) + (if j2<k then 1 else 0)
  let cut (k : ℕ) := if k=j0 ∨ k=j1 ∨ k=j2 then 1 else 0
  have next (k : ℕ) : saved (k+1) = saved k + cut k := by
    simp only [saved,cut]
    split_ifs <;> omega
  have key : ∀ k ≤ C.gates.length, ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ),
      (∀ g ∈ hs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      hs.length + saved k ≤ k ∧
      (j0<k → m (14+j0) = .inl false) ∧
      (∀ w t, w < 14 + k → m w = .inr t → t < 14 + hs.length) ∧
      ∀ x : Fin 14 → Bool, ∀ w < 14 + k,
        (patchRun C j0 f0 x k).getD w false = rval (runG hs (List.ofFn x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => .inr w, by simp, by simp [saved], by simp, ?_, ?_⟩
      · intro w t hw ht; cases ht; simpa using hw
      · intro x w _; simp [patchRun, runG, rval]
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, stored, h3, h4⟩ := ih (by omega)
      have hklt : k < C.gates.length := by omega
      have finish : ∀ (res : Bool ⊕ ℕ) (e : List Gate),
          (∀ g ∈ e, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
          (∀ t, res = .inr t → t < 14 + hs.length + e.length) →
          (k=j0 → res = .inl false) → e.length + cut k ≤ 1 →
          (∀ x : Fin 14 → Bool, (patchRun C j0 f0 x (k + 1)).getD (14 + k) false = rval (runG (hs ++ e) (List.ofFn x)) res) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ),
            (∀ g ∈ hs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
            hs.length + saved (k+1) ≤ k+1 ∧
            (j0<k+1 → m (14+j0) = .inl false) ∧
            (∀ w t, w < 14 + (k + 1) → m w = .inr t → t < 14 + hs.length) ∧
            ∀ x : Fin 14 → Bool, ∀ w < 14 + (k + 1),
              (patchRun C j0 f0 x (k + 1)).getD w false = rval (runG hs (List.ofFn x)) (m w) := by
        intro res e he hres hpin helen hval
        refine ⟨hs ++ e, Function.update m (14 + k) res, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg; rcases List.mem_append.mp hg with hg | hg; exact h1 g hg; exact he g hg
        · rw [List.length_append,next]
          omega
        · intro hl
          by_cases eq : k=j0
          · subst k
            rw [Function.update_self]
            exact hpin rfl
          · rw [Function.update_of_ne (by omega : 14+j0 ≠ 14+k)]
            exact stored (by omega)
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = 14 + k
          · subst hwe; rw [Function.update_self] at ht; have := hres t ht; omega
          · rw [Function.update_of_ne hwe] at ht; have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = 14 + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, patchRun_prefix C j0 f0 x k (k + 1) (by omega) w (by omega), h4 x w (by omega)]
            exact (rval_ext hs e (List.ofFn x) (m w) fun t ht => by simpa using h3 w t (by omega) ht).symm
      by_cases hkj : k = j0
      · subst hkj
        refine finish (.inl false) [] (by simp) (by simp) (by simp) (by simp [cut]) (fun x => ?_)
        rw [patchRun, ← patchRun_len C k f0 x k, getD_snoc_at, if_pos rfl]
        rfl
      · obtain ⟨hop, a, b, hab, _, ha, hb⟩ := hshape k C.gates[k] (List.getElem?_eq_getElem hklt)
        have localEmit : ∃ (res : Bool ⊕ ℕ) (e : List Gate),
            e.length + cut k ≤ 1 ∧
            (∀ g ∈ e, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) ∧
            (∀ t, res=.inr t → t<14+hs.length+e.length) ∧
            ∀ y : List Bool, y.length=14 → rval (runG (hs++e) y) res =
              C.gates[k].op.eval [rval (runG hs y) (m a),rval (runG hs y) (m b)] := by
          by_cases hot : k=j1 ∨ k=j2
          · have use := reads k hot C.gates[k] (List.getElem?_eq_getElem hklt)
            rw [hab] at use
            have pin : m (14+j0) = .inl false := stored (by rcases hot with rfl|rfl <;> omega)
            have atPin : m a = .inl false ∨ m b = .inl false := by
              rcases (show 14+j0=a ∨ 14+j0=b by simpa using use) with eq|eq
              · exact Or.inl (eq ▸ pin)
              · exact Or.inr (eq ▸ pin)
            obtain ⟨res,ok,val⟩ := emitZero hs C.gates[k].op hop (m a) (m b) (h3 a · ha) (h3 b · hb) atPin
            refine ⟨res,[],by simp [cut,hot],by simp,by simpa using ok,?_⟩
            simpa using val
          · obtain ⟨res,e,le,ok,br,ev⟩ := emit_ao hs C.gates[k].op hop (m a) (m b) (h3 a · ha) (h3 b · hb)
            exact ⟨res,e,by simpa [cut,hkj,hot] using le,ok,br,ev⟩
        obtain ⟨res,e,helen,he,hres,heval⟩ := localEmit
        refine finish res e he hres (fun eq => (hkj eq).elim) helen (fun x => ?_)
        rw [patchRun, ← patchRun_len C j0 f0 x k, getD_snoc_at, if_neg hkj, List.getElem?_eq_getElem hklt]
        dsimp only
        rw [hab, heval (List.ofFn x) (by simp)]
        simp only [List.map_cons, List.map_nil, h4 x a ha, h4 x b hb]
  obtain ⟨hs, m, h1, h2, _, _, h4⟩ := key C.gates.length le_rfl
  have h0 : j0<C.gates.length := by omega
  have h1s : j1<C.gates.length := by omega
  simp [saved,h0,h1s,valid] at h2
  rcases hm : m C.output with b | t
  · obtain ⟨x, y, hxy⟩ := hne
    rw [h4 x C.output hout, h4 y C.output hout, hm] at hxy
    exact absurd rfl hxy
  · refine ⟨⟨hs, t⟩, fun g hg => ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩, ?_, fun x => ?_⟩
    · change hs.length ≤ C.gates.length - 1; omega
    · change rval (runG hs (List.ofFn x)) (.inr t) = _
      rw [← hm, ← h4 x C.output hout]

end Research5962.Clamp
