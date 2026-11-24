import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Simultaneous cyclic translation of the point and line labels gives the first 56 rows.
-- The first three orbits are edges and the next five are maximal independent sets.
-- The final two rows are the set of all points and the set of all lines.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.R_meta_2346_461
    (idle : ∀ (D : Circuit), D.size ≤ 26 → IsAO2 15 D →
      (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
      (∀ r : Fin 58, D.eval ((List.ofFn (fun i : Fin 14 => (([129, 130, 136, 244, 480, 720, 1188, 3008, 127, 16256] : List ℕ).getD (if r.val = 57 then 9 else r.val / 7) 0).testBit (7 * (i.val / 7) + (i.val + 7 - r.val % 7) % 7))) ++ [false]) =
          decide (r.val < 21)) →
      (∀ s : Bool, ∃ v : ℕ → Bool,
        let W := D.wires ((List.ofFn (fun i : Fin 14 => decide (i = if s then 0 else 7))) ++ [false])
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧ v 14 = false ∧
        (∀ j < D.size,
          let a := opnd D j 0
          let b := opnd D j 1
          v (15+j) = if (gateAt D j).op.eval [] then ((W.getD a false && v b) || (v a && W.getD b false)) else (v a || v b)) ∧ v D.output = false) → False)
    (edge : ∀ (D : Circuit) (e : ℕ), e < 21 → D.size ≤ 26 → IsAO2 15 D →
      (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
      (∀ r : Fin 58, D.eval ((List.ofFn (fun i : Fin 14 => (([129, 130, 136, 244, 480, 720, 1188, 3008, 127, 16256] : List ℕ).getD (if r.val = 57 then 9 else r.val / 7) 0).testBit (7 * (i.val / 7) + (i.val + 7 - r.val % 7) % 7))) ++ [decide (r.val = e)]) =
          decide (r.val < 21)) →
      (∀ s : Bool, ∃ v : ℕ → Bool,
        let W := D.wires ((List.ofFn (fun i : Fin 14 => decide (i = if s then 0 else 7))) ++ [false])
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧ v 14 = decide (e = 0) ∧
        (∀ j < D.size,
          let a := opnd D j 0
          let b := opnd D j 1
          v (15+j) = if (gateAt D j).op.eval [] then ((W.getD a false && v b) || (v a && W.getD b false)) else (v a || v b)) ∧ v D.output = false) → False) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  let run (gs : List Gate) (x : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

  have run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
      run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
    rfl

  have run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
      (run gs x).getD w false = x.getD w false := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

  let value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD w false

  have input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
      value C x p = x p := by
    change (run C.gates (List.ofFn x)).getD p false = x p
    have hp : (p : ℕ) < (List.ofFn x).length := by simp
    rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
    simp

  have extend {x y : List Bool} {a b : Bool} (hl : x.length = y.length)
      (h : ∀ i, x.getD i false = true → y.getD i false = true)
      (hab : a = true → b = true) : ∀ i, (x ++ [a]).getD i false = true →
        (y ++ [b]).getD i false = true := by
    intro i
    by_cases hi : i < x.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]
      exact h i
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), ← hl]
      cases i - x.length with
      | zero => exact hab
      | succ j => simp

  have evalAnd (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
  have evalOr (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl

  have monoRun (gs : List Gate) (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (x y : List Bool) (hl : x.length = y.length)
      (h : ∀ i, x.getD i false = true → y.getD i false = true) :
      ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
    induction gs generalizing x y with
    | nil => exact h
    | cons g gs ih =>
      rw [run_cons, run_cons]
      apply ih (fun t ht => hop t (by simp [ht])) _ _ (by simp [hl])
      apply extend hl h
      rcases hop g (by simp) with op | op
      · simp only [op, evalAnd, List.all_eq_true, id_eq]
        intro hx t ht
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
        exact h i (hx _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
      · simp only [op, evalOr, List.any_eq_true, id_eq]
        rintro ⟨t,ht,ht'⟩
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
        exact ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,h i ht'⟩
  rintro ⟨gates,out⟩ small ao distinct first correct deriv
  cases gates with
  | nil => cases first
  | cons g gs =>
    let C : Circuit := ⟨g :: gs, out⟩
    let D : Circuit := ⟨gs, out⟩
    change IsAO2 14 C at ao
    change ∀ j < C.size, opnd C j 0 ≠ opnd C j 1 at distinct
    change g.op = .and at first
    have glen : g.inputs.length = 2 := ao.2.2 g (by simp [C])
    obtain ⟨a,b,hin⟩ : ∃ a b, g.inputs = [a,b] := by
      rcases hh : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩ <;> simp_all
    have hzero : 0 < C.size := Nat.zero_lt_succ _
    have oa : opnd C 0 0 = a := by change g.inputs.getD 0 0 = a; rw [hin] <;> rfl
    have ob : opnd C 0 1 = b := by change g.inputs.getD 1 0 = b; rw [hin] <;> rfl
    have ab : a ≠ b := oa ▸ ob ▸ distinct 0 hzero
    have ha : a < 14 := ao.2.1 0 hzero a (by change a ∈ g.inputs; simp [hin])
    have hb : b < 14 := ao.2.1 0 hzero b (by change b ∈ g.inputs; simp [hin])
    let A : Fin 14 := ⟨a,ha⟩
    let B : Fin 14 := ⟨b,hb⟩
    have ne : A ≠ B := fun h => ab (congrArg Fin.val h)
    have hsz : D.size + 1 = C.size := rfl
    have ds : D.size ≤ 26 := by change C.size ≤ 27 at small; omega
    have dg (j : ℕ) : gateAt D j = gateAt C (j+1) := rfl
    have doi (j : ℕ) (i : Fin 2) : opnd D j i = opnd C (j+1) i := rfl
    have dop (t : Gate) (ht : t ∈ gs) : t.op = .and ∨ t.op = .or :=
      ao.1 t (List.mem_cons_of_mem g ht)
    have dao : IsAO2 15 D := by
      refine ⟨dop, ?_, fun t ht => ao.2.2 t (List.mem_cons_of_mem g ht)⟩
      intro j hj i hi
      have := ao.2.1 (j+1) (show j+1 < C.size by change j < D.size at hj; omega) i hi
      omega
    have dd (j : ℕ) (hj : j < D.size) : opnd D j 0 ≠ opnd D j 1 :=
      distinct (j+1) (by omega)
    let rows := ([129, 258, 516, 1032, 2064, 4128, 8256, 130, 260, 520, 1040, 2080, 4160, 8193, 136, 272, 544, 1088, 2049, 4098, 8196, 244, 361, 595, 1063, 2126, 4125, 8250, 480, 833, 1539, 3078, 6156, 12312, 8368, 720, 1313, 2626, 5125, 10250, 4244, 8488, 1188, 2376, 4625, 9250, 2244, 4361, 8722, 3008, 5889, 11778, 7300, 14600, 12944, 9632, 127, 16256] : List ℕ)
    let pos := ([129, 258, 516, 1032, 2064, 4128, 8256, 130, 260, 520, 1040, 2080, 4160, 8193, 136, 272, 544, 1088, 2049, 4098, 8196] : List ℕ)
    let row := fun (r : Fin 58) (i : Fin 14) => (rows.getD r.val 0).testBit i.val
    let idx := fun (u v : Fin 14) => pos.idxOf (2^u.val + 2^v.val)
    have idxBound : ∀ u v : Fin 14, idx u v ≤ 21 := by decide +kernel
    let k := idx A B
    have kBound : k ≤ 21 := idxBound A B
    let seed := fun (r : Fin 58) => decide (r.val < 21 ∧ r.val = k)
    have posVal : ∀ u v : Fin 14, u ≠ v → ∀ r : Fin 58, r.val < 21 →
        decide (r.val < 21 ∧ r.val = idx u v) = (row r u && row r v) := by decide +kernel
    have marked : ∀ (u v : Fin 14), u ≠ v → ∀ s : Bool,
        ((decide (u = if s then 0 else 7) && decide (v.val = if s then 7 else 0)) ||
        (decide (u.val = if s then 7 else 0) && decide (v = if s then 0 else 7))) =
          decide (idx u v = 0) := by decide +kernel
    have singleton : ∀ (u v : Fin 14), u ≠ v → ∀ s : Bool,
        (decide (u = if s then 0 else 7) && decide (v = if s then 0 else 7)) = false := by decide +kernel
    have packing : ∀ r : Fin 58, ∀ i : Fin 14, row r i =
        (([129, 130, 136, 244, 480, 720, 1188, 3008, 127, 16256] : List ℕ).getD (if r.val = 57 then 9 else r.val / 7) 0).testBit (7 * (i.val / 7) + (i.val + 7 - r.val % 7) % 7) := by decide +kernel
    have rowOK : ∀ r : Fin 58, (∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
        row r (Fin.castAdd 7 p) = true ∧ row r (Fin.natAdd 7 l) = true) ↔ r.val < 21 := by
      decide +kernel
    have read (x : Fin 14 → Bool) (i : Fin 14) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have wires (x : Fin 14 → Bool) :
        C.wires (List.ofFn x) = D.wires ((List.ofFn x) ++ [x A && x B]) := by
      change run (g :: gs) _ = run gs _
      rw [run_cons,first,hin]
      change run gs ((List.ofFn x) ++ [(List.ofFn x).getD a false && ((List.ofFn x).getD b false && true)]) = _
      rw [show (List.ofFn x).getD a false = x A from read x A,
          show (List.ofFn x).getD b false = x B from read x B, Bool.and_true]
    have rowEval (r : Fin 58) :
        D.eval ((List.ofFn (row r)) ++ [seed r]) = decide (r.val < 21) := by
      have hc : C.eval (List.ofFn (row r)) = true ↔ r.val < 21 :=
        (correct (row r)).trans (rowOK r)
      have hr : C.eval (List.ofFn (row r)) =
          D.eval ((List.ofFn (row r)) ++ [row r A && row r B]) :=
        congrArg (fun w : List Bool => w.getD out false) (wires (row r))
      by_cases hp : r.val < 21
      · rw [show seed r = (row r A && row r B) from posVal A B ne r hp, ← hr]
        simpa [hp] using hc.mpr hp
      · simp only [seed, hp, false_and, decide_false]
        apply Bool.eq_false_iff.mpr
        intro ht
        have hz := monoRun gs dop _ _ (by simp)
          (extend (x := List.ofFn (row r)) (y := List.ofFn (row r))
            (a := false) (b := row r A && row r B) rfl (fun _ h => h) (by simp)) out ht
        exact hp (hc.mp (hr.trans hz))
    let one := fun (s : Bool) (i : Fin 14) => decide (i = if s then 0 else 7)
    have dw (s : Bool) : C.wires (List.ofFn (one s)) =
        D.wires ((List.ofFn (one s)) ++ [false]) := by
      rw [wires, show (one s A && one s B) = false from singleton A B ne s]
    have dr : ∀ s : Bool, ∃ v : ℕ → Bool,
        let W := D.wires ((List.ofFn (one s)) ++ [false])
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧ v 14 = decide (k = 0) ∧
        (∀ j < D.size,
          let a := opnd D j 0
          let b := opnd D j 1
          v (15+j) = if (gateAt D j).op.eval [] then
            ((W.getD a false && v b) || (v a && W.getD b false)) else (v a || v b)) ∧ v D.output = false := by
      intro s
      obtain ⟨v,vi,vg,vo⟩ := deriv s
      refine ⟨v,vi,?_,?_,vo⟩
      · have h := (vg 0 hzero).1 first
        change v 14 = (((C.wires (List.ofFn (one s))).getD (opnd C 0 0) false && v (opnd C 0 1)) ||
          (v (opnd C 0 0) && (C.wires (List.ofFn (one s))).getD (opnd C 0 1) false)) at h
        rw [oa,ob,vi a ha,vi b hb] at h
        have va : (C.wires (List.ofFn (one s))).getD a false = one s A := input_value C (one s) A
        have vb : (C.wires (List.ofFn (one s))).getD b false = one s B := input_value C (one s) B
        rw [va,vb] at h
        exact h.trans (marked A B ne s)
      · intro j hj
        have h := vg (j+1) (show j+1 < C.size by omega)
        have hw (n : ℕ) : (D.wires (List.ofFn (one s) ++ [false])).getD n false =
            (C.wires (List.ofFn (one s))).getD n false := by rw [dw]
        have hop := dop (gateAt D j) (by
          change gs.getD j _ ∈ gs
          rw [List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem hj)
        rcases hop with ho | ho
        · have test : (gateAt D j).op.eval [] = true := by rw [ho] <;> rfl
          simp only [test, ↓reduceIte, hw, doi]
          simpa only [show 14 + (j+1) = 15+j by omega] using h.1 ho
        · have test : (gateAt D j).op.eval [] = false := by rw [ho] <;> rfl
          simp only [test, Bool.false_eq_true, ↓reduceIte, hw, doi]
          simpa only [show 14 + (j+1) = 15+j by omega] using h.2 ho
    by_cases hk : k < 21
    · refine edge D k hk ds dao dd ?_ dr
      intro r
      have he : seed r = decide (r.val = k) := by
        apply Bool.decide_congr
        change (r.val < 21 ∧ r.val = k) ↔ r.val = k
        omega
      simpa only [he, show row r = _ from funext (packing r)] using rowEval r
    · have sk (r : Fin 58) : seed r = false := by
        change decide (r.val < 21 ∧ r.val = k) = false
        simp only [decide_eq_false_iff_not]; omega
      refine idle D ds dao dd ?_ ?_
      · intro r; simpa only [sk, show row r = _ from funext (packing r)] using rowEval r
      · simpa only [show decide (k = 0) = false by simp only [decide_eq_false_iff_not]; omega] using dr
