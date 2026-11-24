import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_1886_215
    (project : ∀ (m : ℕ) (l : List ℕ) (C : Circuit), FanInTwo C →
    (∃ x y : Fin m → Bool,
      C.eval (l.map fun i => (List.ofFn x).getD i false) ≠
      C.eval (l.map fun i => (List.ofFn y).getD i false)) →
    ∃ D : Circuit, FanInTwo D ∧
      D.size + C.gates.countP (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          fun i => l.getD i (m+1) == m) ≤ C.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (l.map fun i => (List.ofFn x).getD i false))
    (minor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (fewReaders : ∀ (D : Circuit) (s : Bool), FanInTwo D → D.size ≤ 18 →
      (∀ e ∈ ([1,4,5,12,16] : List ℕ),
        D.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun i => decide (i = e / 10 ∨ i = e % 10 ∨ (i = 10 ∧ (s = true ∨ e = 1))))) ≤ 5) →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [if s then x 0 && x 1 else x 0 || x 1]) ≠
        (fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e % 10)))) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [if x3 = Bool.true then x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) else x6 (0 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C p b hC hs
  -- Input wire i (below ten) is read as wire p i; every other wire keeps its index.
  let r : ℕ → ℕ := fun i => if h : i < 10 then ((p ⟨i, h⟩ : Fin 10) : ℕ) else i
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map r⟩), r C.output⟩
  have hD : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2⟩ := hC g0 hg0
    exact ⟨h1, by simpa using h2⟩
  have hsD : D.size ≤ 18 := by
    change (C.gates.map _).length ≤ 18
    rw [List.length_map]
    exact hs
  have snoc : ∀ (l : List Bool) (v : Bool) (i : ℕ),
      (l ++ [v]).getD i false = if i < l.length then l.getD i false
        else if i = l.length then v else false := by
    intro l v i
    split_ifs with h1 h2
    · exact List.getD_append _ _ _ _ h1
    · subst h2; simp
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, i - l.length = k + 1 := ⟨i - l.length - 1, by omega⟩
      rw [hk]; simp
  -- The relabeled circuit sees on wire r i what the original sees on wire i.
  have step : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w' w : List Bool),
      w'.length = w.length → 10 ≤ w.length →
      (∀ i, w'.getD (r i) false = w.getD i false) →
      ∀ i, ((gs.map (fun g => (⟨g.op, g.inputs.map r⟩ : PEqualNP.CircuitLowerBounds.Gate))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (r i) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i
          false := by
    intro gs
    induction gs with
    | nil => intro w' w _ _ hinv; exact hinv
    | cons g gs ih =>
      intro w' w hlen h10 hinv
      simp only [List.map_cons, List.foldl_cons]
      have hv : g.op.eval ((g.inputs.map r).map fun i => w'.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => hinv i)
      rw [hv]
      apply ih
      · simp [hlen]
      · simp; omega
      · intro i
        rw [snoc, snoc, hlen]
        by_cases hi : i < 10
        · have hr : r i = ((p ⟨i, hi⟩ : Fin 10) : ℕ) := by simp [r, hi]
          have hpi : ((p ⟨i, hi⟩ : Fin 10) : ℕ) < w.length := by omega
          rw [hr]
          simp only [hpi, show i < w.length by omega, ite_true]
          rw [← hr]
          exact hinv i
        · have hr : r i = i := by simp [r, hi]
          have hi' := hinv i
          rw [hr] at hi' ⊢
          split_ifs <;> first | exact hi' | rfl
  have key : ∀ (x : Fin 10 → Bool) (e : Bool),
      D.eval (List.ofFn x ++ [e]) = C.eval (List.ofFn (x ∘ p) ++ [e]) := by
    intro x e
    apply step C.gates
    · simp
    · simp
    · intro i
      by_cases hi : i < 10
      · have hr : r i = ((p ⟨i, hi⟩ : Fin 10) : ℕ) := by simp [r, hi]
        rw [hr, List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hi)]
        simp only [List.getElem_ofFn, Function.comp_apply, Fin.eta]
      · have hr : r i = i := by simp [r, hi]
        rw [hr, List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
        simp
  let P := (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
  let H := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
  by_contra! allInputs
  have correct (x : Fin 10 → Bool) :
      D.eval (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1]) = P x := by
    rw [key]
    exact allInputs x
  let tag : Fin 5 → ℕ := (![1,4,5,12,16] : Fin 5 → ℕ)
  let code : Fin 5 → Fin 10 → ℕ := ![![8,8,0,1,5,6,3,4,2,7],![8,0,1,5,8,3,4,2,7,6],![8,0,1,2,3,8,4,5,6,7],![0,8,8,5,1,4,3,6,7,2],![0,8,3,2,1,4,8,7,6,5]]
  let row (q : Fin 5) (s : Bool) :=
    List.ofFn (code q) ++ [if s then 8 else min (code q 0) (code q 1)]
  let expand (q : Fin 5) (x : Fin 8 → Bool) (j : Fin 10) :=
    (List.ofFn x).getD (code q j) false
  have target (q : Fin 5) (x : Fin 8 → Bool) : P (expand q x) = H x := by
    fin_cases q
    · change ((false && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 5) || (x 5 && false) || (false && x 6) || (false && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 7) || (x 6 && x 4) || (x 4 && x 7) || (x 7 && x 3) || (x 3 && x 2) || (x 2 && x 6)) = _
      dsimp only [H]
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((false && x 0) || (x 0 && x 1) || (x 1 && x 5) || (x 5 && false) || (false && false) || (false && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 7) || (false && x 6) || (x 3 && x 2) || (x 2 && x 6) || (x 6 && x 4) || (x 4 && x 7) || (x 7 && x 3)) = _
      dsimp only [H]
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && false) || (false && false) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (false && x 5) || (x 5 && x 7) || (x 7 && x 4) || (x 4 && x 6) || (x 6 && false)) = _
      dsimp only [H]
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 0 && false) || (false && false) || (false && x 5) || (x 5 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (false && x 3) || (false && x 6) || (x 5 && x 7) || (x 1 && x 2) || (x 4 && x 6) || (x 6 && x 2) || (x 2 && x 3) || (x 3 && x 7) || (x 7 && x 4)) = _
      dsimp only [H]
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 0 && false) || (false && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (false && false) || (x 3 && x 7) || (x 2 && x 6) || (x 1 && x 5) || (x 4 && x 7) || (x 7 && x 5) || (x 5 && false) || (false && x 6) || (x 6 && x 4)) = _
      dsimp only [H]
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
  have values (q : Fin 5) (x : Fin 8 → Bool) :
      D.eval ((row q b).map fun i => (List.ofFn x).getD i false) = H x := by
    have extra : (List.ofFn x).getD (if b then 8 else min (code q 0) (code q 1)) false =
        (if b then expand q x 0 && expand q x 1 else expand q x 0 || expand q x 1) := by
      fin_cases q <;> cases b <;> first | rfl | exact (Bool.and_false _).symm | exact (Bool.or_false _).symm | exact (Bool.false_and _).symm | exact (Bool.false_or _).symm
    have inEq : (row q b).map (fun i => (List.ofFn x).getD i false) =
        List.ofFn (expand q x) ++
          [if b then expand q x 0 && expand q x 1 else expand q x 0 || expand q x 1] := by
      simp only [row,List.map_append,List.map_cons,List.map_nil,extra]
      rw [List.map_ofFn] <;> rfl
    rw [inEq,correct,target]
  have table : ∀ (q : Fin 5) (s : Bool) (j : Fin 11),
      ((row q s).getD j.val 9 == 8) =
        decide (j.val = tag q / 10 ∨ j.val = tag q % 10 ∨ (j.val = 10 ∧ (s = true ∨ tag q = 1))) := by
    decide
  have limits (q : Fin 5) : D.gates.countP (fun g =>
      (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
        (fun i => decide (i = tag q / 10 ∨ i = tag q % 10 ∨ (i = 10 ∧ (b = true ∨ tag q = 1))))) ≤ 5 := by
    let h₀ : Fin 8 → Bool := fun _ => false
    let h₁ : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have vary : H h₀ ≠ H h₁ := by decide
    obtain ⟨E,he,sz,eval⟩ := project 8 (row q b) D hD
      ⟨h₀,h₁,by rw [values,values]; exact vary⟩
    have floor : 13 ≤ E.size := by
      by_contra! small
      apply minor
      exact ⟨E,he,by omega,fun x => (eval x).trans (values q x)⟩
    have same (i : ℕ) : ((row q b).getD i 9 == 8) =
        decide (i = tag q / 10 ∨ i = tag q % 10 ∨ (i = 10 ∧ (b = true ∨ tag q = 1))) := by
      by_cases hi : i < 11
      · exact table q b ⟨i,hi⟩
      · have len : (row q b).length ≤ i := by simp [row]; omega
        rw [List.getD_eq_default _ _ len]
        have bounds : tag q / 10 < 10 ∧ tag q % 10 < 10 := by fin_cases q <;> decide
        have a : i ≠ tag q / 10 := by omega
        have c : i ≠ tag q % 10 := by omega
        have d : i ≠ 10 := by omega
        simp [a,c,d]
    have predicates : (fun g : Gate =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          (fun i => (row q b).getD i (8+1) == 8)) = _ :=
      funext (fun g => congrArg (fun f => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any f)
        (funext same))
    rw [predicates] at sz
    omega
  have five (e : ℕ) (he : e ∈ ([1,4,5,12,16] : List ℕ)) :
      D.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
        (fun i => decide (i = e / 10 ∨ i = e % 10 ∨ (i = 10 ∧ (b = true ∨ e = 1))))) ≤ 5 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h <;> subst e
    · exact limits 0
    · exact limits 1
    · exact limits 2
    · exact limits 3
    · exact limits 4
  obtain ⟨x,bad⟩ := fewReaders D b hD hsD five
  apply bad
  rw [correct]
  change _ = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) || ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false)))))))))))))))
  dsimp only [P]
  simp only [Bool.or_false]
  ac_rfl
