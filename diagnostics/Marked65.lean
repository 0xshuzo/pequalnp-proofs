import PEqualNP.Defs

namespace PlaneMarked65.trace
open PEqualNP.CircuitLowerBounds

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_append (F : List Bool → Gate → Bool) (a b : List Gate) (w : List Bool) :
    fl F (a ++ b) w = fl F b (fl F a w) := by
  simp [fl, List.foldl_append]

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

theorem fl_len (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ w : List Bool, (fl F gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [fl_cons, ih]
    simp
    omega

theorem fl_keep (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (fl F gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [fl_cons, ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem fl_at (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) (k : ℕ)
    (hk : k < gs.length) :
    (fl F gs w).getD (w.length + k) false = F (fl F (gs.take k) w) gs[k] ∧
      ∀ a, a < w.length + k → (fl F gs w).getD a false = (fl F (gs.take k) w).getD a false := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hlen : (fl F (gs.take k) w).length = w.length + k := by
    rw [fl_len, List.length_take, Nat.min_eq_left (le_of_lt hk)]
  have e : fl F gs w = fl F (gs.drop (k + 1))
      (fl F (gs.take k) w ++ [F (fl F (gs.take k) w) gs[k]]) := by
    conv_lhs => rw [hsplit]
    rw [fl_append, fl_cons]
  constructor
  · rw [e, fl_keep _ _ _ _ (by simp; omega), ← hlen]
    simp
  · intro a ha
    rw [e, fl_keep _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]

def sel (op : GateOp) (p q : Bool) : Bool :=
  match op with
  | GateOp.and => p
  | _ => q

end PlaneMarked65.trace

open PlaneMarked65.trace PEqualNP.CircuitLowerBounds in
theorem PlaneMarked65.trace : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∀ (x3 : ℕ) (x4 : List Bool), ∃ (x5 : ℕ → Bool), (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = x3)) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x4.getD x8 Bool.false && x5 x9 || x5 x8 && x4.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9)) := by
  intro C hC x3 x4
  obtain ⟨_, hrb, _⟩ := hC
  let F : List Bool → Gate → Bool := fun D g =>
    sel g.op
      (x4.getD (g.inputs.getD 0 0) false && D.getD (g.inputs.getD 1 0) false
        || D.getD (g.inputs.getD 0 0) false && x4.getD (g.inputs.getD 1 0) false)
      (D.getD (g.inputs.getD 0 0) false || D.getD (g.inputs.getD 1 0) false)
  let W0 : List Bool := (List.range 26).map (fun i => decide (i = x3))
  have hW0 : W0.length = 26 := by simp [W0]
  refine ⟨fun w => (fl F C.gates W0).getD w false, ?_, ?_⟩
  · intro w hw
    show (fl F C.gates W0).getD w false = _
    rw [fl_keep _ _ _ _ (by omega)]
    simp [W0, List.getD_eq_getElem?_getD, hw]
  · intro k g a b hk hin
    obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.mp hk
    have hlt2 : ∀ i ∈ [a, b], i < 26 + k := by
      intro i hi
      refine hrb k hlt i ?_
      have : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hlt]
      rw [this, hg, hin]
      exact hi
    obtain ⟨h1, h2⟩ := fl_at F C.gates W0 k hlt
    rw [hW0, hg] at h1
    rw [hW0] at h2
    have ea := h2 a (hlt2 a (by simp))
    have eb := h2 b (hlt2 b (by simp))
    have hF : F (fl F (C.gates.take k) W0) g
        = sel g.op
          (x4.getD a false && (fl F (C.gates.take k) W0).getD b false
            || (fl F (C.gates.take k) W0).getD a false && x4.getD b false)
          ((fl F (C.gates.take k) W0).getD a false || (fl F (C.gates.take k) W0).getD b false) := by
      show sel g.op _ _ = _
      rw [hin]
      rfl
    constructor
    · intro hop
      show (fl F C.gates W0).getD (26 + k) false
        = (x4.getD a false && (fl F C.gates W0).getD b false
          || (fl F C.gates W0).getD a false && x4.getD b false)
      rw [h1, hF, hop, ea, eb]
      rfl
    · intro hop
      show (fl F C.gates W0).getD (26 + k) false
        = ((fl F C.gates W0).getD a false || (fl F C.gates W0).getD b false)
      rw [h1, hF, hop, ea, eb]
      rfl


-- The final cold conjunction criterion is adapted from R_meta_2081_317.


open PEqualNP.CircuitLowerBounds

-- A final conjunction has zero mark if both ordinary operands are false.
-- The two factors need this property on the point singleton and the line singleton.
-- On every input their intersection must be exactly the incidence function.

set_option maxHeartbeats 1600000 in
theorem PlaneMarked65.factor (budget : ℕ)
    (factor :
      ∃ C : Circuit, C.size ≤ budget ∧ PEqualNP.TopForm.IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ p l : Fin 13 → Bool,
          C.eval (List.ofFn (Fin.addCases p l)) = true ↔
          ∃ j : Fin 13, l j = true ∧
            (p j || p (j + 1) || p (j + 3) || p (j + 9)) = true) ∧
        ∃ k a b : Nat, C.output = 26 + k ∧
          C.gates[k]? = some ⟨.and,[a,b]⟩ ∧
          ∀ s : Bool,
            let ws := C.wires (List.ofFn fun i : Fin 26 =>
              decide (i.val = if s = true then 13 else 0))
            ws.getD a false = false ∧ ws.getD b false = false)
    (traces : ∀ C : Circuit, PEqualNP.TopForm.IsAO2 26 C →
      ∀ (r : Nat) (ws : List Bool), ∃ d : Nat → Bool,
        (∀ n < 26, d n = decide (n = r)) ∧
        ∀ (k : Nat) (g : Gate) (a b : Nat), C.gates[k]? = some g →
          g.inputs = [a,b] →
          (g.op = .and → d (26 + k) = ((ws.getD a false && d b) || (d a && ws.getD b false))) ∧
          (g.op = .or → d (26 + k) = (d a || d b))) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ budget ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       x3.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 x3.output = Bool.false := by
  classical
  dsimp only
  obtain ⟨C, hs, hAO, hnd, heval, k, a, b, hout, hgate, hcold⟩ := factor
  refine ⟨C, hs, hAO, hnd, ?_, ?_, ?_⟩
  · intro i j hij
    apply (heval (fun t => decide (t = i)) (fun t => decide (t = j))).2
    refine ⟨j, by simp, ?_⟩
    rcases hij with h | h | h | h <;> subst i <;> simp
  · intro p _
    let l : Fin 13 → Bool := fun j => !(p j || p (j + 1) || p (j + 3) || p (j + 9))
    change C.eval (List.ofFn (Fin.addCases p l)) = false
    cases hv : C.eval (List.ofFn (Fin.addCases p l)) with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hp⟩ := (heval p l).1 hv
      change (!(p j || p (j + 1) || p (j + 3) || p (j + 9))) = true at hj
      rw [hp] at hj
      contradiction
  · intro s
    let ws := C.wires (List.ofFn fun i : Fin 26 =>
      decide (i.val = if s = true then 13 else 0))
    obtain ⟨d, hraw, hrec⟩ := traces C hAO (if s = true then 0 else 13) ws
    refine ⟨d, hraw, hrec, ?_⟩
    obtain ⟨ha, hb⟩ := hcold s
    change ws.getD a false = false at ha
    change ws.getD b false = false at hb
    rw [hout, (hrec k ⟨.and,[a,b]⟩ a b hgate rfl).1 rfl, ha, hb]
    simp


namespace PlaneMarked65

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
set_option maxHeartbeats 10000000
set_option maxRecDepth 32768

def C : Circuit := ⟨[
  ⟨.or, [13, 17]⟩,
  ⟨.or, [23, 25]⟩,
  ⟨.or, [26, 27]⟩,
  ⟨.and, [0, 28]⟩,
  ⟨.or, [13, 14]⟩,
  ⟨.or, [18, 24]⟩,
  ⟨.or, [30, 31]⟩,
  ⟨.and, [1, 32]⟩,
  ⟨.or, [29, 33]⟩,
  ⟨.or, [13, 15]⟩,
  ⟨.or, [16, 20]⟩,
  ⟨.or, [35, 36]⟩,
  ⟨.and, [3, 37]⟩,
  ⟨.or, [34, 38]⟩,
  ⟨.or, [14, 16]⟩,
  ⟨.or, [17, 21]⟩,
  ⟨.or, [40, 41]⟩,
  ⟨.and, [4, 42]⟩,
  ⟨.or, [39, 43]⟩,
  ⟨.or, [15, 17]⟩,
  ⟨.or, [18, 22]⟩,
  ⟨.or, [45, 46]⟩,
  ⟨.and, [5, 47]⟩,
  ⟨.or, [44, 48]⟩,
  ⟨.or, [16, 18]⟩,
  ⟨.or, [19, 23]⟩,
  ⟨.or, [50, 51]⟩,
  ⟨.and, [6, 52]⟩,
  ⟨.or, [49, 53]⟩,
  ⟨.or, [17, 19]⟩,
  ⟨.or, [20, 24]⟩,
  ⟨.or, [55, 56]⟩,
  ⟨.and, [7, 57]⟩,
  ⟨.or, [54, 58]⟩,
  ⟨.or, [18, 20]⟩,
  ⟨.or, [21, 25]⟩,
  ⟨.or, [60, 61]⟩,
  ⟨.and, [8, 62]⟩,
  ⟨.or, [59, 63]⟩,
  ⟨.or, [13, 19]⟩,
  ⟨.or, [21, 22]⟩,
  ⟨.or, [65, 66]⟩,
  ⟨.and, [9, 67]⟩,
  ⟨.or, [64, 68]⟩,
  ⟨.or, [14, 20]⟩,
  ⟨.or, [22, 23]⟩,
  ⟨.or, [70, 71]⟩,
  ⟨.and, [10, 72]⟩,
  ⟨.or, [69, 73]⟩,
  ⟨.or, [15, 21]⟩,
  ⟨.or, [23, 24]⟩,
  ⟨.or, [75, 76]⟩,
  ⟨.and, [11, 77]⟩,
  ⟨.or, [74, 78]⟩,
  ⟨.or, [16, 22]⟩,
  ⟨.or, [24, 25]⟩,
  ⟨.or, [80, 81]⟩,
  ⟨.and, [12, 82]⟩,
  ⟨.or, [79, 83]⟩,
  ⟨.or, [14, 15]⟩,
  ⟨.or, [19, 25]⟩,
  ⟨.or, [85, 86]⟩,
  ⟨.or, [84, 2]⟩,
  ⟨.or, [84, 87]⟩,
  ⟨.and, [88, 89]⟩], 90⟩

def edges : List (Fin 13 × Fin 13) := [
  (0,0), (0,4), (0,10), (0,12), (1,0), (1,1), (1,5), (1,11), (2,1), (2,2), (2,6), (2,12), (3,0), (3,2), (3,3), (3,7), (4,1), (4,3), (4,4), (4,8), (5,2), (5,4), (5,5), (5,9), (6,3), (6,5), (6,6), (6,10), (7,4), (7,6), (7,7), (7,11), (8,5), (8,7), (8,8), (8,12), (9,0), (9,6), (9,8), (9,9), (10,1), (10,7), (10,9), (10,10), (11,2), (11,8), (11,10), (11,11), (12,3), (12,9), (12,11), (12,12)]


def E (i j : Fin 13) : Prop := i=j ∨ i=j+1 ∨ i=j+3 ∨ i=j+9

theorem compute (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
  ∃ i j : Fin 13, E i j ∧ x (Fin.castAdd 13 i)=true ∧ x (Fin.natAdd 13 j)=true := by
  have membership : ∀ i j : Fin 13, (i,j) ∈ edges ↔ E i j := by
    unfold E
    decide
  have eq : C.eval (List.ofFn x) = edges.any (fun e =>
      x (Fin.castAdd 13 e.1) && x (Fin.natAdd 13 e.2)) := by
    change C.eval [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] = _
    simp [C, edges, Circuit.eval, Circuit.wires, GateOp.eval]
    bv_decide
  rw [eq,List.any_eq_true]
  constructor
  · rintro ⟨⟨i,j⟩,m,b⟩
    exact ⟨i,j,(membership i j).mp m,by simpa using b⟩
  · rintro ⟨i,j,m,b⟩
    exact ⟨(i,j),(membership i j).mpr m,by simpa using b⟩

theorem full (p l : Fin 13 → Bool) :
    C.eval (List.ofFn (Fin.addCases p l)) = true ↔
      ∃ j : Fin 13, l j = true ∧ (p j || p (j+1) || p (j+3) || p (j+9)) = true := by
  have H := compute (Fin.addCases p l)
  simp only [Fin.addCases_left,Fin.addCases_right] at H
  rw [H]
  constructor
  · rintro ⟨i,j,m,hi,hj⟩
    refine ⟨j,hj,?_⟩
    rcases m with h|h|h|h <;> subst i <;> simp [hi]
  · rintro ⟨j,hj,hp⟩
    simp only [Bool.or_eq_true] at hp
    rcases hp with ((h|h)|h)|h
    · exact ⟨j,j,Or.inl rfl,h,hj⟩
    · exact ⟨j+1,j,Or.inr (Or.inl rfl),h,hj⟩
    · exact ⟨j+3,j,Or.inr (Or.inr (Or.inl rfl)),h,hj⟩
    · exact ⟨j+9,j,Or.inr (Or.inr (Or.inr rfl)),h,hj⟩

theorem marked65 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (65 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       x3.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 x3.output = Bool.false := by
  apply factor 65 _ PlaneMarked65.trace
  refine ⟨C, by decide, by decide, by decide, full, 64, 88, 89, rfl, by decide, ?_⟩
  decide

end PlaneMarked65
