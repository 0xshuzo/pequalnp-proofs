import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each group gives an omitted input position and the allowed raw OR endpoints.
-- Position eleven keeps all inputs. The leading true supplies the constant wire.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3079_461
    (classify :
      let w := fun (a b dropped : ℕ) (m : ℕ) =>
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        let xs := List.ofFn x
        true :: (xs ++ [x 0 || x 4, xs.getD a false || xs.getD b false]).set dropped false
      let y := fun (m : ℕ) =>
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (a b : ℕ) (D : Circuit), FanInTwo D → D.size ≤ 13 →
        (∀ m < 512, D.eval (w a b 11 m) = y m) →
        ∃ g ∈ ([(0,[0,3]),(4,[1,4]),(4,[4,5]),(9,[0,1,2,3,5,8]),(11,[1,2,3,5,6,7,8])] : List (ℕ × List ℕ)), ∃ i ∈ g.2, ∃ j ∈ g.2, i < j ∧ ∃ E : Circuit,
          FanInTwo E ∧ E.size ≤ 13 ∧ ∀ m < 512,
            E.eval (w i j g.1 m) = y m)
    (bounded :
      let w := fun (a b dropped : ℕ) (m : ℕ) =>
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        let xs := List.ofFn x
        true :: (xs ++ [x 0 || x 4, xs.getD a false || xs.getD b false]).set dropped false
      let y := fun (m : ℕ) =>
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ g ∈ ([(0,[0,3]),(4,[1,4]),(4,[4,5]),(9,[0,1,2,3,5,8]),(11,[1,2,3,5,6,7,8])] : List (ℕ × List ℕ)), ∀ i ∈ g.2, ∀ j ∈ g.2, i < j →
        ∀ E : Circuit, FanInTwo E →
        (∀ m < 512, E.eval (w i j g.1 m) = y m) → 14 ≤ E.size) :
∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 ≠ (9 : ℕ) ∧ ↑x2 ≠ (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), (∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) ∨ ↑x1 = x9 ∧ (↑x2 = x9 ∨ (10 : ℕ) ≤ ↑x2 ∨ (x9, ↑x2) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))]) ∨ ↑x2 = x9 ∧ (↑x1 = x9 ∨ (10 : ℕ) ≤ ↑x1 ∨ (x9, ↑x1) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))])) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b out tail hlen hab ha hb _coverage
  by_contra! h
  let index (i : Fin 26) := if i.val = 25 then 0 else i.val + 1
  let gate (g : Fin 3 × Fin 26 × Fin 26) : Gate :=
    if g.1.val = 0 then ⟨.and, [index g.2.1, index g.2.2]⟩
    else if g.1.val = 1 then ⟨.or, [index g.2.1, index g.2.2]⟩
    else ⟨.not, [index g.2.1]⟩
  let D : Circuit := ⟨tail.map gate, out.val + 1⟩
  have fan : FanInTwo D := by
    intro g hg
    change g ∈ tail.map gate at hg
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg
    by_cases hzero : q.1.val = 0
    · simp only [gate, hzero, if_true] <;> simp
    · by_cases hone : q.1.val = 1 <;> simp only [gate, hzero, hone, if_false, if_true] <;> simp
  have sz : D.size ≤ 13 := by
    change (tail.map gate).length ≤ 13
    simpa only [List.length_map] using hlen
  let read (v : List Bool) (i : Fin 26) :=
    if i.val = 25 then true else v.getD i.val false
  let step (v : List Bool) (g : Fin 3 × Fin 26 × Fin 26) := v ++ [
    if g.1.val = 0 then read v g.2.1 && read v g.2.2 else
    if g.1.val = 1 then read v g.2.1 || read v g.2.2 else !read v g.2.1]
  let gateStep (v : List Bool) (g : Gate) :=
    v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))]
  have rd (v : List Bool) (i : Fin 26) :
      (true :: v).getD (index i) false = read v i := by
    by_cases hi : i.val = 25 <;> simp only [index, read, hi, if_true, if_false, List.getD_cons_zero, List.getD_cons_succ]
  have calcStep (v : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :
      gateStep (true :: v) (gate g) = true :: step v g := by
    have andEval (p q : Bool) : GateOp.and.eval [p,q] = (p && q) := by cases p <;> cases q <;> rfl
    have orEval (p q : Bool) : GateOp.or.eval [p,q] = (p || q) := by cases p <;> cases q <;> rfl
    have notEval (p : Bool) : GateOp.not.eval [p] = !p := by cases p <;> rfl
    by_cases hz : g.1.val = 0
    · simp only [gateStep, gate, hz, if_true, List.map_cons, List.map_nil, rd,
        andEval, step, List.cons_append]
    · by_cases ho : g.1.val = 1 <;>
        simp only [gateStep, gate, hz, ho, Nat.one_ne_zero, if_true, if_false, List.map_cons,
          List.map_nil, rd, orEval, notEval, step, List.cons_append]
  have simulate (gs : List (Fin 3 × Fin 26 × Fin 26)) (v : List Bool) :
      (gs.map gate).foldl gateStep (true :: v) = true :: gs.foldl step v := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simpa only [List.map_cons, List.foldl_cons, calcStep] using ih (step v g)
  let boundary := fun (a b dropped : ℕ) (m : ℕ) =>
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        let xs := List.ofFn x
        true :: (xs ++ [x 0 || x 4, xs.getD a false || xs.getD b false]).set dropped false
  let target := fun (m : ℕ) =>
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have agrees (m : ℕ) (hm : m < 512) : D.eval (boundary a.val b.val 11 m) = target m := by
    let x : Fin 9 → Bool := fun i => m.testBit i.val
    let xs := List.ofFn x
    let u := x 0 || x 4
    have xl : xs.length = 9 := by simp [xs]
    have pre (i : Fin 26) (hn : i.val ≠ 9) (ht : i.val ≠ 25) :
        read (xs ++ [u]) i = xs.getD i.val false := by
      simp only [read, ht, if_false]
      by_cases hi : i.val < 9
      · exact List.getD_append _ _ _ _ (by omega)
      · have hr : xs.getD i.val false = false := List.getD_eq_default _ _ (by omega)
        rw [hr, List.getD_append_right _ _ _ _ (by omega), xl]
        cases hh : i.val - 9 with
        | zero => omega
        | succ y => simp
    let init := xs ++ [u, xs.getD a.val false || xs.getD b.val false]
    have bd : boundary a.val b.val 11 m = true :: init := by
      change true :: init.set 11 false = true :: init
      rw [List.set_eq_of_length_le (by simp [init, xl])]
    have seed : step (xs ++ [u]) (1, a, b) = init := by
      change (xs ++ [u]) ++ [read (xs ++ [u]) a || read (xs ++ [u]) b] = _
      rw [pre a hab.1 ha, pre b hab.2 hb]
      exact List.append_assoc _ _ _
    have eqm := Classical.not_not.mp (h m hm)
    change (((1, a, b) :: tail).foldl step (xs ++ [u])).getD out.val false = target m at eqm
    rw [List.foldl_cons, seed] at eqm
    rw [bd]
    change ((tail.map gate).foldl gateStep (true :: init)).getD (out.val+1) false = _
    rw [simulate]
    exact eqm
  obtain ⟨g, hg, i, hi, j, hj, hlt, E, hE, hs, he⟩ := classify a.val b.val D fan sz agrees
  have hh := bounded g hg i hi j hj hlt E hE he
  omega
