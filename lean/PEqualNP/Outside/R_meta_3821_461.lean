import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3821_461
    (pinOne : ∀ (f : (Fin 10 → Bool) → Bool), HasCircuitSize 10 f 16 →
      (∃ x, f (Function.update x (Fin.last 9) (!(x (Fin.last 9)))) ≠ f x) →
      (∃ y z : Fin 9 → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc z false)) →
      HasCircuitSize 9 (fun y => f (Fin.snoc y false)) 15)
    (compress : ∀ (D : Circuit) (p : Equiv.Perm (Fin 10)) (v : Bool) (K : Finset ℕ),
      FanInTwo D →
      let ins := fun (y : Fin 9 → Bool) => (Fin.lastCases v y : Fin 10 → Bool) ∘ p
      let W := fun (i : ℕ) (y : Fin 9 → Bool) =>
          (D.wires (List.ofFn (ins y))).getD i false
      (∀ j < D.size, j ∉ K →
          (∃ t : Bool, W (10+j) = fun _ => t) ∨ ∃ i < 10+j, W (10+j) = W i) →
      HasCircuitSize 9 (fun y => D.eval (List.ofFn (ins y))) (max K.card 1))
    (marked :
      let G := fun (x : Fin 10 → Bool) => (List.finRange 5).any fun i =>
        x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
        x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
        x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))
      ∀ (D : Circuit), FanInTwo D → 17 ≤ D.size → D.size ≤ 19 →
      D.gates.getLast?.map Gate.op = some GateOp.or → D.output+1 = 10+D.size →
      (∀ i ∈ (D.gates.getLast?.map Gate.inputs).getD [], ∃ x : Fin 10 → Bool,
        (D.wires (List.ofFn x)).getD i false ≠ circuitFun 10 D x) →
      (∀ x, G x = false ∨ (List.ofFn x).count true ≤ 2 → circuitFun 10 D x = G x) →
      ∃ (p : Equiv.Perm (Fin 10)) (v : Bool) (K : Finset ℕ),
        (∀ x, G (x ∘ p) = G x) ∧ K.card ≤ (if v then 10 else 15) ∧
        let ins := fun (y : Fin 9 → Bool) => (Fin.lastCases v y : Fin 10 → Bool) ∘ p
        let W := fun (i : ℕ) (y : Fin 9 → Bool) =>
          (D.wires (List.ofFn (ins y))).getD i false
        ∀ j < D.size, j ∉ K →
          (∃ t : Bool, W (10+j) = fun _ => t) ∨ ∃ i < 10+j, W (10+j) = W i) :
have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12) := by
  let G := fun (x : Fin 10 → Bool) => (List.finRange 5).any fun i =>
        x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
        x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
        x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))
  dsimp only
  intro C a b fan small
  let f : (Fin 10 → Bool) → Bool := fun x =>
    (C.wires (List.ofFn x)).getD a false || (C.wires (List.ofFn x)).getD b false
  change _ → _ → (∀ x, G x = false ∨ (List.ofFn x).count true ≤ 2 → f x = G x) → _
  intro first second correct
  let g : Gate := ⟨.or,[a,b]⟩
  let D : Circuit := ⟨C.gates++[g],10+C.size⟩
  have hD : FanInTwo D := by
    intro q hq
    change q ∈ C.gates ++ [g] at hq
    rcases List.mem_append.mp hq with h | h
    · exact fan q h
    · obtain rfl := List.mem_singleton.mp h
      simp [g]
  have sizeD : D.size = C.size+1 := by
    change (C.gates++[g]).length = C.gates.length+1
    simp
  have lastD : D.gates.getLast?.map Gate.op = some GateOp.or := by
    change (C.gates++[g]).getLast?.map Gate.op = some GateOp.or
    simp [g]
  let run (gs : List Gate) (w : List Bool) :=
    gs.foldl (fun u h => u ++ [h.op.eval (h.inputs.map fun i => u.getD i false)]) w
  have lengthRun (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons q qs ih =>
      change (run qs (w ++ [_])).length = _
      rw [ih]
      simp <;> omega
  have calcD (x : Fin 10 → Bool) : circuitFun 10 D x = f x := by
    change (run (C.gates++[g]) (List.ofFn x)).getD (10+C.size) false = _
    let w := run C.gates (List.ofFn x)
    have hw : w.length = 10+C.size := by
      change (run C.gates (List.ofFn x)).length = 10+C.gates.length
      simp [lengthRun]
    have app : run (C.gates++[g]) (List.ofFn x) = w ++ [GateOp.or.eval [w.getD a false,w.getD b false]] := by
      simp [run,w,g,List.foldl_append]
    rw [app,←hw,List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self]
    change GateOp.or.eval [w.getD a false,w.getD b false] = (w.getD a false || w.getD b false)
    cases w.getD a false <;> cases w.getD b false <;> rfl
  have ltWire (i : ℕ) (x : Fin 10 → Bool) (h : (C.wires (List.ofFn x)).getD i false = true) :
      i < 10 + C.size := by
    by_contra! out
    change (run C.gates (List.ofFn x)).getD i false = true at h
    change 10+C.gates.length ≤ i at out
    rw [List.getD_eq_default _ _ (by simpa [lengthRun] using out)] at h
    contradiction
  have old (i : ℕ) (hi : i < 10+C.size) (x : Fin 10 → Bool) :
      (D.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false := by
    change (run (C.gates++[g]) (List.ofFn x)).getD i false = _
    unfold run
    rw [List.foldl_append]
    apply List.getD_append
    change i < (run C.gates (List.ofFn x)).length
    change i < 10+C.gates.length at hi
    simpa [lengthRun] using hi
  have finalUseful : ∀ i ∈ (D.gates.getLast?.map Gate.inputs).getD [], ∃ x : Fin 10 → Bool,
      (D.wires (List.ofFn x)).getD i false ≠ circuitFun 10 D x := by
    obtain ⟨x,xa,xb⟩ := first
    obtain ⟨y,ya,yb⟩ := second
    intro i hi
    have hAB : i = a ∨ i = b := by
      simpa [D,g] using hi
    rcases hAB with eq | eq
    · refine ⟨y,?_⟩
      rw [eq,old a (ltWire a x xa),calcD]
      simp only [f,ya,yb] <;> decide
    · refine ⟨x,?_⟩
      rw [eq,old b (ltWire b y yb),calcD]
      simp only [f,xa,xb] <;> decide
  by_cases narrow : C.size ≤ 15
  · have has : HasCircuitSize 10 f 16 := ⟨D,hD,by omega,calcD⟩
    let z : Fin 10 → Bool := fun i => decide (i=4)
    let v := Function.update z (Fin.last 9) (!(z (Fin.last 9)))
    have dep : f v ≠ f z := by
      rw [correct v (Or.inr (by decide +kernel)),correct z (Or.inr (by decide +kernel))]
      decide +kernel
    let empty : Fin 9 → Bool := fun _ => false
    let edge : Fin 9 → Bool := fun i => decide (i=0 ∨ i=1)
    have nc : f (Fin.snoc empty false) ≠ f (Fin.snoc edge false) := by
      rw [correct _ (Or.inr (by decide +kernel)),correct _ (Or.inr (by decide +kernel))]
      decide +kernel
    obtain ⟨E,hE,se,he⟩ := pinOne f has ⟨z,dep⟩ ⟨empty,edge,nc⟩
    refine ⟨Equiv.refl _,false,E,(fun _ => rfl),hE,se,?_⟩
    intro y
    change E.eval (List.ofFn y) = f (Fin.lastCases false y)
    rw [he]
    congr 1
  · obtain ⟨p,v,K,symm,card,reuse⟩ := marked D hD (by omega) (by omega) lastD
      (by change (10+C.size)+1 = 10+D.size; omega) finalUseful
      (fun x h => (calcD x).trans (correct x h))
    obtain ⟨E,hE,se,he⟩ := compress D p v K hD reuse
    refine ⟨p,v,E,symm,hE,?_,?_⟩
    · cases v <;> simp_all <;> omega
    · intro y
      exact (he y).trans (calcD _)
