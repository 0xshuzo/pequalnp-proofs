import PEqualNP.Outside.L_meta_9752
namespace Lower9767
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9752.Physical
set_option maxRecDepth 18000
set_option maxHeartbeats 0
-- The gate normalization and elimination are those of the published L9752.
private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun j => w.getD j false)
private def step (w : List Bool) (g : Gate) : List Bool := w ++ [value g w]
private def AgreeAway (pin : Nat) (a b : List Bool) : Prop :=
  a.length = b.length ∧ pin < b.length ∧
    ∀ j, j ≠ pin → a.getD j false = b.getD j false
private theorem unread_value (g : Gate) (a b : List Bool) (near : AgreeAway pin a b)
    (_legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h : reads pin g = false) : value g a = value g b := by
  unfold value
  rw [← normGate_eval g (fun i => a.getD i false), ← normGate_eval g (fun i => b.getD i false)]
  congr 1
  apply List.map_congr_left
  intro j hj
  apply near.2.2 j
  rintro rfl
  have yes : reads pin g = true := List.contains_iff_mem.mpr hj
  simp [h] at yes
private theorem step_agree (a b : List Bool) (g : Gate) (near : AgreeAway pin a b)
    (same : value g a = value g b) : AgreeAway pin (step a g) (step b g) := by
  obtain ⟨length, bound, eq⟩ := near
  refine ⟨by simp [step,length], by simp [step]; omega, ?_⟩
  intro j hj
  by_cases small : j < b.length
  · simpa only [step, List.getD_append _ _ _ _ small,
      List.getD_append _ _ _ _ (by omega : j < a.length)] using eq j hj
  · simp only [step,List.getD_append_right _ _ _ _ (by omega : a.length ≤ j),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ j),length,same]
private theorem fold_agree (p : List Gate) (a b : List Bool)
    (near : AgreeAway pin a b) (fan : FanInTwo ⟨p, 0⟩) (silent : ∀ g ∈ p, reads pin g = false) :
    AgreeAway pin (p.foldl step a) (p.foldl step b) := by
  induction p generalizing a b with
  | nil => exact near
  | cons g p ih =>
    exact ih _ _ (step_agree a b g near (unread_value g a b near (fan g (by simp)).1 (silent g (by simp))))
      (fun k hk => fan k (by simp [hk])) (fun k hk => silent k (by simp [hk]))
private theorem necessary {n : Nat} (pin : Nat) (hp : pin < n) (f : (Fin n → Bool) → Bool)
    (a z x : Fin n → Bool) (test : (List.ofFn x).getD pin false ≠ f x)
    (hDiff : f a ≠ f z)
    (hNear : ∀ i : Fin n, i.val ≠ pin → (List.ofFn a).getD i.val false = (List.ofFn z).getD i.val false)
    (C : Circuit) (fan : FanInTwo C) (ev : ∀ y, C.eval (List.ofFn y) = f y) :
    0 < C.gates.countP (reads pin) := by
  have raw : C.output ≠ pin := by
    intro eq
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn x)
    have v := ev x
    change (wiresFrom C.gates (List.ofFn x)).getD C.output false = f x at v
    rw [eq, ht, List.getD_append _ _ _ _ (by simpa using hp : pin < (List.ofFn x).length)] at v
    exact test v
  by_contra! no
  have silent : ∀ g ∈ C.gates, reads pin g = false := by
    intro g hg
    by_contra! h
    have yes : reads pin g = true := by cases eq : reads pin g <;> simp_all
    have pos : 0 < C.gates.countP (reads pin) := List.countP_pos_iff.mpr ⟨g,hg,yes⟩
    omega
  have near : AgreeAway pin (List.ofFn a) (List.ofFn z) := by
    refine ⟨by simp, by simpa using hp, ?_⟩
    intro j hj
    by_cases small : j < n
    · exact hNear ⟨j,small⟩ hj
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt small),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt small)]
  have same := (fold_agree C.gates _ _ near fan silent).2.2 C.output raw
  change C.eval (List.ofFn a) = C.eval (List.ofFn z) at same
  exact hDiff ((ev a).symm.trans (same.trans (ev z)))
private theorem project {m n k : Nat} {f : (Fin n → Bool) → Bool} {g : (Fin m → Bool) → Bool}
    (bank : List (Option (Fin m))) (pin : Nat) (hp : pin < n)
    (lift : (Fin m → Bool) → (Fin n → Bool)) (a z x : Fin n → Bool)
    (test : (List.ofFn x).getD pin false ≠ f x) (hDiff : f a ≠ f z)
    (hNear : ∀ i : Fin n, i.val ≠ pin → (List.ofFn a).getD i.val false = (List.ofFn z).getD i.val false)
    (absent : bank[pin]? = some none) (gZero : g (fun _ => false) = false)
    (layoutEq : ∀ y, restrict bank y = List.ofFn (lift y))
    (cofactor : ∀ y, f (lift y) = g y) (lower : ¬ HasCircuitSize m g k) :
    ¬ HasCircuitSize n f (k+1) := by
  rintro ⟨C,fan,small,ev⟩
  have save := necessary pin hp f a z x test hDiff hNear C fan ev
  have rest (y) : C.eval (restrict bank y) = g y := (layoutEq y) ▸ ((ev (lift y)).trans (cofactor y))
  obtain ⟨H,leg,cost,sem⟩ := eliminate_pin bank pin C fan absent ⟨fun _ => false,(rest _).trans gZero⟩
  exact lower ⟨H,leg,by omega,fun y => (sem y).trans (rest y)⟩
def F12 (x : Fin 12 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def F13 (x : Fin 13 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 6) || (x 12 && x 8) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def F14 (x : Fin 14 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 5) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def F15 (x : Fin 15 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 5) || (x 14 && x 11) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def F16 (x : Fin 16 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 5) || (x 14 && x 11) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 15 && x 10) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def F17 (x : Fin 17 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 5) || (x 14 && x 11) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 15 && x 10) || (x 16 && x 8) || (x 16 && x 5) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def F18 (x : Fin 18 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 5) || (x 14 && x 11) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 15 && x 10) || (x 16 && x 8) || (x 16 && x 5) || (x 17 && x 7) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def F19 (x : Fin 19 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 5) || (x 14 && x 11) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 15 && x 10) || (x 16 && x 8) || (x 16 && x 5) || (x 17 && x 7) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9) || (x 18 && x 9)
def F20 (x : Fin 20 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 5) || (x 14 && x 11) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 15 && x 10) || (x 16 && x 8) || (x 16 && x 5) || (x 17 && x 7) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9) || (x 18 && x 9) || (x 19 && x 11) || (x 19 && x 7) || (x 19 && x 5)
def F21 (x : Fin 21 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 20) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 5) || (x 14 && x 20) || (x 14 && x 11) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 15 && x 10) || (x 16 && x 8) || (x 16 && x 5) || (x 17 && x 20) || (x 17 && x 7) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9) || (x 18 && x 9) || (x 19 && x 11) || (x 19 && x 7) || (x 19 && x 5)
def F22 (x : Fin 22 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 20) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 21) || (x 13 && x 5) || (x 14 && x 20) || (x 14 && x 21) || (x 14 && x 11) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 21) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 9) || (x 15 && x 10) || (x 16 && x 8) || (x 16 && x 5) || (x 17 && x 20) || (x 17 && x 7) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9) || (x 18 && x 21) || (x 18 && x 9) || (x 19 && x 11) || (x 19 && x 7) || (x 19 && x 5)
def F23 (x : Fin 23 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 20) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 21) || (x 13 && x 22) || (x 13 && x 5) || (x 14 && x 20) || (x 14 && x 21) || (x 14 && x 11) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 21) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 22) || (x 2 && x 9) || (x 15 && x 10) || (x 15 && x 22) || (x 16 && x 8) || (x 16 && x 5) || (x 17 && x 20) || (x 17 && x 22) || (x 17 && x 7) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9) || (x 18 && x 21) || (x 18 && x 9) || (x 19 && x 11) || (x 19 && x 7) || (x 19 && x 5)
def F24 (x : Fin 24 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 20) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 21) || (x 13 && x 22) || (x 13 && x 5) || (x 14 && x 20) || (x 14 && x 21) || (x 14 && x 11) || (x 14 && x 23) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 3 && x 21) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 22) || (x 2 && x 9) || (x 15 && x 10) || (x 15 && x 22) || (x 15 && x 23) || (x 16 && x 8) || (x 16 && x 23) || (x 16 && x 5) || (x 17 && x 20) || (x 17 && x 22) || (x 17 && x 7) || (x 4 && x 6) || (x 4 && x 23) || (x 4 && x 7) || (x 4 && x 9) || (x 18 && x 21) || (x 18 && x 9) || (x 19 && x 11) || (x 19 && x 7) || (x 19 && x 5)
def F25 (x : Fin 25 → Bool) : Bool := (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 12 && x 20) || (x 12 && x 6) || (x 12 && x 8) || (x 13 && x 6) || (x 13 && x 21) || (x 13 && x 22) || (x 13 && x 5) || (x 14 && x 20) || (x 14 && x 21) || (x 14 && x 11) || (x 14 && x 23) || (x 0 && x 6) || (x 0 && x 11) || (x 0 && x 10) || (x 0 && x 24) || (x 3 && x 21) || (x 3 && x 10) || (x 3 && x 8) || (x 3 && x 7) || (x 2 && x 11) || (x 2 && x 8) || (x 2 && x 22) || (x 2 && x 9) || (x 15 && x 10) || (x 15 && x 22) || (x 15 && x 23) || (x 16 && x 8) || (x 16 && x 23) || (x 16 && x 24) || (x 16 && x 5) || (x 17 && x 20) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 7) || (x 4 && x 6) || (x 4 && x 23) || (x 4 && x 7) || (x 4 && x 9) || (x 18 && x 21) || (x 18 && x 24) || (x 18 && x 9) || (x 19 && x 11) || (x 19 && x 7) || (x 19 && x 5)
def F26 (x : Fin 26 → Bool) : Bool := (x 0 && x 17) || (x 0 && x 23) || (x 0 && x 25) || (x 1 && x 13) || (x 1 && x 14) || (x 1 && x 18) || (x 1 && x 24) || (x 2 && x 14) || (x 2 && x 15) || (x 2 && x 19) || (x 2 && x 25) || (x 3 && x 13) || (x 3 && x 15) || (x 3 && x 16) || (x 3 && x 20) || (x 4 && x 14) || (x 4 && x 16) || (x 4 && x 17) || (x 4 && x 21) || (x 5 && x 15) || (x 5 && x 17) || (x 5 && x 18) || (x 5 && x 22) || (x 6 && x 16) || (x 6 && x 18) || (x 6 && x 19) || (x 6 && x 23) || (x 7 && x 17) || (x 7 && x 19) || (x 7 && x 20) || (x 7 && x 24) || (x 8 && x 18) || (x 8 && x 20) || (x 8 && x 21) || (x 8 && x 25) || (x 9 && x 13) || (x 9 && x 19) || (x 9 && x 21) || (x 9 && x 22) || (x 10 && x 14) || (x 10 && x 20) || (x 10 && x 22) || (x 10 && x 23) || (x 11 && x 15) || (x 11 && x 21) || (x 11 && x 23) || (x 11 && x 24) || (x 12 && x 16) || (x 12 && x 22) || (x 12 && x 24) || (x 12 && x 25)
private theorem core : ¬ HasCircuitSize 12 F12 18 := by
  rintro ⟨C,h,s,e⟩
  apply PEqualNP.Outside.L_meta_9752
  refine ⟨C,h,s,fun x => (e x).trans ?_⟩
  unfold F12
  ac_rfl
private def bank13 : List (Option (Fin 12)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,none]
private def lift13 (y : Fin 12 → Bool) : Fin 13 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,false]
private theorem lower13 : ¬ HasCircuitSize 13 F13 19 := by
  apply project (g := F12) bank13 12 (by decide) lift13 (fun i : Fin 13 => decide (i.val = 8))
    (fun i : Fin 13 => decide (i.val = 12 ∨ i.val = 8)) (fun i : Fin 13 => decide (i.val = 12))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F13,lift13,F12]
  · exact core
private def bank14 : List (Option (Fin 13)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,none]
private def lift14 (y : Fin 13 → Bool) : Fin 14 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,false]
private theorem lower14 : ¬ HasCircuitSize 14 F14 20 := by
  apply project (g := F13) bank14 13 (by decide) lift14 (fun i : Fin 14 => decide (i.val = 5))
    (fun i : Fin 14 => decide (i.val = 13 ∨ i.val = 5)) (fun i : Fin 14 => decide (i.val = 13))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F14,lift14,F13]
  · exact lower13
private def bank15 : List (Option (Fin 14)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,none]
private def lift15 (y : Fin 14 → Bool) : Fin 15 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,false]
private theorem lower15 : ¬ HasCircuitSize 15 F15 21 := by
  apply project (g := F14) bank15 14 (by decide) lift15 (fun i : Fin 15 => decide (i.val = 11))
    (fun i : Fin 15 => decide (i.val = 14 ∨ i.val = 11)) (fun i : Fin 15 => decide (i.val = 14))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F15,lift15,F14]
  · exact lower14
private def bank16 : List (Option (Fin 15)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,none]
private def lift16 (y : Fin 15 → Bool) : Fin 16 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,false]
private theorem lower16 : ¬ HasCircuitSize 16 F16 22 := by
  apply project (g := F15) bank16 15 (by decide) lift16 (fun i : Fin 16 => decide (i.val = 10))
    (fun i : Fin 16 => decide (i.val = 15 ∨ i.val = 10)) (fun i : Fin 16 => decide (i.val = 15))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F16,lift16,F15]
  · exact lower15
private def bank17 : List (Option (Fin 16)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,none]
private def lift17 (y : Fin 16 → Bool) : Fin 17 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,false]
private theorem lower17 : ¬ HasCircuitSize 17 F17 23 := by
  apply project (g := F16) bank17 16 (by decide) lift17 (fun i : Fin 17 => decide (i.val = 5))
    (fun i : Fin 17 => decide (i.val = 16 ∨ i.val = 5)) (fun i : Fin 17 => decide (i.val = 16))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F17,lift17,F16]
  · exact lower16
private def bank18 : List (Option (Fin 17)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,none]
private def lift18 (y : Fin 17 → Bool) : Fin 18 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,false]
private theorem lower18 : ¬ HasCircuitSize 18 F18 24 := by
  apply project (g := F17) bank18 17 (by decide) lift18 (fun i : Fin 18 => decide (i.val = 7))
    (fun i : Fin 18 => decide (i.val = 17 ∨ i.val = 7)) (fun i : Fin 18 => decide (i.val = 17))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F18,lift18,F17]
  · exact lower17
private def bank19 : List (Option (Fin 18)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,none]
private def lift19 (y : Fin 18 → Bool) : Fin 19 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,false]
private theorem lower19 : ¬ HasCircuitSize 19 F19 25 := by
  apply project (g := F18) bank19 18 (by decide) lift19 (fun i : Fin 19 => decide (i.val = 9))
    (fun i : Fin 19 => decide (i.val = 18 ∨ i.val = 9)) (fun i : Fin 19 => decide (i.val = 18))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F19,lift19,F18]
  · exact lower18
private def bank20 : List (Option (Fin 19)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,none]
private def lift20 (y : Fin 19 → Bool) : Fin 20 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,false]
private theorem lower20 : ¬ HasCircuitSize 20 F20 26 := by
  apply project (g := F19) bank20 19 (by decide) lift20 (fun i : Fin 20 => decide (i.val = 11))
    (fun i : Fin 20 => decide (i.val = 19 ∨ i.val = 11)) (fun i : Fin 20 => decide (i.val = 19))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F20,lift20,F19]
  · exact lower19
private def bank21 : List (Option (Fin 20)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,none]
private def lift21 (y : Fin 20 → Bool) : Fin 21 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,false]
private theorem lower21 : ¬ HasCircuitSize 21 F21 27 := by
  apply project (g := F20) bank21 20 (by decide) lift21 (fun i : Fin 21 => decide (i.val = 12))
    (fun i : Fin 21 => decide (i.val = 20 ∨ i.val = 12)) (fun i : Fin 21 => decide (i.val = 20))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F21,lift21,F20]
  · exact lower20
private def bank22 : List (Option (Fin 21)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,none]
private def lift22 (y : Fin 21 → Bool) : Fin 22 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,false]
private theorem lower22 : ¬ HasCircuitSize 22 F22 28 := by
  apply project (g := F21) bank22 21 (by decide) lift22 (fun i : Fin 22 => decide (i.val = 14))
    (fun i : Fin 22 => decide (i.val = 21 ∨ i.val = 14)) (fun i : Fin 22 => decide (i.val = 21))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F22,lift22,F21]
  · exact lower21
private def bank23 : List (Option (Fin 22)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,none]
private def lift23 (y : Fin 22 → Bool) : Fin 23 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,false]
private theorem lower23 : ¬ HasCircuitSize 23 F23 29 := by
  apply project (g := F22) bank23 22 (by decide) lift23 (fun i : Fin 23 => decide (i.val = 17))
    (fun i : Fin 23 => decide (i.val = 22 ∨ i.val = 17)) (fun i : Fin 23 => decide (i.val = 22))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F23,lift23,F22]
  · exact lower22
private def bank24 : List (Option (Fin 23)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,none]
private def lift24 (y : Fin 23 → Bool) : Fin 24 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,false]
private theorem lower24 : ¬ HasCircuitSize 24 F24 30 := by
  apply project (g := F23) bank24 23 (by decide) lift24 (fun i : Fin 24 => decide (i.val = 16))
    (fun i : Fin 24 => decide (i.val = 23 ∨ i.val = 16)) (fun i : Fin 24 => decide (i.val = 23))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F24,lift24,F23]
  · exact lower23
private def bank25 : List (Option (Fin 24)) := [some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,none]
private def lift25 (y : Fin 24 → Bool) : Fin 25 → Bool := ![y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,false]
private theorem lower25 : ¬ HasCircuitSize 25 F25 31 := by
  apply project (g := F24) bank25 24 (by decide) lift25 (fun i : Fin 25 => decide (i.val = 16))
    (fun i : Fin 25 => decide (i.val = 24 ∨ i.val = 16)) (fun i : Fin 25 => decide (i.val = 24))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F25,lift25,F24]
  · exact lower24
private def bank26 : List (Option (Fin 25)) := [some 1,some 12,some 13,some 14,some 0,some 3,some 2,some 15,some 16,some 17,some 4,some 18,some 19,some 20,some 6,some 21,some 11,some 10,some 8,some 22,some 23,some 24,some 7,some 9,none,some 5]
private def lift26 (y : Fin 25 → Bool) : Fin 26 → Bool := ![y 1,y 12,y 13,y 14,y 0,y 3,y 2,y 15,y 16,y 17,y 4,y 18,y 19,y 20,y 6,y 21,y 11,y 10,y 8,y 22,y 23,y 24,y 7,y 9,false,y 5]
private theorem lower26 : ¬ HasCircuitSize 26 F26 32 := by
  apply project (g := F25) bank26 24 (by decide) lift26 (fun i : Fin 26 => decide (i.val = 1))
    (fun i : Fin 26 => decide (i.val = 24 ∨ i.val = 1)) (fun i : Fin 26 => decide (i.val = 24))
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro y
    rfl
  · intro y
    simp [F26,lift26,F25]
  · exact lower25
theorem lower : ¬ (PEqualNP.MetaComplexity.HasCircuitSize 26 (fun x : Fin 26 → Bool => (x 0 && x 17) || (x 0 && x 23) || (x 0 && x 25) || (x 1 && x 13) || (x 1 && x 14) || (x 1 && x 18) || (x 1 && x 24) || (x 2 && x 14) || (x 2 && x 15) || (x 2 && x 19) || (x 2 && x 25) || (x 3 && x 13) || (x 3 && x 15) || (x 3 && x 16) || (x 3 && x 20) || (x 4 && x 14) || (x 4 && x 16) || (x 4 && x 17) || (x 4 && x 21) || (x 5 && x 15) || (x 5 && x 17) || (x 5 && x 18) || (x 5 && x 22) || (x 6 && x 16) || (x 6 && x 18) || (x 6 && x 19) || (x 6 && x 23) || (x 7 && x 17) || (x 7 && x 19) || (x 7 && x 20) || (x 7 && x 24) || (x 8 && x 18) || (x 8 && x 20) || (x 8 && x 21) || (x 8 && x 25) || (x 9 && x 13) || (x 9 && x 19) || (x 9 && x 21) || (x 9 && x 22) || (x 10 && x 14) || (x 10 && x 20) || (x 10 && x 22) || (x 10 && x 23) || (x 11 && x 15) || (x 11 && x 21) || (x 11 && x 23) || (x 11 && x 24) || (x 12 && x 16) || (x 12 && x 22) || (x 12 && x 24) || (x 12 && x 25)) 32) := lower26
end Lower9767
