import PEqualNP.Outside.L_meta_9752
namespace Signed9746
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9752.Physical
private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun j => w.getD j false)
private def step (w : List Bool) (g : Gate) : List Bool := w ++ [value g w]
private def AgreeAway (a b : List Bool) : Prop :=
  a.length = b.length ∧ 0 < b.length ∧
    ∀ j, j ≠ 0 → a.getD j false = b.getD j false
private theorem unread_value (g : Gate) (a b : List Bool) (near : AgreeAway a b)
    (_legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h : reads 0 g = false) : value g a = value g b := by
  unfold value
  rw [← normGate_eval g (fun i => a.getD i false), ← normGate_eval g (fun i => b.getD i false)]
  congr 1
  apply List.map_congr_left
  intro j hj
  apply near.2.2 j
  rintro rfl
  have yes : reads 0 g = true := List.contains_iff_mem.mpr hj
  simp [h] at yes
private theorem step_agree (a b : List Bool) (g : Gate) (near : AgreeAway a b)
    (same : value g a = value g b) : AgreeAway (step a g) (step b g) := by
  obtain ⟨length, bound, eq⟩ := near
  refine ⟨by simp [step,length], by simp [step], ?_⟩
  intro j hj
  by_cases small : j < b.length
  · simpa only [step, List.getD_append _ _ _ _ small,
      List.getD_append _ _ _ _ (by omega : j < a.length)] using eq j hj
  · simp only [step,List.getD_append_right _ _ _ _ (by omega : a.length ≤ j),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ j),length,same]
private theorem fold_agree (p : List Gate) (a b : List Bool)
    (near : AgreeAway a b) (fan : FanInTwo ⟨p, 0⟩) (silent : ∀ g ∈ p, reads 0 g = false) :
    AgreeAway (p.foldl step a) (p.foldl step b) := by
  induction p generalizing a b with
  | nil => exact near
  | cons g p ih =>
    exact ih _ _ (step_agree a b g near (unread_value g a b near (fan g (by simp)).1 (silent g (by simp))))
      (fun k hk => fan k (by simp [hk])) (fun k hk => silent k (by simp [hk]))
namespace Step14
def f (x : Fin 14 → Bool) : Bool := (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def next (x : Fin 13 → Bool) : Bool := (x 0 && x 6) || (x 0 && x 8) || (x 0 && x 12) || (x 1 && x 7) || (x 1 && x 11) || (x 1 && x 12) || (x 2 && x 6) || (x 2 && x 10) || (x 2 && x 11) || (x 3 && x 9) || (x 3 && x 10) || (x 3 && x 12) || (x 4 && x 8) || (x 4 && x 9) || (x 4 && x 11) || (x 5 && x 7) || (x 5 && x 8) || (x 5 && x 10)
def bank : List (Option (Fin 13)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12]
def lift (y : Fin 13 → Bool) : Fin 14 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12]
def probe (b : Bool) : Fin 14 → Bool := ![b,false,false,false,false,false,false,false,true,false,false,false,false,false]
theorem cofactor (y) : f (lift y) = next y := by simp [f,lift,next]
theorem layout_eq (y) : restrict bank y = List.ofFn (lift y) := by rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem necessary (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (List.ofFn x) = f x) :
    0 < C.gates.countP (reads 0) := by
  have raw : C.output ≠ 0 := by
    intro eq
    let x : Fin 14 → Bool := fun i => decide (i = 0)
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn x)
    have v := ev x
    change (wiresFrom C.gates (List.ofFn x)).getD C.output false = f x at v
    rw [eq, ht, List.getD_append _ _ _ _ (by decide : 0 < (List.ofFn x).length)] at v
    exact (by decide : (List.ofFn x).getD 0 false ≠ f x) v
  by_contra! no
  have silent : ∀ g ∈ C.gates, reads 0 g = false := by
    intro g hg
    by_contra! h
    have yes : reads 0 g = true := by cases eq : reads 0 g <;> simp_all
    have pos : 0 < C.gates.countP (reads 0) := List.countP_pos_iff.mpr ⟨g,hg,yes⟩
    omega
  have near : AgreeAway (List.ofFn (probe false)) (List.ofFn (probe true)) := by
    refine ⟨rfl, by decide, ?_⟩
    intro j diff
    by_cases small : j < 14
    · exact (by decide +kernel : ∀ i : Fin 14, i.val ≠ 0 → (List.ofFn (probe false)).getD i.val false = (List.ofFn (probe true)).getD i.val false) ⟨j,small⟩ diff
    · have past (b : Bool) : (List.ofFn (probe b)).length ≤ j := by rw [List.length_ofFn]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (past false), List.getElem?_eq_none (past true)]
  have same := (fold_agree C.gates _ _ near fan silent).2.2 C.output raw
  change C.eval (List.ofFn (probe false)) = C.eval (List.ofFn (probe true)) at same
  rw [ev,ev] at same
  contradiction
theorem lower (core : ¬ HasCircuitSize 13 next 19) : ¬ HasCircuitSize 14 f 20 := by
  rintro ⟨C,fan,small,ev⟩
  have nonzero := necessary C fan ev
  have rest (y) : C.eval (restrict bank y) = next y := (layout_eq y) ▸ ((ev (lift y)).trans (cofactor y))
  obtain ⟨D,legal,cost,table⟩ := eliminate_pin bank 0 C fan (by decide) ⟨fun _ => false, (rest _).trans (by decide)⟩
  exact core ⟨D,legal,by omega,fun y => (table y).trans (rest y)⟩
end Step14
namespace Step13
def f (x : Fin 13 → Bool) : Bool := (x 0 && x 6) || (x 0 && x 8) || (x 0 && x 12) || (x 1 && x 7) || (x 1 && x 11) || (x 1 && x 12) || (x 2 && x 6) || (x 2 && x 10) || (x 2 && x 11) || (x 3 && x 9) || (x 3 && x 10) || (x 3 && x 12) || (x 4 && x 8) || (x 4 && x 9) || (x 4 && x 11) || (x 5 && x 7) || (x 5 && x 8) || (x 5 && x 10)
def next (x : Fin 12 → Bool) : Bool := (x 0 && x 6) || (x 0 && x 10) || (x 0 && x 11) || (x 1 && x 5) || (x 1 && x 9) || (x 1 && x 10) || (x 2 && x 8) || (x 2 && x 9) || (x 2 && x 11) || (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 10) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def bank : List (Option (Fin 12)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11]
def lift (y : Fin 12 → Bool) : Fin 13 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11]
def probe (b : Bool) : Fin 13 → Bool := ![b,false,false,false,false,false,true,false,false,false,false,false,false]
theorem cofactor (y) : f (lift y) = next y := by simp [f,lift,next]
theorem layout_eq (y) : restrict bank y = List.ofFn (lift y) := by rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem necessary (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (List.ofFn x) = f x) :
    0 < C.gates.countP (reads 0) := by
  have raw : C.output ≠ 0 := by
    intro eq
    let x : Fin 13 → Bool := fun i => decide (i = 0)
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn x)
    have v := ev x
    change (wiresFrom C.gates (List.ofFn x)).getD C.output false = f x at v
    rw [eq, ht, List.getD_append _ _ _ _ (by decide : 0 < (List.ofFn x).length)] at v
    exact (by decide : (List.ofFn x).getD 0 false ≠ f x) v
  by_contra! no
  have silent : ∀ g ∈ C.gates, reads 0 g = false := by
    intro g hg
    by_contra! h
    have yes : reads 0 g = true := by cases eq : reads 0 g <;> simp_all
    have pos : 0 < C.gates.countP (reads 0) := List.countP_pos_iff.mpr ⟨g,hg,yes⟩
    omega
  have near : AgreeAway (List.ofFn (probe false)) (List.ofFn (probe true)) := by
    refine ⟨rfl, by decide, ?_⟩
    intro j diff
    by_cases small : j < 13
    · exact (by decide +kernel : ∀ i : Fin 13, i.val ≠ 0 → (List.ofFn (probe false)).getD i.val false = (List.ofFn (probe true)).getD i.val false) ⟨j,small⟩ diff
    · have past (b : Bool) : (List.ofFn (probe b)).length ≤ j := by rw [List.length_ofFn]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (past false), List.getElem?_eq_none (past true)]
  have same := (fold_agree C.gates _ _ near fan silent).2.2 C.output raw
  change C.eval (List.ofFn (probe false)) = C.eval (List.ofFn (probe true)) at same
  rw [ev,ev] at same
  contradiction
theorem lower (core : ¬ HasCircuitSize 12 next 18) : ¬ HasCircuitSize 13 f 19 := by
  rintro ⟨C,fan,small,ev⟩
  have nonzero := necessary C fan ev
  have rest (y) : C.eval (restrict bank y) = next y := (layout_eq y) ▸ ((ev (lift y)).trans (cofactor y))
  obtain ⟨D,legal,cost,table⟩ := eliminate_pin bank 0 C fan (by decide) ⟨fun _ => false, (rest _).trans (by decide)⟩
  exact core ⟨D,legal,by omega,fun y => (table y).trans (rest y)⟩
end Step13
theorem signed_lower : ¬ HasCircuitSize 14 Step14.f 20 := Step14.lower (Step13.lower PEqualNP.Outside.L_meta_9752)
end Signed9746
