import PEqualNP.Outside.L_meta_9752
namespace Signed9829
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
set_option maxRecDepth 16000

private theorem paid_pin {n m k : ℕ} (f : (Fin n → Bool) → Bool)
    (g : (Fin m → Bool) → Bool) (bank : List (Option (Fin m)))
    (probe : Bool → Fin n → Bool) (raw : Fin n → Bool)
    (positive : 0 < n) (different : (List.ofFn raw).getD 0 false ≠ f raw)
    (separate : f (probe false) ≠ f (probe true))
    (agree : ∀ i : Fin n, i.val ≠ 0 →
      (List.ofFn (probe false)).getD i.val false = (List.ofFn (probe true)).getD i.val false)
    (absent : bank[0]? = some none)
    (lift : (Fin m → Bool) → Fin n → Bool)
    (layoutEq : ∀ y, restrict bank y = List.ofFn (lift y))
    (restricted : ∀ y, f (lift y) = g y)
    (hasFalse : g (fun _ => false) = false)
    (core : ¬ HasCircuitSize m g k) : ¬ HasCircuitSize n f (k+1) := by
  rintro ⟨C,fan,small,ev⟩
  have rawOut : C.output ≠ 0 := by
    intro eq
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn raw)
    have h := ev raw
    change (wiresFrom C.gates (List.ofFn raw)).getD C.output false = f raw at h
    rw [eq, ht, List.getD_append _ _ _ _ (by simpa using positive : 0 < (List.ofFn raw).length)] at h
    exact different h
  have positiveUse : 0 < C.gates.countP (reads 0) := by
    by_contra! no
    have silent : ∀ a ∈ C.gates, reads 0 a = false := by
      intro a ha
      by_contra! h
      have yes : reads 0 a = true := by cases e : reads 0 a <;> simp_all
      have pos : 0 < C.gates.countP (reads 0) := List.countP_pos_iff.mpr ⟨a,ha,yes⟩
      omega
    have near : AgreeAway (List.ofFn (probe false)) (List.ofFn (probe true)) := by
      refine ⟨by simp, by simpa using positive, ?_⟩
      intro j diff
      by_cases h : j < n
      · exact agree ⟨j,h⟩ diff
      · have past (b : Bool) : (List.ofFn (probe b)).length ≤ j := by rw [List.length_ofFn]; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (past false), List.getElem?_eq_none (past true)]
    have same := (fold_agree C.gates _ _ near fan silent).2.2 C.output rawOut
    change C.eval (List.ofFn (probe false)) = C.eval (List.ofFn (probe true)) at same
    rw [ev,ev] at same
    exact separate same
  have rest (y) : C.eval (restrict bank y) = g y :=
    (layoutEq y) ▸ ((ev (lift y)).trans (restricted y))
  obtain ⟨D,legal,cost,table⟩ := eliminate_pin bank 0 C fan absent
    ⟨fun _ => false, (rest _).trans hasFalse⟩
  exact core ⟨D,legal,by omega,fun y => (table y).trans (rest y)⟩

def f12 (x : Fin 12 → Bool) : Bool := (x 0 && x 6) || (x 0 && x 10) || (x 0 && x 11) || (x 3 && x 8) || (x 3 && x 10) || (x 3 && x 7) || (x 2 && x 8) || (x 2 && x 9) || (x 2 && x 11) || (x 1 && x 10) || (x 1 && x 9) || (x 1 && x 5) || (x 4 && x 6) || (x 4 && x 9) || (x 4 && x 7)
def f13 (x : Fin 13 → Bool) : Bool := (x 0 && x 9) || (x 1 && x 7) || (x 1 && x 11) || (x 1 && x 12) || (x 4 && x 9) || (x 4 && x 11) || (x 4 && x 8) || (x 3 && x 9) || (x 3 && x 10) || (x 3 && x 12) || (x 2 && x 11) || (x 2 && x 10) || (x 2 && x 6) || (x 5 && x 7) || (x 5 && x 10) || (x 5 && x 8)
def f14 (x : Fin 14 → Bool) : Bool := (x 1 && x 10) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 0 && x 8) || (x 5 && x 10) || (x 5 && x 12) || (x 5 && x 9) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 3 && x 12) || (x 3 && x 11) || (x 3 && x 7) || (x 6 && x 8) || (x 6 && x 11) || (x 6 && x 9)
def f15 (x : Fin 15 → Bool) : Bool := (x 2 && x 11) || (x 3 && x 9) || (x 3 && x 13) || (x 3 && x 14) || (x 1 && x 9) || (x 0 && x 12) || (x 6 && x 11) || (x 6 && x 13) || (x 6 && x 10) || (x 5 && x 11) || (x 5 && x 12) || (x 5 && x 14) || (x 4 && x 13) || (x 4 && x 12) || (x 4 && x 8) || (x 7 && x 9) || (x 7 && x 12) || (x 7 && x 10)
def f16 (x : Fin 16 → Bool) : Bool := (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 14) || (x 4 && x 15) || (x 2 && x 10) || (x 1 && x 13) || (x 0 && x 10) || (x 0 && x 12) || (x 0 && x 9) || (x 7 && x 12) || (x 7 && x 14) || (x 7 && x 11) || (x 6 && x 12) || (x 6 && x 13) || (x 6 && x 15) || (x 5 && x 14) || (x 5 && x 13) || (x 5 && x 9) || (x 8 && x 10) || (x 8 && x 13) || (x 8 && x 11)
def f17 (x : Fin 17 → Bool) : Bool := (x 4 && x 13) || (x 5 && x 11) || (x 5 && x 15) || (x 5 && x 16) || (x 3 && x 11) || (x 2 && x 14) || (x 1 && x 11) || (x 1 && x 13) || (x 1 && x 10) || (x 8 && x 13) || (x 8 && x 15) || (x 8 && x 12) || (x 0 && x 15) || (x 7 && x 13) || (x 7 && x 14) || (x 7 && x 16) || (x 6 && x 15) || (x 6 && x 14) || (x 6 && x 10) || (x 9 && x 11) || (x 9 && x 14) || (x 9 && x 12)
def f18 (x : Fin 18 → Bool) : Bool := (x 5 && x 14) || (x 6 && x 12) || (x 6 && x 16) || (x 6 && x 17) || (x 4 && x 12) || (x 3 && x 15) || (x 2 && x 12) || (x 2 && x 14) || (x 2 && x 11) || (x 9 && x 14) || (x 9 && x 16) || (x 9 && x 13) || (x 1 && x 16) || (x 8 && x 14) || (x 8 && x 15) || (x 8 && x 17) || (x 7 && x 16) || (x 7 && x 15) || (x 7 && x 11) || (x 0 && x 11) || (x 0 && x 13) || (x 10 && x 12) || (x 10 && x 15) || (x 10 && x 13)
def f19 (x : Fin 19 → Bool) : Bool := (x 6 && x 15) || (x 7 && x 13) || (x 7 && x 17) || (x 7 && x 18) || (x 5 && x 13) || (x 4 && x 16) || (x 3 && x 13) || (x 3 && x 15) || (x 3 && x 12) || (x 10 && x 15) || (x 10 && x 17) || (x 10 && x 14) || (x 2 && x 17) || (x 9 && x 15) || (x 9 && x 16) || (x 9 && x 18) || (x 8 && x 17) || (x 8 && x 16) || (x 8 && x 12) || (x 1 && x 12) || (x 1 && x 14) || (x 11 && x 13) || (x 11 && x 16) || (x 11 && x 14) || (x 0 && x 12) || (x 0 && x 18)
def f20 (x : Fin 20 → Bool) : Bool := (x 7 && x 16) || (x 8 && x 14) || (x 8 && x 18) || (x 8 && x 19) || (x 6 && x 14) || (x 6 && x 0) || (x 5 && x 0) || (x 5 && x 17) || (x 4 && x 14) || (x 4 && x 16) || (x 4 && x 13) || (x 11 && x 0) || (x 11 && x 16) || (x 11 && x 18) || (x 11 && x 15) || (x 3 && x 18) || (x 10 && x 16) || (x 10 && x 17) || (x 10 && x 19) || (x 9 && x 18) || (x 9 && x 17) || (x 9 && x 13) || (x 2 && x 13) || (x 2 && x 15) || (x 12 && x 14) || (x 12 && x 17) || (x 12 && x 15) || (x 1 && x 0) || (x 1 && x 13) || (x 1 && x 19)
def f21 (x : Fin 21 → Bool) : Bool := (x 8 && x 17) || (x 9 && x 15) || (x 9 && x 19) || (x 9 && x 20) || (x 7 && x 15) || (x 7 && x 1) || (x 6 && x 1) || (x 6 && x 0) || (x 6 && x 18) || (x 5 && x 15) || (x 5 && x 0) || (x 5 && x 17) || (x 5 && x 14) || (x 12 && x 1) || (x 12 && x 17) || (x 12 && x 19) || (x 12 && x 16) || (x 4 && x 0) || (x 4 && x 19) || (x 11 && x 17) || (x 11 && x 18) || (x 11 && x 20) || (x 10 && x 19) || (x 10 && x 18) || (x 10 && x 14) || (x 3 && x 14) || (x 3 && x 16) || (x 13 && x 15) || (x 13 && x 18) || (x 13 && x 16) || (x 2 && x 1) || (x 2 && x 14) || (x 2 && x 20)
def f22 (x : Fin 22 → Bool) : Bool := (x 9 && x 18) || (x 10 && x 16) || (x 10 && x 20) || (x 10 && x 21) || (x 8 && x 16) || (x 8 && x 2) || (x 8 && x 0) || (x 7 && x 2) || (x 7 && x 1) || (x 7 && x 19) || (x 6 && x 16) || (x 6 && x 1) || (x 6 && x 18) || (x 6 && x 15) || (x 13 && x 2) || (x 13 && x 18) || (x 13 && x 20) || (x 13 && x 17) || (x 5 && x 1) || (x 5 && x 20) || (x 5 && x 0) || (x 12 && x 18) || (x 12 && x 0) || (x 12 && x 19) || (x 12 && x 21) || (x 11 && x 20) || (x 11 && x 19) || (x 11 && x 15) || (x 4 && x 0) || (x 4 && x 15) || (x 4 && x 17) || (x 14 && x 16) || (x 14 && x 19) || (x 14 && x 17) || (x 3 && x 2) || (x 3 && x 15) || (x 3 && x 21)
def f23 (x : Fin 23 → Bool) : Bool := (x 10 && x 19) || (x 10 && x 0) || (x 11 && x 17) || (x 11 && x 21) || (x 11 && x 22) || (x 9 && x 17) || (x 9 && x 3) || (x 9 && x 1) || (x 8 && x 3) || (x 8 && x 2) || (x 8 && x 20) || (x 7 && x 17) || (x 7 && x 2) || (x 7 && x 19) || (x 7 && x 16) || (x 14 && x 3) || (x 14 && x 19) || (x 14 && x 21) || (x 14 && x 18) || (x 6 && x 2) || (x 6 && x 21) || (x 6 && x 1) || (x 6 && x 0) || (x 13 && x 19) || (x 13 && x 1) || (x 13 && x 20) || (x 13 && x 22) || (x 12 && x 21) || (x 12 && x 20) || (x 12 && x 16) || (x 5 && x 1) || (x 5 && x 16) || (x 5 && x 18) || (x 15 && x 17) || (x 15 && x 20) || (x 15 && x 18) || (x 15 && x 0) || (x 4 && x 3) || (x 4 && x 16) || (x 4 && x 0) || (x 4 && x 22)
def f24 (x : Fin 24 → Bool) : Bool := (x 0 && x 15) || (x 0 && x 21) || (x 0 && x 23) || (x 1 && x 16) || (x 1 && x 22) || (x 2 && x 13) || (x 2 && x 17) || (x 2 && x 23) || (x 3 && x 13) || (x 3 && x 14) || (x 3 && x 18) || (x 4 && x 14) || (x 4 && x 15) || (x 4 && x 19) || (x 5 && x 13) || (x 5 && x 15) || (x 5 && x 16) || (x 5 && x 20) || (x 6 && x 14) || (x 6 && x 16) || (x 6 && x 17) || (x 6 && x 21) || (x 7 && x 15) || (x 7 && x 17) || (x 7 && x 18) || (x 7 && x 22) || (x 8 && x 16) || (x 8 && x 18) || (x 8 && x 19) || (x 8 && x 23) || (x 9 && x 17) || (x 9 && x 19) || (x 9 && x 20) || (x 10 && x 18) || (x 10 && x 20) || (x 10 && x 21) || (x 11 && x 13) || (x 11 && x 19) || (x 11 && x 21) || (x 11 && x 22) || (x 12 && x 14) || (x 12 && x 20) || (x 12 && x 22) || (x 12 && x 23)

theorem base : ¬ HasCircuitSize 12 f12 18 := by
  rintro ⟨C,fan,cost,ev⟩
  apply PEqualNP.Outside.L_meta_9752
  refine ⟨C,fan,cost,?_⟩
  intro x
  rw [ev]
  change f12 x = ((x 0 && x 6) || (x 0 && x 10) || (x 0 && x 11) || (x 1 && x 5) || (x 1 && x 9) || (x 1 && x 10) || (x 2 && x 8) || (x 2 && x 9) || (x 2 && x 11) || (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 10) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9))
  unfold f12
  ac_rfl

private def bank13 : List (Option (Fin 12)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11]
private def lift13 (y : Fin 12 → Bool) : Fin 13 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11]
private def probe13 (b : Bool) : Fin 13 → Bool := ![b,false,false,false,false,false,false,false,false,true,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower13 : ¬ HasCircuitSize 13 f13 19 := by
  apply paid_pin f13 f12 bank13 probe13 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift13 (fun y => by rfl) (fun y => by simp [f13,lift13,f12]) (by decide)
    base

private def bank14 : List (Option (Fin 13)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12]
private def lift14 (y : Fin 13 → Bool) : Fin 14 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12]
private def probe14 (b : Bool) : Fin 14 → Bool := ![b,false,false,false,false,false,false,false,true,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower14 : ¬ HasCircuitSize 14 f14 20 := by
  apply paid_pin f14 f13 bank14 probe14 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift14 (fun y => by rfl) (fun y => by simp [f14,lift14,f13]) (by decide)
    lower13

private def bank15 : List (Option (Fin 14)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13]
private def lift15 (y : Fin 14 → Bool) : Fin 15 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13]
private def probe15 (b : Bool) : Fin 15 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,true,false,false]

set_option maxHeartbeats 2000000 in
theorem lower15 : ¬ HasCircuitSize 15 f15 21 := by
  apply paid_pin f15 f14 bank15 probe15 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift15 (fun y => by rfl) (fun y => by simp [f15,lift15,f14]) (by decide)
    lower14

private def bank16 : List (Option (Fin 15)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14]
private def lift16 (y : Fin 15 → Bool) : Fin 16 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14]
private def probe16 (b : Bool) : Fin 16 → Bool := ![b,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower16 : ¬ HasCircuitSize 16 f16 22 := by
  apply paid_pin f16 f15 bank16 probe16 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift16 (fun y => by rfl) (fun y => by simp [f16,lift16,f15]) (by decide)
    lower15

private def bank17 : List (Option (Fin 16)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15]
private def lift17 (y : Fin 16 → Bool) : Fin 17 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15]
private def probe17 (b : Bool) : Fin 17 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false]

set_option maxHeartbeats 2000000 in
theorem lower17 : ¬ HasCircuitSize 17 f17 23 := by
  apply paid_pin f17 f16 bank17 probe17 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift17 (fun y => by rfl) (fun y => by simp [f17,lift17,f16]) (by decide)
    lower16

private def bank18 : List (Option (Fin 17)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16]
private def lift18 (y : Fin 17 → Bool) : Fin 18 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16]
private def probe18 (b : Bool) : Fin 18 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower18 : ¬ HasCircuitSize 18 f18 24 := by
  apply paid_pin f18 f17 bank18 probe18 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift18 (fun y => by rfl) (fun y => by simp [f18,lift18,f17]) (by decide)
    lower17

private def bank19 : List (Option (Fin 18)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17]
private def lift19 (y : Fin 18 → Bool) : Fin 19 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17]
private def probe19 (b : Bool) : Fin 19 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower19 : ¬ HasCircuitSize 19 f19 25 := by
  apply paid_pin f19 f18 bank19 probe19 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift19 (fun y => by rfl) (fun y => by simp [f19,lift19,f18]) (by decide)
    lower18

private def bank20 : List (Option (Fin 19)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18]
private def lift20 (y : Fin 19 → Bool) : Fin 20 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18]
private def probe20 (b : Bool) : Fin 20 → Bool := ![b,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower20 : ¬ HasCircuitSize 20 f20 26 := by
  apply paid_pin f20 f19 bank20 probe20 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift20 (fun y => by rfl) (fun y => by simp [f20,lift20,f19]) (by decide)
    lower19

private def bank21 : List (Option (Fin 20)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19]
private def lift21 (y : Fin 20 → Bool) : Fin 21 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19]
private def probe21 (b : Bool) : Fin 21 → Bool := ![b,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower21 : ¬ HasCircuitSize 21 f21 27 := by
  apply paid_pin f21 f20 bank21 probe21 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift21 (fun y => by rfl) (fun y => by simp [f21,lift21,f20]) (by decide)
    lower20

private def bank22 : List (Option (Fin 21)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20]
private def lift22 (y : Fin 21 → Bool) : Fin 22 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20]
private def probe22 (b : Bool) : Fin 22 → Bool := ![b,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower22 : ¬ HasCircuitSize 22 f22 28 := by
  apply paid_pin f22 f21 bank22 probe22 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift22 (fun y => by rfl) (fun y => by simp [f22,lift22,f21]) (by decide)
    lower21

private def bank23 : List (Option (Fin 22)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21]
private def lift23 (y : Fin 22 → Bool) : Fin 23 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21]
private def probe23 (b : Bool) : Fin 23 → Bool := ![b,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower23 : ¬ HasCircuitSize 23 f23 29 := by
  apply paid_pin f23 f22 bank23 probe23 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift23 (fun y => by rfl) (fun y => by simp [f23,lift23,f22]) (by decide)
    lower22

private def bank24 : List (Option (Fin 23)) := [none,some 10,some 11,some 9,some 8,some 7,some 14,some 6,some 13,some 12,some 5,some 15,some 4,some 17,some 3,some 2,some 19,some 21,some 1,some 20,some 16,some 18,some 0,some 22]
private def lift24 (y : Fin 23 → Bool) : Fin 24 → Bool := ![false,y 10,y 11,y 9,y 8,y 7,y 14,y 6,y 13,y 12,y 5,y 15,y 4,y 17,y 3,y 2,y 19,y 21,y 1,y 20,y 16,y 18,y 0,y 22]
private def probe24 (b : Bool) : Fin 24 → Bool := ![b,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false]

set_option maxHeartbeats 2000000 in
theorem lower24 : ¬ HasCircuitSize 24 f24 30 := by
  apply paid_pin f24 f23 bank24 probe24 (fun i => decide (i = 0))
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    lift24 (fun y => by rfl) (fun y => by simp [f24,lift24,f23]) (by decide)
    lower23

end Signed9829
