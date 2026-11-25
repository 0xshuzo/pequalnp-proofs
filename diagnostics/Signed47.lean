import PEqualNP.Outside.L_meta_9752
namespace Minor9836
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

private theorem one_cut {n m : Nat} {f : (Fin n → Bool) → Bool} {t : (Fin m → Bool) → Bool}
    (hn : 0<n) (bank : List (Option (Fin m))) (none0 : bank[0]?=some none)
    (lift : (Fin m → Bool) → Fin n → Bool) (matched : ∀ y, restrict bank y = List.ofFn (lift y))
    (eqt : ∀ y, f (lift y) = t y) (zero : ∃ y,t y=false)
    (p q z : Fin n → Bool) (raw : (List.ofFn z).getD 0 false ≠ f z) (flip : f p ≠ f q)
    (away : ∀ i : Fin n, i.val ≠ 0 → p i = q i) {k : Nat}
    (core : ¬ HasCircuitSize m t k) : ¬ HasCircuitSize n f (k+1) := by
  rintro ⟨C,fan,small,ev⟩
  have nonraw : C.output ≠ 0 := by
    intro eq
    obtain ⟨tail, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn z)
    have v := ev z
    change (wiresFrom C.gates (List.ofFn z)).getD C.output false = f z at v
    rw [eq, ht, List.getD_append _ _ _ _ (by simpa using hn : 0 < (List.ofFn z).length)] at v
    exact raw v
  have someReader : 0 < C.gates.countP (reads 0) := by
    by_contra! no
    have silent : ∀ g ∈ C.gates, reads 0 g = false := by
      intro g hg
      by_contra! h
      have yes : reads 0 g = true := by cases eq : reads 0 g <;> simp_all
      have pos : 0 < C.gates.countP (reads 0) := List.countP_pos_iff.mpr ⟨g,hg,yes⟩
      omega
    have near : AgreeAway (List.ofFn p) (List.ofFn q) := by
      refine ⟨by simp,by simpa using hn,?_⟩
      intro j hj
      by_cases h : j<n
      · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn,
            List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn]
        exact away ⟨j,h⟩ hj
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none
            (by simpa using Nat.le_of_not_gt h : (List.ofFn p).length ≤ j),
            List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h : (List.ofFn q).length ≤ j)]
    have un := (fold_agree C.gates _ _ near fan silent).2.2 C.output nonraw
    change C.eval (List.ofFn p) = C.eval (List.ofFn q) at un
    exact flip ((ev p).symm.trans (un.trans (ev q)))
  have rest (y) : C.eval (restrict bank y)=t y := (matched y) ▸ ((ev (lift y)).trans (eqt y))
  obtain ⟨y,hy⟩ := zero
  obtain ⟨D,leg,sz,he⟩ := eliminate_pin bank 0 C fan none0 ⟨y,(rest y).trans hy⟩
  exact core ⟨D,leg,by omega, fun v => (he v).trans (rest v)⟩
def f12 (x : Fin 12 → Bool) : Bool := (x 0 && x 6) || (x 0 && x 10) || (x 0 && x 11) || (x 1 && x 5) || (x 1 && x 9) || (x 1 && x 10) || (x 2 && x 8) || (x 2 && x 9) || (x 2 && x 11) || (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 10) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def f13 (x : Fin 13 → Bool) : Bool := (x 0 && x 8) || (x 0 && x 12) || (x 1 && x 7) || (x 1 && x 11) || (x 1 && x 12) || (x 2 && x 6) || (x 2 && x 10) || (x 2 && x 11) || (x 3 && x 9) || (x 3 && x 10) || (x 3 && x 12) || (x 4 && x 8) || (x 4 && x 9) || (x 4 && x 11) || (x 5 && x 7) || (x 5 && x 8) || (x 5 && x 10)
def f14 (x : Fin 14 → Bool) : Bool := (x 0 && x 8) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def f15 (x : Fin 15 → Bool) : Bool := (x 0 && x 13) || (x 1 && x 9) || (x 2 && x 10) || (x 2 && x 14) || (x 3 && x 9) || (x 3 && x 13) || (x 3 && x 14) || (x 4 && x 8) || (x 4 && x 12) || (x 4 && x 13) || (x 5 && x 11) || (x 5 && x 12) || (x 5 && x 14) || (x 6 && x 10) || (x 6 && x 11) || (x 6 && x 13) || (x 7 && x 9) || (x 7 && x 10) || (x 7 && x 12)
def f16 (x : Fin 16 → Bool) : Bool := (x 0 && x 13) || (x 1 && x 14) || (x 2 && x 10) || (x 3 && x 11) || (x 3 && x 15) || (x 4 && x 10) || (x 4 && x 14) || (x 4 && x 15) || (x 5 && x 9) || (x 5 && x 13) || (x 5 && x 14) || (x 6 && x 12) || (x 6 && x 13) || (x 6 && x 15) || (x 7 && x 11) || (x 7 && x 12) || (x 7 && x 14) || (x 8 && x 10) || (x 8 && x 11) || (x 8 && x 13)
def f17 (x : Fin 17 → Bool) : Bool := (x 0 && x 10) || (x 0 && x 12) || (x 1 && x 14) || (x 2 && x 15) || (x 3 && x 11) || (x 4 && x 12) || (x 4 && x 16) || (x 5 && x 11) || (x 5 && x 15) || (x 5 && x 16) || (x 6 && x 10) || (x 6 && x 14) || (x 6 && x 15) || (x 7 && x 13) || (x 7 && x 14) || (x 7 && x 16) || (x 8 && x 12) || (x 8 && x 13) || (x 8 && x 15) || (x 9 && x 11) || (x 9 && x 12) || (x 9 && x 14)
def f18 (x : Fin 18 → Bool) : Bool := (x 0 && x 16) || (x 1 && x 11) || (x 1 && x 13) || (x 2 && x 15) || (x 3 && x 16) || (x 4 && x 12) || (x 5 && x 13) || (x 5 && x 17) || (x 6 && x 12) || (x 6 && x 16) || (x 6 && x 17) || (x 7 && x 11) || (x 7 && x 15) || (x 7 && x 16) || (x 8 && x 14) || (x 8 && x 15) || (x 8 && x 17) || (x 9 && x 13) || (x 9 && x 14) || (x 9 && x 16) || (x 10 && x 12) || (x 10 && x 13) || (x 10 && x 15)
def f19 (x : Fin 19 → Bool) : Bool := (x 0 && x 12) || (x 0 && x 15) || (x 1 && x 17) || (x 2 && x 12) || (x 2 && x 14) || (x 3 && x 16) || (x 4 && x 17) || (x 5 && x 13) || (x 6 && x 14) || (x 6 && x 18) || (x 7 && x 13) || (x 7 && x 17) || (x 7 && x 18) || (x 8 && x 12) || (x 8 && x 16) || (x 8 && x 17) || (x 9 && x 15) || (x 9 && x 16) || (x 9 && x 18) || (x 10 && x 14) || (x 10 && x 15) || (x 10 && x 17) || (x 11 && x 13) || (x 11 && x 14) || (x 11 && x 16)
def f20 (x : Fin 20 → Bool) : Bool := (x 0 && x 16) || (x 1 && x 13) || (x 1 && x 16) || (x 2 && x 18) || (x 3 && x 13) || (x 3 && x 15) || (x 4 && x 17) || (x 5 && x 18) || (x 6 && x 14) || (x 7 && x 15) || (x 7 && x 19) || (x 8 && x 14) || (x 8 && x 18) || (x 8 && x 19) || (x 9 && x 13) || (x 9 && x 17) || (x 9 && x 18) || (x 10 && x 16) || (x 10 && x 17) || (x 10 && x 19) || (x 11 && x 15) || (x 11 && x 16) || (x 11 && x 18) || (x 12 && x 14) || (x 12 && x 15) || (x 12 && x 17)
def f21 (x : Fin 21 → Bool) : Bool := (x 0 && x 20) || (x 1 && x 17) || (x 2 && x 14) || (x 2 && x 17) || (x 3 && x 19) || (x 4 && x 14) || (x 4 && x 16) || (x 5 && x 18) || (x 6 && x 19) || (x 7 && x 15) || (x 8 && x 16) || (x 8 && x 20) || (x 9 && x 15) || (x 9 && x 19) || (x 9 && x 20) || (x 10 && x 14) || (x 10 && x 18) || (x 10 && x 19) || (x 11 && x 17) || (x 11 && x 18) || (x 11 && x 20) || (x 12 && x 16) || (x 12 && x 17) || (x 12 && x 19) || (x 13 && x 15) || (x 13 && x 16) || (x 13 && x 18)
def f22 (x : Fin 22 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 18) || (x 1 && x 21) || (x 2 && x 18) || (x 3 && x 15) || (x 3 && x 18) || (x 4 && x 20) || (x 5 && x 15) || (x 5 && x 17) || (x 6 && x 19) || (x 7 && x 20) || (x 8 && x 16) || (x 9 && x 17) || (x 9 && x 21) || (x 10 && x 16) || (x 10 && x 20) || (x 10 && x 21) || (x 11 && x 15) || (x 11 && x 19) || (x 11 && x 20) || (x 12 && x 18) || (x 12 && x 19) || (x 12 && x 21) || (x 13 && x 17) || (x 13 && x 18) || (x 13 && x 20) || (x 14 && x 16) || (x 14 && x 17) || (x 14 && x 19)
def f23 (x : Fin 23 → Bool) : Bool := (x 0 && x 16) || (x 0 && x 22) || (x 1 && x 17) || (x 1 && x 19) || (x 2 && x 22) || (x 3 && x 19) || (x 4 && x 16) || (x 4 && x 19) || (x 5 && x 21) || (x 6 && x 16) || (x 6 && x 18) || (x 7 && x 20) || (x 8 && x 21) || (x 9 && x 17) || (x 10 && x 18) || (x 10 && x 22) || (x 11 && x 17) || (x 11 && x 21) || (x 11 && x 22) || (x 12 && x 16) || (x 12 && x 20) || (x 12 && x 21) || (x 13 && x 19) || (x 13 && x 20) || (x 13 && x 22) || (x 14 && x 18) || (x 14 && x 19) || (x 14 && x 21) || (x 15 && x 17) || (x 15 && x 18) || (x 15 && x 20)
def f24 (x : Fin 24 → Bool) : Bool := (x 0 && x 17) || (x 0 && x 18) || (x 1 && x 17) || (x 1 && x 23) || (x 2 && x 18) || (x 2 && x 20) || (x 3 && x 23) || (x 4 && x 20) || (x 5 && x 17) || (x 5 && x 20) || (x 6 && x 22) || (x 7 && x 17) || (x 7 && x 19) || (x 8 && x 21) || (x 9 && x 22) || (x 10 && x 18) || (x 11 && x 19) || (x 11 && x 23) || (x 12 && x 18) || (x 12 && x 22) || (x 12 && x 23) || (x 13 && x 17) || (x 13 && x 21) || (x 13 && x 22) || (x 14 && x 20) || (x 14 && x 21) || (x 14 && x 23) || (x 15 && x 19) || (x 15 && x 20) || (x 15 && x 22) || (x 16 && x 18) || (x 16 && x 19) || (x 16 && x 21)
def f25 (x : Fin 25 → Bool) : Bool := (x 0 && x 22) || (x 1 && x 18) || (x 1 && x 19) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 19) || (x 3 && x 21) || (x 4 && x 24) || (x 5 && x 21) || (x 6 && x 18) || (x 6 && x 21) || (x 7 && x 23) || (x 8 && x 18) || (x 8 && x 20) || (x 9 && x 22) || (x 10 && x 23) || (x 11 && x 19) || (x 12 && x 20) || (x 12 && x 24) || (x 13 && x 19) || (x 13 && x 23) || (x 13 && x 24) || (x 14 && x 18) || (x 14 && x 22) || (x 14 && x 23) || (x 15 && x 21) || (x 15 && x 22) || (x 15 && x 24) || (x 16 && x 20) || (x 16 && x 21) || (x 16 && x 23) || (x 17 && x 19) || (x 17 && x 20) || (x 17 && x 22)
def f26 (x : Fin 26 → Bool) : Bool := (x 1 && x 0) || (x 1 && x 23) || (x 2 && x 19) || (x 2 && x 20) || (x 3 && x 0) || (x 3 && x 19) || (x 3 && x 25) || (x 4 && x 20) || (x 4 && x 22) || (x 5 && x 25) || (x 6 && x 22) || (x 7 && x 19) || (x 7 && x 22) || (x 8 && x 24) || (x 9 && x 19) || (x 9 && x 21) || (x 10 && x 23) || (x 11 && x 24) || (x 12 && x 0) || (x 12 && x 20) || (x 13 && x 21) || (x 13 && x 25) || (x 14 && x 20) || (x 14 && x 24) || (x 14 && x 25) || (x 15 && x 19) || (x 15 && x 23) || (x 15 && x 24) || (x 16 && x 22) || (x 16 && x 23) || (x 16 && x 25) || (x 17 && x 0) || (x 17 && x 21) || (x 17 && x 22) || (x 17 && x 24) || (x 18 && x 20) || (x 18 && x 21) || (x 18 && x 23)
def f27 (x : Fin 27 → Bool) : Bool := (x 0 && x 1) || (x 2 && x 1) || (x 2 && x 24) || (x 3 && x 20) || (x 3 && x 21) || (x 4 && x 1) || (x 4 && x 20) || (x 4 && x 26) || (x 5 && x 21) || (x 5 && x 23) || (x 6 && x 26) || (x 7 && x 23) || (x 8 && x 20) || (x 8 && x 23) || (x 9 && x 25) || (x 10 && x 20) || (x 10 && x 22) || (x 11 && x 24) || (x 12 && x 25) || (x 13 && x 1) || (x 13 && x 21) || (x 14 && x 22) || (x 14 && x 26) || (x 15 && x 21) || (x 15 && x 25) || (x 15 && x 26) || (x 16 && x 20) || (x 16 && x 24) || (x 16 && x 25) || (x 17 && x 23) || (x 17 && x 24) || (x 17 && x 26) || (x 18 && x 1) || (x 18 && x 22) || (x 18 && x 23) || (x 18 && x 25) || (x 19 && x 21) || (x 19 && x 22) || (x 19 && x 24)
def f28 (x : Fin 28 → Bool) : Bool := (x 1 && x 0) || (x 1 && x 2) || (x 3 && x 2) || (x 3 && x 25) || (x 4 && x 0) || (x 4 && x 21) || (x 4 && x 22) || (x 5 && x 2) || (x 5 && x 21) || (x 5 && x 27) || (x 6 && x 22) || (x 6 && x 24) || (x 7 && x 27) || (x 8 && x 24) || (x 9 && x 21) || (x 9 && x 24) || (x 10 && x 26) || (x 11 && x 21) || (x 11 && x 23) || (x 12 && x 25) || (x 13 && x 0) || (x 13 && x 26) || (x 14 && x 2) || (x 14 && x 22) || (x 15 && x 23) || (x 15 && x 27) || (x 16 && x 22) || (x 16 && x 26) || (x 16 && x 27) || (x 17 && x 21) || (x 17 && x 25) || (x 17 && x 26) || (x 18 && x 0) || (x 18 && x 24) || (x 18 && x 25) || (x 18 && x 27) || (x 19 && x 2) || (x 19 && x 23) || (x 19 && x 24) || (x 19 && x 26) || (x 20 && x 22) || (x 20 && x 23) || (x 20 && x 25)
def f29 (x : Fin 29 → Bool) : Bool := (x 2 && x 1) || (x 2 && x 3) || (x 4 && x 3) || (x 4 && x 26) || (x 5 && x 1) || (x 5 && x 22) || (x 5 && x 23) || (x 6 && x 3) || (x 6 && x 22) || (x 6 && x 28) || (x 7 && x 23) || (x 7 && x 25) || (x 8 && x 28) || (x 9 && x 25) || (x 10 && x 0) || (x 10 && x 22) || (x 10 && x 25) || (x 11 && x 27) || (x 12 && x 22) || (x 12 && x 24) || (x 13 && x 0) || (x 13 && x 26) || (x 14 && x 0) || (x 14 && x 1) || (x 14 && x 27) || (x 15 && x 0) || (x 15 && x 3) || (x 15 && x 23) || (x 16 && x 0) || (x 16 && x 24) || (x 16 && x 28) || (x 17 && x 23) || (x 17 && x 27) || (x 17 && x 28) || (x 18 && x 22) || (x 18 && x 26) || (x 18 && x 27) || (x 19 && x 1) || (x 19 && x 25) || (x 19 && x 26) || (x 19 && x 28) || (x 20 && x 3) || (x 20 && x 24) || (x 20 && x 25) || (x 20 && x 27) || (x 21 && x 23) || (x 21 && x 24) || (x 21 && x 26)
def f30 (x : Fin 30 → Bool) : Bool := (x 3 && x 0) || (x 3 && x 2) || (x 3 && x 4) || (x 5 && x 4) || (x 5 && x 27) || (x 6 && x 2) || (x 6 && x 23) || (x 6 && x 24) || (x 7 && x 4) || (x 7 && x 23) || (x 7 && x 29) || (x 8 && x 24) || (x 8 && x 26) || (x 9 && x 29) || (x 10 && x 0) || (x 10 && x 26) || (x 11 && x 1) || (x 11 && x 23) || (x 11 && x 26) || (x 12 && x 28) || (x 13 && x 0) || (x 13 && x 23) || (x 13 && x 25) || (x 14 && x 0) || (x 14 && x 1) || (x 14 && x 27) || (x 15 && x 1) || (x 15 && x 2) || (x 15 && x 28) || (x 16 && x 1) || (x 16 && x 4) || (x 16 && x 24) || (x 17 && x 1) || (x 17 && x 25) || (x 17 && x 29) || (x 18 && x 0) || (x 18 && x 24) || (x 18 && x 28) || (x 18 && x 29) || (x 19 && x 23) || (x 19 && x 27) || (x 19 && x 28) || (x 20 && x 2) || (x 20 && x 26) || (x 20 && x 27) || (x 20 && x 29) || (x 21 && x 4) || (x 21 && x 25) || (x 21 && x 26) || (x 21 && x 28) || (x 22 && x 24) || (x 22 && x 25) || (x 22 && x 27)
def f31 (x : Fin 31 → Bool) : Bool := (x 4 && x 1) || (x 4 && x 3) || (x 4 && x 5) || (x 6 && x 5) || (x 6 && x 28) || (x 7 && x 3) || (x 7 && x 24) || (x 7 && x 25) || (x 8 && x 5) || (x 8 && x 24) || (x 8 && x 30) || (x 9 && x 25) || (x 9 && x 27) || (x 10 && x 30) || (x 11 && x 1) || (x 11 && x 27) || (x 12 && x 2) || (x 12 && x 24) || (x 12 && x 27) || (x 13 && x 0) || (x 13 && x 29) || (x 14 && x 0) || (x 14 && x 1) || (x 14 && x 24) || (x 14 && x 26) || (x 15 && x 1) || (x 15 && x 2) || (x 15 && x 28) || (x 16 && x 2) || (x 16 && x 3) || (x 16 && x 29) || (x 17 && x 0) || (x 17 && x 2) || (x 17 && x 5) || (x 17 && x 25) || (x 18 && x 2) || (x 18 && x 26) || (x 18 && x 30) || (x 19 && x 1) || (x 19 && x 25) || (x 19 && x 29) || (x 19 && x 30) || (x 20 && x 24) || (x 20 && x 28) || (x 20 && x 29) || (x 21 && x 0) || (x 21 && x 3) || (x 21 && x 27) || (x 21 && x 28) || (x 21 && x 30) || (x 22 && x 5) || (x 22 && x 26) || (x 22 && x 27) || (x 22 && x 29) || (x 23 && x 25) || (x 23 && x 26) || (x 23 && x 28)
def f32 (x : Fin 32 → Bool) : Bool := (x 0 && x 1) || (x 5 && x 2) || (x 5 && x 4) || (x 5 && x 6) || (x 7 && x 6) || (x 7 && x 29) || (x 8 && x 4) || (x 8 && x 25) || (x 8 && x 26) || (x 9 && x 6) || (x 9 && x 25) || (x 9 && x 31) || (x 10 && x 26) || (x 10 && x 28) || (x 11 && x 31) || (x 12 && x 2) || (x 12 && x 28) || (x 13 && x 3) || (x 13 && x 25) || (x 13 && x 28) || (x 14 && x 1) || (x 14 && x 30) || (x 15 && x 1) || (x 15 && x 2) || (x 15 && x 25) || (x 15 && x 27) || (x 16 && x 2) || (x 16 && x 3) || (x 16 && x 29) || (x 17 && x 3) || (x 17 && x 4) || (x 17 && x 30) || (x 18 && x 1) || (x 18 && x 3) || (x 18 && x 6) || (x 18 && x 26) || (x 19 && x 3) || (x 19 && x 27) || (x 19 && x 31) || (x 20 && x 2) || (x 20 && x 26) || (x 20 && x 30) || (x 20 && x 31) || (x 21 && x 25) || (x 21 && x 29) || (x 21 && x 30) || (x 22 && x 1) || (x 22 && x 4) || (x 22 && x 28) || (x 22 && x 29) || (x 22 && x 31) || (x 23 && x 6) || (x 23 && x 27) || (x 23 && x 28) || (x 23 && x 30) || (x 24 && x 26) || (x 24 && x 27) || (x 24 && x 29)
def f33 (x : Fin 33 → Bool) : Bool := (x 1 && x 2) || (x 6 && x 0) || (x 6 && x 3) || (x 6 && x 5) || (x 6 && x 7) || (x 8 && x 7) || (x 8 && x 30) || (x 9 && x 5) || (x 9 && x 26) || (x 9 && x 27) || (x 10 && x 7) || (x 10 && x 26) || (x 10 && x 32) || (x 11 && x 27) || (x 11 && x 29) || (x 12 && x 0) || (x 12 && x 32) || (x 13 && x 3) || (x 13 && x 29) || (x 14 && x 0) || (x 14 && x 4) || (x 14 && x 26) || (x 14 && x 29) || (x 15 && x 0) || (x 15 && x 2) || (x 15 && x 31) || (x 16 && x 2) || (x 16 && x 3) || (x 16 && x 26) || (x 16 && x 28) || (x 17 && x 3) || (x 17 && x 4) || (x 17 && x 30) || (x 18 && x 4) || (x 18 && x 5) || (x 18 && x 31) || (x 19 && x 2) || (x 19 && x 4) || (x 19 && x 7) || (x 19 && x 27) || (x 20 && x 4) || (x 20 && x 28) || (x 20 && x 32) || (x 21 && x 3) || (x 21 && x 27) || (x 21 && x 31) || (x 21 && x 32) || (x 22 && x 26) || (x 22 && x 30) || (x 22 && x 31) || (x 23 && x 2) || (x 23 && x 5) || (x 23 && x 29) || (x 23 && x 30) || (x 23 && x 32) || (x 24 && x 7) || (x 24 && x 28) || (x 24 && x 29) || (x 24 && x 31) || (x 25 && x 0) || (x 25 && x 27) || (x 25 && x 28) || (x 25 && x 30)
def f34 (x : Fin 34 → Bool) : Bool := (x 2 && x 0) || (x 2 && x 3) || (x 7 && x 1) || (x 7 && x 4) || (x 7 && x 6) || (x 7 && x 8) || (x 9 && x 8) || (x 9 && x 31) || (x 10 && x 6) || (x 10 && x 27) || (x 10 && x 28) || (x 11 && x 0) || (x 11 && x 8) || (x 11 && x 27) || (x 11 && x 33) || (x 12 && x 28) || (x 12 && x 30) || (x 13 && x 1) || (x 13 && x 33) || (x 14 && x 0) || (x 14 && x 4) || (x 14 && x 30) || (x 15 && x 1) || (x 15 && x 5) || (x 15 && x 27) || (x 15 && x 30) || (x 16 && x 1) || (x 16 && x 3) || (x 16 && x 32) || (x 17 && x 3) || (x 17 && x 4) || (x 17 && x 27) || (x 17 && x 29) || (x 18 && x 4) || (x 18 && x 5) || (x 18 && x 31) || (x 19 && x 0) || (x 19 && x 5) || (x 19 && x 6) || (x 19 && x 32) || (x 20 && x 3) || (x 20 && x 5) || (x 20 && x 8) || (x 20 && x 28) || (x 21 && x 5) || (x 21 && x 29) || (x 21 && x 33) || (x 22 && x 4) || (x 22 && x 28) || (x 22 && x 32) || (x 22 && x 33) || (x 23 && x 27) || (x 23 && x 31) || (x 23 && x 32) || (x 24 && x 3) || (x 24 && x 6) || (x 24 && x 30) || (x 24 && x 31) || (x 24 && x 33) || (x 25 && x 8) || (x 25 && x 29) || (x 25 && x 30) || (x 25 && x 32) || (x 26 && x 0) || (x 26 && x 1) || (x 26 && x 28) || (x 26 && x 29) || (x 26 && x 31)
def f35 (x : Fin 35 → Bool) : Bool := (x 3 && x 0) || (x 3 && x 1) || (x 3 && x 4) || (x 8 && x 2) || (x 8 && x 5) || (x 8 && x 7) || (x 8 && x 9) || (x 10 && x 9) || (x 10 && x 32) || (x 11 && x 0) || (x 11 && x 7) || (x 11 && x 28) || (x 11 && x 29) || (x 12 && x 1) || (x 12 && x 9) || (x 12 && x 28) || (x 12 && x 34) || (x 13 && x 29) || (x 13 && x 31) || (x 14 && x 0) || (x 14 && x 2) || (x 14 && x 34) || (x 15 && x 1) || (x 15 && x 5) || (x 15 && x 31) || (x 16 && x 2) || (x 16 && x 6) || (x 16 && x 28) || (x 16 && x 31) || (x 17 && x 2) || (x 17 && x 4) || (x 17 && x 33) || (x 18 && x 4) || (x 18 && x 5) || (x 18 && x 28) || (x 18 && x 30) || (x 19 && x 0) || (x 19 && x 5) || (x 19 && x 6) || (x 19 && x 32) || (x 20 && x 1) || (x 20 && x 6) || (x 20 && x 7) || (x 20 && x 33) || (x 21 && x 4) || (x 21 && x 6) || (x 21 && x 9) || (x 21 && x 29) || (x 22 && x 6) || (x 22 && x 30) || (x 22 && x 34) || (x 23 && x 5) || (x 23 && x 29) || (x 23 && x 33) || (x 23 && x 34) || (x 24 && x 28) || (x 24 && x 32) || (x 24 && x 33) || (x 25 && x 4) || (x 25 && x 7) || (x 25 && x 31) || (x 25 && x 32) || (x 25 && x 34) || (x 26 && x 0) || (x 26 && x 9) || (x 26 && x 30) || (x 26 && x 31) || (x 26 && x 33) || (x 27 && x 1) || (x 27 && x 2) || (x 27 && x 29) || (x 27 && x 30) || (x 27 && x 32)
def f36 (x : Fin 36 → Bool) : Bool := (x 4 && x 1) || (x 4 && x 2) || (x 4 && x 5) || (x 9 && x 3) || (x 9 && x 6) || (x 9 && x 8) || (x 9 && x 10) || (x 11 && x 0) || (x 11 && x 10) || (x 11 && x 33) || (x 12 && x 1) || (x 12 && x 8) || (x 12 && x 29) || (x 12 && x 30) || (x 13 && x 2) || (x 13 && x 10) || (x 13 && x 29) || (x 13 && x 35) || (x 14 && x 0) || (x 14 && x 30) || (x 14 && x 32) || (x 15 && x 0) || (x 15 && x 1) || (x 15 && x 3) || (x 15 && x 35) || (x 16 && x 2) || (x 16 && x 6) || (x 16 && x 32) || (x 17 && x 3) || (x 17 && x 7) || (x 17 && x 29) || (x 17 && x 32) || (x 18 && x 3) || (x 18 && x 5) || (x 18 && x 34) || (x 19 && x 0) || (x 19 && x 5) || (x 19 && x 6) || (x 19 && x 29) || (x 19 && x 31) || (x 20 && x 1) || (x 20 && x 6) || (x 20 && x 7) || (x 20 && x 33) || (x 21 && x 0) || (x 21 && x 2) || (x 21 && x 7) || (x 21 && x 8) || (x 21 && x 34) || (x 22 && x 5) || (x 22 && x 7) || (x 22 && x 10) || (x 22 && x 30) || (x 23 && x 7) || (x 23 && x 31) || (x 23 && x 35) || (x 24 && x 6) || (x 24 && x 30) || (x 24 && x 34) || (x 24 && x 35) || (x 25 && x 29) || (x 25 && x 33) || (x 25 && x 34) || (x 26 && x 5) || (x 26 && x 8) || (x 26 && x 32) || (x 26 && x 33) || (x 26 && x 35) || (x 27 && x 1) || (x 27 && x 10) || (x 27 && x 31) || (x 27 && x 32) || (x 27 && x 34) || (x 28 && x 2) || (x 28 && x 3) || (x 28 && x 30) || (x 28 && x 31) || (x 28 && x 33)
def f37 (x : Fin 37 → Bool) : Bool := (x 5 && x 2) || (x 5 && x 3) || (x 5 && x 6) || (x 10 && x 4) || (x 10 && x 7) || (x 10 && x 9) || (x 10 && x 11) || (x 12 && x 1) || (x 12 && x 11) || (x 12 && x 34) || (x 13 && x 2) || (x 13 && x 9) || (x 13 && x 30) || (x 13 && x 31) || (x 14 && x 0) || (x 14 && x 3) || (x 14 && x 11) || (x 14 && x 30) || (x 14 && x 36) || (x 15 && x 0) || (x 15 && x 1) || (x 15 && x 31) || (x 15 && x 33) || (x 16 && x 1) || (x 16 && x 2) || (x 16 && x 4) || (x 16 && x 36) || (x 17 && x 3) || (x 17 && x 7) || (x 17 && x 33) || (x 18 && x 4) || (x 18 && x 8) || (x 18 && x 30) || (x 18 && x 33) || (x 19 && x 0) || (x 19 && x 4) || (x 19 && x 6) || (x 19 && x 35) || (x 20 && x 1) || (x 20 && x 6) || (x 20 && x 7) || (x 20 && x 30) || (x 20 && x 32) || (x 21 && x 0) || (x 21 && x 2) || (x 21 && x 7) || (x 21 && x 8) || (x 21 && x 34) || (x 22 && x 1) || (x 22 && x 3) || (x 22 && x 8) || (x 22 && x 9) || (x 22 && x 35) || (x 23 && x 6) || (x 23 && x 8) || (x 23 && x 11) || (x 23 && x 31) || (x 24 && x 8) || (x 24 && x 32) || (x 24 && x 36) || (x 25 && x 7) || (x 25 && x 31) || (x 25 && x 35) || (x 25 && x 36) || (x 26 && x 30) || (x 26 && x 34) || (x 26 && x 35) || (x 27 && x 6) || (x 27 && x 9) || (x 27 && x 33) || (x 27 && x 34) || (x 27 && x 36) || (x 28 && x 2) || (x 28 && x 11) || (x 28 && x 32) || (x 28 && x 33) || (x 28 && x 35) || (x 29 && x 3) || (x 29 && x 4) || (x 29 && x 31) || (x 29 && x 32) || (x 29 && x 34)
def f38 (x : Fin 38 → Bool) : Bool := (x 6 && x 3) || (x 6 && x 4) || (x 6 && x 7) || (x 11 && x 5) || (x 11 && x 8) || (x 11 && x 10) || (x 11 && x 12) || (x 13 && x 0) || (x 13 && x 2) || (x 13 && x 12) || (x 13 && x 35) || (x 14 && x 0) || (x 14 && x 3) || (x 14 && x 10) || (x 14 && x 31) || (x 14 && x 32) || (x 15 && x 1) || (x 15 && x 4) || (x 15 && x 12) || (x 15 && x 31) || (x 15 && x 37) || (x 16 && x 1) || (x 16 && x 2) || (x 16 && x 32) || (x 16 && x 34) || (x 17 && x 2) || (x 17 && x 3) || (x 17 && x 5) || (x 17 && x 37) || (x 18 && x 0) || (x 18 && x 4) || (x 18 && x 8) || (x 18 && x 34) || (x 19 && x 5) || (x 19 && x 9) || (x 19 && x 31) || (x 19 && x 34) || (x 20 && x 0) || (x 20 && x 1) || (x 20 && x 5) || (x 20 && x 7) || (x 20 && x 36) || (x 21 && x 2) || (x 21 && x 7) || (x 21 && x 8) || (x 21 && x 31) || (x 21 && x 33) || (x 22 && x 1) || (x 22 && x 3) || (x 22 && x 8) || (x 22 && x 9) || (x 22 && x 35) || (x 23 && x 2) || (x 23 && x 4) || (x 23 && x 9) || (x 23 && x 10) || (x 23 && x 36) || (x 24 && x 7) || (x 24 && x 9) || (x 24 && x 12) || (x 24 && x 32) || (x 25 && x 0) || (x 25 && x 9) || (x 25 && x 33) || (x 25 && x 37) || (x 26 && x 8) || (x 26 && x 32) || (x 26 && x 36) || (x 26 && x 37) || (x 27 && x 31) || (x 27 && x 35) || (x 27 && x 36) || (x 28 && x 7) || (x 28 && x 10) || (x 28 && x 34) || (x 28 && x 35) || (x 28 && x 37) || (x 29 && x 3) || (x 29 && x 12) || (x 29 && x 33) || (x 29 && x 34) || (x 29 && x 36) || (x 30 && x 4) || (x 30 && x 5) || (x 30 && x 32) || (x 30 && x 33) || (x 30 && x 35)
def f39 (x : Fin 39 → Bool) : Bool := (x 7 && x 0) || (x 7 && x 4) || (x 7 && x 5) || (x 7 && x 8) || (x 12 && x 6) || (x 12 && x 9) || (x 12 && x 11) || (x 12 && x 13) || (x 14 && x 0) || (x 14 && x 1) || (x 14 && x 3) || (x 14 && x 13) || (x 14 && x 36) || (x 15 && x 1) || (x 15 && x 4) || (x 15 && x 11) || (x 15 && x 32) || (x 15 && x 33) || (x 16 && x 2) || (x 16 && x 5) || (x 16 && x 13) || (x 16 && x 32) || (x 16 && x 38) || (x 17 && x 2) || (x 17 && x 3) || (x 17 && x 33) || (x 17 && x 35) || (x 18 && x 3) || (x 18 && x 4) || (x 18 && x 6) || (x 18 && x 38) || (x 19 && x 1) || (x 19 && x 5) || (x 19 && x 9) || (x 19 && x 35) || (x 20 && x 0) || (x 20 && x 6) || (x 20 && x 10) || (x 20 && x 32) || (x 20 && x 35) || (x 21 && x 1) || (x 21 && x 2) || (x 21 && x 6) || (x 21 && x 8) || (x 21 && x 37) || (x 22 && x 3) || (x 22 && x 8) || (x 22 && x 9) || (x 22 && x 32) || (x 22 && x 34) || (x 23 && x 2) || (x 23 && x 4) || (x 23 && x 9) || (x 23 && x 10) || (x 23 && x 36) || (x 24 && x 3) || (x 24 && x 5) || (x 24 && x 10) || (x 24 && x 11) || (x 24 && x 37) || (x 25 && x 8) || (x 25 && x 10) || (x 25 && x 13) || (x 25 && x 33) || (x 26 && x 1) || (x 26 && x 10) || (x 26 && x 34) || (x 26 && x 38) || (x 27 && x 0) || (x 27 && x 9) || (x 27 && x 33) || (x 27 && x 37) || (x 27 && x 38) || (x 28 && x 32) || (x 28 && x 36) || (x 28 && x 37) || (x 29 && x 8) || (x 29 && x 11) || (x 29 && x 35) || (x 29 && x 36) || (x 29 && x 38) || (x 30 && x 4) || (x 30 && x 13) || (x 30 && x 34) || (x 30 && x 35) || (x 30 && x 37) || (x 31 && x 5) || (x 31 && x 6) || (x 31 && x 33) || (x 31 && x 34) || (x 31 && x 36)
def f40 (x : Fin 40 → Bool) : Bool := (x 0 && x 24) || (x 0 && x 26) || (x 0 && x 36) || (x 0 && x 39) || (x 1 && x 25) || (x 1 && x 27) || (x 1 && x 37) || (x 2 && x 21) || (x 2 && x 26) || (x 2 && x 28) || (x 2 && x 38) || (x 3 && x 21) || (x 3 && x 22) || (x 3 && x 27) || (x 3 && x 29) || (x 3 && x 39) || (x 4 && x 22) || (x 4 && x 23) || (x 4 && x 28) || (x 4 && x 30) || (x 5 && x 23) || (x 5 && x 24) || (x 5 && x 29) || (x 5 && x 31) || (x 6 && x 21) || (x 6 && x 24) || (x 6 && x 25) || (x 6 && x 30) || (x 6 && x 32) || (x 7 && x 22) || (x 7 && x 25) || (x 7 && x 26) || (x 7 && x 31) || (x 7 && x 33) || (x 8 && x 23) || (x 8 && x 26) || (x 8 && x 27) || (x 8 && x 32) || (x 8 && x 34) || (x 9 && x 24) || (x 9 && x 27) || (x 9 && x 28) || (x 9 && x 33) || (x 9 && x 35) || (x 10 && x 25) || (x 10 && x 28) || (x 10 && x 29) || (x 10 && x 34) || (x 10 && x 36) || (x 11 && x 26) || (x 11 && x 29) || (x 11 && x 30) || (x 11 && x 35) || (x 11 && x 37) || (x 12 && x 27) || (x 12 && x 30) || (x 12 && x 31) || (x 12 && x 36) || (x 12 && x 38) || (x 13 && x 28) || (x 13 && x 31) || (x 13 && x 32) || (x 13 && x 37) || (x 13 && x 39) || (x 14 && x 29) || (x 14 && x 32) || (x 14 && x 33) || (x 14 && x 38) || (x 15 && x 30) || (x 15 && x 33) || (x 15 && x 34) || (x 15 && x 39) || (x 16 && x 21) || (x 16 && x 31) || (x 16 && x 34) || (x 16 && x 35) || (x 17 && x 22) || (x 17 && x 32) || (x 17 && x 35) || (x 17 && x 36) || (x 18 && x 21) || (x 18 && x 23) || (x 18 && x 33) || (x 18 && x 36) || (x 18 && x 37) || (x 19 && x 22) || (x 19 && x 24) || (x 19 && x 34) || (x 19 && x 37) || (x 19 && x 38) || (x 20 && x 23) || (x 20 && x 25) || (x 20 && x 35) || (x 20 && x 38) || (x 20 && x 39)
def bank13 : List (Option (Fin 12)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11]
def lift13 (y : Fin 12 → Bool) : Fin 13 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut13 (h : ¬HasCircuitSize 12 f12 18) : ¬HasCircuitSize 13 f13 19 := by
  apply one_cut (by decide) bank13 (by decide) lift13 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=8)) (fun i => decide (i.val=0 ∨ i.val=8)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f13,f12,lift13,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank14 : List (Option (Fin 13)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12]
def lift14 (y : Fin 13 → Bool) : Fin 14 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut14 (h : ¬HasCircuitSize 13 f13 19) : ¬HasCircuitSize 14 f14 20 := by
  apply one_cut (by decide) bank14 (by decide) lift14 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=8)) (fun i => decide (i.val=0 ∨ i.val=8)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f14,f13,lift14,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank15 : List (Option (Fin 14)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13]
def lift15 (y : Fin 14 → Bool) : Fin 15 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut15 (h : ¬HasCircuitSize 14 f14 20) : ¬HasCircuitSize 15 f15 21 := by
  apply one_cut (by decide) bank15 (by decide) lift15 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=13)) (fun i => decide (i.val=0 ∨ i.val=13)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f15,f14,lift15,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank16 : List (Option (Fin 15)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14]
def lift16 (y : Fin 15 → Bool) : Fin 16 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut16 (h : ¬HasCircuitSize 15 f15 21) : ¬HasCircuitSize 16 f16 22 := by
  apply one_cut (by decide) bank16 (by decide) lift16 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=13)) (fun i => decide (i.val=0 ∨ i.val=13)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f16,f15,lift16,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank17 : List (Option (Fin 16)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15]
def lift17 (y : Fin 16 → Bool) : Fin 17 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut17 (h : ¬HasCircuitSize 16 f16 22) : ¬HasCircuitSize 17 f17 23 := by
  apply one_cut (by decide) bank17 (by decide) lift17 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=10)) (fun i => decide (i.val=0 ∨ i.val=10)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f17,f16,lift17,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank18 : List (Option (Fin 17)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16]
def lift18 (y : Fin 17 → Bool) : Fin 18 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut18 (h : ¬HasCircuitSize 17 f17 23) : ¬HasCircuitSize 18 f18 24 := by
  apply one_cut (by decide) bank18 (by decide) lift18 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=16)) (fun i => decide (i.val=0 ∨ i.val=16)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f18,f17,lift18,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank19 : List (Option (Fin 18)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17]
def lift19 (y : Fin 18 → Bool) : Fin 19 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut19 (h : ¬HasCircuitSize 18 f18 24) : ¬HasCircuitSize 19 f19 25 := by
  apply one_cut (by decide) bank19 (by decide) lift19 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=12)) (fun i => decide (i.val=0 ∨ i.val=12)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f19,f18,lift19,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank20 : List (Option (Fin 19)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18]
def lift20 (y : Fin 19 → Bool) : Fin 20 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut20 (h : ¬HasCircuitSize 19 f19 25) : ¬HasCircuitSize 20 f20 26 := by
  apply one_cut (by decide) bank20 (by decide) lift20 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=16)) (fun i => decide (i.val=0 ∨ i.val=16)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f20,f19,lift20,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank21 : List (Option (Fin 20)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19]
def lift21 (y : Fin 20 → Bool) : Fin 21 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut21 (h : ¬HasCircuitSize 20 f20 26) : ¬HasCircuitSize 21 f21 27 := by
  apply one_cut (by decide) bank21 (by decide) lift21 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=20)) (fun i => decide (i.val=0 ∨ i.val=20)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f21,f20,lift21,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank22 : List (Option (Fin 21)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20]
def lift22 (y : Fin 21 → Bool) : Fin 22 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut22 (h : ¬HasCircuitSize 21 f21 27) : ¬HasCircuitSize 22 f22 28 := by
  apply one_cut (by decide) bank22 (by decide) lift22 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=16)) (fun i => decide (i.val=0 ∨ i.val=16)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f22,f21,lift22,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank23 : List (Option (Fin 22)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21]
def lift23 (y : Fin 22 → Bool) : Fin 23 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut23 (h : ¬HasCircuitSize 22 f22 28) : ¬HasCircuitSize 23 f23 29 := by
  apply one_cut (by decide) bank23 (by decide) lift23 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=16)) (fun i => decide (i.val=0 ∨ i.val=16)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f23,f22,lift23,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank24 : List (Option (Fin 23)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22]
def lift24 (y : Fin 23 → Bool) : Fin 24 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut24 (h : ¬HasCircuitSize 23 f23 29) : ¬HasCircuitSize 24 f24 30 := by
  apply one_cut (by decide) bank24 (by decide) lift24 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=17)) (fun i => decide (i.val=0 ∨ i.val=17)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f24,f23,lift24,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank25 : List (Option (Fin 24)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23]
def lift25 (y : Fin 24 → Bool) : Fin 25 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut25 (h : ¬HasCircuitSize 24 f24 30) : ¬HasCircuitSize 25 f25 31 := by
  apply one_cut (by decide) bank25 (by decide) lift25 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=22)) (fun i => decide (i.val=0 ∨ i.val=22)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f25,f24,lift25,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank26 : List (Option (Fin 25)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24]
def lift26 (y : Fin 25 → Bool) : Fin 26 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut26 (h : ¬HasCircuitSize 25 f25 31) : ¬HasCircuitSize 26 f26 32 := by
  apply one_cut (by decide) bank26 (by decide) lift26 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=1)) (fun i => decide (i.val=0 ∨ i.val=1)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f26,f25,lift26,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank27 : List (Option (Fin 26)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25]
def lift27 (y : Fin 26 → Bool) : Fin 27 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut27 (h : ¬HasCircuitSize 26 f26 32) : ¬HasCircuitSize 27 f27 33 := by
  apply one_cut (by decide) bank27 (by decide) lift27 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=1)) (fun i => decide (i.val=0 ∨ i.val=1)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f27,f26,lift27,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank28 : List (Option (Fin 27)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26]
def lift28 (y : Fin 27 → Bool) : Fin 28 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut28 (h : ¬HasCircuitSize 27 f27 33) : ¬HasCircuitSize 28 f28 34 := by
  apply one_cut (by decide) bank28 (by decide) lift28 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=1)) (fun i => decide (i.val=0 ∨ i.val=1)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f28,f27,lift28,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank29 : List (Option (Fin 28)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27]
def lift29 (y : Fin 28 → Bool) : Fin 29 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut29 (h : ¬HasCircuitSize 28 f28 34) : ¬HasCircuitSize 29 f29 35 := by
  apply one_cut (by decide) bank29 (by decide) lift29 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=10)) (fun i => decide (i.val=0 ∨ i.val=10)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f29,f28,lift29,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank30 : List (Option (Fin 29)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28]
def lift30 (y : Fin 29 → Bool) : Fin 30 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut30 (h : ¬HasCircuitSize 29 f29 35) : ¬HasCircuitSize 30 f30 36 := by
  apply one_cut (by decide) bank30 (by decide) lift30 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=3)) (fun i => decide (i.val=0 ∨ i.val=3)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f30,f29,lift30,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank31 : List (Option (Fin 30)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29]
def lift31 (y : Fin 30 → Bool) : Fin 31 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut31 (h : ¬HasCircuitSize 30 f30 36) : ¬HasCircuitSize 31 f31 37 := by
  apply one_cut (by decide) bank31 (by decide) lift31 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=13)) (fun i => decide (i.val=0 ∨ i.val=13)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f31,f30,lift31,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank32 : List (Option (Fin 31)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30]
def lift32 (y : Fin 31 → Bool) : Fin 32 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut32 (h : ¬HasCircuitSize 31 f31 37) : ¬HasCircuitSize 32 f32 38 := by
  apply one_cut (by decide) bank32 (by decide) lift32 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=1)) (fun i => decide (i.val=0 ∨ i.val=1)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f32,f31,lift32,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank33 : List (Option (Fin 32)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31]
def lift33 (y : Fin 32 → Bool) : Fin 33 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut33 (h : ¬HasCircuitSize 32 f32 38) : ¬HasCircuitSize 33 f33 39 := by
  apply one_cut (by decide) bank33 (by decide) lift33 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=6)) (fun i => decide (i.val=0 ∨ i.val=6)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f33,f32,lift33,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank34 : List (Option (Fin 33)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32]
def lift34 (y : Fin 33 → Bool) : Fin 34 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut34 (h : ¬HasCircuitSize 33 f33 39) : ¬HasCircuitSize 34 f34 40 := by
  apply one_cut (by decide) bank34 (by decide) lift34 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=2)) (fun i => decide (i.val=0 ∨ i.val=2)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f34,f33,lift34,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank35 : List (Option (Fin 34)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33]
def lift35 (y : Fin 34 → Bool) : Fin 35 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut35 (h : ¬HasCircuitSize 34 f34 40) : ¬HasCircuitSize 35 f35 41 := by
  apply one_cut (by decide) bank35 (by decide) lift35 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=3)) (fun i => decide (i.val=0 ∨ i.val=3)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f35,f34,lift35,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank36 : List (Option (Fin 35)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33,some 34]
def lift36 (y : Fin 35 → Bool) : Fin 36 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33,y 34]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut36 (h : ¬HasCircuitSize 35 f35 41) : ¬HasCircuitSize 36 f36 42 := by
  apply one_cut (by decide) bank36 (by decide) lift36 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=11)) (fun i => decide (i.val=0 ∨ i.val=11)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f36,f35,lift36,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank37 : List (Option (Fin 36)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33,some 34,some 35]
def lift37 (y : Fin 36 → Bool) : Fin 37 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33,y 34,y 35]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut37 (h : ¬HasCircuitSize 36 f36 42) : ¬HasCircuitSize 37 f37 43 := by
  apply one_cut (by decide) bank37 (by decide) lift37 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=14)) (fun i => decide (i.val=0 ∨ i.val=14)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f37,f36,lift37,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank38 : List (Option (Fin 37)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33,some 34,some 35,some 36]
def lift38 (y : Fin 37 → Bool) : Fin 38 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33,y 34,y 35,y 36]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut38 (h : ¬HasCircuitSize 37 f37 43) : ¬HasCircuitSize 38 f38 44 := by
  apply one_cut (by decide) bank38 (by decide) lift38 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=13)) (fun i => decide (i.val=0 ∨ i.val=13)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f38,f37,lift38,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank39 : List (Option (Fin 38)) := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,some 29,some 30,some 31,some 32,some 33,some 34,some 35,some 36,some 37]
def lift39 (y : Fin 38 → Bool) : Fin 39 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,y 9,y 10,y 11,y 12,y 13,y 14,y 15,y 16,y 17,y 18,y 19,y 20,y 21,y 22,y 23,y 24,y 25,y 26,y 27,y 28,y 29,y 30,y 31,y 32,y 33,y 34,y 35,y 36,y 37]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut39 (h : ¬HasCircuitSize 38 f38 44) : ¬HasCircuitSize 39 f39 45 := by
  apply one_cut (by decide) bank39 (by decide) lift39 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=7)) (fun i => decide (i.val=0 ∨ i.val=7)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f39,f38,lift39,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
def bank40 : List (Option (Fin 39)) := [none,some 28,some 26,some 27,some 25,some 12,some 29,some 31,some 30,some 24,some 23,some 22,some 21,some 20,some 19,some 7,some 18,some 17,some 16,some 15,some 14,some 38,some 33,some 13,some 11,some 36,some 34,some 37,some 10,some 9,some 8,some 6,some 35,some 5,some 4,some 3,some 2,some 32,some 1,some 0]
def lift40 (y : Fin 39 → Bool) : Fin 40 → Bool := ![false,y 28,y 26,y 27,y 25,y 12,y 29,y 31,y 30,y 24,y 23,y 22,y 21,y 20,y 19,y 7,y 18,y 17,y 16,y 15,y 14,y 38,y 33,y 13,y 11,y 36,y 34,y 37,y 10,y 9,y 8,y 6,y 35,y 5,y 4,y 3,y 2,y 32,y 1,y 0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut40 (h : ¬HasCircuitSize 39 f39 45) : ¬HasCircuitSize 40 f40 46 := by
  apply one_cut (by decide) bank40 (by decide) lift40 (fun _ => rfl) ?_ ⟨fun _ => false,by decide⟩ (fun i => decide (i.val=24)) (fun i => decide (i.val=0 ∨ i.val=24)) (fun i => decide (i.val=0)) (by decide) (by decide) (by decide) h
  intro y
  simp [f40,f39,lift40,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc] <;> (try dsimp) <;> ac_rfl
theorem signed_lower : ¬ HasCircuitSize 40 f40 46 := cut40 (cut39 (cut38 (cut37 (cut36 (cut35 (cut34 (cut33 (cut32 (cut31 (cut30 (cut29 (cut28 (cut27 (cut26 (cut25 (cut24 (cut23 (cut22 (cut21 (cut20 (cut19 (cut18 (cut17 (cut16 (cut15 (cut14 (cut13 (PEqualNP.Outside.L_meta_9752))))))))))))))))))))))))))))
end Minor9836
