import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2374

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def wires (g : Gate) (C : Circuit) (x : Fin 10 → Bool) (i : Nat) :=
  (C.wires ((⟨[g],0⟩ : Circuit).wires (List.ofFn x))).getD i false

def Cover (k : Nat) := ∃ g : Gate, ∃ C : Circuit, ∃ a b : Nat,
    FanInTwo (⟨[g],0⟩ : Circuit) ∧ FanInTwo C ∧ C.size≤k ∧
    (∃ x, wires g C x a=true ∧ wires g C x b=false) ∧
    (∃ x, wires g C x a=false ∧ wires g C x b=true) ∧
    ∀ x, (wires g C x a || wires g C x b)=target x

theorem literal_iff : (¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false)) ↔ Cover 17 := by

  classical
  change (¬ ∀ g C a b, FanInTwo (⟨[g],0⟩ : Circuit) → FanInTwo C → C.size≤17 →
    (∃ x, wires g C x a=true ∧ wires g C x b=false) →
    (∃ x, wires g C x a=false ∧ wires g C x b=true) →
    (∀ x, target x=false → wires g C x a=false ∧ wires g C x b=false) →
    ∃ x, target x=true ∧ wires g C x a=false ∧ wires g C x b=false) ↔ _
  constructor
  · intro h
    by_contra bad
    apply h
    intro g C a b legal tail budget left right safe
    by_contra miss
    apply bad
    refine ⟨g,C,a,b,legal,tail,budget,left,right,?_⟩
    intro x
    cases ht : target x with
    | false =>
      obtain ⟨ha,hb⟩ := safe x ht
      simp [ha,hb]
    | true =>
      by_cases ha : wires g C x a=true
      · simp [ha]
      by_cases hb : wires g C x b=true
      · simp [hb]
      exact False.elim (miss ⟨x,ht,Bool.eq_false_iff.mpr ha,Bool.eq_false_iff.mpr hb⟩)
  · rintro ⟨g,C,a,b,legal,tail,budget,left,right,all⟩ h
    have safe (x) (hz : target x=false) : wires g C x a=false ∧ wires g C x b=false := by
      have e := (all x).trans hz
      cases ha : wires g C x a <;> cases hb : wires g C x b <;> simp_all
    obtain ⟨x,ht,ha,hb⟩ := h g C a b legal tail budget left right safe
    have e := all x
    simp [ht,ha,hb] at e

def firstGate : Gate := ⟨.or,[2,6]⟩
def tailNet : Circuit := ⟨[⟨.and,[1,10]⟩,
  ⟨.or,[1,4]⟩,
  ⟨.or,[12,5]⟩,
  ⟨.and,[0,13]⟩,
  ⟨.or,[2,4]⟩,
  ⟨.or,[15,8]⟩,
  ⟨.and,[3,16]⟩,
  ⟨.or,[2,5]⟩,
  ⟨.or,[18,9]⟩,
  ⟨.and,[7,19]⟩,
  ⟨.or,[5,6]⟩,
  ⟨.and,[8,21]⟩,
  ⟨.or,[4,6]⟩,
  ⟨.and,[9,23]⟩,
  ⟨.or,[14,17]⟩,
  ⟨.or,[25,20]⟩,
  ⟨.or,[26,22]⟩,
  ⟨.or,[27,24]⟩],28⟩

def pins (x : Fin 10 → Bool) : List Bool := [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9]

theorem pinList (x : Fin 10 → Bool) : List.ofFn x = pins x := by
  apply List.ext_getElem
  · simp [pins]
  · intro i hi hj
    have bound : i<10 := by simpa [pins] using hj
    interval_cases i <;> rfl

theorem physical : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    let w := tailNet.wires ((⟨[firstGate],0⟩ : Circuit).wires [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9])
    (w.getD 11 false || w.getD 28 false)=((b0 && b1) || (b1 && b2) || (b2 && b3) || (b3 && b4) || (b4 && b0) || (b0 && b5) || (b1 && b6) || (b2 && b7) || (b3 && b8) || (b4 && b9) || (b5 && b7) || (b7 && b9) || (b9 && b6) || (b6 && b8) || (b8 && b5)) := by
  decide +kernel

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem checkedFan (C : Circuit) (legal : C.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true) : FanInTwo C := by
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,passed.2⟩

theorem near : Cover 18 := by
  refine ⟨firstGate,tailNet,11,28,?_,?_,?_,?_,?_,?_⟩
  · exact checkedFan _ (by decide +kernel)
  · exact checkedFan _ (by decide +kernel)
  · decide +kernel
  · refine ⟨(fun i => decide (i.val=1 ∨ i.val=2)),?_⟩
    decide +kernel
  · refine ⟨(fun i => decide (i.val=0 ∨ i.val=1)),?_⟩
    decide +kernel
  · intro x
    unfold wires target
    rw [pinList]
    exact physical (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)

end PEqualNP.Outside.L_meta_2374
