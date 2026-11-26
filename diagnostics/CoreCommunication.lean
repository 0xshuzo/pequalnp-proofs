import PEqualNP.Defs
namespace Plane9759Core
set_option maxHeartbeats 0
def core (p l : Nat) : Bool := (p.testBit 0 && l.testBit 0) || (p.testBit 1 && l.testBit 0) || (p.testBit 0 && l.testBit 1) || (p.testBit 2 && l.testBit 1) || (p.testBit 1 && l.testBit 2) || (p.testBit 2 && l.testBit 2) || (p.testBit 0 && l.testBit 3) || (p.testBit 3 && l.testBit 3) || (p.testBit 1 && l.testBit 4) || (p.testBit 3 && l.testBit 4) || (p.testBit 0 && l.testBit 5) || (p.testBit 4 && l.testBit 5) || (p.testBit 1 && l.testBit 6) || (p.testBit 4 && l.testBit 6) || (p.testBit 2 && l.testBit 7) || (p.testBit 3 && l.testBit 7) || (p.testBit 4 && l.testBit 7)
def help (l : Nat) : Nat := (1 * ((l.testBit 2 || l.testBit 3).toNat)) + (2 * ((l.testBit 1 || l.testBit 4).toNat)) + (4 * ((l.testBit 2 || l.testBit 5).toNat)) + (8 * ((l.testBit 4 || l.testBit 5).toNat)) + (16 * ((l.testBit 1 || l.testBit 6).toNat)) + (32 * ((l.testBit 3 || l.testBit 6).toNat)) + (64 * ((l.testBit 0 || l.testBit 7).toNat))
def lines : Fin 6 → Nat := ![30, 42, 126, 84, 102, 120]
def points : Fin 7 → Nat := ![0, 1, 2, 4, 8, 16, 31]
def pt : Fin 17 → Nat := ![0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 3, 4]
def ln : Fin 17 → Nat := ![5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 12]
def no : Fin 17 → Nat := ![4162, 4225, 2596, 2689, 1316, 1346, 2280, 2689, 1256, 1346, 1008, 2689, 1008, 1346, 3304, 3876, 3876]
def yes : Fin 17 → Nat := ![4129, 4194, 2625, 2660, 1410, 1412, 2433, 2536, 1602, 1608, 1665, 2032, 2370, 2384, 4132, 4136, 4144]

def f (r : Nat) : Bool := core (r%32) (r/32)
def wire (r : Nat) (j : Fin 20) : Bool :=
  if j.val < 13 then r.testBit j.val else (help (r/32)).testBit (j.val-13)
def toggle (r j : Nat) : Nat := r ^^^ 2^j
def force (r k : Nat) (out : Bool) : Prop :=
  f r = out ∧ f (toggle r k) = !out ∧ r.testBit k = out ∧
  ∀ j : Fin 20, (wire r j != wire (toggle r k) j) = decide (j.val=k)

theorem allSeventeen : ∀ i : Fin 17,
    force (yes i) (pt i) true ∧ force (yes i) (ln i) true ∧
    force (no i) (pt i) false ∧ force (no i) (ln i) false := by
  unfold force; decide +kernel

theorem sameHelp : ∀ i : Fin 6, help (lines i) = 63 := by decide +kernel
theorem distinguishLines : ∀ (i j : Fin 6), i ≠ j → ∃ k : Fin 7,
    core (points k) (lines i) ≠ core (points k) (lines j) := by decide +kernel
theorem distinguishPoints : ∀ (i j : Fin 7), i ≠ j → ∃ k : Fin 6,
    core (points i) (lines k) ≠ core (points j) (lines k) := by decide +kernel

theorem line_message {k : Nat} (encode : Nat → Fin k) (decode : Fin k → Nat → Nat → Bool)
    (h : ∀ p l, decode (encode l) (help l) p = core p l) : 6 ≤ k := by
  have inj : Function.Injective (fun i : Fin 6 => encode (lines i)) := by
    intro i j eq
    by_contra ne
    obtain ⟨r,raw⟩ := distinguishLines i j ne
    apply raw
    rw [← h,← h,sameHelp,sameHelp]
    exact congrArg (fun (v : Fin k) => decode v 63 (points r)) eq
  simpa using Fintype.card_le_of_injective _ inj

theorem point_message {k : Nat} (encode : Nat → Nat → Fin k) (decode : Fin k → Nat → Bool)
    (h : ∀ p l, decode (encode p (help l)) l = core p l) : 7 ≤ k := by
  have inj : Function.Injective (fun i : Fin 7 => encode (points i) 63) := by
    intro i j eq
    by_contra ne
    obtain ⟨r,raw⟩ := distinguishPoints i j ne
    apply raw
    rw [← h,← h,sameHelp]
    exact congrArg (fun (v : Fin k) => decode v (lines r)) eq
  simpa using Fintype.card_le_of_injective _ inj

end Plane9759Core
