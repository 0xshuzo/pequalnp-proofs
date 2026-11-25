import Mathlib
import PEqualNP.Outside.L_meta_1674
open PEqualNP.Outside.L_meta_1674
namespace Mask670
def costBits (f : Nat → Bool) : List Nat → Nat
  | [] => 0
  | w::ws => 2^1*costBits f ws+(f w).toNat
theorem costBits_at (f : Nat → Bool) (zeroFlag : f 0=false) (ws : List Nat) (i : Nat) :
    (costBits f ws).testBit i = f (ws.getD i 0) := by
  induction ws generalizing i with
  | nil => simp [costBits,zeroFlag]
  | cons w ws ih =>
    have small : (f w).toNat < 2^1 := by cases f w <;> decide
    cases i with
    | zero =>
      rw [costBits,Nat.testBit_two_pow_mul_add _ small]
      change (if 0<1 then (f w).toNat.testBit 0 else _) = f w
      cases f w <;> rfl
    | succ i =>
      rw [costBits,Nat.testBit_two_pow_mul_add _ small]
      simp only [show ¬i+1<1 from by omega,ite_false]
      exact ih i
abbrev MaskPool := QS × Nat × Nat
noncomputable def missingCost (q : QS) (x : Nat) : Bool :=
  !(navail q.2.2.2.2.2.2.2 q.1 q.2.2.2.2.2.2.1 x)
def nonconstCost (q : QS) (x : Nat) : Bool := !(nconst q.1 x)
noncomputable def maskSpec (q : QS) : MaskPool :=
  (q,costBits (missingCost q) q.2.2.2.2.2.1,costBits (nonconstCost q) q.2.2.2.2.2.1)
theorem mask_missing (s : QS) (i : Nat) :
    (maskSpec s).2.1.testBit i = !(navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1 (s.2.2.2.2.2.1.getD i 0)) :=
  costBits_at (missingCost s) (by rfl) _ i
theorem mask_varies (s : QS) (i : Nat) :
    (maskSpec s).2.2.testBit i = !(nconst s.1 (s.2.2.2.2.2.1.getD i 0)) :=
  costBits_at (nonconstCost s) (by rfl) _ i
noncomputable def maskedCost (m : MaskPool) (i j op : Nat) (ka kb : Bool) : Bool :=
  let s := m.1
  let ax := !(m.2.1.testBit i)
  let ay := !(m.2.1.testBit j)
  let validRest := Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond ax 0 1)) (cond kb 0 (cond ay 0 1)))
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (cond ka 0 (cond (!(m.2.2.testBit i)) 1 0)))
      (cond kb 0 (cond (!(m.2.2.testBit j)) 1 0)))
  let lo := s.2.2.2.1
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  and validRest
    (cond (Nat.ble (Nat.succ lo) hi)
      (or (and (Nat.ble (Nat.add lo 2) hi) (and ax ay))
        (force (zN op (s.2.2.2.2.2.1.getD i 0) (s.2.2.2.2.2.1.getD j 0)) av))
      (cond (Nat.ble lo hi)
        (nconst s.1 (zN op (s.2.2.2.2.2.1.getD i 0) (s.2.2.2.2.2.1.getD j 0))) false))
theorem masked_eq (s : QS) (i j op : Nat) (ka kb : Bool) :
    maskedCost (maskSpec s) i j op ka kb = fastCost s i j op ka kb := by
  simp only [maskedCost,fastCost,force_eq,show (maskSpec s).1 = s from rfl,
    mask_missing,mask_varies,Bool.not_not,nloss,Bool.or_comm]
end Mask670
