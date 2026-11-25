import Mathlib
import PEqualNP.Outside.L_meta_1674
open PEqualNP.Outside.L_meta_1674
namespace Cache670
abbrev CachedPool := QS × List Nat
noncomputable def availFlag (s : QS) (x : Nat) : Nat :=
  (navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1 x).toNat
noncomputable def cacheSpec (s : QS) : CachedPool :=
  (s,s.2.2.2.2.2.1.map (availFlag s))
theorem cached_get (s : QS) (i : Nat) :
    (cacheSpec s).2.getD i (availFlag s 0) = availFlag s (s.2.2.2.2.2.1.getD i 0) := by
  simp only [cacheSpec,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases s.2.2.2.2.2.1[i]? <;> rfl
theorem flag_beq (x : Bool) : (x.toNat == 1) = x := by cases x <;> rfl
noncomputable def cachedCost (cs : CachedPool) (i j op : Nat) (ka kb : Bool) : Bool :=
  let s := cs.1
  let first := cs.2.getD i (availFlag s 0) == 1
  let second := cs.2.getD j (availFlag s 0) == 1
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond first 0 1)) (cond kb 0 (cond second 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and first second)))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem cached_eq (s : QS) (i j op : Nat) (ka kb : Bool) :
    cachedCost (cacheSpec s) i j op ka kb = fastCost s i j op ka kb := by
  simp only [cachedCost,fastCost,force_eq,show (cacheSpec s).1 = s from rfl,cached_get,availFlag,flag_beq]
end Cache670
