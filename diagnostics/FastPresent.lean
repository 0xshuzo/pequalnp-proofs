import PEqualNP.Defs
namespace PCX150.FastPresent

def mark (m : Nat) : Nat := if m = 0 then 0 else 1

def three (m : Nat) : Nat :=
  mark (m &&& 3) + mark (m &&& 12) + mark (m &&& 48)

def lookup (x : Nat) := (0xfefefea9fefefea9fefefea9a9a9a954 >>> (2*(x%64))) % 4

theorem sixBits : ∀ r : Fin 64, lookup r.val = three r.val := by decide +kernel

theorem truncated (n x m : Nat) (hm : m < 2^n) :
    ((x % 2^n) &&& m) = x &&& m := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases sm : i < n
  · simp [Nat.testBit_and,Nat.testBit_mod_two_pow,sm]
  · have h := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm
         (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt sm)))
    simp [Nat.testBit_and,Nat.testBit_mod_two_pow,h]

theorem shifted (s x m : Nat) : (((x >>> s) &&& m) <<< s) = x &&& (m <<< s) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : s ≤ i
  · have back : s + (i-s) = i := by omega
    simp [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,h,back,
      Nat.add_comm (i-s) s]
  · simp [Nat.testBit_and,Nat.testBit_shiftLeft,h]

theorem markShift (x s m : Nat) :
    mark ((x >>> s) &&& m) = mark (x &&& (m <<< s)) := by
  rw [←shifted]
  simp [mark,Nat.shiftLeft_eq]

theorem lookup_correct (x s : Nat) :
    lookup (x >>> s) = mark (x &&& (3 <<< s)) +
      mark (x &&& (12 <<< s)) + mark (x &&& (48 <<< s)) := by
  let r : Fin 64 := ⟨(x >>> s) % 64, Nat.mod_lt _ (by decide)⟩
  have h := sixBits r
  change lookup ((x >>> s) % 64) = three ((x >>> s)%64) at h
  have idem (a : Nat) : lookup (a%64) = lookup a := by simp [lookup]
  rw [idem] at h
  rw [h,three]
  have bound (m : Nat) (small : m<64) : (((x>>>s)%64) &&& m) = (x>>>s) &&& m :=
    truncated 6 (x >>> s) m small
  rw [bound 3 (by decide),bound 12 (by decide),bound 48 (by decide),
      markShift,markShift,markShift]

def fast (x : Nat) : Nat :=
  mark (x &&& 63) + mark (x &&& 4032) + mark (x &&& 258048) + mark (x &&& 16515072) + lookup (x >>> 24) + lookup (x >>> 30) + lookup (x >>> 36) + lookup (x >>> 42) + lookup (x >>> 48) + lookup (x >>> 54)

def tags : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,13194139533312,52776558133248,211106232532992,844424930131968,3377699720527872,13510798882111488,54043195528445952,216172782113783808,864691128455135232]
def slow (m : Nat) : Nat :=
  (List.range 22).foldl (fun n k => if m &&& tags[k]! != 0 then n+1 else n) 0

theorem inc (m n : Nat) : (if m != 0 then n+1 else n) = n + mark m := by
  by_cases h : m=0 <;> simp [h,mark]

theorem exactFast (x : Nat) : fast x = slow x := by
  unfold fast slow
  rw [show List.range 22 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] by decide]
  simp only [lookup_correct,List.foldl_cons,List.foldl_nil,inc,Nat.zero_add,Nat.add_assoc]
  rfl

end PCX150.FastPresent
