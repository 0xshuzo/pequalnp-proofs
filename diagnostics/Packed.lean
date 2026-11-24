import Mathlib

namespace PetersenPacked

abbrev W := BitVec 29
abbrev Mask := BitVec 208

def packed (w : W) : Mask :=
  let col : Mask := w.setWidth 208
  let p0 := col &&& 65535
  let p1 := (p0 ||| (p0 <<< 96)) &&& 0xff000000000000000000000000ff
  let p2 := (p1 ||| (p1 <<< 48)) &&& 0xf000000000000f000000000000f000000000000f
  let p3 := (p2 ||| (p2 <<< 24)) &&& 0xc000003000000c000003000000c000003000000c000003
  let p4 := (p3 ||| (p3 <<< 12)) &&& 0x8004002001000800400200100080040020010008004002001
  (p4 * 8191) &&& (((~~~col >>> 16) &&& 8191) * 0x8004002001000800400200100080040020010008004002001)

def block (w : W) (p : Nat) : BitVec 13 :=
  if w.getLsbD p = true then ~~~(w.extractLsb' 16 13) else 0

def direct (w : W) : Mask :=
  block w 15 ++ block w 14 ++ block w 13 ++ block w 12 ++ block w 11 ++ block w 10 ++ block w 9 ++ block w 8 ++ block w 7 ++ block w 6 ++ block w 5 ++ block w 4 ++ block w 3 ++ block w 2 ++ block w 1 ++ block w 0

set_option maxHeartbeats 4000000 in
lemma packed_eq (w : W) : packed w = direct w := by
  unfold packed direct block
  bv_decide

set_option maxHeartbeats 4000000 in
lemma bit_packed (w : W) (p : Fin 16) (n : Fin 13) :
    (packed w).getLsbD (p.val * 13 + n.val) = (w.getLsbD p.val && !(w.getLsbD (n.val+16))) := by
  rw [packed_eq]
  fin_cases p <;> fin_cases n <;> unfold direct block <;> bv_decide

def coverage : List W → Mask
  | [] => 0
  | w::xs => packed w ||| coverage xs

lemma coverage_bits (xs : List W) (p : Fin 16) (n : Fin 13) :
    (coverage xs).getLsbD (p.val * 13 + n.val) =
      xs.any (fun w => w.getLsbD p.val && !(w.getLsbD (n.val + 16))) := by
  induction xs with
  | nil => rfl
  | cons w xs ih => simp only [coverage, List.any_cons, BitVec.getLsbD_or, bit_packed, ih]

lemma coverage_full (xs : List W) (h : ∀ p : Fin 16, ∀ n : Fin 13,
    xs.any (fun w => w.getLsbD p.val && !(w.getLsbD (n.val + 16))) = true) :
    coverage xs = BitVec.allOnes 208 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let p : Fin 16 := ⟨i / 13, by omega⟩
  let n : Fin 13 := ⟨i % 13, by omega⟩
  have eq : p.val * 13 + n.val = i := by dsimp [p,n];omega
  rw [← eq, coverage_bits, h, BitVec.getLsbD_allOnes, eq]
  simp [hi]

end PetersenPacked
