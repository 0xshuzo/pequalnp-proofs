import PEqualNP.Defs

namespace BlockQuotaDigits

def bit (b : Bool) : ℕ := if b then 1 else 0
def nand (x y : Bool) : Bool := !(x && y)

def fa (x y z : Bool) : Bool × Bool :=
  let t := nand x y
  let u := nand x t
  let v := nand y t
  let p := nand u v
  let a := nand p z
  let b := nand p a
  let c := nand z a
  (nand b c, nand t a)

theorem nand_clauses (x y z : Bool) :
    z = nand x y ↔ (z = false ∨ x = false ∨ y = false) ∧
      (z = true ∨ x = true) ∧ (z = true ∨ y = true) := by
  cases x <;> cases y <;> cases z <;> decide

theorem fa_total (x y z : Bool) :
    bit (fa x y z).1 + 2 * bit (fa x y z).2 = bit x + bit y + bit z := by
  cases x <;> cases y <;> cases z <;> decide

def add4 (a b c d : Bool) (st : Bool × Bool × Bool) : Bool × (Bool × Bool × Bool) :=
  let p := fa a b st.1
  let q := fa c d st.2.1
  let r := fa p.1 q.1 st.2.2
  (r.1,p.2,q.2,r.2)

def wt (s : Bool × Bool × Bool) := bit s.1 + bit s.2.1 + bit s.2.2

theorem add4_balance (a b c d : Bool) (s : Bool × Bool × Bool) :
    bit (add4 a b c d s).1 + 2 * wt (add4 a b c d s).2 =
    bit a + bit b + bit c + bit d + wt s := by
  have p := fa_total a b s.1
  have q := fa_total c d s.2.1
  have r := fa_total (fa a b s.1).1 (fa c d s.2.1).1 s.2.2
  simp only [add4,wt]
  omega

theorem interchange (a b c d : Bool) (s t : Bool × Bool × Bool) (h : wt s = wt t) :
    (add4 a b c d s).1 = (add4 a c b d t).1 ∧
      wt (add4 a b c d s).2 = wt (add4 a c b d t).2 := by
  have h₁ := add4_balance a b c d s
  have h₂ := add4_balance a c b d t
  cases hx : (add4 a b c d s).1 <;> cases hy : (add4 a c b d t).1 <;>
    simp only [hx,hy,bit,Bool.false_eq_true,if_false,if_true] at h₁ h₂ <;>
    constructor <;> first | rfl | omega

def lowLt (old x k : Bool) := if x == k then old else k

def inv (d e g cin kin : Bool) : Prop :=
  bit kin + bit g ≤ bit cin + bit d + bit e

theorem compareStep (d e g x y r s cin kin : Bool)
    (h : inv d e g cin kin) :
    inv (lowLt d x r) (lowLt e y s) (lowLt g (fa x y cin).1 (fa r s kin).1)
      (fa x y cin).2 (fa r s kin).2 := by
  revert h
  revert kin cin s r y x g e d
  unfold inv
  decide

theorem compareEnd (g : Bool) (h : inv false false g false false) : g = false := by
  cases g <;> simp_all [inv,bit]

theorem lowLt_spec (u v w : ℕ) (U V : Bool) (hu : u < w) (hv : v < w) :
    lowLt (decide (u < v)) U V =
      decide (u + w*bit U < v + w*bit V) := by
  cases U <;> cases V <;> simp [lowLt,bit] <;> omega

end BlockQuotaDigits
