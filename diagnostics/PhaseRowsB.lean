import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9750.PhaseRows

-- Each binary gate with free phases has the same separating rows as one of the
-- four tests for a single input cell. OR corresponds to the complement of 00.
def polarity (p a : Bool) : Bool := if p then a else !a
def gateCell (p q a b : Bool) : Bool := polarity p a && polarity q b
def takeBit (keep a : Bool) : Bool := if keep then a else false

theorem row_formula : ∀ p q ka kb other ap an bp bn : Bool,
    (!(other || takeBit ka (Bool.xor ap an) || takeBit kb (Bool.xor bp bn) ||
      (Bool.xor (gateCell p q ap bp) (gateCell p q an bn)))) =
    (!(other || (Bool.xor ap an) || (Bool.xor bp bn)) ||
      takeBit (!ka) (!other && (Bool.xor ap an) && !(Bool.xor bp bn) && !polarity q bp) ||
      takeBit (!kb) (!other && !(Bool.xor ap an) && (Bool.xor bp bn) && !polarity p ap) ||
      takeBit (!(ka || kb)) (!other && (Bool.xor ap an) && (Bool.xor bp bn) &&
        !polarity (Bool.xor p q) (Bool.xor ap bp))) := by decide

def polar {w} (p : Bool) (a : BitVec w) := if p then a else ~~~a
def kept {w} (keep : Bool) (a : BitVec w) := if keep then a else 0
def cell {w} (p q : Bool) (a b : BitVec w) := polar p a &&& polar q b

theorem polar_bit {w} (p : Bool) (a : BitVec w) (i : Nat) (h : i < w) :
    (polar p a).getLsbD i = polarity p (a.getLsbD i) := by
  cases p <;> simp [polar,polarity,BitVec.getLsbD_not,h]

theorem kept_bit {w} (k : Bool) (a : BitVec w) (i : Nat) :
    (kept k a).getLsbD i = takeBit k (a.getLsbD i) := by
  cases k <;> simp [kept,takeBit,BitVec.getLsbD_zero]

-- 'other' marks rows separated by the live wires other than the selected pair.
-- The four terms on the right respectively cover missing, A-only, B-only and
-- A-and-B rows. If both wires change, their parity decides the permitted cells.
theorem missing_rows {w} (p q ka kb : Bool) (other ap an bp bn : BitVec w) :
    ~~~(other ||| kept ka (ap ^^^ an) ||| kept kb (bp ^^^ bn) |||
        (cell p q ap bp ^^^ cell p q an bn)) =
      (~~~(other ||| (ap ^^^ an) ||| (bp ^^^ bn)) |||
       kept (!ka) (~~~other &&& (ap ^^^ an) &&& ~~~(bp ^^^ bn) &&& ~~~polar q bp) |||
       kept (!kb) (~~~other &&& ~~~(ap ^^^ an) &&& (bp ^^^ bn) &&& ~~~polar p ap) |||
       kept (!(ka || kb)) (~~~other &&& (ap ^^^ an) &&& (bp ^^^ bn) &&&
         ~~~polar (Bool.xor p q) (ap ^^^ bp))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [cell,kept_bit,polar_bit _ _ _ hi,BitVec.getLsbD_or,BitVec.getLsbD_and,
    BitVec.getLsbD_xor,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  exact row_formula p q ka kb (other.getLsbD i) (ap.getLsbD i) (an.getLsbD i)
    (bp.getLsbD i) (bn.getLsbD i)

end PEqualNP.Outside.L_meta_9750.PhaseRows
