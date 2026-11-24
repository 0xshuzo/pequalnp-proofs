import PEqualNP.Defs
namespace Local4211

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (u v : Fin 26) : Bool :=
  if u.val < 13 then decide (13 ≤ v.val) && [0,1,3,9].contains ((u.val+26-v.val)%13)
  else decide (v.val < 13) && [0,1,3,9].contains ((v.val+26-u.val)%13)

def plane : SimpleGraph (Fin 26) where
  Adj u v := edge u v = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel plane.Adj := fun u v => inferInstanceAs (Decidable (edge u v = true))


end Local4211
namespace Geometry4678
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.HeptadCover PEqualNP.GenericRejection
open Local4211

abbrev L := singerLines3
abbrev edges := incidences L
def pt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
def ln (l : Fin 13) : Fin 26 := Fin.natAdd 13 l
def pair (u v : Fin 26) := List.ofFn (fun t : Fin 26 => decide (t=u ∨ t=v))
def flag (e : Fin 13 × Fin 13) := incidenceInput {e.1} {e.2}
def negative (Q : Finset (Fin 13)) := incidenceInput Q (missLines L Q)
def edgeOf (u v : Fin 26) : Fin 13 × Fin 13 :=
  if u.val<13 then (Fin.ofNat 13 u.val, Fin.ofNat 13 v.val) else (Fin.ofNat 13 v.val, Fin.ofNat 13 u.val)
def witnessMask : List (List Nat) := [
[39,39,39,29,83,39,71,135,275,533,1059,2055,4115,0,105,83,39,0,29,275,39,39,71,0,29,0],
[39,39,39,78,83,39,71,135,275,550,1059,2055,4115,0,0,83,39,78,0,275,39,39,71,142,0,58],
[39,39,39,29,29,39,71,135,270,533,1037,2055,4110,116,0,0,39,78,29,0,39,39,71,142,29,0],
[29,78,29,29,29,105,77,141,281,540,1037,2073,4137,0,105,0,0,78,29,281,0,77,29,142,29,58],
[83,83,29,29,83,58,83,154,275,533,1049,2067,4115,116,0,83,0,0,29,275,83,0,83,58,29,58],
[39,39,39,105,58,39,101,166,297,549,1059,2083,4131,116,105,0,39,0,0,1059,39,39,0,166,101,58],
[71,71,71,77,83,101,71,195,329,593,1098,2118,4163,116,105,83,0,78,0,0,71,71,71,0,77,202],
[135,135,135,141,154,166,195,135,387,897,1155,2181,4233,404,201,195,135,0,141,0,0,135,135,142,0,154],
[275,275,270,281,275,297,329,387,275,801,1283,2307,4362,308,297,275,387,270,0,275,0,0,275,270,281,0],
[533,550,533,540,533,549,593,897,801,533,1541,2565,4625,0,609,593,549,774,533,0,533,0,0,550,533,562],
[1059,1059,1037,1037,1049,1059,1098,1155,1283,1541,1059,3082,5123,1124,0,1155,1059,1098,1037,1059,0,1059,0,0,1037,1066],
[2055,2055,2055,2073,2067,2083,2118,2181,2307,2565,3082,2055,6153,2132,2185,0,2055,2118,2069,2067,2055,0,2055,0,0,2074],
[4115,4115,4110,4137,4115,4131,4163,4233,4362,4625,5123,6153,4115,4148,4137,4115,0,4110,4233,4115,4115,4131,0,4110,0,0],
[0,0,116,0,116,116,116,404,308,0,1124,2132,4148,116,2272,464,420,1348,2196,1328,116,1124,340,308,116,1136],
[105,0,0,105,0,105,105,201,297,609,0,2185,4137,2272,105,449,801,840,2185,297,609,105,201,680,105,232],
[83,83,0,0,83,0,83,195,275,593,1155,0,4115,464,449,83,387,1602,1553,275,83,195,83,402,337,210],
[39,39,39,0,0,39,0,135,387,549,1059,2055,0,420,801,387,39,774,1157,1059,39,39,135,166,549,674],
[0,78,78,78,0,0,78,0,270,774,1098,2118,4110,1348,840,1602,774,78,1548,2314,2118,78,78,270,332,1098],
[29,0,29,29,29,0,0,141,0,533,1037,2069,4233,2196,2185,1553,1157,1548,29,1049,533,141,29,156,29,664],
[275,275,0,281,275,1059,0,0,275,0,1059,2067,4115,1328,297,275,1059,2314,1049,275,2067,1059,275,58,281,58],
[39,39,39,0,83,39,71,0,0,533,0,2055,4115,116,609,83,39,2118,533,2067,39,39,71,550,85,562],
[39,39,39,77,0,39,71,135,0,0,1059,0,4131,1124,105,195,39,78,141,1059,39,39,71,142,77,170],
[71,71,71,29,83,0,71,135,275,0,0,2055,0,340,201,83,135,78,29,275,71,71,71,142,29,154],
[0,142,142,142,58,166,0,142,270,550,0,0,4110,308,680,402,166,270,156,58,550,142,142,142,284,58],
[29,0,29,29,29,101,77,0,281,533,1037,0,0,116,105,337,549,332,29,281,85,77,29,284,29,568],
[0,58,0,58,58,58,202,154,0,562,1066,2074,0,1136,232,210,674,1098,664,58,562,170,154,58,568,58]]

def wQ (u v : Fin 26) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => (((witnessMask.getD u.val []).getD v.val 0).testBit p.val))
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem negRows : ∀ u v : Fin 26, ¬plane.Adj u v →
    IsQuadrangle L (wQ u v) ∧
    (negative (wQ u v)).getD u.val false=true ∧ (negative (wQ u v)).getD v.val false=true := by
  intro u; fin_cases u <;> decide +kernel
theorem posRows : ∀ u v : Fin 26, plane.Adj u v → edgeOf u v∈edges ∧ pair u v=flag (edgeOf u v) := by
  intro u; fin_cases u <;> decide +kernel
theorem edgeInc : ∀ e : Fin 13 × Fin 13, e∈edges ↔ e.1∈L e.2 := by decide
theorem fLength (e : Fin 13 × Fin 13) : (flag e).length=26 := by simp [flag,incidenceInput]
theorem pLength (u v : Fin 26) : (pair u v).length=26 := by simp [pair]
theorem nLength (Q : Finset (Fin 13)) : (negative Q).length=26 := by simp [negative,incidenceInput]
theorem readPair (u v i : Fin 26) : (pair u v).getD i.val false=decide (i=u ∨ i=v) := by simp [pair]
theorem hitFlag : ∀ e d : Fin 13 × Fin 13, ((flag e).getD (pt d.1).val false && (flag e).getD (ln d.2).val false)=decide (e=d) := by
  intro e
  obtain ⟨p,l⟩ := e
  fin_cases p <;> decide +kernel
theorem absent : ∀ u v : Fin 26, ¬plane.Adj u v → ∀ e∈edges,
    ((pair u v).getD (pt e.1).val false && (pair u v).getD (ln e.2).val false)=false := by
  intro u; fin_cases u <;> decide +kernel

end Geometry4678
