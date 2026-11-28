import PEqualNP.Defs
namespace Plane9341.Fiber
def shape : Array (Nat×Nat) := #[(1, 16),(2, 12),(3, 8),(3, 9),(4, 4),(4, 6),(4, 7),(5, 5),(6, 4),(7, 4),(8, 3),(9, 3),(12, 2),(16, 1)]
abbrev S := Fin 14
def entry (i:S) := shape[i.val]!
def rate (c:Nat) := if c≤1 then 4 else if c≤4 then 3 else if c≤9 then 2 else if c≤15 then 1 else 0
def sharp (r c:Nat) := if r=5 ∧ c=5 then 3 else if r=2 ∧ c=12 then 2 else rate c
def fee (r c s d i j:Nat) := 4*(21+i-r-s)+(r-i)*sharp r c+(s-i)*sharp s d+i*rate (c+d-j)
def good (a b:S) (i j : Fin 17) : Prop :=
  let (r,c):=entry a
  let (s,d):=entry b
  i.val≤min r s → j.val≤min c d → r+s≤21+i.val → c+d≤21+j.val →
    68≤max (fee r c s d i.val j.val) (fee c r d s j.val i.val)
instance decGood (a b : S) (i j : Fin 17) : Decidable (good a b i j) := by
  unfold good
  infer_instance
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price0 : ∀ b i j, good 0 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price1 : ∀ b i j, good 1 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price2 : ∀ b i j, good 2 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price3 : ∀ b i j, good 3 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price4 : ∀ b i j, good 4 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price5 : ∀ b i j, good 5 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price6 : ∀ b i j, good 6 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price7 : ∀ b i j, good 7 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price8 : ∀ b i j, good 8 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price9 : ∀ b i j, good 9 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price10 : ∀ b i j, good 10 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price11 : ∀ b i j, good 11 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price12 : ∀ b i j, good 12 b i j := by decide +kernel
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem price13 : ∀ b i j, good 13 b i j := by decide +kernel
theorem allPrices (a b:S) (i j : Fin 17) : good a b i j := by
  fin_cases a
  · exact price0 b i j
  · exact price1 b i j
  · exact price2 b i j
  · exact price3 b i j
  · exact price4 b i j
  · exact price5 b i j
  · exact price6 b i j
  · exact price7 b i j
  · exact price8 b i j
  · exact price9 b i j
  · exact price10 b i j
  · exact price11 b i j
  · exact price12 b i j
  · exact price13 b i j

theorem requiresPencil (a b:S) (i j : Fin 17)
    (rows : (entry a).1+(entry b).1≤21+i.val)
    (cols : (entry a).2+(entry b).2≤21+j.val)
    (lo : i.val≤min (entry a).1 (entry b).1) (ro : j.val≤min (entry a).2 (entry b).2)
    (noPencil : Prop)
    (rowFees : noPencil → fee (entry a).1 (entry a).2 (entry b).1 (entry b).2 i.val j.val≤66)
    (colFees : noPencil → fee (entry a).2 (entry a).1 (entry b).2 (entry b).1 j.val i.val≤66) :
    ¬noPencil := by
  intro np
  have h:=allPrices a b i j
  change i.val≤min (entry a).1 (entry b).1 → j.val≤min (entry a).2 (entry b).2 →
     (entry a).1+(entry b).1≤21+i.val → (entry a).2+(entry b).2≤21+j.val → _ at h
  have lower:=h lo ro rows cols
  have upper:=max_le (rowFees np) (colFees np)
  omega
end Plane9341.Fiber
