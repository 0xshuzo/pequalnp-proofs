import PEqualNP.Defs
namespace Plane9348.StarPatch
open Finset
abbrev V := Fin 21
abbrev J := Fin 7
abbrev Box := Finset V × Finset V
def rows : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def black (r c : V) := (rows.getD r.val 0).testBit c.val
def weight3 : List Nat := [0, 595464, 271448, 0, 569410, 74433, 0, 360978, 595464, 0, 790673, 569410, 0, 33931, 360978, 0, 271448, 790673, 0, 74433, 33931]
def weight2 : List Nat := [0, 41104, 102401, 0, 328832, 819208, 0, 533505, 262211, 0, 73738, 537, 0, 589904, 4296, 0, 524930, 34368, 0, 5138, 274944]
def weight (r c : V) : Nat :=
 if (weight3.getD r.val 0).testBit c.val then 3 else if (weight2.getD r.val 0).testBit c.val then 2 else 0
def ink (s : Bool) (r c : V) := if s then black c r else black r c
def price (s : Bool) (r c : V) := if s then weight c r else weight r c
def marks (s : Bool) (i : J) : Nat :=
 if s then ([37377, 299016, 294977, 262665, 4169, 33352, 266816] : List Nat).getD i.val 0 else ([18692, 149536, 1196288, 1181700, 1064996, 131364, 1050912] : List Nat).getD i.val 0
def anchor (s : Bool) (i : J) : Finset V := univ.filter fun c : V => (marks s i).testBit c.val
def allowed (s : Bool) (i : J) := univ.filter fun r : V => ∀c∈anchor s i,ink s r c=false
def other (s : Bool) (R : Finset V) := univ.filter fun c : V => ∀r∈R,ink s r c=false
def value (s : Bool) (R C : Finset V) := ∑r∈R,∑c∈C,price s r c
def audit (s : Bool) (i : J) : Prop :=
 ∀R∈(allowed s i).powerset,value s R (other s R)≤24
instance (s i) : Decidable (audit s i) := by unfold audit; infer_instance
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem cfalse0 : audit false 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem cfalse1 : audit false 1 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem cfalse2 : audit false 2 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem cfalse3 : audit false 3 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem cfalse4 : audit false 4 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem cfalse5 : audit false 5 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem cfalse6 : audit false 6 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem ctrue0 : audit true 0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem ctrue1 : audit true 1 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem ctrue2 : audit true 2 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem ctrue3 : audit true 3 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem ctrue4 : audit true 4 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem ctrue5 : audit true 5 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem ctrue6 : audit true 6 := by decide +kernel

theorem checked (s : Bool) (i : J) : audit s i := by
  cases s <;> fin_cases i <;> first | assumption | exact cfalse0 | exact cfalse1 | exact cfalse2 | exact cfalse3 | exact cfalse4 | exact cfalse5 | exact cfalse6 | exact ctrue0 | exact ctrue1 | exact ctrue2 | exact ctrue3 | exact ctrue4 | exact ctrue5 | exact ctrue6
theorem cap (s : Bool) (i : J) (R C : Finset V)
    (valid : ∀r∈R,∀c∈C,ink s r c=false) (anchored : anchor s i ⊆ C) :
    value s R C ≤ 24 := by
  have rowBound : R ⊆ allowed s i := by
    intro r hr
    exact mem_filter.mpr ⟨mem_univ _,fun c hc => valid r hr c (anchored hc)⟩
  have cols : C ⊆ other s R := by
    intro c hc
    exact mem_filter.mpr ⟨mem_univ _,fun r hr => valid r hr c hc⟩
  apply le_trans _ ((checked s i) R (mem_powerset.mpr rowBound))
  apply sum_le_sum
  intro r _
  exact sum_le_sum_of_subset_of_nonneg cols (fun _ _ _ => Nat.zero_le _)
theorem amount : value false univ univ = 364 := by decide +kernel
theorem support : ∀r c : V, 0<weight r c → black r c=false := by decide +kernel
end Plane9348.StarPatch
