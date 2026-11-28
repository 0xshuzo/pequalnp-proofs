import PEqualNP.Defs
namespace Plane9348.OddSixteen
open Finset
abbrev V := Fin 21
abbrev J := Fin 7
abbrev Box := Finset V × Finset V
def rows : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def black (r c : V) := (rows.getD r.val 0).testBit c.val
def cert : List (Nat × Nat) := [(1311239,48136), (1183848,311937), (36355,536604), (1179733,316672), (38028,335921), (1998912,6017), (700928,1237), (1115173,289032), (1122566,150568), (196905,805440), (87616,1310874), (1575240,152067), (411668,1085792), (541090,1247748), (270545,623874), (1606162,144516)]
def count (r c : V) := (cert.filter (fun p => p.1.testBit r.val && p.2.testBit c.val)).length
set_option maxHeartbeats 1600000 in
theorem witness : cert.length=16 ∧ ∀r c : V, (if black r c then count r c=0 else count r c % 2=1) := by decide +kernel
end Plane9348.OddSixteen
