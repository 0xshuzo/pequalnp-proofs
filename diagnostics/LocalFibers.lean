import PEqualNP.Defs
namespace Plane9341.Local
open Finset
abbrev V := Fin 21
abbrev F := Fin 48
def originCatalog : Array (Nat × Nat) := #[(1369,872450),(4157,385088),(9507,608268),(12359,115736),(20681,360978),(31233,32862),(33969,860420),(36355,536604),(50245,332056),(53537,328268),(67209,796690),(76865,540954),(102917,271448),(133195,578064),(139907,560148),(141361,573764),(147981,301136),(164625,791620),(196905,805440),(229569,788240),(262315,633344),(264729,569410),(270545,623874),(286757,100680),(295235,595464),(336641,527434),(362529,533320),(525327,96272),(536849,83014),(550017,67862),(561283,75284),(595977,25170),(706561,4948),(729093,19792),(803081,72258),(819221,79168),(1053329,304134),(1054755,57868),(1066753,268302),(1115173,289032),(1118529,280074),(1179733,316672),(1196193,297732),(1311239,48136),(1329217,37642),(1575953,28934),(1704195,24068),(1900673,12034)]
def rows : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def cb (i : F) := (originCatalog[i.val]!).2
def residual (a b : F) := 917342 ^^^ (cb a ||| cb b)
def count (n : Nat) := (univ.filter (fun j : V => n.testBit j.val=true)).card
def possible (m : Nat) := (univ.filter (fun i : V => (rows.getD i.val 0) &&& m=0)).card
def pairOK (a b : F) : Prop := 5≤count (residual a b) ∧
   (count (residual a b)=5 → possible (residual a b)=6)
instance (a b : F) : Decidable (pairOK a b) := by unfold pairOK;infer_instance
def gap (i j k:F) := 917342 ^^^ (cb i ||| cb j ||| cb k)
def tripleOK (i j k:F) := gap i j k=0 ∨ gap i j k &&& (gap i j k-1)≠0
instance (a b c:F) : Decidable (tripleOK a b c) := by unfold tripleOK;infer_instance
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p0 : ∀ b, pairOK 0 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t0 : ∀ b c,tripleOK 0 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p1 : ∀ b, pairOK 1 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t1 : ∀ b c,tripleOK 1 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p2 : ∀ b, pairOK 2 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t2 : ∀ b c,tripleOK 2 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p3 : ∀ b, pairOK 3 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t3 : ∀ b c,tripleOK 3 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p4 : ∀ b, pairOK 4 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t4 : ∀ b c,tripleOK 4 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p5 : ∀ b, pairOK 5 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t5 : ∀ b c,tripleOK 5 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p6 : ∀ b, pairOK 6 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t6 : ∀ b c,tripleOK 6 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p7 : ∀ b, pairOK 7 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t7 : ∀ b c,tripleOK 7 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p8 : ∀ b, pairOK 8 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t8 : ∀ b c,tripleOK 8 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p9 : ∀ b, pairOK 9 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t9 : ∀ b c,tripleOK 9 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p10 : ∀ b, pairOK 10 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t10 : ∀ b c,tripleOK 10 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p11 : ∀ b, pairOK 11 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t11 : ∀ b c,tripleOK 11 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p12 : ∀ b, pairOK 12 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t12 : ∀ b c,tripleOK 12 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p13 : ∀ b, pairOK 13 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t13 : ∀ b c,tripleOK 13 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p14 : ∀ b, pairOK 14 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t14 : ∀ b c,tripleOK 14 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p15 : ∀ b, pairOK 15 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t15 : ∀ b c,tripleOK 15 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p16 : ∀ b, pairOK 16 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t16 : ∀ b c,tripleOK 16 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p17 : ∀ b, pairOK 17 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t17 : ∀ b c,tripleOK 17 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p18 : ∀ b, pairOK 18 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t18 : ∀ b c,tripleOK 18 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p19 : ∀ b, pairOK 19 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t19 : ∀ b c,tripleOK 19 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p20 : ∀ b, pairOK 20 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t20 : ∀ b c,tripleOK 20 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p21 : ∀ b, pairOK 21 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t21 : ∀ b c,tripleOK 21 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p22 : ∀ b, pairOK 22 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t22 : ∀ b c,tripleOK 22 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p23 : ∀ b, pairOK 23 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t23 : ∀ b c,tripleOK 23 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p24 : ∀ b, pairOK 24 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t24 : ∀ b c,tripleOK 24 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p25 : ∀ b, pairOK 25 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t25 : ∀ b c,tripleOK 25 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p26 : ∀ b, pairOK 26 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t26 : ∀ b c,tripleOK 26 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p27 : ∀ b, pairOK 27 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t27 : ∀ b c,tripleOK 27 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p28 : ∀ b, pairOK 28 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t28 : ∀ b c,tripleOK 28 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p29 : ∀ b, pairOK 29 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t29 : ∀ b c,tripleOK 29 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p30 : ∀ b, pairOK 30 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t30 : ∀ b c,tripleOK 30 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p31 : ∀ b, pairOK 31 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t31 : ∀ b c,tripleOK 31 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p32 : ∀ b, pairOK 32 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t32 : ∀ b c,tripleOK 32 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p33 : ∀ b, pairOK 33 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t33 : ∀ b c,tripleOK 33 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p34 : ∀ b, pairOK 34 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t34 : ∀ b c,tripleOK 34 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p35 : ∀ b, pairOK 35 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t35 : ∀ b c,tripleOK 35 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p36 : ∀ b, pairOK 36 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t36 : ∀ b c,tripleOK 36 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p37 : ∀ b, pairOK 37 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t37 : ∀ b c,tripleOK 37 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p38 : ∀ b, pairOK 38 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t38 : ∀ b c,tripleOK 38 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p39 : ∀ b, pairOK 39 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t39 : ∀ b c,tripleOK 39 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p40 : ∀ b, pairOK 40 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t40 : ∀ b c,tripleOK 40 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p41 : ∀ b, pairOK 41 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t41 : ∀ b c,tripleOK 41 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p42 : ∀ b, pairOK 42 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t42 : ∀ b c,tripleOK 42 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p43 : ∀ b, pairOK 43 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t43 : ∀ b c,tripleOK 43 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p44 : ∀ b, pairOK 44 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t44 : ∀ b c,tripleOK 44 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p45 : ∀ b, pairOK 45 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t45 : ∀ b c,tripleOK 45 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p46 : ∀ b, pairOK 46 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t46 : ∀ b c,tripleOK 46 b c := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem p47 : ∀ b, pairOK 47 b := by decide +kernel
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem t47 : ∀ b c,tripleOK 47 b c := by decide +kernel
set_option maxHeartbeats 800000 in
theorem certifiedp (a b:F) : pairOK a b := by
  fin_cases a
  · exact p0 b
  · exact p1 b
  · exact p2 b
  · exact p3 b
  · exact p4 b
  · exact p5 b
  · exact p6 b
  · exact p7 b
  · exact p8 b
  · exact p9 b
  · exact p10 b
  · exact p11 b
  · exact p12 b
  · exact p13 b
  · exact p14 b
  · exact p15 b
  · exact p16 b
  · exact p17 b
  · exact p18 b
  · exact p19 b
  · exact p20 b
  · exact p21 b
  · exact p22 b
  · exact p23 b
  · exact p24 b
  · exact p25 b
  · exact p26 b
  · exact p27 b
  · exact p28 b
  · exact p29 b
  · exact p30 b
  · exact p31 b
  · exact p32 b
  · exact p33 b
  · exact p34 b
  · exact p35 b
  · exact p36 b
  · exact p37 b
  · exact p38 b
  · exact p39 b
  · exact p40 b
  · exact p41 b
  · exact p42 b
  · exact p43 b
  · exact p44 b
  · exact p45 b
  · exact p46 b
  · exact p47 b
set_option maxHeartbeats 800000 in
theorem certifiedt (a b c:F) : tripleOK a b c := by
  fin_cases a
  · exact t0 b c
  · exact t1 b c
  · exact t2 b c
  · exact t3 b c
  · exact t4 b c
  · exact t5 b c
  · exact t6 b c
  · exact t7 b c
  · exact t8 b c
  · exact t9 b c
  · exact t10 b c
  · exact t11 b c
  · exact t12 b c
  · exact t13 b c
  · exact t14 b c
  · exact t15 b c
  · exact t16 b c
  · exact t17 b c
  · exact t18 b c
  · exact t19 b c
  · exact t20 b c
  · exact t21 b c
  · exact t22 b c
  · exact t23 b c
  · exact t24 b c
  · exact t25 b c
  · exact t26 b c
  · exact t27 b c
  · exact t28 b c
  · exact t29 b c
  · exact t30 b c
  · exact t31 b c
  · exact t32 b c
  · exact t33 b c
  · exact t34 b c
  · exact t35 b c
  · exact t36 b c
  · exact t37 b c
  · exact t38 b c
  · exact t39 b c
  · exact t40 b c
  · exact t41 b c
  · exact t42 b c
  · exact t43 b c
  · exact t44 b c
  · exact t45 b c
  · exact t46 b c
  · exact t47 b c
end Plane9341.Local
