import Mathlib

namespace PetersenLive

def catalogue : List Nat := [3,414,445,901,902,903,905,908,912,913,915,918,923,925,928,935,938,958,1112,1113,1115,1116,1117,1118,1123,1125,1126,1127,1128,1135,1136,1137,1138,1156,1157,1158,1167,1168,1178]

def witnesses : List (Nat × Nat) := [(261,277),(50,51),(42,46),(42,106),(42,170),(42,298),(261,325),(261,389),(50,58),(52,54),(69,325),(261,269),(193,209),(274,306),(276,277),(69,101),(73,75),(385,389),(42,58),(68,196),(136,168),(385,387),(208,209),(208,216),(9,25),(10,11),(72,76),(130,194),(136,392)]

def restrictions : List (Nat × Nat × Nat) := [(0,9,3),(1,9,3),(2,9,3),(3,9,3),(4,9,2),(5,9,3),(6,9,2),(7,9,2),(8,9,3),(0,4,4),(1,6,4),(2,7,4),(3,4,4),(4,6,4),(4,7,4),(5,7,4),(6,7,4),(6,8,4)]

def vertexMask (i : Nat) : Nat := (1 <<< i) &&& 511

def target (x : Nat) : Bool :=
  ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
    (fun e => x.testBit (e / 10) && x.testBit (e % 10))

def signals (q x : Nat) : Nat := x |||
  (if x &&& 17 != 0 then 512 else 0) |||
  (if x &&& q != 0 then 1024 else 0)

def digit (b : Bool) : Nat := if b then 1 else 0

def small (m : Nat) : Bool := m &&& (m-1) == 0

def budget (q L : Nat) (z : Nat × Nat × Nat) : Bool :=
  let a := z.1
  let b := z.2.1
  let keep := 511 ^^^ (vertexMask a ||| vertexMask b)
  let p' := 17 &&& keep
  let q' := q &&& keep
  let pLive := L.testBit 9
  let qLive := L.testBit 10
  let removed := digit (!pLive || small p') + digit (!qLive || small q' || (pLive && (p' == q')))
  let constants := digit (L.testBit a) + digit (decide (b < 9) && L.testBit b) +
    digit (pLive && (p' == 0)) + digit (qLive && (q' == 0))
  decide (removed + constants ≤ z.2.2)

def maskCode (a b L : Nat) : Nat :=
  let d := if L = 2047 then 11 else if L = 1535 then 9 else if L = 2031 then 4
    else if L = 2046 then 0 else 99
  100*d+10*a+b

def admissible (a b L : Nat) : Bool :=
  let q := vertexMask a ||| vertexMask b
  let must := 511 ^^^ (17 ||| q)
  ((L &&& must) == must) &&
    witnesses.all (fun t => (signals q t.1 &&& L) != (signals q t.2 &&& L)) &&
    restrictions.all (budget q L)

def check (a b L : Nat) : Bool :=
  !admissible a b L || catalogue.contains (maskCode a b L)

lemma witnesses_flip : witnesses.all (fun t => target t.1 != target t.2) = true := by decide +kernel

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

lemma span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

def row (a b : Nat) := span (check a b) 2048 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_0 : row 0 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_1 : row 0 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_2 : row 0 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_3 : row 0 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_4 : row 0 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_5 : row 0 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_6 : row 0 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_7 : row 0 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_8 : row 0 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0_9 : row 0 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1_1 : row 1 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1_2 : row 1 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1_3 : row 1 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1_4 : row 1 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1_5 : row 1 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1_6 : row 1 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1_7 : row 1 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1_8 : row 1 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1_9 : row 1 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_2_2 : row 2 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_2_3 : row 2 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_2_4 : row 2 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_2_5 : row 2 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_2_6 : row 2 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_2_7 : row 2 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_2_8 : row 2 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_2_9 : row 2 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_3_3 : row 3 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_3_4 : row 3 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_3_5 : row 3 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_3_6 : row 3 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_3_7 : row 3 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_3_8 : row 3 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_3_9 : row 3 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_4_4 : row 4 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_4_5 : row 4 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_4_6 : row 4 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_4_7 : row 4 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_4_8 : row 4 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_4_9 : row 4 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_5_5 : row 5 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_5_6 : row 5 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_5_7 : row 5 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_5_8 : row 5 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_5_9 : row 5 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_6_6 : row 6 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_6_7 : row 6 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_6_8 : row 6 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_6_9 : row 6 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_7_7 : row 7 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_7_8 : row 7 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_7_9 : row 7 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_8_8 : row 8 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_8_9 : row 8 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_9_9 : row 9 9 = true := by decide +kernel

lemma all_rows (a b : Fin 10) (h : a ≤ b) : row a.val b.val = true := by
  fin_cases a <;> fin_cases b
  · exact row_0_0
  · exact row_0_1
  · exact row_0_2
  · exact row_0_3
  · exact row_0_4
  · exact row_0_5
  · exact row_0_6
  · exact row_0_7
  · exact row_0_8
  · exact row_0_9
  · exact False.elim ((by decide : ¬ (1 : Fin 10) ≤ 0) h)
  · exact row_1_1
  · exact row_1_2
  · exact row_1_3
  · exact row_1_4
  · exact row_1_5
  · exact row_1_6
  · exact row_1_7
  · exact row_1_8
  · exact row_1_9
  · exact False.elim ((by decide : ¬ (2 : Fin 10) ≤ 0) h)
  · exact False.elim ((by decide : ¬ (2 : Fin 10) ≤ 1) h)
  · exact row_2_2
  · exact row_2_3
  · exact row_2_4
  · exact row_2_5
  · exact row_2_6
  · exact row_2_7
  · exact row_2_8
  · exact row_2_9
  · exact False.elim ((by decide : ¬ (3 : Fin 10) ≤ 0) h)
  · exact False.elim ((by decide : ¬ (3 : Fin 10) ≤ 1) h)
  · exact False.elim ((by decide : ¬ (3 : Fin 10) ≤ 2) h)
  · exact row_3_3
  · exact row_3_4
  · exact row_3_5
  · exact row_3_6
  · exact row_3_7
  · exact row_3_8
  · exact row_3_9
  · exact False.elim ((by decide : ¬ (4 : Fin 10) ≤ 0) h)
  · exact False.elim ((by decide : ¬ (4 : Fin 10) ≤ 1) h)
  · exact False.elim ((by decide : ¬ (4 : Fin 10) ≤ 2) h)
  · exact False.elim ((by decide : ¬ (4 : Fin 10) ≤ 3) h)
  · exact row_4_4
  · exact row_4_5
  · exact row_4_6
  · exact row_4_7
  · exact row_4_8
  · exact row_4_9
  · exact False.elim ((by decide : ¬ (5 : Fin 10) ≤ 0) h)
  · exact False.elim ((by decide : ¬ (5 : Fin 10) ≤ 1) h)
  · exact False.elim ((by decide : ¬ (5 : Fin 10) ≤ 2) h)
  · exact False.elim ((by decide : ¬ (5 : Fin 10) ≤ 3) h)
  · exact False.elim ((by decide : ¬ (5 : Fin 10) ≤ 4) h)
  · exact row_5_5
  · exact row_5_6
  · exact row_5_7
  · exact row_5_8
  · exact row_5_9
  · exact False.elim ((by decide : ¬ (6 : Fin 10) ≤ 0) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 10) ≤ 1) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 10) ≤ 2) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 10) ≤ 3) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 10) ≤ 4) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 10) ≤ 5) h)
  · exact row_6_6
  · exact row_6_7
  · exact row_6_8
  · exact row_6_9
  · exact False.elim ((by decide : ¬ (7 : Fin 10) ≤ 0) h)
  · exact False.elim ((by decide : ¬ (7 : Fin 10) ≤ 1) h)
  · exact False.elim ((by decide : ¬ (7 : Fin 10) ≤ 2) h)
  · exact False.elim ((by decide : ¬ (7 : Fin 10) ≤ 3) h)
  · exact False.elim ((by decide : ¬ (7 : Fin 10) ≤ 4) h)
  · exact False.elim ((by decide : ¬ (7 : Fin 10) ≤ 5) h)
  · exact False.elim ((by decide : ¬ (7 : Fin 10) ≤ 6) h)
  · exact row_7_7
  · exact row_7_8
  · exact row_7_9
  · exact False.elim ((by decide : ¬ (8 : Fin 10) ≤ 0) h)
  · exact False.elim ((by decide : ¬ (8 : Fin 10) ≤ 1) h)
  · exact False.elim ((by decide : ¬ (8 : Fin 10) ≤ 2) h)
  · exact False.elim ((by decide : ¬ (8 : Fin 10) ≤ 3) h)
  · exact False.elim ((by decide : ¬ (8 : Fin 10) ≤ 4) h)
  · exact False.elim ((by decide : ¬ (8 : Fin 10) ≤ 5) h)
  · exact False.elim ((by decide : ¬ (8 : Fin 10) ≤ 6) h)
  · exact False.elim ((by decide : ¬ (8 : Fin 10) ≤ 7) h)
  · exact row_8_8
  · exact row_8_9
  · exact False.elim ((by decide : ¬ (9 : Fin 10) ≤ 0) h)
  · exact False.elim ((by decide : ¬ (9 : Fin 10) ≤ 1) h)
  · exact False.elim ((by decide : ¬ (9 : Fin 10) ≤ 2) h)
  · exact False.elim ((by decide : ¬ (9 : Fin 10) ≤ 3) h)
  · exact False.elim ((by decide : ¬ (9 : Fin 10) ≤ 4) h)
  · exact False.elim ((by decide : ¬ (9 : Fin 10) ≤ 5) h)
  · exact False.elim ((by decide : ¬ (9 : Fin 10) ≤ 6) h)
  · exact False.elim ((by decide : ¬ (9 : Fin 10) ≤ 7) h)
  · exact False.elim ((by decide : ¬ (9 : Fin 10) ≤ 8) h)
  · exact row_9_9

lemma classify (a b : Fin 10) (hab : a ≤ b) (L : Nat) (hL : L < 2048)
    (h : admissible a.val b.val L = true) : maskCode a.val b.val L ∈ catalogue := by
  have tested := span_ok (all_rows a b hab) L (Nat.zero_le _) (by omega)
  simpa only [check, h, Bool.not_true, Bool.false_or, List.contains_iff_mem] using tested

end PetersenLive
