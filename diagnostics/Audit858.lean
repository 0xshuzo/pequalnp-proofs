import PEqualNP.Defs

namespace Mask858
set_option maxRecDepth 10000
set_option maxHeartbeats 0
abbrev W := BitVec 16
def sel (k : BitVec 4) (bank : List W) : W := bank.getD k.toNat 0
def gate (o : BitVec 2) (a b : W) : W := if o=0 then a &&& b else if o=1 then a ||| b else ~~~a
def bank0 : List W := [15,240,3840,61440,4369,8738,17476,34952]
def pick0 (k : BitVec 4)  : W := (if k < 8#4 then (if k < 4#4 then (if k < 2#4 then (if k < 1#4 then 15#16 else 240#16) else (if k < 3#4 then 3840#16 else 61440#16)) else (if k < 6#4 then (if k < 5#4 then 4369#16 else 8738#16) else (if k < 7#4 then 17476#16 else 34952#16))) else (if k < 12#4 then (if k < 10#4 then (if k < 9#4 then 0#16 else 0#16) else (if k < 11#4 then 0#16 else 0#16)) else (if k < 14#4 then (if k < 13#4 then 0#16 else 0#16) else (if k < 15#4 then 0#16 else 0#16))))

def pick1 (k : BitVec 4) (g0 : W) : W := (if k < 8#4 then (if k < 4#4 then (if k < 2#4 then (if k < 1#4 then 15#16 else 240#16) else (if k < 3#4 then 3840#16 else 61440#16)) else (if k < 6#4 then (if k < 5#4 then 4369#16 else 8738#16) else (if k < 7#4 then 17476#16 else 34952#16))) else (if k < 12#4 then (if k < 10#4 then (if k < 9#4 then g0 else 0#16) else (if k < 11#4 then 0#16 else 0#16)) else (if k < 14#4 then (if k < 13#4 then 0#16 else 0#16) else (if k < 15#4 then 0#16 else 0#16))))

def pick2 (k : BitVec 4) (g0 g1 : W) : W := (if k < 8#4 then (if k < 4#4 then (if k < 2#4 then (if k < 1#4 then 15#16 else 240#16) else (if k < 3#4 then 3840#16 else 61440#16)) else (if k < 6#4 then (if k < 5#4 then 4369#16 else 8738#16) else (if k < 7#4 then 17476#16 else 34952#16))) else (if k < 12#4 then (if k < 10#4 then (if k < 9#4 then g0 else g1) else (if k < 11#4 then 0#16 else 0#16)) else (if k < 14#4 then (if k < 13#4 then 0#16 else 0#16) else (if k < 15#4 then 0#16 else 0#16))))

def pick3 (k : BitVec 4) (g0 g1 g2 : W) : W := (if k < 8#4 then (if k < 4#4 then (if k < 2#4 then (if k < 1#4 then 15#16 else 240#16) else (if k < 3#4 then 3840#16 else 61440#16)) else (if k < 6#4 then (if k < 5#4 then 4369#16 else 8738#16) else (if k < 7#4 then 17476#16 else 34952#16))) else (if k < 12#4 then (if k < 10#4 then (if k < 9#4 then g0 else g1) else (if k < 11#4 then g2 else 0#16)) else (if k < 14#4 then (if k < 13#4 then 0#16 else 0#16) else (if k < 15#4 then 0#16 else 0#16))))

def pick4 (k : BitVec 4) (g0 g1 g2 g3 : W) : W := (if k < 8#4 then (if k < 4#4 then (if k < 2#4 then (if k < 1#4 then 15#16 else 240#16) else (if k < 3#4 then 3840#16 else 61440#16)) else (if k < 6#4 then (if k < 5#4 then 4369#16 else 8738#16) else (if k < 7#4 then 17476#16 else 34952#16))) else (if k < 12#4 then (if k < 10#4 then (if k < 9#4 then g0 else g1) else (if k < 11#4 then g2 else g3)) else (if k < 14#4 then (if k < 13#4 then 0#16 else 0#16) else (if k < 15#4 then 0#16 else 0#16))))

def pick5 (k : BitVec 4) (g0 g1 g2 g3 g4 : W) : W := (if k < 8#4 then (if k < 4#4 then (if k < 2#4 then (if k < 1#4 then 15#16 else 240#16) else (if k < 3#4 then 3840#16 else 61440#16)) else (if k < 6#4 then (if k < 5#4 then 4369#16 else 8738#16) else (if k < 7#4 then 17476#16 else 34952#16))) else (if k < 12#4 then (if k < 10#4 then (if k < 9#4 then g0 else g1) else (if k < 11#4 then g2 else g3)) else (if k < 14#4 then (if k < 13#4 then g4 else 0#16) else (if k < 15#4 then 0#16 else 0#16))))

def pick6 (k : BitVec 4) (g0 g1 g2 g3 g4 g5 : W) : W := (if k < 8#4 then (if k < 4#4 then (if k < 2#4 then (if k < 1#4 then 15#16 else 240#16) else (if k < 3#4 then 3840#16 else 61440#16)) else (if k < 6#4 then (if k < 5#4 then 4369#16 else 8738#16) else (if k < 7#4 then 17476#16 else 34952#16))) else (if k < 12#4 then (if k < 10#4 then (if k < 9#4 then g0 else g1) else (if k < 11#4 then g2 else g3)) else (if k < 14#4 then (if k < 13#4 then g4 else g5) else (if k < 15#4 then 0#16 else 0#16))))

theorem no7 (o0 : BitVec 2) (a0 : BitVec 4) (b0 : BitVec 4) (o1 : BitVec 2) (a1 : BitVec 4) (b1 : BitVec 4) (o2 : BitVec 2) (a2 : BitVec 4) (b2 : BitVec 4) (o3 : BitVec 2) (a3 : BitVec 4) (b3 : BitVec 4) (o4 : BitVec 2) (a4 : BitVec 4) (b4 : BitVec 4) (o5 : BitVec 2) (a5 : BitVec 4) (b5 : BitVec 4) (o6 : BitVec 2) (a6 : BitVec 4) (b6 : BitVec 4) :
  let g0 := gate o0 (pick0 a0 ) (pick0 b0 )
  let g1 := gate o1 (pick1 a1 g0) (pick1 b1 g0)
  let g2 := gate o2 (pick2 a2 g0 g1) (pick2 b2 g0 g1)
  let g3 := gate o3 (pick3 a3 g0 g1 g2) (pick3 b3 g0 g1 g2)
  let g4 := gate o4 (pick4 a4 g0 g1 g2 g3) (pick4 b4 g0 g1 g2 g3)
  let g5 := gate o5 (pick5 a5 g0 g1 g2 g3 g4) (pick5 b5 g0 g1 g2 g3 g4)
  let g6 := gate o6 (pick6 a6 g0 g1 g2 g3 g4 g5) (pick6 b6 g0 g1 g2 g3 g4 g5)
  g0 ≠ 858#16 ∧ g1 ≠ 858#16 ∧ g2 ≠ 858#16 ∧ g3 ≠ 858#16 ∧ g4 ≠ 858#16 ∧ g5 ≠ 858#16 ∧ g6 ≠ 858#16 := by
  unfold gate pick0 pick1 pick2 pick3 pick4 pick5 pick6
  bv_decide (config := {timeout := 300})
end Mask858
#print axioms Mask858.no7
