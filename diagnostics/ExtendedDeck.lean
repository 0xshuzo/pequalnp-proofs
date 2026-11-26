import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9791.ExtendedDeck
def full : List Nat := [10518528, 4259840, 8527872, 286720, 573440, 1155072, 2310144, 4620288, 9240576, 1703936, 3407872, 6823936, 13647872, 2092, 4184, 177, 354, 708, 1416, 2832, 5664, 3137, 6274, 4357]
def small : List Nat := [1280, 8832, 12544, 6272, 11264, 5632, 2816, 10, 69, 98, 49, 88, 44, 22]
def conforms (m : List Nat) : Bool := decide (m.length=14) &&
  m.all (fun j => j<24) && decide m.Nodup &&
  (List.range 14).all (fun i => (List.range 14).all (fun j =>
    ((full.getD (m.getD i 0) 0).testBit (m.getD j 0)) ==
    ((small.getD i 0).testBit j)))
def maps0 : List (List Nat) := [[2, 4, 6, 8, 3, 5, 7, 19, 17, 15, 13, 18, 16, 14], [4, 2, 3, 8, 5, 7, 6, 23, 14, 17, 15, 16, 18, 13], [17, 19, 14, 13, 15, 18, 16, 11, 6, 8, 7, 5, 3, 4], [7, 6, 4, 11, 3, 8, 5, 21, 15, 16, 18, 13, 19, 14], [6, 7, 3, 11, 8, 5, 4, 22, 14, 15, 16, 19, 13, 18], [0, 3, 4, 8, 6, 11, 5, 18, 15, 13, 21, 16, 19, 14], [3, 0, 4, 8, 5, 11, 6, 23, 14, 21, 13, 16, 19, 15], [16, 14, 13, 22, 18, 19, 15, 12, 5, 4, 8, 7, 11, 3], [8, 5, 3, 12, 11, 4, 7, 20, 18, 15, 19, 22, 14, 13]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps0 : maps0.all conforms = true := by decide +kernel
def maps9 : List (List Nat) := [[5, 8, 4, 12, 11, 3, 7, 23, 15, 18, 13, 22, 14, 19], [19, 18, 14, 20, 13, 22, 15, 10, 4, 7, 11, 5, 12, 3], [4, 10, 3, 11, 7, 5, 12, 21, 14, 20, 15, 22, 13, 18], [3, 7, 4, 9, 5, 11, 12, 17, 14, 22, 13, 20, 19, 15], [18, 19, 13, 20, 22, 15, 14, 9, 3, 4, 7, 12, 5, 11], [15, 14, 13, 23, 18, 17, 16, 12, 5, 6, 7, 8, 2, 3], [7, 5, 2, 12, 3, 8, 6, 20, 17, 16, 18, 14, 23, 13], [5, 7, 6, 12, 2, 3, 8, 22, 16, 18, 13, 23, 14, 17], [18, 17, 13, 20, 23, 16, 14, 9, 3, 6, 8, 12, 5, 2]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps9 : maps9.all conforms = true := by decide +kernel
def maps18 : List (List Nat) := [[3, 8, 6, 9, 5, 2, 12, 19, 14, 23, 13, 20, 17, 16], [15, 18, 14, 21, 13, 16, 19, 10, 4, 8, 5, 11, 6, 3], [4, 5, 3, 10, 11, 8, 6, 20, 14, 16, 19, 21, 18, 13], [19, 14, 16, 20, 21, 13, 18, 12, 8, 3, 11, 10, 5, 6], [8, 11, 5, 12, 3, 10, 6, 22, 16, 21, 18, 14, 20, 13], [11, 8, 6, 12, 5, 3, 10, 23, 21, 18, 13, 20, 14, 16], [17, 18, 13, 20, 14, 16, 23, 10, 2, 8, 6, 12, 5, 3], [2, 10, 8, 6, 3, 5, 12, 21, 23, 20, 13, 14, 16, 18], [1, 3, 5, 10, 11, 12, 6, 18, 16, 14, 22, 21, 20, 13]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps18 : maps18.all conforms = true := by decide +kernel
def maps27 : List (List Nat) := [[2, 10, 6, 12, 11, 3, 7, 20, 17, 18, 13, 22, 14, 21], [10, 2, 3, 12, 11, 6, 7, 23, 18, 17, 21, 22, 14, 13], [16, 22, 14, 13, 23, 18, 17, 11, 6, 7, 8, 2, 3, 12], [6, 8, 3, 11, 7, 2, 12, 19, 14, 23, 17, 22, 13, 18], [21, 18, 14, 23, 13, 22, 17, 8, 6, 7, 11, 2, 12, 3], [15, 14, 21, 13, 17, 22, 23, 3, 0, 12, 7, 2, 11, 6], [0, 3, 6, 7, 12, 2, 11, 18, 21, 13, 23, 22, 17, 14], [2, 4, 8, 7, 11, 3, 12, 15, 23, 14, 13, 22, 18, 19], [17, 14, 13, 19, 18, 22, 23, 4, 2, 12, 7, 8, 11, 3]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps27 : maps27.all conforms = true := by decide +kernel
def maps36 : List (List Nat) := [[15, 14, 13, 21, 18, 22, 20, 6, 5, 12, 7, 10, 11, 3], [16, 18, 13, 22, 14, 21, 20, 7, 5, 10, 6, 12, 11, 3], [5, 7, 10, 6, 3, 11, 12, 17, 20, 22, 13, 14, 21, 18], [0, 3, 5, 6, 2, 8, 7, 14, 15, 18, 23, 17, 16, 13], [3, 0, 7, 6, 5, 2, 8, 21, 18, 23, 13, 16, 17, 15], [1, 0, 5, 2, 7, 11, 6, 23, 16, 21, 22, 17, 13, 15], [18, 21, 15, 13, 23, 16, 17, 11, 7, 6, 8, 2, 5, 0], [19, 15, 16, 17, 13, 21, 23, 7, 8, 0, 11, 2, 6, 5], [22, 16, 15, 23, 13, 21, 17, 8, 7, 6, 11, 2, 0, 5]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps36 : maps36.all conforms = true := by decide +kernel
def maps45 : List (List Nat) := [[1, 3, 5, 4, 11, 7, 8, 14, 16, 18, 22, 19, 15, 13], [14, 23, 15, 13, 21, 16, 19, 2, 4, 8, 6, 11, 5, 0], [4, 2, 0, 6, 8, 11, 5, 17, 15, 13, 19, 16, 21, 23], [2, 4, 7, 12, 5, 11, 9, 14, 17, 19, 13, 20, 22, 15], [4, 2, 5, 12, 11, 9, 7, 23, 15, 17, 19, 22, 20, 13], [0, 11, 5, 9, 2, 12, 7, 19, 15, 22, 23, 17, 20, 13], [21, 17, 15, 20, 22, 13, 23, 9, 0, 2, 11, 12, 5, 7], [14, 15, 17, 13, 22, 23, 21, 5, 6, 0, 12, 11, 2, 7], [16, 22, 13, 23, 21, 17, 15, 12, 5, 7, 6, 0, 2, 11]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps45 : maps45.all conforms = true := by decide +kernel
def maps54 : List (List Nat) := [[20, 17, 13, 21, 23, 22, 15, 6, 5, 7, 12, 0, 11, 2], [0, 3, 5, 12, 11, 10, 7, 14, 15, 18, 21, 22, 20, 13], [3, 0, 7, 12, 5, 11, 10, 23, 18, 21, 13, 20, 22, 15], [17, 20, 13, 21, 15, 22, 23, 10, 2, 12, 7, 0, 11, 5], [2, 7, 0, 10, 5, 11, 12, 18, 23, 22, 13, 20, 21, 15], [2, 8, 6, 10, 5, 11, 9, 18, 17, 19, 13, 20, 21, 16], [10, 2, 5, 8, 11, 6, 9, 23, 20, 17, 21, 19, 16, 13], [14, 19, 16, 13, 23, 20, 17, 11, 6, 9, 12, 2, 5, 8], [21, 20, 16, 23, 13, 19, 17, 12, 6, 9, 11, 2, 8, 5]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps54 : maps54.all conforms = true := by decide +kernel
def maps63 : List (List Nat) := [[6, 11, 5, 12, 2, 9, 8, 22, 16, 19, 17, 23, 20, 13], [15, 17, 21, 19, 16, 13, 23, 9, 0, 2, 5, 8, 11, 6], [0, 5, 6, 9, 8, 2, 11, 20, 21, 13, 23, 19, 17, 16], [14, 19, 13, 20, 21, 16, 18, 9, 3, 8, 6, 10, 5, 11], [3, 6, 8, 9, 5, 11, 10, 17, 18, 21, 13, 20, 19, 16], [1, 2, 5, 9, 11, 12, 8, 17, 16, 23, 22, 19, 20, 13], [14, 19, 13, 17, 22, 23, 18, 9, 3, 8, 12, 7, 2, 11], [3, 9, 7, 12, 2, 11, 8, 20, 18, 19, 13, 23, 22, 17], [15, 19, 13, 23, 22, 17, 20, 8, 5, 9, 7, 12, 2, 11]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps63 : maps63.all conforms = true := by decide +kernel
def maps72 : List (List Nat) := [[16, 22, 13, 17, 19, 23, 20, 7, 5, 12, 8, 9, 2, 11], [5, 8, 9, 7, 11, 2, 12, 18, 20, 23, 13, 22, 17, 19], [9, 3, 6, 5, 4, 8, 7, 13, 17, 18, 19, 15, 16, 14], [3, 5, 7, 9, 4, 6, 8, 20, 18, 16, 14, 19, 17, 15], [18, 20, 15, 14, 16, 19, 17, 12, 7, 9, 8, 6, 4, 5], [8, 7, 5, 12, 4, 9, 6, 22, 16, 17, 19, 14, 20, 15], [7, 8, 4, 12, 9, 6, 5, 23, 15, 16, 17, 20, 14, 19], [1, 4, 5, 9, 7, 12, 6, 19, 16, 14, 22, 17, 20, 15], [0, 9, 4, 6, 8, 12, 5, 17, 15, 20, 23, 16, 14, 19]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps72 : maps72.all conforms = true := by decide +kernel
def maps81 : List (List Nat) := [[21, 19, 15, 20, 14, 16, 23, 9, 0, 8, 6, 12, 5, 4], [12, 5, 4, 11, 0, 8, 6, 13, 14, 16, 23, 21, 19, 15], [20, 19, 15, 21, 14, 23, 16, 11, 5, 8, 12, 6, 0, 4], [5, 11, 0, 12, 6, 8, 4, 22, 15, 19, 16, 14, 23, 21], [4, 8, 0, 10, 12, 6, 5, 18, 15, 16, 14, 20, 21, 23], [19, 20, 14, 21, 23, 16, 15, 10, 4, 5, 8, 0, 6, 12], [6, 5, 4, 11, 7, 9, 12, 13, 14, 20, 17, 22, 19, 15], [16, 19, 15, 22, 14, 17, 20, 11, 5, 9, 6, 12, 7, 4], [5, 6, 4, 11, 12, 9, 7, 21, 15, 17, 20, 22, 19, 14]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps81 : maps81.all conforms = true := by decide +kernel
def maps90 : List (List Nat) := [[0, 9, 4, 12, 11, 6, 7, 20, 15, 17, 21, 22, 14, 19], [9, 0, 6, 12, 11, 4, 7, 23, 17, 15, 19, 22, 14, 21], [4, 2, 6, 11, 7, 0, 12, 13, 14, 23, 15, 22, 21, 17], [2, 4, 6, 11, 12, 0, 7, 19, 17, 15, 23, 22, 21, 14], [0, 3, 4, 11, 12, 8, 7, 13, 15, 18, 23, 22, 19, 14], [3, 0, 7, 11, 4, 12, 8, 21, 18, 23, 14, 19, 22, 15], [16, 15, 14, 22, 19, 23, 21, 7, 6, 0, 8, 11, 12, 4], [17, 19, 14, 23, 15, 22, 21, 8, 6, 11, 7, 0, 12, 4], [18, 21, 15, 14, 23, 19, 22, 6, 7, 11, 8, 12, 4, 0]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps90 : maps90.all conforms = true := by decide +kernel
def maps99 : List (List Nat) := [[1, 2, 6, 3, 7, 12, 8, 13, 16, 23, 22, 18, 14, 17], [4, 2, 6, 5, 9, 8, 12, 13, 14, 23, 19, 20, 16, 17], [2, 4, 6, 5, 12, 8, 9, 15, 17, 19, 23, 20, 16, 14], [0, 3, 6, 5, 12, 8, 10, 13, 21, 18, 23, 20, 16, 14], [15, 18, 21, 14, 20, 16, 23, 3, 0, 8, 5, 12, 6, 10], [15, 16, 21, 22, 14, 19, 23, 1, 0, 8, 4, 12, 11, 6], [9, 3, 6, 11, 12, 10, 7, 13, 17, 18, 20, 22, 21, 14], [3, 9, 7, 11, 6, 12, 10, 19, 18, 20, 14, 21, 22, 17], [15, 20, 14, 21, 22, 17, 19, 10, 4, 9, 7, 11, 6, 12]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps99 : maps99.all conforms = true := by decide +kernel
def maps108 : List (List Nat) := [[4, 7, 9, 10, 6, 12, 11, 18, 19, 22, 14, 21, 20, 17], [10, 4, 7, 6, 5, 9, 8, 14, 18, 19, 20, 16, 17, 15], [4, 6, 8, 10, 5, 7, 9, 21, 19, 17, 15, 20, 18, 16], [0, 9, 6, 8, 7, 5, 10, 19, 21, 20, 15, 18, 16, 17], [9, 0, 6, 8, 10, 5, 7, 23, 17, 15, 20, 18, 16, 21], [10, 2, 7, 5, 6, 0, 8, 13, 18, 23, 21, 16, 15, 17], [2, 5, 6, 10, 8, 0, 7, 20, 17, 15, 23, 18, 21, 16], [7, 6, 0, 12, 10, 8, 5, 14, 15, 16, 18, 20, 23, 21], [17, 20, 16, 23, 15, 18, 21, 12, 6, 10, 7, 0, 8, 5]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps108 : maps108.all conforms = true := by decide +kernel
def maps117 : List (List Nat) := [[6, 7, 5, 12, 0, 10, 8, 22, 16, 18, 21, 23, 20, 15], [1, 0, 5, 10, 7, 12, 8, 21, 16, 23, 22, 18, 20, 15], [10, 4, 7, 12, 0, 11, 8, 14, 18, 19, 21, 23, 22, 15], [4, 10, 8, 12, 7, 0, 11, 20, 19, 21, 15, 22, 23, 18], [8, 5, 7, 11, 0, 12, 10, 13, 18, 20, 23, 21, 22, 15], [16, 21, 15, 22, 23, 18, 20, 11, 5, 10, 8, 12, 7, 0], [5, 8, 10, 11, 7, 0, 12, 19, 20, 23, 15, 22, 21, 18], [7, 5, 6, 11, 8, 10, 9, 13, 17, 20, 18, 19, 21, 16], [11, 5, 8, 7, 6, 10, 9, 15, 19, 20, 21, 17, 18, 16]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps117 : maps117.all conforms = true := by decide +kernel
def maps126 : List (List Nat) := [[5, 7, 9, 11, 6, 8, 10, 22, 20, 18, 16, 21, 19, 17], [1, 10, 7, 9, 8, 6, 11, 20, 22, 21, 16, 19, 17, 18], [8, 6, 7, 12, 9, 11, 10, 14, 18, 21, 19, 20, 22, 17], [12, 6, 9, 8, 7, 11, 10, 16, 20, 21, 22, 18, 19, 17], [6, 8, 10, 12, 7, 9, 11, 23, 21, 19, 17, 22, 20, 18], [10, 2, 7, 11, 9, 12, 8, 13, 18, 23, 20, 19, 22, 17], [2, 11, 8, 10, 9, 7, 12, 21, 23, 22, 17, 20, 18, 19], [9, 0, 8, 7, 12, 10, 11, 15, 19, 21, 20, 22, 18, 23], [0, 9, 10, 7, 12, 8, 11, 17, 21, 19, 23, 22, 18, 20]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checked_maps126 : maps126.all conforms = true := by decide +kernel
def maps : List (List Nat) := maps0 ++ maps9 ++ maps18 ++ maps27 ++ maps36 ++ maps45 ++ maps54 ++ maps63 ++ maps72 ++ maps81 ++ maps90 ++ maps99 ++ maps108 ++ maps117 ++ maps126
theorem deck_conforms : maps.all conforms=true := by
  simp only [maps,List.all_append,checked_maps0,checked_maps9,checked_maps18,checked_maps27,checked_maps36,checked_maps45,checked_maps54,checked_maps63,checked_maps72,checked_maps81,checked_maps90,checked_maps99,checked_maps108,checked_maps117,checked_maps126]
def covers (i j : Nat) := maps.any (fun m => !(m.contains i) && !(m.contains j))
def exceptional : List (Nat × Nat) := [(5,22),(6,22),(7,16),(8,22),(11,16),(12,16),(16,22)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_0 : (List.range 24).all (fun j => decide (j≤0) || (covers 0 j == !(exceptional.contains (0,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_1 : (List.range 24).all (fun j => decide (j≤1) || (covers 1 j == !(exceptional.contains (1,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_2 : (List.range 24).all (fun j => decide (j≤2) || (covers 2 j == !(exceptional.contains (2,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_3 : (List.range 24).all (fun j => decide (j≤3) || (covers 3 j == !(exceptional.contains (3,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_4 : (List.range 24).all (fun j => decide (j≤4) || (covers 4 j == !(exceptional.contains (4,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_5 : (List.range 24).all (fun j => decide (j≤5) || (covers 5 j == !(exceptional.contains (5,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_6 : (List.range 24).all (fun j => decide (j≤6) || (covers 6 j == !(exceptional.contains (6,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_7 : (List.range 24).all (fun j => decide (j≤7) || (covers 7 j == !(exceptional.contains (7,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_8 : (List.range 24).all (fun j => decide (j≤8) || (covers 8 j == !(exceptional.contains (8,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_9 : (List.range 24).all (fun j => decide (j≤9) || (covers 9 j == !(exceptional.contains (9,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_10 : (List.range 24).all (fun j => decide (j≤10) || (covers 10 j == !(exceptional.contains (10,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_11 : (List.range 24).all (fun j => decide (j≤11) || (covers 11 j == !(exceptional.contains (11,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_12 : (List.range 24).all (fun j => decide (j≤12) || (covers 12 j == !(exceptional.contains (12,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_13 : (List.range 24).all (fun j => decide (j≤13) || (covers 13 j == !(exceptional.contains (13,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_14 : (List.range 24).all (fun j => decide (j≤14) || (covers 14 j == !(exceptional.contains (14,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_15 : (List.range 24).all (fun j => decide (j≤15) || (covers 15 j == !(exceptional.contains (15,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_16 : (List.range 24).all (fun j => decide (j≤16) || (covers 16 j == !(exceptional.contains (16,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_17 : (List.range 24).all (fun j => decide (j≤17) || (covers 17 j == !(exceptional.contains (17,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_18 : (List.range 24).all (fun j => decide (j≤18) || (covers 18 j == !(exceptional.contains (18,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_19 : (List.range 24).all (fun j => decide (j≤19) || (covers 19 j == !(exceptional.contains (19,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_20 : (List.range 24).all (fun j => decide (j≤20) || (covers 20 j == !(exceptional.contains (20,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_21 : (List.range 24).all (fun j => decide (j≤21) || (covers 21 j == !(exceptional.contains (21,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_22 : (List.range 24).all (fun j => decide (j≤22) || (covers 22 j == !(exceptional.contains (22,j))))=true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem row_23 : (List.range 24).all (fun j => decide (j≤23) || (covers 23 j == !(exceptional.contains (23,j))))=true := by decide +kernel
end PEqualNP.Outside.L_meta_9791.ExtendedDeck
