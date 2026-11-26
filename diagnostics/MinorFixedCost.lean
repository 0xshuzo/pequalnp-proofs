import PEqualNP.Outside.L_meta_9752

namespace PEqualNP.Outside.L_meta_9750.Gap4029
open PEqualNP.Outside.L_meta_9752.Engine
def goal : Sig := 0xfffffffefffffffefffffffafffffffafffffffefffffffefffffffafffffffafffffffefffffffefffffffafffffff0fffefffefffefffefffafffafff0fff0fffffffeffffffeefffffffaffffffaafffffffeffffffeefffffffaffffffaafffffefeffffeeeefffffafaffff0000fefefefeeeeeeeeefafafafa00000000fffffffefffffffefffffffafffffffafffffffefffffffefffffffafffffffafffffffefffffffefffffffafffffff0fffefffefffefffefffafffafff0fff0fffffffeffffffeefffffffaffffffaafffffffeffffffeefffffffaffffffaafffffefeffffeeeefffffafaffff0000fefefefeeeeeeeeefafafafa00000000
def raw : List Sig := varsX 1023

def names (xs : List (Nat × Nat × Nat)) : List (Sig × Row × Row) :=
  xs.map (fun x => (inputs.getD x.1 zero,Fin.ofNat 2048 x.2.1,Fin.ofNat 2048 x.2.2))
def sliceGoal (z o : Nat) : Sig := movedWord (fixRows z o) goal
theorem weaken {u roots T b v} (lo : Lower u roots T b) (le : v ≤ b) : Lower u roots T v :=
  fun p bank hr ht => le.trans (lo p bank hr ht)
theorem liftCut (z o avail drop q prior L : Nat) (swaps : List Nat) (xs : List (Nat × Nat × Nat))
    (lower : Face true q prior)
    (initial : checkMap (fixRows z o) raw goal (varsX avail) (sliceGoal z o)=true)
    (domain : movedWord (fixRows z o) (subcube z o)=one)
    (pr : properB (sliceGoal z o)=true) (pc : properB (graphGoal q)=true)
    (valid : checkLift (swaps.map swapRows ++ fixRows drop 0) (sliceGoal z o) (varsX avail)
      (varsX q) (graphGoal q) (names xs)=true)
    (price : L ≤ prior + ((names xs).map Prod.fst).toFinset.card) :
    Slice true raw goal (subcube z o) L :=
  slice_correct initial domain (proper_of _ pr) (weaken (lift_ok valid (proper_of _ pr) (proper_of _ pc) lower) price)
theorem simpleCut (z o avail L : Nat) (xs : List (Nat × Nat × Nat))
    (initial : checkMap (fixRows z o) raw goal (varsX avail) (sliceGoal z o)=true)
    (domain : movedWord (fixRows z o) (subcube z o)=one)
    (pr : properB (sliceGoal z o)=true)
    (valid : checkEssential (sliceGoal z o) (varsX avail) (names xs)=true)
    (price : L ≤ ((names xs).map Prod.fst).toFinset.card-1) :
    Slice true raw goal (subcube z o) L :=
  slice_correct initial domain (proper_of _ pr) (weaken (lower_count (proper_of _ pr) (names xs) valid) price)
set_option maxRecDepth 32000
set_option maxHeartbeats 0
theorem column0 : Slice true raw goal (subcube 0 2) 12 :=
  liftCut 0 2 1021 64 509 11 12 [96, 114, 131, 84, 133, 166, 167, 169] [(6, 0, 64)] h989_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column1 : Slice true raw goal (subcube 0 128) 12 :=
  liftCut 0 128 895 16 509 11 12 [64, 65, 50, 101, 167, 169] [(4, 0, 16)] h989_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column2 : Slice true raw goal (subcube 2 0) 12 :=
  liftCut 2 0 1021 128 510 11 12 [64, 65, 50, 101, 151] [(7, 16, 144)] h990_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column3 : Slice true raw goal (subcube 128 0) 12 :=
  liftCut 128 0 895 16 509 11 12 [64, 65, 50, 101, 167, 169] [(4, 256, 272)] h989_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column4 : Slice true raw goal (subcube 4 0) 11 :=
  liftCut 4 0 1019 512 503 10 11 [64, 65, 146, 67, 148, 101, 169] [(9, 8, 520)] h983_10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column5 : Slice true raw goal (subcube 8 0) 11 :=
  liftCut 8 0 1015 0 1519 11 11 [32, 147, 148, 165, 134, 135, 169] [] h3023_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column6 : Slice true raw goal (subcube 16 0) 11 :=
  liftCut 16 0 1007 128 509 11 11 [64, 65, 50, 101, 167, 169] [] h989_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column7 : Slice true raw goal (subcube 32 0) 11 :=
  liftCut 32 0 991 0 1519 11 11 [160, 81, 98, 115, 132, 149, 166, 151, 168] [] h3023_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column8 : Slice true raw goal (subcube 64 0) 11 :=
  liftCut 64 0 959 2 509 11 11 [96, 114, 131, 84, 133, 166, 167, 169] [] h989_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column9 : Slice true raw goal (subcube 512 0) 11 :=
  liftCut 512 0 511 8 507 10 11 [64, 65, 66, 147, 148, 133, 134] [(3, 256, 264)] h987_10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column10 : Slice true raw goal (subcube 16 128) 11 :=
  liftCut 16 128 879 0 509 11 11 [64, 65, 50, 101, 167, 169] [] h989_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column11 : Slice true raw goal (subcube 64 2) 11 :=
  liftCut 64 2 957 0 509 11 11 [96, 114, 131, 84, 133, 166, 167, 169] [] h989_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column15 : Slice true raw goal (subcube 0 4) 10 :=
  liftCut 0 4 1019 544 439 8 10 [64, 65, 146, 67, 148, 165, 166] [(5, 0, 32), (9, 0, 512)] h855_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column16 : Slice true raw goal (subcube 0 16) 10 :=
  liftCut 0 16 1007 384 253 8 10 [64, 65, 50, 132, 101, 135, 168, 169] [(7, 0, 128), (8, 0, 256)] h477_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column17 : Slice true raw goal (subcube 0 64) 10 :=
  liftCut 0 64 959 3 253 8 10 [128, 82, 99, 116, 133, 166, 135, 168, 169] [(0, 0, 1), (1, 0, 2)] h477_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column18 : Slice true raw goal (subcube 0 512) 10 :=
  liftCut 0 512 511 12 439 8 10 [128, 113, 146, 163, 84, 117, 150, 135, 169] [(2, 0, 4), (3, 0, 8)] h855_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column19 : Slice true raw goal (subcube 1 0) 10 :=
  liftCut 1 0 1022 66 253 8 10 [128, 82, 99, 116, 133, 166, 135, 168, 169] [(1, 64, 66), (6, 2, 66)] h477_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column20 : Slice true raw goal (subcube 256 0) 10 :=
  liftCut 256 0 767 144 253 8 10 [64, 65, 50, 132, 101, 135, 168, 169] [(4, 128, 144), (7, 16, 144)] h477_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column23 : Slice true raw goal (subcube 36 0) 10 :=
  liftCut 36 0 987 0 507 10 10 [96, 113, 146, 83, 132, 149, 150] [] h987_10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column28 : Slice true raw goal (subcube 516 0) 10 :=
  liftCut 516 0 507 0 503 10 10 [64, 65, 146, 67, 148, 101, 169] [] h983_10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column29 : Slice true raw goal (subcube 520 0) 10 :=
  liftCut 520 0 503 0 507 10 10 [64, 65, 66, 147, 148, 133, 134] [] h987_10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column30 : Slice true raw goal (subcube 0 8) 9 :=
  liftCut 0 8 1015 772 237 6 9 [48, 33, 67, 101, 118] [(2, 32, 36), (8, 0, 256), (9, 0, 512)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column31 : Slice true raw goal (subcube 0 32) 9 :=
  liftCut 0 32 991 517 237 6 9 [16, 66, 67, 133, 134, 135] [(0, 0, 1), (2, 0, 4), (9, 8, 520)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column33 : Slice true raw goal (subcube 1 64) 9 :=
  liftCut 1 64 958 2 253 8 9 [128, 82, 99, 116, 133, 166, 135, 168, 169] [(1, 0, 2)] h477_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column39 : Slice true raw goal (subcube 4 512) 9 :=
  liftCut 4 512 507 8 439 8 9 [128, 113, 146, 163, 84, 117, 150, 135, 169] [(3, 0, 8)] h855_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column42 : Slice true raw goal (subcube 8 4) 9 :=
  liftCut 8 4 1011 544 249 7 9 [64, 65, 66, 67, 133, 134] [(5, 0, 32), (9, 0, 512)] h473_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column43 : Slice true raw goal (subcube 8 16) 9 :=
  liftCut 8 16 999 384 249 7 9 [64, 65, 50, 67, 101, 135, 152] [(7, 0, 128), (8, 0, 256)] h473_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column45 : Slice true raw goal (subcube 8 512) 9 :=
  liftCut 8 512 503 4 439 8 9 [128, 113, 146, 163, 84, 117, 150, 135, 169] [(2, 0, 4)] h855_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column50 : Slice true raw goal (subcube 32 4) 9 :=
  liftCut 32 4 987 512 439 8 9 [64, 65, 146, 67, 148, 165, 166] [(9, 0, 512)] h855_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column51 : Slice true raw goal (subcube 32 64) 9 :=
  liftCut 32 64 927 3 249 7 9 [16, 33, 67, 133, 150, 152] [(0, 0, 1), (1, 0, 2)] h473_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column53 : Slice true raw goal (subcube 32 512) 9 :=
  liftCut 32 512 479 12 249 7 9 [64, 65, 66, 67, 133, 134] [(2, 0, 4), (3, 0, 8)] h473_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column54 : Slice true raw goal (subcube 33 0) 9 :=
  liftCut 33 0 990 66 249 7 9 [16, 33, 67, 133, 150, 152] [(1, 64, 66), (6, 2, 66)] h473_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column55 : Slice true raw goal (subcube 40 0) 9 :=
  liftCut 40 0 983 516 249 7 9 [64, 65, 66, 67, 133, 134] [(2, 512, 516), (9, 4, 516)] h473_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column63 : Slice true raw goal (subcube 256 16) 9 :=
  liftCut 256 16 751 128 253 8 9 [64, 65, 50, 132, 101, 135, 168, 169] [(7, 0, 128)] h477_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column66 : Slice true raw goal (subcube 264 0) 9 :=
  liftCut 264 0 759 144 249 7 9 [64, 65, 50, 67, 101, 135, 152] [(4, 128, 144), (7, 16, 144)] h473_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column77 : Slice true raw goal (subcube 1 4) 8 :=
  liftCut 1 4 1018 544 237 6 8 [16, 66, 67, 133, 134, 135] [(5, 0, 32), (9, 0, 512)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column79 : Slice true raw goal (subcube 1 32) 8 :=
  liftCut 1 32 990 516 237 6 8 [16, 66, 67, 133, 134, 135] [(2, 0, 4), (9, 8, 520)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column87 : Slice true raw goal (subcube 12 0) 8 :=
  liftCut 12 0 1011 512 439 8 8 [128, 113, 146, 163, 84, 117, 150, 135, 169] [] h855_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column99 : Slice true raw goal (subcube 256 8) 8 :=
  liftCut 256 8 759 516 237 6 8 [48, 33, 67, 101, 118] [(2, 32, 36), (9, 0, 512)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column101 : Slice true raw goal (subcube 256 512) 8 :=
  liftCut 256 512 255 12 237 6 8 [48, 33, 67, 101, 118] [(2, 0, 4), (3, 0, 8)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column102 : Slice true raw goal (subcube 257 0) 8 :=
  liftCut 257 0 766 144 237 6 8 [16, 50, 101, 135, 152] [(4, 128, 144), (7, 16, 144)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column103 : Slice true raw goal (subcube 260 0) 8 :=
  liftCut 260 0 763 144 237 6 8 [48, 33, 83, 101, 118, 135, 152] [(4, 128, 144), (7, 16, 144)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column109 : Slice true raw goal (subcube 513 0) 8 :=
  liftCut 513 0 510 36 237 6 8 [16, 66, 67, 133, 134, 135] [(2, 32, 36), (5, 4, 36)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column111 : Slice true raw goal (subcube 544 0) 8 :=
  liftCut 544 0 479 4 439 8 8 [64, 65, 146, 67, 148, 165, 166] [] h855_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column114 : Slice true raw goal (subcube 12 512) 8 :=
  liftCut 12 512 499 0 439 8 8 [128, 113, 146, 163, 84, 117, 150, 135, 169] [] h855_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column175 : Slice true raw goal (subcube 544 4) 8 :=
  liftCut 544 4 475 0 439 8 8 [64, 65, 146, 67, 148, 165, 166] [] h855_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem column212 : Slice true raw goal (subcube 5 32) 7 :=
  liftCut 5 32 986 512 237 6 7 [16, 66, 67, 133, 134, 135] [(9, 8, 520)] h461_6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

structure CertifiedColumn where
  domain : Sig
  bound : Nat
  valid : Slice true raw goal domain bound
def columns : Array CertifiedColumn := #[⟨subcube 0 2,12,column0⟩,⟨subcube 0 128,12,column1⟩,⟨subcube 2 0,12,column2⟩,⟨subcube 128 0,12,column3⟩,⟨subcube 4 0,11,column4⟩,⟨subcube 8 0,11,column5⟩,⟨subcube 16 0,11,column6⟩,⟨subcube 32 0,11,column7⟩,⟨subcube 64 0,11,column8⟩,⟨subcube 512 0,11,column9⟩,⟨subcube 16 128,11,column10⟩,⟨subcube 64 2,11,column11⟩,⟨subcube 0 4,10,column15⟩,⟨subcube 0 16,10,column16⟩,⟨subcube 0 64,10,column17⟩,⟨subcube 0 512,10,column18⟩,⟨subcube 1 0,10,column19⟩,⟨subcube 256 0,10,column20⟩,⟨subcube 36 0,10,column23⟩,⟨subcube 516 0,10,column28⟩,⟨subcube 520 0,10,column29⟩,⟨subcube 0 8,9,column30⟩,⟨subcube 0 32,9,column31⟩,⟨subcube 1 64,9,column33⟩,⟨subcube 4 512,9,column39⟩,⟨subcube 8 4,9,column42⟩,⟨subcube 8 16,9,column43⟩,⟨subcube 8 512,9,column45⟩,⟨subcube 32 4,9,column50⟩,⟨subcube 32 64,9,column51⟩,⟨subcube 32 512,9,column53⟩,⟨subcube 33 0,9,column54⟩,⟨subcube 40 0,9,column55⟩,⟨subcube 256 16,9,column63⟩,⟨subcube 264 0,9,column66⟩,⟨subcube 1 4,8,column77⟩,⟨subcube 1 32,8,column79⟩,⟨subcube 12 0,8,column87⟩,⟨subcube 256 8,8,column99⟩,⟨subcube 256 512,8,column101⟩,⟨subcube 257 0,8,column102⟩,⟨subcube 260 0,8,column103⟩,⟨subcube 513 0,8,column109⟩,⟨subcube 544 0,8,column111⟩,⟨subcube 12 512,8,column114⟩,⟨subcube 544 4,8,column175⟩,⟨subcube 5 32,7,column212⟩]
def columnAt (i : Nat) : CertifiedColumn := columns[i]?.getD ⟨subcube 0 2,12,column0⟩
def rq : Array Row := #[33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,65,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,66,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,516,516,516,516,516,516,516,516,516,516,516,516,516,516,516,516,264,264,264,264,264,264,264,264,264,264,264,264,264,264,264,264,520,520,520,520,520,520,520,520,520,520,520,520,520,520,520,520,144,144,144,144,144,144,144,144,144,144,144,144,144,144,144,144,272,272,272,272,272,272,272,272,272,272,272,272,272,272,272,272,63,95,159,287,543,59,62,122,186,314,570,93,94,124,220,348,604,121,122,124,248,376,632,159,175,207,399,655,171,174,186,234,426,682,205,206,220,236,460,716,233,234,236,248,488,744,391,398,406,422,454,902,453,454,460,468,484,964,535,539,563,595,659,787,563,566,570,626,690,818,625,626,628,632,752,880,647,651,659,675,707,899,931,934,938,946,994,993,994,996,1000,1008,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33]
def sq : Array Row := #[31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,58,92,120,143,170,204,232,390,452,531,562,624,643,930,992,31,31,31,31,31,58,58,58,58,58,58,92,92,92,92,92,92,120,120,120,120,120,120,143,143,143,143,143,170,170,170,170,170,170,204,204,204,204,204,204,232,232,232,232,232,232,390,390,390,390,390,390,452,452,452,452,452,452,531,531,531,531,531,531,562,562,562,562,562,562,624,624,624,624,624,624,643,643,643,643,643,643,930,930,930,930,930,992,992,992,992,992,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31]
def rp (i : Fin 320) : Row := rq[i.val]?.getD 0
def sp (i : Fin 320) : Row := sq[i.val]?.getD 0
theorem pairRows : properPairs goal rp sp := by
  unfold properPairs
  decide +kernel
def base : List Decor := [(inputs.getD 0 zero,0xfffffffffffffffff087f041fc1041041f82083f0000000000000000000000000000ffffffffffff,0xfffffffffffffffff003f000fc0000000f80001f2411241124112411241124112411241124112411),(inputs.getD 1 zero,0x17ff0bffc2fc20bff8417ff000000000000000000000000ffff000000000000,0xfffffffffffffffff07ff03ffc0fc003ff8007ff6d336d336d336d336d336d336d336d336d336d33),(inputs.getD 2 zero,0x208110207ffc4fc2f89f85f0000000000000000ffffffff0000000000000000,0xfffffffffffffffff000000003ffc0fc0f81f81f0355035503550355035503550355035503550355),(inputs.getD 3 zero,0x41022040840bfffffffffff00000000ffffffff000000000000000000000000,0xfffffffffffffffff000000000003fffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff),(inputs.getD 4 zero,0x8204ffffc81081040ffffffffffffff00000000000000000000000000000000,0xfffffffffffffffff0000ffffc000000007fffff1c0f1c0f1c0f1c0f1c0f1c0f1c0f1c0f1c0f1c0f),(inputs.getD 5 zero,0xfffffffffffffffffffc8fff11023f23f17e27e100000000000000000000ffff000000000000ffff,0xffc0fff00003f03f07e07e0d8aad8aad8aad8aad8aad8aad8aad8aad8aad8aa),(inputs.getD 6 zero,0xfc10fc823f43ffc827ff882000000000000000000000000ffff0000ffff0000,0xf800fc003f03ffc007ff80092cc92cc92cc92cc92cc92cc92cc92cc92cc92cc),(inputs.getD 7 zero,0xffff41043ffffffff9041040000ffff00000000000000000000000000000000,0xffff00003ffffffff800000e3f0e3f0e3f0e3f0e3f0e3f0e3f0e3f0e3f0e3f0),(inputs.getD 8 zero,0xffe082083ffd04104208208ffff00000000ffff000000000000ffff00000000,0xffc000003ffc00000000000c300c300c300c300c300c300c300c300c300c300),(inputs.getD 9 zero,0xffffffffe0820820841041000000000ffff0000ffff00000000000000000000,0xffffffffc00000000000000fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00)]
theorem baseFaith : ∀ v ∈ base, faithful rp sp v := by
  have checked : base.all (fun v => v.2 == pairSig rp sp v.1)=true := by decide +kernel
  intro v h
  exact beq_iff_eq.mp (List.all_eq_true.mp checked v h)
def whole (d ops : Nat) := decodeBank d ops base
def liveWords (d ops m : Nat) := selectLive m (whole d ops)
def valWords (d ops m : Nat) := (liveWords d ops m).map Prod.fst
def prices (d ops : Nat) (fees : List (Nat × Nat)) : List BoundPool :=
  fees.filterMap (fun item =>
    let c := columnAt item.1
    materialize true raw (chosenSteps (whole d ops) ops item.2 d) c.domain c.bound)
theorem prices_sound (d ops : Nat) (fees : List (Nat × Nat)) :
    ∀p∈prices d ops fees, ValidPool true raw goal p := by
  intro p hp
  obtain ⟨it,_,ok⟩ := List.mem_filterMap.mp hp
  exact materialize_sound (columnAt it.1).valid ok
structure Failed (k : Nat) where
  bank : List Sig
  impossible : Impossible true goal k bank.toFinset
def linksOf {k} (links : Nat → List (Failed k)) (tag : Nat) := (links tag).map Failed.bank
def check (cap d ops m : Nat) (fees : List (Nat × Nat)) (links : Nat → List (Failed (cap-1))) : Bool :=
  let ws := liveWords d ops m
  decide (valWords d ops m).Nodup && !(valWords d ops m).contains goal &&
     testAll (cap,ws.length,ws,preCov true ws,prices d ops fees,linksOf links) ws
def finish (cap d ops m : Nat) (fees : List (Nat × Nat)) (links : Nat → List (Failed (cap-1)))
    (ok : check cap d ops m fees links=true) : Failed cap := by
  have tested := ok
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at tested
  refine ⟨valWords d ops m,?_⟩
  apply node_sound (raw:=raw) pairRows _ tested.1.1 _ (prices_sound d ops fees) _ tested.2
  · intro w hw
    exact decode_faithful _ _ base rp sp baseFaith w ((selectLive_sub _ _).subset hw)
  · intro hm
    have h : (valWords d ops m).contains goal=true := by
      simpa only [List.contains_eq_mem, decide_eq_true_eq, valWords] using hm
    have hz : (valWords d ops m).contains goal=false := by simpa only [List.contains_eq_mem] using tested.1.2
    rw [h] at hz
    contradiction
  · intro tag xs hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    exact v.impossible

end PEqualNP.Outside.L_meta_9750.Gap4029
