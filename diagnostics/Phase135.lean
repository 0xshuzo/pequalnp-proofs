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
abbrev Failed (_k : Nat) := List Sig
structure ReadyFee where
  domain : Sig
  bound : Nat
  paid : Nat
  maskedWires : List Sig
  knownBad : List Sig
  fixed : Nat

def preparedAvail (domain : Sig) (words : List Sig) (x : Sig) : Bool :=
  let m := masked domain x
  m == zero || m == domain || words.contains m || words.contains (masked domain (neg x))

def readyFee (p : BoundPool) (ws : List Sig) : ReadyFee :=
  let d := p.domain
  let words := p.wires.map (masked d)
  ⟨d,p.bound,p.paid,words,ws.filter (fun x => !preparedAvail d words x),ws.countP (isMaskedConstant d)⟩

def feeDies (f : ReadyFee) (budget : Nat) (a b z : Sig) (ka kb : Bool) : Bool :=
  if !f.knownBad.all (fun x => (!ka && x==a) || (!kb && x==b)) then false else
  let constant := isMaskedConstant f.domain z
  let fixed := f.fixed - ((!ka && isMaskedConstant f.domain a).toNat)
     - ((!kb && isMaskedConstant f.domain b).toNat)
  let limit := f.bound+fixed+constant.toNat
  let paid := budget+f.paid
  if limit≤paid then false else
  let extra := !preparedAvail f.domain f.maskedWires z
  if !extra then true else
    paid+1<limit && preparedAvail f.domain f.maskedWires a && preparedAvail f.domain f.maskedWires b

def supportPhases (rows signal : Bits) (zeroMask oneMask : Nat) : Nat :=
  let q := rows &&& signal
  (if q==0 then zeroMask else 0) ||| (if q==rows then oneMask else 0)

structure PhasePair where
  a : Decor
  b : Decor
  ws : List Decor
  words : List Sig
  fees : List ReadyFee
  budget : Nat
  links : Nat → List (List Sig)

def phaseMove (q : PhasePair) (z : Sig) (ka kb : Bool) : Bool :=
  if q.fees.any (fun f => feeDies f q.budget q.a.1 q.b.1 z ka kb) then true else
  let bank := z :: (delTwo q.ws q.a q.b ka kb).map Prod.fst
  (q.links (keySet bank)).any (sameWords bank)

def phaseGate (q : PhasePair) (op ab aOnly bOnly both : Nat) : Bool :=
  if !((ab ||| aOnly ||| bOnly ||| both).testBit op) then true else
  let z := bin op q.a.1 q.b.1
  if !properB z || q.words.contains z then true else
  (!ab.testBit op || phaseMove q z false false) &&
  (!aOnly.testBit op || phaseMove q z true false) &&
  (!bOnly.testBit op || phaseMove q z false true) &&
  (!both.testBit op || phaseMove q z true true)

def phaseCheck (cap d ops m : Nat) (fees : List (Nat × Nat))
    (links : Nat → List (Failed (cap-1))) : Bool :=
  let ws := liveWords d ops m
  let words := ws.map Prod.fst
  let n := ws.length
  let fs := (prices d ops fees).map (fun p => readyFee p words)
  let cv := coverage false ws
  let singles := cv.2.1
  let doubles := cv.2.2
  let both := if n+1≤cap then 15 else 0
  let row (a b : Decor) :=
    let ca := a.2.1 ^^^ a.2.2
    let cb := b.2.1 ^^^ b.2.2
    let ma := supportPhases (singles &&& ca) b.2.1 6 9
    let mb := supportPhases (singles &&& cb) a.2.1 10 5
    let mab := if (ma &&& mb) == 0 then 0 else
      (ma &&& mb) &&& supportPhases (doubles &&& ca &&& cb) (a.2.1 ^^^ b.2.1) 3 12
    let aOnly := if n≤cap then mb else 0
    let bOnly := if n≤cap then ma else 0
    let q : PhasePair := ⟨a,b,ws,words,fs,cap-1,links⟩
    phaseGate q 0 mab aOnly bOnly both && phaseGate q 1 mab aOnly bOnly both &&
      phaseGate q 2 mab aOnly bOnly both && phaseGate q 3 mab aOnly bOnly both
  let rec allPairs : List Decor → Bool
    | [] => true
    | a::bs => bs.all (row a) && allPairs bs
  decide words.Nodup && !words.contains goal &&
    (cv.1 != BitVec.allOnes 320 || n>cap+1 || allPairs ws)
def finish (cap d ops m : Nat) (fees : List (Nat × Nat)) (links : Nat → List (Failed (cap-1)))
    (_ : phaseCheck cap d ops m fees links=true) : Failed cap := valWords d ops m
def state21 : Failed 9 :=
  finish 9 4 27097037800544 11006 [(2, 15), (3, 15), (36, 0)] (fun _ => []) (by decide +kernel)
def children3 (code : Nat) : List (Failed 9) :=
  if code=9889397882390767932 then [state21] else
  []
def state6 : Failed 10 :=
  finish 10 3 57005835328 7135 [(3, 7), (1, 5), (2, 7), (16, 4)] children3 (by decide +kernel)
def state8 : Failed 10 :=
  finish 10 3 56997446720 7135 [(2, 7), (3, 7), (16, 4)] children3 (by decide +kernel)
def state18 : Failed 10 :=
  finish 10 3 57047778400 6911 [(2, 7), (3, 7), (16, 0), (21, 0)] children3 (by decide +kernel)
def state20 : Failed 10 :=
  finish 10 3 21563966560 7934 [(2, 7), (3, 7), (36, 0)] children3 (by decide +kernel)
def state26 : Failed 10 :=
  finish 10 3 6078616672 5119 [(36, 0), (2, 7), (3, 7), (7, 5)] children3 (by decide +kernel)
def state28 : Failed 10 :=
  finish 10 3 57584931936 4863 [(2, 7), (3, 7), (0, 7), (1, 7)] children3 (by decide +kernel)
def state31 : Failed 10 :=
  finish 10 3 23233582176 5119 [(22, 0), (2, 7), (3, 7)] children3 (by decide +kernel)
def state33 : Failed 10 :=
  finish 10 3 57534612576 5087 [(2, 7), (3, 7), (0, 7), (1, 7)] children3 (by decide +kernel)
def state39 : Failed 10 :=
  finish 10 3 22688192672 7135 [(2, 7), (3, 7), (4, 5), (9, 0)] children3 (by decide +kernel)
def state46 : Failed 10 :=
  finish 10 3 57501058208 5111 [(2, 7), (3, 7), (0, 7), (1, 7)] children3 (by decide +kernel)
def state49 : Failed 10 :=
  finish 10 3 57618202880 6910 [(10, 7), (11, 7), (31, 0), (34, 0), (4, 7), (9, 7), (35, 0), (39, 0), (2, 7), (3, 7)] children3 (by decide +kernel)
def state50 : Failed 10 :=
  finish 10 3 57618202880 4862 [(10, 7), (11, 7), (18, 7), (20, 7), (31, 0), (35, 0), (34, 0), (39, 0), (2, 7), (3, 7)] children3 (by decide +kernel)
def state65 : Failed 10 :=
  finish 10 3 57450596608 6142 [(1, 7), (2, 7), (3, 7), (9, 5)] children3 (by decide +kernel)
def state66 : Failed 10 :=
  finish 10 3 57500928256 6135 [(2, 7), (0, 6), (3, 7), (17, 4)] children3 (by decide +kernel)
def state70 : Failed 10 :=
  finish 10 3 57600779520 5631 [(2, 7), (3, 7), (34, 4)] children3 (by decide +kernel)
def state73 : Failed 10 :=
  finish 10 3 57534588160 6111 [(2, 7), (3, 7), (35, 0)] children3 (by decide +kernel)
def state76 : Failed 10 :=
  finish 10 3 57534592256 6111 [(2, 7), (3, 7), (34, 4)] children3 (by decide +kernel)
def state77 : Failed 10 :=
  finish 10 3 57601701120 5631 [(2, 7), (3, 7), (34, 4)] children3 (by decide +kernel)
def state81 : Failed 10 :=
  finish 10 3 57450452224 6142 [(2, 7), (3, 7), (16, 0), (22, 0)] children3 (by decide +kernel)
def state84 : Failed 10 :=
  finish 10 3 57484137728 6139 [(2, 7), (3, 7), (31, 4)] children3 (by decide +kernel)
def state86 : Failed 10 :=
  finish 10 3 57484268800 6139 [(2, 7), (3, 7), (31, 4)] children3 (by decide +kernel)
def state87 : Failed 10 :=
  finish 10 3 57501046016 6135 [(2, 7), (3, 7), (31, 4)] children3 (by decide +kernel)
def state90 : Failed 10 :=
  finish 10 3 57450595584 6142 [(2, 7), (3, 7), (15, 0), (16, 0)] children3 (by decide +kernel)
def state91 : Failed 10 :=
  finish 10 3 57500927232 6135 [(2, 7), (3, 7), (17, 4)] children3 (by decide +kernel)
def state93 : Failed 10 :=
  finish 10 3 57501062400 6135 [(2, 7), (3, 7), (38, 0)] children3 (by decide +kernel)
def state102 : Failed 10 :=
  finish 10 3 23099094114 6135 [(2, 7), (3, 7), (4, 0), (9, 6)] children3 (by decide +kernel)
def state113 : Failed 10 :=
  finish 10 3 57450726563 5118 [(2, 7), (3, 7), (0, 7), (1, 7)] children3 (by decide +kernel)
def state125 : Failed 10 :=
  finish 10 3 23099356421 5119 [(21, 0), (2, 7), (3, 7)] children3 (by decide +kernel)
def children2 (code : Nat) : List (Failed 10) :=
  if code=7026657812532033169 then [state6] else
  if code=8691854719050475871 then [state8] else
  if code=8647889981809343244 then [state18] else
  if code=9918650160236667676 then [state20] else
  if code=8406346566219250339 then [state26] else
  if code=6494799886369151477 then [state28] else
  if code=6498640032406813330 then [state31] else
  if code=5159563525596969460 then [state33] else
  if code=8412947160465530633 then [state39] else
  if code=8438385224491619564 then [state46] else
  if code=9297066115737040152 then [state49] else
  if code=7284579296275597548 then [state50] else
  if code=8390545952257554238 then [state65] else
  if code=8238528329614317781 then [state66] else
  if code=8337971608308465083 then [state70] else
  if code=7279330664617591096 then [state73] else
  if code=7172050345058412064 then [state76] else
  if code=9077376175732885083 then [state77] else
  if code=9992987661112138978 then [state81] else
  if code=8627005762133432462 then [state84] else
  if code=8453483430977935173 then [state86] else
  if code=10450872043953062168 then [state87] else
  if code=9816300646826565465 then [state90] else
  if code=9664283024183329008 then [state91] else
  if code=8362972786755085535 then [state93] else
  if code=8584799624862402933 then [state102] else
  if code=7538341248091665397 then [state113] else
  if code=7005617165491394498 then [state125] else
  []
def state2 : Failed 11 :=
  finish 11 2 5539904 3071 [(18, 2), (11, 3), (10, 3), (25, 0), (9, 3), (16, 0), (3, 3), (15, 0), (2, 3)] children2 (by decide +kernel)
def state3 : Failed 11 :=
  finish 11 2 5544000 2559 [(10, 3), (11, 3), (18, 2), (25, 0), (16, 0), (15, 0), (3, 3), (2, 3)] children2 (by decide +kernel)
def state5 : Failed 11 :=
  finish 11 2 13632576 4095 [(46, 0), (12, 0), (3, 3), (0, 3), (1, 1), (2, 3), (4, 2), (7, 2)] children2 (by decide +kernel)
def state7 : Failed 11 :=
  finish 11 2 5243968 4095 [(46, 0), (12, 0), (2, 3), (3, 3), (4, 2), (7, 2)] children2 (by decide +kernel)
def state9 : Failed 11 :=
  finish 11 2 13915200 3039 [(10, 3), (11, 3), (19, 2), (25, 0), (28, 0), (2, 3), (3, 3), (16, 2)] children2 (by decide +kernel)
def state10 : Failed 11 :=
  finish 11 2 13927488 3071 [(46, 0), (10, 3), (11, 3), (12, 0), (3, 3), (2, 3), (5, 0), (9, 0), (15, 0), (21, 0)] children2 (by decide +kernel)
def state12 : Failed 11 :=
  finish 11 2 5245024 4094 [(31, 0), (34, 0), (10, 3), (11, 3), (15, 1), (2, 3), (3, 3)] children2 (by decide +kernel)
def state13 : Failed 11 :=
  finish 11 2 5539936 3071 [(31, 0), (11, 3), (10, 3), (5, 2), (9, 3), (25, 2), (3, 3), (4, 0), (15, 0), (2, 3)] children2 (by decide +kernel)
def state14 : Failed 11 :=
  finish 11 2 5544032 2559 [(10, 3), (11, 3), (24, 0), (16, 0), (5, 2), (30, 0), (3, 3), (2, 3)] children2 (by decide +kernel)
def state16 : Failed 11 :=
  finish 11 2 9438304 4094 [(34, 0), (10, 3), (11, 3), (31, 0), (2, 3), (3, 3), (9, 3), (15, 1), (35, 0)] children2 (by decide +kernel)
def state17 : Failed 11 :=
  finish 11 2 5244000 4095 [(5, 2), (16, 0), (2, 3), (17, 0), (0, 3), (3, 3), (21, 0)] children2 (by decide +kernel)
def state19 : Failed 11 :=
  finish 11 2 5244000 4094 [(34, 0), (38, 0), (10, 3), (11, 3), (15, 1), (2, 3), (3, 3), (16, 0)] children2 (by decide +kernel)
def state22 : Failed 11 :=
  finish 11 2 4596832 4087 [(38, 0), (19, 1), (11, 3), (10, 3), (35, 0), (18, 1), (2, 3), (3, 3), (16, 0)] children2 (by decide +kernel)
def state23 : Failed 11 :=
  finish 11 2 4863072 4087 [(38, 0), (32, 0), (2, 3), (3, 3), (20, 0), (0, 3), (1, 3), (4, 3), (12, 2)] children2 (by decide +kernel)
def state24 : Failed 11 :=
  finish 11 2 5256288 4087 [(34, 0), (21, 0), (10, 3), (2, 3), (20, 0), (0, 3), (3, 3)] children2 (by decide +kernel)
def state25 : Failed 11 :=
  finish 11 2 5264480 4095 [(36, 0), (7, 1), (2, 3), (3, 3), (21, 0)] children2 (by decide +kernel)
def state27 : Failed 11 :=
  finish 11 2 5526624 3071 [(38, 0), (10, 3), (11, 3), (18, 1), (2, 3), (3, 3), (9, 3), (12, 0), (15, 0), (17, 0), (31, 0)] children2 (by decide +kernel)
def state29 : Failed 11 :=
  finish 11 2 13915232 4095 [(21, 0), (5, 2), (2, 3), (3, 3), (7, 0)] children2 (by decide +kernel)
def state30 : Failed 11 :=
  finish 11 2 13915232 3071 [(22, 0), (18, 1), (10, 3), (11, 3), (20, 2), (2, 3), (3, 3), (17, 0)] children2 (by decide +kernel)
def state32 : Failed 11 :=
  finish 11 2 5538912 3071 [(21, 0), (10, 3), (11, 3), (20, 2), (34, 0), (2, 3), (7, 0), (3, 3), (4, 0), (12, 0), (13, 0), (15, 0), (22, 0)] children2 (by decide +kernel)
def state34 : Failed 11 :=
  finish 11 2 13927520 3071 [(34, 0), (10, 3), (11, 3), (7, 3), (9, 3), (25, 2), (2, 3), (4, 0), (15, 0), (22, 0), (3, 3), (21, 0)] children2 (by decide +kernel)
def state36 : Failed 11 :=
  finish 11 2 5257376 4095 [(21, 0), (34, 0), (2, 3), (7, 2), (0, 2), (3, 3), (5, 1), (9, 1), (22, 0), (30, 0)] children2 (by decide +kernel)
def state37 : Failed 11 :=
  finish 11 2 5519520 3071 [(38, 0), (20, 1), (11, 3), (10, 3), (18, 2), (2, 3), (3, 3)] children2 (by decide +kernel)
def state38 : Failed 11 :=
  finish 11 2 5396640 4063 [(45, 0), (16, 2), (2, 3), (3, 3), (1, 3), (11, 3), (15, 1), (4, 1), (20, 1)] children2 (by decide +kernel)
def state40 : Failed 11 :=
  finish 11 2 5540000 3071 [(11, 3), (10, 3), (7, 2), (16, 0), (4, 3), (3, 3), (5, 0), (9, 0), (12, 0), (15, 0), (21, 0), (2, 3)] children2 (by decide +kernel)
def state42 : Failed 11 :=
  finish 11 2 13644960 4095 [(21, 0), (3, 3), (5, 1), (7, 2), (22, 0), (1, 1), (2, 3), (4, 2), (25, 0), (31, 0)] children2 (by decide +kernel)
def state43 : Failed 11 :=
  finish 11 2 5256352 4095 [(21, 0), (2, 3), (3, 3), (4, 2), (5, 1), (7, 2), (9, 1), (22, 0), (25, 0), (30, 0), (31, 0)] children2 (by decide +kernel)
def state44 : Failed 11 :=
  finish 11 2 5264544 4063 [(31, 0), (22, 0), (11, 3), (3, 3), (18, 0), (1, 3), (2, 3)] children2 (by decide +kernel)
def state45 : Failed 11 :=
  finish 11 2 5538976 3071 [(22, 0), (11, 3), (10, 3), (18, 2), (31, 0), (3, 3), (5, 0), (2, 3), (9, 0), (12, 0), (14, 0), (15, 0), (21, 0)] children2 (by decide +kernel)
def state48 : Failed 11 :=
  finish 11 2 5243136 3838 [(31, 0), (10, 3), (11, 3), (19, 3), (34, 0), (35, 0), (39, 0), (2, 3), (3, 3)] children2 (by decide +kernel)
def state51 : Failed 11 :=
  finish 11 2 5513472 3067 [(10, 3), (11, 3), (25, 0), (16, 0), (17, 0), (28, 0), (2, 3), (3, 3)] children2 (by decide +kernel)
def state52 : Failed 11 :=
  finish 11 2 5517568 3063 [(10, 3), (11, 3), (34, 0), (31, 0), (19, 3), (2, 3), (3, 3)] children2 (by decide +kernel)
def state53 : Failed 11 :=
  finish 11 2 5521664 3055 [(11, 3), (26, 0), (31, 0), (3, 3), (17, 0), (19, 3), (2, 3)] children2 (by decide +kernel)
def state54 : Failed 11 :=
  finish 11 2 5525760 3039 [(10, 3), (11, 3), (31, 0), (34, 0), (19, 3), (2, 3), (3, 3)] children2 (by decide +kernel)
def state55 : Failed 11 :=
  finish 11 2 5529856 3007 [(10, 3), (29, 0), (34, 0), (2, 3), (16, 0), (19, 3), (3, 3)] children2 (by decide +kernel)
def state56 : Failed 11 :=
  finish 11 2 5542144 2559 [(10, 3), (11, 3), (24, 0), (16, 0), (17, 0), (27, 0), (2, 3), (3, 3)] children2 (by decide +kernel)
def state58 : Failed 11 :=
  finish 11 2 9440512 3838 [(10, 3), (11, 3), (31, 0), (34, 0), (19, 3), (2, 3), (3, 3)] children2 (by decide +kernel)
def state59 : Failed 11 :=
  finish 11 2 5508352 3071 [(10, 3), (11, 3), (31, 0), (34, 0), (4, 0), (9, 0), (12, 0), (15, 0), (2, 3), (3, 3)] children2 (by decide +kernel)
def state60 : Failed 11 :=
  finish 11 2 5266688 3839 [(36, 0), (31, 0), (11, 3), (3, 3), (17, 0), (1, 3), (2, 3), (12, 2)] children2 (by decide +kernel)
def state61 : Failed 11 :=
  finish 11 2 5528832 3071 [(22, 0), (7, 1), (10, 3), (11, 3), (2, 3), (3, 3), (4, 0), (5, 0), (9, 0), (12, 0), (15, 0), (21, 0)] children2 (by decide +kernel)
def state63 : Failed 11 :=
  finish 11 2 5519616 3071 [(21, 0), (5, 1), (10, 3), (11, 3), (2, 3), (3, 3), (4, 0), (7, 0), (9, 0), (12, 0), (15, 0), (22, 0)] children2 (by decide +kernel)
def state64 : Failed 11 :=
  finish 11 2 5409024 4095 [(9, 1), (2, 3), (15, 0), (0, 2), (1, 3), (3, 3), (5, 1), (16, 0), (17, 0)] children2 (by decide +kernel)
def state68 : Failed 11 :=
  finish 11 2 5375232 4095 [(42, 0), (15, 0), (2, 3), (3, 3), (9, 1)] children2 (by decide +kernel)
def state69 : Failed 11 :=
  finish 11 2 4596992 4095 [(38, 0), (37, 0), (2, 3), (3, 3), (4, 1), (9, 1), (12, 0)] children2 (by decide +kernel)
def state71 : Failed 11 :=
  finish 11 2 5252352 4095 [(41, 0), (12, 0), (2, 3), (3, 3), (4, 1)] children2 (by decide +kernel)
def state72 : Failed 11 :=
  finish 11 2 5514496 4095 [(4, 1), (35, 0), (2, 3), (3, 3), (7, 1), (41, 0), (46, 0)] children2 (by decide +kernel)
def state74 : Failed 11 :=
  finish 11 2 4863232 4095 [(36, 0), (32, 0), (2, 3), (3, 3), (5, 1), (38, 0)] children2 (by decide +kernel)
def state75 : Failed 11 :=
  finish 11 2 5518592 4095 [(34, 0), (2, 3), (3, 3), (6, 1), (7, 1), (9, 1), (21, 0), (33, 0)] children2 (by decide +kernel)
def state78 : Failed 11 :=
  finish 11 2 13907200 3071 [(21, 0), (5, 1), (10, 3), (11, 3), (2, 3), (3, 3), (4, 0), (7, 0), (9, 0), (12, 0), (15, 0), (22, 0)] children2 (by decide +kernel)
def state79 : Failed 11 :=
  finish 11 2 13653248 3839 [(31, 0), (34, 0), (10, 3), (11, 3), (12, 2), (2, 3), (3, 3)] children2 (by decide +kernel)
def state80 : Failed 11 :=
  finish 11 2 5264640 4095 [(7, 1), (17, 0), (3, 3), (16, 0), (1, 3), (2, 3), (22, 0)] children2 (by decide +kernel)
def state82 : Failed 11 :=
  finish 11 2 5264640 3839 [(31, 0), (36, 0), (10, 3), (11, 3), (12, 2), (2, 3), (3, 3), (17, 0)] children2 (by decide +kernel)
def state83 : Failed 11 :=
  finish 11 2 5395712 4095 [(36, 0), (43, 0), (2, 3), (3, 3), (4, 1), (7, 1), (15, 0)] children2 (by decide +kernel)
def state85 : Failed 11 :=
  finish 11 2 5526784 4095 [(31, 0), (2, 3), (3, 3), (4, 1), (5, 1), (8, 1), (22, 0), (23, 0)] children2 (by decide +kernel)
def state88 : Failed 11 :=
  finish 11 2 13915392 3071 [(22, 0), (7, 1), (10, 3), (11, 3), (2, 3), (3, 3), (4, 0), (5, 0), (9, 0), (12, 0), (15, 0), (21, 0)] children2 (by decide +kernel)
def state89 : Failed 11 :=
  finish 11 2 5408000 4095 [(9, 1), (15, 0), (2, 3), (3, 3), (5, 1), (16, 0), (17, 0)] children2 (by decide +kernel)
def state92 : Failed 11 :=
  finish 11 2 5543168 4095 [(9, 1), (39, 0), (2, 3), (3, 3), (5, 1), (42, 0)] children2 (by decide +kernel)
def state95 : Failed 11 :=
  finish 11 2 5515552 3067 [(10, 3), (11, 3), (20, 2), (28, 0), (16, 0), (3, 3), (2, 3)] children2 (by decide +kernel)
def state96 : Failed 11 :=
  finish 11 2 5519648 3063 [(10, 3), (11, 3), (19, 2), (30, 0), (16, 0), (27, 0), (3, 3), (2, 3)] children2 (by decide +kernel)
def state97 : Failed 11 :=
  finish 11 2 5540128 3071 [(20, 2), (11, 3), (10, 3), (30, 0), (4, 3), (16, 0), (3, 3), (12, 0), (2, 3)] children2 (by decide +kernel)
def state99 : Failed 11 :=
  finish 11 2 13927712 3071 [(42, 0), (39, 0), (2, 3), (3, 3), (20, 2), (0, 3), (1, 3)] children2 (by decide +kernel)
def state101 : Failed 11 :=
  finish 11 2 13644898 4087 [(44, 0), (17, 1), (3, 3), (2, 3), (0, 3), (10, 3), (12, 2), (9, 2), (18, 2)] children2 (by decide +kernel)
def state103 : Failed 11 :=
  finish 11 2 13931618 2559 [(10, 3), (11, 3), (18, 2), (34, 2), (15, 0), (2, 3), (3, 3), (5, 2), (35, 0)] children2 (by decide +kernel)
def state105 : Failed 11 :=
  finish 11 2 5508354 3071 [(18, 2), (10, 3), (11, 3), (25, 0), (9, 3), (17, 0), (2, 3), (15, 0), (3, 3)] children2 (by decide +kernel)
def state106 : Failed 11 :=
  finish 11 2 5528834 3039 [(10, 3), (11, 3), (19, 2), (25, 0), (17, 0), (28, 0), (2, 3), (3, 3)] children2 (by decide +kernel)
def state107 : Failed 11 :=
  finish 11 2 5545218 2559 [(10, 3), (11, 3), (18, 2), (25, 0), (17, 0), (15, 0), (2, 3), (3, 3)] children2 (by decide +kernel)
def state109 : Failed 11 :=
  finish 11 2 13894914 3071 [(41, 0), (35, 0), (2, 3), (3, 3), (18, 2), (0, 3), (1, 3)] children2 (by decide +kernel)
def state111 : Failed 11 :=
  finish 11 2 5264547 4063 [(36, 0), (32, 0), (3, 3), (2, 3), (18, 0), (1, 3), (0, 3), (9, 3), (15, 1)] children2 (by decide +kernel)
def state112 : Failed 11 :=
  finish 11 2 5538979 3071 [(36, 0), (10, 3), (11, 3), (20, 2), (2, 3), (3, 3), (4, 3), (12, 0), (15, 0), (16, 0), (32, 0)] children2 (by decide +kernel)
def state115 : Failed 11 :=
  finish 11 2 5508355 3071 [(10, 3), (11, 3), (5, 2), (17, 0), (9, 3), (2, 3), (4, 0), (7, 0), (12, 0), (15, 0), (22, 0), (3, 3)] children2 (by decide +kernel)
def state116 : Failed 11 :=
  finish 11 2 5528835 3071 [(36, 0), (18, 1), (10, 3), (11, 3), (20, 2), (3, 3), (2, 3)] children2 (by decide +kernel)
def state119 : Failed 11 :=
  finish 11 2 5508357 3071 [(31, 0), (10, 3), (11, 3), (34, 0), (4, 3), (30, 2), (9, 0), (12, 0), (2, 3), (3, 3)] children2 (by decide +kernel)
def state120 : Failed 11 :=
  finish 11 2 5516549 3067 [(10, 3), (11, 3), (25, 0), (17, 0), (7, 2), (2, 3), (9, 3), (30, 2), (3, 3)] children2 (by decide +kernel)
def state122 : Failed 11 :=
  finish 11 2 13894917 3071 [(31, 0), (11, 3), (10, 3), (4, 3), (5, 3), (30, 2), (3, 3), (9, 0), (12, 0), (21, 0), (2, 3), (22, 0)] children2 (by decide +kernel)
def state123 : Failed 11 :=
  finish 11 2 13907205 4095 [(22, 0), (5, 1), (2, 3), (3, 3), (7, 2)] children2 (by decide +kernel)
def state124 : Failed 11 :=
  finish 11 2 13907205 3071 [(21, 0), (20, 1), (10, 3), (11, 3), (18, 2), (2, 3), (3, 3), (16, 0)] children2 (by decide +kernel)
def state126 : Failed 11 :=
  finish 11 2 5395717 4063 [(36, 0), (20, 1), (10, 3), (18, 0), (11, 3), (3, 3), (17, 0), (2, 3), (15, 1)] children2 (by decide +kernel)
def state128 : Failed 11 :=
  finish 11 2 13903141 3067 [(10, 3), (11, 3), (20, 2), (31, 2), (12, 0), (2, 3), (3, 3), (7, 2), (39, 0)] children2 (by decide +kernel)
def state130 : Failed 11 :=
  finish 11 2 5507368 3071 [(20, 2), (10, 3), (11, 3), (30, 0), (4, 3), (17, 0), (2, 3), (12, 0), (3, 3)] children2 (by decide +kernel)
def state131 : Failed 11 :=
  finish 11 2 5515560 3067 [(10, 3), (11, 3), (20, 2), (28, 0), (17, 0), (2, 3), (3, 3)] children2 (by decide +kernel)
def state133 : Failed 11 :=
  finish 11 2 13894952 3071 [(20, 2), (10, 3), (11, 3), (15, 0), (2, 3), (3, 3), (4, 0), (7, 0), (12, 0), (22, 0), (16, 0)] children2 (by decide +kernel)
def state134 : Failed 11 :=
  finish 11 2 13907240 3063 [(10, 3), (11, 3), (19, 2), (30, 0), (27, 0), (2, 3), (3, 3), (17, 2)] children2 (by decide +kernel)
def children1 (code : Nat) : List (Failed 11) :=
  if code=7360674113630702137 then [state2] else
  if code=6743919574358868722 then [state3] else
  if code=7075401949365385359 then [state5] else
  if code=8740598855883828061 then [state7] else
  if code=6679367899589033267 then [state9] else
  if code=8701927247343554035 then [state10] else
  if code=8616779083250376813 then [state12] else
  if code=7135416584522928297 then [state13] else
  if code=7121245200363004339 then [state14] else
  if code=7295104258071707907 then [state16] else
  if code=8977085943104220823 then [state17] else
  if code=8720858952640719134 then [state19] else
  if code=8877017632711345982 then [state22] else
  if code=7926481912578432394 then [state23] else
  if code=6893673056226348627 then [state24] else
  if code=8435598844065150083 then [state25] else
  if code=6867394172511498121 then [state27] else
  if code=9251301515700147017 then [state29] else
  if code=8782513093206597443 then [state30] else
  if code=7733045268794141976 then [state32] else
  if code=6908611675174323962 then [state34] else
  if code=8048704004884411377 then [state36] else
  if code=8177041297292314239 then [state37] else
  if code=7905446374542670871 then [state38] else
  if code=8347075788322130768 then [state40] else
  if code=8543462600450770029 then [state42] else
  if code=7233070122229894477 then [state43] else
  if code=6706698152672182328 then [state44] else
  if code=7375512811749810668 then [state45] else
  if code=9185835770943785231 then [state48] else
  if code=7334512731517591724 then [state51] else
  if code=8416934523443519339 then [state52] else
  if code=5370093818240813634 then [state53] else
  if code=5279923812951754570 then [state54] else
  if code=8511873718814493775 then [state55] else
  if code=8032507656424181935 then [state56] else
  if code=6900397235694734913 then [state58] else
  if code=8508297520610671249 then [state59] else
  if code=8040891821688177089 then [state60] else
  if code=8711142828946684772 then [state61] else
  if code=8745855268479095243 then [state63] else
  if code=9084707698711704207 then [state64] else
  if code=9624113289316465389 then [state68] else
  if code=10700771099580808975 then [state69] else
  if code=9761062694569532604 then [state71] else
  if code=10105424777778744229 then [state72] else
  if code=9750235379447895387 then [state74] else
  if code=9745532088255584580 then [state75] else
  if code=7390500245706716843 then [state78] else
  if code=10135958354205658282 then [state79] else
  if code=9979297241033043113 then [state80] else
  if code=9706088728206619791 then [state82] else
  if code=10362411580249014756 then [state83] else
  if code=9387999631211253272 then [state85] else
  if code=6624674456355294328 then [state88] else
  if code=10510462393280715434 then [state89] else
  if code=9559952618459904360 then [state92] else
  if code=6329092020988559141 then [state95] else
  if code=8234878640285127447 then [state96] else
  if code=8123977240042330769 then [state97] else
  if code=8235494377429548320 then [state99] else
  if code=9927750690923812331 then [state101] else
  if code=6325484788847022479 then [state103] else
  if code=8628390977892786137 then [state105] else
  if code=6051389005046565409 then [state106] else
  if code=7187905560622025809 then [state107] else
  if code=8416948664317555119 then [state109] else
  if code=7420505592913881005 then [state111] else
  if code=8188175655780558344 then [state112] else
  if code=6672381115793835170 then [state115] else
  if code=8027416576522694043 then [state116] else
  if code=6581451970934775816 then [state119] else
  if code=7468436524372961163 then [state120] else
  if code=8236727832114198063 then [state122] else
  if code=8528206822232834009 then [state123] else
  if code=7057207101810462145 then [state124] else
  if code=8032681793715000374 then [state126] else
  if code=6614518942671989858 then [state128] else
  if code=8737624717474236561 then [state130] else
  if code=6039023562933180409 then [state131] else
  if code=8060040817828624550 then [state133] else
  if code=7651796204721886404 then [state134] else
  []
def state1 : Failed 12 :=
  finish 12 1 2112 2047 [(25, 0), (11, 1), (10, 1), (19, 0), (18, 0), (16, 0), (2, 1), (3, 1), (17, 0)] children1 (by decide +kernel)
def state4 : Failed 12 :=
  finish 12 1 1088 2047 [(25, 0), (11, 1), (10, 1), (18, 0), (19, 0), (2, 1), (3, 1), (16, 0), (17, 0)] children1 (by decide +kernel)
def state11 : Failed 12 :=
  finish 12 1 2144 2047 [(31, 0), (10, 1), (11, 1), (20, 0), (4, 1), (25, 0), (2, 1), (3, 1), (17, 0)] children1 (by decide +kernel)
def state15 : Failed 12 :=
  finish 12 1 1120 2047 [(11, 1), (20, 0), (10, 1), (18, 1), (38, 0), (25, 0), (31, 0), (2, 1), (3, 1), (17, 0)] children1 (by decide +kernel)
def state35 : Failed 12 :=
  finish 12 1 2208 2047 [(16, 0), (10, 1), (11, 1), (18, 0), (20, 1), (30, 0), (2, 1), (3, 1), (17, 0), (40, 0)] children1 (by decide +kernel)
def state41 : Failed 12 :=
  finish 12 1 1184 2047 [(31, 0), (11, 1), (10, 1), (18, 0), (20, 1), (30, 0), (3, 1), (2, 1), (17, 0)] children1 (by decide +kernel)
def state47 : Failed 12 :=
  finish 12 1 256 2047 [(31, 0), (10, 1), (11, 1), (34, 0), (19, 1), (2, 1), (3, 1), (4, 0), (5, 0), (7, 0), (9, 0), (12, 0), (15, 0)] children1 (by decide +kernel)
def state57 : Failed 12 :=
  finish 12 1 3328 2047 [(34, 0), (11, 1), (10, 1), (18, 1), (19, 1), (31, 0), (2, 1), (3, 1), (39, 0), (12, 0), (15, 0)] children1 (by decide +kernel)
def state62 : Failed 12 :=
  finish 12 1 2304 2047 [(31, 0), (10, 1), (11, 1), (19, 1), (34, 0), (2, 1), (3, 1), (35, 0), (12, 0), (15, 0), (20, 1)] children1 (by decide +kernel)
def state67 : Failed 12 :=
  finish 12 1 1280 2047 [(10, 1), (11, 1), (31, 0), (34, 0), (19, 1), (40, 0), (2, 1), (3, 1), (12, 0), (15, 0), (18, 1), (20, 1)] children1 (by decide +kernel)
def state94 : Failed 12 :=
  finish 12 1 2336 2047 [(30, 0), (11, 1), (10, 1), (19, 0), (20, 0), (16, 0), (2, 1), (3, 1), (17, 0)] children1 (by decide +kernel)
def state98 : Failed 12 :=
  finish 12 1 1312 2047 [(30, 0), (11, 1), (10, 1), (19, 0), (20, 0), (2, 1), (3, 1), (16, 0), (17, 0), (39, 0)] children1 (by decide +kernel)
def state100 : Failed 12 :=
  finish 12 1 1122 2047 [(44, 0), (10, 1), (11, 1), (18, 0), (12, 0), (2, 1), (3, 1), (34, 0), (9, 0), (35, 0)] children1 (by decide +kernel)
def state104 : Failed 12 :=
  finish 12 1 3330 2047 [(25, 0), (10, 1), (11, 1), (18, 0), (19, 0), (17, 0), (2, 1), (3, 1), (16, 0)] children1 (by decide +kernel)
def state108 : Failed 12 :=
  finish 12 1 1282 2047 [(25, 0), (10, 1), (11, 1), (18, 0), (19, 0), (2, 1), (3, 1), (17, 0), (16, 0), (35, 0)] children1 (by decide +kernel)
def state110 : Failed 12 :=
  finish 12 1 1187 2047 [(32, 0), (10, 1), (11, 1), (18, 0), (20, 0), (31, 0), (2, 1), (3, 1), (34, 0)] children1 (by decide +kernel)
def state114 : Failed 12 :=
  finish 12 1 3331 2047 [(17, 0), (10, 1), (11, 1), (20, 0), (18, 1), (25, 0), (2, 1), (3, 1), (16, 0), (40, 0)] children1 (by decide +kernel)
def state117 : Failed 12 :=
  finish 12 1 1283 2047 [(34, 0), (10, 1), (11, 1), (20, 0), (18, 1), (25, 0), (2, 1), (3, 1), (16, 0)] children1 (by decide +kernel)
def state118 : Failed 12 :=
  finish 12 1 3333 2047 [(34, 0), (10, 1), (11, 1), (18, 0), (9, 1), (30, 0), (2, 1), (3, 1), (16, 0)] children1 (by decide +kernel)
def state121 : Failed 12 :=
  finish 12 1 1285 2047 [(10, 1), (18, 0), (11, 1), (20, 1), (36, 0), (30, 0), (34, 0), (2, 1), (3, 1), (16, 0)] children1 (by decide +kernel)
def state127 : Failed 12 :=
  finish 12 1 1317 2047 [(45, 0), (11, 1), (10, 1), (20, 0), (15, 0), (2, 1), (3, 1), (31, 0), (4, 0), (39, 0)] children1 (by decide +kernel)
def state129 : Failed 12 :=
  finish 12 1 2344 2047 [(30, 0), (10, 1), (11, 1), (19, 0), (20, 0), (17, 0), (2, 1), (3, 1), (16, 0)] children1 (by decide +kernel)
def state132 : Failed 12 :=
  finish 12 1 1320 2047 [(30, 0), (10, 1), (11, 1), (20, 0), (19, 0), (2, 1), (3, 1), (17, 0), (16, 0)] children1 (by decide +kernel)
def children0 (code : Nat) : List (Failed 12) :=
  if code=7379674170187437914 then [state1] else
  if code=6728112036422385457 then [state4] else
  if code=6860519254252435898 then [state11] else
  if code=6964599123642778219 then [state15] else
  if code=7839575002399271006 then [state35] else
  if code=7023941119744754106 then [state41] else
  if code=7702784454772267638 then [state47] else
  if code=6843100614092228547 then [state57] else
  if code=7082542826041660022 then [state62] else
  if code=8508297520610671249 then [state67] else
  if code=6570182701657374572 then [state94] else
  if code=7611626469855022785 then [state98] else
  if code=8688284280119366371 then [state100] else
  if code=6735289159025993035 then [state104] else
  if code=7748575875108090000 then [state108] else
  if code=7737748559986452783 then [state110] else
  if code=8015332181855244568 then [state114] else
  if code=6704939703634369016 then [state117] else
  if code=8396680047570639000 then [state118] else
  if code=7966810421571600509 then [state121] else
  if code=8349924760787572152 then [state127] else
  if code=8225474380592839807 then [state129] else
  if code=8497975573819272830 then [state132] else
  []
def state0 : Failed 13 :=
  finish 13 0 0 1023 [(10, 0), (11, 0), (18, 0), (20, 0), (2, 0), (3, 0), (19, 0)] children0 (by decide +kernel)
theorem checkedRoot : state0 = raw := by decide +kernel
end PEqualNP.Outside.L_meta_9750.Gap4029
