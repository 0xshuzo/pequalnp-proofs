import PEqualNP.Outside.L_meta_2264
import PEqualNP.Outside.L_meta_5242

namespace FourShared2262
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.LowTop2264
open PEqualNP.Outside.L_meta_2264.Profile2264 (graph)

set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

def unpack (m : BitVec 16) : Finset EdgeRow :=
  Finset.univ.filter fun e => m.getLsbD e.val = true

def bits (m : ℕ) : Vertex → Bool := fun i => m.testBit i.val
def neg : Fin 5 → Fin 5 → Vertex → Bool := ![![bits 57,bits 389,bits 596,bits 1186,bits 1546],![bits 177,bits 325,bits 582,bits 1408,bits 1546],![bits 99,bits 325,bits 540,bits 1186,bits 1408],![bits 15,bits 85,bits 540,bits 582,bits 1186],![bits 57,bits 135,bits 269,bits 1186,bits 1546]]
def pr : Fin 10 → Fin 5 × Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def opts : Fin 5 → Fin 10 → BitVec 16 := ![![64111,63406,64889,62968,12030,64453,16212,34251,56731,46975],![60143,42986,63741,46456,32758,53213,24468,4055,57247,16247],![64487,63402,53245,52213,32446,52165,53213,46411,15455,64503],![65467,65530,65470,65357,65470,65530,52681,65467,46411,34767],![65387,64239,64889,62968,65399,65485,48988,64325,32724,46975]]

theorem allOff : ∀ g i, graphFun graph ∅ (neg g i)=false := by decide +kernel

theorem indexPair : ∀ i j : Fin 5, i<j → ∃ k, pr k=(i,j) := by decide +kernel

theorem optionsCorrect : ∀ g k r, (let x := (edgeRow r).1; let y := (edgeRow r).2;
  ¬ ((neg g (pr k).1 x = true ∨ neg g (pr k).2 x = true) ∧
      (neg g (pr k).1 y = true ∨ neg g (pr k).2 y = true))) → r ∈ unpack (opts g k) := by
  decide +kernel

theorem prune {X : Finset EdgeRow} {p q r : BitVec 16}
    (hp : X ⊆ unpack p) (hq : X ⊆ unpack q)
    (mask : (p &&& q) &&& r = (p &&& q)) : X ⊆ unpack r := by
  intro i hi
  have a := (Finset.mem_filter.mp (hp hi)).2
  have b := (Finset.mem_filter.mp (hq hi)).2
  have h := congrArg (fun m : BitVec 16 => m.getLsbD i.val) mask
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  simpa only [BitVec.getLsbD_and,a,b,Bool.true_and] using h
def env1 : Fin 10 → BitVec 16 := opts 0
def data2 : Array (BitVec 16) := #[60015,14199,56731,63597,63609,12022,38687,55182,30630,55823,31334,14951,45181,58030,60101,63685,10990,61688,16212,52569,34653,42858,32112,15729,46456,56197,42922,31684,52165,30192,3742,61612,3804,9962,10492,15173,50648,42472,34249,34250,32971,41920,1475]
def env2 (i : Fin 43) : BitVec 16 := data2[i.val]!
def idx2 : Array (Fin 43) := #[0,0,3,3,10,0,9,0,9,11,13,26,31,24,8,7,7,7,7,1,0,21,4,24,22,19,2,19,2,23,17,37,17,24,29,36,2,29,2,1,16,33,34,24,5,32,5,5,30,5,14,41,15,24,27,28,25,28,25,35,0,1,18,1,18,18,18,18,18,18,40,39,38,19,39,38,2,42,2,1,2,2,2,2,2,2,2,2,2,2,0,21,12,24,1,20,1,1,6,1]
def next2 (i : Fin 10) (k : Fin 10) : Fin 43 := idx2[i.val*10+k.val]!
theorem step2 : ∀ i k, (env1 i &&& opts 1 k) &&& env2 (next2 i k) = (env1 i &&& opts 1 k) := by decide +kernel
def data3 : Array (BitVec 16) := #[60007,13175,63589,63601,63685,55699,31334,14951,51821,60101,10998,56197,29606,31684,52165,52569,52633,30374,11958,34653,55178,30626,42922,45173,51321,61680,31088,14705,29168,55815,27182,58022,58026,25262,10926,37655,15173,15188,54150,13399,23706,50648,13878,22158,3742,3804,3828,1909,51084,30764,30776,14413,10319,14425,12381,32893,61604,61608,28844,28856,10428,49400,2300,45424,23054,49836,2796,41826,7195,5151,31792,15441,15444,11350,29872,38155,46376,13635,46408,42314,19824,3441,34168,34249,34280,17904,15892,5662,3924,34664,18340,6159,12348,45129,41035,10332,41440,41920,13368,13400,1768,32963,33218,451]
def env3 (i : Fin 104) : BitVec 16 := data3[i.val]!
def idx3 : Array (Fin 104) := #[0,32,8,0,30,0,8,94,52,0,1,21,47,1,42,1,19,77,39,1,5,20,16,5,40,5,16,75,68,5,2,57,8,0,49,0,8,93,51,2,2,57,24,3,50,0,15,93,53,3,10,17,46,10,18,9,45,39,73,10,35,20,19,19,87,11,19,75,69,35,38,20,48,11,43,11,48,20,43,38,12,21,90,12,17,11,48,21,17,12,29,20,8,0,64,0,8,75,91,29,6,6,0,0,6,0,0,1,6,6,7,1,0,0,6,0,0,1,7,7,2,57,55,23,92,0,19,93,54,23,31,32,65,31,33,9,48,22,30,31,9,9,9,9,9,9,9,0,0,9,4,4,4,4,4,4,4,2,2,4,10,22,66,10,34,9,45,52,52,10,25,57,61,25,59,4,41,78,53,25,13,21,88,37,86,13,88,77,72,37,14,15,15,15,15,14,15,15,15,15,14,19,19,19,19,14,19,15,19,19,67,22,89,67,22,14,19,79,79,67,26,21,80,26,70,13,15,77,71,26,27,21,81,27,70,14,15,77,71,27,63,76,82,63,98,14,15,78,99,63,11,11,11,11,11,11,11,5,2,11,22,22,22,22,22,11,20,22,22,22,13,12,13,13,13,13,13,1,2,13,14,11,14,14,9,14,14,14,0,14,28,21,85,28,74,13,41,77,39,28,10,20,44,10,44,9,44,20,44,10,56,57,65,31,58,4,48,57,49,56,9,20,45,10,44,9,45,15,45,10,10,22,100,10,22,9,45,79,79,10,10,22,62,10,60,4,45,51,95,10,36,1,14,14,6,14,14,1,2,36,14,16,41,41,16,14,41,15,15,41,96,22,84,84,22,14,41,78,78,96,14,16,83,14,16,14,83,15,15,14,102,20,41,14,20,14,41,79,79,102,101,20,83,4,20,4,83,94,52,101,97,22,14,14,9,14,14,63,0,97,103,20,83,14,17,14,83,77,39,103]
def next3 (i : Fin 43) (k : Fin 10) : Fin 104 := idx3[i.val*10+k.val]!
theorem step3 : ∀ i k, (env2 i &&& opts 2 k) &&& env3 (next3 i k) = (env2 i &&& opts 2 k) := by decide +kernel
def data4 : Array (BitVec 16) := #[55699,29606,52633,30374,11958,55178,30626,42922,63537,63557,63600,61680,31088,29168,59939,59942,31270,27182,59973,51789,60002,31330,58022,58026,25262,10926,10994,56069,13107,13110,31556,52037,15173,13170,56193,56196,54150,31620,31680,23706,52553,52568,50648,13878,22158,3742,34637,51084,63524,30764,51257,30776,14413,51320,63617,63620,61604,61608,28844,28856,10428,63680,49400,14641,45424,51649,55811,55814,23054,14883,51753,51756,51816,60033,60036,49836,60096,37651,15124,37654,15184,41826,52160,33733,7195,31792,29872,38155,46376,13635,46408,42314,19824,34168,34249,34280,17904,15892,5662,3800,3824,34585,34588,34648,34664,18340,14361,45108,12348,14424,2296,41440,33351,2792,33543,839,41920,15377,13331,13368,15425,13381,15428,15440,13394,11346,13400,3377,3660,41035,1740,1768,45129,3860,1841,1844,3908,3920,1904,10251,32828,10314,79,32963,33218,451,710,5133,1039,1095]
def env4 (i : Fin 150) : BitVec 16 := data4[i.val]!
def idx4 : Array (Fin 150) := #[14,20,15,18,15,20,9,14,129,112,28,33,29,32,29,33,31,28,89,115,8,10,48,9,48,10,9,8,9,9,8,10,8,9,8,10,9,8,9,9,54,61,55,9,55,61,65,54,9,83,0,0,0,0,0,0,0,0,0,0,16,21,16,30,16,21,9,16,21,112,69,21,16,32,16,21,9,69,89,112,70,72,71,19,71,72,19,70,19,19,73,76,74,18,74,76,65,73,9,83,4,26,4,18,4,26,26,4,20,146,34,34,35,27,35,34,0,34,0,83,1,1,1,1,1,1,0,1,1,1,37,38,37,30,37,38,38,37,12,83,34,82,35,31,35,82,65,34,31,83,2,41,2,40,2,41,40,2,40,40,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,2,3,3,3,4,4,4,4,4,4,2,4,3,3,101,103,102,46,102,103,40,101,40,46,5,5,5,5,5,5,2,5,5,5,6,6,6,6,6,6,2,6,6,5,7,7,7,7,7,7,2,7,7,5,8,10,107,9,107,10,9,8,9,9,50,53,50,19,50,53,19,50,19,19,11,11,11,9,11,11,11,11,9,11,12,12,12,12,12,12,12,12,12,12,63,12,12,32,12,12,31,63,32,31,13,13,13,12,13,13,13,13,12,13,66,66,67,27,67,66,0,66,0,112,17,17,17,17,17,17,2,17,7,17,22,22,22,15,22,22,0,22,7,22,23,23,23,23,23,23,2,23,7,5,23,23,24,17,24,23,2,23,7,24,25,25,25,17,25,25,2,25,7,24,77,77,79,27,79,77,0,77,0,114,32,30,30,32,30,30,31,32,32,31,78,80,78,30,78,80,12,78,12,30,5,5,36,27,36,5,0,5,0,36,118,124,43,121,43,124,40,118,89,149,39,39,39,39,39,39,2,39,5,5,2,42,2,40,2,42,42,2,40,42,43,43,43,3,43,43,2,43,3,3,5,5,44,44,44,5,2,5,5,44,45,45,45,45,45,45,2,45,5,44,45,99,45,128,45,99,99,45,40,130,4,100,4,128,4,100,99,4,40,130,134,138,135,46,135,138,40,134,40,46,5,5,47,47,47,5,2,5,2,47,49,49,49,49,49,49,2,49,49,17,51,51,51,49,51,51,2,51,49,2,52,52,49,52,49,52,19,52,52,19,139,141,17,52,17,141,19,139,129,142,106,109,51,52,51,109,19,106,52,19,106,109,108,52,108,109,19,106,52,19,50,53,140,19,140,53,19,50,19,19,11,11,56,9,56,11,0,11,8,22,57,57,57,57,57,57,2,57,57,2,57,57,58,49,58,57,2,57,49,24,59,59,59,49,59,59,2,59,49,2,60,60,60,17,60,60,2,60,7,24,62,62,62,19,62,62,42,62,19,42,60,110,60,19,60,110,99,60,19,130,64,64,64,64,64,64,31,64,64,31,68,68,68,68,68,68,2,68,5,17,23,23,75,19,75,23,2,23,2,47,25,113,25,19,25,113,99,25,19,130,7,81,7,81,7,81,31,7,81,81,84,39,39,84,39,39,2,84,84,84,84,39,98,147,98,39,2,84,84,148,85,85,85,85,85,85,2,85,3,2,117,123,85,120,85,123,40,117,89,40,85,123,97,122,97,123,40,85,89,46,4,125,4,122,4,125,40,4,89,149,86,86,86,3,86,86,2,86,3,2,87,5,5,87,5,5,2,87,87,87,88,88,88,88,88,88,2,88,88,2,89,89,6,89,6,89,40,89,89,89,88,90,88,90,88,90,40,88,90,40,7,91,7,90,7,91,40,7,91,91,92,92,92,40,92,92,40,92,40,40,127,92,92,40,92,92,40,127,40,40,93,93,93,40,93,93,40,93,40,40,2,42,2,40,2,42,94,2,40,94,7,95,7,40,7,95,42,7,40,42,96,96,96,40,96,96,42,96,40,42,97,97,97,97,97,97,2,97,3,3,98,98,98,44,98,98,2,98,5,44,133,137,133,136,133,137,40,133,40,46,7,104,7,46,7,104,40,7,40,46,6,6,105,47,105,6,2,6,2,47,84,39,68,52,68,39,2,84,84,142,51,51,108,49,108,51,2,51,49,17,132,90,57,132,57,90,19,132,132,19,129,91,7,129,7,91,19,129,129,129,51,109,60,52,60,109,19,51,52,19,7,111,7,64,7,111,42,7,64,42,7,116,7,81,7,116,42,7,64,82,119,119,119,88,119,119,2,119,88,2,119,126,119,90,119,126,40,119,90,40,7,131,7,46,7,131,42,7,40,99,0,143,0,9,0,143,65,0,112,143,0,144,0,31,0,144,42,0,81,144,0,144,0,31,0,144,65,0,89,145]
def next4 (i : Fin 104) (k : Fin 10) : Fin 150 := idx4[i.val*10+k.val]!
theorem step4 : ∀ i k, (env3 i &&& opts 3 k) &&& env4 (next4 i k) = (env3 i &&& opts 3 k) := by decide +kernel
def data5 : Array (BitVec 16) := #[63537,63557,63600,61680,55571,31088,29168,59939,59942,31270,27182,59973,51789,60002,31330,29350,58022,58026,25262,10926,29478,13107,13110,31556,52037,15173,13170,56193,31620,56196,31680,52505,52553,52568,52617,50648,56069,30246,11830,13878,55050,30498,42794,34637,55176,51084,63524,30764,51257,30776,14413,51320,63617,55427,63620,61604,61608,28844,28856,63680,55811,49400,51753,14641,45424,51649,55814,23054,51756,51816,10866,60033,53894,53898,21134,49836,60096,10978,54022,37651,15124,37654,15184,41826,52160,33733,60036,31792,14883,29872,38155,46376,13635,46408,42314,19824,34168,30112,42408,34249,34280,17904,15892,5662,30340,22156,11924,34585,34588,34648,34664,30592,42888,14361,14424,22666,53648,22928,41440,12348,10960,2792,33543,839,41920,23562,7179,23570,7187,15377,23576,7193,5147,13368,15425,13381,15428,15440,13394,11346,13400,23688,23696,21656,3377,19856,13331,3612,3660,3672,3696,41035,45108,3724,3784,1740,3792,45129,3860,18212,1841,1844,3908,3920,1904,33351,10268,32963,10251,79,10314,710,5133,1095,1039,32828,3594]
def env5 (i : Fin 177) : BitVec 16 := data5[i.val]!
def idx5 : Array (Fin 177) := #[4,53,4,116,4,27,4,4,117,4,20,15,5,6,20,28,20,20,28,20,31,34,31,35,31,34,31,4,145,31,37,15,37,89,37,104,37,9,104,37,38,19,38,89,38,106,38,8,106,38,40,73,40,44,40,44,40,27,44,40,41,15,41,97,41,111,41,20,111,41,42,17,42,98,42,112,42,42,111,42,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,1,2,1,2,2,2,3,2,3,2,3,2,1,3,2,5,2,5,5,5,5,5,5,5,5,5,3,5,6,5,6,5,5,6,5,7,7,0,0,7,7,7,7,7,7,7,8,0,0,8,8,8,8,8,8,9,9,0,0,9,9,9,9,9,9,10,10,10,10,8,10,10,8,8,10,11,11,1,1,11,11,11,11,11,11,12,12,12,12,11,12,12,11,11,12,13,13,2,2,13,11,11,11,11,13,14,14,2,2,14,14,14,14,14,14,7,16,0,3,8,16,8,8,15,8,17,17,17,17,7,17,17,7,15,17,10,18,10,17,8,18,10,8,15,10,10,19,10,17,8,19,10,8,19,10,13,77,2,3,70,30,70,11,120,26,27,36,4,4,36,36,29,36,23,36,21,21,21,5,21,21,21,21,21,21,20,9,5,5,22,20,22,20,22,22,23,23,5,5,23,23,23,23,23,23,24,11,24,24,24,24,24,24,23,24,25,25,25,5,25,25,23,25,23,25,26,14,5,5,26,23,26,23,26,26,27,27,4,27,27,27,27,27,27,27,27,29,4,27,29,29,29,29,28,29,40,72,4,27,78,29,29,29,28,78,23,28,5,6,23,28,23,23,28,20,23,30,5,6,23,30,23,23,30,23,125,115,130,143,127,141,130,0,142,103,32,12,32,32,32,32,32,24,32,32,32,12,33,33,33,32,33,24,33,33,32,35,33,35,33,35,33,24,35,33,37,9,39,39,39,37,39,9,39,39,40,74,40,44,37,105,103,9,104,103,176,19,31,35,38,153,147,8,106,103,43,12,32,32,43,43,43,24,43,43,40,45,31,34,45,45,43,24,45,43,0,46,0,0,46,1,1,1,1,46,47,47,47,47,9,47,47,1,1,47,48,48,48,48,0,12,31,0,0,48,47,47,49,49,0,47,49,0,0,49,50,50,50,50,1,50,50,1,1,50,51,51,51,51,2,12,33,1,2,51,0,52,0,3,0,52,0,0,28,0,0,54,0,3,1,54,1,1,28,1,0,55,0,3,46,54,1,1,15,46,56,56,56,56,0,56,56,0,3,56,47,57,47,56,9,57,47,1,15,47,47,56,49,58,0,56,49,0,3,49,10,19,49,58,38,19,166,1,106,119,1,59,1,3,1,59,1,1,30,1,51,61,51,61,2,35,33,1,3,51,63,0,63,5,63,25,5,25,5,21,64,2,64,64,64,64,64,64,5,64,24,65,24,35,24,65,24,24,30,24,60,60,0,0,60,27,27,27,9,60,60,66,0,0,66,29,29,29,9,66,67,67,47,40,9,67,67,9,9,67,88,88,0,0,88,25,9,25,9,21,62,62,48,17,7,12,12,7,7,62,62,68,48,17,8,12,12,8,8,68,69,69,51,51,13,12,12,11,11,69,7,71,0,3,7,71,7,7,28,7,7,86,0,3,8,86,8,8,28,8,17,75,17,17,8,45,12,8,15,68,11,76,1,3,11,76,11,11,30,11,79,60,4,4,79,27,79,27,21,79,23,9,5,5,80,23,80,23,80,22,40,66,4,4,81,29,81,29,22,81,23,14,5,5,82,23,82,23,82,26,83,13,64,64,83,83,83,83,23,83,24,76,24,35,24,84,24,24,30,24,24,85,24,35,24,85,24,24,85,24,126,126,131,103,128,126,130,0,87,132,87,0,87,87,87,87,87,0,87,39,37,3,87,89,87,89,39,0,89,39,90,90,90,40,90,90,40,4,40,90,91,56,91,91,91,91,91,64,41,91,92,92,92,92,92,92,92,25,92,92,93,93,93,93,93,93,93,64,92,93,94,94,93,93,94,93,93,64,92,94,95,2,95,95,95,32,33,5,33,95,96,51,96,96,96,32,33,24,33,96,32,99,32,35,32,99,32,24,35,32,96,61,96,100,96,35,32,24,35,96,95,3,95,101,95,35,33,5,35,95,102,9,87,39,102,102,102,9,102,39,40,67,103,103,39,103,103,9,39,103,148,121,33,35,149,154,149,11,156,109,150,77,95,101,150,154,149,11,156,150,43,12,31,31,107,43,107,24,107,107,40,12,31,31,108,43,108,24,108,108,43,12,33,33,109,43,109,24,109,109,110,69,96,96,110,43,43,24,43,110,41,15,41,97,159,45,43,20,45,159,50,50,113,49,0,50,49,0,0,113,0,46,0,0,152,1,152,1,22,152,47,47,49,49,22,47,119,1,22,119,50,50,114,114,2,50,114,1,2,114,51,121,51,61,2,121,33,1,120,51,64,3,64,118,64,118,64,64,6,64,165,165,1,1,165,11,11,11,11,165,69,121,51,61,13,121,12,11,30,69,79,122,4,4,122,24,24,24,20,122,123,123,24,5,123,24,23,24,23,123,83,76,64,118,83,124,83,83,30,83,129,0,129,39,129,129,87,0,87,129,92,21,129,39,146,92,39,0,39,146,91,47,133,133,39,91,133,0,39,133,134,1,134,92,134,134,134,1,134,92,92,1,92,92,135,135,135,1,135,135,134,1,134,92,136,136,136,1,136,135,134,1,137,137,137,134,137,1,137,137,92,14,137,137,138,92,137,1,137,138,139,13,137,137,139,134,137,1,137,138,93,50,140,140,137,93,140,1,137,140,144,0,144,95,144,31,31,4,31,144,148,12,32,32,148,148,148,11,148,43,151,151,151,93,151,151,93,1,1,151,43,155,32,35,43,155,43,11,155,43,110,121,96,100,110,154,43,11,154,110,157,157,157,93,1,157,93,1,1,157,158,8,31,31,158,158,158,23,158,108,160,7,144,95,160,43,107,21,107,160,41,8,95,95,161,43,108,20,108,161,162,11,32,32,162,162,162,23,162,43,162,11,33,33,163,162,163,23,163,109,110,13,95,95,164,43,109,23,109,164,168,168,50,10,7,50,10,0,0,151,17,68,48,48,152,12,108,1,22,175,170,170,50,50,13,50,50,1,1,94,151,169,12,12,123,12,12,1,1,169,151,167,1,3,151,65,1,1,3,151,83,167,24,35,83,35,24,24,6,83,92,167,24,6,92,65,5,24,6,92,13,171,1,3,123,85,11,11,85,123,90,50,90,40,135,172,103,1,37,172,90,169,31,31,173,43,43,1,37,174,92,123,32,32,173,43,43,1,43,173]
def next5 (i : Fin 150) (k : Fin 10) : Fin 177 := idx5[i.val*10+k.val]!
theorem step5 : ∀ i k, (env4 i &&& opts 4 k) &&& env5 (next5 i k) = (env4 i &&& opts 4 k) := by decide +kernel
theorem small : ∀ i : Fin 177, (unpack (env5 i)).card ≤ 8 := by decide +kernel

theorem chart_bound (X : Finset EdgeRow) (adm : ∀ g, ∃ k, X ⊆ unpack (opts g k)) : X.card ≤ 8 := by
  obtain ⟨a,ha⟩ := adm 0
  obtain ⟨b,hb⟩ := adm 1
  obtain ⟨c,hc⟩ := adm 2
  obtain ⟨d,hd⟩ := adm 3
  obtain ⟨f,hf⟩ := adm 4
  have h1 : X ⊆ unpack (env1 a) := ha
  have h2 := prune h1 hb (step2 a b)
  have h3 := prune h2 hc (step3 _ c)
  have h4 := prune h3 hd (step4 _ d)
  have h5 := prune h4 hf (step5 _ f)
  exact (Finset.card_le_card h5).trans (small _)

theorem four_clause_bound (A : Fin 4 → Finset Vertex) (X : Finset EdgeRow)
    (edges : ∀ e∈X, ∀ k, ∃ v∈A k, v=(edgeRow e).1 ∨ v=(edgeRow e).2)
    (clean : ∀ x : Vertex → Bool, (∀ k, ∃ v∈A k, x v=true) → graphFun graph ∅ x=true) :
    X.card≤8 := by
  classical
  apply chart_bound
  intro g
  have misses (i : Fin 5) : ∃ k, ∀ v∈A k, neg g i v ≠ true := by
    by_contra! h
    have h1 := clean (neg g i) h
    rw [allOff] at h1
    contradiction
  choose color off using misses
  have bad : ¬Function.Injective color := by
    intro hinj
    have h := Fintype.card_le_of_injective color hinj
    simp at h
  unfold Function.Injective at bad
  push_neg at bad
  obtain ⟨i,j,same,neq⟩ := bad
  have solve (i j : Fin 5) (ord : i<j) (same : color i=color j) :
      ∃ k, X ⊆ unpack (opts g k) := by
    obtain ⟨k,hk⟩ := indexPair i j ord
    refine ⟨k,fun r hr => optionsCorrect g k r ?_⟩
    dsimp only
    rw [hk]
    intro blocked
    obtain ⟨v,hv,hv'⟩ := edges r hr (color i)
    have hvi := off i v hv
    have hvj := off j v (same ▸ hv)
    rcases hv' with rfl | rfl
    · exact blocked.1.elim hvi hvj
    · exact blocked.2.elim hvi hvj
  rcases lt_or_gt_of_ne neq with h | h
  · exact solve i j h same
  · exact solve j i h same.symm

end FourShared2262
namespace FourShared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.LowTop2264
open PEqualNP.Outside.L_meta_2264.Profile2264 (graph)

def key (r : EdgeRow) : Sym2 Vertex := s((edgeRow r).1,(edgeRow r).2)
def rows (X : Finset (Sym2 Vertex)) : Finset EdgeRow := Finset.univ.filter (fun r => key r∈X)

theorem cardRows (X : Finset (Sym2 Vertex)) (sub : X⊆graph.edgeFinset) : X.card≤(rows X).card := by
  have chart : ∀ u v : Vertex, graph.Adj u v → ∃ r : EdgeRow, key r=s(u,v) := by decide +kernel
  have inc : X⊆(rows X).image key := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have adj : graph.Adj u v := SimpleGraph.mem_edgeFinset.mp (sub he)
      obtain ⟨r,hr⟩ := chart u v adj
      exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr.symm ▸ he⟩,hr⟩
  exact (Finset.card_le_card inc).trans Finset.card_image_le

theorem rowOn {C : Circuit} {j : ℕ} {r : EdgeRow}
    (h : key r∈gammaE graph C j) :
    gateVal 11 C j (pairInput (edgeRow r).1 (edgeRow r).2)=true := by
  obtain ⟨_,u,v,eq,on⟩ := Finset.mem_filter.mp h
  change s((edgeRow r).1,(edgeRow r).2)=s(u,v) at eq
  rcases Sym2.eq_iff.mp eq with same | flip
  · simpa only [same.1,same.2] using on
  · have swap : pairInput u v=pairInput v u := by funext w; simp [pairInput,or_comm]
    rw [swap] at on
    simpa only [flip.1,flip.2] using on

theorem double_bound (C : Circuit) (d e : ℕ) (ao : IsAO2 11 C)
    (form : TopForm graph C) (hs : junk graph C={d,e})
    (de : ¬InCone 11 C d e) (ed : ¬InCone 11 C e d)
    (safe : ∀ x, gateVal 11 C d x=true → gateVal 11 C e x=true → graphFun graph ∅ x=true) :
    (gammaE graph C d ∩ gammaE graph C e).card≤8 := by
  classical
  let D := gammaE graph C d ∩ gammaE graph C e
  have dj : d∈junk graph C := by rw [hs]; simp
  have ej : e∈junk graph C := by rw [hs]; simp
  let A : Fin 4 → Finset Vertex := ![side C d 0,side C d 1,side C e 0,side C e 1]
  have clauses (x : Vertex → Bool) : (∀ k, ∃ v∈A k, x v=true) ↔
      gateVal 11 C d x=true ∧ gateVal 11 C e x=true := by
    rw [junkVal ao form hs de ed dj x,junkVal ao form hs de ed ej x]
    constructor
    · intro h
      exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩
    · rintro ⟨⟨a,b⟩,c,f⟩ k
      fin_cases k
      · exact a
      · exact b
      · exact c
      · exact f
  apply (cardRows D (fun r hr => (Finset.mem_filter.mp (Finset.mem_inter.mp hr).1).1)).trans
  apply four_clause_bound A
  · intro r hr k
    have mem := Finset.mem_inter.mp (Finset.mem_filter.mp hr).2
    obtain ⟨w,hw,on⟩ := (clauses _).mpr ⟨rowOn mem.1,rowOn mem.2⟩ k
    exact ⟨w,hw,(Local1490.pairInput_true _ _ _).mp on⟩
  · intro x h
    have pair := (clauses x).mp h
    exact safe x pair.1 pair.2

end FourShared2262
namespace FourShared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.LowTop2264
open PEqualNP.Outside.L_meta_2264.Profile2264 (graph)

theorem atlas_sizes : signatures.all (fun s => decide ((unpack s.2).card≤7)) = true := by
  decide +kernel

theorem star_sizes : ∀ v : Vertex, ((Finset.univ : Finset EdgeRow).filter
    (fun r => v=(edgeRow r).1 ∨ v=(edgeRow r).2)).card≤4 := by decide +kernel

theorem guarded_bound (C : Circuit) (d e j : ℕ) (ao : IsAO2 11 C)
    (form : TopForm graph C) (hs : junk graph C={d,e})
    (de : ¬InCone 11 C d e) (ed : ¬InCone 11 C e d) (jm : j∈junk graph C) :
    ((gammaE graph C j).filter fun h => ∃ z∈wmax graph C j, z∈h).card≤7 := by
  classical
  let D := (gammaE graph C j).filter fun h => ∃ z∈wmax graph C j, z∈h
  apply (cardRows D (fun z hz => (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1)).trans
  let A := side (n := 11) C j 0
  let B := side (n := 11) C j 1
  have raw (x : Vertex → Bool) : gateVal 11 C j x = true ↔ UsefulJunk2264.hits A x ∧ UsefulJunk2264.hits B x :=
    junkVal ao form hs de ed jm x
  have guard (w : Vertex) (hm : w ∈ wmax graph C j) : UsefulJunk2264.safe graph A B w :=
    fun x aa bb hx => (Finset.mem_filter.mp hm).2 x ((raw _).mpr ⟨aa,bb⟩) hx
  have productive (r) (hr : r∈rows D) : UsefulJunk2264.prod graph A B (edgeRow r).1 (edgeRow r).2 := by
    have mem := Finset.mem_filter.mp (Finset.mem_filter.mp hr).2
    obtain ⟨z,zw,zr⟩ := mem.2
    have hraw := (raw _).mp (rowOn mem.1)
    change z∈s((edgeRow r).1,(edgeRow r).2) at zr
    rcases Sym2.mem_iff.mp zr with rfl | rfl
    · exact ⟨hraw.1,hraw.2,Or.inl (guard _ zw)⟩
    · exact ⟨hraw.1,hraw.2,Or.inr (guard _ zw)⟩
  by_cases wide : ∀ c : Vertex, ∃ r∈rows D, (edgeRow r).1≠c ∧ (edgeRow r).2≠c
  · obtain ⟨s,smem,_,cover⟩ := masksForProduct A B (by decide +kernel) (fun c => by
      obtain ⟨r,hr,h1,h2⟩ := wide c
      exact ⟨_,_,productive r hr,h1,h2⟩)
    have inc : rows D ⊆ unpack s.2 := fun r hr =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,cover r (productive r hr)⟩
    exact (Finset.card_le_card inc).trans (of_decide_eq_true (List.all_eq_true.mp atlas_sizes s smem))
  · obtain ⟨c,only⟩ := not_forall.mp wide
    have inc : rows D ⊆ (Finset.univ : Finset EdgeRow).filter (fun r => c=(edgeRow r).1 ∨ c=(edgeRow r).2) := by
      intro r hr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      by_contra! h
      exact only ⟨r,hr,Ne.symm h.1,Ne.symm h.2⟩
    have h := (Finset.card_le_card inc).trans (star_sizes c)
    omega

end FourShared2262

namespace Shared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.Local1490
open PEqualNP.Outside.L_meta_5242.Structural (inCone_trans inCone_lt and_ancestor_junk)

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

-- The backwards induction follows the cone recursion from L_meta_5242.Structural.upper_reaches.
theorem access (ao : IsAO2 n C) (form : TopForm G C) {d e a : ℕ}
    (junkEq : junk G C={d,e}) (inc : ¬InCone n C d e) (ha : a∈tops G C)
    (da : InCone n C d a) : ∃ b : Fin 2, OrReaches n C (opnd C a b) d := by
  have dj : d∈junk G C := by rw [junkEq]; simp
  have dlen := (junkData dj).1
  obtain ⟨alen,aop,_⟩ := topData ha
  have go : ∀ k, InCone n C k a → (d=k ∨ InCone n C d k) → OrReaches n C (n+k) d := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro ka rel
      rcases rel with rfl | dk
      · exact (orReaches_iff n C d d).mpr ⟨dlen,Or.inl rfl⟩
      · obtain ⟨klen,t,tk,mem,dt⟩ := (inCone_iff n C d k).mp dk
        have kop : (gateAt C k).op=GateOp.or := by
          rcases ao.1 _ (gateAt_mem klen) with kand | kor
          · have kj := and_ancestor_junk form alen aop klen kand ka
            have kn : k=d ∨ k=e := by simpa only [junkEq,Finset.mem_insert,Finset.mem_singleton] using kj
            rcases kn with rfl | rfl
            · exact (Nat.lt_irrefl _ (inCone_lt dk)).elim
            · exact (inc dk).elim
          · exact kor
        have tc : InCone n C t k := (inCone_iff n C t k).mpr ⟨klen,t,tk,mem,Or.inl rfl⟩
        exact (orReaches_iff n C k d).mpr ⟨klen,Or.inr ⟨kop,n+t,mem,by omega,ih t tk (inCone_trans tc ka) dt⟩⟩
  obtain ⟨_,k,ka,mem,dk⟩ := (inCone_iff n C d a).mp da
  have ka' : InCone n C k a := (inCone_iff n C k a).mpr ⟨alen,k,ka,mem,Or.inl rfl⟩
  obtain ⟨b,hb⟩ := inputsAsOpnd ao alen mem
  exact ⟨b,hb ▸ go k ka' dk⟩

theorem no_both (ao : IsAO2 n C) {a d : ℕ} (ha : a∈tops G C) (dj : d∈junk G C)
    {b : Fin 2} (r : OrReaches n C (opnd C a b) d) :
    ¬ OrReaches n C (opnd C a (1-b)) d := by
  intro r'
  obtain ⟨al,op,clean⟩ := topData ha
  obtain ⟨_,_,x,hx,off⟩ := junkData dj
  have on : gateVal n C a x=true := (andValOperands ao al op x).mpr (fun c => by
    rcases eitherOperand b c with rfl | rfl
    · exact reachVal r hx
    · exact reachVal r' hx)
  rw [clean x on] at off
  contradiction

theorem shared_cases (ao : IsAO2 n C) (form : TopForm G C) {d e a : ℕ}
    (junkEq : junk G C={d,e}) (de : ¬InCone n C d e) (ed : ¬InCone n C e d)
    (ha : a∈tops G C) (da : InCone n C d a) (ea : InCone n C e a) :
    (∀ x, gateVal n C d x=true → gateVal n C e x=true → graphFun G ∅ x=true) ∨
      (wmax G C d ∩ wmax G C e).Nonempty := by
  classical
  obtain ⟨i,ri⟩ := access ao form junkEq de ha da
  have hswap : junk G C={e,d} := junkEq.trans (Finset.pair_comm _ _)
  obtain ⟨j,rj⟩ := access ao form hswap ed ha ea
  obtain ⟨al,op,clean⟩ := topData ha
  rcases eitherOperand i j with ij | ij
  · rw [ij] at rj
    right
    have pure (k) (rk : OrReaches n C (opnd C a (1-i)) k) (opk : (gateAt C k).op=GateOp.and) : False := by
      have dirty := operandOrAndJunk ao form al op rk opk
      have num : k=d ∨ k=e := by simpa only [junkEq,Finset.mem_insert,Finset.mem_singleton] using dirty
      rcases num with rfl | rfl
      · exact no_both ao ha dirty ri rk
      · exact no_both ao ha dirty rj rk
    have bound := opndBound ao al (1-i)
    obtain ⟨v,hv⟩ := pureOrNonempty ao (by omega : opnd C a (1-i)<n+C.gates.length) pure
    exact ⟨v,Finset.mem_inter.mpr ⟨oppositeSideWmax ao ha ri hv,oppositeSideWmax ao ha rj hv⟩⟩
  · rw [ij] at rj
    left
    intro x xd xe
    apply clean x
    apply (andValOperands ao al op x).mpr
    intro b
    rcases eitherOperand i b with rfl | rfl
    · exact reachVal ri xd
    · exact reachVal rj xe

end Shared2262

namespace FourShared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264.Profile2264 (graph)

theorem profiles (G : SimpleGraph (Fin 11)) [ds : DecidableRel G.Adj] (C : Circuit) (d e : ℕ)
    (hg : G=graph) (ao : IsAO2 11 C) (form : TopForm G C) (hs : junk G C={d,e})
    (de : ¬InCone 11 C d e) (ed : ¬InCone 11 C e d)
    (common : ∃ a∈tops G C, InCone 11 C d a ∧ InCone 11 C e a) :
    let A := fun k => (gammaE G C k).filter (fun h => ∃ z∈wmax G C k, z∈h)
    let both := gammaE G C d ∩ gammaE G C e
    let safe := ∀ x, gateVal 11 C d x=true → gateVal 11 C e x=true → graphFun G ∅ x=true
    (A d).card≤7 ∧ (A e).card≤7 ∧ (safe → both.card≤8) ∧
      (safe ∨ (wmax G C d ∩ wmax G C e).Nonempty) := by
  subst G
  have same : ds = PEqualNP.Outside.L_meta_2264.compactDecidable := Subsingleton.elim _ _
  subst ds
  obtain ⟨a,ha,da,ea⟩ := common
  exact ⟨guarded_bound C d e d ao form hs de ed (by rw [hs]; simp),
    guarded_bound C d e e ao form hs de ed (by rw [hs]; simp),
    double_bound C d e ao form hs de ed,Shared2262.shared_cases ao form hs de ed ha da ea⟩

end FourShared2262
namespace Shared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.Local1490

local instance : DecidableEq GateOp := gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

-- A direct reader of an empty, dirty wire cannot belong to lambda.
theorem first_charge (ao : IsAO2 n C) {w h : ℕ} (hn : (orIn n C w).Nonempty)
    (empty : orIn n C (n+h)=∅) (dirty : ∃ x, gateVal n C h x=true ∧ graphFun G ∅ x=false)
    (route : OrReaches n C w h) : ∃ m∈orN G C \ lam G C,
      OrReaches n C w m ∧ n+h∈(gateAt C m).inputs ∧ h<m := by
  rcases Relation.ReflTransGen.cases_tail (orReaches_reach h w route).1 with he | ⟨r,path,step⟩
  · rw [← he,empty] at hn
    exact (Finset.not_nonempty_empty hn).elim
  · obtain ⟨m,ml,rfl,op,read,lt⟩ := step
    obtain ⟨x,hx,off⟩ := dirty
    have mon : gateVal n C m x=true := (val_or (n := n) (by simp) ml op).mpr ⟨n+h,read,lt,hx⟩
    have pay : m∈orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ml,op,fun clean =>
      Bool.false_ne_true (off ▸ clean x mon)⟩
    refine ⟨m,Finset.mem_sdiff.mpr ⟨pay,?_⟩,reach_orReaches path m rfl ml,read,by omega⟩
    intro hlam
    obtain ⟨_,h0,h1,_⟩ := Finset.mem_filter.mp hlam
    obtain ⟨b,hb⟩ := inputsAsOpnd ao ml read
    rw [hb] at empty
    fin_cases b
    · exact Finset.not_nonempty_iff_eq_empty.mpr empty h0
    · exact Finset.not_nonempty_iff_eq_empty.mpr empty h1

theorem shared_price (ao : IsAO2 n C) (form : TopForm G C) {d e a : ℕ}
    (ne : d ≠ e) (junkEq : junk G C={d,e}) (de : ¬InCone n C d e) (ed : ¬InCone n C e d)
    (ha : a∈tops G C) (da : InCone n C d a) (ea : InCone n C e a) :
    2≤2*(centreless G C).card+(orN G C \ lam G C).card := by
  classical
  by_cases ac : a∈centreless G C
  · have h := Finset.card_pos.mpr ⟨a,ac⟩
    omega
  have raw (i : Fin 2) : (orIn n C (opnd C a i)).Nonempty := by
    by_contra h
    have empty := Finset.not_nonempty_iff_eq_empty.mp h
    apply ac
    apply Finset.mem_filter.mpr
    refine ⟨ha,?_⟩
    fin_cases i
    · exact Or.inl empty
    · exact Or.inr empty
  obtain ⟨i,ri⟩ := access ao form junkEq de ha da
  obtain ⟨j,rj⟩ := access ao form (junkEq.trans (Finset.pair_comm _ _)) ed ha ea
  have dj : d∈junk G C := by rw [junkEq]; simp
  have ej : e∈junk G C := by rw [junkEq]; simp
  obtain ⟨_,dop,dd⟩ := junkData dj
  obtain ⟨_,eop,ee⟩ := junkData ej
  obtain ⟨m,mp,rm,dm,_⟩ := first_charge ao (raw i) (orInAnd dop) dd ri
  obtain ⟨z,zp,_,ez,_⟩ := first_charge ao (raw j) (orInAnd eop) ee rj
  by_cases mz : m=z
  · subst z
    obtain ⟨hm,om,dirtym⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp mp).1
    have ml := Finset.mem_range.mp hm
    obtain ⟨l,r,lr⟩ := binaryInputs ao ml
    have sides (b : Fin 2) : opnd C m b=n+d ∨ opnd C m b=n+e := by
      have dd := dm
      have ee := ez
      rw [lr] at dd ee
      simp only [List.mem_cons,List.not_mem_nil,or_false] at dd ee
      have ls : opnd C m 0=l := by simp [opnd,lr]
      have rs : opnd C m 1=r := by simp [opnd,lr]
      fin_cases b
      · change opnd C m 0=n+d ∨ opnd C m 0=n+e
        rw [ls]
        rcases dd with dd|dd <;> rcases ee with ee|ee <;> omega
      · change opnd C m 1=n+d ∨ opnd C m 1=n+e
        rw [rs]
        rcases dd with dd|dd <;> rcases ee with ee|ee <;> omega
    have sempty (b : Fin 2) : side (n := n) C m b=∅ := by
      unfold side
      rcases sides b with h|h
      · rw [h,orInAnd dop]
      · rw [h,orInAnd eop]
    have em : orIn n C (n+m) = ∅ := by rw [orInOr ao ml om,sempty 0,sempty 1,Finset.empty_union]
    have dirty : ∃ x, gateVal n C m x=true ∧ graphFun G ∅ x=false := by
      by_contra h
      apply dirtym
      intro x hx
      by_contra off
      exact h ⟨x,hx,Bool.eq_false_iff.mpr off⟩
    obtain ⟨k,kp,_,_,mk⟩ := first_charge ao (raw i) em dirty rm
    have two := Finset.one_lt_card_iff.mpr ⟨m,k,mp,kp,mk.ne⟩
    omega
  · have two := Finset.one_lt_card_iff.mpr ⟨m,z,mp,zp,mz⟩
    omega

end Shared2262

namespace Shared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.Local1490

theorem localization (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (d e : ℕ)
    (ao : IsAO2 n C) (form : TopForm G C) (junkEq : junk G C={d,e})
    (u v : Fin n) (edge : s(u,v)∈G.edgeFinset) (a : ℕ) (ha : a∈tops G C)
    (i : Fin 2) (j : ℕ) (member : j=d ∨ j=e)
    (topOn : gateVal n C a (pairInput u v)=true) (route : OrReaches n C (opnd C a i) j)
    (on : gateVal n C j (pairInput u v)=true) :
    let A := fun k => (gammaE G C k).filter (fun h => ∃ z∈wmax G C k, z∈h)
    s(u,v)∈A d ∨ s(u,v)∈A e ∨
      ((∀ x, gateVal n C d x=true → gateVal n C e x=true → graphFun G ∅ x=true) ∧
       s(u,v)∈gammaE G C d ∩ gammaE G C e) := by
  classical
  dsimp only
  have gamma (k) (h : gateVal n C k (pairInput u v)=true) : s(u,v)∈gammaE G C k :=
    Finset.mem_filter.mpr ⟨edge,u,v,rfl,h⟩
  obtain ⟨haLen,haOp,haClean⟩ := topData ha
  have other := (andValOperands ao haLen haOp _).mp topOn (1-i)
  rcases operand_trace u v (opnd C a (1-i)) other with ⟨z,hz,path⟩ | ⟨k,hk,notOr,path,onK⟩
  · have hzW := oppositeSideWmax ao ha route (reach_mem_orIn z path)
    have attached : ∃ w∈wmax G C j, w∈s(u,v) := by
      refine ⟨z,hzW,?_⟩
      rcases hz with rfl | rfl <;> simp
    have atj : s(u,v) ∈ (gammaE G C j).filter (fun h => ∃ z∈wmax G C j, z∈h) :=
      Finset.mem_filter.mpr ⟨gamma j on,attached⟩
    rcases member with rfl | rfl
    · exact Or.inl atj
    · exact Or.inr (Or.inl atj)
  · have kr := reach_orReaches path k rfl hk
    have op := (ao.1 _ (gateAt_mem hk)).resolve_right notOr
    have kj := operandOrAndJunk ao form haLen haOp kr op
    have num : k=d ∨ k=e := by simpa only [junkEq,Finset.mem_insert,Finset.mem_singleton] using kj
    have safe (x) (hj : gateVal n C j x=true) (hkx : gateVal n C k x=true) : graphFun G ∅ x=true := by
      apply haClean x
      apply (andValOperands ao haLen haOp x).mpr
      intro b
      rcases eitherOperand i b with rfl | rfl
      · exact reachVal route hj
      · exact reachVal kr hkx
    have ne : j ≠ k := by
      rintro rfl
      obtain ⟨_,_,x,hx,off⟩ := junkData kj
      rw [safe x hx hx] at off
      contradiction
    have gj := gamma j on
    have gk := gamma k onK
    right
    right
    rcases member with rfl | rfl <;> rcases num with rfl | rfl
    · exact (ne rfl).elim
    · exact ⟨safe,Finset.mem_inter.mpr ⟨gj,gk⟩⟩
    · exact ⟨fun x hd he => safe x he hd,Finset.mem_inter.mpr ⟨gk,gj⟩⟩
    · exact (ne rfl).elim

end Shared2262
