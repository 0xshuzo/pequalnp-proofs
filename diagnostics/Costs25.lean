import Mathlib

namespace PricesOfThirteen2262

def bitCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, m => m%2 + bitCount n (m/2)

def pieces : List ℕ → ℕ → ℕ
  | [], m => bitCount 13 m
  | a :: as, m => min (pieces as m) (1 + pieces as (m ^^^ (m &&& a)))

def extra (old : List ℕ) : List ℕ → ℕ
  | [] => 0
  | s :: rest => (pieces old s - 1) + extra (s::old) rest

theorem bank_0_0 : 6 ≤ extra [768, 562, 1160, 1088] [69, 417, 4098] := by decide +kernel
theorem bank_0_1 : 6 ≤ extra [768, 562, 1160, 1088] [81, 417, 4128] := by decide +kernel
theorem bank_0_2 : 6 ≤ extra [768, 562, 1160, 1088] [85, 289, 2056] := by decide +kernel
theorem bank_0_3 : 6 ≤ extra [768, 562, 1160, 1088] [85, 385, 2052] := by decide +kernel
theorem bank_0_4 : 6 ≤ extra [768, 562, 1160, 1088] [85, 417] := by decide +kernel
theorem bank_0_5 : 7 ≤ extra [768, 562, 1160, 1088] [85, 417, 2052] := by decide +kernel
theorem bank_0_6 : 7 ≤ extra [768, 562, 1160, 1088] [85, 417, 2056] := by decide +kernel
theorem bank_0_7 : 7 ≤ extra [768, 562, 1160, 1088] [85, 417, 4098] := by decide +kernel
theorem bank_0_8 : 7 ≤ extra [768, 562, 1160, 1088] [85, 417, 4128] := by decide +kernel
theorem core_0 : 7 ≤ extra [] [768, 562, 1160, 1088] := by decide +kernel

theorem bank_1_0 : 6 ≤ extra [768, 417, 1160, 1088] [69, 546, 6146] := by decide +kernel
theorem bank_1_1 : 6 ≤ extra [768, 417, 1160, 1088] [69, 562, 4098] := by decide +kernel
theorem bank_1_2 : 7 ≤ extra [768, 417, 1160, 1088] [69, 562, 6146] := by decide +kernel
theorem bank_1_3 : 6 ≤ extra [768, 417, 1160, 1088] [81, 562, 4128] := by decide +kernel
theorem bank_1_4 : 6 ≤ extra [768, 417, 1160, 1088] [85, 530, 2052] := by decide +kernel
theorem bank_1_5 : 6 ≤ extra [768, 417, 1160, 1088] [85, 546, 2050] := by decide +kernel
theorem bank_1_6 : 7 ≤ extra [768, 417, 1160, 1088] [85, 546, 6146] := by decide +kernel
theorem bank_1_7 : 6 ≤ extra [768, 417, 1160, 1088] [85, 560, 2064] := by decide +kernel
theorem bank_1_8 : 6 ≤ extra [768, 417, 1160, 1088] [85, 562] := by decide +kernel
theorem bank_1_9 : 7 ≤ extra [768, 417, 1160, 1088] [85, 562, 2050] := by decide +kernel
theorem bank_1_10 : 7 ≤ extra [768, 417, 1160, 1088] [85, 562, 2052] := by decide +kernel
theorem bank_1_11 : 7 ≤ extra [768, 417, 1160, 1088] [85, 562, 2064] := by decide +kernel
theorem bank_1_12 : 7 ≤ extra [768, 417, 1160, 1088] [85, 562, 4098] := by decide +kernel
theorem bank_1_13 : 7 ≤ extra [768, 417, 1160, 1088] [85, 562, 4128] := by decide +kernel
theorem bank_1_14 : 8 ≤ extra [768, 417, 1160, 1088] [85, 562, 6146] := by decide +kernel
theorem core_1 : 7 ≤ extra [] [768, 417, 1160, 1088] := by decide +kernel

theorem bank_2_0 : 5 ≤ extra [1088, 85, 768, 562] [417, 1160] := by decide +kernel
theorem core_2 : 8 ≤ extra [] [1088, 85, 768, 562] := by decide +kernel


end PricesOfThirteen2262
