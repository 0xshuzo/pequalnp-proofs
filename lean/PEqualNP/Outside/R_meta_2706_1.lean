import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2706_1
    (hNormalize : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
      let val := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (x : Fin 14 → Bool) =>
        (D.wires (List.ofFn x)).getD k false
      let valid := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ) =>
        PEqualNP.MetaComplexity.Monotone2 D ∧ u < 14 + D.size ∧ v < 14 + D.size
      let accepts := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ) =>
        ∀ x : Fin 14 → Bool,
          (∃ s t : Fin 14, (54476011632248939714359330176 : ℕ).testBit (14 * s.val + t.val) = true ∧
             x s = true ∧ x t = true) ↔ val D u x = true ∨ val D v x = true
      let excl := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ) (x : Fin 14 → Bool) =>
        val D u x = true ∧ val D v x = false
      let row := fun (m : ℕ) (z : Fin 14) => m.testBit z.val
      valid C a b → accepts C a b → (∃ x, excl C a b x) → (∃ x, excl C b a x) →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ), valid D u v ∧ D.size = C.size ∧
        accepts D u v ∧ excl D u v (row 129) ∧
        ∃ m ∈ ([257, 514, 4100] : List ℕ), excl D v u (row m))
    (h0 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ), PEqualNP.MetaComplexity.Monotone2 D →
      D.size ≤ 25 → a < 14 + D.size → b < 14 + D.size →
      let read : ℕ → ℕ → Bool := fun k m => (D.wires (List.ofFn (fun z : Fin 14 => m.testBit z.val))).getD k false
      ((∀ m ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ), read a m = true ∨ read b m = true) ∧
      (∀ m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), read a m = false ∧ read b m = false) ∧
      read a 129 = true ∧ read b 129 = false ∧
      read b 257 = true ∧ read a 257 = false) → False)
    (h1 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ), PEqualNP.MetaComplexity.Monotone2 D →
      D.size ≤ 25 → a < 14 + D.size → b < 14 + D.size →
      let read : ℕ → ℕ → Bool := fun k m => (D.wires (List.ofFn (fun z : Fin 14 => m.testBit z.val))).getD k false
      ((∀ m ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ), read a m = true ∨ read b m = true) ∧
      (∀ m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), read a m = false ∧ read b m = false) ∧
      read a 129 = true ∧ read b 129 = false ∧
      read b 514 = true ∧ read a 514 = false) → False)
    (h2 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ), PEqualNP.MetaComplexity.Monotone2 D →
      D.size ≤ 25 → a < 14 + D.size → b < 14 + D.size →
      let read : ℕ → ℕ → Bool := fun k m => (D.wires (List.ofFn (fun z : Fin 14 => m.testBit z.val))).getD k false
      ((∀ m ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ), read a m = true ∨ read b m = true) ∧
      (∀ m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), read a m = false ∧ read b m = false) ∧
      read a 129 = true ∧ read b 129 = false ∧
      read b 4100 = true ∧ read a 4100 = false) → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) → (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) → (26 : ℕ) ≤ x1.size := by
  intro C u v hm hu hv
  dsimp only
  intro hp hn hl hr
  let pred (x : Fin 14 → Bool) : Prop := ∃ s t : Fin 14,
    (54476011632248939714359330176 : ℕ).testBit (14 * s.val + t.val) = true ∧ x s = true ∧ x t = true
  let bits (m : ℕ) (t : Fin 14) := m.testBit t.val
  have adj : ∀ s t : Fin 14, (54476011632248939714359330176 : ℕ).testBit (14 * s.val + t.val) = true ↔
      (s.val, t.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) := by decide +kernel
  have corr (x : Fin 14 → Bool) : pred x ↔ ∃ s t : Fin 14,
      (s.val, t.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x s = true ∧ x t = true := by
    constructor
    · rintro ⟨s,t,he,hs,ht⟩
      exact ⟨s,t,(adj s t).mp he,hs,ht⟩
    · rintro ⟨s,t,he,hs,ht⟩
      exact ⟨s,t,(adj s t).mpr he,hs,ht⟩
  have acc (x : Fin 14 → Bool) : pred x ↔
      (C.wires (List.ofFn x)).getD u false = true ∨ (C.wires (List.ofFn x)).getD v false = true := by
    refine ⟨fun h => hp _ ((corr _).mp h), ?_⟩
    intro h
    by_contra he
    obtain ⟨ha,hb⟩ := hn x (fun h => he ((corr _).mpr h))
    rcases h with h | h
    · rw [ha] at h
      contradiction
    · rw [hb] at h
      contradiction
  obtain ⟨xl, _, hxl⟩ := hl
  obtain ⟨xr, _, hxr⟩ := hr
  obtain ⟨D,a,b,⟨hD,ha,hb⟩,hs,hacc,hfirst,m,hmem,hsecond⟩ :=
    hNormalize C u v ⟨hm,hu,hv⟩ acc ⟨xl,hxl⟩ ⟨xr,hxr⟩
  have pos : ∀ m ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ), pred (bits m) := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only [pred,bits]; decide +kernel
  have neg : ∀ m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), ¬ pred (bits m) := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only [pred,bits]; decide +kernel
  have pp (m : ℕ) (hm : m ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ)) := (hacc (bits m)).mp (pos m hm)
  have nn (m : ℕ) (hm : m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ)) :
      (D.wires (List.ofFn (bits m))).getD a false = false ∧ (D.wires (List.ofFn (bits m))).getD b false = false := by
    have hh := neg m hm
    constructor
    · cases he : (D.wires (List.ofFn (bits m))).getD a false with
      | false => rfl
      | true => exact (hh ((hacc _).mpr (Or.inl he))).elim
    · cases he : (D.wires (List.ofFn (bits m))).getD b false with
      | false => rfl
      | true => exact (hh ((hacc _).mpr (Or.inr he))).elim
  by_contra! hsmall
  have hd : D.size ≤ 25 := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact h0 D a b hD hd ha hb ⟨pp, nn, hfirst.1, hfirst.2, hsecond⟩
  · exact h1 D a b hD hd ha hb ⟨pp, nn, hfirst.1, hfirst.2, hsecond⟩
  · exact h2 D a b hD hd ha hb ⟨pp, nn, hfirst.1, hfirst.2, hsecond⟩
