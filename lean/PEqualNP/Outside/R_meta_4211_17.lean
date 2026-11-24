import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The four translated flags and three boundary orbits locate an internal AND
-- that is true on both sides of the required separation.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4211_17
  (localize : let w := fun (C : Circuit) (i m : ℕ) (k : Fin 13) => (C.wires (List.ofFn (fun z : Fin 26 => m.testBit (13*(z.val/13)+(z.val % 13+13-k.val)%13)))).getD i false
    ∀ (C : Circuit) (a b : Fin (26+C.size)), Monotone2 C → C.size ≤ 62 → a ≠ b →
    (∀ m ∈ ([8193,8194,8200,8704] : List ℕ), ∀ k, (w C a m k || w C b m k) = true) →
    (∀ m ∈ ([8191,12513280,67100672] : List ℕ), ∀ k, (w C a m k || w C b m k) = false) → ∃ g : Fin C.gates.length, (C.gates.get g).op = GateOp.and ∧
        (∃ m ∈ ([8193,8194,8200,8704] : List ℕ), ∃ k, w C (26+g.val) m k = true) ∧
        (∃ m ∈ ([8191,12513280,67100672] : List ℕ), ∃ k, w C (26+g.val) m k = true))
  (mixed : let w := fun (C : Circuit) (i m : ℕ) (k : Fin 13) => (C.wires (List.ofFn (fun z : Fin 26 => m.testBit (13*(z.val/13)+(z.val % 13+13-k.val)%13)))).getD i false
    ∀ (C : Circuit) (a b : Fin (26+C.size)), Monotone2 C → C.size ≤ 62 → a ≠ b →
    (∀ m ∈ ([8193,8194,8200,8704] : List ℕ), ∀ k, (w C a m k || w C b m k) = true) →
    (∃ g : Fin C.gates.length, (C.gates.get g).op = GateOp.and ∧
        (∃ m ∈ ([8193,8194,8200,8704] : List ℕ), ∃ k, w C (26+g.val) m k = true) ∧
        (∃ m ∈ ([8191,12513280,67100672] : List ℕ), ∃ k, w C (26+g.val) m k = true)) → ∃ m ∈ ([8191,15860,31200,46544,77220,107904,146756,277652,292992,539952,1093712,1124388,1996800,3060736,3338304,4942080,5711876,10268688,12513280,67100672] : List ℕ), ∃ k, (w C a m k || w C b m k) = true) :
    have x1 : Finset (Fin (13 : ℕ)) := [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].toFinset; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) (x5 : Fin (26 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (13 : ℕ) x3 ∨ x5 = Fin.natAdd (13 : ℕ) x4); have x4 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x4 : Finset (Fin (13 : ℕ))) (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x6 ∈ x4, x5 = Fin.castAdd (13 : ℕ) x6) ∨ ∃ (x6 : Fin (13 : ℕ)), x5 = Fin.natAdd (13 : ℕ) x6 ∧ ∀ x7 ∈ x4, ¬∃ x9 ∈ x1, x7 = x6 + x9); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Fin (26 : ℕ) → Bool) => (x5.wires (List.ofFn x7)).getD x6 Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x6 →     x6.size ≤ (62 : ℕ) →       ∀ (x9 x10 : Fin ((26 : ℕ) + x6.size)),         x9 ≠ x10 →           (∀ (x12 x13 : Fin (13 : ℕ)), x2 x12 x13 → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 x6 (↑x9) (x3 x12 x13), x5 x6 (↑x10) (x3 x12 x13)] = Bool.true) →             (∀ (x13 : ℕ) (x14 : Fin (13 : ℕ)),                 x13 ∈ [(8191 : ℕ), (7668 : ℕ), (6624 : ℕ), (5584 : ℕ), (3492 : ℕ), (1408 : ℕ), (7492 : ℕ), (7316 : ℕ), (6272 : ℕ), (7472 : ℕ), (4176 : ℕ), (2084 : ℕ), (6144 : ℕ), (5120 : ℕ), (4160 : ℕ), (2304 : ℕ), (2052 : ℕ), (4112 : ℕ), (4096 : ℕ), (0 : ℕ)].toFinset →                   have x16 : Finset (Fin (13 : ℕ)) := {x16 : Fin (13 : ℕ) | x13.testBit ↑(x16 - x14) = Bool.true};                   PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 x6 (↑x9) (x4 x16), x5 x6 (↑x10) (x4 x16)] = Bool.false) →               False := by
  dsimp only
  intro C hm hs a b hn hpos hneg
  have orEval (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by
    change (u || (v || false)) = _
    rw [Bool.or_false]
  let row := fun (m : ℕ) (k : Fin 13) (i : Fin 26) => m.testBit (13 * (i.val / 13) + (i.val % 13 + 13 - k.val) % 13)
  let base : Finset (Fin 13) := ([0,1,3,9] : List (Fin 13)).toFinset
  let near := fun p l : Fin 13 => ∃ d ∈ base, p=l+d
  let yes := fun (p l : Fin 13) (j : Fin 26) => decide (j=Fin.castAdd 13 p ∨ j=Fin.natAdd 13 l)
  let no := fun (m : ℕ) (k : Fin 13) (j : Fin 26) =>
    let P := Finset.univ.filter (fun t : Fin 13 => m.testBit (t-k).val)
    decide ((∃ t ∈ P, j=Fin.castAdd 13 t) ∨ ∃ l : Fin 13, j=Fin.natAdd 13 l ∧ ∀ t ∈ P, ¬ near t l)
  let w := fun (i m : ℕ) (k : Fin 13) => (C.wires (List.ofFn (row m k))).getD i false
  let v := fun (i : ℕ) (x : Fin 26 → Bool) => (C.wires (List.ofFn x)).getD i false
  let good := fun (x : Fin 26 → Bool) => (v a x || v b x)
  have posBool (p l : Fin 13) (hi : near p l) : good (yes p l) = true :=
    (orEval (v a (yes p l)) (v b (yes p l))).symm.trans (hpos p l hi)
  have negBool (m : ℕ) (k : Fin 13)
      (hm : m ∈ ([8191,7668,6624,5584,3492,1408,7492,7316,6272,7472,4176,2084,6144,5120,4160,2304,2052,4112,4096,0] : List ℕ).toFinset) :
      good (no m k) = false :=
    (orEval (v a (no m k)) (v b (no m k))).symm.trans (hneg m k hm)
  let off := fun (m : ℕ) (l : Fin 13) => ∀ p : Fin 13, m.testBit p.val = true → ¬near p l
  have shift : ∀ p l k : Fin 13, near p l ↔ near (p-k) (l-k) := by decide +kernel
  have idxP : ∀ k p : Fin 13,
      13*((Fin.castAdd 13 p).val/13)+((Fin.castAdd 13 p).val % 13+13-k.val)%13 = (p-k).val := by decide +kernel
  have idxL : ∀ k l : Fin 13,
      13*((Fin.natAdd 13 l).val/13)+((Fin.natAdd 13 l).val % 13+13-k.val)%13 = 13+(l-k).val := by decide +kernel
  have apart : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide +kernel
  have pinj : ∀ p t : Fin 13, Fin.castAdd 13 p = Fin.castAdd 13 t → p=t := by decide +kernel
  have linj : ∀ l t : Fin 13, Fin.natAdd 13 l = Fin.natAdd 13 t → l=t := by decide +kernel
  have transport (M m : ℕ) (pm : ∀ t : Fin 13, M.testBit t.val = m.testBit t.val)
      (lm : ∀ t : Fin 13, M.testBit (13+t.val) = true ↔ off m t) (k : Fin 13) :
      row M k = no m k := by
    funext z
    refine Fin.addCases (motive := fun j : Fin (13+13) => row M k j = no m k j) (fun p : Fin 13 => ?_) (fun l : Fin 13 => ?_) z
    · apply Bool.eq_iff_iff.mpr
      change M.testBit _ = true ↔ decide _ = true
      rw [idxP k p,pm,decide_eq_true_eq]
      constructor
      · intro h
        exact Or.inl ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
      · rintro (⟨t,ht,e⟩ | ⟨l,e,_⟩)
        · have hpt := pinj p t e
          exact hpt ▸ (Finset.mem_filter.mp ht).2
        · exact False.elim (apart p l e)
    · apply Bool.eq_iff_iff.mpr
      change M.testBit _ = true ↔ decide _ = true
      rw [idxL k l,lm,decide_eq_true_eq]
      constructor
      · intro o
        refine Or.inr ⟨l,rfl,?_⟩
        intro p hp hi
        exact o (p-k) (Finset.mem_filter.mp hp).2 ((shift p l k).mp hi)
      · rintro (⟨p,_,e⟩ | ⟨t,e,h⟩)
        · exact False.elim (apart p l e.symm)
        · have he := linj l t e
          subst t
          intro p hp hi
          have back : p+k-k=p := by abel
          apply h (p+k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [back] using hp⟩)
          apply (shift (p+k) l k).mpr
          simpa only [back] using hi
  have pos : ∀ m ∈ ([8193,8194,8200,8704] : List ℕ), ∀ k, (w a m k || w b m k) = true := by
    intro m h k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · have e : ∀ t : Fin 13, row 8193 t = yes (t+0) t := by decide +kernel
      have inc : near (k+0) k := ⟨0,by decide,rfl⟩
      change good (row 8193 k) = true
      rw [e]
      exact posBool (k+0) k inc
    · have e : ∀ t : Fin 13, row 8194 t = yes (t+1) t := by decide +kernel
      have inc : near (k+1) k := ⟨1,by decide,rfl⟩
      change good (row 8194 k) = true
      rw [e]
      exact posBool (k+1) k inc
    · have e : ∀ t : Fin 13, row 8200 t = yes (t+3) t := by decide +kernel
      have inc : near (k+3) k := ⟨3,by decide,rfl⟩
      change good (row 8200 k) = true
      rw [e]
      exact posBool (k+3) k inc
    · have e : ∀ t : Fin 13, row 8704 t = yes (t+9) t := by decide +kernel
      have inc : near (k+9) k := ⟨9,by decide,rfl⟩
      change good (row 8704 k) = true
      rw [e]
      exact posBool (k+9) k inc
  have neg : ∀ m ∈ ([8191,15860,31200,46544,77220,107904,146756,277652,292992,539952,1093712,1124388,1996800,3060736,3338304,4942080,5711876,10268688,12513280,67100672] : List ℕ), ∀ k, (w a m k || w b m k) = false := by
    intro m h k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change good (row 8191 k) = false
      rw [transport 8191 8191 (by decide +kernel) (by decide +kernel)]
      exact negBool 8191 k (by decide)
    · change good (row 15860 k) = false
      rw [transport 15860 7668 (by decide +kernel) (by decide +kernel)]
      exact negBool 7668 k (by decide)
    · change good (row 31200 k) = false
      rw [transport 31200 6624 (by decide +kernel) (by decide +kernel)]
      exact negBool 6624 k (by decide)
    · change good (row 46544 k) = false
      rw [transport 46544 5584 (by decide +kernel) (by decide +kernel)]
      exact negBool 5584 k (by decide)
    · change good (row 77220 k) = false
      rw [transport 77220 3492 (by decide +kernel) (by decide +kernel)]
      exact negBool 3492 k (by decide)
    · change good (row 107904 k) = false
      rw [transport 107904 1408 (by decide +kernel) (by decide +kernel)]
      exact negBool 1408 k (by decide)
    · change good (row 146756 k) = false
      rw [transport 146756 7492 (by decide +kernel) (by decide +kernel)]
      exact negBool 7492 k (by decide)
    · change good (row 277652 k) = false
      rw [transport 277652 7316 (by decide +kernel) (by decide +kernel)]
      exact negBool 7316 k (by decide)
    · change good (row 292992 k) = false
      rw [transport 292992 6272 (by decide +kernel) (by decide +kernel)]
      exact negBool 6272 k (by decide)
    · change good (row 539952 k) = false
      rw [transport 539952 7472 (by decide +kernel) (by decide +kernel)]
      exact negBool 7472 k (by decide)
    · change good (row 1093712 k) = false
      rw [transport 1093712 4176 (by decide +kernel) (by decide +kernel)]
      exact negBool 4176 k (by decide)
    · change good (row 1124388 k) = false
      rw [transport 1124388 2084 (by decide +kernel) (by decide +kernel)]
      exact negBool 2084 k (by decide)
    · change good (row 1996800 k) = false
      rw [transport 1996800 6144 (by decide +kernel) (by decide +kernel)]
      exact negBool 6144 k (by decide)
    · change good (row 3060736 k) = false
      rw [transport 3060736 5120 (by decide +kernel) (by decide +kernel)]
      exact negBool 5120 k (by decide)
    · change good (row 3338304 k) = false
      rw [transport 3338304 4160 (by decide +kernel) (by decide +kernel)]
      exact negBool 4160 k (by decide)
    · change good (row 4942080 k) = false
      rw [transport 4942080 2304 (by decide +kernel) (by decide +kernel)]
      exact negBool 2304 k (by decide)
    · change good (row 5711876 k) = false
      rw [transport 5711876 2052 (by decide +kernel) (by decide +kernel)]
      exact negBool 2052 k (by decide)
    · change good (row 10268688 k) = false
      rw [transport 10268688 4112 (by decide +kernel) (by decide +kernel)]
      exact negBool 4112 k (by decide)
    · change good (row 12513280 k) = false
      rw [transport 12513280 4096 (by decide +kernel) (by decide +kernel)]
      exact negBool 4096 k (by decide)
    · change good (row 67100672 k) = false
      rw [transport 67100672 0 (by decide +kernel) (by decide +kernel)]
      exact negBool 0 k (by decide)
  have short : ∀ m ∈ ([8191,12513280,67100672] : List ℕ), ∀ k, (w a m k || w b m k) = false := by
    intro m h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl <;> exact neg _ (by decide)
  have hit := localize C a b hm hs hn pos short
  obtain ⟨m,hm0,k,hk⟩ := mixed C a b hm hs hn pos hit
  exact Bool.false_ne_true ((neg m hm0 k).symm.trans hk)
