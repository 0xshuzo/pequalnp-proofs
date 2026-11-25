import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3338_215
    (pin : let I (b : Bool) (x : Fin 8 → Bool) := [x 1,x 0,x 4,x 7,x 5,x 2,b,x 6,x 3,x 1 || b];
    let T (x : Fin 8 → Bool) := let n := tableIndex x; ([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (n / 64) 0 |>.testBit (n % 64);
    ∀ (p s : List Gate) (g : Gate) (o : ℕ), let C : Circuit := ⟨p ++ g::s,o⟩;
    FanInTwo C → g.op=GateOp.or → 6∈g.inputs → (∀ x, C.eval (I false x)=T x) →
    ∃ D : Circuit, FanInTwo D ∧ D.size≤p.length+s.length ∧
      D.gates.countP (fun h => h.op.eval [true]) ≤ (p++s).countP (fun h => h.op.eval [true]) ∧
      ∀ x, D.eval (List.ofFn x)=T x)
    (raw : let T (x : Fin 8 → Bool) := let n := tableIndex x; ([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (n / 64) 0 |>.testBit (n % 64);
    ∀ D : Circuit, FanInTwo D → D.size≤13 → D.gates.countP (fun h => h.op.eval [true]) ≤ 12 →
    ∃ x, D.eval (List.ofFn x)≠T x)
    (mono : let I (b : Bool) (x : Fin 8 → Bool) := [x 1,x 0,x 4,x 7,x 5,x 2,b,x 6,x 3,x 1 || b];
    let T (x : Fin 8 → Bool) := let n := tableIndex x; ([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (n / 64) 0 |>.testBit (n % 64);
    ∀ C : Circuit, Monotone2 C → C.size≤14 → (∀ x,C.eval (I false x)=T x) →
    ∃ x,C.eval (I true x)≠(T x || x 0 || x 3)) : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) =>   have x4 : ℕ := PEqualNP.MetaComplexity.tableIndex x3;   ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x4 / (64 : ℕ)) (0 : ℕ)).testBit (x4 % (64 : ℕ)); ∀ (x4 x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ),   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x4 ++ x6 :: x5, output := x7 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x8 →     x4.length + x5.length ≤ (13 : ℕ) →       (∀ x11 ∈ x4 ++ x5, x1 x11 = Bool.false) →         x1 x6 = Bool.true →           x6.op = PEqualNP.CircuitLowerBounds.GateOp.or →             (have x14 : Fin (8 : ℕ) → Bool := fun (x14 : Fin (8 : ℕ)) => Decidable.decide (x14 = (1 : Fin (8 : ℕ)) ∨ x14 = (3 : Fin (8 : ℕ)));               have x15 : Bool → Bool := fun (x15 : Bool) => x6.op.eval (List.map (fun (x16 : ℕ) => ({ gates := x4, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x2 x15 x14)).getD x16 Bool.false) x6.inputs);               x15 Bool.true ≠ x15 Bool.false) →               (∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.false x15) = x3 x15) → ∃ (x16 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.true x16) ≠ (x3 x16 || x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ))) := by
  intro rd I T p s g o C fan size others marked op probe low
  have len : C.size ≤ 14 := by
    change (p ++ g :: s).length ≤ 14
    simp only [List.length_append, List.length_cons]
    omega
  by_cases n : ∃ h ∈ p ++ s, h.op = GateOp.not
  · obtain ⟨h,hh,hn⟩ := n
    have uses : 6 ∈ g.inputs := by
      change (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun j => decide (j=6))=true at marked
      rw [op] at marked
      obtain ⟨i,hi,he⟩ := List.any_eq_true.mp (show g.inputs.any (fun j => decide (j=6))=true from marked)
      exact (of_decide_eq_true he) ▸ hi
    obtain ⟨D,fd,sd,pd,eq⟩ := pin p s g o fan op uses low
    have fewer : (p ++ s).countP (fun h => h.op.eval [true]) < (p ++ s).length := by
      have q := List.countP_le_length (p := fun h : Gate => h.op.eval [true]) (l := p ++ s)
      by_contra! he
      have all := List.countP_eq_length.mp (Nat.le_antisymm q he)
      have no := all h hh
      rw [hn] at no
      contradiction
    have price : D.gates.countP (fun h => h.op.eval [true]) ≤ 12 := by
      simp only [List.length_append] at fewer
      omega
    obtain ⟨x,bad⟩ := raw D fd (sd.trans size) price
    exact (bad (eq x)).elim
  · apply mono C _ len low
    intro h hh
    refine ⟨?_,(fan h hh).2⟩
    rcases (fan h hh).1 with and | or | neg
    · exact Or.inl and
    · exact Or.inr or
    · change h.op = GateOp.not at neg
      change h ∈ p ++ g :: s at hh
      rcases List.mem_append.mp hh with hp | tail
      · exact (n ⟨h,List.mem_append_left _ hp,neg⟩).elim
      rcases List.mem_cons.mp tail with rfl | hs
      · rw [op] at neg
        contradiction
      · exact (n ⟨h,List.mem_append_right _ hs,neg⟩).elim
