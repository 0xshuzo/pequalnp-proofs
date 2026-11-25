import PEqualNP.Defs

namespace Near9774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.MetaComplexity.NestedCover

-- Physical wire projections from the published L8933 (Apache-2.0).
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def circuit : Circuit := ⟨[⟨.or,[8,10]⟩,⟨.and,[0,14]⟩,⟨.or,[7,13]⟩,⟨.and,[1,16]⟩,⟨.or,[8,12]⟩,⟨.or,[18,13]⟩,⟨.and,[2,19]⟩,⟨.or,[7,11]⟩,⟨.or,[21,12]⟩,⟨.and,[3,22]⟩,⟨.or,[10,11]⟩,⟨.or,[24,13]⟩,⟨.and,[4,25]⟩,⟨.or,[9,10]⟩,⟨.or,[27,12]⟩,⟨.and,[5,28]⟩,⟨.or,[8,9]⟩,⟨.or,[30,11]⟩,⟨.and,[6,31]⟩,⟨.or,[15,17]⟩,⟨.or,[33,20]⟩,⟨.or,[34,23]⟩,⟨.or,[35,26]⟩,⟨.or,[36,29]⟩,⟨.or,[37,32]⟩],38⟩
def pairs : List (Fin 14 × Fin 14) := [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def target (x : Fin 14 → Bool) := pairs.any fun p => x p.1 && x p.2
theorem valTarget (x : Fin 14 → Bool) : circuit.eval (List.ofFn x) = target x := by
  have h0 : val circuit (List.ofFn x) 0 = x 0 := val_ofFn circuit x (0:Fin 14)
  have h1 : val circuit (List.ofFn x) 1 = x 1 := val_ofFn circuit x (1:Fin 14)
  have h2 : val circuit (List.ofFn x) 2 = x 2 := val_ofFn circuit x (2:Fin 14)
  have h3 : val circuit (List.ofFn x) 3 = x 3 := val_ofFn circuit x (3:Fin 14)
  have h4 : val circuit (List.ofFn x) 4 = x 4 := val_ofFn circuit x (4:Fin 14)
  have h5 : val circuit (List.ofFn x) 5 = x 5 := val_ofFn circuit x (5:Fin 14)
  have h6 : val circuit (List.ofFn x) 6 = x 6 := val_ofFn circuit x (6:Fin 14)
  have h7 : val circuit (List.ofFn x) 7 = x 7 := val_ofFn circuit x (7:Fin 14)
  have h8 : val circuit (List.ofFn x) 8 = x 8 := val_ofFn circuit x (8:Fin 14)
  have h9 : val circuit (List.ofFn x) 9 = x 9 := val_ofFn circuit x (9:Fin 14)
  have h10 : val circuit (List.ofFn x) 10 = x 10 := val_ofFn circuit x (10:Fin 14)
  have h11 : val circuit (List.ofFn x) 11 = x 11 := val_ofFn circuit x (11:Fin 14)
  have h12 : val circuit (List.ofFn x) 12 = x 12 := val_ofFn circuit x (12:Fin 14)
  have h13 : val circuit (List.ofFn x) 13 = x 13 := val_ofFn circuit x (13:Fin 14)
  let v14 := GateOp.or.eval [(x 8),(x 10)]
  have h14 : val circuit (List.ofFn x) 14 = v14 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=0) (by simp) (by decide)]
    change GateOp.or.eval [(if 8 < 14 then val circuit (List.ofFn x) 8 else false),(if 10 < 14 then val circuit (List.ofFn x) 10 else false)] = v14
    simp only [v14,if_pos (by decide : 8 < 14),if_pos (by decide : 10 < 14),h8,h10]
  let v15 := GateOp.and.eval [(x 0),v14]
  have h15 : val circuit (List.ofFn x) 15 = v15 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=1) (by simp) (by decide)]
    change GateOp.and.eval [(if 0 < 15 then val circuit (List.ofFn x) 0 else false),(if 14 < 15 then val circuit (List.ofFn x) 14 else false)] = v15
    simp only [v15,if_pos (by decide : 0 < 15),if_pos (by decide : 14 < 15),h0,h14]
  let v16 := GateOp.or.eval [(x 7),(x 13)]
  have h16 : val circuit (List.ofFn x) 16 = v16 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=2) (by simp) (by decide)]
    change GateOp.or.eval [(if 7 < 16 then val circuit (List.ofFn x) 7 else false),(if 13 < 16 then val circuit (List.ofFn x) 13 else false)] = v16
    simp only [v16,if_pos (by decide : 7 < 16),if_pos (by decide : 13 < 16),h7,h13]
  let v17 := GateOp.and.eval [(x 1),v16]
  have h17 : val circuit (List.ofFn x) 17 = v17 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=3) (by simp) (by decide)]
    change GateOp.and.eval [(if 1 < 17 then val circuit (List.ofFn x) 1 else false),(if 16 < 17 then val circuit (List.ofFn x) 16 else false)] = v17
    simp only [v17,if_pos (by decide : 1 < 17),if_pos (by decide : 16 < 17),h1,h16]
  let v18 := GateOp.or.eval [(x 8),(x 12)]
  have h18 : val circuit (List.ofFn x) 18 = v18 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=4) (by simp) (by decide)]
    change GateOp.or.eval [(if 8 < 18 then val circuit (List.ofFn x) 8 else false),(if 12 < 18 then val circuit (List.ofFn x) 12 else false)] = v18
    simp only [v18,if_pos (by decide : 8 < 18),if_pos (by decide : 12 < 18),h8,h12]
  let v19 := GateOp.or.eval [v18,(x 13)]
  have h19 : val circuit (List.ofFn x) 19 = v19 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=5) (by simp) (by decide)]
    change GateOp.or.eval [(if 18 < 19 then val circuit (List.ofFn x) 18 else false),(if 13 < 19 then val circuit (List.ofFn x) 13 else false)] = v19
    simp only [v19,if_pos (by decide : 18 < 19),if_pos (by decide : 13 < 19),h18,h13]
  let v20 := GateOp.and.eval [(x 2),v19]
  have h20 : val circuit (List.ofFn x) 20 = v20 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=6) (by simp) (by decide)]
    change GateOp.and.eval [(if 2 < 20 then val circuit (List.ofFn x) 2 else false),(if 19 < 20 then val circuit (List.ofFn x) 19 else false)] = v20
    simp only [v20,if_pos (by decide : 2 < 20),if_pos (by decide : 19 < 20),h2,h19]
  let v21 := GateOp.or.eval [(x 7),(x 11)]
  have h21 : val circuit (List.ofFn x) 21 = v21 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=7) (by simp) (by decide)]
    change GateOp.or.eval [(if 7 < 21 then val circuit (List.ofFn x) 7 else false),(if 11 < 21 then val circuit (List.ofFn x) 11 else false)] = v21
    simp only [v21,if_pos (by decide : 7 < 21),if_pos (by decide : 11 < 21),h7,h11]
  let v22 := GateOp.or.eval [v21,(x 12)]
  have h22 : val circuit (List.ofFn x) 22 = v22 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=8) (by simp) (by decide)]
    change GateOp.or.eval [(if 21 < 22 then val circuit (List.ofFn x) 21 else false),(if 12 < 22 then val circuit (List.ofFn x) 12 else false)] = v22
    simp only [v22,if_pos (by decide : 21 < 22),if_pos (by decide : 12 < 22),h21,h12]
  let v23 := GateOp.and.eval [(x 3),v22]
  have h23 : val circuit (List.ofFn x) 23 = v23 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=9) (by simp) (by decide)]
    change GateOp.and.eval [(if 3 < 23 then val circuit (List.ofFn x) 3 else false),(if 22 < 23 then val circuit (List.ofFn x) 22 else false)] = v23
    simp only [v23,if_pos (by decide : 3 < 23),if_pos (by decide : 22 < 23),h3,h22]
  let v24 := GateOp.or.eval [(x 10),(x 11)]
  have h24 : val circuit (List.ofFn x) 24 = v24 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=10) (by simp) (by decide)]
    change GateOp.or.eval [(if 10 < 24 then val circuit (List.ofFn x) 10 else false),(if 11 < 24 then val circuit (List.ofFn x) 11 else false)] = v24
    simp only [v24,if_pos (by decide : 10 < 24),if_pos (by decide : 11 < 24),h10,h11]
  let v25 := GateOp.or.eval [v24,(x 13)]
  have h25 : val circuit (List.ofFn x) 25 = v25 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=11) (by simp) (by decide)]
    change GateOp.or.eval [(if 24 < 25 then val circuit (List.ofFn x) 24 else false),(if 13 < 25 then val circuit (List.ofFn x) 13 else false)] = v25
    simp only [v25,if_pos (by decide : 24 < 25),if_pos (by decide : 13 < 25),h24,h13]
  let v26 := GateOp.and.eval [(x 4),v25]
  have h26 : val circuit (List.ofFn x) 26 = v26 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=12) (by simp) (by decide)]
    change GateOp.and.eval [(if 4 < 26 then val circuit (List.ofFn x) 4 else false),(if 25 < 26 then val circuit (List.ofFn x) 25 else false)] = v26
    simp only [v26,if_pos (by decide : 4 < 26),if_pos (by decide : 25 < 26),h4,h25]
  let v27 := GateOp.or.eval [(x 9),(x 10)]
  have h27 : val circuit (List.ofFn x) 27 = v27 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=13) (by simp) (by decide)]
    change GateOp.or.eval [(if 9 < 27 then val circuit (List.ofFn x) 9 else false),(if 10 < 27 then val circuit (List.ofFn x) 10 else false)] = v27
    simp only [v27,if_pos (by decide : 9 < 27),if_pos (by decide : 10 < 27),h9,h10]
  let v28 := GateOp.or.eval [v27,(x 12)]
  have h28 : val circuit (List.ofFn x) 28 = v28 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=14) (by simp) (by decide)]
    change GateOp.or.eval [(if 27 < 28 then val circuit (List.ofFn x) 27 else false),(if 12 < 28 then val circuit (List.ofFn x) 12 else false)] = v28
    simp only [v28,if_pos (by decide : 27 < 28),if_pos (by decide : 12 < 28),h27,h12]
  let v29 := GateOp.and.eval [(x 5),v28]
  have h29 : val circuit (List.ofFn x) 29 = v29 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=15) (by simp) (by decide)]
    change GateOp.and.eval [(if 5 < 29 then val circuit (List.ofFn x) 5 else false),(if 28 < 29 then val circuit (List.ofFn x) 28 else false)] = v29
    simp only [v29,if_pos (by decide : 5 < 29),if_pos (by decide : 28 < 29),h5,h28]
  let v30 := GateOp.or.eval [(x 8),(x 9)]
  have h30 : val circuit (List.ofFn x) 30 = v30 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=16) (by simp) (by decide)]
    change GateOp.or.eval [(if 8 < 30 then val circuit (List.ofFn x) 8 else false),(if 9 < 30 then val circuit (List.ofFn x) 9 else false)] = v30
    simp only [v30,if_pos (by decide : 8 < 30),if_pos (by decide : 9 < 30),h8,h9]
  let v31 := GateOp.or.eval [v30,(x 11)]
  have h31 : val circuit (List.ofFn x) 31 = v31 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=17) (by simp) (by decide)]
    change GateOp.or.eval [(if 30 < 31 then val circuit (List.ofFn x) 30 else false),(if 11 < 31 then val circuit (List.ofFn x) 11 else false)] = v31
    simp only [v31,if_pos (by decide : 30 < 31),if_pos (by decide : 11 < 31),h30,h11]
  let v32 := GateOp.and.eval [(x 6),v31]
  have h32 : val circuit (List.ofFn x) 32 = v32 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=18) (by simp) (by decide)]
    change GateOp.and.eval [(if 6 < 32 then val circuit (List.ofFn x) 6 else false),(if 31 < 32 then val circuit (List.ofFn x) 31 else false)] = v32
    simp only [v32,if_pos (by decide : 6 < 32),if_pos (by decide : 31 < 32),h6,h31]
  let v33 := GateOp.or.eval [v15,v17]
  have h33 : val circuit (List.ofFn x) 33 = v33 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=19) (by simp) (by decide)]
    change GateOp.or.eval [(if 15 < 33 then val circuit (List.ofFn x) 15 else false),(if 17 < 33 then val circuit (List.ofFn x) 17 else false)] = v33
    simp only [v33,if_pos (by decide : 15 < 33),if_pos (by decide : 17 < 33),h15,h17]
  let v34 := GateOp.or.eval [v33,v20]
  have h34 : val circuit (List.ofFn x) 34 = v34 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=20) (by simp) (by decide)]
    change GateOp.or.eval [(if 33 < 34 then val circuit (List.ofFn x) 33 else false),(if 20 < 34 then val circuit (List.ofFn x) 20 else false)] = v34
    simp only [v34,if_pos (by decide : 33 < 34),if_pos (by decide : 20 < 34),h33,h20]
  let v35 := GateOp.or.eval [v34,v23]
  have h35 : val circuit (List.ofFn x) 35 = v35 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=21) (by simp) (by decide)]
    change GateOp.or.eval [(if 34 < 35 then val circuit (List.ofFn x) 34 else false),(if 23 < 35 then val circuit (List.ofFn x) 23 else false)] = v35
    simp only [v35,if_pos (by decide : 34 < 35),if_pos (by decide : 23 < 35),h34,h23]
  let v36 := GateOp.or.eval [v35,v26]
  have h36 : val circuit (List.ofFn x) 36 = v36 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=22) (by simp) (by decide)]
    change GateOp.or.eval [(if 35 < 36 then val circuit (List.ofFn x) 35 else false),(if 26 < 36 then val circuit (List.ofFn x) 26 else false)] = v36
    simp only [v36,if_pos (by decide : 35 < 36),if_pos (by decide : 26 < 36),h35,h26]
  let v37 := GateOp.or.eval [v36,v29]
  have h37 : val circuit (List.ofFn x) 37 = v37 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=23) (by simp) (by decide)]
    change GateOp.or.eval [(if 36 < 37 then val circuit (List.ofFn x) 36 else false),(if 29 < 37 then val circuit (List.ofFn x) 29 else false)] = v37
    simp only [v37,if_pos (by decide : 36 < 37),if_pos (by decide : 29 < 37),h36,h29]
  let v38 := GateOp.or.eval [v37,v32]
  have h38 : val circuit (List.ofFn x) 38 = v38 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=24) (by simp) (by decide)]
    change GateOp.or.eval [(if 37 < 38 then val circuit (List.ofFn x) 37 else false),(if 32 < 38 then val circuit (List.ofFn x) 32 else false)] = v38
    simp only [v38,if_pos (by decide : 37 < 38),if_pos (by decide : 32 < 38),h37,h32]
  change val circuit (List.ofFn x) 38 = target x
  rw [h38]
  dsimp [v38,v37,v36,v35,v34,v33,v32,v31,v30,v29,v28,v27,v26,v25,v24,v23,v22,v21,v20,v19,v18,v17,v16,v15,v14,target,pairs,GateOp.eval,List.any,List.all]
  bv_decide
theorem legal : Monotone2 circuit := by
  intro k hk
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,le_rfl⟩ | exact ⟨Or.inr rfl,le_rfl⟩
theorem near : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 25 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  refine ⟨circuit,legal,by decide,?_⟩
  intro x
  rw [valTarget]
  change (pairs.any (fun p => x p.1 && x p.2) = true) ↔ _
  rw [List.any_eq_true]
  have ident : ∀ u v : Fin 14, (u,v)∈pairs ↔ (u.val,v.val)∈[(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] := by decide
  constructor
  · rintro ⟨⟨u,v⟩,h,hx⟩
    exact ⟨u,v,(ident u v).mp h,(Bool.and_eq_true_iff.mp hx).1,(Bool.and_eq_true_iff.mp hx).2⟩
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨(u,v),(ident u v).mpr h,Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩
end Near9774
