import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9753.Baseline

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

def circuit : Circuit := ⟨[⟨.or,[7,8]⟩,⟨.or,[14,10]⟩,⟨.and,[0,15]⟩,⟨.or,[7,9]⟩,⟨.or,[17,13]⟩,⟨.and,[1,18]⟩,⟨.or,[8,12]⟩,⟨.or,[20,13]⟩,⟨.and,[2,21]⟩,⟨.or,[7,11]⟩,⟨.or,[23,12]⟩,⟨.and,[3,24]⟩,⟨.or,[10,11]⟩,⟨.or,[26,13]⟩,⟨.and,[4,27]⟩,⟨.or,[9,10]⟩,⟨.or,[29,12]⟩,⟨.and,[5,30]⟩,⟨.or,[8,9]⟩,⟨.or,[32,11]⟩,⟨.and,[6,33]⟩,⟨.or,[16,19]⟩,⟨.or,[35,22]⟩,⟨.or,[36,25]⟩,⟨.or,[37,28]⟩,⟨.or,[38,31]⟩,⟨.or,[39,34]⟩],40⟩
def pairs : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
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
  let v14 := GateOp.or.eval [(x 7),(x 8)]
  have h14 : val circuit (List.ofFn x) 14 = v14 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=0) (by simp) (by decide)]
    change GateOp.or.eval [(if 7 < 14 then val circuit (List.ofFn x) 7 else false),(if 8 < 14 then val circuit (List.ofFn x) 8 else false)] = v14
    simp only [v14,if_pos (by decide : 7 < 14),if_pos (by decide : 8 < 14),h7,h8]
  let v15 := GateOp.or.eval [v14,(x 10)]
  have h15 : val circuit (List.ofFn x) 15 = v15 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=1) (by simp) (by decide)]
    change GateOp.or.eval [(if 14 < 15 then val circuit (List.ofFn x) 14 else false),(if 10 < 15 then val circuit (List.ofFn x) 10 else false)] = v15
    simp only [v15,if_pos (by decide : 14 < 15),if_pos (by decide : 10 < 15),h14,h10]
  let v16 := GateOp.and.eval [(x 0),v15]
  have h16 : val circuit (List.ofFn x) 16 = v16 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=2) (by simp) (by decide)]
    change GateOp.and.eval [(if 0 < 16 then val circuit (List.ofFn x) 0 else false),(if 15 < 16 then val circuit (List.ofFn x) 15 else false)] = v16
    simp only [v16,if_pos (by decide : 0 < 16),if_pos (by decide : 15 < 16),h0,h15]
  let v17 := GateOp.or.eval [(x 7),(x 9)]
  have h17 : val circuit (List.ofFn x) 17 = v17 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=3) (by simp) (by decide)]
    change GateOp.or.eval [(if 7 < 17 then val circuit (List.ofFn x) 7 else false),(if 9 < 17 then val circuit (List.ofFn x) 9 else false)] = v17
    simp only [v17,if_pos (by decide : 7 < 17),if_pos (by decide : 9 < 17),h7,h9]
  let v18 := GateOp.or.eval [v17,(x 13)]
  have h18 : val circuit (List.ofFn x) 18 = v18 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=4) (by simp) (by decide)]
    change GateOp.or.eval [(if 17 < 18 then val circuit (List.ofFn x) 17 else false),(if 13 < 18 then val circuit (List.ofFn x) 13 else false)] = v18
    simp only [v18,if_pos (by decide : 17 < 18),if_pos (by decide : 13 < 18),h17,h13]
  let v19 := GateOp.and.eval [(x 1),v18]
  have h19 : val circuit (List.ofFn x) 19 = v19 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=5) (by simp) (by decide)]
    change GateOp.and.eval [(if 1 < 19 then val circuit (List.ofFn x) 1 else false),(if 18 < 19 then val circuit (List.ofFn x) 18 else false)] = v19
    simp only [v19,if_pos (by decide : 1 < 19),if_pos (by decide : 18 < 19),h1,h18]
  let v20 := GateOp.or.eval [(x 8),(x 12)]
  have h20 : val circuit (List.ofFn x) 20 = v20 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=6) (by simp) (by decide)]
    change GateOp.or.eval [(if 8 < 20 then val circuit (List.ofFn x) 8 else false),(if 12 < 20 then val circuit (List.ofFn x) 12 else false)] = v20
    simp only [v20,if_pos (by decide : 8 < 20),if_pos (by decide : 12 < 20),h8,h12]
  let v21 := GateOp.or.eval [v20,(x 13)]
  have h21 : val circuit (List.ofFn x) 21 = v21 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=7) (by simp) (by decide)]
    change GateOp.or.eval [(if 20 < 21 then val circuit (List.ofFn x) 20 else false),(if 13 < 21 then val circuit (List.ofFn x) 13 else false)] = v21
    simp only [v21,if_pos (by decide : 20 < 21),if_pos (by decide : 13 < 21),h20,h13]
  let v22 := GateOp.and.eval [(x 2),v21]
  have h22 : val circuit (List.ofFn x) 22 = v22 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=8) (by simp) (by decide)]
    change GateOp.and.eval [(if 2 < 22 then val circuit (List.ofFn x) 2 else false),(if 21 < 22 then val circuit (List.ofFn x) 21 else false)] = v22
    simp only [v22,if_pos (by decide : 2 < 22),if_pos (by decide : 21 < 22),h2,h21]
  let v23 := GateOp.or.eval [(x 7),(x 11)]
  have h23 : val circuit (List.ofFn x) 23 = v23 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=9) (by simp) (by decide)]
    change GateOp.or.eval [(if 7 < 23 then val circuit (List.ofFn x) 7 else false),(if 11 < 23 then val circuit (List.ofFn x) 11 else false)] = v23
    simp only [v23,if_pos (by decide : 7 < 23),if_pos (by decide : 11 < 23),h7,h11]
  let v24 := GateOp.or.eval [v23,(x 12)]
  have h24 : val circuit (List.ofFn x) 24 = v24 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=10) (by simp) (by decide)]
    change GateOp.or.eval [(if 23 < 24 then val circuit (List.ofFn x) 23 else false),(if 12 < 24 then val circuit (List.ofFn x) 12 else false)] = v24
    simp only [v24,if_pos (by decide : 23 < 24),if_pos (by decide : 12 < 24),h23,h12]
  let v25 := GateOp.and.eval [(x 3),v24]
  have h25 : val circuit (List.ofFn x) 25 = v25 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=11) (by simp) (by decide)]
    change GateOp.and.eval [(if 3 < 25 then val circuit (List.ofFn x) 3 else false),(if 24 < 25 then val circuit (List.ofFn x) 24 else false)] = v25
    simp only [v25,if_pos (by decide : 3 < 25),if_pos (by decide : 24 < 25),h3,h24]
  let v26 := GateOp.or.eval [(x 10),(x 11)]
  have h26 : val circuit (List.ofFn x) 26 = v26 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=12) (by simp) (by decide)]
    change GateOp.or.eval [(if 10 < 26 then val circuit (List.ofFn x) 10 else false),(if 11 < 26 then val circuit (List.ofFn x) 11 else false)] = v26
    simp only [v26,if_pos (by decide : 10 < 26),if_pos (by decide : 11 < 26),h10,h11]
  let v27 := GateOp.or.eval [v26,(x 13)]
  have h27 : val circuit (List.ofFn x) 27 = v27 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=13) (by simp) (by decide)]
    change GateOp.or.eval [(if 26 < 27 then val circuit (List.ofFn x) 26 else false),(if 13 < 27 then val circuit (List.ofFn x) 13 else false)] = v27
    simp only [v27,if_pos (by decide : 26 < 27),if_pos (by decide : 13 < 27),h26,h13]
  let v28 := GateOp.and.eval [(x 4),v27]
  have h28 : val circuit (List.ofFn x) 28 = v28 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=14) (by simp) (by decide)]
    change GateOp.and.eval [(if 4 < 28 then val circuit (List.ofFn x) 4 else false),(if 27 < 28 then val circuit (List.ofFn x) 27 else false)] = v28
    simp only [v28,if_pos (by decide : 4 < 28),if_pos (by decide : 27 < 28),h4,h27]
  let v29 := GateOp.or.eval [(x 9),(x 10)]
  have h29 : val circuit (List.ofFn x) 29 = v29 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=15) (by simp) (by decide)]
    change GateOp.or.eval [(if 9 < 29 then val circuit (List.ofFn x) 9 else false),(if 10 < 29 then val circuit (List.ofFn x) 10 else false)] = v29
    simp only [v29,if_pos (by decide : 9 < 29),if_pos (by decide : 10 < 29),h9,h10]
  let v30 := GateOp.or.eval [v29,(x 12)]
  have h30 : val circuit (List.ofFn x) 30 = v30 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=16) (by simp) (by decide)]
    change GateOp.or.eval [(if 29 < 30 then val circuit (List.ofFn x) 29 else false),(if 12 < 30 then val circuit (List.ofFn x) 12 else false)] = v30
    simp only [v30,if_pos (by decide : 29 < 30),if_pos (by decide : 12 < 30),h29,h12]
  let v31 := GateOp.and.eval [(x 5),v30]
  have h31 : val circuit (List.ofFn x) 31 = v31 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=17) (by simp) (by decide)]
    change GateOp.and.eval [(if 5 < 31 then val circuit (List.ofFn x) 5 else false),(if 30 < 31 then val circuit (List.ofFn x) 30 else false)] = v31
    simp only [v31,if_pos (by decide : 5 < 31),if_pos (by decide : 30 < 31),h5,h30]
  let v32 := GateOp.or.eval [(x 8),(x 9)]
  have h32 : val circuit (List.ofFn x) 32 = v32 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=18) (by simp) (by decide)]
    change GateOp.or.eval [(if 8 < 32 then val circuit (List.ofFn x) 8 else false),(if 9 < 32 then val circuit (List.ofFn x) 9 else false)] = v32
    simp only [v32,if_pos (by decide : 8 < 32),if_pos (by decide : 9 < 32),h8,h9]
  let v33 := GateOp.or.eval [v32,(x 11)]
  have h33 : val circuit (List.ofFn x) 33 = v33 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=19) (by simp) (by decide)]
    change GateOp.or.eval [(if 32 < 33 then val circuit (List.ofFn x) 32 else false),(if 11 < 33 then val circuit (List.ofFn x) 11 else false)] = v33
    simp only [v33,if_pos (by decide : 32 < 33),if_pos (by decide : 11 < 33),h32,h11]
  let v34 := GateOp.and.eval [(x 6),v33]
  have h34 : val circuit (List.ofFn x) 34 = v34 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=20) (by simp) (by decide)]
    change GateOp.and.eval [(if 6 < 34 then val circuit (List.ofFn x) 6 else false),(if 33 < 34 then val circuit (List.ofFn x) 33 else false)] = v34
    simp only [v34,if_pos (by decide : 6 < 34),if_pos (by decide : 33 < 34),h6,h33]
  let v35 := GateOp.or.eval [v16,v19]
  have h35 : val circuit (List.ofFn x) 35 = v35 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=21) (by simp) (by decide)]
    change GateOp.or.eval [(if 16 < 35 then val circuit (List.ofFn x) 16 else false),(if 19 < 35 then val circuit (List.ofFn x) 19 else false)] = v35
    simp only [v35,if_pos (by decide : 16 < 35),if_pos (by decide : 19 < 35),h16,h19]
  let v36 := GateOp.or.eval [v35,v22]
  have h36 : val circuit (List.ofFn x) 36 = v36 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=22) (by simp) (by decide)]
    change GateOp.or.eval [(if 35 < 36 then val circuit (List.ofFn x) 35 else false),(if 22 < 36 then val circuit (List.ofFn x) 22 else false)] = v36
    simp only [v36,if_pos (by decide : 35 < 36),if_pos (by decide : 22 < 36),h35,h22]
  let v37 := GateOp.or.eval [v36,v25]
  have h37 : val circuit (List.ofFn x) 37 = v37 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=23) (by simp) (by decide)]
    change GateOp.or.eval [(if 36 < 37 then val circuit (List.ofFn x) 36 else false),(if 25 < 37 then val circuit (List.ofFn x) 25 else false)] = v37
    simp only [v37,if_pos (by decide : 36 < 37),if_pos (by decide : 25 < 37),h36,h25]
  let v38 := GateOp.or.eval [v37,v28]
  have h38 : val circuit (List.ofFn x) 38 = v38 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=24) (by simp) (by decide)]
    change GateOp.or.eval [(if 37 < 38 then val circuit (List.ofFn x) 37 else false),(if 28 < 38 then val circuit (List.ofFn x) 28 else false)] = v38
    simp only [v38,if_pos (by decide : 37 < 38),if_pos (by decide : 28 < 38),h37,h28]
  let v39 := GateOp.or.eval [v38,v31]
  have h39 : val circuit (List.ofFn x) 39 = v39 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=25) (by simp) (by decide)]
    change GateOp.or.eval [(if 38 < 39 then val circuit (List.ofFn x) 38 else false),(if 31 < 39 then val circuit (List.ofFn x) 31 else false)] = v39
    simp only [v39,if_pos (by decide : 38 < 39),if_pos (by decide : 31 < 39),h38,h31]
  let v40 := GateOp.or.eval [v39,v34]
  have h40 : val circuit (List.ofFn x) 40 = v40 := by
    rw [val_gate (C:=circuit) (n:=14) (j:=26) (by simp) (by decide)]
    change GateOp.or.eval [(if 39 < 40 then val circuit (List.ofFn x) 39 else false),(if 34 < 40 then val circuit (List.ofFn x) 34 else false)] = v40
    simp only [v40,if_pos (by decide : 39 < 40),if_pos (by decide : 34 < 40),h39,h34]
  change val circuit (List.ofFn x) 40 = target x
  rw [h40]
  dsimp [v40,v39,v38,v37,v36,v35,v34,v33,v32,v31,v30,v29,v28,v27,v26,v25,v24,v23,v22,v21,v20,v19,v18,v17,v16,v15,v14,target,pairs,GateOp.eval,List.any,List.all]
  simp only [Bool.and_true,Bool.or_false,Bool.true_and,Bool.false_or,Bool.and_or_distrib_left,Bool.or_assoc] <;> ac_rfl
theorem legal : Monotone2 circuit := by
  intro k hk
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,le_rfl⟩ | exact ⟨Or.inr rfl,le_rfl⟩
theorem signed : PEqualNP.MetaComplexity.HasCircuitSize 14 (fun x : Fin 14 → Bool => (x 0 && x 7) || (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)) 27 := by
  refine ⟨circuit,?_,by decide,?_⟩
  · intro g hg
    obtain ⟨h,size⟩ := legal g hg
    refine ⟨?_,size⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h ⊢
    exact h.elim Or.inl (fun z => Or.inr (Or.inl z))
  · intro x
    rw [valTarget]
    simp only [target,pairs,List.any,Bool.or_false] <;> ac_rfl
end PEqualNP.Outside.L_meta_9753.Baseline
