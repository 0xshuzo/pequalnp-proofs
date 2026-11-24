import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_1479_417
   (convertRank : ∀ C : Circuit, (∀ (j : ℕ) (g : Gate), C.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
       ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) → ∀ s : Bool, (∃ k : ℕ, 2≤k ∧ ((PEqualNP.ReadK.scalarMults C 14 [0,7] (if s then 7 else 0)).getD C.output none)=some k) → ∃ d : ℕ → Bool, (∀ i : Fin 7, d i.val = (if s then false else decide (i = 0)) ∧ d (7+i.val) = (if s then decide (i = 0) else false)) ∧ (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] → let w := C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then Fin.castAdd 7 (0 : Fin 7) else Fin.natAdd 7 (0 : Fin 7))); (g.op = GateOp.and → d (14+j) = ((w.getD a false && d b) || (d a && w.getD b false))) ∧ (g.op = GateOp.or → d (14+j) = (d a || d b))) ∧ d C.output = false)
   (search : ∃ (C : Circuit) (op : GateOp) (a b : ℕ), C.size≤27 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
       ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) ∧
    C.gates[0]?=some ⟨op,[a,b]⟩ ∧ a*14+b ∈ [1,2,7,8,11,16,17,22,23,25,32,34,36,38] ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 7,
       (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true) ∧
    ∀ s : Bool, ∃ k : ℕ, 2≤k ∧ ((PEqualNP.ReadK.scalarMults C 14 [0,7] (if s then 7 else 0)).getD C.output none)=some k) :
   ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  obtain ⟨C,op,a,b,hs,hshape,_,_,hcorrect,rank⟩ := search
  let hTrace (s : Bool) := convertRank C hshape s (rank s)
  refine ⟨C,hs,hshape,hcorrect,0,0,Or.inl rfl,?_,?_⟩
  · obtain ⟨d,hin,hrec,hout⟩ := hTrace true
    exact ⟨d,by simpa using hin,by simpa using hrec,hout⟩
  · obtain ⟨d,hin,hrec,hout⟩ := hTrace false
    exact ⟨d,by simpa using hin,by simpa using hrec,hout⟩
