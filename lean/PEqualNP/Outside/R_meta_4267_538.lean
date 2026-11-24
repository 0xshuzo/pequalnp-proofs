import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- On x₂ = false the modified circuit must retain eight gates for the six-cycle.
-- At the singleton x₂ the output changes, so some edited gate is separate
-- from the selected OR readers that already see a true input.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
theorem PEqualNP.Outside.R_meta_4267_538
    (cycleBudget : ∀ (D : Circuit) (o : ℕ), FanInTwo D →
    (∀ x : Fin 6 → Bool, (D.wires [true,x 0,x 1,false,x 3,x 5,x 2,x 4]).getD o false = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0))) →
    8 + (D.gates.filter (fun h : Gate => h.inputs.contains 0 || h.inputs.contains 3)).length ≤ D.size)
    (changed : ∀ (C D : Circuit) (a b : ℕ), FanInTwo C → List.Forall₂ (fun g h : Gate => g.op = h.op ∧
      List.Forall₂ (fun i j => j = i+1 ∨ j=0 ∧ (i=a ∨ i=b)) g.inputs h.inputs) C.gates D.gates →
    (C.wires [false,false,true,false,false,false,false]).getD C.output false ≠
      (D.wires [true,false,false,true,false,false,false,false]).getD (C.output+1) false →
    0 < ((C.gates.zip D.gates).filter (fun z : Gate × Gate =>
       !(z.1.op.eval [true,false] && z.1.inputs.contains 2) && z.2.inputs.contains 0)).length)
    (tight : ∀ (f : (Fin 7 → Bool) → Bool),
    f = (fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List ℕ).any (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10)))) →
    ∀ (C D : Circuit) (a b : ℕ), FanInTwo C → C.size=11 → circuitFun 7 C=f →
    List.Forall₂ (fun g h : Gate => g.op = h.op ∧
      List.Forall₂ (fun i j => j = i+1 ∨ j=0 ∧ (i=a ∨ i=b)) g.inputs h.inputs) C.gates D.gates →
    (∀ x : Fin 7 → Bool, (D.wires (true :: List.ofFn x)).getD (C.output+1) false = (f x || x 2)) →
    (C.gates.filter (fun g : Gate => g.op.eval [true,false] && g.inputs.contains 2)).length = 2 →
    ((C.gates.zip D.gates).filter (fun z : Gate × Gate =>
       !(z.1.op.eval [true,false] && z.1.inputs.contains 2) && z.2.inputs.contains 0)).length = 1 →
    (D.gates.filter (fun h : Gate => h.inputs.contains 0 || h.inputs.contains 3)).length = 3 → False) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (∀ (x11 : Fin (7 : ℕ) → Bool), x11 (2 : Fin (7 : ℕ)) = Bool.false → x1 x11 = Bool.false → ¬∀ x14 ∈ x2.gates, (2 : ℕ) ∈ x14.inputs → x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ (x17 : Fin (7 : ℕ)), x17 ≠ (2 : Fin (7 : ℕ)) ∧ ↑x17 ∈ x14.inputs ∧ x11 x17 = Bool.true) → (List.filter (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => x12.op.eval [Bool.true, Bool.false] && x12.inputs.contains (2 : ℕ)) x2.gates).length < (2 : ℕ) := by
  intro f C D a b fan sz base edits modified _
  let sel := (fun g : Gate => g.op.eval [true,false] && g.inputs.contains 2)
  let exc := (fun z : Gate × Gate =>
       !(z.1.op.eval [true,false] && z.1.inputs.contains 2) && z.2.inputs.contains 0)
  let touch := (fun h : Gate => h.inputs.contains 0 || h.inputs.contains 3)
  let R (g h : Gate) := g.op = h.op ∧
    List.Forall₂ (fun i j => j=i+1 ∨ j=0 ∧ (i=a ∨ i=b)) g.inputs h.inputs
  let ok (g : Gate) := g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  have port {l m : List ℕ} (h : List.Forall₂ (fun i j => j=i+1 ∨ j=0 ∧ (i=a ∨ i=b)) l m) :
      l.length = m.length ∧ (2∈l → 0∈m ∨ 3∈m) := by
    induction h with
    | nil => simp
    | @cons i j l m h r ih =>
      refine ⟨by simp [ih.1],?_⟩
      intro hin
      rcases List.mem_cons.mp hin with e|e
      · rcases h with h|h
        · right; exact List.mem_cons.mpr (Or.inl (by omega))
        · left; exact List.mem_cons.mpr (Or.inl h.1.symm)
      · rcases ih.2 e with e|e
        · left; exact List.mem_cons_of_mem _ e
        · right; exact List.mem_cons_of_mem _ e
  have sum {gs hs : List Gate} (r : List.Forall₂ R gs hs) :
      gs.length=hs.length ∧ ((∀ g∈gs, ok g) → ∀ h∈hs, ok h) ∧
      (gs.filter sel).length + ((gs.zip hs).filter exc).length ≤ (hs.filter touch).length := by
    induction r with
    | nil => simp
    | @cons g h gs hs rel rs ih =>
      obtain ⟨hlen,hfan,hcost⟩ := ih
      obtain ⟨hop,hins⟩ := rel
      obtain ⟨len,wp⟩ := port hins
      refine ⟨by simp [hlen],?_,?_⟩
      · intro okAll q hq
        rcases List.mem_cons.mp hq with rfl|hq
        · obtain ⟨ho,hi⟩ := okAll g List.mem_cons_self
          exact ⟨hop ▸ ho,len ▸ hi⟩
        · exact hfan (fun q hq => okAll q (List.mem_cons_of_mem _ hq)) _ hq
      · have use (s : sel g = true) : touch h = true := by
          have info : g.op.eval [true,false]=true ∧ 2∈g.inputs := by simpa [sel] using s
          have hg := info.2
          rcases wp hg with p|p <;> simp [touch,p]
        have idx : exc (g,h) = (!sel g && h.inputs.contains 0) := rfl
        have use0 (s : h.inputs.contains 0 = true) : touch h = true := by
          change (h.inputs.contains 0 || h.inputs.contains 3) = true
          rw [s]; rfl
        cases s : sel g <;> cases p : h.inputs.contains 0 <;> cases z : touch h <;>
          simp_all [List.filter_cons,idx] <;> omega
  obtain ⟨len,fd,charged⟩ := sum (show List.Forall₂ R C.gates D.gates from edits)
  have hd : FanInTwo D := fd fan
  have sizeD : D.size=C.size := len.symm
  let lift (x : Fin 6 → Bool) : Fin 7 → Bool := ![x 0,x 1,false,x 3,x 5,x 2,x 4]
  have geometry : ∀ x : Fin 6 → Bool, (f (lift x) || (lift x) 2) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)) := by
    dsimp only [f,lift]; decide +kernel
  have cut := cycleBudget D (C.output+1) hd (fun x =>
    (show (D.wires [true,x 0,x 1,false,x 3,x 5,x 2,x 4]).getD (C.output+1) false = _ from modified (lift x)).trans (geometry x))
  have e := congrFun base (![false,false,true,false,false,false,false] : Fin 7 → Bool)
  have g := modified (![false,false,true,false,false,false,false] : Fin 7 → Bool)
  change (C.wires [false,false,true,false,false,false,false]).getD C.output false = false at e
  change (D.wires [true,false,false,true,false,false,false,false]).getD (C.output+1) false = true at g
  have pos := changed C D a b fan edits (by rw [e,g]; decide)
  change 0 < ((C.gates.zip D.gates).filter exc).length at pos
  change 8 + (D.gates.filter touch).length ≤ D.size at cut
  change (C.gates.filter sel).length < 2
  by_contra tooMany
  have countSel : (C.gates.filter sel).length = 2 := by omega
  have countExc : ((C.gates.zip D.gates).filter exc).length = 1 := by omega
  have countAll : (D.gates.filter touch).length = 3 := by omega
  exact tight f rfl C D a b fan sz base edits modified countSel countExc countAll
