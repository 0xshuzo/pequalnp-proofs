import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29814_aux
open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (xs : List Bool) :=
  gs.foldl (fun t g => t ++ [g.op.eval (g.inputs.map fun j => t.getD j false)]) xs

private theorem firstRaw (gs : List Gate) (b : Bool) (t : List Bool) :
    (run gs (b::t)).getD 0 false = b := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    exact ih (t ++ [g.op.eval (g.inputs.map fun j => (b::t).getD j false)])

private theorem coupled (gs : List Gate)
    (safe : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ 2 ∈ g.inputs)
    (t : List Bool) : ∃ u : List Bool,
    run gs (false::false::true::t) = false::false::true::u ∧
    run gs (true::false::true::t) = true::false::true::u := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    let bit (b : Bool) := g.op.eval (g.inputs.map fun j => (b::false::true::t).getD j false)
    have eq : bit false = bit true := by
      by_cases z : 0 ∈ g.inputs
      · obtain ⟨op,two⟩ := safe g (by simp) z
        have yes (b : Bool) : bit b = true := by
          dsimp only [bit]
          rw [op]
          apply List.any_eq_true.mpr
          exact ⟨true,List.mem_map.mpr ⟨2,two,rfl⟩,rfl⟩
        exact (yes false).trans (yes true).symm
      · apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        cases j with
        | zero => exact (z hj).elim
        | succ j => rfl
    have a : run (g::gs) (false::false::true::t) =
        run gs (false::false::true::(t ++ [bit false])) := rfl
    have b : run (g::gs) (true::false::true::t) =
        run gs (true::false::true::(t ++ [bit true])) := rfl
    rw [a,b,←eq]
    exact ih (fun g' hg' => safe g' (List.mem_cons_of_mem _ hg')) _

private def low (i : Fin 7) := decide (i.val = 2 ∨ i.val = 6)
private def high (i : Fin 7) := decide (i.val = 0 ∨ i.val = 2 ∨ i.val = 6)
private def single (i : Fin 7) := decide (i.val = 0)

end PEqualNP.Outside.L_meta_29814_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29814_aux in
theorem PEqualNP.Outside.L_meta_29814 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 3 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 2 false = true) := by
  rintro ⟨C,i,k,_,_,_,spec,_,unique,op,_,_,_,two,_⟩
  have safe (g : Gate) (hg : g ∈ C.gates) (reads : 0 ∈ g.inputs) :
      g.op = .or ∧ 2 ∈ g.inputs := by
    obtain ⟨j,hj,atJ⟩ := List.getElem_of_mem hg
    have he : C.gates.get ⟨j,hj⟩ = g := atJ
    have same : (⟨j,hj⟩ : Fin C.gates.length) = i := unique _ (by simpa only [he] using reads)
    have hgI : g = C.gates.get i := he.symm.trans (congrArg (fun z : Fin C.gates.length => C.gates.get z) same)
    rw [hgI]
    exact ⟨op,two⟩
  have fa := spec low
  have fb := spec high
  let t : List Bool := [false,false,false,true]
  change (run C.gates (false::false::true::t)).getD C.output false = false at fa
  change (run C.gates (true::false::true::t)).getD C.output false = true at fb
  cases h : C.output with
  | zero =>
    have no := spec single
    change (run C.gates (true::[false,false,false,false,false,false])).getD C.output false = false at no
    rw [h] at no
    exact Bool.noConfusion ((firstRaw C.gates true [false,false,false,false,false,false]).symm.trans no)
  | succ j =>
    obtain ⟨u,ha,hb⟩ := coupled C.gates safe t
    rw [h,ha] at fa
    rw [h,hb] at fb
    change (false::true::u).getD j false = false at fa
    change (false::true::u).getD j false = true at fb
    exact Bool.noConfusion (fa.symm.trans fb)
