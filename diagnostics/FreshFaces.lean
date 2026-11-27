import PEqualNP.Outside.L_meta_26680

namespace PEqualNP.Outside.L_meta_9822.FreshFaces

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_26680_aux

def edgeWord (ws : List Nat) : Nat :=
  ([(1, 2), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (6, 9), (6, 8), (5, 8)] : List (Nat × Nat)).foldl (fun a e => a ||| (ws.getD e.1 0 &&& ws.getD e.2 0)) 0

def rawMap (indices : List Nat) : List Nat :=
  indices.map (fun i => xs256.getD i 0)

theorem physical {ws : List Nat} {k : Nat} (h : Lower true mask256 ws (edgeWord ws) k)
    (C : Circuit)
    (fan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (correct : (execN C.gates ws).getD C.output 0 &&& mask256 = edgeWord ws &&& mask256) :
    k ≤ C.gates.countP (fun g => !isNotGate g) := by
  have sup : ∀ v ∈ ws, Avail true mask256 ws v := fun v hv => Or.inr (Or.inl ⟨v,hv,rfl⟩)
  obtain ⟨p,bank,hp,hr,hs⟩ := execN_reach true C.gates ws fan (fun h => Bool.noConfusion h) 0 ws ws rfl sup
  have avail : Avail true mask256 bank ((execN C.gates ws).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates ws).length
    · exact hs _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Or.inl (Or.inl (by simp))
  have lb := h p bank hr (avail_of_eq correct avail)
  omega

def raw458 : List Nat := rawMap [7, 7, 3, 4, 0, 2, 1, 8, 6, 5]

theorem field458 : Lower true mask256 raw458 (edgeWord raw458) 11 :=
  lower_iso (d1 := dom_255) (roots1 := roots_255) (T1 := goal_255) []
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) lowS_255

def raw490 : List Nat := rawMap [4, 3, 7, 7, 0, 6, 8, 1, 2, 5]

theorem field490 : Lower true mask256 raw490 (edgeWord raw490) 11 :=
  lower_iso (d1 := dom_255) (roots1 := roots_255) (T1 := goal_255) []
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) lowS_255

end PEqualNP.Outside.L_meta_9822.FreshFaces
