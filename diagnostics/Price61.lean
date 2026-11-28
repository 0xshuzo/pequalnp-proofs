import PEqualNP.Defs

namespace Plane17872

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def mkGate (q : Nat × Nat) : Gate := ⟨.or,[q.1,q.2]⟩
def get (bank : List (List (Fin 24))) (i : Nat) : List (Fin 24) := bank.getD i []
def push (b : List (List (Fin 24))) (q : Nat × Nat) := b ++ [get b q.1 ++ get b q.2]
def sem (x : Fin 24 → Bool) (B : List (List (Fin 24))) := B.map (fun s => s.any x)

theorem read_sem (B : List (List (Fin 24))) (x : Fin 24 → Bool) (i : ℕ) :
    (sem x B).getD i false = (get B i).any x := by
  simp only [sem,get,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases B[i]? <;> rfl

theorem sem_fold (s : List (Nat × Nat)) (x : Fin 24 → Bool) (B : List (List (Fin 24))) :
    (s.map mkGate).foldl (fun w (g : Gate) => w ++ [g.op.eval
      (g.inputs.map fun i => w.getD i false)]) (sem x B) = sem x (s.foldl push B) := by
  induction s generalizing B with
  | nil => rfl
  | cons q t ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih (push B q)]
    congr 1
    simp [push,sem,List.map_append,mkGate,GateOp.eval, List.any_append,← read_sem]

def layout : List (Nat × Nat) := [(0,1), (24,3), (15,16), (26,18), (12,14), (28,20), (13,19), (30,23), (12,18), (32,22), (33,23), (17,21), (35,22), (16,20), (37,21), (38,23), (15,19), (40,20), (41,22), (14,18), (43,19), (44,21), (13,17), (46,18), (47,20), (12,16), (49,17), (50,19), (14,15), (52,17), (53,23), (13,14), (55,16), (56,22), (12,13), (58,15), (59,21)]
def terms : List (Nat × Nat) := [(0,29), (1,31), (2,34), (3,36), (4,39), (5,42), (6,45), (7,48), (8,51), (9,54), (10,57), (11,60)]
def C : Circuit := ⟨layout.map mkGate,0⟩
def raw : List (List (Fin 24)) := (List.finRange 24).map (fun i => [i])
def label (i : Nat) := get (layout.foldl push raw) i

theorem val_eq (x : Fin 24 → Bool) (i : ℕ) :
    PEqualNP.BlindGate.wireValue C 24 x i = (label i).any x := by
  have hh : sem x raw = List.ofFn x := by simp [sem,raw,List.finRange,List.map_ofFn]
  unfold PEqualNP.BlindGate.wireValue Circuit.wires C
  rw [← hh,sem_fold]
  apply read_sem

def link (a b : Fin 12) : Prop :=
   (9 : Fin 13).succAbove a + (0 : Fin 13).succAbove b ∈
      ({0,1,3,9} : Finset (Fin 13))
instance (a b : Fin 12) : Decidable (link a b) := by unfold link; infer_instance

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 10000 in
theorem geometry : ∀ (u v : Fin 24),
    (∃ q ∈ terms, u ∈ label q.1 ∧ v ∈ label q.2) ↔
      ∃ (a b : Fin 12), link a b ∧ u = a.castAdd 12 ∧ v = b.natAdd 12 := by
  decide +kernel

theorem detector (x : Fin 24 → Bool) :
   (terms.any fun q => PEqualNP.BlindGate.wireValue C 24 x q.1 &&
      PEqualNP.BlindGate.wireValue C 24 x q.2) = true ↔
      ∃ a b : Fin 12, link a b ∧ x (a.castAdd 12) = true ∧ x (b.natAdd 12) = true := by
  simp only [val_eq, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨q,hq,⟨u,hu,hxu⟩,v,hv,hxv⟩
    obtain ⟨a,b,h,eu,ev⟩ := (geometry u v).mp ⟨q,hq,hu,hv⟩
    exact ⟨a,b,h,eu ▸ hxu,ev ▸ hxv⟩
  · rintro ⟨a,b,h,ha,hb⟩
    obtain ⟨q,hq,hu,hv⟩ := (geometry (a.castAdd 12) (b.natAdd 12)).mpr ⟨a,b,h,rfl,rfl⟩
    exact ⟨q,hq,⟨_,hu,ha⟩,_,hv,hb⟩

end Plane17872

open Plane17872 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem plane17872Price61 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (24 : ℕ) → Bool) → Prop := fun (x2 : Fin (24 : ℕ) → Bool) => ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (12 : ℕ)), Fin.succAbove (9 : Fin (13 : ℕ)) x3 + Fin.succAbove (0 : Fin (13 : ℕ)) x4 ∈ x1 ∧ x2 (Fin.castAdd (12 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (ℕ × ℕ)) (x5 : ℕ) (x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ x4 ≠ [] ∧ x3.size + (2 : ℕ) * x4.length ≤ (61 : ℕ) ∧ x5 < (24 : ℕ) + x3.size ∧ x6 < (24 : ℕ) + x3.size ∧ (∀ x7 ∈ x4, x7.1 < (24 : ℕ) + x3.size ∧ x7.2 < (24 : ℕ) + x3.size) ∧ ∀ (x7 : Fin (24 : ℕ) → Bool), ((x4.any fun (x8 : ℕ × ℕ) => PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.1 && PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.2) = Bool.true ↔ x2 x7) ∧ (¬x2 x7 → PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x5 = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧ PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x6 = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ)))) := by
  dsimp only
  refine ⟨C,terms,25,27,?_,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  · intro g hg
    change g ∈ layout.map mkGate at hg
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hg
    exact ⟨Or.inr rfl,by decide⟩
  · intro x
    refine ⟨detector x, fun _ => ?_⟩
    have p : label 25 = [0,1,3] := by decide +kernel
    have l : label 27 = [15,16,18] := by decide +kernel
    simp [val_eq,p,l,Bool.or_assoc]
