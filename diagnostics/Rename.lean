import Mathlib
import PEqualNP.Defs

namespace Rename4801

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.MetaComplexity.NestedCover

def move {n : ℕ} (e : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (e ⟨w,h⟩).val else w

def gate {n : ℕ} (e : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (move e)⟩

def run {α : Type} (d : α) (f : GateOp → List α → α) (gs : List Gate) (xs : List α) : List α :=
  gs.foldl (fun s g => s ++ [f g.op (g.inputs.map fun i => s.getD i d)]) xs

private theorem transfer {α : Type} {n : ℕ} (e : Equiv.Perm (Fin n))
    (d : α) (f : GateOp → List α → α) (gs : List Gate) (old new : List α)
    (large : n ≤ old.length) (length : new.length=old.length)
    (matches : ∀ w, new.getD (move e w) d = old.getD w d) :
    ∀ w, (run d f (gs.map (gate e)) new).getD (move e w) d = (run d f gs old).getD w d := by
  induction gs generalizing old new with
  | nil => exact matches
  | cons g gs ih =>
    let value := f g.op (g.inputs.map fun i => old.getD i d)
    have value' : f (gate e g).op ((gate e g).inputs.map fun i => new.getD i d) = value := by
      change f g.op ((g.inputs.map (move e)).map fun i => new.getD i d) = _
      simp only [List.map_map,Function.comp_def,matches,value]
    change ∀ w,
      (run d f (gs.map (gate e)) (new ++ [f (gate e g).op ((gate e g).inputs.map fun i => new.getD i d)])).getD (move e w) d =
        (run d f gs (old ++ [value])).getD w d
    rw [value']
    apply ih (old ++ [value]) (new ++ [value]) (by simp; omega) (by simp [length])
    intro w
    by_cases hw : w < old.length
    · have mh : move e w < new.length := by
        by_cases hr : w < n
        · have eh := (e ⟨w,hr⟩).isLt
          simp only [move,hr,↓reduceDIte]
          omega
        · simpa [move,hr,length] using hw
      rw [List.getD_append _ _ _ _ mh,List.getD_append _ _ _ _ hw,matches]
    · have hr : ¬w<n := by omega
      rw [show move e w = w by simp [move,hr]]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),length]

def vecOp (op : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match op with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 1) [[0,0]]
  | _ => []

private theorem vecRun (n : ℕ) (C : Circuit) (a b : ℕ) :
    readVectors C n [a,b] 1 = run [] vecOp C.gates ((List.range n).map (leafVectors [a,b] 1)) := by
  rfl

theorem rename : ∀ (n : ℕ) (C : Circuit) (e : Equiv.Perm (Fin n)),
      IsAO2 n C → ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧
        (∀ z : Fin n → Bool, D.eval (List.ofFn z) = C.eval (List.ofFn (fun i => z (e i)))) ∧
        ∀ a b : Fin n, readsAtMost D n [(e a).val,(e b).val] 1 = readsAtMost C n [a.val,b.val] 1 := by
  intro n C e ao
  let D : Circuit := ⟨C.gates.map (gate e),move e C.output⟩
  have len : D.gates.length = C.gates.length := List.length_map
  have moved (j : ℕ) (hj : j < C.gates.length) : gateAt D j = gate e (gateAt C j) := by
    change (C.gates.map (gate e)).getD j _ = gate e (C.gates.getD j _)
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getD_eq_getElem _ _ hj,List.getElem_map]
  have dao : IsAO2 n D := by
    refine ⟨?_,?_,?_⟩
    · intro g h
      obtain ⟨h0,inC,rfl⟩ := List.mem_map.mp h
      exact ao.1 h0 inC
    · intro j hj i hi
      have hj' : j<C.gates.length := by simpa only [len] using hj
      rw [moved j hj'] at hi
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hi
      have bound := ao.2.1 j hj' u hu
      by_cases raw : u<n
      · have h := (e ⟨u,raw⟩).isLt
        simp only [move,raw,↓reduceDIte]
        omega
      · simpa [move,raw] using bound
    · intro g hg
      obtain ⟨h0,inC,rfl⟩ := List.mem_map.mp hg
      simpa only [gate,List.length_map] using ao.2.2 h0 inC
  refine ⟨D,dao,len,?_,?_⟩
  · intro z
    apply transfer e false GateOp.eval C.gates (List.ofFn fun i => z (e i)) (List.ofFn z)
      (by simp) (by simp)
    intro w
    by_cases h : w<n
    · have m : move e w < n := by simpa [move,h] using (e ⟨w,h⟩).isLt
      rw [List.getD_eq_getElem _ _ (by simpa using m),List.getD_eq_getElem _ _ (by simpa using h)]
      simp [move,h]
    · rw [show move e w = w by simp [move,h]]
      rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
  · intro a b
    have raw (i : Fin n) : leafVectors [(e a).val,(e b).val] 1 (e i).val =
        leafVectors [a.val,b.val] 1 i.val := by
      simp [leafVectors, Fin.val_inj]
    let old := (List.range n).map (leafVectors [a.val,b.val] 1)
    let new := (List.range n).map (leafVectors [(e a).val,(e b).val] 1)
    have match0 (w : ℕ) : new.getD (move e w) [] = old.getD w [] := by
      by_cases h : w < n
      · have m : move e w < n := by simpa [move,h] using (e ⟨w,h⟩).isLt
        rw [List.getD_eq_getElem _ _ (by simpa [new] using m),
          List.getD_eq_getElem _ _ (by simpa [old] using h)]
        simpa [new,old,move,h] using raw ⟨w,h⟩
      · rw [show move e w = w by simp [move,h]]
        rw [List.getD_eq_default _ _ (by simp [new]; omega),List.getD_eq_default _ _ (by simp [old]; omega)]
    unfold readsAtMost
    rw [vecRun,vecRun]
    have value := transfer e [] vecOp C.gates old new (by simp [old]) (by simp [old,new]) match0 C.output
    exact congrArg (fun vs : List (List ℕ) => vs.any fun v => v.all fun k => decide (k ≤ 1)) value

end Rename4801
