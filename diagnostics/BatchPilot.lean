import Mathlib
import PEqualNP.Outside.L_meta_1674
open PEqualNP.Outside.L_meta_1674
namespace Batch670
noncomputable def forcePackedList {β : Type} (xs : List PackedSig) : (List PackedSig → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f =>
    force p.1 fun a => force p.2 fun b => ih fun ps => f ((a,b)::ps)) xs
theorem forcePackedList_eq {β : Type} (xs : List PackedSig) (f : List PackedSig → β) :
    forcePackedList xs f = f xs := by
  induction xs generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change force p.1 (fun a => force p.2 fun b => forcePackedList ps fun qs => f ((a,b)::qs)) = _
    rw [force_eq,force_eq,ih]
noncomputable def forceBatch {β : Type} (b : Batch) (f : Batch → β) : β :=
  force b.2.2.1 fun r => forcePackedList b.2.2.2.1 fun cols =>
  force b.2.2.2.2.1 fun a => force b.2.2.2.2.2.1 fun y => force b.2.2.2.2.2.2 fun z =>
  f (b.1,b.2.1,r,cols,a,y,z)
theorem forceBatch_eq {β : Type} (b : Batch) (f : Batch → β) : forceBatch b f = f b := by
  simp only [forceBatch,force_eq,forcePackedList_eq]
end Batch670
