import Mathlib
import PEqualNP.Outside.L_meta_1674
open PEqualNP.Outside.L_meta_1674
namespace Pair670
noncomputable def forcedPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch)
    (xs : List Lane) (i j op : Nat) : Bool :=
  let a := laneWire b i
  let t := laneWire b j
  force (packedColumn (!u) a) fun ca => force (packedColumn (!u) t) fun cb =>
  force (packedColumn (!u) (packedOp op a t)) fun cz =>
  let run := fun (ka kb : Bool) =>
    let len := 1+(b.2.1-(if ka then 0 else 1)-(if kb then 0 else 1))
    if len>b.1 then true else
      onMarks (fun c => fallbackAt fl c i j op ka kb)
        (fullMarks b.2.2.1 ((takePacked b.2.2.2.2 ca cb ka kb) ||| cz)) xs
  run false false && run true false && run false true && run true true
theorem forcedPair_eq (fl u b xs i j op) :
    forcedPair fl u b xs i j op = batchPair fl u b xs i j op := by
  rcases b with ⟨k,n,r,vs,cov⟩
  simp only [forcedPair,force_eq,batchPair,batchMove]
end Pair670
