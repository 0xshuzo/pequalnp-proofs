import Mathlib
import PEqualNP.Outside.L_meta_1674
open PEqualNP.Outside.L_meta_1674
namespace Cheap670
noncomputable def cheapTrivial (l : Lane) (i j op : Nat) : Bool :=
  let ws := l.2.2.2.2.1
  force (ws.getD i 0) fun a => force (ws.getD j 0) fun b =>
  force (zN op a b) fun z => (z == 0) || ws.any (fun w => z == w)
set_option maxRecDepth 8192 in
theorem trivialClosed (c : NodeContext) (i j op : Nat) (ka kb : Bool)
    (cut : cheapTrivial (laneOf c) i j op = true) : checkAt c i j op ka kb = true := by
  let a := contextWire c i
  let b := contextWire c j
  let z := (dbin op a b).1
  have reduced : z.toNat = 0 ∨
      (c.2.2.1.map (fun w : Decor => w.1.toNat)).any (fun v => z.toNat == v) = true := by
    simpa only [cheapTrivial,laneOf,force_eq,getW,zN_full,Bool.or_eq_true,beq_iff_eq,
      a,b,z,contextWire,dbin] using cut
  have skip : (!properB z || c.2.2.1.any (fun v => v.1 == z)) = true := by
    rcases reduced with eq | hit
    · have hz : z = zero := by
        apply BitVec.eq_of_toNat_eq
        exact eq.trans (show (0 : Nat) = zero.toNat from rfl)
      simp [properB,hz]
    · obtain ⟨v,hv,eq⟩ := List.any_eq_true.mp hit
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
      have e : w.1 = z := by
        apply BitVec.eq_of_toNat_eq
        exact (beq_iff_eq.mp eq).symm
      rw [Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩)
  change (if _ then true else if _ then true else if _ then true else _) = true
  rw [show ((!properB z || c.2.2.1.any (fun v => v.1 == z)) = true) from skip]
  simp
end Cheap670
