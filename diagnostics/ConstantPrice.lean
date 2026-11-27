import PEqualNP.Outside.L_meta_9752

namespace PEqualNP.Outside.L_meta_9750.ConstantPrice
open PEqualNP.Outside.L_meta_9752.Engine

theorem comb_available {R} (d : Nat) (a b : Wire R) {bank}
    (ha : Available true bank a) (hb : Available true bank b)
    (h : Constant a ∨ Constant b) : Available true bank (comb d a b) := by
  unfold comb
  split
  · exact from_constant false h ha hb
  split
  · exact from_constant true h ha hb
  split
  · exact from_constant false (h.imp id inv_constant) ha (avail_inv rfl hb)
  · exact from_constant false (h.imp inv_constant id) (avail_inv rfl ha) hb

theorem restricted_constant {f : Row → Row} {d a : Sig}
    (dom : ∀ r, bit (f r) d = true) (hc : isMaskedConstant d a = true) :
    Constant (restrictRows f (observe a)) := by
  have cases' : masked d a = zero ∨ masked d a = d := by
    simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using hc
  rcases cases' with h | h
  · exact ⟨false,masked_zero dom h⟩
  · exact ⟨true,masked_one dom h⟩

-- A priced restriction with a constant operand supplies the new signed gate for
-- free. This bypasses lookup of the new 2048-bit wire in the projected pool.
theorem constant_price {raw T c} (valid : ValidPool true raw T c)
    (d : Nat) (a b : Sig) (rest : List Sig) (k : Nat)
    (ca : isMaskedConstant c.domain a=true ∨ isMaskedConstant c.domain b=true)
    (ha : availableB true c.domain c.wires a=true)
    (hb : availableB true c.domain c.wires b=true)
    (hs : ∀ w ∈ rest, availableB true c.domain c.wires w=true)
    (price : k+c.paid < c.bound+(bin d a b :: rest).countP (isMaskedConstant c.domain))
    (nd : (bin d a b :: rest).Nodup) :
    Impossible true T k (bin d a b :: rest).toFinset := by
  intro j hj run
  obtain ⟨f,roots,bank,dom,nc,low,reach,pool,_⟩ := valid
  let wires := bin d a b :: rest
  have hz : Available true bank (restrictRows f (observe (bin d a b))) := by
    rw [obs_bin,restrict_comb]
    exact comb_available d _ _ (availableB_sound dom pool ha) (availableB_sound dom pool hb)
      (ca.imp (restricted_constant dom) (restricted_constant dom))
  have supply' : supply true bank ((wires.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hv,rfl⟩ := List.mem_map.mp hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    change w ∈ bin d a b :: rest at hw
    rcases List.mem_cons.mp hw with rfl | h
    · exact hz
    · exact availableB_sound dom pool (hs _ h)
  have bound := projected_bound f (list_run run wires nd rfl) nc reach supply' low
  have count := count_constants (d:=c.domain) dom wires
  change k+c.paid < c.bound+wires.countP (isMaskedConstant c.domain) at price
  omega

end PEqualNP.Outside.L_meta_9750.ConstantPrice
