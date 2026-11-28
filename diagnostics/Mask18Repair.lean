import PEqualNP.Defs

namespace TinyProjection
abbrev Sig := BitVec 512
abbrev Row := Fin 512
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
abbrev Probe32 := BitVec 32
def view32 (w : Probe32) (i : Fin 32) := w.getLsbD i.val
def sample32 (rows : Fin 32 → Row) (v : Sig) : Probe32 :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (rows i) v))).cast (List.length_ofFn)
theorem sample32_read (rows : Fin 32 → Row) (v : Sig) (i : Fin 32) :
    view32 (sample32 rows v) i = bit (rows i) v := by
  simp only [sample32,view32,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def normalLow (w : Probe32) := (w &&& 262143) ||| (if w.getLsbD 0 then 4294705152 else 0)
def lowRows (r : Fin 32 → Row) (i : Fin 32) := if i.val < 18 then r i else r 0

theorem maskLow : ∀ i : Fin 32, (262143 : Probe32).getLsbD i.val = decide (i.val < 18) := by decide +kernel
theorem maskHigh : ∀ i : Fin 32, (4294705152 : Probe32).getLsbD i.val = decide (18 ≤ i.val) := by decide +kernel

theorem normalLow_read (r : Fin 32 → Row) (v : Sig) :
    normalLow (sample32 r v) = sample32 (lowRows r) v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin 32 := ⟨i,hi⟩
  have e := sample32_read r v j
  have z := sample32_read r v 0
  have o := sample32_read (lowRows r) v j
  change (sample32 r v).getLsbD i = bit (r j) v at e
  change (sample32 r v).getLsbD 0 = bit (r 0) v at z
  change (sample32 (lowRows r) v).getLsbD i = bit (lowRows r j) v at o
  rw [o]
  have m : (262143 : Probe32).getLsbD i = decide (i < 18) := maskLow j
  have n : (4294705152 : Probe32).getLsbD i = decide (18 ≤ i) := maskHigh j
  have zs : ∀ t : Fin 32, (0 : Probe32).getLsbD t.val = false := by decide +kernel
  have zi : (0 : Probe32).getLsbD i = false := zs j
  unfold normalLow
  rw [BitVec.getLsbD_or,BitVec.getLsbD_and,m]
  by_cases h : i < 18
  · have hn : ¬ 18 ≤ i := by omega
    rw [show lowRows r j = r j from if_pos h, ← e]
    cases hb : (sample32 r v).getLsbD 0 with
    | false =>
      change ((sample32 r v).getLsbD i && decide (i < 18) || (0 : Probe32).getLsbD i) = _
      rw [zi]
      simp only [h,decide_true,Bool.and_true,Bool.or_false]
    | true =>
      change ((sample32 r v).getLsbD i && decide (i < 18) || (4294705152 : Probe32).getLsbD i) = _
      rw [n]
      simp only [h,hn,decide_true,decide_false,Bool.and_true,Bool.or_false]
  · have hn : 18 ≤ i := by omega
    rw [show lowRows r j = r 0 from if_neg h, ← z]
    cases hb : (sample32 r v).getLsbD 0 with
    | false =>
      change ((sample32 r v).getLsbD i && decide (i < 18) || (0 : Probe32).getLsbD i) = false
      rw [zi]
      simp only [h,decide_false,Bool.and_false,Bool.or_false]
    | true =>
      change ((sample32 r v).getLsbD i && decide (i < 18) || (4294705152 : Probe32).getLsbD i) = true
      rw [n]
      simp only [h,hn,decide_false,decide_true,Bool.and_false,Bool.or_true]

end TinyProjection
