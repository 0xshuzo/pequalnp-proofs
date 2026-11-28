import PEqualNP.Defs
namespace Plane9341.LineCode
open Finset
abbrev V := Fin 21
def rows : List Nat := [1179809,262467,524934,1049868,2585,5170,10340,20680,41360,82720,165440,330880,661760,1323520,549889,1099778,102405,204810,409620,819240,1638480]
def meet (r c : V) := (rows.getD r.val 0).testBit c.val
def points (c : V) := univ.filter (fun r=>meet r c)
def degree (s : Finset V) (r : V) := (s.filter (meet r)).card
set_option maxHeartbeats 1000000 in
theorem lineSize : ∀ c : V, (points c).card=5 := by decide +kernel
set_option maxHeartbeats 1600000 in
theorem oneIntersection : ∀ c d : V, c≠d → ((points c)∩(points d)).card=1 := by decide +kernel
theorem uniquePoint (c d : V) (ne : c≠d) (p q : V) (pc : meet p c=true) (qc : meet q c=true)
    (pd : meet p d=true) (qd : meet q d=true) : p=q := by
  obtain ⟨v,eq⟩:=card_eq_one.mp (oneIntersection c d ne)
  have a : p∈points c ∩ points d := by simp [points,pc,pd]
  have b : q∈points c ∩ points d := by simp [points,qc,qd]
  rw [eq] at a b
  exact (mem_singleton.mp a).trans (mem_singleton.mp b).symm

theorem weightSix (s : Finset V) (even : ∀p, degree s p % 2=0) (ne : s.Nonempty) : 6≤s.card := by
  classical
  obtain ⟨c,hc⟩:=ne
  have next (p : {v // v∈points c}) : ∃d∈s.erase c,meet p.val d=true := by
    have on : meet p.val c=true := (mem_filter.mp p.property).2
    have hm : c∈s.filter (meet p.val) := mem_filter.mpr ⟨hc,on⟩
    have pos := card_pos.mpr (show (s.filter (meet p.val)).Nonempty from ⟨c,hm⟩)
    have parity := even p.val
    unfold degree at parity
    have e:=card_erase_add_one hm
    have nonempty : ((s.filter (meet p.val)).erase c).Nonempty := card_pos.mp (by omega)
    obtain ⟨d,hd⟩:=nonempty
    obtain ⟨diff,h⟩:=mem_erase.mp hd
    exact ⟨d,mem_erase.mpr ⟨diff,(mem_filter.mp h).1⟩,(mem_filter.mp h).2⟩
  choose pick belongs incidence using next
  let f (p : {v // v∈points c}) : {v // v∈s.erase c} := ⟨pick p,belongs p⟩
  have inj : Function.Injective f := by
    intro p q eq
    have same : pick p=pick q := congrArg Subtype.val eq
    apply Subtype.ext
    exact uniquePoint c (pick p) (Ne.symm (mem_erase.mp (belongs p)).1) p.val q.val
      (mem_filter.mp p.property).2 (mem_filter.mp q.property).2 (incidence p) (same.symm ▸ incidence q)
  have bound := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_coe] at bound
  rw [lineSize] at bound
  have e:=card_erase_add_one hc
  omega
end Plane9341.LineCode
