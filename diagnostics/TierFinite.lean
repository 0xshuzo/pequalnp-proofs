import Mathlib
namespace PEqualNP.Outside.L_meta_11028
namespace Tier

def firstSlot (code : Nat) := code &&& 15
def secondSlot (code : Nat) := (code >>> 4) &&& 15
def outputSlot (code : Nat) := (code >>> 8) &&& 15

def relation (v : Nat→Nat) (c : Nat) : Prop :=
  if outputSlot c=0 then v (firstSlot c)≠v (secondSlot c) else
    v (firstSlot c)=v (secondSlot c) → v (outputSlot c-1)≤v (firstSlot c)

def violates (p : List Nat) (c : Nat) : Bool :=
  let a := p.getD (firstSlot c) 0
  let b := p.getD (secondSlot c) 0
  let d := outputSlot c
  decide (firstSlot c<p.length ∧ secondSlot c<p.length) &&
    if d=0 then a==b else
      decide (d-1<p.length) && (a==b) && decide (a<p.getD (d-1) 0)

theorem violates_sound {p c v} (agrees : ∀ i<p.length, p.getD i 0=v i)
    (r : relation v c) : violates p c≠true := by
  intro bad
  simp only [violates,Bool.and_eq_true,decide_eq_true_eq] at bad
  have ha := agrees (firstSlot c) bad.1.1
  have hb := agrees (secondSlot c) bad.1.2
  by_cases h : outputSlot c=0
  · simp only [relation,h,ite_true] at r
    have eq : p.getD (firstSlot c) 0=p.getD (secondSlot c) 0 := by
      simpa only [h,ite_true,beq_iff_eq] using bad.2
    exact r (ha.symm.trans (eq.trans hb))
  · simp only [relation,h,ite_false] at r
    have bx := bad.2
    simp only [h,ite_false,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at bx
    have hc := agrees (outputSlot c-1) bx.1.1
    have low := r (ha.symm.trans (bx.1.2.trans hb))
    omega

def exhaustive (levels : Nat) (rules : List Nat) : Nat → List Nat → Bool
  | 0,ps => rules.any (violates ps)
  | n+1,ps => rules.any (violates ps) ||
      (List.range levels).all fun j => exhaustive levels rules n (ps++[j])

theorem append_agree {p : List Nat} {v : Nat→Nat} (h : ∀ i<p.length, p.getD i 0=v i) :
    ∀ i<(p++[v p.length]).length, (p++[v p.length]).getD i 0=v i := by
  intro i hi
  by_cases e : i<p.length
  · have eq : (p++[v p.length]).getD i 0=p.getD i 0 := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_append,e]
    exact eq.trans (h i e)
  · have x : i=p.length := by simp at hi; omega
    subst i
    simp [List.getD_eq_getElem?_getD,List.getElem?_append]

theorem exhaustive_sound {levels rules n ps v} (reject : exhaustive levels rules n ps=true)
    (small : ∀ i, v i<levels) (model : ∀ c∈rules, relation v c)
    (agrees : ∀ i<ps.length, ps.getD i 0=v i) : False := by
  have noBad (p : List Nat) (h : ∀ i<p.length, p.getD i 0=v i) : rules.any (violates p)≠true := by
    intro e
    obtain ⟨c,hc,b⟩ := List.any_eq_true.mp e
    exact violates_sound h (model c hc) b
  induction n generalizing ps with
  | zero => exact noBad ps agrees reject
  | succ n ih =>
    have casesOf : rules.any (violates ps)=true ∨ (List.range levels).all (fun j => exhaustive levels rules n (ps++[j]))=true := by
      simpa only [exhaustive,Bool.or_eq_true] using reject
    have r : (List.range levels).all (fun j => exhaustive levels rules n (ps++[j]))=true :=
      casesOf.resolve_left (noBad ps agrees)
    exact ih (List.all_eq_true.mp r (v ps.length) (List.mem_range.mpr (small _))) (append_agree agrees)

end Tier

end PEqualNP.Outside.L_meta_11028
