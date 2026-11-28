import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10008.Hubs
variable {P L : Type}

def rowOn (D : P → L → Prop) (p : P) := ∃ j, D p j
def colOn (D : P → L → Prop) (j : L) := ∃ p, D p j
def rowHub (I D : P → L → Prop) (p : P) := ∃ j, I p j ∧ colOn D j
def colHub (I D : P → L → Prop) (j : L) := ∃ p, I p j ∧ rowOn D p

def cellColor (I D : P → L → Prop) (c : P → L → Bool) :=
  ∀ p j q l, D p j → D q l → I p l → c p j ≠ c q l

def hubColor (I D : P → L → Prop) (u : P → Bool) (v : L → Bool) :=
  (∀ p j, rowOn D p → colOn D j → I p j → u p ≠ v j) ∧
  (∀ p j, D p j → rowHub I D p → colHub I D j → u p = v j)

private theorem sameThird (a b c : Bool) (ha : a ≠ c) (hb : b ≠ c) : a=b := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem hubCriterion (I D : P → L → Prop) :
    (∃ c, cellColor I D c) ↔ ∃ u v, hubColor I D u v := by
  classical
  constructor
  · rintro ⟨c,ok⟩
    let u (p : P) := if h : rowOn D p then c p (Classical.choose h) else false
    let v (j : L) := if h : colOn D j then c (Classical.choose h) j else false
    have ru (p : P) (j : L) (hit : D p j) (hub : rowHub I D p) : c p j = u p := by
      obtain ⟨l,inc,q,hit'⟩ := hub
      have active : rowOn D p := ⟨j,hit⟩
      dsimp [u]
      rw [dif_pos active]
      exact sameThird _ _ (c q l) (ok p j q l hit hit' inc)
        (ok p _ q l (Classical.choose_spec active) hit' inc)
    have cv (p : P) (j : L) (hit : D p j) (hub : colHub I D j) : c p j = v j := by
      obtain ⟨q,inc,l,hit'⟩ := hub
      have active : colOn D j := ⟨p,hit⟩
      dsimp [v]
      rw [dif_pos active]
      apply sameThird _ _ (c q l)
      · exact fun e => ok q l p j hit' hit inc e.symm
      · exact fun e => ok q l _ j hit' (Classical.choose_spec active) inc e.symm
    refine ⟨u,v,?_,?_⟩
    · intro p j ra ca inc
      dsimp [u,v]
      rw [dif_pos ra,dif_pos ca]
      exact ok p _ _ j (Classical.choose_spec ra) (Classical.choose_spec ca) inc
    · intro p j hit rh ch
      exact (ru p j hit rh).symm.trans (cv p j hit ch)
  · rintro ⟨u,v,diff,eq⟩
    let c (p : P) (j : L) := if rowHub I D p then u p else v j
    have onRow (p : P) (j : L) (h : rowHub I D p) : c p j = u p := by simp [c,h]
    have onCol (p : P) (j : L) (hit : D p j) (h : colHub I D j) : c p j = v j := by
      by_cases rh : rowHub I D p
      · rw [onRow p j rh,eq p j hit rh h]
      · simp [c,rh]
    refine ⟨c,?_⟩
    intro p j q l hp hq inc
    have rh : rowHub I D p := ⟨l,inc,q,hq⟩
    have ch : colHub I D l := ⟨p,inc,j,hp⟩
    rw [onRow p j rh,onCol q l hq ch]
    exact diff p l ⟨j,hp⟩ ⟨q,hq⟩ inc

def twoBoxes (I D : P → L → Prop) := ∃ (A : Bool → P → Prop) (B : Bool → L → Prop),
    (∀ h p j, A h p → B h j → ¬I p j) ∧ (∀ p j, D p j → ∃ h, A h p ∧ B h j)

theorem physicalTwo (I D : P → L → Prop) :
    twoBoxes I D ↔ ∃ u v, hubColor I D u v := by
  rw [←hubCriterion I D]
  classical
  constructor
  · rintro ⟨A,B,safe,cov⟩
    let c (p : P) (j : L) := if h : D p j then (cov p j h).choose else false
    have carries (p : P) (j : L) (h : D p j) : A (c p j) p ∧ B (c p j) j := by
      dsimp [c]
      rw [dif_pos h]
      exact (cov p j h).choose_spec
    refine ⟨c,?_⟩
    intro p j q l hp hq inc e
    exact safe (c p j) p l (carries p j hp).1 (e.symm ▸ (carries q l hq).2) inc
  · rintro ⟨c,h⟩
    refine ⟨fun z p => ∃ j, D p j ∧ c p j = z,
      fun z j => ∃ p, D p j ∧ c p j = z,?_,?_⟩
    · rintro z p j ⟨l,pl,el⟩ ⟨q,qj,eq⟩ inc
      exact h p l q j pl qj inc (el.trans eq.symm)
    · intro p j hit
      exact ⟨c p j,⟨j,hit,rfl⟩,⟨p,hit,rfl⟩⟩
end PEqualNP.Outside.L_meta_10008.Hubs
