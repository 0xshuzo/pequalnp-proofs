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
abbrev V := Fin 31
abbrev Box := Finset V × Finset V
def masks : List Nat := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def mask (i : V) := masks.getD i.val 0
def mark (i j : V) := (mask i).testBit j.val
def legal (old : List Box) := ∀ r ∈ old, ∀ p ∈ r.1, ∀ j ∈ r.2, mark p j = false
def hit (old : List Box) (p j : V) := ∃ r ∈ old, p ∈ r.1 ∧ j ∈ r.2
def residual (old : List Box) (p j : V) := mark p j = false ∧ ¬hit old p j
def full (old : List Box) := ∀ p j, mark p j = false → hit old p j
def inc (p j : V) := mark p j = true

private theorem shortBank (old : List Box) (fit : old.length ≤ 15) (good : legal old) (done : full old) :
    ∃ core : List Box, core.length ≤ 15 ∧ legal core ∧ twoBoxes inc (residual core) := by
  refine ⟨old,fit,good,fun _ _ => False,fun _ _ => False,?_,?_⟩
  · intro _ _ _ h
    exact False.elim h
  · intro p j h
    exact False.elim (h.2 (done p j h.1))

theorem physicalReduction :
    (∃ bank : List Box, bank.length ≤ 17 ∧ legal bank ∧ full bank) ↔
    ∃ core : List Box, core.length ≤ 15 ∧ legal core ∧
      ∃ u v, hubColor inc (residual core) u v := by
  classical
  constructor
  · rintro ⟨bank,budget,good,done⟩
    suffices e : ∃ core : List Box, core.length ≤ 15 ∧ legal core ∧ twoBoxes inc (residual core) by
      obtain ⟨core,len,safe,rest⟩ := e
      exact ⟨core,len,safe,(physicalTwo inc (residual core)).mp rest⟩
    cases bank with
    | nil => exact shortBank [] (by decide) good done
    | cons a tail =>
      cases tail with
      | nil => exact shortBank [a] (by simp) good done
      | cons b core =>
        have hlen : core.length ≤ 15 := by simp only [List.length_cons] at budget; omega
        refine ⟨core,hlen,?_,fun z p => if z then p∈a.1 else p∈b.1,
          fun z j => if z then j∈a.2 else j∈b.2,?_,?_⟩
        · intro r hr
          exact good r (by simp [hr])
        · intro z p j hp hj
          cases z with
          | false =>
            have h := good b (by simp) p (by simpa using hp) j (by simpa using hj)
            exact fun e => by simp [inc,h] at e
          | true =>
            have h := good a (by simp) p (by simpa using hp) j (by simpa using hj)
            exact fun e => by simp [inc,h] at e
        · intro p j miss
          obtain ⟨r,rs,hp,hj⟩ := done p j miss.1
          rcases List.mem_cons.mp rs with e|rs
          · subst r; exact ⟨true,by simpa using hp,by simpa using hj⟩
          · rcases List.mem_cons.mp rs with e|rs
            · subst r; exact ⟨false,by simpa using hp,by simpa using hj⟩
            · exact False.elim (miss.2 ⟨r,rs,hp,hj⟩)
  · rintro ⟨core,len,safe,hub⟩
    obtain ⟨A,B,pure,rest⟩ := (physicalTwo inc (residual core)).mpr hub
    let extra (z : Bool) : Box := (Finset.univ.filter (A z),Finset.univ.filter (B z))
    refine ⟨extra true :: extra false :: core,by simp only [List.length_cons]; omega,?_,?_⟩
    · intro r hr
      have gg (z : Bool) : ∀ p ∈ (extra z).1, ∀ j ∈ (extra z).2, mark p j = false := by
        intro p hp j hj
        have h := pure z p j (by simpa [extra] using hp) (by simpa [extra] using hj)
        cases e : mark p j with
        | false => rfl
        | true => exact False.elim (h e)
      rcases List.mem_cons.mp hr with e|hh
      · exact e.symm ▸ gg true
      · rcases List.mem_cons.mp hh with e|hhh
        · exact e.symm ▸ gg false
        · exact safe r hhh
    · intro p j blank
      by_cases has : hit core p j
      · obtain ⟨r,rm,pr,jr⟩ := has
        exact ⟨r,by simp [rm],pr,jr⟩
      · obtain ⟨z,pa,jb⟩ := rest p j ⟨blank,has⟩
        have q : extra z ∈ extra true :: extra false :: core := by cases z <;> simp
        exact ⟨extra z,q,by simpa [extra] using pa,by simpa [extra] using jb⟩

theorem forbiddenPath {I D : P → L → Prop} (h : twoBoxes I D) {p q : P} {l m : L}
    (bad : D p l) (activeRow : rowOn D q) (activeCol : colOn D m)
    (first : I p m) (middle : I q m) (last : I q l) : False := by
  obtain ⟨u,v,opp,eq⟩ := (physicalTwo I D).mp h
  have ra : rowOn D p := ⟨l,bad⟩
  have ca : colOn D l := ⟨p,bad⟩
  have same := eq p l bad ⟨m,first,activeCol⟩ ⟨q,last,activeRow⟩
  have mid := sameThird _ _ (v m) (opp p m ra activeCol first) (opp q m activeRow activeCol middle)
  exact (opp q l activeRow ca last) (mid.symm.trans same)

end PEqualNP.Outside.L_meta_10008.Hubs
