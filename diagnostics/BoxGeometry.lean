import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_164_box

open PEqualNP.ProofComplexity
abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev C := Clause V
abbrev Occ := Hole → Row
abbrev Box := Row × Row × Hole

def occ (a : Occ) (v : V) : Bool := decide (a v.2 = v.1)
def Bad (a : Occ) (R : C) : Prop := ¬ClauseSat (occ a) R
def upd (a : Occ) (h : Hole) (r : Row) : Occ := fun j => if j=h then r else a j
def Twin (v : V) (e : Row) (a : Occ) : Prop :=
  a v.2 = e ∧ (∀ r : Row, (∃ j, a j=r) ↔ r≠v.1) ∧
    (∀ r : Row, (∃ j, upd a v.2 v.1 j=r) ↔ r≠e)
def inside (s : Box) (a : Occ) : Prop :=
  ∀ j : Hole, s.1=s.2.1 ∨ j≠s.2.2 → a j≠s.1 ∧ a j≠s.2.1
def Hull (s : Box) (R : C) := ∀ a, Bad a R → inside s a
def sel (b : Bool) (a : Occ) (v : V) := if b then upd a v.2 v.1 else a
def missingRow (b : Bool) (v : V) (e : Row) := if b then e else v.1

def fill (v : V) (e q : Row) (j : Hole) : Occ := fun k =>
  if k=v.2 then e else if k=j then q else
    ((List.finRange 5).filter (fun r => r != v.1 && r != e && r != q)).getD
      (((List.finRange 4).filter (fun l => l != v.2 && l != j)).idxOf k) 0

instance (v : V) (e : Row) (a : Occ) : Decidable (Twin v e a) := by unfold Twin; infer_instance
set_option maxHeartbeats 0 in
theorem fillOK : ∀ (v : V) (e q : Row) (j : Hole), v.1≠e → q≠v.1 → q≠e → j≠v.2 →
    Twin v e (fill v e q j) ∧ fill v e q j j=q := by decide +kernel

theorem otherRow : ∀ w e : Row, ∃ q : Row, q≠w ∧ q≠e := by decide +kernel
theorem otherHole : ∀ h g : Hole, ∃ j : Hole, j≠h ∧ j≠g := by decide +kernel

theorem someTwin (v : V) (e : Row) (ne : v.1≠e) : ∃ a, Twin v e a := by
  obtain ⟨q,qw,qe⟩ := otherRow v.1 e
  obtain ⟨j,jh,_⟩ := otherHole v.2 v.2
  exact ⟨_,(fillOK v e q j ne qw qe jh).1⟩

theorem missingSel {v : V} {e : Row} {a : Occ} (ha : Twin v e a) (b : Bool) (r : Row) :
    (∃ j, sel b a v j=r) ↔ r ≠ missingRow b v e := by
  cases b with
  | false => exact ha.2.1 r
  | true => exact ha.2.2 r

theorem boxEverywhere {s : Box} {v : V} {e : Row} (ne : v.1≠e) (b : Bool)
    (contain : ∀ a, Twin v e a → inside s (sel b a v)) :
    ∀ a, inside s a → ∀ j, j≠v.2 → a j≠missingRow b v e := by
  obtain ⟨one,twin⟩ := someTwin v e ne
  by_cases diagonal : s.1=s.2.1
  · have eq : s.1=missingRow b v e := by
      by_contra diff
      obtain ⟨j,hj⟩ := (missingSel twin b s.1).2 diff
      exact (contain one twin j (Or.inl diagonal)).1 hj
    intro a ha j _
    exact eq ▸ (ha j (Or.inl diagonal)).1
  · obtain ⟨k,kv,ks⟩ := otherHole v.2 s.2.2
    have excluded (r : Row) (member : r=s.1 ∨ r=s.2.1) : r=v.1 ∨ r=e := by
      by_contra no
      have rw' : r≠v.1 := fun h => no (Or.inl h)
      have re : r≠e := fun h => no (Or.inr h)
      obtain ⟨t,hk⟩ := fillOK v e r k ne rw' re kv
      have val : sel b (fill v e r k) v k=r := by
        cases b <;> simpa [sel,upd,kv] using hk
      have c := contain _ t k (Or.inr ks)
      rcases member with h|h
      · exact c.1 (val.trans h)
      · exact c.2 (val.trans h)
    have a1 := excluded s.1 (Or.inl rfl)
    have a2 := excluded s.2.1 (Or.inr rfl)
    have both : (s.1=v.1 ∧ s.2.1=e) ∨ (s.1=e ∧ s.2.1=v.1) := by grind
    have hMatch : s.2.2=v.2 := by
      by_contra fail
      have c := contain one twin v.2 (Or.inr (Ne.symm fail))
      have f : sel b one v v.2 = (if b then v.1 else e) := by
        cases b <;> simp [sel,upd,twin.1]
      rcases both with h|h <;> cases b <;> simp_all
    intro a ha j jv
    have c := ha j (Or.inr (fun eq => jv (eq.trans hMatch)))
    rcases both with h|h <;> cases b <;> simp_all [missingRow]

theorem mixBad {a z : Occ} {R : C} (ha : Bad a R) (hz : Bad z R) (h : Hole) :
    Bad (upd a h (z h)) R := by
  rintro ⟨l,hl,sat⟩
  rcases l with ⟨⟨p,j⟩,sg⟩
  change decide (upd a h (z h) j=p)=sg at sat
  by_cases e : j=h
  · subst j
    exact hz ⟨((p,h),sg),hl,by simpa [occ,upd] using sat⟩
  · exact ha ⟨((p,j),sg),hl,by simpa [occ,upd,e] using sat⟩

theorem routeLeft {P N R : C} {v : V} {a : Occ}
    (eq : R=P.erase (v,true) ∪ N.erase (v,false)) (hr : Bad a R)
    (bit : a v.2≠v.1) : Bad a P := by
  rintro ⟨z,hz,yes⟩
  have diff : z≠(v,true) := by
    rintro rfl
    change decide (a v.2=v.1)=true at yes
    exact bit (of_decide_eq_true yes)
  exact hr ⟨z,by rw [eq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨diff,hz⟩),yes⟩

theorem routeRight {P N R : C} {v : V} {a : Occ}
    (eq : R=P.erase (v,true) ∪ N.erase (v,false)) (hr : Bad a R)
    (bit : a v.2=v.1) : Bad a N := by
  rintro ⟨z,hz,yes⟩
  have diff : z≠(v,false) := by
    rintro rfl
    change decide (a v.2=v.1)=false at yes
    simp [bit] at yes
  exact hr ⟨z,by rw [eq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨diff,hz⟩),yes⟩

def Mandatory (v : V) (e : Row) (R : C) :=
  ∀ a, Twin v e a → Bad a R ∧ Bad (upd a v.2 v.1) R

theorem mergeHull {P N R : C} {v : V} {e : Row} (ne : v.1≠e)
    (eq : R=P.erase (v,true) ∪ N.erase (v,false)) (forced : Mandatory v e R)
    {left right : Box} (lh : Hull left P) (rh : Hull right N) : Hull (v.1,e,v.2) R := by
  have lc := boxEverywhere (s:=left) ne false (by
    intro a t
    exact lh a (routeLeft eq (forced a t).1 (fun yes => ne (yes.symm.trans t.1))))
  have rc := boxEverywhere (s:=right) ne true (by
    intro a t
    exact rh _ (routeRight eq (forced a t).2 (by simp [upd])))
  obtain ⟨z,zt⟩ := someTwin v e ne
  intro a hbad j hj
  have diff := hj.resolve_left ne
  have a0 := mixBad hbad (forced z zt).1 v.2
  have a1 := mixBad hbad (forced z zt).2 v.2
  have p := routeLeft eq a0 (by simpa [upd,zt.1] using Ne.symm ne)
  have n := routeRight eq a1 (by simp [upd])
  exact ⟨by simpa [upd,diff,missingRow] using lc _ (lh _ p) j diff,
    by simpa [upd,diff,missingRow] using rc _ (rh _ n) j diff⟩

end PEqualNP.Outside.L_pcx_164_box
