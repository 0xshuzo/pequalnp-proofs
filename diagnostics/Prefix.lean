import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17603
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover
open PEqualNP.MetaComplexity.NestedCover
private abbrev I := Fin 13
private def valid (s : List ℕ) := s=[0,1] ∨ s=[13,14]
private def anc (s : List ℕ) := if s=[0,1] then 13 else 1
private def header (s : List ℕ) (C : Circuit) : Circuit :=
  ⟨⟨.or,s⟩ :: ⟨.and,[26,anc s]⟩ :: C.gates,C.output⟩
private def augmented (s : List ℕ) (X Y : Finset I) :=
  let x := incidenceInput X Y
  x ++ [s.any (fun i => x.getD i false)]
private def test (C : Circuit) (s : List ℕ) (X Y : Finset I) (b : Bool) :=
  C.eval (augmented s X Y ++ [b])
private def bonus (s : List ℕ) (X Y : Finset I) : Bool :=
  GateOp.and.eval ([26,anc s].map fun i => (augmented s X Y).getD i false)
private theorem pref (C : Circuit) (s : List ℕ) (X Y : Finset I) :
    (header s C).eval (incidenceInput X Y)=test C s X Y (bonus s X Y) := by
  let x := incidenceInput X Y
  have hor : GateOp.or.eval (s.map fun i => x.getD i false)=s.any (fun i => x.getD i false) := by
    simp [GateOp.eval,List.any_map,Function.comp_def]
  change C.eval (((x ++ [GateOp.or.eval (s.map fun i => x.getD i false)]) ++
    [GateOp.and.eval ([26,anc s].map fun i => (x ++ [GateOp.or.eval (s.map fun i => x.getD i false)]).getD i false)]))=_
  rw [hor]
  rfl
private theorem bools (a b c : Bool) :
    GateOp.and.eval [[a,b].any id,c]=((a || b) && c) := by cases a <;> cases b <;> cases c <;> rfl
private theorem pointBonus (X Y : Finset I) :
    bonus [0,1] X Y=((decide ((0:I)∈X) || decide ((1:I)∈X)) && decide ((0:I)∈Y)) := by
  exact bools _ _ _
private theorem lineBonus (X Y : Finset I) :
    bonus [13,14] X Y=((decide ((0:I)∈Y) || decide ((1:I)∈Y)) && decide ((1:I)∈X)) := by
  exact bools _ _ _
private def special (s : List ℕ) (p l : I) :=
  if s=[0,1] then decide (l=0 ∧ (p=0 ∨ p=1)) else decide (p=1 ∧ (l=0 ∨ l=1))
private theorem flags (s : List ℕ) (hs : valid s) (p l : I) :
    bonus s {p} {l}=special s p l := by
  rcases hs with rfl|rfl
  · rw [pointBonus]; simp [special,Bool.eq_iff_iff] <;> grind
  · rw [lineBonus]; simp [special,Bool.eq_iff_iff] <;> grind
private theorem missing (s : List ℕ) (hs : valid s) (Q : Finset I) :
    bonus s Q (missLines singerLines3 Q)=false := by
  have h (p l : I) (inc : p∈singerLines3 l) (pp : p∈Q) : l∉missLines singerLines3 Q := by
    intro lm
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp lm).2 inc pp
  rcases hs with rfl|rfl
  · rw [pointBonus]
    have f0 := h 0 0 (by decide)
    have f1 := h 1 0 (by decide)
    by_cases p0 : (0:I)∈Q <;> by_cases p1 : (1:I)∈Q <;> simp_all
  · rw [lineBonus]
    have f0 := h 1 0 (by decide)
    have f1 := h 1 1 (by decide)
    by_cases p1 : (1:I)∈Q <;> simp_all
private def Yes (C : Circuit) (s : List ℕ) :=
  ∀ p l : I,p∈singerLines3 l → test C s {p} {l} (special s p l)=true
private def No (C : Circuit) (s : List ℕ) :=
  ∀ Q : Finset I,IsQuadrangle singerLines3 Q → test C s Q (missLines singerLines3 Q) false=false
private def reject (C : Circuit) :=
  ∀ Q : Finset I,IsQuadrangle singerLines3 Q → C.eval (incidenceInput Q (missLines singerLines3 Q))=false
private theorem fullTests (s : List ℕ) (hs : valid s) (C : Circuit) :
    (Yes C s ∧ No C s) ↔ RightOnIncidentPairs singerLines3 (header s C) ∧ reject (header s C) := by
  constructor
  · rintro ⟨yes,no⟩
    constructor
    · intro l p h; rw [pref,flags s hs]; exact yes _ _ h
    · intro Q h; rw [pref,missing s hs]; exact no _ h
  · rintro ⟨yes,no⟩
    constructor
    · intro p l h; have z := yes l p h; rwa [pref,flags s hs] at z
    · intro Q h; have z := no Q h; rwa [pref,missing s hs] at z
private theorem headMono (s : List ℕ) (hs : valid s) (C : Circuit) (hm : Monotone2 C) : Monotone2 (header s C) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl|ht
  · rcases hs with rfl|rfl <;> decide
  · rcases List.mem_cons.mp ht with rfl|hg
    · exact ⟨Or.inl rfl,by decide⟩
    · exact hm _ hg
private theorem headBack (s : List ℕ) (hs : valid s) (C : Circuit) (h : ReadsBack 28 C) : ReadsBack 26 (header s C) := by
  intro j hj u hu
  cases j with
  | zero =>
    change u∈s at hu
    rcases hs with rfl|rfl <;> simp at hu <;> omega
  | succ j =>
    cases j with
    | zero =>
      change u∈[26,anc s] at hu
      rcases hs with rfl|rfl <;> simp [anc] at hu <;> omega
    | succ j =>
      have hj' : j<C.gates.length := by simpa [header] using hj
      have eq : gateAt (header s C) (j+2)=gateAt C j := by rfl
      change u∈(gateAt (header s C) (j+2)).inputs at hu
      rw [eq] at hu
      have := h j hj' u hu
      omega
private theorem sizeEq (s : List ℕ) (C : Circuit) : (header s C).size=C.size+2 := by
  simp [header,Circuit.size]
end PEqualNP.Outside.L_meta_17603
