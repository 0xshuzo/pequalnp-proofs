import PEqualNP.Defs
namespace Restore17601
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.HeptadCover
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
abbrev I := Fin 13
def heads : List (List Nat) := [[],[0],[13],[0,1],[13,14],[0,13],[0,14]]
def rail (s : List Nat) (x : List Bool) := x ++ [s.any fun i => x.getD i false]
def test (s : List Nat) (C : Circuit) (P L : Finset I) (b : Bool) :=
  C.eval (rail s (incidenceInput P L) ++ [b])
def hit (p l u v : I) := decide (u=p ∧ v=l)
def Yes (C : Circuit) (s : List Nat) (p l : I) :=
  ∀ u v : I, u ∈ singerLines3 v → test s C {u} {v} (hit p l u v) = true
def No (C : Circuit) (s : List Nat) :=
  ∀ Q : Finset I, IsQuadrangle singerLines3 Q → test s C Q (missLines singerLines3 Q) false = false
def hdr (C : Circuit) (s : List Nat) (p l : I) : Circuit :=
  ⟨⟨.or,s⟩ :: ⟨.and,[p.val,13+l.val]⟩ :: C.gates,C.output⟩
theorem hsLen {s : List Nat} (hs : s ∈ heads) : s.length≤2 ∧ ∀ i∈s,i<26 := by
  have h : ∀ t ∈ heads, t.length≤2 ∧ ∀ i∈t,i<26 := by decide
  exact h s hs
theorem legal {C : Circuit} {s : List Nat} (hs : s ∈ heads) (p l : I) (hm : Monotone2 C) :
    Monotone2 (hdr C s p l) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl|h
  · exact ⟨Or.inr rfl,(hsLen hs).1⟩
  rcases List.mem_cons.mp h with rfl|h
  · exact ⟨Or.inl rfl,by decide⟩
  · exact hm _ h
theorem reads {C : Circuit} {s : List Nat} (hs : s ∈ heads) (p l : I) (hr : ReadsBack 28 C) :
    ReadsBack 26 (hdr C s p l) := by
  intro i hi w hw
  cases i with
  | zero => exact (hsLen hs).2 w hw
  | succ i =>
    cases i with
    | zero =>
      change w ∈ [p.val,13+l.val] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> have := p.isLt <;> have := l.isLt <;> omega
    | succ i =>
      have h : i < C.gates.length := by simpa [hdr] using hi
      exact (by have := hr i h w (show w ∈ (gateAt C i).inputs from hw); omega)
theorem price (C : Circuit) (s : List Nat) (p l : I) : (hdr C s p l).size=C.size+2 := by
  simp [hdr,Circuit.size]
theorem phys (C : Circuit) (s : List Nat) (p l : I) (P L : Finset I) :
    (hdr C s p l).eval (incidenceInput P L) = test s C P L (decide (p∈P ∧ l∈L)) := by
  let x := incidenceInput P L
  have op : GateOp.or.eval (s.map fun i => x.getD i false)=s.any (fun i=>x.getD i false) := by
    simp [GateOp.eval,List.any_map,Function.comp_def]
  have plen : x.length=26 := by simp [x,incidenceInput]
  have a : (rail s x).getD p.val false = decide (p∈P) := by
    rw [rail,List.getD_append _ _ _ _ (by omega)]
    change ((List.ofFn fun t : I=>decide (t∈P)) ++ _).getD p.val false=_
    rw [List.getD_append _ _ _ _ (by simpa using p.isLt)]
    simp [List.getD_eq_getElem?_getD,p.isLt]
  have b : (rail s x).getD (13+l.val) false = decide (l∈L) := by
    rw [rail,List.getD_append _ _ _ _ (by have := l.isLt; omega)]
    simp [x,incidenceInput,List.getD_eq_getElem?_getD,List.getElem?_append_right,l.isLt]
  change C.eval (((x ++ [GateOp.or.eval (s.map fun i => x.getD i false)]) ++
    [GateOp.and.eval ([p.val,13+l.val].map fun i => (x ++ [GateOp.or.eval (s.map fun i => x.getD i false)]).getD i false)]))=_
  rw [op]
  change C.eval (rail s x ++ [GateOp.and.eval ([p.val,13+l.val].map fun i => (rail s x).getD i false)])=_
  change C.eval (rail s x ++ [GateOp.and.eval ([p.val,13+l.val].map fun i => (rail s x).getD i false)]) = C.eval (rail s x ++ [decide (p∈P ∧ l∈L)])
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,a,b,decide_and]
theorem full (C : Circuit) (s : List Nat) (p l : I) (pl : p∈singerLines3 l) :
    (Yes C s p l ∧ No C s) ↔
      RightOnIncidentPairs singerLines3 (hdr C s p l) ∧
      ∀ Q : Finset I, IsQuadrangle singerLines3 Q →
      (hdr C s p l).eval (incidenceInput Q (missLines singerLines3 Q))=false := by
  have yp (u v : I) : decide (p∈({u}:Finset I) ∧ l∈({v}:Finset I))=hit p l u v := by
    simp [hit,eq_comm]
  have nq (Q : Finset I) : decide (p∈Q ∧ l∈missLines singerLines3 Q)=false := by
    apply decide_eq_false
    rintro ⟨a,b⟩
    have dis := (Finset.mem_filter.mp b).2
    exact Finset.disjoint_left.mp dis pl a
  constructor
  · rintro ⟨y,n⟩
    exact ⟨fun v u h => by rw [phys,yp]; exact y u v h,
      fun Q h => by rw [phys,nq]; exact n Q h⟩
  · rintro ⟨y,n⟩
    exact ⟨fun u v h => by have z := y v u h; rwa [phys,yp] at z,
      fun Q h => by have z := n Q h; rwa [phys,nq] at z⟩
end Restore17601
