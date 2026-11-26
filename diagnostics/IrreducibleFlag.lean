import PEqualNP.Outside.L_meta_1892
import PEqualNP.Outside.L_meta_5875

namespace FlagIrreducible5877
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_5875
open PEqualNP.Outside.L_meta_1892_aux.Dirty

def dirtyAt (C : Circuit) (j : Nat) : Prop :=
  (∃ g : Gate, C.gates[j]? = some g ∧ g.op = .and) ∧
  ∃ a b : Fin 42, ¬plane.Adj a b ∧ wire C (pairInput a b) (42+j)=true

def orAt (C : Circuit) (j : Nat) : Prop :=
  ∃ inputs : List Nat, inputs.length ≤ 2 ∧
    ∀ x : Input, wire C x (42+j) = GateOp.or.eval (inputs.map (read C x j))

/-- At size 124 some AND both accepts a nonedge pair and has no equivalent
fan-in-two OR of earlier wires. This allows either wire type on the OR inputs. -/
theorem irreducible (C : Circuit) (mono : Monotone2 C) (small : C.size≤124)
    (ok : ∀ x : Input, C.eval (List.ofFn x)=true ↔ yes x) :
    ∃ j < C.gates.length, dirtyAt C j ∧ ¬orAt C j := by
  classical
  by_contra none
  have replace (j : Fin C.gates.length) (hj : dirtyAt C j.val) : orAt C j.val := by
    by_contra h
    exact none ⟨j.val,j.isLt,hj,h⟩
  let inputs (j : Fin C.gates.length) := if h : dirtyAt C j.val then (replace j h).choose else []
  have specs (j : Fin C.gates.length) (h : dirtyAt C j.val) :
      (inputs j).length ≤ 2 ∧
        ∀ x : Input, wire C x (42+j.val)=GateOp.or.eval ((inputs j).map (read C x j.val)) := by
    simpa only [inputs,dif_pos h] using (replace j h).choose_spec
  let gate (j : Fin C.gates.length) : Gate := if dirtyAt C j.val then ⟨.or,inputs j⟩ else C.gates[j.val]
  let D : Circuit := ⟨List.ofFn gate,C.output⟩
  have len : D.gates.length=C.gates.length := by simp [D]
  have get (j : Fin C.gates.length) : D.gates[j.val]? = some (gate j) := by
    have hj : j.val < D.gates.length := by rw [len]; exact j.isLt
    rw [List.getElem?_eq_getElem hj]
    simp [D]
  have dm : Monotone2 D := by
    intro g hg
    change g ∈ List.ofFn gate at hg
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hg
    by_cases hj : dirtyAt C j.val
    · rw [show gate j = ⟨.or,inputs j⟩ by simp [gate,hj]]
      exact ⟨Or.inr rfl,(specs j hj).1⟩
    · rw [show gate j = C.gates[j.val] by simp [gate,hj]]
      exact mono _ (List.getElem_mem j.isLt)
  have same (x : Input) (w : Nat) : wire D x w = wire C x w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases raw : w < 42
      · exact (wire_input D x ⟨w,raw⟩).trans (wire_input C x ⟨w,raw⟩).symm
      by_cases outside : 42+C.gates.length ≤ w
      · rw [wire_outside D x (i := w) (by omega),wire_outside C x (i := w) outside]
      let j : Fin C.gates.length := ⟨w-42,by omega⟩
      have hw : w=42+j.val := by dsimp [j]; omega
      have rd : read D x j.val = read C x j.val := by
        funext t
        by_cases ht : t < 42+j.val
        · simpa only [read,if_pos ht] using ih t (by omega)
        · simp only [read,if_neg ht]
      rw [hw,gate_sem D x (get j),rd]
      by_cases hj : dirtyAt C j.val
      · rw [show gate j = ⟨.or,inputs j⟩ by simp [gate,hj]]
        exact ((specs j hj).2 x).symm
      · rw [show gate j = C.gates[j.val] by simp [gate,hj]]
        exact (gate_sem C x (List.getElem?_eq_getElem j.isLt)).symm
  have dok (x : Input) : D.eval (List.ofFn x)=true ↔ yes x := by
    change wire D x C.output=true ↔ yes x
    rw [same]
    exact ok x
  have dsmall : D.size≤124 := by
    change D.gates.length≤124
    rw [len]
    exact small
  obtain ⟨a,b,nonedge,k,g,got,hop,hit⟩ := independent D dm dsmall dok
  obtain ⟨hk,_⟩ := List.getElem?_eq_some_iff.mp got
  let j : Fin C.gates.length := ⟨k,by omega⟩
  have eqg : gate j = g := Option.some.inj ((get j).symm.trans got)
  have hitC : wire C (pairInput a b) (42+k)=true := (same _ _).symm.trans hit
  by_cases h : dirtyAt C k
  · have ho : (gate j).op=.or := by
      have hj : dirtyAt C j.val := h
      simp [gate,hj]
    rw [eqg,hop] at ho
    cases ho
  · have hg : gate j = C.gates[j.val] := by
      have hj : ¬dirtyAt C j.val := h
      simp [gate,hj]
    have old : C.gates[k]?=some g := by
      exact (List.getElem?_eq_getElem j.isLt).trans (congrArg some (hg.symm.trans eqg))
    exact h ⟨⟨_,old,hop⟩,a,b,nonedge,hitC⟩

end FlagIrreducible5877

namespace FlagIrreducible5877
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_5875
open PEqualNP.Outside.L_meta_1892_aux.Dirty
open PEqualNP.Outside.L_meta_1892_aux.Transport (changeC idx lookup_change)

private theorem transportOr (C : Circuit) (e : Fin 42 ≃ Fin 42) (j : Nat) :
    orAt (changeC e C) j → orAt C j := by
  rintro ⟨xs,len,correct⟩
  have inverse (r : Nat) : ∃ t, idx e t=r ∧ (t < 42+j ↔ r < 42+j) := by
    by_cases h : r<42
    · let s := e.symm (⟨r,h⟩ : Fin 42)
      have hs : s.val<42 := s.isLt
      refine ⟨s.val,?_,by omega⟩
      simpa [idx,hs,s] using congrArg Fin.val (e.apply_symm_apply (⟨r,h⟩ : Fin 42))
    · exact ⟨r,by simp [idx,h],Iff.rfl⟩
  choose inv hidx hbound using inverse
  refine ⟨xs.map inv,by simpa using len,?_⟩
  intro x
  let y : Input := x ∘ e.symm
  have pull : y ∘ e = x := by funext v; simp [y]
  have wireEq (t : Nat) : wire (changeC e C) y (idx e t) = wire C x t := by
    have hw := lookup_change e C y t
    change wire (changeC e C) y (idx e t) = wire C (y ∘ e) t at hw
    rwa [pull] at hw
  have gateIx : idx e (42+j) = 42+j := by simp [idx,show ¬42+j<42 by omega]
  have gated := wireEq (42+j)
  rw [gateIx] at gated
  have compare (r : Nat) : read (changeC e C) y j r = read C x j (inv r) := by
    have hw := wireEq (inv r)
    rw [hidx r] at hw
    by_cases h : r<42+j
    · simpa only [read,if_pos h,if_pos ((hbound r).2 h)] using hw
    · simp only [read,if_neg h,if_neg (fun hn => h ((hbound r).1 hn))]
  rw [← gated,correct y,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact compare i

/-- A single nonredundant AND is active on both the posted base and one of
its fourteen flags in a size-preserving relabeling of the original circuit. -/
theorem canonical (C : Circuit) (mono : Monotone2 C) (small : C.size≤124)
    (ok : ∀ x : Input, C.eval (List.ofFn x)=true ↔ yes x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size=C.size ∧
    (∀ x : Input, D.eval (List.ofFn x)=true ↔ yes x) ∧
    ∃ k g m, D.gates[k]?=some g ∧ g.op=.and ∧ m ∈ masks ∧
      wire D baseInput (42+k)=true ∧ wire D (maskInput m) (42+k)=true ∧ ¬orAt D k := by
  classical
  obtain ⟨k,hk,⟨⟨g,got,hand⟩,a,b,nonedge,hot⟩,essential⟩ := irreducible C mono small ok
  have missing : PEqualNP.Outside.L_meta_1892_aux.Transport.adj a b=false := by
    exact decide_eq_false nonedge
  obtain ⟨f,onto,adj,ha,hb⟩ := PEqualNP.Outside.L_meta_1892_aux.Transport.transportPair a b missing
  let e : Fin 42 ≃ Fin 42 := Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr onto,onto⟩
  have ea : baseInput (e a)=true := ha
  have eb : baseInput (e b)=true := hb
  obtain ⟨m,hm,ma,mb⟩ := pair_mask ((base_spec _).mp ea) ((base_spec _).mp eb)
  let D := changeC e C
  have dm : Monotone2 D := by
    intro q hq
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hq
    exact ⟨(mono t ht).1,by simpa [PEqualNP.Outside.L_meta_1892_aux.Transport.changeGate] using (mono t ht).2⟩
  have dok (x : Input) : D.eval (List.ofFn x)=true ↔ yes x := by
    have hw : D.eval (List.ofFn x)=C.eval (List.ofFn (x ∘ e)) := lookup_change e C x C.output
    rw [hw,ok]
    exact PEqualNP.Outside.L_meta_1892_aux.Transport.yes_move e onto adj x
  have grows (x : Input) (xa : x (e a)=true) (xb : x (e b)=true) : wire D x (42+k)=true := by
    have hw := lookup_change e C x (42+k)
    change wire D x (idx e (42+k)) = wire C (x ∘ e) (42+k) at hw
    rw [show idx e (42+k)=42+k by simp [idx,show ¬42+k<42 by omega]] at hw
    rw [hw]
    apply PEqualNP.Outside.L_meta_1892_aux.Transport.evalMono1892 C.gates (42+k)
        (fun g' hg' => (mono g' hg').1) (pairInput a b) (x ∘ e) _ hot
    intro i hi
    obtain h|h : i=a ∨ i=b := by simpa [pairInput] using hi
    · simpa [h] using xa
    · simpa [h] using xb
  refine ⟨D,dm,by simp [D,changeC,Circuit.size],dok,k,
    PEqualNP.Outside.L_meta_1892_aux.Transport.changeGate e g,m,?_,hand,hm,grows _ ea eb,grows _ ma mb,
    fun wrong => essential (transportOr C e k wrong)⟩
  simp [D,changeC,List.getElem?_map,got]

end FlagIrreducible5877
