import Mathlib
import PEqualNP.Outside.L_meta_1485
import PEqualNP.Outside.L_meta_5242

namespace PositiveRead2846
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_5242
open PEqualNP.Outside.L_meta_1485

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem criticalOR (hL : IsLeastAO G C) {j : Nat} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) (b : Fin 2) :
    ∃ u v : Fin n, G.Adj u v ∧
      let x := GraphSupport.input ({u,v} : Finset (Fin n))
      circuitFun n (bypass n C j (opnd C j b)) x = false ∧
      val C (List.ofFn x) (opnd C j b) = false ∧
      val C (List.ofFn x) (opnd C j (1-b)) = true := by
  classical
  let i := opnd C j b
  let D := bypass n C j i
  have hi : i < n+j := Structural.opnd_lt hL.1 hj b
  have hD : IsAO2 n D := isAO2_bypass hL.1 hi
  have hAO (k) (hk : k < C.gates.length) := hL.1.1 _ (Base.gateAt_mem hk)
  have forward (x : Fin n → Bool) : val C (List.ofFn x) i = true →
      val C (List.ofFn x) (n+j) = true :=
    fun h => (val_or (by simp) hj hor).mpr ⟨i,Structural.opnd_mem hL.1 hj b,hi,h⟩
  have down (x : Fin n → Bool) : circuitFun n D x = true → circuitFun n C x = true :=
    bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id)
      (fun op legal l f g h => opMono_imp op legal l g f h)
      (by simp) hAO hj (Or.inl hi) (forward x)
  have pairpos (u v : Fin n) (h : G.Adj u v) :
      graphFun G ∅ (GraphSupport.input ({u,v} : Finset (Fin n))) = true :=
    (GraphSupport.graph_true G _).mpr ⟨u,v,h,by simp,by simp⟩
  obtain ⟨u,v,edge,fail⟩ : ∃ u v : Fin n, G.Adj u v ∧
      circuitFun n D (GraphSupport.input ({u,v} : Finset (Fin n))) = false := by
    by_contra! all
    have eq : circuitFun n D = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        rw [← hL.2.1]
        exact down x hx
      · intro hx
        have src : graphFun G ∅ (GraphSupport.input (GraphSupport.support x)) = true := by
          simpa only [GraphSupport.input_support] using hx
        obtain ⟨u,v,edge,hu,hv⟩ := (GraphSupport.graph_true G _).mp src
        have on : circuitFun n D (GraphSupport.input ({u,v} : Finset (Fin n))) = true := by
          simpa only [Bool.not_eq_false] using all u v edge
        apply Structural.wire_mono hD _ x _ D.output on
        intro w hw
        have mem : w ∈ ({u,v} : Finset (Fin n)) := of_decide_eq_true hw
        rcases Finset.mem_insert.mp mem with rfl | hv'
        · exact (Finset.mem_filter.mp hu).2
        · obtain rfl := Finset.mem_singleton.mp hv'
          exact (Finset.mem_filter.mp hv).2
    have l := hL.2.2 D hD eq
    have e := bypass_length n C j i
    change C.gates.length ≤ (bypass n C j i).gates.length at l
    omega
  let x := GraphSupport.input ({u,v} : Finset (Fin n))
  have win : circuitFun n C x = true := by rw [hL.2.1]; exact pairpos u v edge
  have diff : val C (List.ofFn x) (n+j) ≠ val C (List.ofFn x) i := by
    intro eq
    have out := bypass_eval_eq (by simp) hAO hj (Or.inl hi) eq
    change circuitFun n D x = circuitFun n C x at out
    rw [win] at out
    exact Bool.noConfusion ((show circuitFun n D x = false from fail).symm.trans out)
  have off : val C (List.ofFn x) i = false := Bool.eq_false_iff.mpr fun h => diff ((forward x h).trans h.symm)
  have top : val C (List.ofFn x) (n+j) = true := by
    cases ht : val C (List.ofFn x) (n+j) with
    | false => exact (diff (ht.trans off.symm)).elim
    | true => rfl
  obtain ⟨w,hm,_,hw⟩ := (val_or (by simp) hj hor).mp top
  obtain ⟨d,rfl⟩ := (Structural.mem_inputs_iff_opnd hL.1 hj w).mp hm
  rcases Final.two_cases b d with h | h
  · subst d
    rw [show val C (List.ofFn x) (opnd C j b) = false from off] at hw
    contradiction
  · subst d
    exact ⟨u,v,edge,fail,off,hw⟩


theorem criticalBelow (hL : IsLeastAO G C) {j i : Nat} (hj : j < C.gates.length)
    (hi : i < n+j) (forward : ∀ x : Fin n → Bool,
      val C (List.ofFn x) i = true → val C (List.ofFn x) (n+j) = true) :
    ∃ u v : Fin n, G.Adj u v ∧
      let x := GraphSupport.input ({u,v} : Finset (Fin n))
      circuitFun n (bypass n C j i) x = false ∧
      val C (List.ofFn x) i = false ∧ val C (List.ofFn x) (n+j) = true := by
  classical
  let D := bypass n C j i
  have hD : IsAO2 n D := isAO2_bypass hL.1 hi
  have hAO (k) (hk : k < C.gates.length) := hL.1.1 _ (Base.gateAt_mem hk)
  have down (x : Fin n → Bool) : circuitFun n D x = true → circuitFun n C x = true :=
    bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id)
      (fun op legal l f g h => opMono_imp op legal l g f h)
      (by simp) hAO hj (Or.inl hi) (forward x)
  have pairpos (u v : Fin n) (h : G.Adj u v) :
      graphFun G ∅ (GraphSupport.input ({u,v} : Finset (Fin n))) = true :=
    (GraphSupport.graph_true G _).mpr ⟨u,v,h,by simp,by simp⟩
  obtain ⟨u,v,edge,fail⟩ : ∃ u v : Fin n, G.Adj u v ∧
      circuitFun n D (GraphSupport.input ({u,v} : Finset (Fin n))) = false := by
    by_contra! all
    have eq : circuitFun n D = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        rw [← hL.2.1]
        exact down x hx
      · intro hx
        have src : graphFun G ∅ (GraphSupport.input (GraphSupport.support x)) = true := by
          simpa only [GraphSupport.input_support] using hx
        obtain ⟨u,v,edge,hu,hv⟩ := (GraphSupport.graph_true G _).mp src
        have on : circuitFun n D (GraphSupport.input ({u,v} : Finset (Fin n))) = true := by
          simpa only [Bool.not_eq_false] using all u v edge
        apply Structural.wire_mono hD _ x _ D.output on
        intro w hw
        have mem : w ∈ ({u,v} : Finset (Fin n)) := of_decide_eq_true hw
        rcases Finset.mem_insert.mp mem with rfl | hv'
        · exact (Finset.mem_filter.mp hu).2
        · obtain rfl := Finset.mem_singleton.mp hv'
          exact (Finset.mem_filter.mp hv).2
    have l := hL.2.2 D hD eq
    have e := bypass_length n C j i
    change C.gates.length ≤ (bypass n C j i).gates.length at l
    omega
  let x := GraphSupport.input ({u,v} : Finset (Fin n))
  have win : circuitFun n C x = true := by rw [hL.2.1]; exact pairpos u v edge
  have diff : val C (List.ofFn x) (n+j) ≠ val C (List.ofFn x) i := by
    intro eq
    have out := bypass_eval_eq (by simp) hAO hj (Or.inl hi) eq
    change circuitFun n D x = circuitFun n C x at out
    rw [win] at out
    exact Bool.noConfusion ((show circuitFun n D x = false from fail).symm.trans out)
  have off : val C (List.ofFn x) i = false := Bool.eq_false_iff.mpr fun h => diff ((forward x h).trans h.symm)
  have top : val C (List.ofFn x) (n+j) = true := by
    cases ht : val C (List.ofFn x) (n+j) with
    | false => exact (diff (ht.trans off.symm)).elim
    | true => rfl
  exact ⟨u,v,edge,fail,off,top⟩

def active (G : SimpleGraph (Fin n)) (C : Circuit) (w : Nat) : Prop :=
  ∃ u v, G.Adj u v ∧ val C (List.ofFn (GraphSupport.input ({u,v} : Finset (Fin n)))) w = true

theorem all_active (hL : IsLeastAO G C) (edge : ∃ u v, G.Adj u v)
    (i : Nat) (hi : i<C.gates.length) : active G C (n+i) := by
  classical
  obtain ⟨u,v,huv⟩ := edge
  have hn := u.isLt
  have isOut : active G C C.output := by
    refine ⟨u,v,huv,?_⟩
    change circuitFun n C _ = true
    rw [hL.2.1]
    exact (GraphSupport.graph_true G _).mpr ⟨u,v,huv,by simp,by simp⟩
  by_contra hbad
  let B := (Finset.range C.gates.length).filter (fun j => ¬ active G C (n+j))
  have hB : i ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hbad⟩
  let m := B.max' ⟨i,hB⟩
  have hm : m ∈ B := Finset.max'_mem _ _
  obtain ⟨hm',dead⟩ := Finset.mem_filter.mp hm
  have hmL := Finset.mem_range.mp hm'
  have hAO (k) (hk : k<C.gates.length) := hL.1.1 _ (Base.gateAt_mem hk)
  have other : C.output ≠ n+m := fun eq => dead (eq ▸ isOut)
  obtain ⟨r,hr,read⟩ : ∃ r < C.gates.length, n+m ∈ (gateAt C r).inputs := by
    by_contra! no
    have shrink := hL.2.2 (bypass n C m 0) (isAO2_bypass hL.1 (by omega)) (by
      rw [← hL.2.1]
      funext x
      exact bypass_eval_unread (by simp) hAO hmL (Or.inl (by omega)) other no)
    have len := bypass_length n C m 0
    change C.gates.length ≤ (bypass n C m 0).gates.length at shrink
    omega
  have lt := hL.1.2.1 r hr (n+m) read
  have next : active G C (n+r) := by
    by_contra no
    have mem : r ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,no⟩
    have mx : r ≤ m := Finset.le_max' _ _ mem
    omega
  rcases hAO r hr with hand | hor
  · obtain ⟨s,t,adj,top⟩ := next
    exact dead ⟨s,t,adj,((val_and (by simp) hr hand).mp top _ read).2⟩
  · obtain ⟨d,hd⟩ := (Structural.mem_inputs_iff_opnd hL.1 hr _).mp read
    obtain ⟨s,t,adj,_,_,on⟩ := criticalOR hL hr hor (1-d)
    have eq : (1:Fin 2)-(1-d)=d := by fin_cases d <;> decide
    rw [eq,hd] at on
    exact dead ⟨s,t,adj,on⟩

theorem switch_vertex (hL : IsLeastAO G C) {j : Nat} (hj : j<C.gates.length) (p : Fin n)
    (alone : ∀ x : Fin n → Bool, x p = true → val C (List.ofFn x) (n+j) = true) :
    ∃ u v, G.Adj u v ∧ p ≠ u ∧ p ≠ v ∧
       val C (List.ofFn (GraphSupport.input ({u,v} : Finset (Fin n)))) (n+j) = true := by
  have hp := p.isLt
  obtain ⟨u,v,edge,_,off,on⟩ := criticalBelow hL (i := p.val) hj (by omega)
    (fun x hx => alone x ((Base.val_ofFn C x p).symm.trans hx))
  have off' : GraphSupport.input ({u,v} : Finset (Fin n)) p = false :=
    (Base.val_ofFn C _ p).symm.trans off
  have no : p ∉ ({u,v} : Finset (Fin n)) := of_decide_eq_false off'
  exact ⟨u,v,edge,fun e => no (e ▸ Finset.mem_insert_self _ _),
    fun e => no (e ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),on⟩

end PositiveRead2846
