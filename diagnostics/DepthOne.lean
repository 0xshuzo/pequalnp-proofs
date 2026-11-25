import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_3720
import PEqualNP.Outside.L_meta_3652
import PEqualNP.Outside.L_meta_1491

namespace Star3722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core
open PEqualNP.Outside.L_meta_3652_aux


theorem liveCone {n : ℕ} (C : Circuit) (live : PEqualNP.FactorSubst.liveSize n C=C.size) :
    ∀ j<C.gates.length,InOutputCone n C j := by
  intro j hj
  have sub : PEqualNP.FactorSubst.liveGates n C ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
  have same : PEqualNP.FactorSubst.liveGates n C=Finset.range C.gates.length := Finset.eq_of_subset_of_card_le sub (by
    change (Finset.range C.gates.length).card≤PEqualNP.FactorSubst.liveSize n C
    rw [live,Finset.card_range];exact le_rfl)
  have inLive : j∈PEqualNP.FactorSubst.liveGates n C := same ▸ Finset.mem_range.mpr hj
  obtain ⟨_,lo,h|h⟩ := Finset.mem_filter.mp inLive
  · exact ⟨hj, Or.inl (by omega)⟩
  · exact ⟨hj,Or.inr ⟨lo,h⟩⟩

theorem topPath {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hLift : IsLiftFixedPoint G C) (hOC : ∀ j<C.gates.length,InOutputCone n C j)
    (h7 : ∀ k<C.gates.length,(gateAt C k).op=.and → ∀ t∈(gateAt C k).inputs, ¬BW G C t)
    (j : ℕ) (hj : j<C.gates.length) (jb : BW G C (n+j)) :
    Relation.ReflTransGen (PEqualNP.Outside.L_meta_1491.S90.OrStep n C) C.output (n+j) := by
  classical
  have hG : Good n C := ⟨fun g hg => ⟨hAO.1 g hg,hAO.2.2 g hg⟩,hAO.2.1⟩
  have hL' : ∀ h < C.gates.length, (gateAt C h).op = GateOp.or → ¬ BW G C (n + h) →
      ∀ t ∈ (gateAt C h).inputs, ¬ BW G C t := by
    intro h hh hop hnb t ht hbt
    apply hLift
    obtain ⟨a, b, hin, ha, hb, _⟩ := two hG h hh
    rw [hin] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨h, hh, 0, hOC h hh, hop, hnb, ?_⟩
      have e0 : opnd C h 0 = t := by simp [opnd, hin]
      rw [e0]
      exact ⟨hbt, fun _ => true, ones hG t (by omega)⟩
    · refine ⟨h, hh, 1, hOC h hh, hop, hnb, ?_⟩
      have e0 : opnd C h 1 = t := by simp [opnd, hin]
      rw [e0]
      exact ⟨hbt, fun _ => true, ones hG t (by omega)⟩

  have follow (o : ℕ) (ol : o<C.gates.length) (hc : InCone n C j o) :
      Relation.ReflTransGen (PEqualNP.Outside.L_meta_1491.S90.OrStep n C) (n+o) (n+j) := by
    induction o using Nat.strong_induction_on with
    | _ o ih =>
      obtain ⟨_,k,ko,mem,desc⟩ := (inCone_iff n C j o).mp hc
      have root : BW G C (n+k) := by
        rcases desc with same|inside
        · simpa [←same] using jb
        · by_contra hd
          exact closure G hG h7 hL' k (by omega) hd j inside jb
      have orOp := (hAO.1 _ (PEqualNP.Outside.L_meta_1491.S90.gateAt_mem ol)).resolve_left (fun a => h7 o ol a _ mem root)
      have step : PEqualNP.Outside.L_meta_1491.S90.OrStep n C (n+o) (n+k) := ⟨o,ol,rfl,orOp,mem,by omega⟩
      rcases desc with rfl|inside
      · exact Relation.ReflTransGen.single step
      · exact Relation.ReflTransGen.head step (ih k ko (by omega) inside)
  obtain ⟨_,eq|⟨lo,c⟩⟩ := hOC j hj
  · rw [eq]
  · have ol := ((inCone_iff n C j (C.output-n)).mp c).1
    have eq : n+(C.output-n)=C.output := by omega
    exact eq ▸ follow (C.output-n) ol c

def component (one : Bool) (v : Bool×Bool) := if one then v.2 else v.1
theorem partUp {n : ℕ} {C : Circuit} (hG : Good n C) (isLine : ℕ→Bool) (z : List Bool) (hz : z.length=n)
    (one : Bool) {w w' : ℕ} (path : Relation.ReflTransGen (PEqualNP.Outside.L_meta_1491.S90.OrStep n C) w w')
    (hit : component one (PP C isLine z w')=true) : component one (PP C isLine z w)=true := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact hit
  | head st _ ih =>
    obtain ⟨k,hk,rfl,op,mem,_⟩ := st
    obtain ⟨a,b,ins,_,_,_⟩ := two hG k hk
    rw [ins] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rw [PP_or hG isLine z hz k hk a b ins op]
    cases one <;> rcases mem with rfl|rfl <;> simp_all [component]

theorem starSingle (N : ℕ) (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 (N+N) C) (lift : IsLiftFixedPoint G C) (live : PEqualNP.FactorSubst.liveSize (N+N) C=C.size)
    (clean : ∀ k<C.gates.length, (gateAt C k).op=.and → ∀ t∈(gateAt C k).inputs, ¬BW G C t)
    (p l : Fin N) (edge : s(Fin.castAdd N p,Fin.natAdd N l)∈starEdges G C) :
    lineSingle C (N+N) (fun w=>decide (N≤w)) p.val (N+l.val)=true := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let L := fun w : ℕ => decide (N≤w)
  let z := zin (N+N) p.val (N+l.val)
  have hz : z.length=N+N := zin_length _ _ _
  have good : Good (N+N) C := ⟨fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩,ao.2.1⟩
  have hp (w : ℕ) (h : Fin.castAdd N p∈orIn (N+N) C w) : (PP C L z w).1=true := by
    apply partUp good L z hz false (PEqualNP.Outside.L_meta_1491.S90.mem_orIn_reach _ h)
    change (PP C L z p.val).1=true
    rw [PP_lt C L z p.val (by rw [hz];omega)]
    have low : L p.val=false := by simp [L,p.isLt]
    rw [low]
    have valid : p.val<N+N := by omega
    change (zin (N+N) p.val (N+l.val)).getD p.val false=true
    rw [zin_getD _ _ _ _ valid]
    simp
  have hl (w : ℕ) (h : Fin.natAdd N l∈orIn (N+N) C w) : (PP C L z w).2=true := by
    apply partUp good L z hz true (PEqualNP.Outside.L_meta_1491.S90.mem_orIn_reach _ h)
    change (PP C L z (N+l.val)).2=true
    rw [PP_lt C L z _ (by rw [hz];omega)]
    have high : L (N+l.val)=true := by simp [L]
    rw [high]
    have valid : N+l.val<N+N := by omega
    change (zin (N+N) p.val (N+l.val)).getD (N+l.val) false=true
    rw [zin_getD _ _ _ _ valid]
    simp
  obtain ⟨j,hj,hcross⟩ := Finset.mem_biUnion.mp edge
  obtain ⟨⟨a,b⟩,sides,eq⟩ := Finset.mem_image.mp hcross
  obtain ⟨sa,sb⟩ := Finset.mem_product.mp sides
  obtain ⟨len,op,below⟩ := Finset.mem_filter.mp hj
  have jl := Finset.mem_range.mp len
  obtain ⟨u,v,ins,_,_,_⟩ := two good j jl
  change (PP C L z C.output).2=true
  apply partUp good L z hz true (topPath G C ao lift (liveCone C live) clean j jl below)
  change (PP C L z (N+N+j)).2=true
  rw [PP_and good L z hz j jl u v ins op]
  simp only [side,opnd,ins,List.getD] at sa sb
  rcases Sym2.eq_iff.mp eq with h|h
  · obtain ⟨rfl,rfl⟩ := h
    simp [hp u sa,hl v sb]
  · obtain ⟨rfl,rfl⟩ := h
    simp [hl u sa,hp v sb]

theorem doubleSubset (N : ℕ) (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 (N+N) C) (lift : IsLiftFixedPoint G C) (live : PEqualNP.FactorSubst.liveSize (N+N) C=C.size)
    (clean : ∀ k<C.gates.length, (gateAt C k).op=.and → ∀ t∈(gateAt C k).inputs, ¬BW G C t)
    (E : List (ℕ×ℕ)) (p l : Fin N) (adj : G.Adj (Fin.castAdd N p) (Fin.natAdd N l))
    (h : (p.val,N+l.val)∈doubleReread C (N+N) (fun w=>decide (N≤w)) E) :
    s(Fin.castAdd N p,Fin.natAdd N l)∈Ustar G C := by
  apply Finset.mem_sdiff.mpr
  refine ⟨G.mem_edgeFinset.mpr adj,?_⟩
  intro star
  have on := starSingle N G C ao lift live clean p l star
  have off := (List.mem_filter.mp h).2
  simp [on] at off

end Star3722

namespace Depth3722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core
open PEqualNP.Outside.L_meta_3652_aux
open PEqualNP.Outside.L_meta_1491.S90 (OrStep gateAt_mem operand_cone or_trace reach_var_val below_of_reach off_star)

def Flat (n : ℕ) (C : Circuit) : Prop :=
  ∀ i<C.gates.length,∀ j<C.gates.length,
    (gateAt C i).op=.and → (gateAt C j).op=.and → ¬InCone n C i j

lemma allLive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) : PEqualNP.FactorSubst.liveSize n C=C.size :=
  PEqualNP.Outside.L_meta_3720.live_all (graphFun G ∅) C.gates C.output
    (PEqualNP.Outside.L_meta_3720.ao_of n C least.1) (fun x=>congrFun least.2.1 x)
    (fun gs o ao eq => least.2.2 ⟨gs,o⟩ (PEqualNP.Outside.L_meta_3720.ao_to n gs o ao) (funext eq))

lemma upperPath {n : ℕ} {C : Circuit} {u : ℕ}
    (oc : InOutputCone n C u)
    (up : ∀ v<C.gates.length,InCone n C u v → (gateAt C v).op=.or) :
    Relation.ReflTransGen (OrStep n C) C.output (n+u) := by
  have follow (o : ℕ) (ol : o<C.gates.length) (hc : InCone n C u o) :
      Relation.ReflTransGen (OrStep n C) (n+o) (n+u) := by
    induction o using Nat.strong_induction_on with
    | _ o ih =>
      obtain ⟨_,k,ko,mem,desc⟩ := (inCone_iff n C u o).mp hc
      have step : OrStep n C (n+o) (n+k) := ⟨o,ol,rfl,up o ol hc,mem,by omega⟩
      rcases desc with rfl|inside
      · exact Relation.ReflTransGen.single step
      · exact Relation.ReflTransGen.head step (ih k ko (by omega) inside)
  obtain ⟨_,eq|⟨lo,c⟩⟩ := oc
  · rw [eq]
  · have ol := ((inCone_iff n C u (C.output-n)).mp c).1
    have eq : n+(C.output-n)=C.output := by omega
    exact eq ▸ follow (C.output-n) ol c

lemma impAncestor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) {j t : ℕ} (jl : j<C.gates.length) (tm : t∈(gateAt C j).inputs)
    (bw : BW G C t) : ∃ a<C.gates.length,(gateAt C a).op=.and ∧ InCone n C a j := by
  have good : Good n C := ⟨fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩,ao.2.1⟩
  have tl := ao.2.1 j jl t tm
  obtain ⟨w,path,_,raw|⟨a,al,rfl,nor⟩⟩ := or_trace (n:=n) (C:=C)
    (x:=List.ofFn (fun _ : Fin n=>true)) (by simp) t (ones good t (by omega))
  · let v : Fin n := ⟨w,raw⟩
    have on := reach_var_val (eof v) t v path (by simp [eof])
    have no := bw (eof v) on
    rw [F_eof] at no
    cases no
  · exact ⟨a,al,(ao.1 _ (gateAt_mem al)).resolve_right nor,operand_cone jl tm tl path⟩

lemma normal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) (flat : Flat n C) :
    IsLiftFixedPoint G C ∧
    (∀ j<C.gates.length,(gateAt C j).op=.and → ∀ t∈(gateAt C j).inputs,¬BW G C t) ∧
    (∀ j<C.gates.length,(gateAt C j).op=.and → BelowF G C j) := by
  have ao := least.1
  have good : Good n C := ⟨fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩,ao.2.1⟩
  have oc := Star3722.liveCone C (allLive G C least)
  have upper {j : ℕ} (jl : j<C.gates.length) (up : ∀ v<C.gates.length,InCone n C j v → (gateAt C v).op=.or) :
      BelowF G C j := below_of_reach (graphFun G ∅) (fun x=>congrFun least.2.1 x) j (upperPath (oc j jl) up)
  constructor
  · rintro ⟨j,jl,b,_,_,dirty,imp⟩
    obtain ⟨x,y,ins,_,_,_⟩ := two good j jl
    have mem : opnd C j b ∈ (gateAt C j).inputs := by fin_cases b <;> simp [opnd,ins]
    obtain ⟨h,hl,op,hj⟩ := impAncestor G C ao jl mem imp.1
    apply dirty
    apply upper jl
    intro v vl jv
    apply (ao.1 _ (gateAt_mem vl)).resolve_left
    intro vp
    exact flat h hl v vl op vp (PEqualNP.Outside.L_meta_3720.inCone_trans n C h j hj v jv)
  constructor
  · intro j jl op t mem tb
    obtain ⟨a,al,ap,aj⟩ := impAncestor G C ao jl mem tb
    exact flat a al j jl ap op aj
  · intro j jl op
    apply upper jl
    intro v vl jv
    exact (ao.1 _ (gateAt_mem vl)).resolve_left (fun vp=>flat j jl v vl op vp jv)

theorem result (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj] (C : Circuit)
    (adj : ∀ p l,I p l → G.Adj (Fin.castAdd N p) (Fin.natAdd N l))
    (least : IsLeastAO G C) (flat : Flat (N+N) C) :
    IsLiftFixedPoint G C ∧
    (∀ j<C.gates.length,(gateAt C j).op=.and → ∀ t∈(gateAt C j).inputs,¬BW G C t) ∧
    PEqualNP.FactorSubst.liveSize (N+N) C=C.size ∧
    doubleReread C (N+N) (fun w=>decide (N≤w)) ((List.finRange N).flatMap
      (fun p=>((List.finRange N).filter (fun l=>decide (I p l))).map (fun l=>(p.val,N+l.val))))=[] := by
  obtain ⟨lift,clean,below⟩ := normal G C least flat
  have live := allLive G C least
  refine ⟨lift,clean,live,?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e mem
  have listed := (List.mem_filter.mp mem).1
  simp only [List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_finRange,true_and,
    decide_eq_true_eq] at listed
  obtain ⟨p,l,inc,rfl⟩ := listed
  have u := Star3722.doubleSubset N G C least.1 lift live clean _ p l (adj p l inc) mem
  obtain ⟨_,_,_,h,hjunk,_⟩ := off_star G C least (fun i il j jl a _ b=>flat i il j jl a b) _ _ u
  obtain ⟨hl,hAnd,hNo⟩ := Finset.mem_filter.mp hjunk
  obtain ⟨_,x,hx,fx⟩ := hNo
  have on := below h (Finset.mem_range.mp hl) hAnd x hx
  rw [fx] at on
  cases on

end Depth3722
