import PEqualNP.Outside.L_meta_17589
import Mathlib
import PEqualNP.Outside.L_meta_3243
import PEqualNP.Outside.L_meta_3245
import PEqualNP.Outside.L_meta_1737
import PEqualNP.Outside.L_meta_3652
import PEqualNP.MetaComplexity.Helpers.CoverCircuitGraph
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_3720
import PEqualNP.Outside.L_meta_1491
import PEqualNP.Outside.L_meta_599
import PEqualNP.Outside.L_meta_217

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
namespace Forest3722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core
open PEqualNP.Outside.L_meta_3652_aux (inCone_iff)
open PEqualNP.Outside.L_meta_3245_aux (Inv inv_cover gates_eq gateAt_get)
open PEqualNP.MetaComplexity.CoverCircuit

lemma compileFlat (n : ℕ) (own : List (ℕ × List ℕ))
    (h : ∀ b∈own,b.1<n ∧ ∀ v∈b.2,v<n) :
    let C := coverCircuitB n own
    IsAO2 n C ∧ ∀ i<C.gates.length,∀ j<C.gates.length,
      (gateAt C i).op=.and → (gateAt C j).op=.and → ¬InCone n C i j := by
  let C := coverCircuitB n own
  obtain ⟨S,T,ops,imS,imT,sides⟩ := inv_cover (fun w=>w<n) (fun w=>w<n) own n true 0
    (fun _ z=>z) (fun _ z=>z) (by simp) (fun b hb=>Or.inl (h b hb))
  have gates : C.gates = coverGatesB n true 0 own := gates_eq n own
  rw [←gates] at ops imS imT sides
  have ao : IsAO2 n C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hg
      exact (ops k g hk).1
    · intro j hj t ht
      exact (ops j _ (gateAt_get C j hj)).2.2 t ht
    · intro g hg
      obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hg
      exact (ops k g hk).2.1
  let marked := fun w : ℕ=>w<n ∨ w∈S ∨ w∈T
  have source (j : ℕ) (jl : j<C.gates.length) (m : marked (n+j)) :
      (gateAt C j).op=.or ∧ ∀ t∈(gateAt C j).inputs,marked t := by
    have collect (U : Finset ℕ) (get : ∀ w∈U,∃ k g,C.gates[k]?=some g ∧ w=n+k ∧
        g.op=.or ∧ ∀ t∈g.inputs,t<n ∨ t∈U) (mU : n+j∈U) (sub : ∀ t∈U,marked t) :
        (gateAt C j).op=.or ∧ ∀ t∈(gateAt C j).inputs,marked t := by
      obtain ⟨k,g,access,eq,gor,r⟩ := get (n+j) mU
      have jk : j=k := Nat.add_left_cancel eq
      subst k
      rw [gateAt_get C j jl] at access
      cases Option.some.inj access
      exact ⟨gor,fun t ht=>(r t ht).elim Or.inl (sub t)⟩
    rcases m with lo|s|t
    · omega
    · exact collect S imS s (fun _ z=>Or.inr (Or.inl z))
    · exact collect T imT t (fun _ z=>Or.inr (Or.inr z))
  have up {i j : ℕ} (ij : InCone n C i j) (mj : marked (n+j)) : marked (n+i) := by
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      obtain ⟨jl,k,kl,read,hk⟩ := (inCone_iff n C i j).mp ij
      have mk := (source j jl mj).2 _ read
      rcases hk with rfl|ik
      · exact mk
      · exact ih k kl ik mk
  refine ⟨ao,?_⟩
  intro i il j jl ai aj ij
  obtain ⟨a,b,inputs,order⟩ := sides j _ (gateAt_get C j jl) aj
  have markS (t : ℕ) (ht : t<n ∨ t∈S) : marked t := ht.elim Or.inl (fun z=>Or.inr (Or.inl z))
  have markT (t : ℕ) (ht : t<n ∨ t∈T) : marked t := ht.elim Or.inl (fun z=>Or.inr (Or.inr z))
  have ab : marked a ∧ marked b := order.elim
    (fun z=>⟨markS a z.1,markT b z.2⟩) (fun z=>⟨markT a z.1,markS b z.2⟩)
  obtain ⟨_,k,_,read,hk⟩ := (inCone_iff n C i j).mp ij
  rw [inputs] at read
  simp only [List.mem_cons,List.not_mem_nil,or_false] at read
  have mk : marked (n+k) := read.elim (fun e=>e.symm ▸ ab.1) (fun e=>e.symm ▸ ab.2)
  have mi : marked (n+i) := hk.elim (fun e=>e.symm ▸ mk) (fun inside=>up inside mk)
  have bad := (source i il mi).1
  rw [ai] at bad
  cases bad

theorem tight (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bound : ∀ (D : Circuit), IsAO2 n D → circuitFun n D=graphFun G ∅ →
      ∃ U : Finset (Fin n), CoverPromise.IsVertexCover G U ∧ G.edgeSet.ncard+U.card≤D.size+1) :
    ∃ C : Circuit, IsLeastAO G C ∧ ∀ i<C.gates.length,∀ j<C.gates.length,
      (gateAt C i).op=.and → (gateAt C j).op=.and → ¬InCone n C i j := by
  classical
  let covers := Finset.univ.filter (fun T : Finset (Fin n)=>CoverPromise.IsVertexCover G T)
  have full : (Finset.univ : Finset (Fin n))∈covers := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,fun _ _ _=>Or.inl (Finset.mem_univ _)⟩
  obtain ⟨T,Tmem,minimum⟩ := covers.exists_min_image Finset.card ⟨_,full⟩
  have cov := (Finset.mem_filter.mp Tmem).2
  let E := graph_edges n G
  let V := graph_cover T
  let own := blocks E V
  let C := coverCircuitB n own
  have ok := blocks_ok n E V (graph_hE n G)
  have valid : ∀ b∈own,b.1<n ∧ ∀ v∈b.2,v<n := fun b hb=>(ok b hb).2
  obtain ⟨ao,flat⟩ := compileFlat n own valid
  obtain ⟨cost,ev⟩ := PEqualNP.Outside.L_meta_3243.cover_all n own valid
    (fun b hb=>List.length_pos_iff.mp (ok b hb).1)
  have transfer : C.size=(coverCircuit n E V).size := by
    by_cases empty : own=[]
    · rw [size_nil n E V empty]
      simpa [C,empty] using cost
    · have unit := size_blocks n E V empty
      change (coverCircuit n E V).size+1=(own.map (fun b=>b.2.length)).sum+own.length at unit
      change C.size=(own.map (fun b=>b.2.length)).sum+own.length-1 at cost
      omega
  have eq : circuitFun n C=graphFun G ∅ := by
    funext x
    have ae := circuitFun_blocks n E V x ok
    have be := ev (List.ofFn x) List.length_ofFn
    have matchV : circuitFun n C x=circuitFun n (coverCircuit n E V) x := be.trans ae.symm
    rw [matchV,circuitFun_eq_graph n E V G (graph_hG n G) (graph_hE n G) (graph_hT n G T cov)]
    simp [graphFun]
  refine ⟨C,⟨ao,eq,?_⟩,flat⟩
  intro D dao dcorrect
  by_cases he : ∃ i j,G.Adj i j
  · have ub := size_le n (graph_edges n G) (graph_cover T) (graph_edges_ne_nil n G he)
    rw [graph_edges_length,graph_cover_length] at ub
    obtain ⟨U,hU,lower⟩ := bound D dao dcorrect
    have ct := minimum U (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU⟩)
    have edgeCount : G.edgeSet.ncard=G.edgeFinset.card := by
      rw [←Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset]
    rw [edgeCount] at lower
    change (coverCircuit n E V).size+1≤G.edgeFinset.card+T.card at ub
    omega
  · have edgeNil : E=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e mem
      obtain ⟨p,⟨_,hij⟩,_⟩ := (graph_mem_edges n G e).mp mem
      exact he ⟨p.1,p.2,hij⟩
    have ownNil : own=[] := by
      have z : (own.map (fun b=>b.2.length)).sum=0 :=
        (sum_blocks E V).trans (by rw [edgeNil]; rfl)
      cases v : own with
      | nil => rfl
      | cons b bs =>
        have pos := (ok b (show b∈own from by rw [v]; exact List.mem_cons_self)).1
        rw [v,List.map_cons,List.sum_cons] at z
        omega
    have zero := size_nil n E V ownNil
    omega


end Forest3722
namespace Pseudo3722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
def Sparse {n : Nat} (G : SimpleGraph (Fin n)) :=
  ∀ S : Finset (Fin n),{e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀ v∈e,v∈S}.ncard ≤ S.card

theorem budget {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (no4 : NoFourCycle G) (sparse : Sparse G)
    (small : ∃ T : Finset (Fin n),CoverPromise.IsVertexCover G T ∧ T.card≤5)
    (C : Circuit) (ao : IsAO2 n C) (eq : circuitFun n C=graphFun G ∅) :
    ∃ T : Finset (Fin n),CoverPromise.IsVertexCover G T ∧ G.edgeSet.ncard+T.card≤C.size+1 := by
  classical
  have no_four : ∀ a b c d : Fin n,a≠c → b≠d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d ac bd ⟨ab,bc,cd,da⟩
    exact bd (Finset.card_le_one.mp (no4 a c ac) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc.symm⟩)
      d (Finset.mem_filter.mpr ⟨Finset.mem_univ _,da.symm,cd⟩))
  have girth : ∀ v : Fin n,∀ c : G.Walk v v,c.IsCycle → c.length≠4 := by
    intro v c hc hlen
    cases c with
    | nil => simp at hlen
    | cons h1 p1 =>
      cases p1 with
      | nil => simp at hlen
      | cons h2 p2 =>
        cases p2 with
        | nil => simp at hlen
        | cons h3 p3 =>
          cases p3 with
          | nil => simp at hlen
          | cons h4 p4 =>
            cases p4 with
            | nil =>
              have hnd := hc.support_nodup
              simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
                List.tail_cons, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
                not_or] at hnd
              exact no_four _ _ _ _ (fun z=>hnd.2.1.2 z.symm) hnd.1.2.1 ⟨h1,h2,h3,h4⟩
            | cons h5 p5 =>
              simp only [SimpleGraph.Walk.length_cons] at hlen
              omega
  let covers := Finset.univ.filter (fun T : Finset (Fin n)=>CoverPromise.IsVertexCover G T)
  obtain ⟨T,tc,ts⟩ := small
  have tm : T∈covers := Finset.mem_filter.mpr ⟨Finset.mem_univ _,tc⟩
  obtain ⟨U,um,min⟩ := covers.exists_min_image Finset.card ⟨T,tm⟩
  have cover := (Finset.mem_filter.mp um).2
  have five := (min T tm).trans ts
  have mono : Monotone2 C := fun g hg=>⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  have truth (x : Fin n→Bool) : C.eval (List.ofFn x)=true ↔ ∃u v,G.Adj u v ∧ x u=true ∧ x v=true := by
    change circuitFun n C x=true ↔ _
    rw [eq]
    simp [graphFun]
  let A : Finset ℕ := (Finset.range C.size).filter
    (fun j => ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
  let O : Finset ℕ := (Finset.range C.size).filter
    (fun j => ¬ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
  have hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and := by
    intro j
    simp only [A, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    rintro ⟨g, hg, _⟩
    exact (List.getElem?_eq_some_iff.mp hg).1
  have hsum : A.card + O.card = C.size := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.range C.size)
      (fun j : ℕ => ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    rw [Finset.card_range] at h
    exact h
  have hcov : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ O := by
    intro j g hg hop
    simp only [O, Finset.mem_filter, Finset.mem_range]
    refine ⟨(List.getElem?_eq_some_iff.mp hg).1, ?_⟩
    rintro ⟨g', hg', hop'⟩
    have : g' = g := Option.some.inj (hg'.symm.trans hg)
    rw [this, hop] at hop'
    cases hop'
  have orBound := PEqualNP.Outside.L_meta_599 n G C O sparse girth mono truth hcov
  have andBound := PEqualNP.Outside.L_meta_217 n U.card G C five no_four
    (fun V vcover=>min V (Finset.mem_filter.mpr ⟨Finset.mem_univ _,vcover⟩)) mono truth A
    (fun j g jg op=>(hA j).mpr ⟨g,jg,op⟩)
  exact ⟨U,cover,by omega⟩
end Pseudo3722
namespace Sparse3722
open PEqualNP.TopForm

theorem sparse {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (no4 : NoFourCycle G)
    (triangle : ∀ a b x,G.Adj a b → G.Adj x a → ¬G.Adj x b)
    (T : Finset (Fin n)) (tc : ∀a b,G.Adj a b → a∈T ∨ b∈T) (ts : T.card≤3) :
    ∀ S : Finset (Fin n),{e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀ v∈e,v∈S}.ncard≤S.card := by
  classical
  intro S
  let U := S∩T
  let X := G.edgeFinset.filter (fun e=>∀v∈e,v∈S)
  have same : {e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀ v∈e,v∈S}=(↑X : Set (Sym2 (Fin n))) := by
    ext e
    simp [X]
  rw [same,Set.ncard_coe_finset]
  let pick (x : Fin n) := if h : ∃ v∈U,G.Adj x v then h.choose else x
  have picks {x v : Fin n} (vu : v∈U) (xv : G.Adj x v) : pick x∈U ∧ G.Adj x (pick x) := by
    have h : ∃ w∈U,G.Adj x w := ⟨v,vu,xv⟩
    simpa [pick,h] using h.choose_spec
  let P (a b : Fin n) (e : Sym2 (Fin n)) : Prop :=
    (G.Adj a b ∧ e=s(a,b)) ∨ ∃ x,G.Adj x a ∧ G.Adj x b ∧ e=s(x,if pick x=a then b else a)
  let R : Fin n ⊕ Finset (Fin n) → Sym2 (Fin n) → Prop :=
    Sum.elim (fun x e=>e=s(x,pick x)) (fun F e=>∃ a b : Fin n,a<b ∧ F={a,b} ∧ P a b e)
  let K := (S\U).disjSum (U.powersetCard 2)
  have uniqueP {a b : Fin n} (ab : a<b) {e f : Sym2 (Fin n)} (one : P a b e) (two : P a b f) : e=f := by
    rcases one with ⟨edge,ea⟩|⟨x,xa,xb,ea⟩ <;> rcases two with ⟨ed,eb⟩|⟨y,ya,yb,eb⟩
    · exact ea.trans eb.symm
    · exact (triangle a b y edge ya yb).elim
    · exact (triangle a b x ed xa xb).elim
    · have xy := Finset.card_le_one.mp (no4 a b ab.ne)
        x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xa.symm,xb.symm⟩)
        y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ya.symm,yb.symm⟩)
      subst y
      exact ea.trans eb.symm
  have unique (k) (e f : Sym2 (Fin n)) (re : R k e) (rf : R k f) : e=f := by
    cases k with
    | inl x => exact re.trans rf.symm
    | inr F =>
      obtain ⟨a,b,ab,rfl,pe⟩ := re
      obtain ⟨c,d,cd,eq,pf⟩ := rf
      have mema : a∈({c,d} : Finset (Fin n)) := by rw [←eq];simp
      have memb : b∈({c,d} : Finset (Fin n)) := by rw [←eq];simp
      simp only [Finset.mem_insert,Finset.mem_singleton] at mema memb
      have ac : a=c := by rcases mema with h|h <;> rcases memb with g|g <;> omega
      have bd : b=d := by rcases memb with g|g <;> omega
      subst c; subst d
      exact uniqueP ab pe pf
  have twoKey {a b : Fin n} (au : a∈U) (bu : b∈U) (ab : a<b) {e : Sym2 (Fin n)} (mark : P a b e) :
      ∃ k∈K,R k e := by
    refine ⟨Sum.inr {a,b},Finset.inr_mem_disjSum.mpr (Finset.mem_powersetCard.mpr ⟨?_,?_⟩),a,b,ab,rfl,mark⟩
    · intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> assumption
    · simp [ab.ne]
  have outside {x v : Fin n} (xs : x∈S) (xu : x∉U) (vu : v∈U) (xv : G.Adj x v) : ∃ k∈K,R k s(x,v) := by
    obtain ⟨pu,xp⟩ := picks vu xv
    rcases lt_trichotomy (pick x) v with pv|pv|vp
    · apply twoKey pu vu pv
      exact Or.inr ⟨x,xp,xv,by simp⟩
    · exact ⟨Sum.inl x,Finset.inl_mem_disjSum.mpr (Finset.mem_sdiff.mpr ⟨xs,xu⟩),by change s(x,v)=s(x,pick x); rw [pv]⟩
    · apply twoKey vu pu vp
      exact Or.inr ⟨x,xv,xp,by simp [vp.ne.symm]⟩
  have existsKey : ∀ e∈X,∃ k∈K,R k e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      obtain ⟨edge,ends⟩ := Finset.mem_filter.mp he
      have adj := G.mem_edgeFinset.mp edge
      have aa := ends a (by simp)
      have bb := ends b (by simp)
      by_cases au : a∈U
      · by_cases bu : b∈U
        · rcases lt_or_gt_of_ne adj.ne with ab|ba
          · exact twoKey au bu ab (Or.inl ⟨adj,rfl⟩)
          · exact twoKey bu au ba (Or.inl ⟨adj.symm,Sym2.eq_swap⟩)
        · rw [Sym2.eq_swap]
          exact outside bb bu au adj.symm
      · have bu : b∈U := Finset.mem_inter.mpr ⟨bb,(tc _ _ adj).resolve_left (fun h=>au (Finset.mem_inter.mpr ⟨aa,h⟩))⟩
        exact outside aa au bu adj
  let key (e : Sym2 (Fin n)) := if h : e∈X then (existsKey e h).choose else Sum.inr ∅
  have spec (e : Sym2 (Fin n)) (ex : e∈X) : key e∈K ∧ R (key e) e := by
    simpa [key,ex] using (existsKey e ex).choose_spec
  have price := Finset.card_le_card_of_injOn key (fun e he=>(spec e he).1)
    (fun e he f hf z=>unique (key f) e f (z ▸ (spec e he).2) (spec f hf).2)
  have cases3 (k : Nat) (hk : k≤3) : k.choose 2≤k := by interval_cases k <;> decide
  have small := cases3 U.card ((Finset.card_le_card (Finset.inter_subset_right (s₁:=S) (s₂:=T))).trans ts)
  have part := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁:=S) (s₂:=T))
  change X.card ≤ ((S\U).disjSum (U.powersetCard 2)).card at price
  rw [Finset.card_disjSum,Finset.card_powersetCard] at price
  change (S\U).card+U.card=S.card at part
  omega
end Sparse3722
namespace Forest3722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK
open PEqualNP.Outside.L_meta_3652_aux (BW)

-- Every counterexample must beat every cover circuit budget strictly.
theorem necessary (N : ℕ) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj]
    (adj : ∀ p l,I p l → G.Adj (Fin.castAdd N p) (Fin.natAdd N l))
    (fails : ¬∃ D : Circuit, IsLeastAO G D ∧ IsLiftFixedPoint G D ∧
      (∀ j<D.gates.length,(gateAt D j).op=.and → ∀t∈(gateAt D j).inputs,¬BW G D t) ∧
      PEqualNP.FactorSubst.liveSize (N+N) D=D.size ∧ doubleReread D (N+N)
        (fun w=>decide (N≤w)) ((List.finRange N).flatMap fun p=>
          ((List.finRange N).filter fun l=>decide (I p l)).map fun l=>(p.val,N+l.val))=[]) :
    ∃ D : Circuit, IsAO2 (N+N) D ∧ circuitFun (N+N) D=graphFun G ∅ ∧
      ∀ U : Finset (Fin (N+N)),CoverPromise.IsVertexCover G U → D.size+1<G.edgeSet.ncard+U.card := by
  classical
  by_contra bad
  apply fails
  obtain ⟨C,least,flat⟩ := tight (N+N) G (by
    intro D ao eq
    by_contra noCover
    apply bad
    refine ⟨D,ao,eq,?_⟩
    intro U cover
    exact lt_of_not_ge (fun budget=>noCover ⟨U,cover,budget⟩))
  exact ⟨C,least,Depth3722.result N I G C adj least flat⟩
end Forest3722

theorem Sparse3722.full : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj], (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → (∃ T : Finset (Fin (N+N)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T ∧ T.card≤3) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.Core.IsLiftFixedPoint G D ∧ (∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) ∧ PEqualNP.FactorSubst.liveSize (N + N) D = D.size ∧ PEqualNP.ReadK.doubleReread D (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val)))) = [] := by
  intro N I _ G _ incidence no4 sm _ _ _
  let col (v : Fin (N+N)) := decide (v.val<N)
  have diff (u v : Fin (N+N)) (h : G.Adj u v) : col u≠col v := by
    obtain ⟨p,l,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (incidence u v).mp h <;> simp [col,p.isLt]
  have nt (a b x : Fin (N+N)) (ab : G.Adj a b) (xa : G.Adj x a) (xb : G.Adj x b) : False := by
    have c₁ := diff a b ab
    have c₂ := diff x a xa
    have c₃ := diff x b xb
    have impossible : ∀ p q r : Bool,p≠q → r≠p → r≠q → False := by decide
    exact impossible _ _ _ c₁ c₂ c₃
  obtain ⟨T,tc,sz⟩ := sm
  have pseudo := Sparse3722.sparse G no4 nt T tc sz
  obtain ⟨D,least,flat⟩ := Forest3722.tight (N+N) G (Pseudo3722.budget G no4 pseudo ⟨T,tc,by omega⟩)
  exact ⟨D,least,Depth3722.result N I G D
    (fun p l hit=>(incidence _ _).mpr ⟨p,l,hit,Or.inl ⟨rfl,rfl⟩⟩) least flat⟩


theorem Sparse3722.throughThree : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj], (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → N≤3 → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.Core.IsLiftFixedPoint G D ∧ (∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) ∧ PEqualNP.FactorSubst.liveSize (N + N) D = D.size ∧ PEqualNP.ReadK.doubleReread D (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val)))) = [] := by
  intro N I _ G _ rel no4 nsmall C ao eq
  apply Sparse3722.full N I G rel no4 _ C ao eq
  let T := (Finset.univ : Finset (Fin N)).image (Fin.castAdd N)
  refine ⟨T,?_,?_⟩
  · intro u v uv
    obtain ⟨p,l,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (rel u v).mp uv
    · exact Or.inl (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩)
  · have h : T.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_image_le
    simpa using h.trans (by simpa using nsmall)

namespace Sparse3722
open PEqualNP.TopForm
theorem sparse_at {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (no4 : NoFourCycle G)
    (triangle : ∀ a b x,G.Adj a b → G.Adj x a → ¬G.Adj x b)
    (T : Finset (Fin n)) (tc : ∀a b,G.Adj a b → a∈T ∨ b∈T) (S : Finset (Fin n)) (ts : (S∩T).card≤3) :
    {e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀ v∈e,v∈S}.ncard≤S.card := by
  classical
  let U := S∩T
  let X := G.edgeFinset.filter (fun e=>∀v∈e,v∈S)
  have same : {e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀ v∈e,v∈S}=(↑X : Set (Sym2 (Fin n))) := by
    ext e
    simp [X]
  rw [same,Set.ncard_coe_finset]
  let pick (x : Fin n) := if h : ∃ v∈U,G.Adj x v then h.choose else x
  have picks {x v : Fin n} (vu : v∈U) (xv : G.Adj x v) : pick x∈U ∧ G.Adj x (pick x) := by
    have h : ∃ w∈U,G.Adj x w := ⟨v,vu,xv⟩
    simpa [pick,h] using h.choose_spec
  let P (a b : Fin n) (e : Sym2 (Fin n)) : Prop :=
    (G.Adj a b ∧ e=s(a,b)) ∨ ∃ x,G.Adj x a ∧ G.Adj x b ∧ e=s(x,if pick x=a then b else a)
  let R : Fin n ⊕ Finset (Fin n) → Sym2 (Fin n) → Prop :=
    Sum.elim (fun x e=>e=s(x,pick x)) (fun F e=>∃ a b : Fin n,a<b ∧ F={a,b} ∧ P a b e)
  let K := (S\U).disjSum (U.powersetCard 2)
  have uniqueP {a b : Fin n} (ab : a<b) {e f : Sym2 (Fin n)} (one : P a b e) (two : P a b f) : e=f := by
    rcases one with ⟨edge,ea⟩|⟨x,xa,xb,ea⟩ <;> rcases two with ⟨ed,eb⟩|⟨y,ya,yb,eb⟩
    · exact ea.trans eb.symm
    · exact (triangle a b y edge ya yb).elim
    · exact (triangle a b x ed xa xb).elim
    · have xy := Finset.card_le_one.mp (no4 a b ab.ne)
        x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xa.symm,xb.symm⟩)
        y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ya.symm,yb.symm⟩)
      subst y
      exact ea.trans eb.symm
  have unique (k) (e f : Sym2 (Fin n)) (re : R k e) (rf : R k f) : e=f := by
    cases k with
    | inl x => exact re.trans rf.symm
    | inr F =>
      obtain ⟨a,b,ab,rfl,pe⟩ := re
      obtain ⟨c,d,cd,eq,pf⟩ := rf
      have mema : a∈({c,d} : Finset (Fin n)) := by rw [←eq];simp
      have memb : b∈({c,d} : Finset (Fin n)) := by rw [←eq];simp
      simp only [Finset.mem_insert,Finset.mem_singleton] at mema memb
      have ac : a=c := by rcases mema with h|h <;> rcases memb with g|g <;> omega
      have bd : b=d := by rcases memb with g|g <;> omega
      subst c; subst d
      exact uniqueP ab pe pf
  have twoKey {a b : Fin n} (au : a∈U) (bu : b∈U) (ab : a<b) {e : Sym2 (Fin n)} (mark : P a b e) :
      ∃ k∈K,R k e := by
    refine ⟨Sum.inr {a,b},Finset.inr_mem_disjSum.mpr (Finset.mem_powersetCard.mpr ⟨?_,?_⟩),a,b,ab,rfl,mark⟩
    · intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> assumption
    · simp [ab.ne]
  have outside {x v : Fin n} (xs : x∈S) (xu : x∉U) (vu : v∈U) (xv : G.Adj x v) : ∃ k∈K,R k s(x,v) := by
    obtain ⟨pu,xp⟩ := picks vu xv
    rcases lt_trichotomy (pick x) v with pv|pv|vp
    · apply twoKey pu vu pv
      exact Or.inr ⟨x,xp,xv,by simp⟩
    · exact ⟨Sum.inl x,Finset.inl_mem_disjSum.mpr (Finset.mem_sdiff.mpr ⟨xs,xu⟩),by change s(x,v)=s(x,pick x); rw [pv]⟩
    · apply twoKey vu pu vp
      exact Or.inr ⟨x,xv,xp,by simp [vp.ne.symm]⟩
  have existsKey : ∀ e∈X,∃ k∈K,R k e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      obtain ⟨edge,ends⟩ := Finset.mem_filter.mp he
      have adj := G.mem_edgeFinset.mp edge
      have aa := ends a (by simp)
      have bb := ends b (by simp)
      by_cases au : a∈U
      · by_cases bu : b∈U
        · rcases lt_or_gt_of_ne adj.ne with ab|ba
          · exact twoKey au bu ab (Or.inl ⟨adj,rfl⟩)
          · exact twoKey bu au ba (Or.inl ⟨adj.symm,Sym2.eq_swap⟩)
        · rw [Sym2.eq_swap]
          exact outside bb bu au adj.symm
      · have bu : b∈U := Finset.mem_inter.mpr ⟨bb,(tc _ _ adj).resolve_left (fun h=>au (Finset.mem_inter.mpr ⟨aa,h⟩))⟩
        exact outside aa au bu adj
  let key (e : Sym2 (Fin n)) := if h : e∈X then (existsKey e h).choose else Sum.inr ∅
  have spec (e : Sym2 (Fin n)) (ex : e∈X) : key e∈K ∧ R (key e) e := by
    simpa [key,ex] using (existsKey e ex).choose_spec
  have price := Finset.card_le_card_of_injOn key (fun e he=>(spec e he).1)
    (fun e he f hf z=>unique (key f) e f (z ▸ (spec e he).2) (spec f hf).2)
  have cases3 (k : Nat) (hk : k≤3) : k.choose 2≤k := by interval_cases k <;> decide
  have small := cases3 U.card ts
  have part := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁:=S) (s₂:=T))
  change X.card ≤ ((S\U).disjSum (U.powersetCard 2)).card at price
  rw [Finset.card_disjSum,Finset.card_powersetCard] at price
  change (S\U).card+U.card=S.card at part
  omega
end Sparse3722
namespace DominatingSetPilot

open PEqualNP.Outside.L_meta_17589_aux

theorem dominating_bound {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (correct : sem_Comp n G D)
    (T : Finset (Fin n)) (dom : ∀ v, v ∉ T → ∃ t ∈ T, G v t) :
    2*n ≤ D.length + 1 + 2*T.card := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch hG h.1 correct
  obtain ⟨pos,hpos⟩ := k4_assigned hG h correct
  let J := ineligSet n D \ T
  obtain ⟨hs,hcard⟩ := k4_exits_ge hpos T J (fun i hi =>
    ⟨(Finset.mem_sdiff.mp hi).1,dom i (Finset.mem_sdiff.mp hi).2⟩)
  have hj := Finset.card_le_card hs
  rw [hcard] at hj
  have hflow := carrier_flow_union h T (by rw [sem_supp_out hG correct]; simp)
  have hsur := surplus_carrierT_le h.1 b hb T
  have hsum := surplus_identity h
  have htotal := Bplus_le_total n D
  have h1 : J.card + (ineligSet n D ∩ T).card = (ineligSet n D).card := by
    exact Finset.card_sdiff_add_card_inter _ _
  have h2 : T \ eligSet n D = ineligSet n D ∩ T := by
    ext i
    simp [ineligSet, and_comm]
  have h3 := Finset.card_sdiff_add_card_inter T (eligSet n D)
  rw [h2] at h3
  have h4 := inelig_card_add n D
  omega

theorem strict_dominating_bound {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (correct : sem_Comp n G D)
    (T : Finset (Fin n)) (dom : ∀ v, v ∉ T → ∃ t ∈ T, G v t)
    (hedge : ∃ u v t₁ t₂, t₁ ∈ T ∧ t₂ ∈ T ∧ G t₁ u ∧ G t₂ v ∧ G u v) :
    2*n < D.length + 1 + 2*T.card := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch hG h.1 correct
  obtain ⟨pos,hpos⟩ := k4_assigned hG h correct
  let J := ineligSet n D \ T
  obtain ⟨hs,hcard⟩ := k4_exits_ge hpos T J (fun i hi =>
    ⟨(Finset.mem_sdiff.mp hi).1,dom i (Finset.mem_sdiff.mp hi).2⟩)
  have hj := Finset.card_le_card hs
  rw [hcard] at hj
  have hflow := carrier_flow_union h T (by rw [sem_supp_out hG correct]; simp)
  have hsur := surplus_carrierT_le h.1 b hb T
  have hsum := surplus_identity h
  have htotal := Bplus_le_total n D
  have h1 : J.card + (ineligSet n D ∩ T).card = (ineligSet n D).card := by
    exact Finset.card_sdiff_add_card_inter _ _
  have h2 : T \ eligSet n D = ineligSet n D ∩ T := by
    ext i
    simp [ineligSet, and_comm]
  have h3 := Finset.card_sdiff_add_card_inter T (eligSet n D)
  rw [h2] at h3
  have h4 := inelig_card_add n D
  by_contra hsmall
  have hem : merges n D (carrierT n D T) = ∅ := Finset.card_eq_zero.mp (by omega)
  have heq : J.image pos = exitArcs n D (carrierT n D T) :=
    Finset.eq_of_subset_of_card_le hs (by omega)
  have inactive (t v : Fin n) (ht : t ∈ T) (hv : G t v) : v ∈ ineligSet n D := by
    obtain ⟨j,hr,hAnd,_,_,_,s,hleft,_,hright,_⟩ := sem_joint_meeting hG h.1 correct hv
    have noU : ¬ (supp n D (n+j) ∩ T).Nonempty := by
      rintro ⟨w,hw⟩
      obtain ⟨ho,hwT⟩ := Finset.mem_inter.mp hw
      have hwo := ho
      rw [sem_supp_and h.1 hr hAnd, Finset.mem_inter] at hwo
      have hm : j ∈ merges n D (carrierT n D T) := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hr, k4_mem_carrier.mpr ⟨w,Finset.mem_inter.mpr ⟨ho,hwT⟩⟩,
          k4_mem_carrier.mpr ⟨w,Finset.mem_inter.mpr ⟨hwo.1,hwT⟩⟩,
          k4_mem_carrier.mpr ⟨w,Finset.mem_inter.mpr ⟨hwo.2,hwT⟩⟩⟩
      rw [hem] at hm
      exact Finset.notMem_empty j hm
    have hx : (j,s) ∈ exitArcs n D (carrierT n D T) :=
      k4_mem_exit.mpr ⟨hr,⟨t, Finset.mem_inter.mpr ⟨hleft,ht⟩⟩,noU⟩
    rw [← heq] at hx
    obtain ⟨i,hi,hiPos⟩ := Finset.mem_image.mp hx
    have hin := (Finset.mem_sdiff.mp hi).1
    have onlyI := (hpos.1 i hin).2.2.2
    rw [hiPos] at onlyI
    change supp n D (src D (j,!s)) = {i} at onlyI
    rw [onlyI, Finset.mem_singleton] at hright
    exact hright.symm ▸ hin
  obtain ⟨u,v,t₁,t₂,ht₁,ht₂,hu,hv,huv⟩ := hedge
  rcases sem_elig_cover hG h correct huv with eu|ev
  · exact (sem_mem_inelig.mp (inactive t₁ u ht₁ hu)) eu
  · exact (sem_mem_inelig.mp (inactive t₂ v ht₂ hv)) ev

end DominatingSetPilot

namespace Four3722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK
open PEqualNP.Outside.L_meta_17589_aux
theorem circuitDom {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : NoFourCycle G) (hdeg : ∀ v, 2 ≤ G.degree v)
    (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ sem_Edge G.Adj x) :
    ∀ (T : Finset (Fin n)), (∀ v, v ∉ T → ∃ t ∈ T, G.Adj v t) →
      (∃ u v t₁ t₂, t₁ ∈ T ∧ t₂ ∈ T ∧ G.Adj t₁ u ∧ G.Adj t₂ v ∧ G.Adj u v) →
        2*n < C.size+1+2*T.card := by
  intro T dom internal
  classical
  by_cases hn : n = 0
  · subst n
    obtain ⟨v,_⟩ := internal
    exact Fin.elim0 v
  have two (v : Fin n) : ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b := by
    have hd : 1 < (G.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hdeg v
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hd
    exact ⟨a, b, (G.mem_neighborFinset v a).mp ha, (G.mem_neighborFinset v b).mp hb, hab⟩
  have hg : sem_Gr G.Adj := by
    refine ⟨fun _ _ h => h.symm, fun v => G.loopless.irrefl v, ?_, ?_⟩
    · intro v w hvw
      obtain ⟨a,b,ha,hb,hab⟩ := two v
      by_cases hwa : G.Adj w a
      · refine ⟨b,hb,fun hwb => ?_⟩
        have both : 1 < (Finset.univ.filter fun t => G.Adj v t ∧ G.Adj w t).card :=
          Finset.one_lt_card.mpr ⟨a, by simp [ha,hwa], b, by simp [hb,hwb], hab⟩
        exact (Nat.not_lt_of_ge (hfree v w hvw)) both
      · exact ⟨a,ha,hwa⟩
    · intro u v
      obtain ⟨a,b,ha,hb,hab⟩ := two u
      by_cases hav : a = v
      · exact ⟨b,hb,fun h => hab (hav.trans h.symm)⟩
      · exact ⟨a,ha,hav⟩
  have nosingle (i : Fin n) : ¬ sem_Edge G.Adj (fun k => decide (k = i)) := by
    rintro ⟨u,v,huv,hu,hv⟩
    have hui : u = i := of_decide_eq_true hu
    have hvi : v = i := of_decide_eq_true hv
    exact huv.ne (hui.trans hvi.symm)
  have positive (i j : Fin n) (hij : G.Adj i j) :
      sem_Edge G.Adj (fun k => decide (k = i) || decide (k = j)) :=
    ⟨i,j,hij,by simp,by simp⟩
  obtain ⟨D,hlive,hlen,hval⟩ := normalize_strictLive (n := n) C hmono
    (by
      intro b
      let v : Fin n := ⟨0, by omega⟩
      cases b
      · obtain ⟨u,_,hu,_,_⟩ := two v
        refine ⟨fun k => decide (k = v) || decide (k = u), ?_⟩
        rw [Ne, Bool.not_eq_false]
        exact (hC _).2 (positive v u hu)
      · exact ⟨fun k => decide (k = v), fun he => nosingle v ((hC _).1 he)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun he => nosingle i ((hC _).1 ?_)⟩
      rw [he]
      simp)
    (by
      intro i
      obtain ⟨j,_,hij,_,_⟩ := two i
      refine ⟨fun k => decide (k = j), fun k => decide (k = i) || decide (k = j),
        fun k hk => by simp [hk], fun he => nosingle j ((hC _).1 ?_)⟩
      rw [he]
      exact (hC _).2 (positive i j hij))
  have hcomp : sem_Comp n G.Adj D := fun x => by rw [hval x]; exact hC x
  have charge := DominatingSetPilot.strict_dominating_bound hg hlive hcomp T dom internal
  omega

def side (v : Fin 8) := decide (4≤v.val)
def group (b : Bool) : Finset (Fin 8) := Finset.univ.filter fun v => side v=b
theorem groupCard (b : Bool) : (group b).card=4 := by cases b <;> decide +kernel
theorem inGroup {v : Fin 8} {b : Bool} : v∈group b ↔ side v=b := by simp [group]
theorem diffBool {a b : Bool} (ne : a≠b) : b= !a := by cases a <;> cases b <;> simp_all
theorem triangleFree {G : SimpleGraph (Fin 8)} (cross : ∀ u v,G.Adj u v → side u≠side v) :
    ∀ a b x,G.Adj a b → G.Adj x a → ¬G.Adj x b := by
  intro a b x ab xa xb
  exact (cross a b ab) ((diffBool (cross x a xa)).trans (diffBool (cross x b xb)).symm)
theorem sideCover {G : SimpleGraph (Fin 8)} (cross : ∀ u v,G.Adj u v → side u≠side v) (b : Bool) :
    CoverPromise.IsVertexCover G (group b) := by
  intro u v uv
  simp only [inGroup]
  have xy := cross u v uv
  cases b <;> cases e : side u <;> cases f : side v <;> simp_all

theorem properSparse (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj] (no4 : NoFourCycle G)
    (cross : ∀ u v,G.Adj u v → side u≠side v) (S : Finset (Fin 8)) (v : Fin 8) (vs : v∉S) :
    {e : Sym2 (Fin 8) | e∈G.edgeSet ∧ ∀ w∈e,w∈S}.ncard≤S.card := by
  let T := group (side v)
  have sub : S∩T ⊆ T.erase v := by
    intro w hw
    obtain ⟨ws,wt⟩ := Finset.mem_inter.mp hw
    exact Finset.mem_erase.mpr ⟨fun h => vs (h ▸ ws),wt⟩
  have card := Finset.card_le_card sub
  have vt : v∈T := inGroup.mpr rfl
  rw [Finset.card_erase_of_mem vt] at card
  change _ ≤ (group (side v)).card - 1 at card
  rw [groupCard] at card
  exact Sparse3722.sparse_at G no4 (triangleFree cross) T (sideCover cross _) S card

theorem denseMinimum (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj] (no4 : NoFourCycle G)
    (cross : ∀ u v,G.Adj u v → side u≠side v) (dense : 8<G.edgeSet.ncard) :
    ∀ v, 2≤G.degree v := by
  intro v
  let S := (Finset.univ : Finset (Fin 8)).erase v
  let away := G.edgeFinset \ G.incidenceFinset v
  have hA : {e : Sym2 (Fin 8) | e∈G.edgeSet ∧ ∀ w∈e,w∈S}=(↑away : Set (Sym2 (Fin 8))) := by
    ext e
    simp only [Finset.mem_coe,Finset.mem_sdiff,SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_incidenceFinset,S,Finset.mem_erase,Finset.mem_univ,and_true,Set.mem_setOf_eq,
      SimpleGraph.incidenceSet, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨he,hv⟩
      exact ⟨he, fun h => (hv v h.2) rfl⟩
    · rintro ⟨he,hv⟩
      exact ⟨he,fun w hw e => hv ⟨he,e ▸ hw⟩⟩
  have sparse := properSparse G no4 cross S v (by simp [S])
  rw [hA,Set.ncard_coe_finset] at sparse
  have s7 : S.card=7 := by
    simp [S,Finset.card_erase_of_mem]
  have sub : G.incidenceFinset v ⊆ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.mem_incidenceFinset.mp he).1
  have sum := Finset.card_sdiff_add_card_eq_card sub
  change away.card+(G.incidenceFinset v).card=G.edgeFinset.card at sum
  rw [SimpleGraph.card_incidenceFinset_eq_degree] at sum
  have edgeCount : G.edgeSet.ncard=G.edgeFinset.card := by
    rw [←Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset]
  omega

theorem denseGeometry (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj] (no4 : NoFourCycle G)
    (cross : ∀ u v,G.Adj u v → side u≠side v) (dense : 8<G.edgeSet.ncard) :
    G.edgeSet.ncard ≤ 9 ∧ ∃ T : Finset (Fin 8), T.card≤2 ∧
    (∀ v,v∉T → ∃ t∈T,G.Adj v t) ∧
    ∃ u v t₁ t₂, t₁∈T ∧ t₂∈T ∧ G.Adj t₁ u ∧ G.Adj t₂ v ∧ G.Adj u v := by
  classical
  let A := G.neighborFinset
  have ac (v) : (A v).card=G.degree v := G.card_neighborFinset_eq_degree v
  have mem (a b) : b ∈ A a ↔ G.Adj a b := G.mem_neighborFinset a b
  have contained (v) : A v ⊆ group (!(side v)) := by
    intro w hw
    exact inGroup.mpr (diffBool (cross v w ((mem v w).mp hw)))
  have overlap (v w : Fin 8) (vw : v≠w) : (A v∩A w).card ≤ 1 := by
    refine (Finset.card_le_card ?_).trans (no4 v w vw)
    intro t ht
    obtain ⟨a,b⟩ := Finset.mem_inter.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem v t).mp a,(mem w t).mp b⟩
  have cap (v w : Fin 8) (vw : v≠w) (same : side v=side w) : G.degree v+G.degree w≤5 := by
    have sub : A v ∪ A w ⊆ group (!(side w)) := Finset.union_subset (same ▸ contained v) (contained w)
    have h := Finset.card_le_card sub
    rw [groupCard] at h
    have i := overlap v w vw
    have u := Finset.card_union_add_card_inter (A v) (A w)
    rw [ac,ac] at u
    omega
  have mindeg := denseMinimum G no4 cross dense
  have maxdeg (v : Fin 8) : G.degree v≤3 := by
    have many : 1 < (group (side v)).card := by rw [groupCard]; decide
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp many
    by_cases av : a=v
    · have r := cap b v (fun bv => ab (av.trans bv.symm)) (inGroup.mp hb)
      have := mindeg b
      omega
    · have r := cap a v av (inGroup.mp ha)
      have := mindeg a
      omega
  let H : Finset (Fin 8) := Finset.univ.filter fun v => G.degree v=3
  have hmem (v) : v∈H ↔ G.degree v=3 := by simp [H]
  have onePer (b : Bool) : (H∩group b).card≤1 := by
    refine Finset.card_le_one.mpr fun u hu v hv => ?_
    by_contra ne
    obtain ⟨uc,us⟩ := Finset.mem_inter.mp hu
    obtain ⟨vc,vs⟩ := Finset.mem_inter.mp hv
    have c := cap u v ne ((inGroup.mp us).trans (inGroup.mp vs).symm)
    rw [(hmem u).mp uc,(hmem v).mp vc] at c
    omega
  have splitH : H=(H∩group false)∪(H∩group true) := by
    ext v
    cases e : side v <;> simp [inGroup,e]
  have hle : H.card≤2 := by
    have c := Finset.card_union_le (H∩group false) (H∩group true)
    rw [← splitH] at c
    have h1 := onePer false
    have h2 := onePer true
    omega
  have ds : (∑ v : Fin 8, G.degree v)=16+H.card := by
    have eq (v : Fin 8) : G.degree v=2+(if G.degree v=3 then 1 else 0) := by
      have := maxdeg v
      have := mindeg v
      split <;> omega
    simp only [Finset.sum_congr rfl (fun v _=>eq v),Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    simp [H,Finset.card_filter]
  have total := G.sum_degrees_eq_twice_card_edges
  have edgeCount : G.edgeSet.ncard=G.edgeFinset.card := by
    rw [←Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset]
  have exactH : H.card=2 := by omega
  refine ⟨by omega,?_⟩
  obtain ⟨p,hp,l,hl,pl⟩ := Finset.one_lt_card.mp (show 1<H.card by omega)
  have pd := (hmem p).mp hp
  have ld := (hmem l).mp hl
  have sep : side p≠side l := by
    intro eq
    have c := cap p l pl eq
    omega
  have rest (v : Fin 8) (on : G.degree v=3) : (group (!(side v)) \ A v).card=1 := by
    have c := Finset.card_sdiff_add_card_eq_card (contained v)
    rw [groupCard,ac,on] at c
    omega
  have dis : ¬ G.Adj p l := by
    intro link
    have lp : p∈A l := (mem l p).mpr link.symm
    have rm : 1<((A l).erase p).card := by rw [Finset.card_erase_of_mem lp,ac,ld]; decide
    obtain ⟨r,hr,s,hs,rs⟩ := Finset.one_lt_card.mp rm
    have other (u : Fin 8) (hu : u∈(A l).erase p) :
        ∃ w∈group (!(side p)) \ A p, G.Adj u w := by
      obtain ⟨up,lu⟩ := Finset.mem_erase.mp hu
      have ul := (mem l u).mp lu
      have us : side u=side p := (diffBool (cross l u ul)).trans (diffBool (cross l p link.symm)).symm
      have existsOff : ¬ A u ⊆ A p := by
        intro inside
        have e : A u∩A p=A u := Finset.inter_eq_left.mpr inside
        have h := overlap u p up
        rw [e,ac] at h
        have := mindeg u
        omega
      obtain ⟨w,wu,wp⟩ := Finset.not_subset.mp existsOff
      refine ⟨w,Finset.mem_sdiff.mpr ⟨?_,wp⟩,(mem u w).mp wu⟩
      simpa only [us] using contained u wu
    obtain ⟨a,ha,ra⟩ := other r hr
    obtain ⟨b,hb,sb⟩ := other s hs
    have ab : a=b := Finset.card_le_one.mp (rest p pd).le a ha b hb
    have common (w : Fin 8) (rw : G.Adj r w) (sw : G.Adj s w) : w∈A r∩A s :=
      Finset.mem_inter.mpr ⟨(mem r w).mpr rw,(mem s w).mpr sw⟩
    have la : l=a := Finset.card_le_one.mp (overlap r s rs) l
      (common l ((mem l r).mp (Finset.mem_of_mem_erase hr)).symm
        ((mem l s).mp (Finset.mem_of_mem_erase hs)).symm) a (common a ra (ab ▸ sb))
    exact (Finset.mem_sdiff.mp ha).2 (la ▸ (mem p l).mpr link)
  have fill (x y : Fin 8) (d : G.degree x=3) (op : side x≠side y) (off : ¬G.Adj x y)
      (v : Fin 8) (sv : side v=side y) (vy : v≠y) : G.Adj x v := by
    by_contra not
    have yg : y∈group (!(side x)) := inGroup.mpr (diffBool op)
    have vg : v∈group (!(side x)) := inGroup.mpr (sv.trans (diffBool op))
    exact vy (Finset.card_le_one.mp (rest x d).le v (Finset.mem_sdiff.mpr
      ⟨vg,fun m=>not ((mem x v).mp m)⟩) y (Finset.mem_sdiff.mpr ⟨yg,fun m=>off ((mem x y).mp m)⟩))
  let T : Finset (Fin 8) := {p,l}
  refine ⟨T,Finset.card_le_two,?_,?_⟩
  · intro v hv
    have vp : v≠p := fun eq=>hv (eq ▸ Finset.mem_insert_self _ _)
    have vl : v≠l := fun eq=>hv (eq ▸ (by simp [T]))
    by_cases sv : side v=side l
    · exact ⟨p,by simp [T],(fill p l pd sep dis _ sv vl).symm⟩
    · have sp : side v=side p := (diffBool (Ne.symm sv)).trans (diffBool (Ne.symm sep)).symm
      exact ⟨l,by simp [T],(fill l p ld (Ne.symm sep) (fun h=>dis h.symm) _ sp vp).symm⟩
  · obtain ⟨u,pu⟩ := Finset.card_pos.mp (show 0<(A p).card by rw [ac,pd]; decide)
    have pu' := (mem p u).mp pu
    have up : p∈A u := (mem u p).mpr pu'.symm
    have val : 0<((A u).erase p).card := by
      rw [Finset.card_erase_of_mem up,ac]
      have := mindeg u
      omega
    obtain ⟨v,hv⟩ := Finset.card_pos.mp val
    obtain ⟨vp,uv⟩ := Finset.mem_erase.mp hv
    have uv' := (mem u v).mp uv
    have same : side v=side p := (diffBool (cross u v uv')).trans (diffBool (cross u p pu'.symm)).symm
    exact ⟨u,v,p,l,by simp [T],by simp [T],pu',fill l p ld (Ne.symm sep) (fun h=>dis h.symm) _ same vp,uv'⟩

theorem fourBudget (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj] (no4 : NoFourCycle G)
    (cross : ∀ u v, G.Adj u v → side u ≠ side v) (C : Circuit)
    (ao : IsAO2 8 C) (eq : circuitFun 8 C=graphFun G ∅) :
    ∃ U : Finset (Fin 8), CoverPromise.IsVertexCover G U ∧ G.edgeSet.ncard+U.card≤C.size+1 := by
  classical
  by_cases dense : 8<G.edgeSet.ncard
  · obtain ⟨edge,T,two,dom,intern⟩ := denseGeometry G no4 cross dense
    have tr (x : Fin 8 → Bool) : C.eval (List.ofFn x)=true ↔ sem_Edge G.Adj x := by
      change circuitFun 8 C x=true ↔ _
      rw [eq]
      simp [graphFun,sem_Edge]
    have h := circuitDom G no4 (denseMinimum G no4 cross dense) C
      (fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩) tr T dom intern
    refine ⟨group false,sideCover cross false,?_⟩
    rw [groupCard]
    omega
  · apply Pseudo3722.budget G no4 _ ⟨group false,sideCover cross false,(groupCard false).le.trans (by decide)⟩ C ao eq
    intro S
    by_cases full : S=Finset.univ
    · subst S
      simpa using (Nat.le_of_not_gt dense)
    · obtain ⟨v,hv⟩ : ∃ v, v∉S := by
        by_contra! all
        exact full (Finset.eq_univ_iff_forall.mpr all)
      exact properSparse G no4 cross S v hv

theorem throughFour : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj], (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → N≤4 → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.Core.IsLiftFixedPoint G D ∧ (∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) ∧ PEqualNP.FactorSubst.liveSize (N + N) D = D.size ∧ PEqualNP.ReadK.doubleReread D (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val)))) = [] := by
  intro N I _ G _ incidence no4 small C ao eq
  by_cases low : N≤3
  · exact Sparse3722.throughThree N I G incidence no4 low C ao eq
  have four : N=4 := by omega
  subst N
  have different (p l : Fin 4) : side (Fin.castAdd 4 p)≠side (Fin.natAdd 4 l) := by
    have lo : ¬ 4≤(Fin.castAdd 4 p).val := Nat.not_le.mpr p.isLt
    have hi : 4≤(Fin.natAdd 4 l).val := by rw [Fin.val_natAdd]; omega
    simp only [side,lo,hi,decide_false,decide_true,Bool.false_ne_true,not_false_eq_true]
  have cross (u v : Fin 8) (uv : G.Adj u v) : side u≠side v := by
    obtain ⟨p,l,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (incidence u v).mp uv
    · exact different p l
    · exact (different p l).symm
  obtain ⟨D,least,flat⟩ := Forest3722.tight 8 G (fourBudget G no4 cross)
  exact ⟨D,least,Depth3722.result 4 I G D
    (fun p l hit=>(incidence _ _).mpr ⟨p,l,hit,Or.inl ⟨rfl,rfl⟩⟩) least flat⟩

end Four3722
