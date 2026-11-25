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
