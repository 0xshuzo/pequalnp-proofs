import PEqualNP.Outside.L_meta_17265
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

namespace Ten3722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK
open PEqualNP.Outside.L_meta_17265_aux
open LeafCore3241 ForestBipartite3241 MatrixPacking3241

theorem tenBudget {N : ℕ} (I : Fin N→Fin N→Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj]
    (inc : ∀ a b,G.Adj a b ↔ ∃ p l, I p l ∧
      ((a=Fin.castAdd N p ∧ b=Fin.natAdd N l) ∨ (a=Fin.natAdd N l ∧ b=Fin.castAdd N p)))
    (no4 : NoFourCycle G) (small : G.edgeSet.ncard≤10) (C : Circuit) (ao : IsAO2 (N+N) C)
    (eq : circuitFun (N+N) C=graphFun G ∅) :
    ∃ U : Finset (Fin (N+N)), CoverPromise.IsVertexCover G U ∧ G.edgeSet.ncard+U.card≤C.size+1 := by
  classical
  let E := (Finset.univ : Finset (Fin N × Fin N)).filter fun e=>I e.1 e.2
  have memE (p l : Fin N) : (p,l)∈E ↔ I p l := by simp [E]
  have same : G=bip E := by
    ext a b
    constructor
    · intro h
      obtain ⟨p,l,pl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (inc a b).mp h
      · exact bip_adjacency ((memE p l).mpr pl)
      · exact (bip_adjacency ((memE p l).mpr pl)).symm
    · intro h
      rcases h with ⟨_,⟨⟨p,l⟩,he,rfl,rfl⟩|⟨⟨p,l⟩,he,rfl,rfl⟩⟩
      · exact (inc _ _).mpr ⟨p,l,(memE p l).mp he,Or.inl ⟨rfl,rfl⟩⟩
      · exact (inc _ _).mpr ⟨p,l,(memE p l).mp he,Or.inr ⟨rfl,rfl⟩⟩
  subst G
  have free : FourFree E := by
    intro p q l s pq ls e₁ e₂ e₃ e₄
    have ne : Fin.castAdd N p≠Fin.castAdd N q := fun e=>pq (Fin.castAdd_inj.mp e)
    have one := no4 _ _ ne
    have eq := Finset.card_le_one.mp one (Fin.natAdd N l) (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,bip_adjacency e₁,bip_adjacency e₃⟩) (Fin.natAdd N s) (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,bip_adjacency e₂,bip_adjacency e₄⟩)
    exact ls (Fin.natAdd_injective N N eq)
  have ec : (bip E).edgeSet.ncard=(bip E).edgeFinset.card := by
    rw [←Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset]
  have size : E.card≤10 := by rwa [ec,bip_edges] at small
  have counts := MatrixPacking3241.full E free size NormalizeCores3241.census
  obtain ⟨S,cv,price⟩ := bound_of_counts (bip E) counts C ao (eq.trans (ordinary_eq _))
  exact ⟨S,fun u v edge=>by simpa using cv edge,by simpa only [ec] using price⟩

theorem edgesTen : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj], (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → G.edgeSet.ncard≤10 → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.Core.IsLiftFixedPoint G D ∧ (∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) ∧ PEqualNP.FactorSubst.liveSize (N + N) D = D.size ∧ PEqualNP.ReadK.doubleReread D (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val)))) = [] := by
  intro N I _ G _ inc no4 ten C ao eq
  obtain ⟨D,least,flat⟩ := Forest3722.tight (N+N) G (tenBudget I G inc no4 ten)
  exact ⟨D,least,Depth3722.result N I G D
    (fun p l hit=>(inc _ _).mpr ⟨p,l,hit,Or.inl ⟨rfl,rfl⟩⟩) least flat⟩

end Ten3722
