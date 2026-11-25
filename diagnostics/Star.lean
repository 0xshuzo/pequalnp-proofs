import Mathlib
import PEqualNP.Defs
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
