import PEqualNP.Outside.L_meta_2264
import PEqualNP.Outside.L_meta_5242

namespace Shared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.Local1490
open PEqualNP.Outside.L_meta_5242.Structural (inCone_trans inCone_lt and_ancestor_junk)

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

-- The backwards induction follows the cone recursion from L_meta_5242.Structural.upper_reaches.
theorem access (ao : IsAO2 n C) (form : TopForm G C) {d e a : ℕ}
    (junkEq : junk G C={d,e}) (inc : ¬InCone n C d e) (ha : a∈tops G C)
    (da : InCone n C d a) : ∃ b : Fin 2, OrReaches n C (opnd C a b) d := by
  have dj : d∈junk G C := by rw [junkEq]; simp
  have dlen := (junkData dj).1
  obtain ⟨alen,aop,_⟩ := topData ha
  have go : ∀ k, InCone n C k a → (d=k ∨ InCone n C d k) → OrReaches n C (n+k) d := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro ka rel
      rcases rel with rfl | dk
      · exact (orReaches_iff n C d d).mpr ⟨dlen,Or.inl rfl⟩
      · obtain ⟨klen,t,tk,mem,dt⟩ := (inCone_iff n C d k).mp dk
        have kop : (gateAt C k).op=GateOp.or := by
          rcases ao.1 _ (gateAt_mem klen) with kand | kor
          · have kj := and_ancestor_junk form alen aop klen kand ka
            have kn : k=d ∨ k=e := by simpa only [junkEq,Finset.mem_insert,Finset.mem_singleton] using kj
            rcases kn with rfl | rfl
            · exact (Nat.lt_irrefl _ (inCone_lt dk)).elim
            · exact (inc dk).elim
          · exact kor
        have tc : InCone n C t k := (inCone_iff n C t k).mpr ⟨klen,t,tk,mem,Or.inl rfl⟩
        exact (orReaches_iff n C k d).mpr ⟨klen,Or.inr ⟨kop,n+t,mem,by omega,ih t tk (inCone_trans tc ka) dt⟩⟩
  obtain ⟨_,k,ka,mem,dk⟩ := (inCone_iff n C d a).mp da
  have ka' : InCone n C k a := (inCone_iff n C k a).mpr ⟨alen,k,ka,mem,Or.inl rfl⟩
  obtain ⟨b,hb⟩ := inputsAsOpnd ao alen mem
  exact ⟨b,hb ▸ go k ka' dk⟩

theorem no_both (ao : IsAO2 n C) {a d : ℕ} (ha : a∈tops G C) (dj : d∈junk G C)
    {b : Fin 2} (r : OrReaches n C (opnd C a b) d) :
    ¬ OrReaches n C (opnd C a (1-b)) d := by
  intro r'
  obtain ⟨al,op,clean⟩ := topData ha
  obtain ⟨_,_,x,hx,off⟩ := junkData dj
  have on : gateVal n C a x=true := (andValOperands ao al op x).mpr (fun c => by
    rcases eitherOperand b c with rfl | rfl
    · exact reachVal r hx
    · exact reachVal r' hx)
  rw [clean x on] at off
  contradiction

theorem shared_cases (ao : IsAO2 n C) (form : TopForm G C) {d e a : ℕ}
    (junkEq : junk G C={d,e}) (de : ¬InCone n C d e) (ed : ¬InCone n C e d)
    (ha : a∈tops G C) (da : InCone n C d a) (ea : InCone n C e a) :
    (∀ x, gateVal n C d x=true → gateVal n C e x=true → graphFun G ∅ x=true) ∨
      (wmax G C d ∩ wmax G C e).Nonempty := by
  classical
  obtain ⟨i,ri⟩ := access ao form junkEq de ha da
  have hswap : junk G C={e,d} := junkEq.trans (Finset.pair_comm _ _)
  obtain ⟨j,rj⟩ := access ao form hswap ed ha ea
  obtain ⟨al,op,clean⟩ := topData ha
  rcases eitherOperand i j with rfl | rfl
  · right
    have pure (k) (rk : OrReaches n C (opnd C a (1-i)) k) (opk : (gateAt C k).op=GateOp.and) : False := by
      have dirty := operandOrAndJunk ao form al op rk opk
      have num : k=d ∨ k=e := by simpa only [junkEq,Finset.mem_insert,Finset.mem_singleton] using dirty
      rcases num with rfl | rfl
      · exact no_both ao ha dirty ri rk
      · exact no_both ao ha dirty rj rk
    have bound := opndBound ao al (1-i)
    obtain ⟨v,hv⟩ := pureOrNonempty ao (by omega : opnd C a (1-i)<n+C.gates.length) pure
    exact ⟨v,Finset.mem_inter.mpr ⟨oppositeSideWmax ao ha ri hv,oppositeSideWmax ao ha rj hv⟩⟩
  · left
    intro x xd xe
    apply clean x
    apply (andValOperands ao al op x).mpr
    intro b
    rcases eitherOperand i b with rfl | rfl
    · exact reachVal ri xd
    · exact reachVal rj xe

end Shared2262
namespace Shared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.Local1490

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

-- A direct reader of an empty, dirty wire cannot belong to lambda.
theorem first_charge (ao : IsAO2 n C) {w h : ℕ} (hn : (orIn n C w).Nonempty)
    (empty : orIn n C (n+h)=∅) (dirty : ∃ x, gateVal n C h x=true ∧ graphFun G ∅ x=false)
    (route : OrReaches n C w h) : ∃ m∈orN G C \ lam G C,
      OrReaches n C w m ∧ n+h∈(gateAt C m).inputs ∧ h<m := by
  rcases Relation.ReflTransGen.cases_tail (orReaches_reach h w route).1 with he | ⟨r,path,step⟩
  · rw [← he,empty] at hn
    exact (Finset.not_nonempty_empty hn).elim
  · obtain ⟨m,ml,rfl,op,read,lt⟩ := step
    obtain ⟨x,hx,off⟩ := dirty
    have mon : gateVal n C m x=true := (val_or (n := n) (by simp) ml op).mpr ⟨n+h,read,lt,hx⟩
    have pay : m∈orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ml,op,fun clean =>
      Bool.false_ne_true (off ▸ clean x mon)⟩
    refine ⟨m,Finset.mem_sdiff.mpr ⟨pay,?_⟩,reach_orReaches path m rfl ml,read,by omega⟩
    intro hlam
    obtain ⟨_,h0,h1,_⟩ := Finset.mem_filter.mp hlam
    obtain ⟨b,hb⟩ := inputsAsOpnd ao ml read
    rw [hb] at empty
    fin_cases b
    · exact Finset.not_nonempty_iff_eq_empty.mpr empty h0
    · exact Finset.not_nonempty_iff_eq_empty.mpr empty h1

theorem shared_price (ao : IsAO2 n C) (form : TopForm G C) {d e a : ℕ}
    (ne : d ≠ e) (junkEq : junk G C={d,e}) (de : ¬InCone n C d e) (ed : ¬InCone n C e d)
    (ha : a∈tops G C) (da : InCone n C d a) (ea : InCone n C e a) :
    2≤2*(centreless G C).card+(orN G C \ lam G C).card := by
  classical
  by_cases ac : a∈centreless G C
  · have h := Finset.card_pos.mpr ⟨a,ac⟩
    omega
  have raw (i : Fin 2) : (orIn n C (opnd C a i)).Nonempty := by
    by_contra h
    have empty := Finset.not_nonempty_iff_eq_empty.mp h
    apply ac
    apply Finset.mem_filter.mpr
    refine ⟨ha,?_⟩
    fin_cases i
    · exact Or.inl empty
    · exact Or.inr empty
  obtain ⟨i,ri⟩ := access ao form junkEq de ha da
  obtain ⟨j,rj⟩ := access ao form (junkEq.trans (Finset.pair_comm _ _)) ed ha ea
  have dj : d∈junk G C := by rw [junkEq]; simp
  have ej : e∈junk G C := by rw [junkEq]; simp
  obtain ⟨_,dop,dd⟩ := junkData dj
  obtain ⟨_,eop,ee⟩ := junkData ej
  obtain ⟨m,mp,rm,dm,_⟩ := first_charge ao (raw i) (orInAnd dop) dd ri
  obtain ⟨z,zp,_,ez,_⟩ := first_charge ao (raw j) (orInAnd eop) ee rj
  by_cases mz : m=z
  · subst z
    obtain ⟨hm,om,dirtym⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp mp).1
    have ml := Finset.mem_range.mp hm
    obtain ⟨l,r,lr⟩ := binaryInputs ao ml
    have sides (b : Fin 2) : opnd C m b=n+d ∨ opnd C m b=n+e := by
      have dd := dm
      have ee := ez
      rw [lr] at dd ee
      simp only [List.mem_cons,List.not_mem_nil,or_false] at dd ee
      have ls : opnd C m 0=l := by simp [opnd,lr]
      have rs : opnd C m 1=r := by simp [opnd,lr]
      fin_cases b
      · rw [ls]
        rcases dd with dd|dd <;> rcases ee with ee|ee <;> omega
      · rw [rs]
        rcases dd with dd|dd <;> rcases ee with ee|ee <;> omega
    have sempty (b : Fin 2) : side (n := n) C m b=∅ := by
      unfold side
      rcases sides b with h|h
      · rw [h,orInAnd dop]
      · rw [h,orInAnd eop]
    have em : orIn n C (n+m) = ∅ := by rw [orInOr ao ml om,sempty 0,sempty 1,Finset.empty_union]
    have dirty : ∃ x, gateVal n C m x=true ∧ graphFun G ∅ x=false := by
      by_contra h
      apply dirtym
      intro x hx
      by_contra off
      exact h ⟨x,hx,Bool.eq_false_iff.mpr off⟩
    obtain ⟨k,kp,_,_,mk⟩ := first_charge ao (raw i) em dirty rm
    have two := Finset.one_lt_card_iff.mpr ⟨m,k,mp,kp,mk.ne⟩
    omega
  · have two := Finset.one_lt_card_iff.mpr ⟨m,z,mp,zp,mz⟩
    omega

end Shared2262
