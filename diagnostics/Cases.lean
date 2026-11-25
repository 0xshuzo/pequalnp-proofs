import PEqualNP.Outside.L_meta_2264
import PEqualNP.Outside.L_meta_5242
import PEqualNP.Outside.L_meta_2693

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
  rcases eitherOperand i j with ij | ij
  · rw [ij] at rj
    right
    have pure (k) (rk : OrReaches n C (opnd C a (1-i)) k) (opk : (gateAt C k).op=GateOp.and) : False := by
      have dirty := operandOrAndJunk ao form al op rk opk
      have num : k=d ∨ k=e := by simpa only [junkEq,Finset.mem_insert,Finset.mem_singleton] using dirty
      rcases num with rfl | rfl
      · exact no_both ao ha dirty ri rk
      · exact no_both ao ha dirty rj rk
    have bound := opndBound ao al (1-i)
    obtain ⟨v,hv⟩ := pureOrNonempty ao (by omega : opnd C a (1-i)<n+C.gates.length) pure
    exact ⟨v,Finset.mem_inter.mpr ⟨oppositeSideWmax ao ha ri hv,oppositeSideWmax ao ha rj hv⟩⟩
  · rw [ij] at rj
    left
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

local instance : DecidableEq GateOp := gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

-- A direct reader of an empty, dirty wire cannot belong to lambda.
theorem first_charge (ao : IsAO2 n C) {w h : ℕ} (hn : (orIn n C w).Nonempty)
    (empty : orIn n C (n+h)=∅) (dirty : ∃ x, gateVal n C h x=true ∧ graphFun G ∅ x=false)
    (route : OrReaches n C w h) : ∃ m∈orN G C \ lam G C,
      OrReaches n C w m ∧ (n + h) ∈ (gateAt C m).inputs ∧ (LT.lt h m) := by
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
      · change opnd C m 0=n+d ∨ opnd C m 0=n+e
        rw [ls]
        rcases dd with dd|dd <;> rcases ee with ee|ee <;> omega
      · change opnd C m 1=n+d ∨ opnd C m 1=n+e
        rw [rs]
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

namespace Shared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.Local1490

theorem localization (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (d e : ℕ)
    (ao : IsAO2 n C) (form : TopForm G C) (junkEq : junk G C={d,e})
    (u v : Fin n) (edge : s(u,v)∈G.edgeFinset) (a : ℕ) (ha : a∈tops G C)
    (i : Fin 2) (j : ℕ) (member : j=d ∨ j=e)
    (topOn : gateVal n C a (pairInput u v)=true) (route : OrReaches n C (opnd C a i) j)
    (on : gateVal n C j (pairInput u v)=true) :
    let A := fun k => (gammaE G C k).filter (fun h => ∃ z∈wmax G C k, z∈h)
    s(u,v)∈A d ∨ s(u,v)∈A e ∨
      ((∀ x, gateVal n C d x=true → gateVal n C e x=true → graphFun G ∅ x=true) ∧
       s(u,v)∈gammaE G C d ∩ gammaE G C e) := by
  classical
  dsimp only
  have gamma (k) (h : gateVal n C k (pairInput u v)=true) : s(u,v)∈gammaE G C k :=
    Finset.mem_filter.mpr ⟨edge,u,v,rfl,h⟩
  obtain ⟨haLen,haOp,haClean⟩ := topData ha
  have other := (andValOperands ao haLen haOp _).mp topOn (1-i)
  rcases operand_trace u v (opnd C a (1-i)) other with ⟨z,hz,path⟩ | ⟨k,hk,notOr,path,onK⟩
  · have hzW := oppositeSideWmax ao ha route (reach_mem_orIn z path)
    have attached : ∃ w∈wmax G C j, w∈s(u,v) := by
      refine ⟨z,hzW,?_⟩
      rcases hz with rfl | rfl <;> simp
    have atj : s(u,v) ∈ (gammaE G C j).filter (fun h => ∃ z∈wmax G C j, z∈h) :=
      Finset.mem_filter.mpr ⟨gamma j on,attached⟩
    rcases member with rfl | rfl
    · exact Or.inl atj
    · exact Or.inr (Or.inl atj)
  · have kr := reach_orReaches path k rfl hk
    have op := (ao.1 _ (gateAt_mem hk)).resolve_right notOr
    have kj := operandOrAndJunk ao form haLen haOp kr op
    have num : k=d ∨ k=e := by simpa only [junkEq,Finset.mem_insert,Finset.mem_singleton] using kj
    have safe (x) (hj : gateVal n C j x=true) (hkx : gateVal n C k x=true) : graphFun G ∅ x=true := by
      apply haClean x
      apply (andValOperands ao haLen haOp x).mpr
      intro b
      rcases eitherOperand i b with rfl | rfl
      · exact reachVal route hj
      · exact reachVal kr hkx
    have ne : j ≠ k := by
      rintro rfl
      obtain ⟨_,_,x,hx,off⟩ := junkData kj
      rw [safe x hx hx] at off
      contradiction
    have gj := gamma j on
    have gk := gamma k onK
    right
    right
    rcases member with rfl | rfl <;> rcases num with rfl | rfl
    · exact (ne rfl).elim
    · exact ⟨safe,Finset.mem_inter.mpr ⟨gj,gk⟩⟩
    · exact ⟨fun x hd he => safe x he hd,Finset.mem_inter.mpr ⟨gk,gj⟩⟩
    · exact (ne rfl).elim

end Shared2262
namespace Shared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.Local1490
open PEqualNP.Outside.L_meta_2264.Profile2264 (graph)

local instance : DecidableEq GateOp := gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem first_charge_ne (ao : IsAO2 n C) {w h : ℕ} (neq : w ≠ n+h)
    (empty : orIn n C (n+h)=∅) (dirty : ∃ x, gateVal n C h x=true ∧ graphFun G ∅ x=false)
    (route : OrReaches n C w h) : ∃ m∈orN G C \ lam G C,
      OrReaches n C w m ∧ (n + h) ∈ (gateAt C m).inputs ∧ (LT.lt h m) := by
  rcases Relation.ReflTransGen.cases_tail (orReaches_reach h w route).1 with he | ⟨r,path,step⟩
  · exact (neq he.symm).elim
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

theorem singleton_guard (C : Circuit) (d e : ℕ) (w : Fin 11) (least : IsLeastAO graph C)
    (form : TopForm graph C) (lt : d < e) (hs : junk graph C={d,e})
    (de : ¬InCone 11 C d e) (ed : ¬InCone 11 C e d)
    (common : ∃ a∈tops graph C, InCone 11 C d a ∧ InCone 11 C e a)
    (notSafe : ¬∀ x, gateVal 11 C d x=true → gateVal 11 C e x=true → graphFun graph ∅ x=true)
    (only : ∀ v, v∈wmax graph C d ∨ v∈wmax graph C e → v=w)
    (cross : ∀ a∈tops graph C, ∀ u∈side C a 0, ∀ v∈side C a 1, graph.Adj u v)
    (route : ∀ u v, s(u,v)∈Ustar graph C → ∃ a∈tops graph C, ∃ (b : Fin 2) j, (j=d ∨ j=e) ∧
      gateVal 11 C a (pairInput u v)=true ∧ OrReaches 11 C (opnd C a b) j ∧
      gateVal 11 C j (pairInput u v)=true)
    (budget : 17 + (tops graph C \ centreless graph C).card + 2*(centreless graph C).card
      + (orN graph C \ lam graph C).card ≤ C.size+(Ustar graph C).card)
    (cover : ∀ T : Finset (Fin 11), IsMinCover (graph.deleteEdges ↑(Ustar graph C)) T →
      T.card ≤ (tops graph C \ centreless graph C).card) : 22≤C.size := by
  classical
  have all (u v : Fin 11) (h : s(u,v)∈Ustar graph C) : w∈s(u,v) := by
    obtain ⟨a,ha,b,j,num,atop,r,jp⟩ := route u v h
    have loc := localization 11 graph C d e least.1 form hs u v (Finset.mem_sdiff.mp h).1 a ha b j num atop r jp
    rcases loc with single|single|both
    · obtain ⟨y,hy,ye⟩ := (Finset.mem_filter.mp single).2
      simpa only [only y (Or.inl hy)] using ye
    · obtain ⟨y,hy,ye⟩ := (Finset.mem_filter.mp single).2
      simpa only [only y (Or.inr hy)] using ye
    · exact (notSafe both.1).elim
  let I := graph.edgeFinset.filter (fun edge => w∈edge)
  have sub : Ustar graph C ⊆ I := by
    intro f hf
    induction f using Sym2.ind with
    | _ u v => exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hf).1,all u v hf⟩
  have ideg : I.card≤4 := by
    change (graph.edgeFinset.filter (fun edge => w∈edge)).card≤4
    fin_cases w <;> decide +kernel
  have ud := (Finset.card_le_card sub).trans ideg
  let H := graph.deleteEdges ↑(Ustar graph C)
  let can (k : ℕ) := ∃ T : Finset (Fin 11), H.IsVertexCover (T : Set _) ∧ T.card=k
  have ex : ∃ k,can k := ⟨_,Finset.univ,fun _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
  obtain ⟨T,hT,sz⟩ := Nat.find_spec ex
  have minT : IsMinCover H T := ⟨hT,by
    intro S hS
    rw [sz]
    exact Nat.find_min' ex ⟨S,hS,rfl⟩⟩
  have tc := cover T minT
  have full := Profile2264.cover_uncovered T {w} _ hT (fun u v hu => by
    rcases Sym2.mem_iff.mp (all u v hu) with h|h
    · exact Or.inl (Finset.mem_singleton.mpr h.symm)
    · exact Or.inr (Finset.mem_singleton.mpr h.symm))
  have seven := Profile2264.seven_cover _ full
  have bound := Finset.card_union_le T ({w} : Finset (Fin 11))
  rw [Finset.card_singleton] at bound
  obtain ⟨a,ha,da,ea⟩ := common
  have pay := shared_price least.1 form lt.ne hs de ed ha da ea
  obtain ⟨i,ri⟩ := access least.1 form hs de ha da
  obtain ⟨j,rj⟩ := access least.1 form (hs.trans (Finset.pair_comm _ _)) ed ha ea
  obtain ⟨al,aop,clean⟩ := topData ha
  have ji : j=i := by
    rcases eitherOperand i j with eq|eq
    · exact eq
    · rw [eq] at rj
      exfalso
      apply notSafe
      intro x xd xe
      apply clean x
      apply (andValOperands least.1 al aop x).mpr
      intro b
      rcases eitherOperand i b with h|h
      · rw [h]; exact reachVal ri xd
      · rw [h]; exact reachVal rj xe
  rw [ji] at rj
  by_cases no : a∈centreless graph C
  · have cost := Finset.card_pos.mpr ⟨a,no⟩
    have dj : d∈junk graph C := by rw [hs]; simp
    obtain ⟨_,dop,dirty⟩ := junkData dj
    have neq : opnd C a i ≠ 11+d := by
      intro eq
      rw [eq] at rj
      obtain ⟨_,bad|⟨op,_,_,_,_⟩⟩ := (orReaches_iff 11 C d e).mp rj
      · omega
      · rw [dop] at op; cases op
    obtain ⟨g,hg,_,_,_⟩ := first_charge_ne least.1 neq (orInAnd dop) dirty ri
    have pc := Finset.card_pos.mpr ⟨g,hg⟩
    omega
  · have raw (b : Fin 2) : (side (n := 11) C a b).Nonempty := by
      by_contra empty
      apply no
      apply Finset.mem_filter.mpr
      refine ⟨ha,?_⟩
      have hz := Finset.not_nonempty_iff_eq_empty.mp empty
      fin_cases b
      · exact Or.inl hz
      · exact Or.inr hz
    obtain ⟨u,hu⟩ := raw i
    obtain ⟨v,hv⟩ := raw (1-i)
    have vw : v=w := only v (Or.inl (oppositeSideWmax least.1 ha ri hv))
    subst v
    have edge : graph.Adj u w := by
      fin_cases i
      · exact cross a ha u hu w hv
      · exact (cross a ha w hv u hu).symm
    have yes : s(u,w)∈I := Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr edge, by simp⟩
    have out : s(u,w)∉Ustar graph C := by
      intro bad
      apply (Finset.mem_sdiff.mp bad).2
      apply Finset.mem_biUnion.mpr
      refine ⟨a,ha,Finset.mem_image.mpr ?_⟩
      fin_cases i
      · exact ⟨(u,w), Finset.mem_product.mpr ⟨hu,hv⟩,rfl⟩
      · exact ⟨(w,u), Finset.mem_product.mpr ⟨hv,hu⟩,Sym2.eq_swap⟩
    have strict : Ustar graph C ⊂ I := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun h => out (h.symm ▸ yes)⟩
    have card := Finset.card_lt_card strict
    omega

end Shared2262
namespace Shared2262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2264.Profile2264 (graph)

theorem small_uncovered (C : Circuit) (d e : ℕ) (hLeast : IsLeastAO graph C)
    (form : TopForm graph C) (ne : d < e) (hs : junk graph C={d,e})
    (de : ¬InCone 11 C d e) (ed : ¬InCone 11 C e d)
    (common : ∃ a∈tops graph C, InCone 11 C d a ∧ InCone 11 C e a)
    (budget : 17 + (tops graph C \ centreless graph C).card + 2*(centreless graph C).card
      + (orN graph C \ lam graph C).card ≤ C.size+(Ustar graph C).card)
    (cover : ∀ T : Finset (Fin 11), IsMinCover (graph.deleteEdges ↑(Ustar graph C)) T →
      T.card ≤ (tops graph C \ centreless graph C).card)
    (small : (Ustar graph C).card≤2) : 22≤C.size := by
  classical
  obtain ⟨a,ha,da,ea⟩ := common
  have pay := shared_price hLeast.1 form ne.ne hs de ed ha da ea
  let H := graph.deleteEdges ↑(Ustar graph C)
  let can (k : ℕ) := ∃ T : Finset (Fin 11), H.IsVertexCover (T : Set _) ∧ T.card=k
  have ex : ∃ k,can k := ⟨_,Finset.univ,fun _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
  obtain ⟨T,hT,sz⟩ := Nat.find_spec ex
  have minT : IsMinCover H T := ⟨hT,by
    intro S hS
    rw [sz]
    exact Nat.find_min' ex ⟨S,hS,rfl⟩⟩
  have c := cover T minT
  have p := PEqualNP.Outside.L_meta_2693 (Ustar graph C) T hT
  omega

end Shared2262
