import Mathlib
import PEqualNP.Outside.L_meta_4791
import PEqualNP.MetaComplexity.Helpers.LowerPart
import PEqualNP.Outside.L_meta_3692
namespace Packs2584
variable {α : Type} [DecidableEq α]
def pts (D : Finset (Finset α)) := D.biUnion id
def allUnions (F : Finset (Finset α)) := F.powerset.image pts
def big (F : Finset (Finset α)) := F.filter (fun A=>3≤A.card)
def dbl (F : Finset (Finset α)) := F.filter (fun A=>A.card=2)
def seen (F : Finset (Finset α)) (U : Finset α) := (big F).filter (fun A=>A⊆U)
theorem intersect (F : Finset (Finset α)) (linear : ∀a∈F,∀b∈F,a≠b→(a∩b).card≤1)
    (a b : Finset α) (ha : a∈F) (hb : b∈F) (ab : a≠b) (two : 2≤a.card) : ¬a⊆b := by
  intro sub
  have hh : a∩b=a := Finset.inter_eq_left.mpr sub
  have h := linear a ha b hb ab
  rw [hh] at h
  omega
theorem recover (F : Finset (Finset α)) (linear : ∀a∈F,∀b∈F,a≠b→(a∩b).card≤1)
    (D : Finset (Finset α)) (sub : D⊆F) (small : D.card≤2) :
    seen F (pts D) = D∩big F := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨hA,subA⟩ := Finset.mem_filter.mp ha
    obtain ⟨inF,sz⟩ := Finset.mem_filter.mp hA
    refine Finset.mem_inter.mpr ⟨?_,hA⟩
    by_contra miss
    have cover : a⊆D.biUnion (fun b=>a∩b) := by
      intro x hx
      obtain ⟨b,hb,xb⟩ := Finset.mem_biUnion.mp (subA hx)
      exact Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_inter.mpr ⟨hx,xb⟩⟩
    have bound : a.card≤D.card := calc
      _ ≤ (D.biUnion (fun b=>a∩b)).card := Finset.card_le_card cover
      _ ≤ ∑b∈D,(a∩b).card := Finset.card_biUnion_le
      _ ≤ ∑_b∈D,1 := Finset.sum_le_sum (fun b hb=>linear a inF b (sub hb) (fun e=>miss (e ▸ hb)))
      _ = _ := by simp
    omega
  · intro h
    obtain ⟨ad,ab⟩ := Finset.mem_inter.mp h
    exact Finset.mem_filter.mpr ⟨ab,fun x hx=>Finset.mem_biUnion.mpr ⟨a,ad,hx⟩⟩

theorem cards (F : Finset (Finset α)) (non : ∀a∈F,a.Nonempty)
    (linear : ∀a∈F,∀b∈F,a≠b→(a∩b).card≤1) :
    let h := big F
    let t := dbl F
    let u := (t.powersetCard 2).image pts
    1+F.card+h.card.choose 2+u.card+(if t.Nonempty then h.card else 0)≤(allUnions F).card := by
  classical
  let H := big F
  let T := dbl F
  let A := (H.powersetCard 2).image pts
  let D := (T.powersetCard 2).image pts
  let S := insert (∅ : Finset α) F
  have ss : S⊆allUnions F := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|h
    · exact Finset.mem_image.mpr ⟨∅,by simp,by simp [pts]⟩
    · exact Finset.mem_image.mpr ⟨{x},by simpa using h,by simp [pts]⟩
  have hh (x) (hx : x∈A) : seen F x∈H.powersetCard 2 := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨inc,sz⟩ := Finset.mem_powersetCard.mp hq
    have eq := recover F linear q (inc.trans (Finset.filter_subset _ _)) sz.le
    rwa [eq,Finset.inter_eq_left.mpr inc]
  have getA : A.card=H.card.choose 2 := by
    rw [show A=(H.powersetCard 2).image pts from rfl,Finset.card_image_of_injOn,Finset.card_powersetCard]
    intro a ha b hb eq
    obtain ⟨ia,sa⟩ := Finset.mem_powersetCard.mp ha
    obtain ⟨ib,sb⟩ := Finset.mem_powersetCard.mp hb
    have x := congrArg (seen F) eq
    rwa [recover F linear a (ia.trans (Finset.filter_subset _ _)) sa.le,Finset.inter_eq_left.mpr ia,
      recover F linear b (ib.trans (Finset.filter_subset _ _)) sb.le,Finset.inter_eq_left.mpr ib] at x
  have disHT : Disjoint T H := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h := (Finset.mem_filter.mp hx).2
    have k := (Finset.mem_filter.mp hy).2
    omega
  have typeD (x) (hx : x∈D) : seen F x=∅ ∧ 3≤x.card := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨inc,sz⟩ := Finset.mem_powersetCard.mp hq
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (by omega : 1<q.card)
    have s1 := (Finset.mem_filter.mp (inc ha)).2
    have s2 := (Finset.mem_filter.mp (inc hb)).2
    have included (z) (hz : z∈q) : z⊆pts q := fun x hx=>Finset.mem_biUnion.mpr ⟨z,hz,hx⟩
    refine ⟨(recover F linear q (inc.trans (Finset.filter_subset _ _)) sz.le).trans
      (Finset.disjoint_iff_inter_eq_empty.mp (disHT.mono_left inc)),?_⟩
    by_contra! sm
    have eqA := Finset.eq_of_subset_of_card_le (included a ha) (show (pts q).card≤a.card by omega)
    have eqB := Finset.eq_of_subset_of_card_le (included b hb) (show (pts q).card≤b.card by omega)
    exact ne (eqA.trans eqB.symm)
  have typeS (x) (hx : x∈S) : (seen F x).card≤1 := by
    rcases Finset.mem_insert.mp hx with rfl|hx
    · have z := recover F linear ∅ (Finset.empty_subset _) (by simp)
      have e : seen F ∅=∅ := by simpa [pts] using z
      simp [e]
    · have z := recover F linear {x} (by simpa using hx) (by simp)
      simpa [pts] using (congrArg Finset.card z).le.trans (Finset.card_le_card (Finset.inter_subset_left : ({x} : Finset _)∩big F⊆{x}))
  have noD : Disjoint S D := by
    apply Finset.disjoint_left.mpr
    intro x xs xd
    obtain ⟨z,size⟩ := typeD x xd
    rcases Finset.mem_insert.mp xs with rfl|xf
    · simp at size
    · have inH : x∈big F := Finset.mem_filter.mpr ⟨xf,size⟩
      have yes : x∈seen F x := Finset.mem_filter.mpr ⟨inH,Finset.Subset.rfl⟩
      simpa [z] using yes
  have noA : Disjoint (S∪D) A := by
    apply Finset.disjoint_left.mpr
    intro x xs xa
    have sz := (Finset.mem_powersetCard.mp (hh x xa)).2
    rcases Finset.mem_union.mp xs with s|d
    · have := typeS x s;omega
    · simp [(typeD x d).1] at sz
  have embed {B : Finset (Finset α)} (inc : B⊆F) : (B.powersetCard 2).image pts⊆allUnions F := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨q,Finset.mem_powerset.mpr ((Finset.mem_powersetCard.mp hq).1.trans inc),rfl⟩
  let base := (S∪D)∪A
  have valid : base⊆allUnions F := Finset.union_subset (Finset.union_subset ss (embed (Finset.filter_subset _ _))) (embed (Finset.filter_subset _ _))
  have zF : (∅ : Finset α)∉F := fun h=>by simpa using non ∅ h
  have baseCt : base.card=1+F.card+H.card.choose 2+D.card := by
    rw [show base=(S∪D)∪A from rfl,Finset.card_union_of_disjoint noA,Finset.card_union_of_disjoint noD,getA,
      show S=insert ∅ F from rfl,Finset.card_insert_of_notMem zF]
    omega
  change 1+F.card+H.card.choose 2+D.card+(if T.Nonempty then H.card else 0)≤_
  rw [←baseCt]
  by_cases ht : T.Nonempty
  · obtain ⟨t,tr⟩ := ht
    have tf := (Finset.mem_filter.mp tr).1
    have ts := (Finset.mem_filter.mp tr).2
    have notH (h) (hh : h∈H) : t≠h := fun e=>Finset.disjoint_left.mp disHT tr (e.symm ▸ hh)
    let mix (h : Finset α) := h∪t
    have info (h) (hb : h∈H) : seen F (mix h)={h} ∧ h≠mix h ∧ mix h∈allUnions F := by
      have hf := (Finset.mem_filter.mp hb).1
      have part : {h,t}⊆F := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl|other
        · exact hf
        · exact (Finset.mem_singleton.mp other).symm ▸ tf
      have lte : ({h,t} : Finset _).card≤2 := (Finset.card_insert_le ..).trans (by simp)
      have eq : pts {h,t}=mix h := by simp [pts,mix]
      have kill : t∉H := Finset.disjoint_left.mp disHT tr
      refine ⟨?_,?_,Finset.mem_image.mpr ⟨{h,t},Finset.mem_powerset.mpr part,eq⟩⟩
      · rw [←eq,recover F linear _ part lte]
        ext x;simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton];aesop
      · intro eqh
        exact intersect F linear _ _ tf hf (notH h hb) ts.ge (eqh.symm ▸ Finset.subset_union_right)
    have mi : Set.InjOn mix (↑H : Set (Finset α)) := by
      intro a ha b hb eq
      have t := congrArg (seen F) eq
      simpa only [(info _ ha).1,(info _ hb).1,Finset.singleton_inj] using t
    have dis : Disjoint base (H.image mix) := by
      apply Finset.disjoint_left.mpr
      intro w hw hn
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
      have eq := (info a ha).1
      rcases Finset.mem_union.mp hw with sd|part
      · rcases Finset.mem_union.mp sd with s|d
        · rcases Finset.mem_insert.mp s with z|xf
          · have contains : a⊆mix a := Finset.subset_union_left
            have nul : a=∅ := Finset.subset_empty.mp (z ▸ contains)
            have size := (Finset.mem_filter.mp ha).2
            simp [nul] at size
          · have size := (Finset.mem_filter.mp ha).2
            have sub : a⊆mix a := Finset.subset_union_left
            exact intersect F linear a (mix a) (Finset.mem_filter.mp ha).1 xf (info a ha).2.1 (by omega) sub
        · have t := (typeD _ d).1
          simp [eq] at t
      · have sz := (Finset.mem_powersetCard.mp (hh _ part)).2
        simp [eq] at sz
    have cost := Finset.card_le_card (Finset.union_subset valid (Finset.image_subset_iff.mpr (fun a ha=>(info a ha).2.2)))
    rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injOn mi] at cost
    simpa [show T.Nonempty from ⟨t,tr⟩] using cost
  · simpa [ht] using Finset.card_le_card valid
end Packs2584

namespace Fiber2584
variable {α : Type} [DecidableEq α]
def points (D : Finset (Finset α)) := D.biUnion id
def candidates (F : Finset (Finset α)) := F.powersetCard 2
def sums (F : Finset (Finset α)) := (candidates F).image points

theorem onFour : ∀U : Finset (Fin 4),
  (((Finset.univ : Finset (Fin 4)).powersetCard 2).powersetCard 2 |>.filter (fun D=>points D=U)).card≤3 := by
  decide +kernel

set_option maxHeartbeats 900000 in
theorem cards (F : Finset (Finset α)) (two : ∀e∈F,e.card=2)
    (U : Finset α) (hit : U∈sums F) :
    ((candidates F).filter (fun D=>points D=U)).card≤3 := by
  classical
  obtain ⟨D,hD,eq⟩ := Finset.mem_image.mp hit
  obtain ⟨sub,len⟩ := Finset.mem_powersetCard.mp hD
  have small : U.card ≤ 4 := calc
    _ = (D.biUnion id).card := congrArg Finset.card eq.symm
    _ ≤ ∑e∈D,e.card := Finset.card_biUnion_le
    _ = ∑_e∈D,2 := Finset.sum_congr rfl (fun e he=>two e (sub he))
    _ = 4 := by simp [len]
  let idx (x : α) : Fin 4 := if h : x∈U then
    Fin.castLE (by simpa using small) ((Fintype.equivFin {x // x∈U}) ⟨x,h⟩) else 0
  have inj : Set.InjOn idx (↑U : Set α) := by
    intro x hx y hy eq
    change x∈U at hx
    change y∈U at hy
    simp only [idx,dif_pos hx,dif_pos hy] at eq
    have h := congrArg Fin.val eq
    exact congrArg Subtype.val ((Fintype.equivFin {x // x∈U}).injective (Fin.ext h))
  let f (e : Finset α) := e.image idx
  have finj {e g : Finset α} (eU : e⊆U) (gU : g⊆U) (eq : f e=f g) : e=g := by
    ext x
    constructor
    · intro he
      have ix : idx x∈f g := eq ▸ Finset.mem_image_of_mem idx he
      obtain ⟨y,hy,h⟩ := Finset.mem_image.mp ix
      exact inj (gU hy) (eU he) h ▸ hy
    · intro hg
      have ix : idx x∈f e := eq.symm ▸ Finset.mem_image_of_mem idx hg
      obtain ⟨y,hy,h⟩ := Finset.mem_image.mp ix
      exact inj (eU hy) (gU hg) h ▸ hy
  let fiber := (candidates F).filter (fun D=>points D=U)
  have raw (d) (hd : d∈fiber) (e) (he : e∈d) : e⊆U := by
    intro z hz
    rw [←(Finset.mem_filter.mp hd).2]
    exact Finset.mem_biUnion.mpr ⟨e,he,hz⟩
  apply le_trans _ (onFour (U.image idx))
  apply Finset.card_le_card_of_injOn (fun d=>d.image f)
  · intro d hd
    obtain ⟨mem,eq⟩ := Finset.mem_filter.mp hd
    obtain ⟨ss,sz⟩ := Finset.mem_powersetCard.mp mem
    have injF : Set.InjOn f (↑d : Set (Finset α)) :=
      fun e he g hg h=>finj (raw _ hd _ he) (raw _ hd _ hg) h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_,(Finset.card_image_of_injOn injF).trans sz⟩,?_⟩
    · intro z hz
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
        (Finset.card_image_of_injOn (fun x hx y hy h=>inj (raw _ hd _ he hx) (raw _ hd _ he hy) h)).trans (two e (ss he))⟩
    · ext z
      constructor
      · intro hz
        obtain ⟨g,hg,zg⟩ := Finset.mem_biUnion.mp hz
        obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hg
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp zg
        exact Finset.mem_image_of_mem _ (raw d hd e he hx)
      · intro hz
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨e,he,xe⟩ := Finset.mem_biUnion.mp (eq.symm ▸ hx)
        exact Finset.mem_biUnion.mpr ⟨f e,Finset.mem_image_of_mem _ he,Finset.mem_image_of_mem _ xe⟩
  · intro d hd t ht h
    change d.image f=t.image f at h
    ext e
    constructor
    · intro he
      have z := h ▸ Finset.mem_image_of_mem f he
      obtain ⟨g,hg,q⟩ := Finset.mem_image.mp z
      exact finj (raw _ ht _ hg) (raw _ hd _ he) q ▸ hg
    · intro he
      have z := h.symm ▸ Finset.mem_image_of_mem f he
      obtain ⟨g,hg,q⟩ := Finset.mem_image.mp z
      exact finj (raw _ hd _ hg) (raw _ ht _ he) q ▸ hg

theorem twoLoss (F : Finset (Finset α)) (two : ∀e∈F,e.card=2) : F.card≤(sums F).card+2 := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f:=points) (s:=candidates F) (t:=sums F)
    (fun _ he=>Finset.mem_image_of_mem _ he)
  have c := Finset.sum_le_sum (s:=sums F) (fun U hU=>cards F two U hU)
  rw [←h] at c
  simp only [candidates,Finset.card_powersetCard,Finset.sum_const,nsmul_eq_mul] at c
  have geom (n : Nat) : n* (n-1) = 2*n.choose 2 := by
    cases n with
    | zero => decide
    | succ n =>
      induction n with
      | zero => decide
      | succ n ih =>
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel] at ih ⊢
        nlinarith
  have e := geom F.card
  by_contra! no
  have z : 3≤F.card := by omega
  let a := F.card-3
  have ha : F.card=a+3 := by dsimp [a];omega
  have hb : F.card-1=a+2 := by omega
  rw [hb,ha] at e
  have sq : a≤a*a := by cases a <;> simp <;> nlinarith
  have mt : (sums F).card≤a := by omega
  rw [ha] at c
  nlinarith
end Fiber2584
namespace Incidence2584
variable {α : Type} [DecidableEq α]
theorem row (n : Nat) (pos : 0<n) : n≤1+n.choose 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => decide
    | succ n =>
      have h := ih (by omega)
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      omega

theorem count (F : Finset (Finset α))
    (linear : ∀a∈F,∀b∈F,a≠b→(a∩b).card≤1) :
    ∑a∈F,a.card ≤ (F.biUnion id).card + F.card.choose 2 := by
  classical
  let P := F.biUnion id
  let atP (x : α) := F.filter (fun A=>x∈A)
  have members (x) : (atP x).powersetCard 2⊆F.powersetCard 2 := by
    intro q hq
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_powersetCard.mp hq).1.trans (Finset.filter_subset _ _),
      (Finset.mem_powersetCard.mp hq).2⟩
  have dis : Set.PairwiseDisjoint (↑P : Set α) (fun x=>(atP x).powersetCard 2) := by
    intro x hx y hy xy
    apply Finset.disjoint_left.mpr
    intro D h1 h2
    obtain ⟨i,hI,j,hJ,ij⟩ := Finset.one_lt_card.mp (by rw [(Finset.mem_powersetCard.mp h1).2];decide : 1<D.card)
    have ui := Finset.mem_filter.mp ((Finset.mem_powersetCard.mp h1).1 hI)
    have uj := Finset.mem_filter.mp ((Finset.mem_powersetCard.mp h1).1 hJ)
    have vi := Finset.mem_filter.mp ((Finset.mem_powersetCard.mp h2).1 hI)
    have vj := Finset.mem_filter.mp ((Finset.mem_powersetCard.mp h2).1 hJ)
    exact xy (Finset.card_le_one.mp (linear _ ui.1 _ uj.1 ij) x (Finset.mem_inter.mpr ⟨ui.2,uj.2⟩)
      y (Finset.mem_inter.mpr ⟨vi.2,vj.2⟩))
  have pairs : ∑x∈P,(atP x).card.choose 2≤F.card.choose 2 := by
    simp only [←Finset.card_powersetCard]
    rw [←Finset.card_biUnion dis]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun x _ =>members x))
  have countX : ∑x∈P,(atP x).card=∑a∈F,a.card := by
    simp only [atP,Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [←Finset.card_filter]
    have eq : P.filter (fun x=>x∈a)=a := by
      ext x
      exact ⟨fun h=>(Finset.mem_filter.mp h).2,fun h=>Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨a,ha,h⟩,h⟩⟩
    rw [eq]
  rw [←countX]
  have bound := Finset.sum_le_sum (s:=P) (fun x hx=>row (atP x).card (by
    obtain ⟨a,ha,e⟩ := Finset.mem_biUnion.mp hx
    exact Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,e⟩⟩))
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at bound
  exact bound.trans (Nat.add_le_add_left pairs P.card)
end Incidence2584
namespace Bound2584
open Packs2584
variable {α : Type} [DecidableEq α]

theorem edgeBudget (F : Finset (Finset α)) (nonempty : F.Nonempty) (non : ∀a∈F,a.Nonempty)
    (linear : ∀a∈F,∀b∈F,a≠b→(a∩b).card≤1) :
    (∑a∈F,a.card)+min (pts F).card F.card+2 ≤ (allUnions F).card+(pts F).card+F.card := by
  classical
  let H := big F
  let T := dbl F
  let D := (T.powersetCard 2).image pts
  let A := F.filter (fun a=>a.card=1)
  have ht : ∀a∈T,a.card=2 := fun a h=>(Finset.mem_filter.mp h).2
  have hsub : H⊆F := Finset.filter_subset _ _
  have tsub : T⊆F := Finset.filter_subset _ _
  have part : (H∪T)∪A=F := by
    ext e
    simp only [H,T,A,big,dbl,Finset.mem_union,Finset.mem_filter]
    by_cases hf : e∈F
    · have z := Finset.card_pos.mpr (non e hf)
      simp only [hf,true_and,iff_true]
      omega
    · tauto
  have dis1 : Disjoint H T := by
    apply Finset.disjoint_left.mpr;intro e he et
    have k := (Finset.mem_filter.mp he).2
    have t := ht _ et
    omega
  have dis2 : Disjoint (H∪T) A := by
    apply Finset.disjoint_left.mpr;intro e he ea
    have aa := (Finset.mem_filter.mp ea).2
    rcases Finset.mem_union.mp he with h|t
    · have := (Finset.mem_filter.mp h).2;omega
    · have := ht _ t;omega
  have count := congrArg Finset.card part
  rw [Finset.card_union_of_disjoint dis2,Finset.card_union_of_disjoint dis1] at count
  have hsum := Incidence2584.count H (fun a ha b hb=>linear a (hsub ha) b (hsub hb))
  change (∑a∈H,a.card)≤(pts H).card + H.card.choose 2 at hsum
  have esum : (∑a∈F,a.card)≤(pts H).card+H.card.choose 2+2*T.card+A.card := by
    calc
      _ = (∑a∈H,a.card)+(∑a∈T,a.card)+(∑a∈A,a.card) := by conv_lhs => rw [←part,Finset.sum_union dis2,Finset.sum_union dis1]
      _ = (∑a∈H,a.card)+(∑_a∈T,2)+(∑_a∈A,1) := by
        have ones : (∑a∈A,a.card)=∑_a∈A,1 := Finset.sum_congr rfl (fun a ha=>(Finset.mem_filter.mp ha).2)
        rw [Finset.sum_congr rfl (fun a ha=>ht a ha),ones]
      _ ≤ _ := by simp;omega
  have pack := Packs2584.cards F non linear
  change 1+F.card+H.card.choose 2+D.card+(if T.Nonempty then H.card else 0)≤_ at pack
  have fiber := Fiber2584.twoLoss T ht
  change T.card≤D.card+2 at fiber
  have basis : pts H⊆pts F := by
    intro x hx
    obtain ⟨a,ha,xa⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨a,hsub ha,xa⟩
  have compare := Finset.card_le_card basis
  have pun := min_le_left (pts F).card F.card
  have lun := min_le_right (pts F).card F.card
  by_cases high : H.Nonempty
  · have hp := Finset.card_pos.mpr high
    by_cases low : T.Nonempty
    · rw [if_pos low] at pack
      by_cases only : H.card=1
      · obtain ⟨h,eqH⟩ := Finset.card_eq_one.mp only
        obtain ⟨t,ht⟩ := low
        have t2 := (Finset.mem_filter.mp ht).2
        have hf : h∈H := eqH ▸ Finset.mem_singleton_self h
        have h3 := (Finset.mem_filter.mp hf).2
        have ne : t≠h := by rintro rfl;omega
        have ns := intersect F linear t h (tsub ht) (hsub hf) ne t2.ge
        have neq : pts H≠pts F := by
          intro eq
          apply ns
          intro x hx
          have mem : x∈pts F := Finset.mem_biUnion.mpr ⟨t,tsub ht,hx⟩
          rw [←eq,eqH] at mem
          simpa [pts] using mem
        have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨basis,neq⟩)
        omega
      · omega
    · have tt := Finset.not_nonempty_iff_eq_empty.mp low
      simp only [if_neg low] at pack
      have t0 : T.card=0 := by simp [tt]
      omega
  · have h0 := Finset.not_nonempty_iff_eq_empty.mp high
    have hC : H.card=0 := by simp [h0]
    have p0 : (pts H).card=0 := by simp [h0,pts]
    simp only [hC,Nat.choose_zero_succ,ite_self,Nat.add_zero] at esum pack
    by_cases a0 : A.Nonempty
    · have := Finset.card_pos.mpr a0;omega
    · have aC : A.card=0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp a0)
      have fpos := Finset.card_pos.mpr nonempty
      by_cases t1 : T.card=1
      · obtain ⟨t,eq⟩ := Finset.card_eq_one.mp t1
        have it : t∈T := eq ▸ Finset.mem_singleton_self t
        have size := ht t it
        have sub : t⊆pts F := fun x hx=>Finset.mem_biUnion.mpr ⟨t,tsub it,hx⟩
        have := Finset.card_le_card sub
        omega
      · have many : 2≤T.card := by omega
        have p : (T.powersetCard 2).Nonempty := Finset.powersetCard_nonempty.mpr many
        obtain ⟨j,hj⟩ := p
        have dpos := Finset.card_pos.mpr (show D.Nonempty from ⟨_,Finset.mem_image_of_mem _ hj⟩)
        omega
end Bound2584

namespace Frontier4675
variable {N : Nat}
abbrev Index (N : Nat) := Fin N

noncomputable def visited (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun v=>∃r∈roots,Relation.ReflTransGen (fun i j=>j∈child i) r v)
theorem mem_visit (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) (v : Fin N) :
    v∈visited roots child ↔ ∃r∈roots,Relation.ReflTransGen (fun i j=>j∈child i) r v := by
  classical
  simp [visited]

theorem rootVisit (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) :
    roots⊆visited roots child := by
  intro i hi
  exact (mem_visit _ _ _).mpr ⟨i,hi,.refl⟩

theorem childVisit {roots : Finset (Fin N)} {child : Fin N → Finset (Fin N)} {i j}
    (hi : i∈visited roots child) (hj : j∈child i) : j∈visited roots child := by
  obtain ⟨r,hr,tr⟩ := (mem_visit _ _ _).mp hi
  exact (mem_visit _ _ _).mpr ⟨r,hr,tr.tail hj⟩

noncomputable def tips (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) :=
  (visited roots child).filter (fun i=>child i=∅)

noncomputable def forks (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N)) :=
  (visited roots child).filter (fun i=>2≤(child i).card)

theorem budget (roots : Finset (Fin N)) (child : Fin N → Finset (Fin N))
    (two : ∀i,(child i).card≤2) :
    (tips roots child).card≤roots.card+(forks roots child).card := by
  classical
  let V := visited roots child
  let U := V.filter (fun i=>(child i).Nonempty)
  let B := forks roots child
  have support : V ⊆ roots ∪ U.biUnion child := by
    intro i hi
    obtain ⟨r,hr,reach⟩ := (mem_visit _ _ _).mp hi
    cases reach with
    | refl => exact Finset.mem_union_left _ hr
    | tail prev step =>
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_filter.mpr
        ⟨(mem_visit _ _ _).mpr ⟨r,hr,prev⟩,⟨_,step⟩⟩,step⟩
  have ucnt : ∑ i∈U,(child i).card ≤ U.card+B.card := by
    have h := Finset.sum_le_sum (s:=U) (fun i (hi : i∈U) =>
      (show (child i).card ≤ 1+(if 2≤(child i).card then 1 else 0) by have := two i;split <;> omega))
    have d : U.filter (fun i=>2≤(child i).card)=B := by
      ext i
      change i∈U.filter (fun j=>2≤(child j).card) ↔ i∈V.filter (fun j=>2≤(child j).card)
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨u,t⟩
        exact ⟨(Finset.mem_filter.mp u).1,t⟩
      · rintro ⟨v,t⟩
        exact ⟨Finset.mem_filter.mpr ⟨v,Finset.card_pos.mp (by omega)⟩,t⟩
    rw [Finset.sum_add_distrib,←Finset.card_filter,d] at h
    simpa using h
  have splitV : (tips roots child).card+U.card=V.card := by
    have d : V.filter (fun i=>¬child i=∅)=U := by ext i;simp [U,Finset.nonempty_iff_ne_empty]
    have h := Finset.card_filter_add_card_filter_not (s:=V) (fun i=>child i=∅)
    rw [d] at h
    exact h
  have c := (Finset.card_le_card support).trans (Finset.card_union_le _ _)
  have d : (U.biUnion child).card ≤ ∑i∈U,(child i).card := Finset.card_biUnion_le
  change _≤roots.card+B.card
  omega

theorem cover {α : Type} [DecidableEq α] (roots : Finset (Fin N)) (child : Fin N→Finset (Fin N))
    (earlier : ∀i j,j∈child i→j < i) (alive direct : Fin N→Finset α)
    (transfer : ∀i∈visited roots child, ∀e∈alive i,
      (∃j∈child i,e∈alive j) ∨ (child i=∅ ∧ e∈direct i) ∨ (∃r∈roots,r < i ∧ e∈alive r)) :
    roots.biUnion alive ⊆ (tips roots child).biUnion direct := by
  classical
  intro e he
  obtain ⟨r,hr,er⟩ := Finset.mem_biUnion.mp he
  let W := (visited roots child).filter (fun i=>e∈alive i)
  have wn : W.Nonempty := ⟨r,Finset.mem_filter.mpr ⟨rootVisit roots child hr,er⟩⟩
  let i := W.min' wn
  have mi : i∈W := Finset.min'_mem W wn
  have least (j : Fin N) (h : j∈W) : i≤j := Finset.min'_le W j h
  obtain ⟨hv,ee⟩ := Finset.mem_filter.mp mi
  rcases transfer i hv e ee with ⟨j,hj,ej⟩|⟨empty,ed⟩|⟨s,hs,lt,es⟩
  · exact False.elim (not_lt_of_ge (least j (Finset.mem_filter.mpr ⟨childVisit hv hj,ej⟩)) (earlier i j hj))
  · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨hv,empty⟩,ed⟩
  · exact False.elim (not_lt_of_ge (least s (Finset.mem_filter.mpr ⟨rootVisit roots child hs,es⟩)) lt)
end Frontier4675
namespace Trace2584
variable {N : Nat}
abbrev W (N : Nat) := Fin N
def reachable (r : Finset (W N)) (ch : W N → Finset (W N)) (j : W N) := ∃i∈r,Relation.ReflTransGen (fun i j=>j∈ch i) i j
noncomputable def tips (r : Finset (W N)) (ch : W N → Finset (W N)) : Finset (W N) := by
  classical
  exact Finset.univ.filter (fun i=>reachable r ch i ∧ ch i=∅)
theorem unpack (r : Finset (W N)) (ch : W N → Finset (W N)) (j : W N) :
    j∈tips r ch ↔ reachable r ch j ∧ ch j=∅ := by
  classical
  simp [tips]
theorem mono {r t : Finset (W N)} (sub : r⊆t) (ch : W N→Finset (W N)) : tips r ch⊆tips t ch := by
  intro i hi
  obtain ⟨⟨j,hj,p⟩,e⟩ := (unpack _ _ _).mp hi
  exact (unpack _ _ _).mpr ⟨⟨j,sub hj,p⟩,e⟩

theorem propagate (ch : W N→Finset (W N)) (lt : ∀i j,j∈ch i→j < i)
    (good : W N→Prop) (gate : ∀i,(ch i).Nonempty→(good i ↔ ∀j∈ch i,good j)) (o : W N) :
    good o ↔ ∀j∈tips {o} ch,good j := by
  classical
  constructor
  · intro ho j hj
    obtain ⟨⟨i,hi,path⟩,_⟩ := (unpack _ _ _).mp hj
    obtain rfl := Finset.mem_singleton.mp hi
    clear hj
    induction path with
    | refl => exact ho
    | tail path step ih => exact (gate _ ⟨_,step⟩).mp ih _ step
  · intro ends
    by_contra bad
    let F := Finset.univ.filter (fun j=>reachable {o} ch j ∧ ¬good j)
    have ho : o∈F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨o,by simp,.refl⟩,bad⟩
    have non : F.Nonempty := ⟨o,ho⟩
    let i := F.min' non
    obtain ⟨r,badI⟩ := (Finset.mem_filter.mp (Finset.min'_mem F non)).2
    change reachable {o} ch i at r
    change ¬good i at badI
    by_cases ee : ch i=∅
    · exact badI (ends i ((unpack _ _ _).mpr ⟨r,ee⟩))
    · obtain ⟨j,hj⟩ := Classical.not_forall.mp (fun h=>badI ((gate _ (Finset.nonempty_iff_ne_empty.mpr ee)).mpr h))
      have yes : j∈ch i := by by_contra no;exact hj (fun e=>(no e).elim)
      have no : ¬good j := fun g=>hj (fun _=>g)
      obtain ⟨a,ar,path⟩ := r
      have jf : j∈F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨a,ar,path.tail yes⟩,no⟩
      exact (not_lt_of_ge (Finset.min'_le F j jf)) (lt _ _ yes)
end Trace2584
namespace Ports4675
open Frontier4675
inductive Node (V : Type) (N : Nat) where
  | raw (v : V)
  | meet (a b : Fin N)
  | join (a b : Fin N)
  deriving DecidableEq

end Ports4675
namespace Circuit4675
open Ports4675
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.EdgeOwnership
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
variable {n : Nat} (C : Circuit) (ao : IsAO2 n C)
abbrev W (n : Nat) (C : Circuit) := Fin (n+C.gates.length)

def operand (k : Fin C.gates.length) (b : Fin 2) : W n C :=
  ⟨opnd C k.val b,(LowerPart.opnd_lt C ao k.val k.isLt b).trans_le (Nat.add_le_add_left k.isLt.le n)⟩

def tag (i : W n C) : Node (Fin n) (n+C.gates.length) :=
  if h : i.val < n then .raw ⟨i.val,h⟩ else
    let k : Fin C.gates.length := ⟨i.val-n,by have := i.isLt;omega⟩
    if (gateAt C k.val).op=GateOp.and then .meet (operand C ao k 0) (operand C ao k 1)
    else .join (operand C ao k 0) (operand C ao k 1)

theorem layout (i : W n C) :
    (∃v : Fin n,tag C ao i=.raw v ∧ i.val=v.val) ∨
    ∃k : Fin C.gates.length,i.val=n+k.val ∧
      ((tag C ao i=.meet (operand C ao k 0) (operand C ao k 1) ∧ (gateAt C k.val).op=GateOp.and) ∨
       (tag C ao i=.join (operand C ao k 0) (operand C ao k 1) ∧ (gateAt C k.val).op=GateOp.or)) := by
  by_cases h : i.val < n
  · exact Or.inl ⟨⟨i.val,h⟩,by simp [tag,h],rfl⟩
  · let k : Fin C.gates.length := ⟨i.val-n,by have := i.isLt;omega⟩
    refine Or.inr ⟨k,by dsimp [k];omega,?_⟩
    rcases LeafBound.ao_op ao k.isLt with eq|eq
    · exact Or.inl ⟨by simp only [tag,h,↓reduceDIte];change (if (gateAt C k.val).op=GateOp.and then _ else _)=_;rw [if_pos eq],eq⟩
    · have ne : (gateAt C k.val).op≠GateOp.and := eq ▸ (by decide)
      exact Or.inr ⟨by simp only [tag,h,↓reduceDIte];change (if (gateAt C k.val).op=GateOp.and then _ else _)=_;rw [if_neg ne],eq⟩

theorem ofRaw {i : W n C} {v : Fin n} (q : tag C ao i=.raw v) : i.val=v.val := by
  rcases layout C ao i with ⟨u,t,e⟩|⟨k,e,⟨t,_⟩|⟨t,_⟩⟩ <;> rw [t] at q <;> cases q
  exact e

theorem ofMeet {i a b : W n C} (q : tag C ao i=.meet a b) :
    ∃k : Fin C.gates.length,i.val=n+k.val ∧ (gateAt C k.val).op=GateOp.and ∧
      a=operand C ao k 0 ∧ b=operand C ao k 1 := by
  rcases layout C ao i with ⟨u,t,e⟩|⟨k,e,⟨t,op⟩|⟨t,op⟩⟩ <;> rw [t] at q <;> cases q
  exact ⟨k,e,op,rfl,rfl⟩

theorem ofJoin {i a b : W n C} (q : tag C ao i=.join a b) :
    ∃k : Fin C.gates.length,i.val=n+k.val ∧ (gateAt C k.val).op=GateOp.or ∧
      a=operand C ao k 0 ∧ b=operand C ao k 1 := by
  rcases layout C ao i with ⟨u,t,e⟩|⟨k,e,⟨t,op⟩|⟨t,op⟩⟩ <;> rw [t] at q <;> cases q
  exact ⟨k,e,op,rfl,rfl⟩

theorem gateCount :
    (Finset.univ.filter (fun i : W n C=>(match tag C ao i with | .raw _=>false | _=>true) = true)).card=C.size := by
  let f : Fin C.gates.length → W n C := fun k=>⟨n+k.val,Nat.add_lt_add_left k.isLt n⟩
  have eq : Finset.univ.filter (fun i : W n C=>(match tag C ao i with | .raw _=>false | _=>true) = true) =
      Finset.univ.image f := by
    ext i
    cases q : tag C ao i with
    | raw v =>
      have e := ofRaw C ao q
      simp only [Finset.mem_filter,q,Finset.mem_univ,true_and,Finset.mem_image]
      constructor
      · intro h;contradiction
      rintro ⟨k,rfl⟩
      have lt := v.isLt
      change n+k.val=v.val at e
      omega
    | meet a b =>
      obtain ⟨k,e,_,_,_⟩ := ofMeet C ao q
      simp only [Finset.mem_filter,q,Finset.mem_univ,true_and,Finset.mem_image]
      exact ⟨fun _=>⟨k,Fin.ext e.symm⟩,fun _=>True.intro⟩
    | join a b =>
      obtain ⟨k,e,_,_,_⟩ := ofJoin C ao q
      simp only [Finset.mem_filter,q,Finset.mem_univ,true_and,Finset.mem_image]
      exact ⟨fun _=>⟨k,Fin.ext e.symm⟩,fun _=>True.intro⟩
  rw [eq,Finset.card_image_of_injective _ (show Function.Injective f from fun a b h=>by
    apply Fin.ext;have e := congrArg Fin.val h;change n+a.val=n+b.val at e;omega)]
  simp [Circuit.size]
end Circuit4675
namespace Circuit4675
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Ports4675
variable {n : Nat} (C : Circuit) (ao : IsAO2 n C)
def links (conj : Bool) (i : W n C) : Finset (W n C) :=
  match tag C ao i with
  | .raw _ => ∅
  | .meet a b => if conj then {a,b} else ∅
  | .join a b => if conj then ∅ else {a,b}
def vars (i : W n C) : Finset (Fin n) := match tag C ao i with | .raw v=>{v} | _=>∅
noncomputable def tipsAt (c : Bool) (r : Finset (W n C)) := Trace2584.tips r (links C ao c)
noncomputable def clause (i : W n C) := (tipsAt C ao false {i}).biUnion (vars C ao)
noncomputable def clauses (o : W n C) := (tipsAt C ao true {o}).image (clause C ao)
def CNF (o : W n C) : Prop :=
  ∀i∈tipsAt C ao true {o},∀j∈tipsAt C ao false {i},∃v,tag C ao j=.raw v

theorem desc (c : Bool) (i j : W n C) (w : j∈links C ao c i) : j < i := by
  rcases layout C ao i with ⟨v,t,e⟩|⟨k,e,⟨t,op⟩|⟨t,op⟩⟩
  · simp [links,t] at w
  · have pick : j=operand C ao k 0 ∨ j=operand C ao k 1 := by cases c <;> simp_all [links,t]
    change j.val < i.val;rw [e]
    rcases pick with rfl|rfl <;> exact LowerPart.opnd_lt C ao _ k.isLt _
  · have pick : j=operand C ao k 0 ∨ j=operand C ao k 1 := by cases c <;> simp_all [links,t]
    change j.val < i.val;rw [e]
    rcases pick with rfl|rfl <;> exact LowerPart.opnd_lt C ao _ k.isLt _

theorem topAnd (o : W n C) (x : Fin n→Bool) : wireVal n C o.val x=true ↔
    ∀j∈tipsAt C ao true {o},wireVal n C j.val x=true := by
  apply Trace2584.propagate _ (desc C ao true)
  intro i non
  rcases layout C ao i with ⟨v,t,e⟩|⟨k,e,⟨t,op⟩|⟨t,op⟩⟩
  · simp [links,t] at non
  · simp only [links,t,ite_true,Finset.mem_insert,Finset.mem_singleton]
    rw [e]
    simpa using LowerPart.val_and C ao k.val k.isLt op x
  · simp [links,t] at non

theorem bottomOr (i : W n C) (x : Fin n→Bool) : wireVal n C i.val x=false ↔
    ∀j∈tipsAt C ao false {i},wireVal n C j.val x=false := by
  apply Trace2584.propagate _ (desc C ao false)
  intro j non
  rcases layout C ao j with ⟨v,t,e⟩|⟨k,e,⟨t,op⟩|⟨t,op⟩⟩
  · simp [links,t] at non
  · simp [links,t] at non
  · simp only [links,t,ite_false,Finset.mem_insert,Finset.mem_singleton]
    rw [e]
    have z := LowerPart.val_or C ao k.val k.isLt op x
    change wireVal n C (n+k.val) x=true ↔ _ at z
    simp_all

theorem semantics (o : W n C) (cnf : CNF C ao o) (x : Fin n→Bool) :
    wireVal n C o.val x=true ↔ ∀Q∈clauses C ao o,∃v∈Q,x v=true := by
  classical
  have localEq (i) (hi : i∈tipsAt C ao true {o}) :
      wireVal n C i.val x=true ↔ ∃v∈clause C ao i,x v=true := by
    have z := bottomOr C ao i x
    constructor
    · intro h
      by_contra! no
      have off := z.mpr (by
        intro j hj
        obtain ⟨v,t⟩ := cnf i hi j hj
        have mem : v∈clause C ao i := Finset.mem_biUnion.mpr ⟨j,hj,by simp [vars,t]⟩
        rw [ofRaw C ao t];exact (PEqualNP.Outside.L_meta_4791.val_ofFn C x v).trans (by simpa using no _ mem))
      exact Bool.false_ne_true (off.symm.trans h)
    · rintro ⟨v,hv,on⟩
      obtain ⟨j,hj,hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨u,t⟩ := cnf _ hi _ hj
      have eq : v=u := by simpa [vars,t] using hv
      by_contra! off
      have k := z.mp (by simpa using off) j hj
      rw [ofRaw C ao t] at k
      exact Bool.false_ne_true (k.symm.trans ((PEqualNP.Outside.L_meta_4791.val_ofFn C x u).trans (eq ▸ on)))
  rw [topAnd C ao o x]
  exact ⟨fun h Q hQ=>by obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ;exact (localEq _ hi).mp (h _ hi),
    fun h i hi=>(localEq _ hi).mpr (h _ (Finset.mem_image_of_mem _ hi))⟩

def gates (conj : Bool) := Finset.univ.filter (fun i : W n C=>
  (match tag C ao i with | .meet _ _=>conj | .join _ _=>!conj | _=>false)=true)

theorem budget (c : Bool) (r : Finset (W n C)) : (tipsAt C ao c r).card≤r.card+(gates C ao c).card := by
  classical
  let ch := links C ao c
  have eq : tipsAt C ao c r=Frontier4675.tips r ch := by
    ext i
    change i∈Trace2584.tips r ch ↔ i∈Frontier4675.tips r ch
    rw [Trace2584.unpack,Frontier4675.tips,Finset.mem_filter,Frontier4675.mem_visit] <;> rfl
  have two (i) : (ch i).card≤2 := by
    have ab (a b : W n C) : ({a,b} : Finset _).card≤2 := (Finset.card_insert_le ..).trans (by simp)
    cases q : tag C ao i <;> cases c <;> simp [ch,links,q,ab]
  have sub : Frontier4675.forks r ch⊆gates C ao c := by
    intro i h
    have k := (Finset.mem_filter.mp h).2
    cases q : tag C ao i <;> cases c <;> simp_all [ch,links,gates,q]
  exact eq ▸ (Frontier4675.budget r ch two).trans (Nat.add_le_add_left (Finset.card_le_card sub) _)

theorem cost (o : W n C) {P L : Finset (Fin n)} (pa : P∈clauses C ao o) (la : L∈clauses C ao o) :
    (clauses C ao o).card+(P∪L).card≤C.size+3 := by
  classical
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp pa
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp la
  let roots : Finset (W n C) := {i,j}
  let R := tipsAt C ao false roots
  have lift (k : W n C) (hk : k∈roots) : clause C ao k⊆R.biUnion (vars C ao) := by
    intro v hv
    obtain ⟨t,ht,vt⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨t,Trace2584.mono (Finset.singleton_subset_iff.mpr hk) _ ht,vt⟩
  have compared := Finset.card_le_card (Finset.union_subset (lift i (by simp [roots])) (lift j (by simp [roots])))
  have c1 : (R.biUnion (vars C ao)).card≤R.card := calc
    _ ≤ ∑k∈R,(vars C ao k).card := Finset.card_biUnion_le
    _ ≤ ∑_k∈R,1 := Finset.sum_le_sum (fun k _=>by cases q : tag C ao k <;> simp [vars,q])
    _ = _ := by simp
  have c2 : R.card≤2+(gates C ao false).card := (budget C ao _ _).trans
    (Nat.add_le_add_right (show roots.card≤2 from (Finset.card_insert_le ..).trans (by simp)) _)
  have c3 : (clauses C ao o).card≤1+(gates C ao true).card := Finset.card_image_le.trans (by simpa using budget C ao true {o})
  have dis : Disjoint (gates C ao true) (gates C ao false) := by
    apply Finset.disjoint_left.mpr
    intro k h z
    cases q : tag C ao k <;> simp_all [gates,q]
  have both : gates C ao true∪gates C ao false=Finset.univ.filter (fun i : W n C=>(match tag C ao i with | .raw _=>false | _=>true)=true) := by
    ext i;cases q : tag C ao i <;> simp [gates,q]
  have sum := Finset.card_union_of_disjoint dis
  rw [both,gateCount C ao] at sum
  omega
end Circuit4675

namespace Clauses2584
variable {P L : Type} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

def unions (B : L → Finset P) : Finset (Finset P) :=
  (Finset.univ : Finset L).powerset.image (fun J=>J.biUnion B)

def close (B : L → Finset P) (U : Finset P) := Finset.univ.filter (fun l=>B l⊆U)

theorem necessary (B : L → Finset P) (K : Finset (Finset P × Finset L))
    (spec : ∀ X Y,(∃l∈Y,(X∩B l).Nonempty) ↔ ∀c∈K,(X∩c.1).Nonempty ∨ (Y∩c.2).Nonempty)
    (U : Finset P) (hU : U∈unions B) :
    (U,(close B U)ᶜ)∈K := by
  classical
  obtain ⟨J,_,eq⟩ := Finset.mem_image.mp hU
  have neg : ¬∃l∈close B U,(Uᶜ ∩ B l).Nonempty := by
    rintro ⟨l,hl,p,hp⟩
    obtain ⟨pn,pl⟩ := Finset.mem_inter.mp hp
    exact (Finset.mem_compl.mp pn) ((Finset.mem_filter.mp hl).2 pl)
  obtain ⟨c,empty⟩ := Classical.not_forall.mp (fun h=>neg ((spec Uᶜ (close B U)).mpr h))
  have hc : c∈K := by
    by_contra bad
    exact empty (fun h=>(bad h).elim)
  have offP (p) (h : p∈c.1) : p∈U := by
    by_contra bad
    exact empty (fun _=>Or.inl ⟨p,Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr bad,h⟩⟩)
  have offL (l) (h : l∈c.2) : l∉close B U := by
    intro bad
    exact empty (fun _=>Or.inr ⟨l,Finset.mem_inter.mpr ⟨bad,h⟩⟩)
  have covers (p l) (h : p∈B l) : p∈c.1 ∨ l∈c.2 := by
    have z := (spec {p} {l}).mp ⟨l,by simp,p,Finset.mem_inter.mpr ⟨by simp,h⟩⟩ c hc
    rcases z with ⟨w,hw⟩|⟨w,hw⟩
    · obtain ⟨eq,q⟩ := Finset.mem_inter.mp hw
      exact Or.inl (Finset.mem_singleton.mp eq ▸ q)
    · obtain ⟨eq,q⟩ := Finset.mem_inter.mp hw
      exact Or.inr (Finset.mem_singleton.mp eq ▸ q)
  have cp : c.1=U := by
    apply Finset.Subset.antisymm (fun p hp=>offP p hp)
    intro p hp
    obtain ⟨l,hl,pl⟩ := Finset.mem_biUnion.mp (eq.symm ▸ hp)
    exact (covers p l pl).resolve_right (fun q=>offL l q (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,fun x hx=>eq ▸ Finset.mem_biUnion.mpr ⟨l,hl,hx⟩⟩))
  have cl : c.2=(close B U)ᶜ := by
    apply Finset.Subset.antisymm (fun l h=>Finset.mem_compl.mpr (offL l h))
    intro l hl
    have no : ¬B l⊆U := fun h=>(Finset.mem_compl.mp hl) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    obtain ⟨p,pl,pn⟩ := Finset.not_subset.mp no
    exact (covers p l pl).resolve_left (fun w=>pn (offP p w))
  have cc : c=(U,(close B U)ᶜ) := Prod.ext cp cl
  exact cc ▸ hc

theorem clauseCount (B : L → Finset P) (K : Finset (Finset P × Finset L))
    (spec : ∀ X Y,(∃l∈Y,(X∩B l).Nonempty) ↔ ∀c∈K,(X∩c.1).Nonempty ∨ (Y∩c.2).Nonempty) :
    (unions B).card≤K.card := by
  apply Finset.card_le_card_of_injOn (fun U=>(U,(close B U)ᶜ))
  · exact necessary B K spec
  · intro a ha b hb eq
    exact congrArg Prod.fst eq
end Clauses2584
namespace Labels2584
variable {P L : Type} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
def live (B : L→Finset P) := Finset.univ.filter (fun l=>(B l).Nonempty)
def family (B : L→Finset P) := (live B).image B
def edges (B : L→Finset P) := (live B).biUnion (fun l=>(B l).image (fun p=>(p,l)))
def support (B : L→Finset P) := (family B).biUnion id

theorem memEdge (B : L→Finset P) (p : P) (l : L) : (p,l)∈edges B ↔ p∈B l := by
  constructor
  · rintro h
    obtain ⟨j,hj,hit⟩ := Finset.mem_biUnion.mp h
    obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp hit
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact hq
  · intro h
    exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,h⟩,Finset.mem_image_of_mem _ h⟩

theorem bookkeeping (B : L→Finset P) (linear : ∀i j,i≠j→(B i∩B j).card≤1) :
    (edges B).card+(family B).card=(∑a∈family B,a.card)+(live B).card ∧
    ∃A : Finset P,∃M : Finset L,(∀p l,p∈B l→p∈A ∨ l∈M) ∧ A.card+M.card ≤ min (support B).card (family B).card := by
  classical
  let N := live B
  let F := family B
  have maps (i) (hi : i∈N) : B i∈F := Finset.mem_image_of_mem _ hi
  have same (i j) (eq : B i=B j) (size : 2≤(B i).card) : i=j := by
    by_contra ne
    have h := linear i j ne
    rw [←eq,Finset.inter_self] at h
    omega
  have livePos (a) (ha : a∈F) : a.Nonempty := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hi).2
  have dis : Set.PairwiseDisjoint (N : Set L) (fun l=>(B l).image (fun p=>(p,l))) := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    rintro ⟨p,l⟩ h1 h2
    obtain ⟨_,_,e⟩ := Finset.mem_image.mp h1
    obtain ⟨_,_,f⟩ := Finset.mem_image.mp h2
    exact ne ((congrArg Prod.snd e).trans (congrArg Prod.snd f).symm)
  have total : (edges B).card=∑i∈N,(B i).card := by
    rw [edges,Finset.card_biUnion dis]
    exact Finset.sum_congr rfl (fun i _=>Finset.card_image_of_injective _ (fun _ _ h=>congrArg Prod.fst h))
  let bucket (a : Finset P) := N.filter (fun l=>B l=a)
  have fiber (a) (ha : a∈F) : (∑i∈bucket a,(B i).card)+1=a.card+(bucket a).card := by
    obtain ⟨i,hi,e⟩ := Finset.mem_image.mp ha
    have one : i∈bucket a := Finset.mem_filter.mpr ⟨hi,e⟩
    have big : (B i).Nonempty := (Finset.mem_filter.mp hi).2
    by_cases unit : a.card=1
    · have sums : (∑z∈bucket a,(B z).card)=∑_z∈bucket a,1 := Finset.sum_congr rfl (fun z hz=>by rw [(Finset.mem_filter.mp hz).2,unit])
      rw [sums,unit];simp [Nat.add_comm]
    · have u : bucket a={i} := by
        apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr one)
        intro z hz
        apply Finset.mem_singleton.mpr
        have eq := (Finset.mem_filter.mp hz).2
        have gt := Finset.card_pos.mpr (livePos a ha)
        exact same z i (eq.trans e.symm) (by rw [eq];omega)
      simp [u,e]
  constructor
  · have joined := Finset.sum_congr (s₁:=F) rfl (fun a ha=>fiber a ha)
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at joined
    have aggregate := Finset.sum_fiberwise_of_maps_to maps (fun i=>(B i).card)
    have nc := Finset.card_eq_sum_card_fiberwise (f:=B) (s:=N) (t:=F) maps
    change (∑a∈F,∑i∈bucket a,(B i).card)=_ at aggregate
    change N.card=∑a∈F,(bucket a).card at nc
    change (edges B).card+F.card=(∑a∈F,a.card)+N.card
    rw [total,←aggregate,nc];exact joined
  · by_cases small : (support B).card≤F.card
    · refine ⟨support B,∅,?_,by simp [small,Nat.min_eq_left small,F]⟩
      exact fun p l h=>Or.inl (Finset.mem_biUnion.mpr ⟨B l,maps l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,h⟩),h⟩)
    · let M := N.filter (fun l=>2≤(B l).card)
      let H := F.filter (fun a=>2≤a.card)
      let T := F.filter (fun a=>a.card=1)
      let A := T.biUnion id
      have mi : M.card≤H.card := Finset.card_le_card_of_injOn B
        (fun l hl=>Finset.mem_filter.mpr ⟨maps l (Finset.mem_filter.mp hl).1,(Finset.mem_filter.mp hl).2⟩)
        (fun i hi j hj e=>same i j e (Finset.mem_filter.mp hi).2)
      have ai : A.card≤T.card := calc
        _ ≤ ∑a∈T,a.card := Finset.card_biUnion_le
        _ = ∑_a∈T,1 := Finset.sum_congr rfl (fun a ha=>(Finset.mem_filter.mp ha).2)
        _ = _ := by simp
      have dis : Disjoint T H := by
        apply Finset.disjoint_left.mpr;intro a atT atH
        have x := (Finset.mem_filter.mp atT).2
        have y := (Finset.mem_filter.mp atH).2
        omega
      have cap : T.card+H.card≤F.card := by
        rw [←Finset.card_union_of_disjoint dis]
        exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      refine ⟨A,M,?_,?_⟩
      · intro p l hp
        have live : l∈N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp⟩
        by_cases high : 2≤(B l).card
        · exact Or.inr (Finset.mem_filter.mpr ⟨live,high⟩)
        · have z := Finset.card_pos.mpr (show (B l).Nonempty from ⟨p,hp⟩)
          exact Or.inl (Finset.mem_biUnion.mpr ⟨B l,Finset.mem_filter.mpr ⟨maps _ live,by omega⟩,hp⟩)
      · change _ ≤ min _ F.card;omega
end Labels2584

namespace Star2584

-- The proof-word semantics and its count-vector equivalence are from L_meta_3756.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section Circuit
private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

private def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

private def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

private lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

private lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

private lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

private lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
    (k : Fin C.size) :
    (evalFrom d op C.gates xs).getD (outWire n k) d =
      op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
        (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
  let front := evalFrom d op (C.gates.take k.val) xs
  have hf : front.length = outWire n k := by
    have hk : k.val ≤ C.gates.length := k.isLt.le
    simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
  have hsplit : evalFrom d op C.gates xs =
      evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
    simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
      List.take_append_drop]
  have hread (i : ℕ) (hi : i < outWire n k) :
      (evalFrom d op C.gates xs).getD i d = front.getD i d := by
    rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
  change (evalFrom d op C.gates xs).getD (outWire n k) d = _
  rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
  rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hf, inputs_two h k]

private lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

private def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

private def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

private def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

private lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

private lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

private lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

private lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (w : ℕ) :
    circuitValue C z w = true ↔
      ∃ t ∈ words n C w, ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ z a = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [value_input C z hb, words_input C hb]
      constructor
      · intro ht
        exact ⟨[w], rfl, fun i hi => ⟨⟨w, hb⟩, by simpa only [List.mem_singleton, eq_comm] using hi, ht⟩⟩
      · rintro ⟨t, ht, hp⟩
        have ht' : t = [w] := ht
        obtain ⟨a, ha, hz⟩ := hp w (by simp [ht'])
        exact (Fin.ext ha : a = ⟨w, hb⟩) ▸ hz
    · have h1 := ih _ (earlier h k 0)
      have h2 := ih _ (earlier h k 1)
      rw [value_gate h z k, words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true, wordOp, Set.mem_ofPred_eq, h1, h2]
        constructor
        · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
          exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
            (List.mem_append.mp hi).elim (htz i) (huz i)⟩
        · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
          exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
            ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
      · rw [ho]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true, wordOp, Set.mem_union, h1, h2]
        exact ⟨fun h => h.elim (fun ⟨t, ht, ha⟩ => ⟨t, Or.inl ht, ha⟩)
          (fun ⟨t, ht, ha⟩ => ⟨t, Or.inr ht, ha⟩),
          fun ⟨t, ht, ha⟩ => ht.elim (fun h => Or.inl ⟨t, h, ha⟩) (fun h => Or.inr ⟨t, h, ha⟩)⟩
    · simp [value_missing C z hb, words_missing n C hb]

private lemma words_nonempty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) : t ≠ [] := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, _, rfl⟩ := ht
        exact fun hh => ih _ (earlier h k 0) hu (List.append_eq_nil_iff.mp hh).1
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hb] at ht

end Circuit

section ReadWitness

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

private lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

private lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

private lemma mem_andStep_one (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 2 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 3

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 2 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

private def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 2).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 2))).getD w [] :=
  rfl

private lemma leaf_encode (S : List ℕ) (w : ℕ) :
    S.map (fun j => if j = w then min 1 (2 + 1) else 0) = encode S [w] := by
  unfold encode
  apply List.map_congr_left
  intro a _
  by_cases hea : a = w
  · simp [hea]
  · simp [hea, Ne.symm hea]

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (2 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec, leaf_encode]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 2 (andStep 2 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_one _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_one _ _ _).mp hx
        obtain ⟨t, ht, rfl, hts⟩ := ih _ (earlier h k 0) _ hx'
        obtain ⟨u, hu, rfl, hus⟩ := ih _ (earlier h k 1) _ hy
        refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_, fun i hi =>
          (List.mem_append.mp hi).elim (hts i) (hus i)⟩
        have hz' : z = encode S [] := by simpa [encode_nil] using hz
        rw [hz', encode_append, List.nil_append, encode_append]
      · rw [ho] at hv ⊢
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hp | hp
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 0) _ hp
          exact ⟨t, Or.inl ht, he, hs⟩
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 1) _ hp
          exact ⟨t, Or.inr ht, he, hs⟩
    · rw [vec_eval, List.getD_eq_default _ _ (by
        simpa [evalFrom_length, Circuit.size] using hb)] at hv
      simp at hv

private lemma encode_complete {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (t : List ℕ) (ht : t ∈ words n C w) (hs : ∀ i ∈ t, i ∈ S) :
    encode S t ∈ vecs n C S w := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
      simp only [List.getElem_map, List.getElem_range]
      rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      subst ht'
      have hw : w ∈ S := hs w (by simp)
      simp only [leafVectors, hw, ite_true, List.mem_singleton]
      exact (leaf_encode S w).symm
    · have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec]
      rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht ⊢
        change encode S t ∈ andStep 2 (andStep 2 [S.map (fun _ => 0)]
          (vecs n C S (operand C k 0))) (vecs n C S (operand C k 1))
        obtain ⟨t1, ht1, t2, ht2, rfl⟩ := ht
        have h1 := ih _ (earlier h k 0) t1 ht1 (fun i hi => hs i (List.mem_append_left _ hi))
        have h2 := ih _ (earlier h k 1) t2 ht2 (fun i hi => hs i (List.mem_append_right _ hi))
        refine (mem_andStep_one _ _ _).mpr ⟨encode S t1, ?_, encode S t2, h2,
          (encode_append S t1 t2).symm⟩
        refine (mem_andStep_one _ _ _).mpr ⟨encode S [], by simp [encode_nil], encode S t1, h1, ?_⟩
        rw [encode_append, List.nil_append]
      · rw [ho] at ht ⊢
        change encode S t ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew [])
        rw [mem_fold_insertNew, mem_fold_insertNew]
        rcases ht with ht | ht
        · exact Or.inl (Or.inr (ih _ (earlier h k 0) t ht hs))
        · exact Or.inr (ih _ (earlier h k 1) t ht hs)
    · rw [words_missing n C hb] at ht
      exact absurd ht (Set.notMem_empty t)

private lemma read_iff {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (S : List ℕ) :
    readsAtMost C n S 2 = true ↔
      ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 2 := by
  constructor
  · intro r
    obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
    obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
    refine ⟨t, ht, hts, fun i hi => ?_⟩
    have hv : min (t.count i) 3 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
    have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
    omega
  · rintro ⟨t, ht, hts, hc⟩
    refine List.any_eq_true.mpr ⟨encode S t, encode_complete h S _ t ht hts, ?_⟩
    refine List.all_eq_true.mpr fun a ha => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have := hc j hj
    exact decide_eq_true (by omega)

end ReadWitness


open PEqualNP.ReadK PEqualNP.TopForm

theorem structured : ∀ (n m : ℕ) (D : Circuit) (S : Bool → Finset ℕ),
      IsAO2 (n+m) D →
      (∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
        ∃ i < D.size, w = n+m+i ∧ (NestedCover.gateAt D i).op = GateOp.or ∧
          ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ S t) →
      (∀ i < D.size, (NestedCover.gateAt D i).op = GateOp.and →
        ∃ a b, (NestedCover.gateAt D i).inputs = [a,b] ∧ a ∈ S false ∧ b ∈ S true) →
      PEqualNP.ReadK.IsReadK (n+m) D 2 := by
  intro n m D S ao closed cross
  have rowEq (k : Fin D.size) : gateAt D k.val = row D k :=
    List.getD_eq_getElem _ _ k.isLt
  have pureWord (w : ℕ) : ∀ (s : Bool), w ∈ S s → ∀ t ∈ words (n+m) D w,
      ∃ a : ℕ, t = [a] ∧ decide (n ≤ a) = s := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro s hw t ht
      rcases closed s w hw with ⟨hlt,hcolor⟩ | ⟨i,hi,rfl,hop,ins⟩
      · rw [words_input D hlt] at ht
        exact ⟨w, ht, hcolor⟩
      · let k : Fin D.size := ⟨i,hi⟩
        have rEq : gateAt D i = row D k := rowEq k
        have rop : (row D k).op = GateOp.or := by simpa only [rEq] using hop
        change t ∈ words (n+m) D (outWire (n+m) k) at ht
        rw [words_gate ao k, rop] at ht
        have child (b : Fin 2) : operand D k b ∈ S s := by
          apply ins
          rw [rEq, inputs_two ao k]
          fin_cases b <;> simp
        rcases ht with ht | ht
        · exact ih _ (earlier ao k 0) s (child 0) t ht
        · exact ih _ (earlier ao k 1) s (child 1) t ht
  have simple (w : ℕ) : ∀ t ∈ words (n+m) D w, t.Nodup := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro t ht
      rcases wire_cases (n+m) D.size w with hb | ⟨k, rfl⟩ | hb
      · rw [words_input D hb] at ht
        have e : t = [w] := ht
        simp [e]
      · rw [words_gate ao k] at ht
        rcases op_kind ao k with hop | hop
        · rw [hop] at ht
          obtain ⟨u, hu, v, hv, rfl⟩ := ht
          have hgo : (gateAt D k.val).op = GateOp.and := by simpa only [rowEq k] using hop
          obtain ⟨a,b,inputs,ha,hb⟩ := cross k.val k.isLt hgo
          rw [rowEq k] at inputs
          have first : operand D k 0 = a := by simp [operand, inputs]
          have second : operand D k 1 = b := by simp [operand, inputs]
          obtain ⟨x, rfl, hx⟩ := pureWord (operand D k 0) false (by simpa only [first] using ha) u hu
          obtain ⟨y, rfl, hy⟩ := pureWord (operand D k 1) true (by simpa only [second] using hb) v hv
          have hxy : x ≠ y := by intro e; subst y; exact Bool.false_ne_true (hx.symm.trans hy)
          simp [hxy]
        · rw [hop] at ht
          exact ht.elim (ih _ (earlier ao k 0) t) (ih _ (earlier ao k 1) t)
      · rw [words_missing (n+m) D hb] at ht
        exact False.elim (Set.notMem_empty t ht)
  intro X prime
  have active : circuitValue D (setInput X) D.output = true := prime.1
  obtain ⟨t, ht, support⟩ := (value_eq_terms ao (setInput X) D.output).mp active
  apply (read_iff ao (setList X)).2
  refine ⟨t, ht, ?_, fun i _ => (List.nodup_iff_count_le_one.mp (simple _ t ht) i).trans (by decide)⟩
  intro i hi
  obtain ⟨a, rfl, ha⟩ := support i hi
  have hm : a ∈ X := of_decide_eq_true ha
  exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨by simp, decide_eq_true hm⟩, rfl⟩

end Star2584

namespace Star2584
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
theorem fromCover (p l : Nat) (E : Finset (Fin p × Fin l)) (A : Finset (Fin p)) (M : Finset (Fin l))
    (cover : ∀e∈E,e.1∈A ∨ e.2∈M) (s : Nat) (cost : E.card+A.card+M.card ≤ s+1) :
    ∃D : Circuit,IsAO2 (p+l) D ∧
    (∀x,circuitFun (p+l) D x=decide (∃a b,(a,b)∈E ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)) ∧
    D.size ≤ s ∧ PEqualNP.ReadK.IsReadK (p+l) D 2 := by
  obtain ⟨D,S,ao,sz,ok,closed,meet⟩ := PEqualNP.Outside.L_meta_3692 p l E A M cover
  exact ⟨D,ao,ok,by omega,structured p l D S ao closed meet⟩
end Star2584
namespace Main2584
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Labels2584 Clauses2584
variable {p l : Nat}

def split (Q : Finset (Fin (p+l))) := (Finset.univ.filter (fun i : Fin p=>Fin.castAdd l i∈Q),
  Finset.univ.filter (fun j : Fin l=>Fin.natAdd p j∈Q))

theorem input (Q : Finset (Fin (p+l))) (X : Finset (Fin p)) (Y : Finset (Fin l)) :
    (∃v∈Q,Fin.addCases (fun i=>decide (i∈X)) (fun j=>decide (j∈Y)) v=true) ↔
      (X∩(split Q).1).Nonempty ∨ (Y∩(split Q).2).Nonempty := by
  constructor
  · rintro ⟨v,hv,on⟩
    induction v using Fin.addCases with
    | left i => exact Or.inl ⟨i,Finset.mem_inter.mpr ⟨by simpa using on,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩⟩
    | right j => exact Or.inr ⟨j,Finset.mem_inter.mpr ⟨by simpa using on,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩⟩
  · rintro (⟨i,hi⟩|⟨j,hj⟩)
    · obtain ⟨a,b⟩ := Finset.mem_inter.mp hi
      exact ⟨Fin.castAdd l i,(Finset.mem_filter.mp b).2,by simpa using a⟩
    · obtain ⟨a,b⟩ := Finset.mem_inter.mp hj
      exact ⟨Fin.natAdd p j,(Finset.mem_filter.mp b).2,by simpa using a⟩

theorem layer (B : Fin l→Finset (Fin p)) (C : Circuit) (ao : IsAO2 (p+l) C)
    (correct : ∀x,circuitFun (p+l) C x=decide (∃i j,i∈B j ∧ x (Fin.castAdd l i)=true ∧ x (Fin.natAdd p j)=true))
    (o : Circuit4675.W (p+l) C) (out : o.val=C.output) (form : Circuit4675.CNF C ao o) :
    (Packs2584.allUnions (family B)).card + (support B).card + (live B).card≤C.size+3 := by
  classical
  let K0 := Circuit4675.clauses C ao o
  let K := K0.image (@split p l)
  have spec (X : Finset (Fin p)) (Y : Finset (Fin l)) :
      (∃j∈Y,(X∩B j).Nonempty) ↔ ∀c∈K,(X∩c.1).Nonempty ∨ (Y∩c.2).Nonempty := by
    let x : Fin (p+l)→Bool := Fin.addCases (fun i=>decide (i∈X)) (fun j=>decide (j∈Y))
    have sem := Circuit4675.semantics C ao o form x
    rw [out] at sem
    change circuitFun (p+l) C x=true ↔ _ at sem
    rw [correct,decide_eq_true_eq] at sem
    simp only [x,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq] at sem
    constructor
    · rintro ⟨j,y,i,ip⟩ c hc
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨xx,bb⟩ := Finset.mem_inter.mp ip
      exact (input Q X Y).mp (sem.mp ⟨i,j,bb,xx,y⟩ Q hQ)
    · intro h
      obtain ⟨i,j,b,xx,y⟩ := sem.mpr (fun Q hQ=>(input Q X Y).mpr (h _ (Finset.mem_image_of_mem _ hQ)))
      exact ⟨j,y,i,Finset.mem_inter.mpr ⟨xx,b⟩⟩
  have incl : Packs2584.allUnions (family B)⊆unions B := by
    intro U hu
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hu
    let J := (live B).filter (fun j=>B j∈D)
    refine Finset.mem_image.mpr ⟨J,Finset.mem_powerset.mpr (Finset.subset_univ _),?_⟩
    ext x
    constructor
    · intro h
      obtain ⟨j,hj,q⟩ := Finset.mem_biUnion.mp h
      exact Finset.mem_biUnion.mpr ⟨B j,(Finset.mem_filter.mp hj).2,q⟩
    · intro h
      obtain ⟨b,hb,xb⟩ := Finset.mem_biUnion.mp h
      obtain ⟨j,jlive,eq⟩ := Finset.mem_image.mp ((Finset.mem_powerset.mp hD) hb)
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨jlive,eq.symm ▸ hb⟩,eq.symm ▸ xb⟩
  have valid (j) (x) (h : x∈B j) : x∈support B :=
    Finset.mem_biUnion.mpr ⟨B j,Finset.mem_image_of_mem B (Finset.mem_filter.mpr ⟨Finset.mem_univ j,x,h⟩),h⟩
  have allU : support B∈unions B := by
    refine Finset.mem_image.mpr ⟨Finset.univ,by simp,?_⟩
    ext x
    constructor
    · rintro h
      obtain ⟨j,_,hx⟩ := Finset.mem_biUnion.mp h
      exact valid j x hx
    · rintro h
      obtain ⟨A,hA,hx⟩ := Finset.mem_biUnion.mp h
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hA
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hx⟩
  have zeroU : (∅ : Finset (Fin p))∈unions B := Finset.mem_image.mpr ⟨∅,by simp,by simp⟩
  have liveEq : (close B ∅)ᶜ=live B := by
    ext j
    simp [close,live,Finset.nonempty_iff_ne_empty]
  obtain ⟨Q,hQ,eqQ⟩ := Finset.mem_image.mp (necessary B K spec (support B) allU)
  obtain ⟨R,hR,eqR⟩ := Finset.mem_image.mp (necessary B K spec ∅ zeroU)
  have a := congrArg Prod.fst eqQ
  have b := congrArg Prod.snd eqR
  change (split Q).1=support B at a
  change (split R).2=(close B ∅)ᶜ at b
  rw [liveEq] at b
  let X := (support B).image (Fin.castAdd l)
  let Y := (live B).image (Fin.natAdd p)
  have xsub : X⊆Q := by
    intro x h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    have h : i∈(split Q).1 := a.symm ▸ hi
    exact (Finset.mem_filter.mp h).2
  have ysub : Y⊆R := by
    intro x h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    have h : j∈(split R).2 := b.symm ▸ hj
    exact (Finset.mem_filter.mp h).2
  have dis : Disjoint X Y := by
    apply Finset.disjoint_left.mpr;intro x hx hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp hy
    have z := congrArg Fin.val eq
    change p+j.val=i.val at z
    have := i.isLt;omega
  have xsize : X.card=(support B).card := Finset.card_image_of_injective _ (fun a b h=>by have e := congrArg Fin.val h;exact Fin.ext e)
  have ysize : Y.card=(live B).card := Finset.card_image_of_injective _ (fun a b h=>by
    have e := congrArg Fin.val h;change p+a.val=p+b.val at e;exact Fin.ext (by omega))
  have total := Finset.card_le_card (Finset.union_subset_union xsub ysub)
  rw [Finset.card_union_of_disjoint dis,xsize,ysize] at total
  have kcard := (Finset.card_le_card incl).trans ((clauseCount B K spec).trans (show K.card≤K0.card from Finset.card_image_le))
  have cap := Circuit4675.cost C ao o hQ hR
  change K0.card+_≤_ at cap
  omega

theorem normalize (p l : Nat) (I : Fin p→Fin l→Prop) [DecidableRel I] (C : Circuit)
    (linear : ∀a a' b b',a≠a'→b≠b'→¬(I a b ∧ I a b' ∧ I a' b ∧ I a' b'))
    (ao : IsAO2 (p+l) C)
    (correct : ∀x,circuitFun (p+l) C x=decide (∃a b,I a b ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true))
    (form : ∀o : Circuit4675.W (p+l) C,o.val=C.output→Circuit4675.CNF C ao o) :
    ∃D : Circuit,IsAO2 (p+l) D ∧
      (∀x,circuitFun (p+l) D x=decide (∃a b,I a b ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)) ∧
      D.size≤C.size ∧ PEqualNP.ReadK.IsReadK (p+l) D 2 := by
  classical
  let B (j : Fin l) := Finset.univ.filter (fun i=>I i j)
  have bmem (a b) : a∈B b ↔ I a b := by simp [B]
  have lin (i j) (ne : i≠j) : (B i∩B j).card≤1 := by
    apply Finset.card_le_one.mpr;intro a ha b hb;by_contra ab
    obtain ⟨ai,aj⟩ := Finset.mem_inter.mp ha
    obtain ⟨bi,bj⟩ := Finset.mem_inter.mp hb
    exact linear a b i j ab ne ⟨(bmem ..).mp ai,(bmem ..).mp aj,(bmem ..).mp bi,(bmem ..).mp bj⟩
  have clean (u) (hu : u∈family B) : u.Nonempty := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hi).2
  have li (a) (ha : a∈family B) (b) (hb : b∈family B) (ne : a≠b) : (a∩b).card≤1 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    exact lin i j (fun h=>ne (congrArg B h))
  obtain ⟨book,A,M,cover,sz⟩ := bookkeeping B lin
  have budget : (edges B).card+A.card+M.card≤C.size+1 := by
    by_cases non : (family B).Nonempty
    · obtain ⟨U,hU⟩ := non
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨i,hi⟩ := clean (B j) hU
      have pos : circuitFun (p+l) C (fun _=>true)=true := by
        rw [correct,decide_eq_true_eq];exact ⟨i,j,(bmem ..).mp hi,rfl,rfl⟩
      have good : C.output < p+l+C.gates.length := by
        by_contra! no
        have z := PEqualNP.Outside.L_meta_4791.val_ge (C:=C) (x:=List.ofFn (fun _ : Fin (p+l)=>true)) (n:=p+l) (by simp) no
        exact Bool.false_ne_true (z.symm.trans pos)
      let o : Circuit4675.W (p+l) C := ⟨C.output,good⟩
      have cost := layer B C ao (by simpa only [bmem] using correct) o rfl (form o rfl)
      have lower := Bound2584.edgeBudget (family B) non clean li
      change (∑a∈family B,a.card)+min (support B).card (family B).card+2≤_ at lower
      change _≤(Packs2584.allUnions (family B)).card+(support B).card+(family B).card at lower
      omega
    · have z := Finset.not_nonempty_iff_eq_empty.mp non
      have liveZ : live B=∅ := by
        exact Finset.eq_empty_iff_forall_notMem.mpr (fun j hj=>by have h : B j∈family B:=Finset.mem_image_of_mem _ hj;simp [z] at h)
      simp [z,liveZ] at sz book;omega
  obtain ⟨D,dao,ok,cost,read⟩ := Star2584.fromCover p l (edges B) A M
    (fun e he=>cover e.1 e.2 ((memEdge B ..).mp he)) C.size budget
  exact ⟨D,dao,by simpa only [memEdge,bmem] using ok,cost,read⟩
end Main2584
