import PEqualNP.Outside.L_meta_17589
import PEqualNP.Outside.L_meta_3771

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Pencil3773
open PEqualNP.Outside.L_meta_17589_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

/-- A wire accepting all four singletons forces at least three merge gates in their carrier set. -/
theorem four_merges {n : ℕ} {D : Dag} (hS : Strict n D) (T : Finset (Fin n)) (card : T.card=4)
    (w : ℕ) (all : T⊆supp n D w) : 3≤(merges n D (carrierT n D T)).card := by
  classical
  let M (v : ℕ) := supp n D v ∩ T
  let K := merges n D (carrierT n D T)
  have sub (v : ℕ) : M v ⊆ T := Finset.inter_subset_right
  have full : supp n D w ∩ T=T := Finset.inter_eq_right.mpr all
  have three {a b c : ℕ} (ma : a∈K) (mb : b∈K) (mc : c∈K)
      (ab : M (n+a) ≠ M (n+b)) (ac : M (n+a)≠M (n+c)) (bc : M (n+b)≠M (n+c)) : 3≤K.card := by
    exact Finset.two_lt_card.mpr ⟨a,ma,b,mb,c,mc,fun e=>ab (e ▸ rfl),fun e=>ac (e ▸ rfl),fun e=>bc (e ▸ rfl)⟩
  obtain ⟨j,hj,_,ej,mj,first,splitj⟩ := sem_first_mask hS T T (by omega) w full
  change M (n+j)=T at ej
  have middle (v : ℕ) (before : v<n+j) (threeV : 3≤(M v).card) (proper : M v ⊂ T) : 3≤K.card := by
    obtain ⟨k,hk,early,ek,mk,_,splitk⟩ := sem_first_mask hS T (M v) (by omega) v rfl
    change M (n+k)=M v at ek
    rcases splitk with ⟨_,a,_⟩|⟨_,a,b,eq,_,_⟩
    · have big := Finset.card_lt_card a
      have mx := Finset.card_le_card (sub (opA D k))
      have equal : M (opA D k)=T := Finset.eq_of_subset_of_card_le (sub _) (by change _ < (M (opA D k)).card at big; omega)
      exact (first (opA D k) (by have aa := (hS k hk).1; omega) equal).elim
    · have helper (u : ℕ) (lt : M u ⊂ M v) (sz : 2≤(M u).card) : 3≤K.card := by
        obtain ⟨l,ml,el⟩ := k4_mask_gate hS T u sz
        change M (n+l)=M u at el
        apply three mj mk ml
        · rw [ej,ek]; exact proper.ne.symm
        · rw [ej,el]; exact (Finset.ssubset_of_ssubset_of_subset lt proper.le).ne.symm
        · rw [ek,el]; exact lt.ne.symm
      have union := Finset.card_union_le (M (opA D k)) (M (opB D k))
      change M (opA D k) ∪ M (opB D k)=M v at eq
      rw [eq] at union
      by_cases ha : 2≤(M (opA D k)).card
      · exact helper _ a ha
      · exact helper _ b (by omega)
  rcases splitj with ⟨_,a,_⟩|⟨_,a,b,eq,_,_⟩
  · exact absurd rfl (Finset.ssubset_of_ssubset_of_subset a Finset.inter_subset_right).ne
  · change M (opA D j) ∪ M (opB D j)=T at eq
    have s := Finset.card_union_le (M (opA D j)) (M (opB D j))
    rw [eq,card] at s
    by_cases x : 3≤(M (opA D j)).card
    · exact middle _ (hS j hj).1 x a
    by_cases y : 3≤(M (opB D j)).card
    · exact middle _ (hS j hj).2.1 y b
    obtain ⟨u,mu,eu⟩ := k4_mask_gate hS T (opA D j) (show 2≤(M _).card by omega)
    obtain ⟨v,mv,ev⟩ := k4_mask_gate hS T (opB D j) (show 2≤(M _).card by omega)
    change M (n+u)=M (opA D j) at eu
    change M (n+v)=M (opB D j) at ev
    apply three mj mu mv
    · rw [ej,eu]; exact a.ne.symm
    · rw [ej,ev]; exact b.ne.symm
    · rw [eu,ev]; intro bad; rw [bad,Finset.union_self] at eq; exact b.ne eq

/-- Cut capacity when all four members of T reach one wire. -/
theorem pencil {n : ℕ} {G : Fin n→Fin n→Prop} {D : Dag} (hg : sem_Gr G)
    (h : StrictLive n D) (hc : sem_Comp n G D) {pos : Fin n → ℕ×Bool} (hp : k4_Pos n G D pos)
    (T J : Finset (Fin n)) (four : T.card=4) (w : ℕ) (all : T⊆supp n D w)
    (seen : ∀i∈J,i∈ineligSet n D ∧ ∃ a∈T,G i a) :
    J.card+3+(eligSet n D).card≤8+Bplus n D := by
  classical
  obtain ⟨br,pure⟩ := sem_exists_pureBranch hg h.1 hc
  obtain ⟨sub,card⟩ := k4_exits_ge hp T J seen
  have e := Finset.card_le_card sub
  have b := k4_budget hg h hc br pure T
  have m := four_merges h.1 T four w all
  omega

abbrev V := Fin 26
abbrev X := Fin 13
def s (b : Bool) (i : X) : V := if b then Fin.natAdd 13 i else Fin.castAdd 13 i
def adj (a b : V) := decide ((a.val<13) ≠ (b.val<13)) &&
  [0,1,3,9].contains ((a.val+b.val)%13)
def pl : SimpleGraph V where
  Adj x y := adj x y=true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel pl.Adj := fun x y => inferInstanceAs (Decidable (adj x y=true))
private theorem injective (b : Bool) : Function.Injective (s b) := by
  cases b <;> intro a c eq <;> apply Fin.ext <;> have h := congrArg Fin.val eq <;> simp [s] at h <;> omega
private theorem apart (a b : X) : s false a≠s true b := by decide +revert +kernel
private theorem coverSide (b : Bool) (v : X) :
    ∀ x : X,∃ t∈pl.neighborFinset (s b v),pl.Adj (s b x) t := by decide +revert +kernel
private theorem sizeN : ∀ x : V,(pl.neighborFinset x).card=4 := by decide +kernel
private theorem field (b : Bool) (a b' : X) (ab : a≠b') :
    ∃u v : V, ∀i : X, ¬pl.Adj (s b a) (s (!b) i) → ¬pl.Adj (s b b') (s (!b) i) →
      pl.Adj (s (!b) i) u ∨ pl.Adj (s (!b) i) v := by decide +revert +kernel
private theorem thirdPoint : ∀v x y : V,∃z : V,pl.Adj v z ∧ x≠z ∧ y≠z := by decide +kernel
private theorem common (b : Bool) (a c : X) : ∃z : V,pl.Adj z (s b a) ∧ pl.Adj z (s b c) := by
  decide +revert +kernel
private theorem triple (b : Bool) (a c d : X) (ac : a≠c) (ad : a≠d) (cd : c≠d) :
    (Finset.univ.filter fun i : X => ¬pl.Adj (s b a) (s (!b) i) ∧
      ¬pl.Adj (s b c) (s (!b) i) ∧ ¬pl.Adj (s b d) (s (!b) i)).card≤4 := by decide +revert +kernel

private theorem few (A B : Finset X) (disj : ∀p∈A,∀l∈B,¬pl.Adj (s false p) (s true l)) :
    A.card≤3 ∨ B.card≤3 := by
  apply PEqualNP.Outside.L_meta_3771 A B
  intro p hp l hl ep
  apply disj _ hp _ hl
  have tab : ∀p l : X,p+l∈({0,1,3,9}:Finset X) → pl.Adj (s false p) (s true l) := by decide +kernel
  exact tab p l ep

def part (I : Finset V) (b : Bool) : Finset X := Finset.univ.filter fun i => s b i∈I
lemma cardParts (I : Finset V) : (part I false).card+(part I true).card=I.card := by
  classical
  have eq : (part I false).image (s false) ∪ (part I true).image (s true)=I := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv|hv
      all_goals
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp hi).2
    · intro hv
      obtain ⟨b,i,rfl⟩ := (show ∀v : V,∃b i,s b i=v by decide +kernel) v
      cases b
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩)
  have dj : Disjoint ((part I false).image (s false)) ((part I true).image (s true)) := by
    rw [Finset.disjoint_left]; rintro v hv hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp hw
    exact apart _ _ eq.symm
  have card := congrArg Finset.card eq
  rw [Finset.card_union_of_disjoint dj,Finset.card_image_of_injective _ (injective false),
    Finset.card_image_of_injective _ (injective true)] at card
  exact card

set_option maxHeartbeats 2000000 in
theorem twenty {D : Dag} (h : StrictLive 26 D) (hc : sem_Comp 26 pl.Adj D) : 20≤Bplus 26 D := by
  classical
  have hg : sem_Gr pl.Adj := by unfold sem_Gr; decide +kernel
  obtain ⟨pos,hpos⟩ := k4_assigned hg h hc
  obtain ⟨br,hbr⟩ := sem_exists_pureBranch hg h.1 hc
  let U:=eligSet 26 D
  let I:=ineligSet 26 D
  have tot : I.card+U.card=26 := inelig_card_add 26 D
  have paid : U.card≤Bplus 26 D := elig_le_Bplus h.1 br hbr
  have iffpart (b : Bool) (i : X) : i∈part I b ↔ s b i∈I := by simp [part]
  have sep (x y : V) (hx : x∈I) (hy : y∈I) : ¬pl.Adj x y := by
    intro hit; rcases sem_elig_cover hg h hc hit with t|t
    · exact (sem_mem_inelig.mp hx) t
    · exact (sem_mem_inelig.mp hy) t
  have bound (b : Bool) (min : (part I b).card≤(part I (!b)).card) : 20≤Bplus 26 D := by
    let A:=part I b
    let B:=part I (!b)
    have cs : A.card+B.card=I.card := by cases b <;> first |exact cardParts I|exact (Nat.add_comm _ _).trans (cardParts I)
    have pair (i : X) (hi : i∈A) (j : X) (hj : j∈B) :=
      sep _ _ ((iffpart b i).mp hi) ((iffpart (!b) j).mp hj)
    by_contra low
    have necessary : 7≤A.card+B.card := by omega
    have maj : 2≤B.card := by change A.card≤B.card at min; omega
    obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp maj
    obtain ⟨z,zi,zj⟩ := common (!b) i j
    have third := thirdPoint
    obtain ⟨t,zt,it,jt⟩ := third z (s (!b) i) (s (!b) j)
    have exits := k4_three_cons hg h hc hpos ((iffpart _ _).mp hi) ((iffpart _ _).mp hj)
      (fun eq=>ne (injective _ eq)) it jt zi zj zt
    have one := k4_budget hg h hc br hbr {z}
    have strict : U.card<Bplus 26 D := by
      change (exitArcs 26 D (carrierT 26 D {z})).card + _ + U.card ≤ 2*({z}:Finset V).card+Bplus 26 D at one
      rw [Finset.card_singleton] at one; omega
    have rich : 8≤A.card+B.card := by omega
    have small : A.card≤3 := by
      have ff := few (part I false) (part I true) (fun p hp l hl=>
        sep _ _ ((iffpart false _).mp hp) ((iffpart true _).mp hl))
      change A.card≤B.card at min
      cases b
      · exact ff.elim id (fun h=>min.trans h)
      · exact ff.elim (fun h=>min.trans h) id
    have two : A.card≤2 := by
      by_contra too
      obtain ⟨a,ha,c,hc',d,hd,ac,ad,cd⟩ := Finset.two_lt_card.mp (show 2<A.card by omega)
      have bound := triple b a c d ac ad cd
      have sub : B ⊆ Finset.univ.filter (fun i : X => ¬pl.Adj (s b a) (s (!b) i) ∧
          ¬pl.Adj (s b c) (s (!b) i) ∧ ¬pl.Adj (s b d) (s (!b) i)) := by
        intro t ht; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,pair _ ha _ ht,pair _ hc' _ ht,pair _ hd _ ht⟩
      have card := Finset.card_le_card sub; omega
    by_cases aa : 2≤A.card
    · obtain ⟨a,ha,c,hc',ac⟩ := Finset.one_lt_card.mp aa
      obtain ⟨u,v,cover⟩ := field b a c ac
      let J:=B.image (s (!b))
      have see : ∀t∈J,t∈I ∧ ∃a∈({u,v}:Finset V),pl.Adj t a := by
        rintro _ ht; obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ht
        refine ⟨(iffpart _ _).mp ht,?_⟩
        rcases cover t (pair _ ha _ ht) (pair _ hc' _ ht) with hu|hv
        · exact ⟨u,by simp,hu⟩
        · exact ⟨v,by simp,hv⟩
      obtain ⟨sub,card⟩ := k4_exits_ge hpos {u,v} J see
      have lhs := Finset.card_le_card sub
      have cap := k4_budget hg h hc br hbr {u,v}
      have twoT : ({u,v}:Finset V).card≤2 := by
        have ins := Finset.card_insert_le u ({v}:Finset V)
        simpa only [Finset.card_singleton] using ins
      have jc : J.card=B.card := Finset.card_image_of_injective _ (injective _)
      change _+_+U.card≤_ at cap; omega
    · let z:=s (!b) i
      let T:=pl.neighborFinset z
      let J:=B.image (s (!b))
      have inz : z∈I := (iffpart _ _).mp hi
      obtain ⟨_,_,all,_⟩ := hpos.1 z inz
      have full : T⊆supp 26 D (src D (pos z)) := fun x hx=>all x ((pl.mem_neighborFinset _ _).mp hx)
      have see : ∀t∈J,t∈I ∧ ∃a∈T,pl.Adj t a := by
        rintro _ ht; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
        exact ⟨(iffpart _ _).mp hq,coverSide (!b) i q⟩
      have cost := pencil hg h hc hpos T J (sizeN _) _ full see
      have jc : J.card=B.card := Finset.card_image_of_injective _ (injective _)
      change J.card+3+U.card≤_ at cost; omega
  by_cases cmp : (part I false).card≤(part I true).card
  · exact bound false cmp
  · exact bound true (Nat.le_of_lt (Nat.lt_of_not_ge cmp))

/-- Every monotone binary circuit computing the plane-incidence function needs at least 45 gates. -/
theorem unrestricted (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ sem_Edge pl.Adj x) : 45≤C.size := by
  classical
  have two (v : V) : ∃ a b,pl.Adj v a ∧ pl.Adj v b ∧ a≠b :=
    (show ∀ v : V, ∃ a b,pl.Adj v a ∧ pl.Adj v b ∧ a≠b by decide +kernel) v
  have nosingle (i : Fin 26) : ¬ sem_Edge pl.Adj (fun k => decide (k = i)) := by
    rintro ⟨u,v,huv,hu,hv⟩
    have hui : u = i := of_decide_eq_true hu
    have hvi : v = i := of_decide_eq_true hv
    exact huv.ne (hui.trans hvi.symm)
  have positive (i j : Fin 26) (hij : pl.Adj i j) :
      sem_Edge pl.Adj (fun k => decide (k = i) || decide (k = j)) :=
    ⟨i,j,hij,by simp,by simp⟩
  obtain ⟨D,hlive,hlen,hval⟩ := normalize_strictLive (n := 26) C hmono
    (by
      intro b
      let v : Fin 26 := ⟨0, by omega⟩
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
  have hcomp : sem_Comp 26 pl.Adj D := fun x => by rw [hval x]; exact hC x

  have mass := twenty hlive hcomp
  have balance := surplus_identity hlive
  have lower := Bplus_le_total 26 D
  omega
end Pencil3773
