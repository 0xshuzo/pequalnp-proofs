import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_166.ExclusiveTree
variable {V K : Type}
inductive Tree (V K : Type) where
  | stop (k : K)
  | query (v : V) (zero one : Tree V K)
def read (x : V→Bool) : Tree V K → K
  | .stop k => k
  | .query v l r => if x v then read x r else read x l
def leaves : Tree V K → List K
  | .stop k => [k]
  | .query _ l r => leaves l ++ leaves r

theorem appears (t : Tree V K) (x : V→Bool) : read x t ∈ leaves t := by
  induction t with
  | stop => simp [read,leaves]
  | query v l r hl hr => cases q : x v <;> simp_all [read,leaves]
def located (t : Tree V K) (B : Set (V→Bool)) (k : K) := ∀x∈B,read x t=k
def opp (A B : Set (V→Bool)) := ∃ v : V, ∃ b : Bool,
  (∀x∈A,x v=b) ∧ (∀y∈B,y v=(!b))

theorem localSide [DecidableEq K] (v : V) (l r : Tree V K) {A : Set (V→Bool)} {k : K}
    (has : A.Nonempty) (loc : located (.query v l r) A k)
    (once : (leaves (.query v l r)).count k=1) :
    ((∀x∈A,x v=false) ∧ located l A k ∧ (leaves l).count k=1) ∨
    ((∀x∈A,x v=true) ∧ located r A k ∧ (leaves r).count k=1) := by
  simp only [leaves,List.count_append] at once
  by_cases h : (leaves l).count k=0
  · right
    have fixed : ∀x∈A,x v=true := by
      intro x hx
      cases b : x v with
      | true => rfl
      | false =>
        have e:=loc x hx
        have w : read x l=k := by simpa [read,b] using e
        have isin : k ∈ leaves l := w ▸ appears l x
        exact False.elim ((List.count_eq_zero.mp h) isin)
    refine ⟨fixed,?_,by omega⟩
    intro x hx
    simpa [read,fixed x hx] using loc x hx
  · left
    have nil : (leaves r).count k=0 := by omega
    have fixed : ∀x∈A,x v=false := by
      intro x hx
      cases b : x v with
      | false => rfl
      | true =>
        have w : read x r=k := by simpa [read,b] using loc x hx
        have isin : k∈leaves r := w ▸ appears r x
        exact False.elim ((List.count_eq_zero.mp nil) isin)
    refine ⟨fixed,?_,by omega⟩
    intro x hx
    simpa [read,fixed x hx] using loc x hx

theorem exclusive [DecidableEq K] (t : Tree V K) {A B : Set (V→Bool)} {a b : K}
    (ha : A.Nonempty) (hb : B.Nonempty) (ne : a≠b)
    (la : located t A a) (lb : located t B b)
    (ca : (leaves t).count a=1) (cb : (leaves t).count b=1) : opp A B := by
  induction t with
  | stop k =>
    obtain ⟨x,hx⟩:=ha
    obtain ⟨y,hy⟩:=hb
    exact False.elim (ne ((la x hx).symm.trans (lb y hy)))
  | query v l r ihl ihr =>
    rcases localSide v l r ha la ca with aa|aa <;> rcases localSide v l r hb lb cb with bb|bb
    · exact ihl aa.2.1 bb.2.1 aa.2.2 bb.2.2
    · exact ⟨v,false,aa.1,bb.1⟩
    · exact ⟨v,true,aa.1,bb.1⟩
    · exact ihr aa.2.1 bb.2.1 aa.2.2 bb.2.2
end PEqualNP.Outside.L_pcx_166.ExclusiveTree
namespace PEqualNP.Outside.L_pcx_166.ExclusiveTree
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
abbrev C (V : Type) := Clause V
def sound (F : Set (C V)) (t : Tree V (C V)) (c : C V) :=
  (∀ d ∈ leaves t, d∈F) ∧ (∀ x, ¬ClauseSat x c → ¬ClauseSat x (read x t))
theorem build {F : Set (C V)} {π : List (C V)} (proof : IsDerivation F π) :
    ∀ c∈π, ∃t, sound F t c := by
  induction proof with
  | nil => simp
  | @ax xs c h raw ih =>
    intro d mem
    rcases List.mem_cons.mp mem with eq|old
    · subst d
      refine ⟨.stop c,?_,?_⟩
      · intro e he
        have same : e=c := by simpa [leaves] using he
        exact same.symm ▸ raw
      · intro x hx
        exact hx
    · exact ih d old
  | @res xs p n res prev hp hn rr ih =>
    intro d mem
    rcases List.mem_cons.mp mem with eq|old
    · subst d
      obtain ⟨v,pv,nv,resEq⟩:=rr
      obtain ⟨l,lr,ls⟩:=ih p hp
      obtain ⟨r,rr,rs⟩:=ih n hn
      refine ⟨.query v l r,?_,?_⟩
      · intro e he
        rcases List.mem_append.mp he with h|h
        · exact lr e h
        · exact rr e h
      · intro x hx
        cases bit : x v with
        | false =>
          simp only [read,bit,Bool.false_eq_true,ite_false]
          apply ls x
          rintro ⟨q,hm,sat⟩
          apply hx
          have ne : q ≠ (v,true) := by
            intro e
            subst q
            change x v=true at sat
            rw [bit] at sat
            contradiction
          exact ⟨q,by rw [resEq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,hm⟩),sat⟩
        | true =>
          simp only [read,bit,ite_true]
          apply rs x
          rintro ⟨q,hm,sat⟩
          apply hx
          have ne : q ≠ (v,false) := by
            intro e
            subst q
            change x v=false at sat
            rw [bit] at sat
            contradiction
          exact ⟨q,by rw [resEq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,hm⟩),sat⟩
    · exact ih d old
theorem sole {F : Set (C V)} {t : Tree V (C V)} (ok : sound F t ∅) {k : C V}
    (A : Set (V→Bool)) (privateOnly : ∀x∈A,∀c∈F, ¬ClauseSat x c → c=k) :
    located t A k := by
  intro x hx
  exact privateOnly x hx _ (ok.1 _ (appears t x)) (ok.2 x (by simp [ClauseSat]))
end PEqualNP.Outside.L_pcx_166.ExclusiveTree
