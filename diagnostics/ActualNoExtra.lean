import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_178.AffineFree
abbrev Small := Fin 4 × Fin 3
inductive Symbol where
  | off
  | on
  | pos (u : Small)
  | neg (u : Small)
  | extra (id : { f : Finset Small // 2≤f.card }) (sign : Bool)
  deriving DecidableEq
def Compatible : Symbol → Symbol → Prop
  | .off, _ => True
  | _, .off => True
  | .pos u, .pos v => u.1≠v.1 ∧ u.2=v.2
  | .pos u, .neg v => u=v
  | .neg u, .pos v => u=v
  | .extra i s, .extra j t => i=j ∧ s≠t
  | _, _ => False

theorem fullThree : ∀ (c : Fin 4) (f : Fin 3→Fin 4), (∀i j, f i=f j → i=j) →
    (∀ i, f i≠c) → ∀ h, h≠c → ∃i,f i=h := by decide +kernel
theorem otherRow : ∀r : Fin 4, ∃ i : Fin 4, i≠r := by decide +kernel

theorem blockExtra (g : Fin 5→Fin 4→Symbol) (sel : Fin 4→Fin 5)
    (anchor : ∀ i j, ∃ h, g (sel i) h=.pos (i,j))
    (peer : ∀ i k h v, i≠k → g k h=.pos v → Compatible (g i h) (.pos v))
    (ban : ∀ i k h t b, i≠k → g i h=.on → g k h≠.extra t b)
    (mustFill : ∀ k c, (∀h,h≠c → g k h=.off) → g k c=.on) :
    ∀ k c t b, g k c ≠ .extra t b := by
  intro k c t b exotic
  have blocked (i : Fin 4) (j : Fin 3) : g (sel i) c ≠ .pos (i,j) := by
    intro hit
    by_cases e : k=sel i
    · rw [e,hit] at exotic
      cases exotic
    · have ok := peer k (sel i) c (i,j) e hit
      rw [exotic] at ok
      exact ok
  have fills (i : Fin 4) (h : Fin 4) (ne : h≠c) : ∃ j, g (sel i) h=.pos (i,j) := by
    choose f hf using anchor i
    have inj (a b : Fin 3) (eq : f a=f b) : a=b := by
      have aa:=hf a
      rw [eq,hf b] at aa
      simpa using aa.symm
    have away (a : Fin 3) (eq : f a=c) : False := blocked i a (eq ▸ hf a)
    obtain ⟨a,m⟩:=fullThree c f inj away h ne
    exact ⟨a,m ▸ hf a⟩
  have spare : ∃s : Fin 5, ∀i, sel i ≠ s := by
    by_contra! none
    have sur : Function.Surjective sel := none
    have sz:=Fintype.card_le_of_surjective sel sur
    simp at sz
  obtain ⟨s,sp⟩:=spare
  have zero (h : Fin 4) (hc : h≠c) : g s h=.off := by
    have adj (i : Fin 4) : ∃j, Compatible (g s h) (.pos (i,j)) := by
      obtain ⟨j,m⟩:=fills i h hc
      exact ⟨j,peer s (sel i) h (i,j) (Ne.symm (sp i)) m⟩
    cases e : g s h with
    | off => rfl
    | on =>
      obtain ⟨j,z⟩:=adj 0
      rw [e] at z
      exact False.elim z
    | pos u =>
      obtain ⟨j,z⟩:=adj u.1
      rw [e] at z
      exact False.elim (z.1 rfl)
    | neg u =>
      obtain ⟨i,ne⟩:=otherRow u.1
      obtain ⟨j,z⟩:=adj i
      rw [e] at z
      exact False.elim (ne (congrArg Prod.fst (show u=(i,j) from z)).symm)
    | extra id sign =>
      obtain ⟨j,z⟩:=adj 0
      rw [e] at z
      exact False.elim z
  have one:=mustFill s c zero
  by_cases sk : s=k
  · rw [sk,exotic] at one
    cases one
  · exact ban s k c t b sk one exotic
end PEqualNP.Outside.L_pcx_178.AffineFree
namespace PEqualNP.Outside.L_pcx_178.AffineFree
abbrev Board := Small→Bool
abbrev Interpretation := { f : Finset Small // 2≤f.card }→Bool→Board→Bool
def value (I : Interpretation) (x : Board) : Symbol→Bool
  | .off => false
  | .on => true
  | .pos u => x u
  | .neg u => !(x u)
  | .extra t s => I t s x
def RawPair (I : Interpretation) (a b : Symbol) : Prop :=
  (∀ x, ¬(value I x a=true ∧ value I x b=true)) ∨
    ∃ i j : Fin 4, ∃ h : Fin 3, i≠j ∧ a=.pos (i,h) ∧ b=.pos (j,h)
def RawRow (I : Interpretation) (g : Fin 4→Symbol) : Prop :=
  (∀ x, ∃h, value I x (g h)=true) ∨
  (∃i : Fin 4, ∀j : Fin 3, ∃h,g h=.pos (i,j)) ∨
  ∃ i j : Fin 4, ∃ h : Fin 3, i≠j ∧ (∃a,g a=.neg (i,h)) ∧ ∃a,g a=.neg (j,h)
def Rich (I : Interpretation) : Prop :=
  ∀t s u b, ∃ x, I t s x=true ∧ x u=b
def Proper (I : Interpretation) : Prop := ∀t s, ∃x, I t s x=false
private theorem hasOn (I : Interpretation) (rich : Rich I) (a : Symbol) (off : a≠.off) :
    ∃x,value I x a=true := by
  cases a with
  | off => exact False.elim (off rfl)
  | on => exact ⟨fun _=>false,rfl⟩
  | pos u => exact ⟨fun _=>true,rfl⟩
  | neg u => exact ⟨fun _=>false,rfl⟩
  | extra t s =>
    obtain ⟨x,v,_⟩:=rich t s ((0,0):Small) true
    exact ⟨x,v⟩
theorem positivePeer (I : Interpretation) (rich : Rich I) (a : Symbol) (u : Small)
    (ok : RawPair I a (.pos u)) : Compatible a (.pos u) := by
  rcases ok with no|⟨i,j,h,ne,rfl,eq⟩
  · cases a with
    | off => trivial
    | on => exact False.elim (no (fun _=>true) ⟨rfl,rfl⟩)
    | pos v => exact False.elim (no (fun _=>true) ⟨rfl,rfl⟩)
    | neg v =>
      change v=u
      by_contra ne
      exact no (fun z=>decide (z=u)) ⟨by simp [value,ne],by simp [value]⟩
    | extra t s =>
      obtain ⟨x,v,hit⟩:=rich t s u true
      exact False.elim (no x ⟨v,hit⟩)
  · cases eq
    exact ⟨ne,rfl⟩
theorem forcedOne (I : Interpretation) (proper : Proper I) {row : Fin 4→Symbol}
    (ok : RawRow I row) (c : Fin 4) (zeros : ∀h,h≠c → row h=.off) : row c=.on := by
  have remote {h} (ne : row h≠.off) : h=c := by by_contra off; exact ne (zeros h off)
  rcases ok with taut|⟨i,hit⟩|⟨i,j,h,ne,⟨a,ha⟩,b,hb⟩
  · have always (x : Board) : value I x (row c)=true := by
      obtain ⟨h,hh⟩:=taut x
      by_cases same : h=c
      · exact same ▸ hh
      · rw [zeros h same] at hh
        cases hh
    cases e : row c with
    | off => have hh:=always (fun _=>false); rw [e] at hh; cases hh
    | on => rfl
    | pos u => have hh:=always (fun _=>false); rw [e] at hh; cases hh
    | neg u => have hh:=always (fun _=>true); rw [e] at hh; cases hh
    | extra t s =>
      obtain ⟨x,hx⟩:=proper t s
      have hh:=always x
      rw [e] at hh
      change I t s x=true at hh
      rw [hx] at hh
      cases hh
  · obtain ⟨a,ha⟩:=hit 0
    obtain ⟨b,hb⟩:=hit 1
    have ac := remote (h:=a) (by rw [ha]; simp)
    have bc := remote (h:=b) (by rw [hb]; simp)
    rw [ac] at ha
    rw [bc,ha] at hb
    cases hb
  · have ac := remote (h:=a) (by rw [ha]; simp)
    have bc := remote (h:=b) (by rw [hb]; simp)
    rw [ac] at ha
    rw [bc,ha] at hb
    exact False.elim (ne (by simpa using hb))
end PEqualNP.Outside.L_pcx_178.AffineFree
namespace PEqualNP.Outside.L_pcx_178.AffineFree
def privateRow (r : Fin 4) (v : Small) := decide (v.1≠r ∧ v.2.val=v.1.val-(if r<v.1 then 1 else 0))
theorem wallActive : ∀r i : Fin 4, i≠r → ∃h,privateRow r (i,h)=true := by decide +kernel
theorem wallClear : ∀r i j : Fin 4, ∀h : Fin 3, i≠j → ¬(privateRow r (i,h)=true ∧
    privateRow r (j,h)=true) := by decide +kernel

theorem rawAnchors (I : Interpretation) (g : Fin 5→Fin 4→Symbol)
    (row : ∀ i, RawRow I (g i)) (pair : ∀i j h, i≠j → RawPair I (g i h) (g j h)) :
    ∀ r : Fin 4, ∃i : Fin 5, ∀j : Fin 3, ∃h, g i h=.pos (r,j) := by
  intro r
  by_contra absent
  have hitRow (i : Fin 5) : ∃h,value I (privateRow r) (g i h)=true := by
    rcases row i with taut|⟨k,coords⟩|⟨a,b,h,ne,⟨s,hs⟩,t,ht⟩
    · exact taut _
    · have diff : k≠r := fun eq=>absent ⟨i,eq ▸ coords⟩
      obtain ⟨j,on⟩:=wallActive r k diff
      obtain ⟨z,hz⟩:=coords j
      exact ⟨z,by rw [hz];exact on⟩
    · by_cases ah : privateRow r (a,h)=true
      · have f : privateRow r (b,h)=false := by
          cases bh : privateRow r (b,h) with
          | false => rfl
          | true => exact False.elim (wallClear r a b h ne ⟨ah,bh⟩)
        exact ⟨t,by simp [ht,value,f]⟩
      · exact ⟨s,by simp [hs,value,Bool.eq_false_iff.mpr ah]⟩
  choose sel good using hitRow
  have inj : Function.Injective sel := by
    intro i j eq
    by_contra ne
    have dj : value I (privateRow r) (g j (sel i))=true := eq.symm ▸ good j
    rcases pair i j (sel i) ne with dis|⟨a,b,h,ne',A,B⟩
    · exact dis _ ⟨good i,dj⟩
    · have p := good i
      rw [A] at p
      rw [B] at dj
      exact wallClear r a b h ne' ⟨p,dj⟩
  have sz:=Fintype.card_le_of_injective sel inj
  simp at sz

theorem rawNoExtra (I : Interpretation) (g : Fin 5→Fin 4→Symbol)
    (rich : Rich I) (proper : Proper I) (row : ∀ i, RawRow I (g i))
    (pair : ∀i j h, i≠j → RawPair I (g i h) (g j h)) :
    ∀ k c t b, g k c ≠ .extra t b := by
  choose sel anch using rawAnchors I g row pair
  apply blockExtra g sel anch
  · intro i k h v ne pos
    have ok:=pair i k h ne
    rw [pos] at ok
    exact positivePeer I rich _ _ ok
  · intro i k h t b ne on ex
    have ok:=pair i k h ne
    rw [on,ex] at ok
    rcases ok with dis|⟨_,_,_,_,bad,_⟩
    · obtain ⟨x,yes,_⟩:=rich t b ((0,0):Small) true
      exact dis x ⟨rfl,yes⟩
    · cases bad
  · intro k c zeros
    exact forcedOne I proper (row k) c zeros
end PEqualNP.Outside.L_pcx_178.AffineFree
namespace PEqualNP.Outside.L_pcx_178.AffineFree
open Finset
def parityOn (f : Finset Small) (x : Board) : Bool := decide (Odd ((f.filter (fun u=>x u=true)).card))
theorem parityAdd (f : Finset Small) (u : Small) (hu : u∉f) (x : Board) :
    parityOn (insert u f) x = (parityOn f x ^^ x u) := by
  cases h : x u
  · simp [parityOn,filter_insert,h]
  · have off : u∉f.filter (fun v=>x v=true) := fun m=>hu (mem_filter.mp m).1
    by_cases od : Odd ((f.filter fun v=>x v=true).card)
    · have no : ¬Odd ((f.filter fun v=>x v=true).card+1) := by
        rw [Nat.odd_iff] at od ⊢; omega
      simp [parityOn,filter_insert,h,card_insert_of_notMem off,od,no]
    · have yes : Odd ((f.filter fun v=>x v=true).card+1) := by
        rw [Nat.odd_iff] at od ⊢; omega
      simp [parityOn,filter_insert,h,card_insert_of_notMem off,od,yes]
def genuine : Interpretation := fun f s x => decide (parityOn f.val x=s)
theorem parityFiber (f : {f : Finset Small // 2≤f.card}) (s : Bool) (i : Small) (v : Bool) :
    ∃x : Board, parityOn f.val x=s ∧ x i=v := by
  have existsOther : ∃j∈f.val,j≠i := by
    by_contra! bad
    have sub : f.val ⊆ {i} := fun k mk => mem_singleton.mpr (bad k mk)
    have le := card_le_card sub
    have hi:=f.property
    simp only [card_singleton] at le
    omega
  obtain ⟨j,mj,ne⟩:=existsOther
  let first : Board:=fun z=>if z=i then v else false
  let P := f.val.erase j
  let root := parityOn P first
  let x : Board:=fun z=>if z=j then (root ^^ s) else first z
  have filt : (P.filter (fun z=>x z=true))=P.filter (fun z=>first z=true) := by
    ext z
    by_cases h : z=j
    · subst z
      simp [P]
    · simp [x,h]
  have same : parityOn P x=root := by
    change decide (Odd (P.filter (fun z=>x z=true)).card)=decide (Odd (P.filter (fun z=>first z=true)).card)
    rw [filt]
  have r := parityAdd P j (notMem_erase j f.val) x
  have ins : insert j P=f.val := insert_erase mj
  rw [ins,same] at r
  have atJ : x j=(root ^^ s) := by simp [x]
  rw [atJ] at r
  refine ⟨x,?_,by simp [x,first,Ne.symm ne]⟩
  rw [r]
  cases root <;> cases s <;> rfl
theorem actualRich : Rich genuine := by
  intro f s i v
  obtain ⟨x,a,b⟩:=parityFiber f s i v
  exact ⟨x,by simp [genuine,a],b⟩
theorem actualProper : Proper genuine := by
  intro f s
  obtain ⟨x,a,_⟩:=parityFiber f (!s) (0,0) true
  exact ⟨x,by cases s <;> simp_all [genuine]⟩
theorem noGenuineFree (g : Fin 5→Fin 4→Symbol) (row : ∀ i, RawRow genuine (g i))
    (pair : ∀i j h, i≠j → RawPair genuine (g i h) (g j h)) :
    ∀ k c t b, g k c ≠ .extra t b :=
  rawNoExtra genuine g actualRich actualProper row pair
end PEqualNP.Outside.L_pcx_178.AffineFree
