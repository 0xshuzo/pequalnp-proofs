import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9471.Locality

abbrev V := Fin 6 × Fin 5
abbrev L := Literal V
abbrev C := Clause V
abbrev Val := V → Option Bool
def Holds (s : Val) (l : L) := s l.1 = some l.2
def Safe (s : Val) (c : C) : Prop :=
  (∃ l ∈ c, Holds s l) ∨
  ∃ a ∈ c, ∃ b ∈ c, a ≠ b ∧ s a.1 = none ∧ s b.1 = none
def Single (s : Val) (c : C) : Prop :=
  ∃ a ∈ c, s a.1 = none ∧ ∀ b ∈ c, b ≠ a → Holds s (negLit b)
def Ext (s t : Val) := ∀ v b, s v = some b → t v = some b
def BaseSafe (s : Val) := ∀ c ∈ PHP 6 5, Safe s c

theorem clash_holds {s : Val} {l : L} (a : Holds s l) (b : Holds s (negLit l)) : False := by
  simp only [Holds,negLit] at a b
  cases l.2 <;> simp_all

theorem unknown_of_neither {s : Val} {l : L} (a : ¬ Holds s l) (b : ¬ Holds s (negLit l)) :
    s l.1 = none := by
  simp only [Holds,negLit] at a b
  cases e : s l.1 with
  | none => rfl
  | some v => cases v <;> cases l.2 <;> simp_all

theorem safe_forces {s : Val} {G : Set C} {A : Set L}
    (gs : ∀ c ∈ G, Safe s c) (hs : ∀ l ∈ A, Holds s l) {l : L} (h : UPForces G A l) : Holds s l := by
  induction h with
  | hyp a => exact hs _ a
  | @unit d l hd hl others ih =>
    rcases gs d hd with ⟨v,hv,yes⟩ | ⟨a,ha,b,hb,ne,ua,ub⟩
    · by_cases eq : v = l
      · exact eq ▸ yes
      · exact (clash_holds yes (ih v hv eq)).elim
    · by_cases eq : a = l
      · have hit := ih b hb (by simpa [← eq] using Ne.symm ne)
        simp [Holds,negLit,ub] at hit
      · have hit := ih a ha eq
        simp [Holds,negLit,ua] at hit

theorem rup_not_dead {s : Val} {G : Set C} (gs : ∀ c ∈ G, Safe s c) {c : C} (r : IsRUP G c) :
    ¬ (∀ l ∈ c, Holds s (negLit l)) := by
  intro dead
  obtain ⟨d,hd,forces⟩ := r
  have prem : ∀ l ∈ negLit '' (↑c : Set L), Holds s l := by
    rintro l ⟨v,hv,rfl⟩
    exact dead v hv
  rcases gs d hd with ⟨v,hv,yes⟩ | ⟨v,hv,_,_,_,uv,_⟩
  · exact clash_holds yes (safe_forces gs prem (forces v hv))
  · have hit := safe_forces gs prem (forces v hv)
    simp [Holds,negLit,uv] at hit

theorem single_of_not_safe {s : Val} {c : C} (ns : ¬ Safe s c) (nd : ¬ ∀ l ∈ c, Holds s (negLit l)) :
    Single s c := by
  classical
  push Not at nd
  obtain ⟨a,ha,hna⟩ := nd
  have noyes : ∀ l ∈ c, ¬ Holds s l := fun l hl yes => ns (Or.inl ⟨l,hl,yes⟩)
  have ua := unknown_of_neither (noyes a ha) hna
  refine ⟨a,ha,ua,?_⟩
  intro b hb ne
  by_contra nb
  exact ns (Or.inr ⟨a,ha,b,hb,Ne.symm ne,ua,unknown_of_neither (noyes b hb) nb⟩)

theorem safe_run {s : Val} (bs : BaseSafe s) {rs : List C} (run : IsRUPRun (PHP 6 5) rs)
    (no : ∀ c ∈ rs, ¬ Single s c) : ∀ c ∈ rs, Safe s c := by
  induction run with
  | nil => simp
  | @learn rs c prev rup ih =>
    have old := ih (fun d hd => no d (List.mem_cons_of_mem _ hd))
    have g : ∀ d ∈ PHP 6 5 ∪ {d | d ∈ rs}, Safe s d := by
      rintro d (h|h)
      · exact bs d h
      · exact old d h
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · by_contra bad
      exact no _ List.mem_cons_self (single_of_not_safe bad (rup_not_dead g rup))
    · exact old d hd

def Hole (l : L) : Fin 5 := l.1.2
def occupied (c : C) := c.image Hole
def Trivial (c : C) : Prop :=
  (∃ v : V, (v,true)∈c ∧ (v,false)∈c) ∨
  (∃ (p q : Fin 6) (h : Fin 5), p≠q ∧ ((p,h),false)∈c ∧ ((q,h),false)∈c)
def pin (c : C) (v : V) : Option Bool :=
  if v.2∈occupied c then some (decide ((v,false)∈c)) else none
theorem pin_dead {c : C} (nt : ¬Trivial c) : ∀ l∈c, Holds (pin c) (negLit l) := by
  rintro ⟨v,b⟩ h
  have mem : v.2∈occupied c := Finset.mem_image.mpr ⟨(v,b),h,rfl⟩
  cases b with
  | false => simp [pin,Holds,negLit,mem,h]
  | true =>
    have no : (v,false)∉c := fun f => nt (Or.inl ⟨v,h,f⟩)
    simp [pin,Holds,negLit,mem,no]
theorem pin_safe {c : C} (nt : ¬Trivial c) {a b : Fin 5} (ab : a≠b)
    (ha : a∉occupied c) (hb : b∉occupied c) : BaseSafe (pin c) := by
  intro d hd
  rcases hd with ⟨p,rfl⟩ | ⟨p,q,h,pq,rfl⟩
  · apply Or.inr
    have mem (x : Fin 5) : ((p,x),true)∈Finset.univ.image (fun y : Fin 5 => ((p,y),true)) :=
      Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
    exact ⟨_,mem a,_,mem b,fun e => ab (congrArg (fun l : L => l.1.2) e),
      by simp [pin,ha],by simp [pin,hb]⟩
  · have mp : ((p,h),false)∈({((p,h),false),((q,h),false)} : C) := by simp
    have mq : ((q,h),false)∈({((p,h),false),((q,h),false)} : C) := by simp
    by_cases covered : h∈occupied c
    · by_cases first : ((p,h),false)∈c
      · have no : ((q,h),false)∉c := fun second => nt (Or.inr ⟨p,q,h,pq,first,second⟩)
        exact Or.inl ⟨_,mq,by simp [Holds,pin,covered,no]⟩
      · exact Or.inl ⟨_,mp,by simp [Holds,pin,covered,first]⟩
    · exact Or.inr ⟨_,mp,_,mq,fun e => pq (congrArg (fun z : L => z.1.1) e),
        by simp [pin,covered],by simp [pin,covered]⟩
theorem two_free {c : C} (lim : (occupied c).card≤3) : ∃a b : Fin 5, a≠b ∧ a∉occupied c ∧ b∉occupied c := by
  classical
  by_contra! no
  have bound : ((Finset.univ : Finset (Fin 5)) \ occupied c).card≤1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have aa := (Finset.mem_sdiff.mp ha).2
    have bb := (Finset.mem_sdiff.mp hb).2
    by_contra neq
    exact bb (no a b neq aa)
  have eq := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (occupied c))
  have sz : (Finset.univ : Finset (Fin 5)).card=5 := by decide
  omega
theorem trivial_not_single {s : Val} (safe : BaseSafe s) {c : C} (h : Trivial c) : ¬Single s c := by
  intro one
  obtain ⟨l,hl,un,rest⟩ := one
  rcases h with ⟨v,pos,neg⟩ | ⟨p,q,h,pq,ha,hb⟩
  · by_cases eq : (v,true)=l
    · subst l
      have hh := rest _ neg (by simp)
      simp [Holds,negLit,un] at hh
    · by_cases ex : (v,false)=l
      · subst l
        have hh := rest _ pos (by simp)
        simp [Holds,negLit,un] at hh
      · exact clash_holds (l:=(v,true)) (by simpa [Holds,negLit] using rest _ neg ex)
          (by simpa [Holds,negLit] using rest _ pos eq)
  · let d : C := {((p,h),false),((q,h),false)}
    have small : d∈PHP 6 5 := Or.inr ⟨p,q,h,pq,rfl⟩
    have sub : ∀ x∈d, x∈c := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | last
      · exact ha
      · exact Finset.mem_singleton.mp last ▸ hb
    rcases safe d small with ⟨z,hz,yes⟩ | ⟨a,am,b,bm,ne,an,bn⟩
    · by_cases eq : z=l
      · subst z
        simp [Holds,un] at yes
      · exact clash_holds yes (rest _ (sub _ hz) eq)
    · by_cases eq : a=l
      · have bad := rest _ (sub _ bm) (fun e => ne (eq.trans e.symm))
        simp [Holds,negLit,bn] at bad
      · have bad := rest _ (sub _ am) eq
        simp [Holds,negLit,an] at bad
theorem boundary_predecessor {c : C} {rs : List C} (run : IsRUPRun (PHP 6 5) rs)
    (learn : IsRUP (PHP 6 5 ∪ {d | d∈rs}) c) (nt : ¬Trivial c) (lim : (occupied c).card≤3) :
    ∃ d∈rs, ¬Trivial d ∧ ∃ l∈d, l.1.2∉occupied c ∧ ∀ w∈d, w≠l → w.1.2∈occupied c := by
  obtain ⟨a,b,ab,ha,hb⟩ := two_free lim
  have base := pin_safe nt ab ha hb
  have hit : ∃ d∈rs, Single (pin c) d := by
    by_contra! no
    have all := safe_run base run no
    have use : ∀ d∈PHP 6 5 ∪ {e | e∈rs}, Safe (pin c) d := by
      rintro d (hd|hd)
      · exact base d hd
      · exact all d hd
    exact rup_not_dead use learn (pin_dead nt)
  obtain ⟨d,hd,one⟩ := hit
  have non : ¬Trivial d := fun t => trivial_not_single base t one
  obtain ⟨l,hl,unknown,rest⟩ := one
  refine ⟨d,hd,non,l,hl,?_,?_⟩
  · by_contra loc
    simp [pin,loc] at unknown
  · intro w hw ne
    by_contra loc
    have hh := rest w hw ne
    simp [Holds,negLit,pin,loc] at hh

def KeepGame (P : Val → Prop) : Nat → Val → Prop
  | 0,s => P s
  | n+1,s => P s ∧ ∀ v, s v = none → ∃ t, Ext s t ∧ t v ≠ none ∧ KeepGame P n t

theorem ext_trans {s t u : Val} (a : Ext s t) (b : Ext t u) : Ext s u :=
  fun i j eq => b i j (a i j eq)

theorem avoidKept {P : Val → Prop} (k : Nat) (s : Val) (g : KeepGame P k s) (cs : Finset C) (small : cs.card ≤ k) :
    ∃ t, Ext s t ∧ P t ∧ ∀ c ∈ cs, ¬ Single t c := by
  classical
  induction k generalizing s cs with
  | zero =>
    have e : cs = ∅ := Finset.card_eq_zero.mp (by omega)
    subst cs
    exact ⟨s,fun _ _ h => h,g,by simp⟩
  | succ k ih =>
    by_cases hit : ∃ c ∈ cs, Single s c
    · obtain ⟨c,hc,a,ha,ua,forced⟩ := hit
      obtain ⟨t,st,ta,gt⟩ := g.2 a.1 ua
      obtain ⟨u,tu,bu,ok⟩ := ih t gt (cs.erase c) (by rw [Finset.card_erase_of_mem hc]; omega)
      have su := ext_trans st tu
      refine ⟨u,su,bu,?_⟩
      intro d hd
      by_cases eq : d = c
      · subst d
        rintro ⟨z,hz,uz,_⟩
        by_cases ez : z = a
        · subst z
          obtain ⟨b,eb⟩ := Option.ne_none_iff_exists'.mp ta
          have := tu a.1 b eb
          simp_all
        · have ea := forced z hz ez
          have := su z.1 (!z.2) ea
          simp_all
      · exact ok d (Finset.mem_erase.mpr ⟨eq,hd⟩)
    · push Not at hit
      exact ⟨s,fun _ _ h => h,g.1,hit⟩


theorem safe_not_single {s : Val} {c : C} (bs : Safe s c) : ¬Single s c := by
  rintro ⟨l,hl,un,rest⟩
  rcases bs with ⟨z,hz,yes⟩ | ⟨a,am,b,bm,ne,an,bn⟩
  · by_cases eq : z=l
    · subst z
      simp [Holds,un] at yes
    · exact clash_holds yes (rest _ hz eq)
  · by_cases eq : a=l
    · have bad := rest _ bm (fun e => ne (eq.trans e.symm))
      simp [Holds,negLit,bn] at bad
    · have bad := rest _ am eq
      simp [Holds,negLit,an] at bad
theorem earliest {cs : List C} (run : IsRUPRun (PHP 6 5) cs) (ne : cs≠[]) :
    ∃c∈cs, IsRUP (PHP 6 5) c := by
  induction run with
  | nil => contradiction
  | @learn rs c prev learn ih =>
    by_cases empty : rs=[]
    · subst rs
      exact ⟨c,List.mem_cons_self,by simpa using learn⟩
    · obtain ⟨d,hd,h⟩ := ih empty
      exact ⟨d,List.mem_cons_of_mem _ hd,h⟩
theorem not_empty_first : ¬IsRUP (PHP 6 5) (∅ : C) := by
  intro learn
  have nt : ¬Trivial (∅ : C) := by simp [Trivial]
  have sc : (occupied (∅ : C)).card≤3 := by simp [occupied]
  obtain ⟨x,hx,_⟩ := boundary_predecessor (rs:=[]) IsRUPRun.nil (by simpa using learn) nt sc
  simp at hx
theorem excludeEleven
    (firstGame : ∀ c : C, IsRUP (PHP 6 5) c → ∃s, KeepGame (fun t => BaseSafe t ∧ Safe t c) 9 s)
    (rs : List C) (run : IsRUPRun (PHP 6 5) rs) (out : (∅ : C)∈rs) (len : rs.length≤11) : False := by
  classical
  have non : rs≠[] := by intro e; simp [e] at out
  obtain ⟨c,mc,first⟩ := earliest run non
  have nonempty : c≠∅ := fun e => not_empty_first (e ▸ first)
  obtain ⟨s,g⟩ := firstGame c first
  let kept := (rs.toFinset.erase ∅).erase c
  have hm : (∅ : C)∈rs.toFinset := List.mem_toFinset.mpr out
  have cm : c∈rs.toFinset.erase ∅ := Finset.mem_erase.mpr ⟨nonempty,List.mem_toFinset.mpr mc⟩
  have small : kept.card≤9 := by
    simp only [kept,Finset.card_erase_of_mem cm,Finset.card_erase_of_mem hm]
    have size := List.toFinset_card_le (l:=rs)
    omega
  obtain ⟨t,_,⟨bt,ct⟩,others⟩ := avoidKept 9 s g kept small
  have none : ∀d∈rs, ¬Single t d := by
    intro d md
    by_cases he : d=∅
    · subst d
      simp [Single]
    · by_cases eq : d=c
      · subst d
        exact safe_not_single ct
      · exact others d (Finset.mem_erase.mpr ⟨eq,Finset.mem_erase.mpr ⟨he,List.mem_toFinset.mpr md⟩⟩)
  have bad := safe_run bt run none ∅ out
  simp [Safe] at bad
end PEqualNP.Outside.L_meta_9471.Locality
