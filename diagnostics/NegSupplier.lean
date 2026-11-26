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

end PEqualNP.Outside.L_meta_9471.Locality
namespace PEqualNP.Outside.L_meta_9471.Locality
def negOnly (d : C) := ∀l∈d, l.2=false
def noGood (M : Finset V) : C := M.image (fun v => (v,false))
def matching (M : Finset V) := ∀ i j h, (i,h)∈M → (j,h)∈M → i=j
def touch (M : Finset V) (v : V) := ∃u∈M, u.1=v.1 ∨ u.2=v.2
def blocked (rs : List C) (M : Finset V) (v : V) :=
  ∃d∈rs, ∀l∈d, l.1∈M ∨ l.1=v
def openCell (rs : List C) (M : Finset V) (v : V) :=
  v∉M ∧ ¬ touch M v ∧ ¬blocked rs M v
noncomputable def negBoard (rs : List C) (M : Finset V) (v : V) : Option Bool := by
  classical
  exact if v∈M then some true else if touch M v ∨ blocked rs M v then some false else none
theorem open_unknown {rs M v} (h : openCell rs M v) : negBoard rs M v=none := by
  simp [negBoard,h.1,h.2.1,h.2.2]
theorem false_or_unknown {rs M v} (h : v∉M) (nf : negBoard rs M v≠some false) : negBoard rs M v=none := by
  classical
  by_cases b : touch M v ∨ blocked rs M v <;> simp_all [negBoard]
theorem old_neg_safe {M rs d} (md : d∈rs) (neg : negOnly d) (outside : ∃a∈d,a.1∉M) :
    Safe (negBoard rs M) d := by
  classical
  by_cases hit : ∃l∈d, negBoard rs M l.1=some false
  · obtain ⟨l,hl,h⟩ := hit
    exact Or.inl ⟨l,hl,by simpa [Holds,neg l hl] using h⟩
  have off (l : L) (hl : l∈d) := fun e => hit ⟨l,hl,e⟩
  obtain ⟨a,ha,oa⟩ := outside
  have another : ∃b∈d, b.1∉M ∧ b.1≠a.1 := by
    by_contra! no
    have block : blocked rs M a.1 := by
      refine ⟨d,md,?_⟩
      intro l hl
      by_cases f : l.1∈M
      · exact Or.inl f
      · exact Or.inr (no l hl f)
    exact off a ha (by simp [negBoard,oa,block])
  obtain ⟨b,hb,ob,ab⟩ := another
  exact Or.inr ⟨a,ha,b,hb,fun e => ab (congrArg Prod.fst e.symm),
    false_or_unknown oa (off a ha),false_or_unknown ob (off b hb)⟩
theorem board_raw {rs M} (mat : matching M) (rows : ∀p : Fin 6,
    (∃h,(p,h)∈M) ∨ ∃a b : Fin 5, a≠b ∧ openCell rs M (p,a) ∧ openCell rs M (p,b)) :
    BaseSafe (negBoard rs M) := by
  classical
  intro d hd
  rcases hd with ⟨p,rfl⟩|⟨p,q,h,pq,rfl⟩
  · have mem (j : Fin 5) : ((p,j),true)∈Finset.univ.image (fun y : Fin 5 => ((p,y),true)) :=
      Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    rcases rows p with ⟨j,hj⟩|⟨a,b,ab,oa,ob⟩
    · exact Or.inl ⟨_,mem j,by simp [Holds,negBoard,hj]⟩
    · exact Or.inr ⟨_,mem a,_,mem b,fun e => ab (congrArg (fun l : L => l.1.2) e),
        open_unknown oa,open_unknown ob⟩
  · have mp : ((p,h),false)∈({((p,h),false),((q,h),false)} : C) := by simp
    have mq : ((q,h),false)∈({((p,h),false),((q,h),false)} : C) := by simp
    by_cases fp : negBoard rs M (p,h)=some false
    · exact Or.inl ⟨_,mp,fp⟩
    by_cases fq : negBoard rs M (q,h)=some false
    · exact Or.inl ⟨_,mq,fq⟩
    have np : (p,h)∉M := by
      intro mem
      have nq : (q,h)∉M := fun mm => pq (mat p q h mem mm)
      have t : touch M (q,h) := ⟨(p,h),mem,Or.inr rfl⟩
      exact fq (by simp [negBoard,nq,t])
    have nq : (q,h)∉M := by
      intro mem
      have t : touch M (p,h) := ⟨(q,h),mem,Or.inr rfl⟩
      exact fp (by simp [negBoard,np,t])
    exact Or.inr ⟨_,mp,_,mq,fun e => pq (congrArg (fun l : L => l.1.1) e),
      false_or_unknown np fp,false_or_unknown nq fq⟩

theorem negative_supplier {M rs} (mat : matching M)
    (old : ∀d∈rs, negOnly d ∧ ∃a∈d,a.1∉M)
    (rup : IsRUP (PHP 6 5 ∪ {d|d∈rs}) (noGood M)) :
    ∃p : Fin 6, (∀h,(p,h)∉M) ∧
      ∀a b : Fin 5, openCell rs M (p,a) → openCell rs M (p,b) → a=b := by
  classical
  by_contra! no
  have rows : ∀p : Fin 6, (∃h,(p,h)∈M) ∨ ∃a b : Fin 5, a≠b ∧ openCell rs M (p,a) ∧ openCell rs M (p,b) := by
    intro p
    by_cases yes : ∃h,(p,h)∈M
    · exact Or.inl yes
    · obtain ⟨a,b,oa,ob,ab⟩ := no p (by simpa using yes)
      exact Or.inr ⟨a,b,ab,oa,ob⟩
  have sf : ∀d∈PHP 6 5 ∪ {d|d∈rs}, Safe (negBoard rs M) d := by
    rintro d (raw|prev)
    · exact board_raw mat rows d raw
    · exact old_neg_safe prev (old d prev).1 (old d prev).2
  apply rup_not_dead sf rup
  intro l hl
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
  simp [Holds,negLit,negBoard,hv]
end PEqualNP.Outside.L_meta_9471.Locality
