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
abbrev assumptions (c : C) := negLit '' (↑c : Set L)
def nonTaut (c : C) := ∀ l∈c, negLit l∉c
def Dead (s : Val) (c : C) := ∀ l∈c, Holds s (negLit l)
theorem twice (l : L) : negLit (negLit l)=l := by
  rcases l with ⟨v,b⟩
  cases b <;> rfl
theorem opposite_inconsistent {G : Set C} {A : Set L}
    (coh : ∀ l∈A, negLit l∉A)
    (clear : ¬∃ d∈G, ∀a∈d, UPForces G A (negLit a))
    {l : L} (pos : UPForces G A l) (neg : UPForces G A (negLit l)) : False := by
  cases pos with
  | hyp yes =>
    cases neg with
    | hyp no => exact coh _ yes no
    | @unit d z hd hz others =>
      apply clear
      refine ⟨d,hd,?_⟩
      intro a ha
      by_cases eq : a=negLit l
      · rw [eq,twice]
        exact UPForces.hyp yes
      · exact others a ha eq
  | @unit d z hd hz others =>
    apply clear
    refine ⟨d,hd,?_⟩
    intro a ha
    by_cases eq : a=l
    · subst a
      exact neg
    · exact others a ha eq

noncomputable def settled (G : Set C) (A : Set L) (v : V) : Option Bool := by
  classical
  exact if UPForces G A (v,true) then some true else if UPForces G A (v,false) then some false else none
theorem settled_iff {G : Set C} {A : Set L}
    (coh : ∀ l∈A, negLit l∉A)
    (clear : ¬∃ d∈G, ∀a∈d, UPForces G A (negLit a))
    (l : L) : Holds (settled G A) l ↔ UPForces G A l := by
  classical
  rcases l with ⟨v,b⟩
  by_cases up : UPForces G A (v,true)
  · have dn : ¬UPForces G A (v,false) := opposite_inconsistent coh clear up
    cases b <;> simp [Holds,settled,up,dn]
  · by_cases dn : UPForces G A (v,false)
    · cases b <;> simp [Holds,settled,up,dn]
    · cases b <;> simp [Holds,settled,up,dn]

theorem semantic_rup {G : Set C} {c : C} (proper : nonTaut c) :
    IsRUP G c ↔ ∀s : Val, (∀d∈G, Safe s d) → ¬Dead s c := by
  constructor
  · intro r s safe
    exact rup_not_dead safe r
  · intro can
    classical
    by_contra no
    let A := assumptions c
    have clear : ¬∃ d∈G, ∀a∈d, UPForces G A (negLit a) := no
    have coh : ∀ l∈A, negLit l∉A := by
      rintro _ ⟨u,hu,rfl⟩ ⟨v,hv,op⟩
      have eq : negLit v=u := op.trans (twice u)
      exact proper v hv (eq.symm ▸ hu)
    let s := settled G A
    have ok (l : L) : Holds s l ↔ UPForces G A l := settled_iff coh clear l
    have bSafe : ∀ d∈G, Safe s d := by
      intro d hd
      by_contra failed
      have notDead : ¬∀l∈d,Holds s (negLit l) := by
        intro all
        exact no ⟨d,hd,fun l hl => (ok _).mp (all l hl)⟩
      obtain ⟨a,ha,un,other⟩ := single_of_not_safe failed notDead
      have inferred : UPForces G A a := UPForces.unit hd ha (fun v hv ne => (ok _).mp (other v hv ne))
      have got := (ok a).mpr inferred
      simpa [Holds,un] using got
    apply can s bSafe
    intro l hl
    exact (ok _).mpr (UPForces.hyp ⟨l,hl,rfl⟩)

theorem safe_excludes_single {s : Val} {c : C} (sf : Safe s c) : ¬Single s c := by
  rintro ⟨a,ha,ua,others⟩
  rcases sf with ⟨v,hv,yes⟩|⟨v,hv,w,hw,ne,vu,wu⟩
  · by_cases eq : v=a
    · subst v
      simpa [Holds,ua] using yes
    · exact clash_holds yes (others _ hv eq)
  · by_cases eq : v=a
    · have h := others w hw (fun e => ne (eq.trans e.symm))
      simpa [Holds,negLit,wu] using h
    · have h := others v hv eq
      simpa [Holds,negLit,vu] using h

def BoardRun : List C → Prop
  | [] => True
  | c::rs => BoardRun rs ∧ ∀s : Val, BaseSafe s → Dead s c → ∃ d∈rs, Single s d

theorem board_exact {rs : List C} (normal : ∀c∈rs, nonTaut c) :
    IsRUPRun (PHP 6 5) rs ↔ BoardRun rs := by
  induction rs with
  | nil => exact ⟨fun _ => trivial,fun _ => IsRUPRun.nil⟩
  | cons c rs ih =>
    have tailOK : ∀d∈rs, nonTaut d := fun d h => normal d (List.mem_cons_of_mem _ h)
    have cOK := normal c List.mem_cons_self
    constructor
    · intro run
      cases run with
      | learn prev step =>
        refine ⟨(ih tailOK).mp prev,?_⟩
        intro s good dead
        by_contra! none
        have old := safe_run good prev none
        apply rup_not_dead (s:=s) (G:=PHP 6 5 ∪ {d|d∈rs}) _ step dead
        rintro d (hg|hp)
        · exact good d hg
        · exact old d hp
    · rintro ⟨prev,hit⟩
      apply IsRUPRun.learn ((ih tailOK).mpr prev) ((semantic_rup cOK).mpr ?_)
      intro s all dead
      obtain ⟨d,hd,single⟩ := hit s (fun d hm => all d (Or.inl hm)) dead
      exact safe_excludes_single (all d (Or.inr hd)) single
end PEqualNP.Outside.L_meta_9471.Locality

namespace PEqualNP.Outside.L_meta_9471.Locality
theorem necessary_boards {rs : List C} (run : IsRUPRun (PHP 6 5) rs) : BoardRun rs := by
  induction run with
  | nil => trivial
  | @learn rs c prev step ih =>
    refine ⟨ih,?_⟩
    intro s good dead
    by_contra! none
    have old := safe_run good prev none
    apply rup_not_dead (s:=s) (G:=PHP 6 5 ∪ {d|d∈rs}) _ step dead
    rintro d (hg|hp)
    · exact good d hg
    · exact old d hp
theorem ending_empty {rs : List C} (run : IsRUPRun (PHP 6 5) rs) (out : (∅ : C)∈rs) :
    ∃ ts, IsRUPRun (PHP 6 5) ((∅ : C)::ts) ∧ ts.length+1≤rs.length := by
  induction run with
  | nil => simp at out
  | @learn rs c prev step ih =>
    rcases List.mem_cons.mp out with e|m
    · subst c
      exact ⟨rs,IsRUPRun.learn prev step,by simp⟩
    · obtain ⟨ts,rt,small⟩ := ih m
      exact ⟨ts,rt,by simp only [List.length_cons]; omega⟩

theorem pad (t : Nat) {rs : List C} (run : IsRUPRun (PHP 6 5) ((∅ : C)::rs)) :
    IsRUPRun (PHP 6 5) ((∅ : C)::(List.replicate t ∅ ++ rs)) := by
  induction t with
  | zero => simpa using run
  | succ t ih =>
    rw [List.replicate_succ,List.cons_append]
    apply IsRUPRun.learn ih
    exact ⟨∅,Or.inr List.mem_cons_self,by simp⟩
def Passes (s : Val) : List C → Prop
  | [] => True
  | c::cs => Passes s cs ∧ (Dead s c → ∃ d∈cs, Single s d)
theorem passes_all {rs : List C} (ok : BoardRun rs) {s : Val} (raw : BaseSafe s) :
    Passes s rs := by
  induction rs with
  | nil => trivial
  | cons d ds ih => exact ⟨ih ok.1,ok.2 s raw⟩

theorem finite_obstruction {I : Type} (sample : I → Val) (allSafe : ∀ i, BaseSafe (sample i))
    (cover : ∀ cs : List C, cs.length=19 → ∃ i, ¬ Passes (sample i) (∅::cs)) :
    ¬ (∃ rs : List C, IsRUPRun (PHP 6 5) rs ∧ (∅ : C)∈rs ∧ rs.length≤20) := by
  rintro ⟨rs,run,member,lim⟩
  obtain ⟨ts,short,bound⟩ := ending_empty run member
  let t := 19-ts.length
  have sz : (List.replicate t (∅ : C)++ts).length=19 := by
    simp only [List.length_append,List.length_replicate]
    dsimp [t]
    omega
  obtain ⟨i,bad⟩ := cover _ sz
  exact bad (passes_all (necessary_boards (pad t short)) (allSafe i))
end PEqualNP.Outside.L_meta_9471.Locality
