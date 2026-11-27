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
namespace PEqualNP.Outside.L_meta_9471.Locality
theorem taut_safe {c : C} (no : ¬ nonTaut c) (s : Val) : Safe s c := by
  classical
  unfold nonTaut at no
  push Not at no
  obtain ⟨l,hl,op⟩ := no
  rcases l with ⟨v,b⟩
  cases e : s v with
  | none =>
    exact Or.inr ⟨(v,b),hl,negLit (v,b),op,by intro z; have w := congrArg Prod.snd z; cases b <;> simp [negLit] at w,e,e⟩
  | some x =>
    by_cases eq : x=b
    · exact Or.inl ⟨(v,b),hl,eq ▸ e⟩
    · have flip := (by decide : ∀ u w : Bool, u≠w → u=(!w)) x b eq
      exact Or.inl ⟨negLit (v,b),op,by simpa [Holds,negLit,flip] using e⟩
noncomputable def normalList (xs : List C) := by
  classical
  exact xs.filter (fun c => decide (nonTaut c))
theorem normalizing {rs : List C} (run : IsRUPRun (PHP 6 5) rs) :
    IsRUPRun (PHP 6 5) (normalList rs) := by
  classical
  induction run with
  | nil => exact IsRUPRun.nil
  | @learn rs c earlier step ih =>
    by_cases ok : nonTaut c
    · rw [show normalList (c::rs)=c::normalList rs by simp [normalList,ok]]
      apply IsRUPRun.learn ih ((semantic_rup ok).mpr ?_)
      intro s localSafe
      apply rup_not_dead (s:=s) _ step
      rintro d (hg|hm)
      · exact localSafe d (Or.inl hg)
      · by_cases dt : nonTaut d
        · exact localSafe d (Or.inr (by simpa [normalList] using And.intro hm dt))
        · exact taut_safe dt s
    · simpa [normalList,ok] using ih
end PEqualNP.Outside.L_meta_9471.Locality

namespace PEqualNP.Outside.L_meta_9471.PrimeColumn

variable {V : Type} [DecidableEq V]
abbrev assumptions (c : Clause V) := negLit '' (↑c : Set (Literal V))
def clashes (G : Set (Clause V)) (B : Set (Literal V)) :=
  ∃ d∈G, ∀ l∈d, UPForces G B (negLit l)

theorem simulate {G H : Set (Clause V)} {A B : Set (Literal V)}
    (shrinks : ∀ d∈G, ∃ e∈H, e⊆d)
    (hypotheses : ∀ l∈A, UPForces H B l)
    (clean : ¬clashes H B) {l} (old : UPForces G A l) : UPForces H B l := by
  induction old with
  | hyp m => exact hypotheses _ m
  | @unit d k md hk other ih =>
    obtain ⟨e,he,sub⟩ := shrinks d md
    by_cases member : k∈e
    · exact .unit he member (fun z hz ne => ih z (sub hz) ne)
    · exact False.elim (clean ⟨e,he,fun z hz => ih z (sub hz) (fun eq => member (eq ▸ hz))⟩)

theorem shortenClause {G H : Set (Clause V)} {c e : Clause V}
    (shrinks : ∀ d∈G, ∃ f∈H, f⊆d)
    (reconstruct : ∀ l∈c, UPForces H (assumptions e) (negLit l))
    (old : IsRUP G c) : IsRUP H e := by
  change clashes H (assumptions e)
  by_contra clean
  obtain ⟨d,hd,dead⟩ := old
  obtain ⟨f,hf,sub⟩ := shrinks d hd
  apply clean
  refine ⟨f,hf,fun l hl => simulate shrinks ?_ clean (dead l (sub hl))⟩
  rintro _ ⟨z,hz,rfl⟩
  exact reconstruct z hz

theorem transform {G : Set (Clause V)} (f : Clause V → Clause V)
    (sub : ∀ c, f c⊆c)
    (reconstruct : ∀ H : Set (Clause V), G⊆H → ∀ c, ∀ l∈c,
      UPForces H (assumptions (f c)) (negLit l))
    {cs} (run : IsRUPRun G cs) : IsRUPRun G (cs.map f) := by
  induction run with
  | nil => exact IsRUPRun.nil
  | @learn cs c prev step ih =>
    apply IsRUPRun.learn ih (shortenClause ?_ (reconstruct _ (fun _ hg => Or.inl hg) c) step)
    rintro d (base|learned)
    · exact ⟨d,Or.inl base,fun _ m => m⟩
    · exact ⟨f d,Or.inr (List.mem_map.mpr ⟨d,learned,rfl⟩),sub d⟩

abbrev Cell := Fin 6 × Fin 5
abbrev C := Clause Cell
abbrev L := Literal Cell

def keep (c : C) (l : L) : Prop :=
  l.2=false ∨ ∀ q : Fin 6, q≠l.1.1 → ((q,l.1.2),false)∉c
noncomputable def reduced (c : C) : C := by
  classical
  exact c.filter (keep c)

theorem sub (c : C) : reduced c⊆c := by
  classical
  exact Finset.filter_subset _ _
theorem remaining {c : C} {l : L} (m : l∈c) (k : keep c l) : l∈reduced c := by
  classical
  exact Finset.mem_filter.mpr ⟨m,k⟩

theorem recover (H : Set C) (incl : PHP 6 5⊆H) (c : C) (l : L) (m : l∈c) :
    UPForces H (assumptions (reduced c)) (negLit l) := by
  classical
  by_cases ok : keep c l
  · exact .hyp ⟨l,remaining m ok,rfl⟩
  rcases l with ⟨⟨p,h⟩,b⟩
  cases b with
  | false => exact False.elim (ok (Or.inl rfl))
  | true =>
    have bad : ∃ q : Fin 6, q≠p ∧ ((q,h),false)∈c := by
      by_contra no
      exact ok (Or.inr (fun q sep pos => no ⟨q,sep,pos⟩))
    obtain ⟨q,sep,old⟩ := bad
    let d : C := {((p,h),false),((q,h),false)}
    have hd : d∈H := incl (Or.inr ⟨p,q,h,Ne.symm sep,rfl⟩)
    change UPForces H (assumptions (reduced c)) ((p,h),false)
    apply UPForces.unit hd (by simp [d])
    intro z hz ne
    have side : z=((p,h),false) ∨ z=((q,h),false) := by simpa [d] using hz
    rcases side with eq|rfl
    · exact False.elim (ne eq)
    · exact .hyp ⟨((q,h),false),remaining old (Or.inl rfl),rfl⟩

theorem normalize {cs : List C} (run : IsRUPRun (PHP 6 5) cs) :
    IsRUPRun (PHP 6 5) (cs.map reduced) := transform reduced sub recover run

theorem exact_length_normal_form {cs : List C} (run : IsRUPRun (PHP 6 5) cs)
    (empty : (∅ : C)∈cs) :
    ∃ ds : List C, IsRUPRun (PHP 6 5) ds ∧ (∅ : C)∈ds ∧ ds.length=cs.length ∧
      ∀ d∈ds, ∀ (p q : Fin 6) (h : Fin 5), p≠q → ((p,h),true)∈d → ((q,h),false)∉d := by
  classical
  refine ⟨cs.map reduced,normalize run,?_,List.length_map ..,?_⟩
  · apply List.mem_map.mpr
    exact ⟨∅,empty,by simp [reduced]⟩
  · intro d mem p q h sep lit
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp mem
    have surv : keep c ((p,h),true) := (Finset.mem_filter.mp lit).2
    rcases surv with no|clean
    · cases no
    · intro neg
      exact clean q (Ne.symm sep) (sub c neg)

end PEqualNP.Outside.L_meta_9471.PrimeColumn

namespace PEqualNP.Outside.L_meta_9471.PrimeColumn
open PEqualNP.ProofComplexity PEqualNP.Search
variable {V : Type} [DecidableEq V]
abbrev pool (G : Set (Clause V)) (cs : List (Clause V)) := G ∪ {d | d∈cs}
abbrev prime (G : Set (Clause V)) (c : Clause V) := ∀ d, d⊂c → ¬ IsRUP G d

theorem minSub (G : Set (Clause V)) (c : Clause V) (valid : IsRUP G c) :
    ∃ b, b⊆c ∧ IsRUP G b ∧ prime G b := by
  classical
  let P (n : Nat) : Prop := ∃ b : Clause V, b⊆c ∧ IsRUP G b ∧ b.card=n
  have nonempty : ∃ n, P n := ⟨c.card,c,Finset.Subset.rfl,valid,rfl⟩
  obtain ⟨b,sub,good,num⟩ := Nat.find_spec nonempty
  refine ⟨b,sub,good,?_⟩
  intro d proper small
  have atLeast : Nat.find nonempty ≤ d.card :=
    Nat.find_min' nonempty ⟨d,Finset.Subset.trans (Finset.ssubset_iff_subset_ne.mp proper).1 sub,small,rfl⟩
  have lt := Finset.card_lt_card proper
  omega

inductive PrimeRun (G : Set (Clause V)) : List (Clause V) → Prop
  | nil : PrimeRun G []
  | learn {cs c} (prior : PrimeRun G cs) (step : IsRUP (pool G cs) c)
      (tight : prime (pool G cs) c) (fresh : ∀ b ∈ pool G cs, ¬ b⊆c) : PrimeRun G (c::cs)

theorem PrimeRun.run {G : Set (Clause V)} {cs} (pr : PrimeRun G cs) : IsRUPRun G cs := by
  induction pr with
  | nil => exact .nil
  | learn _ s _ _ ih => exact .learn ih s

theorem primeRestore {G : Set (Clause V)} {cs} (old : IsRUPRun G cs) :
    ∃ ds, PrimeRun G ds ∧ ds.length ≤ cs.length ∧
      ∀ d ∈ pool G cs, ∃ b ∈ pool G ds, b⊆d := by
  classical
  induction old with
  | nil =>
    exact ⟨[],.nil,by simp,fun d m => ⟨d,m,Finset.Subset.rfl⟩⟩
  | @learn cs c prev step ih =>
    obtain ⟨ds,pr,len,shrink⟩ := ih
    by_cases seen : ∃ b∈pool G ds, b⊆c
    · refine ⟨ds,pr,by simp; omega,?_⟩
      rintro d (hg|hl)
      · exact shrink d (Or.inl hg)
      · rcases List.mem_cons.mp hl with rfl|hm
        · exact seen
        · exact shrink d (Or.inr hm)
    · have feasible : IsRUP (pool G ds) c :=
        shortenClause shrink (fun l m => UPForces.hyp ⟨l,m,rfl⟩) step
      obtain ⟨b,bc,valid,tight⟩ := minSub _ c feasible
      have fresh : ∀ q∈pool G ds, ¬q⊆b := by
        intro q hq qs
        exact seen ⟨q,hq,Finset.Subset.trans qs bc⟩
      refine ⟨b::ds,.learn pr valid tight fresh,by simpa using len,?_⟩
      rintro d (hg|hl)
      · exact ⟨d,Or.inl hg,Finset.Subset.rfl⟩
      · rcases List.mem_cons.mp hl with rfl|hm
        · exact ⟨b,Or.inr (by simp),bc⟩
        · obtain ⟨e,he,ed⟩ := shrink d (Or.inr hm)
          refine ⟨e,?_,ed⟩
          rcases he with h|h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem primeRefutation {G : Set (Clause V)} (nonempty : (∅ : Clause V)∉G) {cs}
    (old : IsRUPRun G cs) (dead : (∅ : Clause V)∈cs) :
    ∃ ds, PrimeRun G ds ∧ ds.length≤cs.length ∧ (∅ : Clause V)∈ds := by
  obtain ⟨ds,ready,len,sub⟩ := primeRestore old
  obtain ⟨e,whereFrom,below⟩ := sub ∅ (Or.inr dead)
  have eq : e=∅ := Finset.Subset.antisymm below (Finset.empty_subset _)
  subst e
  exact ⟨ds,ready,len,whereFrom.resolve_left nonempty⟩

theorem primeColumn {G : Set C} (base : PHP 6 5⊆G) {c : C}
    (learn : IsRUP G c) (tight : prime G c) : reduced c=c := by
  by_contra wrong
  have ss : reduced c ⊂ c := Finset.ssubset_iff_subset_ne.mpr ⟨sub c,wrong⟩
  apply tight (reduced c) ss
  exact shortenClause (fun d hd => ⟨d,hd,Finset.Subset.rfl⟩) (recover G base c) learn

end PEqualNP.Outside.L_meta_9471.PrimeColumn

namespace PEqualNP.Outside.L_meta_9471.Column70
open PEqualNP.Outside.L_meta_9471.PrimeColumn
open PEqualNP.Outside.L_meta_9471.Locality (nonTaut normalList normalizing)
def Shape (c : C) := ∀ h : Fin 5,
  (∀ p : Fin 6, ((p,h),false)∉c) ∨ ∃ q : Fin 6,
    (∀ p : Fin 6, ((p,h),false)∈c ↔ p=q) ∧ ∀p : Fin 6, ((p,h),true)∉c

theorem prime_shape {cs : List C} (run : PrimeRun (PHP 6 5) cs) :
    ∀ c∈cs, nonTaut c → Shape c := by
  induction run with
  | nil => simp
  | @learn ds c prior step tight fresh ih =>
    intro d hm nt
    rcases List.mem_cons.mp hm with rfl|old
    · intro h
      by_cases absent : ∀ p : Fin 6, ((p,h),false)∉c
      · exact Or.inl absent
      classical
      push Not at absent
      obtain ⟨q,hit⟩ := absent
      refine Or.inr ⟨q,?_,?_⟩
      · intro p
        constructor
        · intro hp
          by_contra sep
          let pair : C := {((p,h),false),((q,h),false)}
          have ax : pair ∈ PHP 6 5 := Or.inr ⟨p,q,h,sep,rfl⟩
          exact fresh pair (Or.inl ax) (by simpa [pair] using And.intro hp hit)
        · rintro rfl
          exact hit
      · intro p hp
        have fixed := primeColumn (G:=pool (PHP 6 5) ds) (fun _ m => Or.inl m) step tight
        have pm : ((p,h),true)∈reduced c := by rwa [fixed]
        have ke := (Finset.mem_filter.mp pm).2
        rcases ke with wrong|disjoint
        · cases wrong
        · by_cases eq : q=p
          · subst p
            exact nt _ hp hit
          · exact disjoint q eq hit
    · exact ih d old nt

theorem column_program {cs : List C} (run : IsRUPRun (PHP 6 5) cs) (member : (∅ : C)∈cs) :
    ∃ ds : List C, IsRUPRun (PHP 6 5) ds ∧ (∅ : C)∈ds ∧
      ds.length≤cs.length ∧ ∀d∈ds, Shape d := by
  classical
  have base : (∅ : C)∉PHP 6 5 := by
    rintro (⟨p,e⟩|⟨p,q,h,_,e⟩)
    · have z : ((p,0),true)∈Finset.univ.image (fun j : Fin 5 => ((p,j),true)) :=
        Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
      rw [←e] at z
      simp at z
    · have z : ((p,h),false)∈({((p,h),false),((q,h),false)} : C) := by simp
      rw [←e] at z
      simp at z
  obtain ⟨xs,pr,lim,dead⟩ := primeRefutation (PHP 6 5) base run member
  have emptyNT : nonTaut (∅ : C) := by simp [nonTaut]
  refine ⟨normalList xs,normalizing pr.run,by simpa [normalList,emptyNT] using dead,?_,?_⟩
  · exact le_trans (List.length_filter_le ..) lim
  · intro d hm
    have pair : d∈xs ∧ nonTaut d := by simpa [normalList] using hm
    exact prime_shape pr d pair.1 pair.2
end PEqualNP.Outside.L_meta_9471.Column70
