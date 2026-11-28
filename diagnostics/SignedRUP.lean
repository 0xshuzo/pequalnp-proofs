import PEqualNP.Defs
open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9471.Switched
namespace Src
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

def Proper (c : C) : Prop := ∀ l∈c, negLit l∉c
def Dead (s : Val) (c : C) : Prop := ∀ l∈c, Holds s (negLit l)

theorem negneg (l : L) : negLit (negLit l)=l := by
  obtain ⟨v,b⟩ := l
  cases b <;> rfl

theorem capture {G : Set C} {c : C} (ok : Proper c) (bad : ¬ IsRUP G c) :
    ∃ s : Val, (∀ d∈G, Safe s d) ∧ Dead s c := by
  classical
  let A := negLit '' (↑c : Set L)
  let F := UPForces G A
  have fromAssum {l : L} (hl : F l) (hn : F (negLit l)) : l∈A := by
    cases hl with
    | hyp a => exact a
    | @unit d p hd hp other =>
      exfalso
      apply bad
      refine ⟨d,hd,?_⟩
      intro u hu
      by_cases e : u=l
      · subst u
        exact hn
      · exact other u hu e
  have noPair {l : L} (hl : F l) (hn : F (negLit l)) : False := by
    obtain ⟨a,ha,ra⟩ := fromAssum hl hn
    obtain ⟨b,hb,rb⟩ := fromAssum hn (by simpa only [negneg] using hl)
    have eq : b=l := by simpa only [negneg] using congrArg negLit rb
    exact ok a ha ((ra.trans eq.symm).symm ▸ hb)
  let s : Val := fun i => if F (i,true) then some true else if F (i,false) then some false else none
  have same (l : L) : Holds s l ↔ F l := by
    rcases l with ⟨v,b⟩
    have imp : F (v,true) → ¬ F (v,false) := fun x y => noPair x y
    cases b <;> by_cases ht : F (v,true) <;> by_cases hf : F (v,false) <;>
      simp_all [Holds,s]
  refine ⟨s,?_,?_⟩
  · intro d hd
    have live : ¬Dead s d := fun dead => bad ⟨d,hd,fun l hl => (same _).1 (dead l hl)⟩
    by_contra ns
    obtain ⟨l,hl,unknown,rest⟩ := single_of_not_safe ns live
    have h : Holds s l := (same l).2 (.unit hd hl (fun k hk ne => (same _).1 (rest k hk ne)))
    simp [Holds,unknown] at h
  · intro l hl
    exact (same _).2 (.hyp ⟨l,hl,rfl⟩)

end Src
namespace Dst
abbrev V := Fin 5 × Fin 4
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

def Proper (c : C) : Prop := ∀ l∈c, negLit l∉c
def Dead (s : Val) (c : C) : Prop := ∀ l∈c, Holds s (negLit l)

theorem negneg (l : L) : negLit (negLit l)=l := by
  obtain ⟨v,b⟩ := l
  cases b <;> rfl

theorem capture {G : Set C} {c : C} (ok : Proper c) (bad : ¬ IsRUP G c) :
    ∃ s : Val, (∀ d∈G, Safe s d) ∧ Dead s c := by
  classical
  let A := negLit '' (↑c : Set L)
  let F := UPForces G A
  have fromAssum {l : L} (hl : F l) (hn : F (negLit l)) : l∈A := by
    cases hl with
    | hyp a => exact a
    | @unit d p hd hp other =>
      exfalso
      apply bad
      refine ⟨d,hd,?_⟩
      intro u hu
      by_cases e : u=l
      · subst u
        exact hn
      · exact other u hu e
  have noPair {l : L} (hl : F l) (hn : F (negLit l)) : False := by
    obtain ⟨a,ha,ra⟩ := fromAssum hl hn
    obtain ⟨b,hb,rb⟩ := fromAssum hn (by simpa only [negneg] using hl)
    have eq : b=l := by simpa only [negneg] using congrArg negLit rb
    exact ok a ha ((ra.trans eq.symm).symm ▸ hb)
  let s : Val := fun i => if F (i,true) then some true else if F (i,false) then some false else none
  have same (l : L) : Holds s l ↔ F l := by
    rcases l with ⟨v,b⟩
    have imp : F (v,true) → ¬ F (v,false) := fun x y => noPair x y
    cases b <;> by_cases ht : F (v,true) <;> by_cases hf : F (v,false) <;>
      simp_all [Holds,s]
  refine ⟨s,?_,?_⟩
  · intro d hd
    have live : ¬Dead s d := fun dead => bad ⟨d,hd,fun l hl => (same _).1 (dead l hl)⟩
    by_contra ns
    obtain ⟨l,hl,unknown,rest⟩ := single_of_not_safe ns live
    have h : Holds s l := (same l).2 (.unit hd hl (fun k hk ne => (same _).1 (rest k hk ne)))
    simp [Holds,unknown] at h
  · intro l hl
    exact (same _).2 (.hyp ⟨l,hl,rfl⟩)

end Dst

structure Transfer where
  pull : Dst.Val → Src.Val
  image : Src.C → Option Dst.C
  discard : ∀ c, image c=none → ∀ s, Src.Safe (pull s) c
  safety : ∀ c d, image c=some d → ∀ s, Dst.Safe s d → Src.Safe (pull s) c
  death : ∀ c d, image c=some d → ∀ s, Dst.Dead s d → Src.Dead (pull s) c
  proper : ∀ c d, image c=some d → Dst.Proper d

def covers (T : Transfer) (G : Set Src.C) (H : Set Dst.C) : Prop :=
  ∀ c∈G, ∀ d, T.image c=some d → ∃ a∈H, a⊆d

theorem safeWeaken (s : Dst.Val) {a b : Dst.C} (sub : a⊆b) (h : Dst.Safe s a) :
    Dst.Safe s b := by
  rcases h with ⟨l,hl,yes⟩|⟨u,hu,v,hv,ne,eu,ev⟩
  · exact Or.inl ⟨l,sub hl,yes⟩
  · exact Or.inr ⟨u,sub hu,v,sub hv,ne,eu,ev⟩

theorem step (T : Transfer) {G : Set Src.C} {H : Set Dst.C}
    (maps : covers T G H) {c : Src.C} {d : Dst.C}
    (im : T.image c=some d) (rc : IsRUP G c) : IsRUP H d := by
  classical
  by_contra no
  obtain ⟨s,safe,dead⟩ := Dst.capture (T.proper c d im) no
  have ss : ∀ p ∈ G, Src.Safe (T.pull s) p := by
    intro p hp
    cases h : T.image p with
    | none => exact T.discard p h s
    | some q =>
      obtain ⟨a,ha,sub⟩ := maps p hp q h
      exact T.safety p q h s (safeWeaken s sub (safe a ha))
  exact Src.rup_not_dead ss rc (T.death c d im s dead)

theorem program (T : Transfer) {G : Set Src.C} {H : Set Dst.C}
    (maps : covers T G H) {xs : List Src.C} (r : IsRUPRun G xs) :
    IsRUPRun H (xs.filterMap T.image) := by
  induction r with
  | nil => exact .nil
  | @learn xs c prev ok ih =>
    cases mc : T.image c with
    | none => simpa [List.filterMap_cons,mc] using ih
    | some d =>
      simp only [List.filterMap_cons,mc]
      apply IsRUPRun.learn ih
      apply step T _ mc ok
      intro p hp e he
      rcases hp with fp|lp
      · obtain ⟨a,ha,sub⟩ := maps p fp e he
        exact ⟨a,Or.inl ha,sub⟩
      · exact ⟨e,Or.inr (List.mem_filterMap.mpr ⟨p,lp,he⟩),fun _ v => v⟩

theorem emptyProgram (T : Transfer) (emptyImage : T.image ∅=some ∅)
    {xs : List Src.C} (endAt : (∅ : Src.C)∈xs) : (∅ : Dst.C)∈xs.filterMap T.image :=
  List.mem_filterMap.mpr ⟨∅,endAt,emptyImage⟩

abbrev Sub := Src.V → Option Dst.L

def mlit (f : Sub) (p : Src.L) : Option Dst.L :=
  (f p.1).map (fun w => (w.1, if p.2 then w.2 else !w.2))
def preVal (f : Sub) (s : Dst.Val) (v : Src.V) : Option Bool :=
  match f v with
  | none => some false
  | some w => (s w.1).map fun t => decide (t=w.2)
def body (f : Sub) (c : Src.C) : Dst.C :=
  Finset.univ.filter (fun l => ∃ p∈c, mlit f p=some l)

theorem memBody (f : Sub) (c : Src.C) (l : Dst.L) :
    l∈body f c ↔ ∃ p∈c, mlit f p=some l := by simp [body]

theorem literalLaws {f : Sub} {s : Dst.Val} {p : Src.L} {w : Dst.L}
    (m : mlit f p=some w) :
    (Src.Holds (preVal f s) p ↔ Dst.Holds s w) ∧
    (Src.Holds (preVal f s) (negLit p) ↔ Dst.Holds s (negLit w)) ∧
    (preVal f s p.1=none ↔ s w.1=none) := by
  rcases p with ⟨p,b⟩
  rcases w with ⟨w,a⟩
  cases h : f p with
  | none => simp [mlit,h] at m
  | some v =>
    rcases v with ⟨v,d⟩
    cases d <;> cases b <;> simp [mlit,h] at m <;>
      obtain ⟨rfl,rfl⟩ := m <;> cases hv : s v with
      | none => simp [Src.Holds,Dst.Holds,preVal,negLit,h,hv]
      | some z => cases z <;> simp [Src.Holds,Dst.Holds,preVal,negLit,h,hv]

theorem liftSafe (f : Sub) (s : Dst.Val) (c : Src.C) (h : Dst.Safe s (body f c)) :
    Src.Safe (preVal f s) c := by
  rcases h with ⟨l,hl,yes⟩|⟨u,hu,v,hv,ne,eu,ev⟩
  · obtain ⟨p,hp,mp⟩ := (memBody f c l).1 hl
    exact Or.inl ⟨p,hp,(literalLaws mp).1.mpr yes⟩
  · obtain ⟨a,ha,ma⟩ := (memBody f c u).1 hu
    obtain ⟨b,hb,mb⟩ := (memBody f c v).1 hv
    refine Or.inr ⟨a,ha,b,hb,?_,(literalLaws ma).2.2.mpr eu,(literalLaws mb).2.2.mpr ev⟩
    intro eq
    subst b
    exact ne (Option.some.inj (ma.symm.trans mb))

theorem safeTaut (s : Dst.Val) (c : Dst.C) (bad : ¬Dst.Proper c) : Dst.Safe s c := by
  classical
  unfold Dst.Proper at bad
  push Not at bad
  obtain ⟨⟨v,b⟩,hb,hn⟩ := bad
  cases e : s v with
  | none =>
    refine Or.inr ⟨_,hb,_,hn,?_,e,e⟩
    intro eq
    have eb := congrArg Prod.snd eq
    cases b <;> simp [negLit] at eb
  | some t =>
    by_cases ht : t=b
    · exact Or.inl ⟨_,hb,ht ▸ e⟩
    · refine Or.inl ⟨_,hn,?_⟩
      cases b <;> cases t <;> simp_all [Dst.Holds,negLit]

def killed (f : Sub) (c : Src.C) : Prop := ∃ p∈c, f p.1=none ∧ p.2=false
noncomputable def paid (f : Sub) (c : Src.C) : Option Dst.C := by
  classical
  exact if killed f c ∨ ¬Dst.Proper (body f c) then none else some (body f c)

noncomputable def signed (f : Sub) : Transfer where
  pull := preVal f
  image := paid f
  discard := by
    intro c hc s
    unfold paid at hc
    split at hc
    next h =>
      rcases h with ⟨⟨v,b⟩,mem,ff,bb⟩|bad
      · exact Or.inl ⟨_,mem,by simpa [Src.Holds,preVal,ff] using congrArg some bb.symm⟩
      · exact liftSafe f s c (safeTaut s _ bad)
    next => simp at hc
  safety := by
    intro c d im s hs
    unfold paid at im
    split at im
    next => simp at im
    next =>
      obtain rfl := Option.some.inj im
      exact liftSafe f s c hs
  death := by
    intro c d im s dead p hp
    unfold paid at im
    split at im
    next => simp at im
    next good =>
      obtain rfl := Option.some.inj im
      cases e : f p.1 with
      | none =>
        have tr : p.2=true := by
          cases eb : p.2 with
          | true => rfl
          | false => exact (good (Or.inl ⟨p,hp,e,eb⟩)).elim
        simp [Src.Holds,negLit,preVal,e,tr]
      | some w =>
        let l : Dst.L := (w.1,if p.2 then w.2 else !w.2)
        have m : mlit f p=some l := by simp [mlit,e,l]
        exact (literalLaws m).2.1.mpr (dead l ((memBody f c l).2 ⟨p,hp,m⟩))
  proper := by
    intro c d im
    unfold paid at im
    split at im
    next => simp at im
    next good =>
      obtain rfl := Option.some.inj im
      exact Classical.byContradiction fun h => good (Or.inr h)

end PEqualNP.Outside.L_meta_9471.Switched
