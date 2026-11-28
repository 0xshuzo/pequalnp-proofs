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

namespace PEqualNP.Outside.L_meta_9471.SwitchInventory
open PEqualNP.ProofComplexity Finset
abbrev Big := Fin 6 × Fin 5
abbrev Small := Fin 5 × Fin 4
def pigeon (m n : Nat) (i : Fin m) : Clause (Fin m × Fin n) := univ.image (fun j => ((i,j),true))
def collision (m n : Nat) (i k : Fin m) (j : Fin n) : Clause (Fin m × Fin n) :=
  {((i,j),false),((k,j),false)}
def raw (m n : Nat) : Finset (Clause (Fin m × Fin n)) :=
  (univ.image (pigeon m n)) ∪
    ((univ.filter (fun v : Fin m × Fin m × Fin n => v.1≠v.2.1)).image
       (fun v => collision m n v.1 v.2.1 v.2.2))
theorem raw_spec {m n : Nat} {C : Clause (Fin m×Fin n)} : C∈raw m n ↔ C∈PHP m n := by
  simp only [raw,mem_union,mem_image,mem_univ,mem_filter,true_and]
  constructor
  · rintro (⟨i,rfl⟩|⟨⟨i,k,j⟩,ne,rfl⟩)
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨i,k,j,ne,rfl⟩
  · rintro (⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩)
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨⟨i,k,j⟩,ne,rfl⟩

def emb (p : Fin 6) (h : Fin 5) (u : Small) : Big := (p.succAbove u.1,h.succAbove u.2)
def lower (p : Fin 6) (h : Fin 5) (z : Big) : Small :=
  (⟨(z.1.val - (if p<z.1 then 1 else 0))%5, Nat.mod_lt _ (by decide)⟩,
   ⟨(z.2.val - (if h<z.2 then 1 else 0))%4, Nat.mod_lt _ (by decide)⟩)
def switch (p : Fin 6) (h : Fin 5) (u : Small) (z : Big) : Option (Small × Bool) :=
  if z=(p,h) then some (u,false)
  else if z=(p,(emb p h u).2) ∨ z=((emb p h u).1,h) then some (u,true)
  else if z=emb p h u ∨ z.1=p ∨ z.2=h then none
  else some (lower p h z,true)

def translate {A B : Type} [DecidableEq B] (f : A→Option (B×Bool)) (z : A×Bool) :
    Finset (B×Bool) :=
  match f z.1 with
  | none => ∅
  | some (w,s) => {(w,if z.2 then s else !s)}
def body {A B : Type} [DecidableEq B] (f : A→Option (B×Bool)) (c : Clause A) :=
  c.biUnion (translate f)
def paid {A B : Type} [DecidableEq A] [DecidableEq B] (f : A→Option (B×Bool)) (c : Clause A) : Bool :=
  decide (∀ z∈c, f z.1=none → z.2=true) &&
    decide (∀ z∈body f c, (z.1,!z.2)∉body f c)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem oneSwitch : let f := switch 5 4 (0,0)
    (((raw 6 5).filter (fun c=> paid f c)).image (body f))=raw 5 4 := by decide +kernel

end PEqualNP.Outside.L_meta_9471.SwitchInventory
namespace PEqualNP.Outside.L_meta_9471.SwitchInventory
open PEqualNP.ProofComplexity Finset
def clauseImage (p : Fin 6) (h : Fin 5) (u : Small) :=
  let f := switch p h u
  ((raw 6 5).filter (fun c=>paid f c)).image (body f)
end PEqualNP.Outside.L_meta_9471.SwitchInventory

namespace PEqualNP.Outside.L_meta_9471.Switched
open PEqualNP.ProofComplexity PEqualNP.Search
abbrev BigRaw := PEqualNP.Outside.L_meta_9471.SwitchInventory.Big
abbrev SmallRaw := PEqualNP.Outside.L_meta_9471.SwitchInventory.Small

theorem bodyAgreement (f : Sub) (c : Src.C) :
    body f c = PEqualNP.Outside.L_meta_9471.SwitchInventory.body f c := by
  ext l
  rw [memBody]
  simp only [PEqualNP.Outside.L_meta_9471.SwitchInventory.body,Finset.mem_biUnion]
  constructor
  · rintro ⟨p,hp,hit⟩
    refine ⟨p,hp,?_⟩
    cases eq : f p.1 with
    | none => simp [mlit,eq] at hit
    | some w =>
      have val : (w.1,if p.2 then w.2 else !w.2) = l := by simpa [mlit,eq] using hit
      simpa [PEqualNP.Outside.L_meta_9471.SwitchInventory.translate,eq] using val.symm
  · rintro ⟨p,hp,hit⟩
    refine ⟨p,hp,?_⟩
    cases eq : f p.1 with
    | none => simp [PEqualNP.Outside.L_meta_9471.SwitchInventory.translate,eq] at hit
    | some w =>
      have val : l = (w.1,if p.2 then w.2 else !w.2) := by simpa [PEqualNP.Outside.L_meta_9471.SwitchInventory.translate,eq] using hit
      simpa [mlit,eq] using val.symm

theorem invoice {f : Sub} {c : Src.C} {d : Dst.C} (bill : (signed f).image c=some d) :
    PEqualNP.Outside.L_meta_9471.SwitchInventory.paid f c=true ∧ PEqualNP.Outside.L_meta_9471.SwitchInventory.body f c=d := by
  change paid f c=some d at bill
  unfold paid at bill
  split at bill
  next => simp at bill
  next good =>
    have bd := Option.some.inj bill
    have pos : ∀ z∈c, f z.1=none → z.2=true := by
      intro z hz ff
      cases e : z.2 with
      | true => rfl
      | false => exact (good (Or.inl ⟨z,hz,ff,e⟩)).elim
    have prop : Dst.Proper (body f c) := Classical.byContradiction fun h => good (Or.inr h)
    have clean : ∀ z∈PEqualNP.Outside.L_meta_9471.SwitchInventory.body f c, (z.1,!z.2)∉PEqualNP.Outside.L_meta_9471.SwitchInventory.body f c := by
      rw [← bodyAgreement]
      exact prop
    exact ⟨by simp [PEqualNP.Outside.L_meta_9471.SwitchInventory.paid,pos,clean],(bodyAgreement f c).symm.trans bd⟩

theorem tableCovers (p : Fin 6) (h : Fin 5) (u : SmallRaw)
    (table : PEqualNP.Outside.L_meta_9471.SwitchInventory.clauseImage p h u ⊆ PEqualNP.Outside.L_meta_9471.SwitchInventory.raw 5 4) :
    covers (signed (PEqualNP.Outside.L_meta_9471.SwitchInventory.switch p h u)) (PHP 6 5) (PHP 5 4) := by
  intro c rawc d sc
  have pair := invoice sc
  have mem : d∈PEqualNP.Outside.L_meta_9471.SwitchInventory.clauseImage p h u := Finset.mem_image.mpr
    ⟨c,Finset.mem_filter.mpr ⟨PEqualNP.Outside.L_meta_9471.SwitchInventory.raw_spec.mpr rawc,pair.1⟩,pair.2⟩
  exact ⟨d,PEqualNP.Outside.L_meta_9471.SwitchInventory.raw_spec.mp (table mem),fun _ hh => hh⟩

theorem emptySigned (f : Sub) : (signed f).image ∅=some ∅ := by
  change paid f ∅=some ∅
  have e : body f ∅=∅ := by ext d; simp [memBody]
  simp [paid,killed,e,Dst.Proper]

theorem physicalSwitch (p : Fin 6) (h : Fin 5) (u : SmallRaw)
    (table : PEqualNP.Outside.L_meta_9471.SwitchInventory.clauseImage p h u ⊆ PEqualNP.Outside.L_meta_9471.SwitchInventory.raw 5 4) (xs : List Src.C)
    (r : IsRUPRun (PHP 6 5) xs) (last : (∅ : Src.C)∈xs) :
    IsRUPRun (PHP 5 4) (xs.filterMap (signed (PEqualNP.Outside.L_meta_9471.SwitchInventory.switch p h u)).image) ∧
    (∅ : Dst.C) ∈ xs.filterMap (signed (PEqualNP.Outside.L_meta_9471.SwitchInventory.switch p h u)).image :=
  ⟨program _ (tableCovers p h u table) r,emptyProgram _ (emptySigned _) last⟩

end PEqualNP.Outside.L_meta_9471.Switched


open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9471.Subsumed
variable {V : Type}

abbrev C (V : Type) := Clause V
def Extends (H G : Set (C V)) : Prop := ∀ c ∈ G, ∃ d ∈ H, d ⊆ c
def Conflict (H : Set (C V)) (A : Set (Literal V)) : Prop :=
  ∃ d ∈ H, ∀ l ∈ d, UPForces H A (negLit l)

theorem forces_of_cover {H G : Set (C V)} {A : Set (Literal V)} {u : Literal V}
    (cov : Extends H G) (clean : ¬ Conflict H A) (p : UPForces G A u) :
    UPForces H A u := by
  induction p with
  | hyp ha => exact .hyp ha
  | @unit c v hc hv others ih =>
    obtain ⟨d,hd,sub⟩ := cov c hc
    by_cases keep : v∈d
    · exact .unit hd keep (fun l hl ne => ih l (sub hl) ne)
    · exact (clean ⟨d,hd,fun l hl => ih l (sub hl) (fun eq => keep (eq ▸ hl))⟩).elim

theorem rup_of_cover {H G : Set (C V)} {c : C V}
    (cov : Extends H G) (r : IsRUP G c) : IsRUP H c := by
  classical
  by_contra bad
  obtain ⟨d,hd,v⟩ := r
  obtain ⟨e,he,sub⟩ := cov d hd
  exact bad ⟨e,he,fun l hl => forces_of_cover cov bad (v l (sub hl))⟩

def bank (F : Set (C V)) (xs : List (C V)) : Set (C V) := F ∪ {c | c∈xs}
def skip (F : Set (C V)) (xs : List (C V)) (c : C V) : Prop :=
  c ≠ ∅ ∧ ∃ d ∈ bank F xs, d ⊆ c

noncomputable def thin (F : Set (C V)) : List (C V) → List (C V) := by
  classical
  exact fun xs => xs.rec [] fun c tail previous => if skip F tail c then previous else c::previous

@[simp] theorem thin_nil (F : Set (C V)) : thin F []=[] := rfl
open Classical in
theorem thin_cons (F : Set (C V)) (c : C V) (xs : List (C V)) :
    thin F (c::xs) = if _ : skip F xs c then thin F xs else c::thin F xs := by
  classical
  by_cases h : skip F xs c <;> simp [thin,h]

theorem extThin (F : Set (C V)) (xs : List (C V)) : Extends (bank F (thin F xs)) (bank F xs) := by
  classical
  induction xs with
  | nil => exact fun c hc => ⟨c,hc,(fun _ h => h)⟩
  | cons c xs ih =>
    rw [thin_cons]
    by_cases z : skip F xs c
    · rw [dif_pos z]
      intro p hp
      rcases hp with hp|hp
      · exact ih p (Or.inl hp)
      · rcases List.mem_cons.mp hp with rfl|inOld
        · obtain ⟨_,d,hd,dc⟩ := z
          obtain ⟨e,he,ed⟩ := ih d hd
          exact ⟨e,he,fun l hl => dc (ed hl)⟩
        · exact ih p (Or.inr inOld)
    · rw [dif_neg z]
      intro p hp
      have lift {d : C V} : d∈bank F (thin F xs) → d∈bank F (c::thin F xs) := by
        rintro (hf|hl)
        · exact Or.inl hf
        · exact Or.inr (List.mem_cons_of_mem _ hl)
      rcases hp with hf|hl
      · exact ⟨p,Or.inl hf,(fun _ h => h)⟩
      · rcases List.mem_cons.mp hl with rfl|old
        · exact ⟨_,Or.inr List.mem_cons_self,(fun _ h => h)⟩
        · obtain ⟨d,hd,sub⟩ := ih p (Or.inr old)
          exact ⟨d,lift hd,sub⟩

theorem runThin (F : Set (C V)) {xs : List (C V)} (r : IsRUPRun F xs) :
    IsRUPRun F (thin F xs) := by
  classical
  induction r with
  | nil => exact .nil
  | @learn xs c prev step ih =>
    rw [thin_cons]
    split
    · exact ih
    · exact .learn ih (rup_of_cover (extThin F xs) step)

theorem emptyThin (F : Set (C V)) (xs : List (C V)) (e : (∅ : C V)∈xs) :
    (∅ : C V)∈thin F xs := by
  classical
  induction xs with
  | nil => simp at e
  | cons c xs ih =>
    rw [thin_cons]
    rcases List.mem_cons.mp e with eq|earlier
    · subst c
      simp [skip]
    · split
      · exact ih earlier
      · exact List.mem_cons_of_mem _ (ih earlier)

end PEqualNP.Outside.L_meta_9471.Subsumed

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9248.Leaf
namespace Generic
variable {V : Type} [DecidableEq V]

abbrev BoardClause (V : Type) := Clause V
def conflict (G : Set (Clause V)) (A : Set (Literal V)) : Prop :=
  ∃ d ∈ G, ∀ l ∈ d, UPForces G A (negLit l)
def db (F : Set (Clause V)) (cs : List (Clause V)) := F ∪ {d | d ∈ cs}

@[simp] theorem inv (l : Literal V) : negLit (negLit l) = l := by
  rcases l with ⟨x,b⟩
  cases b <;> rfl

theorem not_inv (l : Literal V) : negLit l ≠ l := by
  rcases l with ⟨x,b⟩
  cases b <;> simp [negLit]

theorem carry {G H : Set (Clause V)} {A B : Set (Literal V)}
    (sub : G ⊆ H) (initial : ∀ l ∈ A, UPForces H B l)
    {l} (force : UPForces G A l) : UPForces H B l := by
  induction force with
  | hyp h => exact initial _ h
  | unit hd hl _ ih => exact .unit (sub hd) hl ih

theorem substitute {G : Set (Clause V)} {c : Clause V} {B : Set (Literal V)}
    (learn : IsRUP G c) (assumeC : ∀ l ∈ c, UPForces G B (negLit l)) : conflict G B := by
  obtain ⟨d,hd,h⟩ := learn
  refine ⟨d, hd, fun l hl => carry (fun _ hs => hs) ?_ (h l hl)⟩
  rintro _ ⟨m,hm,rfl⟩
  exact assumeC _ hm

theorem splitClause {G : Set (Clause V)} {c : Clause V} {B : Set (Literal V)}
    (extra : ∀ k ∈ c, (∀ m ∈ c, m ≠ k → UPForces G B (negLit m)) → UPForces G B k)
    {l} (force : UPForces (G ∪ {c}) ∅ l) : UPForces G B l := by
  induction force with
  | hyp h => simp at h
  | @unit d k hd hk _ ih =>
    rcases hd with hd | hd
    · exact .unit hd hk ih
    · have e : d = c := hd
      subst d
      exact extra k hk ih

theorem terminalPair {G : Set (Clause V)} {c : Clause V}
    (base : ¬ conflict G ∅) (learn : IsRUP G c) (finish : conflict (G ∪ {c}) ∅) :
    ∃ l ∈ c, IsRUP G {l} ∧ IsRUP G {negLit l} := by
  classical
  have unitExists : ∃ l ∈ c, ∀ m ∈ c, m ≠ l → UPForces G ∅ (negLit m) := by
    by_contra missing
    have pass {z} (h : UPForces (G ∪ {c}) ∅ z) : UPForces G ∅ z :=
      splitClause (fun k hk other => False.elim (missing ⟨k,hk,other⟩)) h
    obtain ⟨d,hd,dead⟩ := finish
    rcases hd with hd | hd
    · exact base ⟨d,hd,fun k hk => pass (dead k hk)⟩
    · have e : d = c := hd
      subst d
      exact base (substitute learn (fun k hk => pass (dead k hk)))
  obtain ⟨l,ml,other⟩ := unitExists
  refine ⟨l,ml,?_,?_⟩
  · have bad : conflict G {negLit l} := by
      apply substitute learn
      intro m hm
      by_cases eq : m = l
      · subst m
        exact .hyp (by simp)
      · exact carry (fun _ h => h) (by simp) (other m hm eq)
    simpa [IsRUP,conflict] using bad
  · suffices bad : conflict G {l} by simpa [IsRUP,conflict] using bad
    by_contra clean
    have notOpp (h : UPForces G {l} (negLit l)) : False := by
      generalize e : negLit l = z at h
      cases h with
      | hyp hz =>
        have eq : _ = l := hz
        exact not_inv l (e.trans eq)
      | @unit d k hd hk rest =>
        apply clean
        refine ⟨d,hd,?_⟩
        intro m hm
        by_cases eq : m = negLit l
        · subst m
          rw [inv]
          exact .hyp (by simp)
        · exact rest m hm (fun hk => eq (hk.trans e.symm))
    have pass {z} (h : UPForces (G ∪ {c}) ∅ z) : UPForces G {l} z := by
      apply splitClause (c:=c) (B:={l}) _ h
      intro k hk other'
      by_cases eq : k = l
      · subst k
        exact .hyp (by simp)
      · exact False.elim (notOpp (other' l ml (Ne.symm eq)))
    obtain ⟨d,hd,dead⟩ := finish
    rcases hd with hd | hd
    · exact clean ⟨d,hd,fun k hk => pass (dead k hk)⟩
    · have e : d = c := hd
      subst d
      exact notOpp (pass (dead l ml))

theorem dbCons (F : Set (Clause V)) (c : Clause V) (cs : List (Clause V)) :
    db F (c :: cs) = db F cs ∪ {c} := by
  ext d
  simp [db,or_comm,or_left_comm,or_assoc]

theorem preceding {F : Set (Clause V)} {cs : List (Clause V)}
    (run : IsRUPRun F cs) (member : (∅ : Clause V) ∈ cs) :
    ∃ ps, IsRUPRun F ps ∧ ps.length < cs.length ∧ conflict (db F ps) ∅ := by
  induction run with
  | nil => simp at member
  | @learn ps c prev learn ih =>
    rcases List.mem_cons.mp member with eq | inTail
    · subst c
      exact ⟨ps,prev,by simp,by simpa [db,conflict,IsRUP] using learn⟩
    · obtain ⟨ts,tv,tl,tc⟩ := ih inTail
      exact ⟨ts,tv,by simp only [List.length_cons]; omega,tc⟩

theorem pairFromRoot {F : Set (Clause V)} (clean : ¬conflict F ∅) {cs : List (Clause V)}
    (run : IsRUPRun F cs) (root : conflict (db F cs) ∅) :
    ∃ ps, IsRUPRun F ps ∧ ps.length < cs.length ∧
      ∃ l : Literal V, IsRUP (db F ps) {l} ∧ IsRUP (db F ps) {negLit l} := by
  induction run with
  | nil => exact False.elim (clean (by simpa [db] using root))
  | @learn ps c prev learn ih =>
    by_cases earlier : conflict (db F ps) ∅
    · obtain ⟨ts,tv,tl,more⟩ := ih earlier
      exact ⟨ts,tv,by simp only [List.length_cons]; omega,more⟩
    · rw [dbCons] at root
      obtain ⟨l,_,a,b⟩ := terminalPair earlier learn root
      exact ⟨ps,prev,by simp,l,a,b⟩

theorem pairPrefix {F : Set (Clause V)} (clean : ¬conflict F ∅) {cs : List (Clause V)}
    (run : IsRUPRun F cs) (member : (∅ : Clause V) ∈ cs) :
    ∃ ps, IsRUPRun F ps ∧ ps.length + 2 ≤ cs.length ∧
      ∃ l : Literal V, IsRUP (db F ps) {l} ∧ IsRUP (db F ps) {negLit l} := by
  obtain ⟨qs,qv,ql,qc⟩ := preceding run member
  obtain ⟨ps,pv,pl,goal⟩ := pairFromRoot clean qv qc
  exact ⟨ps,pv,by omega,goal⟩


end Generic
abbrev V := Fin 12
abbrev L := Literal V
abbrev C := Clause V
abbrev Val := V → Option Bool
def Holds (s : Val) (l : L) := s l.1 = some l.2
def Safe (s : Val) (c : C) : Prop :=
  (∃ l ∈ c, Holds s l) ∨
  ∃ a ∈ c, ∃ b ∈ c, a ≠ b ∧ s a.1 = none ∧ s b.1 = none
def Single (s : Val) (c : C) : Prop :=
  ∃ a ∈ c, s a.1 = none ∧ ∀ b ∈ c, b ≠ a → Holds s (negLit b)
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

def clauseOf (p n : Nat) : C := Finset.univ.filter (fun l : L => (if l.2 then p else n).testBit l.1.val)
abbrev RawId := Fin 22
def terms : Array C := #[clauseOf 7 0, clauseOf 56 0, clauseOf 448 0, clauseOf 1536 0, clauseOf 0 9, clauseOf 0 18, clauseOf 0 36, clauseOf 0 65, clauseOf 0 72, clauseOf 0 130, clauseOf 0 144, clauseOf 0 260, clauseOf 0 288, clauseOf 0 513, clauseOf 0 520, clauseOf 0 576, clauseOf 0 1026, clauseOf 0 1040, clauseOf 0 1152, clauseOf 0 2052, clauseOf 0 2080, clauseOf 0 2304]
def term (i : RawId) := terms[i.val]!
def axs : Finset C := Finset.univ.image term
def Raw : Set C := ↑axs
def ons : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,256,0,0,256,0,0,256,256,32,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,32,32,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,1024,1024,1024,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,512,512,512,512,4,4]
def offs : Array Nat := #[0,2048,256,2304,128,2176,64,2112,32,2080,288,2336,160,2208,96,2144,16,2064,272,2320,144,2192,80,2128,8,2056,264,2312,136,2184,72,2120,4,2052,260,2308,132,2180,68,2116,36,2084,292,2340,292,2084,164,2212,2212,100,2148,2148,2276,2308,20,2068,276,2324,148,2196,84,2132,2324,12,2060,268,2316,140,2188,76,2124,2316,2332,2336,2,2050,258,2306,130,2178,66,2114,34,2082,290,2338,162,2210,98,2146,18,2066,274,2322,146,2194,146,2194,658,2706,82,2130,10,2058,266,2314,138,2186,74,2122,2338,1,2049,257,2305,129,2177,65,2113,33,2081,289,2337,161,2209,97,2145,17,2065,273,2321,145,2193,81,2129,9,2057,265,2313,137,2185,73,2121,73,2121,1097,3145,2337,2339]
def frontA : Array Nat := #[111,74,32,24,16,8,6,4,2,98,96,1]
def frontB : Array Nat := #[111,74,73,24,16,53,6,4,45,143,145,1]
def w0 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,148,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,147,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,135,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,127,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,119,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,117,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,113,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,148,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,147,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,135,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,127,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,119,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,117,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,113,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,112]
def w1 : Array Nat := #[148,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,110,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,102,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,82,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,80,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,78,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,76,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,75,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,148,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,110,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,102,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,82,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,80,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,78,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,76,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,75]
def w2 : Array Nat := #[111,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,74,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,147,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,110,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def w3 : Array Nat := #[135,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,102,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,71,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,135,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,102,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,71,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,25]
def w4 : Array Nat := #[127,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,127,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17]
def w5 : Array Nat := #[111,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,74,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,119,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,82,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,71,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def w6 : Array Nat := #[117,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,80,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,117,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,80,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7]
def w7 : Array Nat := #[115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,78,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,78,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5]
def w8 : Array Nat := #[111,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,74,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,113,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,76,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def w9 : Array Nat := #[0,148,0,0,127,0,0,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,102,0,0,72,0,0,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,80,0,0,22,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,145,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44]
def w10 : Array Nat := #[0,148,0,0,127,0,0,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,102,0,0,72,0,0,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,80,0,0,22,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,0,0,0,0,98,0,0,98,0,0,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44]
def w11 : Array Nat := #[112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,75,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,99,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,146,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,75,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,144,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,97,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def ws := #[w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11]
def cert (x p q : Nat) := (ws[x]!)[24*p+q]!
abbrev I := Fin 149
def index (i : Nat) : I := ⟨i%149,Nat.mod_lt _ (by decide)⟩
def board (i : I) : Val := fun v => if ons[i.val]!.testBit v.val then some true else if offs[i.val]!.testBit v.val then some false else none
def ea (x : V) : I := index (frontA[x.val]!)
def eb (x : V) : I := index (frontB[x.val]!)
def num (p : L) := p.1.val+(if p.2 then 0 else 12)
def cut (x : V) (p q : L) : I := index (cert x.val (num p) (num q))
def cap (x : V) (p q z : L) : Prop :=
  (z=p ∨ Holds (board (ea x)) (negLit z)) ∧ (z=q ∨ Holds (board (eb x)) (negLit z))
local instance (s : Val) (l : L) : Decidable (Holds s l) := by unfold Holds; infer_instance
local instance (s : Val) (c : C) : Decidable (Safe s c) := by unfold Safe; infer_instance
local instance (x : V) (p q z : L) : Decidable (cap x p q z) := by unfold cap; infer_instance
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 4096
theorem finiteRaw : ∀ (i : I) (j : RawId), Safe (board i) (term j) := by decide +kernel
theorem fixed : ∀ x : V, board (ea x) x ≠ none ∧ board (eb x) x ≠ none := by decide +kernel
def Result (x : V) (p q : L) : Prop :=
  let s := board (cut x p q)
  (∀ z, cap x p q z → Holds s (negLit z)) ∨
  (s x ≠ none ∧ (Holds s p ∨ Holds s q ∨ (p≠q ∧ s p.1=none ∧ s q.1=none)))
local instance (x : V) (p q : L) : Decidable (Result x p q) := by unfold Result; infer_instance
def Case (x : V) : Prop := ∀ p q : L, board (ea x) p.1=none → board (eb x) q.1=none →
    cap x p q p → cap x p q q → Result x p q
local instance (x : V) : Decidable (Case x) := by unfold Case; infer_instance
theorem c0 : Case 0 := by decide +kernel
theorem c1 : Case 1 := by decide +kernel
theorem c2 : Case 2 := by decide +kernel
theorem c3 : Case 3 := by decide +kernel
theorem c4 : Case 4 := by decide +kernel
theorem c5 : Case 5 := by decide +kernel
theorem c6 : Case 6 := by decide +kernel
theorem c7 : Case 7 := by decide +kernel
theorem c8 : Case 8 := by decide +kernel
theorem c9 : Case 9 := by decide +kernel
theorem c10 : Case 10 := by decide +kernel
theorem c11 : Case 11 := by decide +kernel
theorem finiteCuts (x : V) : Case x := by
  fin_cases x
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7
  · exact c8
  · exact c9
  · exact c10
  · exact c11
theorem raws (i : I) : ∀ d∈Raw, Safe (board i) d := by
  intro d hd
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
  exact finiteRaw i j

theorem met {G : Set C} {s : Val} {l : L}
    (safe : ∀ d∈G, Safe s d) (fixed : s l.1≠none)
    (u : IsRUP G {l}) (v : IsRUP G {negLit l}) : False := by
  obtain ⟨b,eq⟩ := Option.ne_none_iff_exists'.mp fixed
  by_cases e : b=l.2
  · apply rup_not_dead safe v
    intro z hz
    have ez := Finset.mem_singleton.mp hz
    subst z
    simpa [Generic.inv,Holds,e] using eq
  · apply rup_not_dead safe u
    intro z hz
    have ez := Finset.mem_singleton.mp hz
    subst z
    have be : b = !l.2 := by cases b <;> cases v' : l.2 <;> simp_all
    simpa [Holds,negLit,be] using eq

theorem hard (cs : List C) (run : IsRUPRun Raw cs) (out : (∅ : C) ∈ cs) : 4 ≤ cs.length := by
  classical
  by_contra! short
  have clean : ¬Generic.conflict Raw ∅ := by
    intro bad
    have r : IsRUP Raw (∅ : C) := by simpa [Generic.conflict,IsRUP] using bad
    exact rup_not_dead (raws 0) r (by simp)
  obtain ⟨ps,good,budget,l,left,right⟩ := Generic.pairPrefix clean run out
  have len : ps.length ≤ 1 := by omega
  let x := l.1
  cases ps with
  | nil => exact met (by simpa [Generic.db] using raws (ea x)) (fixed x).1 left right
  | cons h tl =>
    have nil : tl=[] := by cases tl <;> simp_all
    subst tl
    have hr : IsRUP Raw h := by cases good with | learn prev curr => simpa using curr
    have singles (i : I) (fx : board i x ≠ none) : Single (board i) h := by
      apply single_of_not_safe _ (rup_not_dead (raws i) hr)
      intro ok
      apply met (G:=Generic.db Raw [h]) (s:=board i) (l:=l) _ fx left right
      rintro d (hd|hd)
      · exact raws i d hd
      · have eq : d=h := List.mem_singleton.mp hd
        exact eq.symm ▸ ok
    obtain ⟨p,hp,up,ap⟩ := singles (ea x) (fixed x).1
    obtain ⟨q,hq,uq,aq⟩ := singles (eb x) (fixed x).2
    have small (z : L) (hz : z∈h) : cap x p q z := by
      constructor
      · by_cases e : z=p
        · exact Or.inl e
        · exact Or.inr (ap z hz e)
      · by_cases e : z=q
        · exact Or.inl e
        · exact Or.inr (aq z hz e)
    rcases finiteCuts x p q up uq (small p hp) (small q hq) with bad | ⟨fx,ok⟩
    · exact rup_not_dead (raws _) hr (fun z hz => bad _ (small z hz))
    · have goodH : Safe (board (cut x p q)) h := by
        rcases ok with ok | ok | ⟨ne,up',uq'⟩
        · exact Or.inl ⟨p,hp,ok⟩
        · exact Or.inl ⟨q,hq,ok⟩
        · exact Or.inr ⟨p,hp,q,hq,ne,up',uq'⟩
      apply met (G:=Generic.db Raw [h]) (s:=board (cut x p q)) (l:=l) _ fx left right
      rintro d (hd|hd)
      · exact raws _ d hd
      · have eq : d=h := List.mem_singleton.mp hd
        exact eq.symm ▸ goodH

end PEqualNP.Outside.L_meta_9248.Leaf

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9248.Chart
namespace Generic
variable {V : Type} [DecidableEq V]

abbrev BoardClause (V : Type) := Clause V
def conflict (G : Set (Clause V)) (A : Set (Literal V)) : Prop :=
  ∃ d ∈ G, ∀ l ∈ d, UPForces G A (negLit l)
def db (F : Set (Clause V)) (cs : List (Clause V)) := F ∪ {d | d ∈ cs}

@[simp] theorem inv (l : Literal V) : negLit (negLit l) = l := by
  rcases l with ⟨x,b⟩
  cases b <;> rfl

theorem not_inv (l : Literal V) : negLit l ≠ l := by
  rcases l with ⟨x,b⟩
  cases b <;> simp [negLit]

theorem carry {G H : Set (Clause V)} {A B : Set (Literal V)}
    (sub : G ⊆ H) (initial : ∀ l ∈ A, UPForces H B l)
    {l} (force : UPForces G A l) : UPForces H B l := by
  induction force with
  | hyp h => exact initial _ h
  | unit hd hl _ ih => exact .unit (sub hd) hl ih

theorem substitute {G : Set (Clause V)} {c : Clause V} {B : Set (Literal V)}
    (learn : IsRUP G c) (assumeC : ∀ l ∈ c, UPForces G B (negLit l)) : conflict G B := by
  obtain ⟨d,hd,h⟩ := learn
  refine ⟨d, hd, fun l hl => carry (fun _ hs => hs) ?_ (h l hl)⟩
  rintro _ ⟨m,hm,rfl⟩
  exact assumeC _ hm

theorem splitClause {G : Set (Clause V)} {c : Clause V} {B : Set (Literal V)}
    (extra : ∀ k ∈ c, (∀ m ∈ c, m ≠ k → UPForces G B (negLit m)) → UPForces G B k)
    {l} (force : UPForces (G ∪ {c}) ∅ l) : UPForces G B l := by
  induction force with
  | hyp h => simp at h
  | @unit d k hd hk _ ih =>
    rcases hd with hd | hd
    · exact .unit hd hk ih
    · have e : d = c := hd
      subst d
      exact extra k hk ih

theorem terminalPair {G : Set (Clause V)} {c : Clause V}
    (base : ¬ conflict G ∅) (learn : IsRUP G c) (finish : conflict (G ∪ {c}) ∅) :
    ∃ l ∈ c, IsRUP G {l} ∧ IsRUP G {negLit l} := by
  classical
  have unitExists : ∃ l ∈ c, ∀ m ∈ c, m ≠ l → UPForces G ∅ (negLit m) := by
    by_contra missing
    have pass {z} (h : UPForces (G ∪ {c}) ∅ z) : UPForces G ∅ z :=
      splitClause (fun k hk other => False.elim (missing ⟨k,hk,other⟩)) h
    obtain ⟨d,hd,dead⟩ := finish
    rcases hd with hd | hd
    · exact base ⟨d,hd,fun k hk => pass (dead k hk)⟩
    · have e : d = c := hd
      subst d
      exact base (substitute learn (fun k hk => pass (dead k hk)))
  obtain ⟨l,ml,other⟩ := unitExists
  refine ⟨l,ml,?_,?_⟩
  · have bad : conflict G {negLit l} := by
      apply substitute learn
      intro m hm
      by_cases eq : m = l
      · subst m
        exact .hyp (by simp)
      · exact carry (fun _ h => h) (by simp) (other m hm eq)
    simpa [IsRUP,conflict] using bad
  · suffices bad : conflict G {l} by simpa [IsRUP,conflict] using bad
    by_contra clean
    have notOpp (h : UPForces G {l} (negLit l)) : False := by
      generalize e : negLit l = z at h
      cases h with
      | hyp hz =>
        have eq : _ = l := hz
        exact not_inv l (e.trans eq)
      | @unit d k hd hk rest =>
        apply clean
        refine ⟨d,hd,?_⟩
        intro m hm
        by_cases eq : m = negLit l
        · subst m
          rw [inv]
          exact .hyp (by simp)
        · exact rest m hm (fun hk => eq (hk.trans e.symm))
    have pass {z} (h : UPForces (G ∪ {c}) ∅ z) : UPForces G {l} z := by
      apply splitClause (c:=c) (B:={l}) _ h
      intro k hk other'
      by_cases eq : k = l
      · subst k
        exact .hyp (by simp)
      · exact False.elim (notOpp (other' l ml (Ne.symm eq)))
    obtain ⟨d,hd,dead⟩ := finish
    rcases hd with hd | hd
    · exact clean ⟨d,hd,fun k hk => pass (dead k hk)⟩
    · have e : d = c := hd
      subst d
      exact notOpp (pass (dead l ml))

theorem dbCons (F : Set (Clause V)) (c : Clause V) (cs : List (Clause V)) :
    db F (c :: cs) = db F cs ∪ {c} := by
  ext d
  simp [db,or_comm,or_left_comm,or_assoc]

theorem preceding {F : Set (Clause V)} {cs : List (Clause V)}
    (run : IsRUPRun F cs) (member : (∅ : Clause V) ∈ cs) :
    ∃ ps, IsRUPRun F ps ∧ ps.length < cs.length ∧ conflict (db F ps) ∅ := by
  induction run with
  | nil => simp at member
  | @learn ps c prev learn ih =>
    rcases List.mem_cons.mp member with eq | inTail
    · subst c
      exact ⟨ps,prev,by simp,by simpa [db,conflict,IsRUP] using learn⟩
    · obtain ⟨ts,tv,tl,tc⟩ := ih inTail
      exact ⟨ts,tv,by simp only [List.length_cons]; omega,tc⟩

theorem pairFromRoot {F : Set (Clause V)} (clean : ¬conflict F ∅) {cs : List (Clause V)}
    (run : IsRUPRun F cs) (root : conflict (db F cs) ∅) :
    ∃ ps, IsRUPRun F ps ∧ ps.length < cs.length ∧
      ∃ l : Literal V, IsRUP (db F ps) {l} ∧ IsRUP (db F ps) {negLit l} := by
  induction run with
  | nil => exact False.elim (clean (by simpa [db] using root))
  | @learn ps c prev learn ih =>
    by_cases earlier : conflict (db F ps) ∅
    · obtain ⟨ts,tv,tl,more⟩ := ih earlier
      exact ⟨ts,tv,by simp only [List.length_cons]; omega,more⟩
    · rw [dbCons] at root
      obtain ⟨l,_,a,b⟩ := terminalPair earlier learn root
      exact ⟨ps,prev,by simp,l,a,b⟩

theorem pairPrefix {F : Set (Clause V)} (clean : ¬conflict F ∅) {cs : List (Clause V)}
    (run : IsRUPRun F cs) (member : (∅ : Clause V) ∈ cs) :
    ∃ ps, IsRUPRun F ps ∧ ps.length + 2 ≤ cs.length ∧
      ∃ l : Literal V, IsRUP (db F ps) {l} ∧ IsRUP (db F ps) {negLit l} := by
  obtain ⟨qs,qv,ql,qc⟩ := preceding run member
  obtain ⟨ps,pv,pl,goal⟩ := pairFromRoot clean qv qc
  exact ⟨ps,pv,by omega,goal⟩


end Generic
namespace Restrict
open PEqualNP.ProofComplexity PEqualNP.Search
variable {V : Type} [DecidableEq V]
abbrev C (V : Type) := Clause V
abbrev Val (V : Type) := V → Option Bool
def satisfied (s : Val V) (d : C V) := ∃ l ∈ d, s l.1 = some l.2
def residue (s : Val V) (d : C V) := d.filter fun l => s l.1 = none
def kept (s : Val V) (d : C V) : Option (C V) := restrictClause s d
theorem yes_keep {s : Val V} {d : C V} (h : ¬satisfied s d) :
    kept s d = some (residue s d) := by
  unfold satisfied at h
  simp [kept,restrictClause,residue,h]
theorem no_keep {s : Val V} {d : C V} (h : satisfied s d) : kept s d=none := by
  unfold satisfied at h
  simp [kept,restrictClause,h]
def faithful (s : Val V) (G H : Set (C V)) := ∀ d ∈ G, ¬satisfied s d → residue s d ∈ H
def consistent (s : Val V) (H : Set (C V)) (B : Set (Literal V)) (l : Literal V) :=
  (∀ b, s l.1=some b → l.2=b) ∧ (s l.1=none → UPForces H B l)

theorem transfer_forces {s : Val V} {G H : Set (C V)} {A B : Set (Literal V)}
    (pass : faithful s G H) (prem : ∀ l∈A, consistent s H B l)
    (noConflict : ¬ ∃ d ∈ H, ∀ l∈d, UPForces H B (negLit l))
    {l : Literal V} (der : UPForces G A l) : consistent s H B l := by
  induction der with
  | hyp h => exact prem _ h
  | @unit d l hd hl other ih =>
    by_cases alive : satisfied s d
    · obtain ⟨a,ha,holds⟩ := alive
      by_cases eq : a=l
      · subst a
        constructor
        · intro b e
          exact Option.some.inj (holds.symm.trans e)
        · intro e
          rw [holds] at e
          contradiction
      · have bad := (ih a ha eq).1 a.2 holds
        change (!a.2)=a.2 at bad
        cases a.2 <;> simp_all
    · have mem := pass d hd alive
      constructor
      · intro b eh
        by_contra diff
        apply noConflict
        refine ⟨residue s d,mem,?_⟩
        intro a ha
        obtain ⟨hm,unk⟩ := Finset.mem_filter.mp ha
        have ne : a≠l := by intro e; subst a; rw [eh] at unk; contradiction
        exact (ih a hm ne).2 unk
      · intro un
        apply UPForces.unit mem (Finset.mem_filter.mpr ⟨hl,un⟩)
        intro a ha ne
        obtain ⟨hm,unk⟩ := Finset.mem_filter.mp ha
        exact (ih a hm ne).2 unk

theorem transfer_clause {s : Val V} {G H : Set (C V)} {c : C V}
    (pass : faithful s G H) (openC : ¬satisfied s c) (r : IsRUP G c) :
    IsRUP H (residue s c) := by
  classical
  by_contra no
  let A := negLit '' (↑c : Set (Literal V))
  let B := negLit '' (↑(residue s c) : Set (Literal V))
  have pr : ∀ l∈A, consistent s H B l := by
    rintro _ ⟨a,ha,rfl⟩
    constructor
    · intro b e
      change (!a.2)=b
      have neq : a.2≠b := by intro q; exact openC ⟨a,ha,q.symm ▸ e⟩
      exact (by decide : ∀ x y : Bool, x≠y → (!x)=y) a.2 b neq
    · intro un
      apply UPForces.hyp
      exact ⟨a,Finset.mem_filter.mpr ⟨ha,un⟩,rfl⟩
  obtain ⟨d,hd,die⟩ := r
  have force (a) (ha : a∈d) := transfer_forces pass pr no (die a ha)
  by_cases sat : satisfied s d
  · obtain ⟨a,ha,yes⟩ := sat
    have bad := (force a ha).1 a.2 yes
    change (!a.2)=a.2 at bad
    cases a.2 <;> simp_all
  · apply no
    refine ⟨residue s d,pass d hd sat,?_⟩
    intro a ha
    obtain ⟨hm,un⟩ := Finset.mem_filter.mp ha
    exact (force a hm).2 un

theorem transfer_run {s : Val V} {G H : Set (C V)} (pass : faithful s G H)
    {rs : List (C V)} (run : IsRUPRun G rs) : IsRUPRun H (rs.filterMap (kept s)) := by
  classical
  induction run with
  | nil => exact IsRUPRun.nil
  | @learn rs c earlier curr ih =>
    by_cases sat : satisfied s c
    · simpa [List.filterMap_cons,no_keep sat] using ih
    · rw [List.filterMap_cons,yes_keep sat]
      apply IsRUPRun.learn ih
      apply transfer_clause _ sat curr
      intro d hd free
      rcases hd with raw|old
      · exact Or.inl (pass d raw free)
      · apply Or.inr
        exact List.mem_filterMap.mpr ⟨d,old,yes_keep free⟩

theorem transfer_empty (s : Val V) {rs : List (C V)} (m : (∅ : C V) ∈ rs) :
    (∅ : C V) ∈ rs.filterMap (kept s) := by
  apply List.mem_filterMap.mpr
  exact ⟨∅,m,by simp [kept,restrictClause]⟩


variable {W : Type} [DecidableEq W]
def pushLit (f : V → W) (l : Literal V) : Literal W := (f l.1,l.2)
def push (f : V → W) (c : C V) := c.image (pushLit f)
theorem push_forces {G : Set (C V)} {H : Set (C W)} {A B} (f : V → W)
    (pass : ∀c∈G, push f c∈H) (hyp : ∀ l∈A, pushLit f l∈B) {l}
    (h : UPForces G A l) : UPForces H B (pushLit f l) := by
  induction h with
  | hyp h => exact UPForces.hyp (hyp _ h)
  | @unit d l hd hl oth ih =>
    apply UPForces.unit (pass d hd) (Finset.mem_image_of_mem (pushLit f) hl)
    rintro _ hm ne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
    exact ih a ha (fun eq => ne (congrArg (pushLit f) eq))
theorem push_clause {G : Set (C V)} {H : Set (C W)} (f : V → W)
    (pass : ∀c∈G, push f c∈H) {c} (h : IsRUP G c) : IsRUP H (push f c) := by
  obtain ⟨d,hd,die⟩ := h
  refine ⟨push f d,pass d hd,?_⟩
  intro a ha
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
  apply push_forces f pass _ (die l hl)
  rintro _ ⟨v,hv,rfl⟩
  exact ⟨pushLit f v,Finset.mem_image_of_mem (pushLit f) hv,rfl⟩
theorem push_run {G : Set (C V)} {H : Set (C W)} (f : V → W)
    (pass : ∀c∈G, push f c∈H) {rs} (run : IsRUPRun G rs) :
    IsRUPRun H (rs.map (push f)) := by
  induction run with
  | nil => exact IsRUPRun.nil
  | @learn rs c good step ih =>
    apply IsRUPRun.learn ih (push_clause f _ step)
    intro d hd
    rcases hd with a|b
    · exact Or.inl (pass d a)
    · exact Or.inr (List.mem_map.mpr ⟨d,b,rfl⟩)

def Lower (F : Set (C V)) (n : Nat) : Prop :=
  ∀ rs : List (C V), IsRUPRun F rs → (∅ : C V) ∈ rs → n ≤ rs.length

def faithfulMap (F : Set (C V)) (H : Set (C W)) (s : Val V) (f : V → W) : Prop :=
  ∀ d ∈ F, ¬satisfied s d → push f (residue s d) ∈ H

theorem mapped_run {F : Set (C V)} {H : Set (C W)}
    (s : Val V) (f : V → W) (h : faithfulMap F H s f)
    {rs : List (C V)} (run : IsRUPRun F rs) :
    IsRUPRun H ((rs.filterMap (kept s)).map (push f)) := by
  let F' : Set (C V) := {e | ∃ d∈F, ¬satisfied s d ∧ residue s d=e}
  have raw : faithful s F F' := fun d hd free => ⟨d,hd,free,rfl⟩
  apply push_run f _ (transfer_run raw run)
  rintro _ ⟨d,hd,free,rfl⟩
  exact h d hd free

theorem one_more {F : Set (C V)} {n : Nat}
    (consistent : ¬ Generic.conflict F ∅)
    (answers : ∀ v : V, ∃ (s : Val V) (f : V → W) (H : Set (C W)),
      s v≠none ∧ faithfulMap F H s f ∧ Lower H n) : Lower F (n+1) := by
  intro rs run empty
  obtain ⟨ps,rp,len,l,plus,minus⟩ := Generic.pairPrefix consistent run empty
  obtain ⟨s,f,H,set,pass,floor⟩ := answers l.1
  obtain ⟨v,hv⟩ := Option.ne_none_iff_exists'.mp set
  have existsBad : ∃ k : Literal V, s k.1=some (!k.2) ∧ IsRUP (Generic.db F ps) {k} := by
    by_cases e : v=l.2
    · refine ⟨negLit l,?_,minus⟩
      simpa [negLit,e] using hv
    · refine ⟨l,?_,plus⟩
      have ne : v = !l.2 := by cases v <;> cases h : l.2 <;> simp_all
      simpa [ne] using hv
  obtain ⟨k,hk,learn⟩ := existsBad
  have newRun : IsRUPRun F ({k} :: ps) := .learn rp learn
  have fixed : kept s ({k} : C V) = some ∅ := by
    rcases k with ⟨x,b⟩
    cases b <;> simp_all [kept,restrictClause]
  have smaller := mapped_run s f pass newRun
  rw [List.filterMap_cons,fixed] at smaller
  have smallRun : IsRUPRun H (∅ :: (ps.filterMap (kept s)).map (push f)) := by
    simpa [push] using smaller
  have numeric := floor _ smallRun List.mem_cons_self
  have bound := List.length_filterMap_le (f:=kept s) (l:=ps)
  simp only [List.length_cons,List.length_map] at numeric
  omega


abbrev X := Fin 5 × Fin 4
abbrev Ix := Fin 17
def states : Array (Nat × Nat) := #[(3171,2),(101542,2),(103655,3),(105703,4),(236775,5),(3249484,2),(3256719,3),(3317069,3),(3324399,4),(3387823,4),(3390959,5),(3586543,5),(3653103,6),(7585263,6),(7716335,6),(7847407,7),(16236015,8)]
def e0 : Array (Nat × Nat × Nat × Nat) := #[(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672),(0,0,18056,1672)]
def e1 : Array (Nat × Nat × Nat × Nat) := #[(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672),(1,0,18056,1672)]
def e2 : Array (Nat × Nat × Nat × Nat) := #[(1,0,16915,1602),(0,65536,14465,1112),(0,4096,13569,1224),(2,0,18056,1672),(1,0,16922,1602),(0,65536,14472,1112),(0,4096,13576,1224),(2,0,18056,1672),(0,4096,13576,1224),(2,0,18056,1672),(0,4096,13576,1224),(2,0,18056,1672),(0,65536,14472,1112),(0,65536,14472,1112),(2,0,18056,1672),(2,0,18056,1672),(2,0,18056,1672),(2,0,18056,1672),(2,0,18056,1672),(2,0,18056,1672)]
def e3 : Array (Nat × Nat × Nat × Nat) := #[(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672),(3,0,18056,1672)]
def e4 : Array (Nat × Nat × Nat × Nat) := #[(3,0,17475,1602),(3,0,17475,1616),(3,0,17475,1672),(4,0,18056,1672),(3,0,17496,1602),(3,0,17496,1616),(3,0,17496,1672),(4,0,18056,1672),(3,0,17608,1602),(3,0,17608,1616),(3,0,17608,1672),(4,0,18056,1672),(3,0,18056,1602),(3,0,18056,1616),(3,0,18056,1672),(4,0,18056,1672),(4,0,18056,1672),(4,0,18056,1672),(4,0,18056,1672),(4,0,18056,1672)]
def e5 : Array (Nat × Nat × Nat × Nat) := #[(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672),(5,0,18056,1672)]
def e6 : Array (Nat × Nat × Nat × Nat) := #[(0,2129920,14472,531),(0,1114112,14472,531),(0,8320,8928,1224),(0,4352,8928,1224),(6,0,18056,1672),(6,0,18056,1672),(0,4352,8928,1224),(0,8320,8928,1224),(6,0,18056,1672),(6,0,18056,1672),(0,8320,8928,1224),(0,4352,8928,1224),(0,1114112,14472,531),(0,2129920,14472,531),(6,0,18056,1672),(6,0,18056,1672),(0,2129920,14472,531),(0,1114112,14472,531),(6,0,18056,1672),(6,0,18056,1672)]
def e7 : Array (Nat × Nat × Nat × Nat) := #[(5,0,10433,1616),(7,0,18056,1672),(1,131072,14465,1224),(0,2097408,13345,1112),(7,0,18056,1672),(0,2097408,13345,1112),(7,0,18056,1672),(0,2097408,13345,1112),(1,256,5666,1616),(0,2097408,13408,1112),(1,131072,14465,1224),(7,0,18056,1672),(1,131072,14465,1224),(7,0,18056,1672),(1,131072,14465,1224),(7,0,18056,1672),(0,2097408,13408,1112),(0,2097408,13408,1112),(7,0,18056,1672),(7,0,18056,1672)]
def e8 : Array (Nat × Nat × Nat × Nat) := #[(7,0,6163,1049),(2,2097152,18049,1049),(2,131072,14465,1217),(2,8192,13569,1672),(7,0,6170,1049),(2,2097152,18056,1049),(2,131072,14472,1217),(2,8192,13576,1672),(8,0,18056,1672),(2,8192,9992,1616),(2,8192,13576,1672),(2,8192,13576,1672),(2,131072,14472,1217),(8,0,18056,1672),(2,131072,14472,1217),(8,0,18056,1672),(2,2097152,18056,1049),(2,2097152,18056,1049),(8,0,18056,1672),(8,0,18056,1672)]
def e9 : Array (Nat × Nat × Nat × Nat) := #[(7,0,6338,1035),(2,2097152,17608,538),(7,0,12386,720),(2,8192,13072,1672),(6,0,8984,538),(9,0,18056,1672),(7,0,12386,720),(2,8192,8984,1616),(9,0,18056,1672),(9,0,18056,1672),(2,8192,13072,1672),(2,8192,13072,1672),(7,0,6338,1035),(2,2097152,18056,1049),(6,0,18056,1672),(9,0,18056,1672),(2,2097152,18056,1049),(2,2097152,18056,1049),(9,0,18056,1672),(9,0,18056,1672)]
def e10 : Array (Nat × Nat × Nat × Nat) := #[(3,8,13380,1665),(3,8,13380,1672),(3,8,13380,1672),(3,256,13345,1672),(3,256,13408,1665),(3,256,13408,1672),(3,256,13408,1672),(3,8,13324,1672),(3,8192,13576,1665),(3,8192,13576,1672),(3,8192,13576,1672),(3,8,13380,1672),(3,131072,14472,1217),(3,131072,14472,1224),(3,131072,14472,1224),(10,0,18056,1672),(3,2097152,18056,1112),(3,1048576,18056,1091),(10,0,18056,1672),(10,0,18056,1672)]
def e11 : Array (Nat × Nat × Nat × Nat) := #[(3,1048576,18049,531),(3,2097152,17601,538),(9,0,17027,1224),(9,0,17027,1672),(3,1048576,18056,531),(3,2097152,17608,538),(9,0,17048,1224),(9,0,17048,1672),(11,0,18056,1672),(3,2097152,17608,538),(8,0,17608,1217),(8,0,17608,1665),(3,1048576,18056,531),(11,0,18056,1672),(8,0,18056,1224),(8,0,18056,1672),(3,2097152,17608,538),(3,1048576,18056,531),(11,0,18056,1672),(11,0,18056,1672)]
def e12 : Array (Nat × Nat × Nat × Nat) := #[(4,1048576,17475,1091),(4,2097152,17475,1112),(10,0,17475,1224),(10,0,17475,1672),(4,1048576,17496,1091),(4,2097152,17496,1112),(10,0,17496,1224),(10,0,17496,1672),(4,1048576,17608,1091),(4,2097152,17608,1112),(10,0,17608,1224),(10,0,17608,1672),(4,1048576,18056,1091),(4,2097152,18056,1112),(10,0,18056,1224),(10,0,18056,1672),(4,2097152,18056,1112),(4,1048576,18056,1091),(12,0,18056,1672),(12,0,18056,1672)]
def e13 : Array (Nat × Nat × Nat × Nat) := #[(4,8,13380,1602),(4,8,13380,1616),(4,8,13380,1672),(4,256,13345,1672),(4,256,13408,1602),(4,256,13408,1616),(4,256,13408,1672),(4,8,13324,1672),(4,8192,13576,1602),(4,8192,13576,1616),(4,8192,13576,1672),(4,8,13380,1672),(10,0,14472,1602),(10,0,14472,1616),(10,0,14472,1672),(13,0,18056,1672),(10,0,18056,1602),(10,0,18056,1616),(10,0,18056,1672),(13,0,18056,1672)]
def e14 : Array (Nat × Nat × Nat × Nat) := #[(11,0,13380,531),(11,0,13380,538),(4,4194304,17986,1224),(4,262144,14402,1672),(11,0,13408,531),(11,0,13408,538),(4,4194304,18000,1224),(4,262144,14416,1672),(11,0,13576,531),(11,0,13576,538),(4,4194304,18056,1224),(4,262144,14472,1672),(4,262144,14472,1665),(4,262144,14472,1672),(14,0,18056,1672),(4,262144,14472,1672),(4,4194304,18056,1217),(4,4194304,18056,1224),(4,4194304,18056,1224),(14,0,18056,1672)]
def e15 : Array (Nat × Nat × Nat × Nat) := #[(14,0,17475,1602),(14,0,17475,1616),(14,0,17475,1672),(13,0,17475,1672),(14,0,17496,1602),(14,0,17496,1616),(14,0,17496,1672),(13,0,17496,1672),(14,0,17608,1602),(14,0,17608,1616),(14,0,17608,1672),(13,0,17608,1672),(14,0,18056,1602),(14,0,18056,1616),(14,0,18056,1672),(13,0,18056,1672),(12,0,18056,1602),(12,0,18056,1616),(12,0,18056,1672),(15,0,18056,1672)]
def e16 : Array (Nat × Nat × Nat × Nat) := #[(15,0,13380,1091),(15,0,13380,1112),(15,0,13380,1224),(15,0,13380,1672),(15,0,13408,1091),(15,0,13408,1112),(15,0,13408,1224),(15,0,13408,1672),(15,0,13576,1091),(15,0,13576,1112),(15,0,13576,1224),(15,0,13576,1672),(15,0,14472,1091),(15,0,14472,1112),(15,0,14472,1224),(15,0,14472,1672),(15,0,18056,1091),(15,0,18056,1112),(15,0,18056,1224),(15,0,18056,1672)]
def edges := #[e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16]
def root : Ix := 16
def leaf : Ix := 3

def graph (i : Ix) := (states[i.val]!).1
def depth (i : Ix) := (states[i.val]!).2
def cell (x : X) := 5*x.1.val+x.2.val
def on (g : Nat) (v : X) : Bool := g.testBit (cell v)
def active (g : Nat) (r : Fin 5) : Bool := ((g / 2^(5*r.val))%32) != 0
def row (g : Nat) (r : Fin 5) : Clause X :=
  (Finset.univ.filter (fun h : Fin 4 => on g (r,h))).image (fun h : Fin 4 => ((r,h),true))
def col (a b : Fin 5) (j : Fin 4) : Clause X := {((a,j),false),((b,j),false)}
def Raw (g : Nat) : Set (Clause X) := {d |
 (∃ r : Fin 5, active g r ∧ d=row g r) ∨
 (∃ (a b : Fin 5) (j : Fin 4), a≠b ∧ on g (a,j) ∧ on g (b,j) ∧ d=col a b j)}
def entry (i : Ix) (v : X) := (edges[i.val]!)[4*v.1.val+v.2.val]!
def dest (i : Ix) (v : X) : Ix :=
 ⟨(entry i v).1 % _,Nat.mod_lt _ (by decide)⟩
def readIndex {n : Nat} [NeZero n] (s : Nat) (x : Fin n) : Fin n :=
 ⟨((s / 2^(3*x.val))%8)%n,Nat.mod_lt _ (NeZero.pos n)⟩
def rf (i : Ix) (v : X) : Fin 5 → Fin 5 := readIndex (entry i v).2.2.1
def cf (i : Ix) (v : X) : Fin 4 → Fin 4 := readIndex (entry i v).2.2.2
def rename (i : Ix) (v y : X) : X := (rf i v y.1,cf i v y.2)
def assign (i : Ix) (v y : X) : Option Bool :=
 if on (entry i v).2.1 y then some true
 else if on (graph (dest i v)) (rename i v y) then none else some false
def sat (s : Val X) (c : Clause X) : Bool := decide (∃ (r : Fin 5) (h : Fin 4) (b : Bool), ((r,h),b)∈c ∧ s (r,h)=some b)
theorem sat_iff (s : Val X) (c : Clause X) : sat s c = true ↔ satisfied s c := by
 simp only [sat,decide_eq_true_eq]
 constructor
 · rintro ⟨r,h,b,m,e⟩
   exact ⟨((r,h),b),m,e⟩
 · rintro ⟨⟨⟨r,h⟩,b⟩,m,e⟩
   exact ⟨r,h,b,m,e⟩
def guardedRow (i : Ix) (v : X) (r : Fin 5) : Prop :=
 let g:=graph i; let h:=graph (dest i v); let s:=assign i v; let d:=row g r
 active g r = true → sat s d = true ∨
   (active h (rf i v r)=true ∧ push (rename i v) (residue s d)=row h (rf i v r))
def guardedPair (i : Ix) (v : X) (a b : Fin 5) (j : Fin 4) : Prop :=
 let g:=graph i; let h:=graph (dest i v); let s:=assign i v; let d:=col a b j
 a≠b → on g (a,j)=true → on g (b,j)=true → sat s d=true ∨
  (rf i v a≠rf i v b ∧ on h (rf i v a, cf i v j)=true ∧ on h (rf i v b,cf i v j)=true ∧
   push (rename i v) (residue s d)=col (rf i v a) (rf i v b) (cf i v j))
def Check (i : Ix) (v : X) : Prop :=
 depth i≤2 ∨ i=leaf ∨
 (assign i v v≠none ∧ depth i≤depth (dest i v)+1 ∧
  (∀ r, guardedRow i v r) ∧ (∀ a b j, guardedPair i v a b j))
set_option synthInstance.maxSize 4096
set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance (i : Ix) (v : X) (r : Fin 5) : Decidable (guardedRow i v r) := by unfold guardedRow; infer_instance
local instance (i : Ix) (v : X) (a b : Fin 5) (j : Fin 4) : Decidable (guardedPair i v a b j) := by unfold guardedPair; infer_instance
local instance (i : Ix) (v : X) : Decidable (Check i v) := by unfold Check; infer_instance

abbrev Small := PEqualNP.Outside.L_meta_9248.Leaf.V
abbrev smallRaw := PEqualNP.Outside.L_meta_9248.Leaf.Raw
def toSmall (v : X) : Small := ⟨(3*v.1.val+v.2.val)%12,Nat.mod_lt _ (by decide)⟩
def leafFix (v : X) : Option Bool := if on (graph leaf) v then none else some false
theorem smallRows : ∀ r : Fin 5, active (graph leaf) r=true →
  push toSmall (residue leafFix (row (graph leaf) r)) ∈ PEqualNP.Outside.L_meta_9248.Leaf.axs := by decide +kernel
theorem smallCols : ∀ (a b : Fin 5) (j : Fin 4), a≠b → on (graph leaf) (a,j)=true →
  on (graph leaf) (b,j)=true → push toSmall (residue leafFix (col a b j)) ∈ PEqualNP.Outside.L_meta_9248.Leaf.axs := by decide +kernel
theorem leafMap : faithfulMap (Raw (graph leaf)) smallRaw leafFix toSmall := by
  rintro d (⟨r,act,rfl⟩|⟨a,b,j,ne,oa,ob,rfl⟩) alive
  · exact smallRows r act
  · exact smallCols a b j ne oa ob
theorem leaf_transfer (small : Lower smallRaw 4) : Lower (Raw (graph leaf)) 4 := by
  intro cs run empty
  have legal := mapped_run leafFix toSmall leafMap run
  have mem := transfer_empty leafFix empty
  have translated : (∅ : Clause Small) ∈ (cs.filterMap (kept leafFix)).map (push toSmall) :=
    List.mem_map.mpr ⟨∅,mem,by simp [push]⟩
  have bound := small _ legal translated
  simp only [List.length_map] at bound
  exact bound.trans (List.length_filterMap_le (f:=kept leafFix) (l:=cs))
theorem chart_map {i : Ix} {v : X} (rq : ∀ r, guardedRow i v r)
    (cq : ∀ a b j, guardedPair i v a b j) :
    faithfulMap (Raw (graph i)) (Raw (graph (dest i v))) (assign i v) (rename i v) := by
  rintro d (⟨r,active,rfl⟩|⟨a,b,j,ne,oa,ob,rfl⟩) alive
  · rcases rq r active with sat | ⟨ac,eq⟩
    · exact (alive ((sat_iff _ _).1 sat)).elim
    · exact Or.inl ⟨_,ac,eq⟩
  · rcases cq a b j ne oa ob with sat | ⟨neq,ha,hb,eq⟩
    · exact (alive ((sat_iff _ _).1 sat)).elim
    · exact Or.inr ⟨_,_,_,neq,ha,hb,eq⟩

theorem wideRows : ∀ (i : Ix) (r : Fin 5), active (graph i) r=true → 1 < (row (graph i) r).card := by decide +kernel
theorem wideCols : ∀ (a b : Fin 5) (j : Fin 4), a≠b → 1 < (col a b j).card := by decide +kernel

theorem cleanAt (i : Ix) : ¬Generic.conflict (Raw (graph i)) ∅ := by
  have wide : ∀ d ∈ Raw (graph i), 1 < d.card := by
    rintro d (⟨r,active,rfl⟩|⟨a,b,j,ne,_,_,rfl⟩)
    · exact wideRows i r active
    · exact wideCols a b j ne
  have impossible {l : Literal X} (f : UPForces (Raw (graph i)) ∅ l) : False := by
    induction f with
    | hyp h => simp at h
    | @unit d k hd hk rest ih =>
      obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (wide d hd)
      by_cases e : a=k
      · subst k
        exact ih b hb (Ne.symm ne)
      · exact ih a ha e
  rintro ⟨d,hd,dead⟩
  obtain ⟨k,hk,_,_,_⟩ := Finset.one_lt_card.mp (wide d hd)
  exact impossible (dead k hk)

theorem smallFloor (i : Ix) : Lower (Raw (graph i)) 2 := by
  intro rs run out
  obtain ⟨ps,_,len,_⟩ := Generic.pairPrefix (cleanAt i) run out
  omega

theorem eval_chart (accepted : ∀ (i : Ix) (v : X), Check i v)
    (leafLower : Lower (Raw (graph leaf)) 4)
    (k : Nat) (i : Ix) (le : k≤depth i) : Lower (Raw (graph i)) k := by
  induction k generalizing i with
  | zero => intro xs _ _; omega
  | succ k ih =>
    by_cases tiny : k+1≤2
    · intro rs run m
      exact tiny.trans (smallFloor i rs run m)
    by_cases hit : i=leaf
    · subst i
      have leafSize : depth leaf=4 := by decide
      intro rs run m
      have lim : k+1≤4 := by simpa only [leafSize] using le
      exact lim.trans (leafLower rs run m)
    apply one_more (W:=X) (cleanAt i)
    intro v
    rcases accepted i v with low | eq | ⟨fixed,down,row,pair⟩
    · omega
    · exact (hit eq).elim
    · refine ⟨assign i v,rename i v,Raw (graph (dest i v)),fixed,chart_map row pair,?_⟩
      exact ih (dest i v) (by omega)

theorem fullrow (r : Fin 5) : row (graph root) r =
    Finset.univ.image (fun h : Fin 4 => (((r,h),true) : Literal X)) := by
  have all : ∀ s : Fin 5, row (graph root) s = Finset.univ.image
    (fun h : Fin 4 => (((s,h),true) : Literal X)) := by decide +kernel
  exact all r

theorem rootFormula : Raw (graph root) = PHP 5 4 := by
  ext d
  constructor
  · rintro (⟨r,h,rfl⟩|⟨a,b,j,ne,oa,ob,rfl⟩)
    · exact Or.inl ⟨r,fullrow r⟩
    · exact Or.inr ⟨a,b,j,ne,rfl⟩
  · rintro (⟨r,rfl⟩|⟨a,b,j,ne,rfl⟩)
    · have activeAll : ∀ z, active (graph root) z = true := by decide
      exact Or.inl ⟨r,activeAll r,(fullrow r).symm⟩
    · have edgesAll : ∀ v, on (graph root) v = true := by decide
      exact Or.inr ⟨a,b,j,ne,edgesAll _,edgesAll _,rfl⟩

theorem chart_eight (accepted : ∀ (i : Ix) (v : X), Check i v)
    (leafLower : Lower (Raw (graph leaf)) 4) : Lower (PHP 5 4) 8 := by
  rw [← rootFormula]
  exact eval_chart accepted leafLower 8 root (by decide)
theorem rowCheck0 : ∀ v : X, Check (0:Ix) v := by decide +kernel
theorem rowCheck1 : ∀ v : X, Check (1:Ix) v := by decide +kernel
theorem rowCheck2 : ∀ v : X, Check (2:Ix) v := by decide +kernel
theorem rowCheck3 : ∀ v : X, Check (3:Ix) v := by decide +kernel
theorem rowCheck4 : ∀ v : X, Check (4:Ix) v := by decide +kernel
theorem rowCheck5 : ∀ v : X, Check (5:Ix) v := by decide +kernel
theorem rowCheck6 : ∀ v : X, Check (6:Ix) v := by decide +kernel
theorem rowCheck7 : ∀ v : X, Check (7:Ix) v := by decide +kernel
theorem rowCheck8 : ∀ v : X, Check (8:Ix) v := by decide +kernel
theorem rowCheck9 : ∀ v : X, Check (9:Ix) v := by decide +kernel
theorem rowCheck10 : ∀ v : X, Check (10:Ix) v := by decide +kernel
theorem rowCheck11 : ∀ v : X, Check (11:Ix) v := by decide +kernel
theorem rowCheck12 : ∀ v : X, Check (12:Ix) v := by decide +kernel
theorem rowCheck13 : ∀ v : X, Check (13:Ix) v := by decide +kernel
theorem rowCheck14 : ∀ v : X, Check (14:Ix) v := by decide +kernel
theorem rowCheck15 : ∀ v : X, Check (15:Ix) v := by decide +kernel
theorem rowCheck16 : ∀ v : X, Check (16:Ix) v := by decide +kernel
theorem approved (i : Ix) (v : X) : Check i v := by
  fin_cases i
  · exact rowCheck0 v
  · exact rowCheck1 v
  · exact rowCheck2 v
  · exact rowCheck3 v
  · exact rowCheck4 v
  · exact rowCheck5 v
  · exact rowCheck6 v
  · exact rowCheck7 v
  · exact rowCheck8 v
  · exact rowCheck9 v
  · exact rowCheck10 v
  · exact rowCheck11 v
  · exact rowCheck12 v
  · exact rowCheck13 v
  · exact rowCheck14 v
  · exact rowCheck15 v
  · exact rowCheck16 v

theorem lowerEight : Lower (PHP 5 4) 8 :=
 chart_eight approved (leaf_transfer PEqualNP.Outside.L_meta_9248.Leaf.hard)
end Restrict
end PEqualNP.Outside.L_meta_9248.Chart

namespace PEqualNP.Outside.L_meta_9471.SwitchInventory
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem firstRaw : ∀ u, clauseImage 0 0 u = raw 5 4 := by decide +kernel

end PEqualNP.Outside.L_meta_9471.SwitchInventory

namespace PEqualNP.Outside.L_meta_9471.Switched
open PEqualNP.ProofComplexity PEqualNP.Search

def minimumEight {xs : List Dst.C} (r : IsRUPRun (PHP 5 4) xs)
    (last : (∅ : Dst.C)∈xs) : 8≤xs.length :=
  PEqualNP.Outside.L_meta_9248.Chart.Restrict.lowerEight _ r last

noncomputable def budget (p : Fin 6) (h : Fin 5) (u : SmallRaw) (xs : List Src.C) : Nat :=
  (PEqualNP.Outside.L_meta_9471.Subsumed.thin (PHP 5 4)
    (xs.filterMap (signed (PEqualNP.Outside.L_meta_9471.SwitchInventory.switch p h u)).image)).length

theorem incurred (p : Fin 6) (h : Fin 5) (u : SmallRaw)
    (table : PEqualNP.Outside.L_meta_9471.SwitchInventory.clauseImage p h u ⊆
      PEqualNP.Outside.L_meta_9471.SwitchInventory.raw 5 4)
    {xs : List Src.C} (r : IsRUPRun (PHP 6 5) xs) (last : (∅ : Src.C)∈xs) :
    8 ≤ budget p h u xs := by
  obtain ⟨prog,contains⟩ := physicalSwitch p h u table xs r last
  exact minimumEight (PEqualNP.Outside.L_meta_9471.Subsumed.runThin _ prog)
    (PEqualNP.Outside.L_meta_9471.Subsumed.emptyThin _ _ contains)

theorem firstTwenty {xs : List Src.C} (r : IsRUPRun (PHP 6 5) xs) (last : (∅ : Src.C)∈xs)
    (u : SmallRaw) : 8 ≤ budget 0 0 u xs := by
  apply incurred 0 0 u _ r last
  rw [PEqualNP.Outside.L_meta_9471.SwitchInventory.firstRaw]
  exact fun _ h => h

end PEqualNP.Outside.L_meta_9471.Switched
