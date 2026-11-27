import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9248.Waves

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
def BaseSafe (s : Val) := ∀ c ∈ PHP 5 4, Safe s c

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


def Stable (G : Set C) (s : Val) := ∀ d∈G, Safe s d
def Wave (G : Set C) : Set C := G ∪ {c | IsRUP G c}
def Both (G : Set C) (s : Val) :=
  ∀ v, s v=none → ∀ b, ∃ t, Ext s t ∧ t v=some b ∧ Stable G t

theorem safe_of_branches {G : Set C} {s : Val}
    (raw : Stable G s) (split : Both G s) : Stable (Wave G) s := by
  intro c mem
  rcases mem with old | learnt
  · exact raw c old
  · by_contra bad
    obtain ⟨l,hl,unk,rest⟩ := single_of_not_safe bad (rup_not_dead raw learnt)
    obtain ⟨t,ex,neg,stable⟩ := split l.1 unk (!l.2)
    apply rup_not_dead stable learnt
    intro z hz
    by_cases eq : z=l
    · subst z
      exact neg
    · exact ex _ _ (rest z hz eq)

noncomputable section
open Classical
def block (s : Val) : C := Finset.univ.filter (fun l => Holds s (negLit l))

theorem blockMem {s : Val} {l : L} : l∈block s ↔ Holds s (negLit l) := by
  simp [block]

theorem extendWitness {s : Val} {v : V} {b : Bool} (blank : s v=none) :
    let c := insert (v,!b) (block s)
    Proper c ∧ Single s c ∧ ∀ t, Dead t c → Ext s t ∧ t v=some b := by
  dsimp only
  constructor
  · intro l hl hn
    rw [Finset.mem_insert,blockMem] at hl hn
    rcases hl with eq|atOld <;> rcases hn with eq'|atOld'
    · subst l
      cases b <;> simp [negLit] at eq'
    · subst l
      rw [negneg] at atOld'
      simp [Holds,blank] at atOld'
    · have key := congrArg Prod.fst eq'
      change l.1=v at key
      simp [Holds,negLit,key,blank] at atOld
    · rw [negneg] at atOld'
      exact clash_holds atOld' atOld
  constructor
  · refine ⟨(v,!b),Finset.mem_insert_self _ _,blank,?_⟩
    intro z hz ne
    exact blockMem.mp ((Finset.mem_insert.mp hz).resolve_left ne)
  · intro t dt
    constructor
    · intro x u sx
      have member : (x,!u)∈block s := by
        rw [blockMem]
        simpa [Holds,negLit] using sx
      have th := dt _ (Finset.mem_insert_of_mem member)
      simpa [Holds,negLit] using th
    · have th := dt _ (Finset.mem_insert_self _ _)
      simpa [Holds,negLit] using th

theorem noSingle {s : Val} {c : C} (hc : Safe s c) (u : Single s c) : False := by
  obtain ⟨l,hl,un,rest⟩ := u
  rcases hc with ⟨z,hz,yes⟩ | ⟨a,ha,b,hb,ne,ua,ub⟩
  · by_cases e : z=l
    · subst z
      simp [Holds,un] at yes
    · exact clash_holds yes (rest _ hz e)
  · by_cases e : a=l
    · have q := rest b hb (fun eq => ne (e.trans eq.symm))
      simp [Holds,negLit,ub] at q
    · have q := rest a ha e
      simp [Holds,negLit,ua] at q

theorem stableWave (G : Set C) (s : Val) :
    Stable (Wave G) s ↔ Stable G s ∧ Both G s := by
  refine ⟨fun hs => ⟨fun c hc => hs c (Or.inl hc),?_⟩,fun h => safe_of_branches h.1 h.2⟩
  intro v hv b
  let c := insert (v,!b) (block s)
  obtain ⟨well,unit,read⟩ := extendWitness (b:=b) hv
  have unusable : ¬ IsRUP G c := fun good => noSingle (hs c (Or.inr good)) unit
  obtain ⟨t,ht,dead⟩ := capture well unusable
  exact ⟨t,(read t dead).1,(read t dead).2,ht⟩

end
end PEqualNP.Outside.L_meta_9248.Waves
