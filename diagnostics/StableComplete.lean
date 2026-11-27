import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9246.Stable

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
      by_cases e : u=p
      · exact e ▸ hn
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

def Ordered (s : Val) : List C → Prop
  | [] => True
  | c::cs => Ordered s cs ∧ ((∀ d∈cs, Safe s d) → ¬Dead s c)

theorem simulate {G : Set C} {cs} (h : IsRUPRun G cs) (s : Val)
    (base : ∀ c∈G, Safe s c) : Ordered s cs := by
  induction h with
  | nil => trivial
  | learn _ learn ih =>
    refine ⟨ih,fun old => rup_not_dead ?_ learn⟩
    rintro d (hd|hd)
    · exact base d hd
    · exact old d hd

theorem reconstruct (G : Set C) (cs : List C) (proper : ∀ c∈cs, Proper c)
    (test : ∀ s : Val,(∀ d∈G, Safe s d) → Ordered s cs) : IsRUPRun G cs := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    refine .learn (ih (fun d hd => proper d (List.mem_cons_of_mem _ hd))
      (fun s base => (test s base).1)) ?_
    by_contra bad
    obtain ⟨s,all,dead⟩ := capture (proper c List.mem_cons_self) bad
    exact (test s (fun d hd => all d (Or.inl hd))).2 (fun d hd => all d (Or.inr hd)) dead

theorem taut_safe (s : Val) (c : C) (nt : ¬ Proper c) : Safe s c := by
  classical
  unfold Proper at nt
  push Not at nt
  obtain ⟨l,hl,hn⟩ := nt
  cases val : s l.1 with
  | none =>
    refine Or.inr ⟨l,hl,negLit l,hn,?_,val,val⟩
    intro e
    have off := congrArg Prod.snd e
    cases b : l.2 <;> simp [negLit,b] at off
  | some b =>
    by_cases yes : b=l.2
    · exact Or.inl ⟨l,hl,by simp [Holds,val,yes]⟩
    · refine Or.inl ⟨negLit l,hn,?_⟩
      cases b <;> cases h : l.2 <;> simp_all [Holds,negLit]

noncomputable section
open Classical
def scrub : List C → List C
  | [] => []
  | c::cs => if Proper c then c::scrub cs else scrub cs

theorem scrubbed (cs : List C) :
    (∀ c, c∈scrub cs ↔ c∈cs ∧ Proper c) ∧ (scrub cs).length≤cs.length := by
  induction cs with
  | nil => simp [scrub]
  | cons c cs ih =>
    by_cases q : Proper c
    · constructor
      · intro d
        simp only [scrub,if_pos q,List.mem_cons,ih.1]
        aesop
      · simpa [scrub,q] using ih.2
    · constructor
      · intro d
        simp only [scrub,if_neg q,ih.1,List.mem_cons]
        aesop
      · simp only [scrub,if_neg q,List.length_cons]
        exact ih.2.trans (Nat.le_succ _)

theorem removeTaut (s : Val) (cs : List C) (h : Ordered s cs) : Ordered s (scrub cs) := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    by_cases q : Proper c
    · simp only [scrub,if_pos q,Ordered]
      refine ⟨ih h.1,fun good => h.2 ?_⟩
      intro d hd
      by_cases p : Proper d
      · exact good d (((scrubbed cs).1 d).2 ⟨hd,p⟩)
      · exact taut_safe s d p
    · simpa only [scrub,if_neg q] using ih h.1

theorem exact12 :
    (∃ ρ : List C, IsRUPRun (PHP 5 4) ρ ∧ (∅ : C)∈ρ ∧ ρ.length≤12) ↔
    ∃ ρ : List C, (∅ : C)∈ρ ∧ ρ.length≤12 ∧ ∀ s : Val, BaseSafe s → Ordered s ρ := by
  constructor
  · rintro ⟨ρ,run,empty,len⟩
    exact ⟨ρ,empty,len,fun s hs => simulate run s hs⟩
  · rintro ⟨ρ,empty,len,tests⟩
    have empProper : Proper (∅ : C) := by simp [Proper]
    exact ⟨scrub ρ,reconstruct _ _ (fun d hd => (((scrubbed ρ).1 d).1 hd).2)
      (fun s base => removeTaut s ρ (tests s base)),
      ((scrubbed ρ).1 ∅).2 ⟨empty,empProper⟩,(scrubbed ρ).2.trans len⟩

end
end PEqualNP.Outside.L_meta_9246.Stable
