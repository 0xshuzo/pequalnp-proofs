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

namespace PEqualNP.Outside.L_meta_9246.Stable
open PEqualNP.ProofComplexity PEqualNP.Search

def RowRule (s : Val) : Prop := ∀ i : Fin 5, (∃ j : Fin 4, s (i,j)=some true) ∨
  ∃ j k : Fin 4, j≠k ∧ s (i,j)=none ∧ s (i,k)=none
def ColumnRule (s : Val) : Prop := ∀ (i k : Fin 5) (j : Fin 4), i≠k →
  s (i,j)=some true → s (k,j)=some false

theorem rowCriterion (s : Val) (i : Fin 5) :
    Safe s (Finset.univ.image (fun j : Fin 4 => ((i,j),true))) ↔
    (∃ j : Fin 4, s (i,j)=some true) ∨
    ∃ j k : Fin 4, j≠k ∧ s (i,j)=none ∧ s (i,k)=none := by
  constructor
  · rintro (⟨z,mem,yes⟩|⟨z,mz,w,mw,ne,az,aw⟩)
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp mem
      exact Or.inl ⟨j,yes⟩
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp mz
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp mw
      exact Or.inr ⟨j,k,fun e => ne (e ▸ rfl),az,aw⟩
  · rintro (⟨j,yes⟩|⟨j,k,ne,aj,ak⟩)
    · exact Or.inl ⟨_,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,yes⟩
    · refine Or.inr ⟨_,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,
        _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,?_,aj,ak⟩
      intro eq
      exact ne (congrArg (fun z : L => z.1.2) eq)

theorem pairCriterion (s : Val) (a b : V) (ne : a≠b) :
    Safe s {(a,false),(b,false)} ↔
      (s a=some true → s b=some false) ∧ (s b=some true → s a=some false) := by
  have pattern : Safe s {(a,false),(b,false)} ↔
      s a=some false ∨ s b=some false ∨ (s a=none ∧ s b=none) := by
    simp [Safe,Holds,ne,Ne.symm ne]
    <;> tauto
  rw [pattern]
  cases p : s a with
  | none => cases q : s b with
            | none => simp
            | some x => cases x <;> simp
  | some v => cases q : s b with
              | none => cases v <;> simp
              | some x => cases v <;> cases x <;> simp

theorem boardCriterion (s : Val) : BaseSafe s ↔ RowRule s ∧ ColumnRule s := by
  constructor
  · intro guard
    constructor
    · intro i
      exact (rowCriterion s i).1 (guard _ (Or.inl ⟨i,rfl⟩))
    · intro i k j ne
      have diff : (i,j)≠(k,j) := fun e => ne (congrArg Prod.fst e)
      exact ((pairCriterion s _ _ diff).1 (guard _ (Or.inr ⟨i,k,j,ne,rfl⟩))).1
  · rintro ⟨rows,cols⟩ _ (⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩)
    · exact (rowCriterion s i).2 (rows i)
    · refine (pairCriterion s _ _ ?_).2 ⟨cols i k j ne,cols k i j ne.symm⟩
      exact fun e => ne (congrArg Prod.fst e)

theorem twoUnused (s : Val) (safe : BaseSafe s) :
    ∃ j k : Fin 4, j≠k ∧ (∀ i : Fin 5, s (i,j)≠some true) ∧
      (∀ i : Fin 5, s (i,k)≠some true) := by
  classical
  obtain ⟨rows,cols⟩ := (boardCriterion s).1 safe
  have missing : ∃ i : Fin 5, ∀ j : Fin 4, s (i,j)≠some true := by
    by_contra! all
    choose f hit using all
    have inj : Function.Injective f := by
      intro i k eq
      by_contra ne
      have ban := cols i k (f i) ne (hit i)
      rw [eq,hit k] at ban
      contradiction
    have count := Fintype.card_le_of_injective f inj
    simpa using count
  obtain ⟨i,miss⟩ := missing
  obtain ⟨j,k,ne,first,second⟩ := (rows i).resolve_left (fun ⟨u,h⟩ => miss u h)
  have unused (u : Fin 4) (openCell : s (i,u)=none) (v : Fin 5) : s (v,u)≠some true := by
    intro h
    by_cases same : v=i
    · subst v
      exact miss u h
    · have ban := cols v i u same h
      rw [openCell] at ban
      contradiction
  exact ⟨j,k,ne,unused j first,unused k second⟩

end PEqualNP.Outside.L_meta_9246.Stable

namespace PEqualNP.Outside.L_meta_9246.Stable
open PEqualNP.ProofComplexity PEqualNP.Search

def trueSupport (s : Val) : Finset V := Finset.univ.filter (fun v => s v=some true)
def falseSupport (s : Val) : Finset V := Finset.univ.filter (fun v => s v=some false)
def bits (on off : Finset V) : Val :=
  fun v => if v∈on then some true else if v∈off then some false else none

theorem rep (s : Val) : bits (trueSupport s) (falseSupport s)=s := by
  funext v
  cases h : s v with
  | none => simp [bits,trueSupport,falseSupport,h]
  | some b => cases b <;> simp [bits,trueSupport,falseSupport,h]

theorem atMostTwo (s : Val) (safe : BaseSafe s) : (trueSupport s).card≤2 := by
  classical
  have cols := ((boardCriterion s).1 safe).2
  have inj : Set.InjOn (fun v : V => v.2) (↑(trueSupport s) : Set V) := by
    intro a ha b hb eq
    rcases a with ⟨i,j⟩
    rcases b with ⟨k,t⟩
    change j=t at eq
    subst t
    have aa : s (i,j)=some true := (Finset.mem_filter.mp ha).2
    have bb : s (k,j)=some true := (Finset.mem_filter.mp hb).2
    by_cases same : i=k
    · subst k
      rfl
    · have no := cols i k j same aa
      rw [bb] at no
      contradiction
  obtain ⟨j,k,ne,hj,hk⟩ := twoUnused s safe
  have sub : (trueSupport s).image Prod.snd ⊆ (Finset.univ.erase j).erase k := by
    intro t mem
    obtain ⟨⟨i,x⟩,inside,rfl⟩ := Finset.mem_image.mp mem
    have yes : s (i,x)=some true := (Finset.mem_filter.mp inside).2
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩⟩
    · rintro rfl
      exact hk i yes
    · rintro rfl
      exact hj i yes
  have bound := Finset.card_le_card sub
  have jk : k∈(Finset.univ : Finset (Fin 4)).erase j :=
    Finset.mem_erase.mpr ⟨ne.symm,Finset.mem_univ _⟩
  rw [Finset.card_image_of_injOn inj,Finset.card_erase_of_mem jk,
    Finset.card_erase_of_mem (Finset.mem_univ j)] at bound
  simpa using bound

theorem sparseExact :
    (∃ ρ : List C, IsRUPRun (PHP 5 4) ρ ∧ (∅ : C)∈ρ ∧ ρ.length≤12) ↔
    ∃ ρ : List C, (∅ : C)∈ρ ∧ ρ.length≤12 ∧ ∀ on off : Finset V, on.card≤2 →
      RowRule (bits on off) → ColumnRule (bits on off) → Ordered (bits on off) ρ := by
  rw [exact12]
  constructor
  · rintro ⟨ρ,h0,hn,test⟩
    exact ⟨ρ,h0,hn,fun on off _ rows cols => test _ ((boardCriterion _).2 ⟨rows,cols⟩)⟩
  · rintro ⟨ρ,h0,hn,test⟩
    refine ⟨ρ,h0,hn,?_⟩
    intro s hs
    have pair := (boardCriterion s).1 hs
    have q := test (trueSupport s) (falseSupport s) (atMostTwo s hs)
    rw [rep] at q
    exact q pair.1 pair.2

end PEqualNP.Outside.L_meta_9246.Stable
