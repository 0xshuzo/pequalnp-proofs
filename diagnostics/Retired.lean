import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166_Retired
open PEqualNP.ProofComplexity
abbrev V := Fin 5 × Fin 4
abbrev C := Clause V
def join (p n : C) (v : V) : C := p.erase (v,true) ∪ n.erase (v,false)

-- A cone of an ordinary proof using only the allowed pivot cells.
inductive Cone (allow : V → Prop) : C → Prop where
 | raw {c} : c ∈ PHP 5 4 → Cone allow c
 | step {p n v} : allow v → (v,true) ∈ p → (v,false) ∈ n →
     Cone allow p → Cone allow n → Cone allow (join p n v)

theorem lifts {π : List C} (d : IsDerivation (PHP 5 4) π) :
    ∀ c∈π, Cone (fun _ => True) c := by
  induction d with
  | nil => simp
  | ax prev ax ih =>
    intro c h
    rcases List.mem_cons.mp h with rfl|old
    · exact .raw ax
    · exact ih _ old
  | res prev hp hn step ih =>
    obtain ⟨v,p,n,rfl⟩ := step
    intro c h
    rcases List.mem_cons.mp h with rfl|old
    · exact .step trivial p n (ih _ hp) (ih _ hn)
    · exact ih _ old

def inside (S : V → Prop) (c d : C) := ∀ l∈c, S l.1 → l∈d
def killed (S : V → Prop) (a : V → Bool) (c : C) := ∀ l∈c, ¬S l.1 → a l.1 ≠ l.2

theorem retired {S : V→Prop} {c : C} (cone : Cone (fun v => ¬S v) c)
    (a : V→Bool) (off : killed S a c) :
    ∃ r∈PHP 5 4, inside S r c ∧ killed S a r := by
  induction cone with
  | raw raw => exact ⟨_,raw,(fun _ h _ => h),off⟩
  | @step p n v free pos neg cp cn ihp ihn =>
    have kp {l : Literal V} (h : l∈p) (ne : l≠(v,true)) : l∈join p n v :=
      Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,h⟩)
    have kn {l : Literal V} (h : l∈n) (ne : l≠(v,false)) : l∈join p n v :=
      Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,h⟩)
    cases bit : a v with
    | false =>
      have h : killed S a p := by
        intro l m g
        by_cases e : l=(v,true)
        · subst l; simpa using bit
        · exact off l (kp m e) g
      obtain ⟨r,raw,sub,kill⟩ := ihp h
      refine ⟨r,raw,?_,kill⟩
      intro l m g
      apply kp (sub l m g)
      rintro rfl
      exact free g
    | true =>
      have h : killed S a n := by
        intro l m g
        by_cases e : l=(v,false)
        · subst l; simpa using bit
        · exact off l (kn m e) g
      obtain ⟨r,raw,sub,kill⟩ := ihn h
      refine ⟨r,raw,?_,kill⟩
      intro l m g
      apply kn (sub l m g)
      rintro rfl
      exact free g

-- On a concrete ancestry path from the empty clause, only previously queried
-- cells can occur in the clause at the stopping node.
def names (S : V→Prop) (c : C) := ∀ l∈c,S l.1
theorem parents {S : V→Prop} {p n : C} {v : V}
    (h : names S (join p n v)) (hs : S v) : names S p ∧ names S n := by
  constructor
  · intro l m
    by_cases e : l=(v,true)
    · subst l; exact hs
    · exact h l (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,m⟩))
  · intro l m
    by_cases e : l=(v,false)
    · subst l; exact hs
    · exact h l (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e,m⟩))

-- All profiles at this physical site falsify its clause. A suffix assignment
-- respecting their jointly fixed live bits produces a common violated raw clause,
-- once the retired bits of each profile are put back.
def glue (S : V → Prop) [DecidablePred S] (x a : V→Bool) (v : V) :=
  if S v then x v else a v
theorem common {S F : V→Prop} [DecidablePred S] {c : C}
    (cone : Cone (fun v => ¬S v) c) (earlier : names (fun v => S v ∨ F v) c)
    {I : Type} [Nonempty I] (x : I→V→Bool) (fals : ∀i,¬ClauseSat (x i) c)
    (a : V→Bool) (live : ∀v,F v → ∀b,(∀i,x i v=b) → a v=b) :
    ∃r∈PHP 5 4, ∀i, ¬ClauseSat (glue S (x i) a) r := by
  have af (i : I) {l : Literal V} (m : l∈c) : x i l.1≠l.2 :=
    fun e => fals i ⟨l,m,e⟩
  have k : killed S a c := by
    intro l m ns
    have f := (earlier l m).resolve_left ns
    cases val : l.2 with
    | false =>
      have all : ∀i,x i l.1=true := by intro i; have h := af i m; cases u : x i l.1 <;> simp_all
      have aa := live l.1 f true all
      simp [aa,val]
    | true =>
      have all : ∀i,x i l.1=false := by intro i; have h := af i m; cases u : x i l.1 <;> simp_all
      have aa := live l.1 f false all
      simp [aa,val]
  obtain ⟨r,raw,sub,fail⟩ := retired cone a k
  refine ⟨r,raw,?_⟩
  intro i
  rintro ⟨l,m,on⟩
  by_cases g : S l.1
  · exact af i (sub l m g) (by simpa [glue,g] using on)
  · exact fail l m g (by simpa [glue,g] using on)
end PEqualNP.Outside.L_pcx_166_Retired
