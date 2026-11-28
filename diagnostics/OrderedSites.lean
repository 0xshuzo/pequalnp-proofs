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

namespace PEqualNP.Outside.L_pcx_166_Retired
open PEqualNP.ProofComplexity
abbrev Site := C × V

-- A topological proof list may be unfolded using the same site for all copies
-- of a shared node. Free pivots may be queried at any time on any path.
inductive Schedule (bank : List Site) (free : V → Bool) (rank : V→Nat) : Nat→C→Prop where
 | raw {k c} : c∈PHP 5 4 → Schedule bank free rank k c
 | step {k p n v} : (join p n v,v)∈bank → (v,true)∈p → (v,false)∈n →
     (free v=true ∨ k≤rank v) →
     Schedule bank free rank (if free v then k else rank v) p →
     Schedule bank free rank (if free v then k else rank v) n →
     Schedule bank free rank k (join p n v)

theorem coneAlong {bank free rank k c} (tr : Schedule bank free rank k c) {P : V→Prop}
    (safe : ∀w,free w=true ∨ k≤rank w → P w) : Cone P c := by
  induction tr with
  | raw ax => exact .raw ax
  | @step k p n w m pp nn ok tp tn i1 i2 =>
    have up : k≤(if free w then k else rank w) := by
      cases b : free w <;> simp [b] at * 
      exact ok
    have more : ∀z,free z=true ∨ (if free w then k else rank w)≤rank z → P z := by
      intro z h
      exact safe z (h.imp_right (Nat.le_trans up))
    exact .step (safe w ok) pp nn (i1 more) (i2 more)

theorem splitCone {v : V} {c : C} (tr : Cone (fun w => w≠v) c)
    {a b : V→Bool} (ag : ∀w,w≠v → a w=b w) (raw : ∀r∈PHP 5 4,ClauseSat a r ∨ ClauseSat b r)
    (ha : ¬ClauseSat a c) (hb : ¬ClauseSat b c) : False := by
  induction tr with
  | raw ax => exact (raw _ ax).elim ha hb
  | @step p n w diff pp nn tp tn ihp ihn =>
    have left {x : V→Bool} (off : x w=false) (hc : ¬ClauseSat x (join p n w)) : ¬ClauseSat x p := by
      rintro ⟨l,m,e⟩
      have ne : l≠(w,true) := by rintro rfl; change x w=true at e; simp_all
      exact hc ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,m⟩),e⟩
    have right {x : V→Bool} (on_ : x w=true) (hc : ¬ClauseSat x (join p n w)) : ¬ClauseSat x n := by
      rintro ⟨l,m,e⟩
      have ne : l≠(w,false) := by rintro rfl; change x w=false at e; simp_all
      exact hc ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,m⟩),e⟩
    cases d : a w with
    | false => exact ihp (left d ha) (left ((ag w diff).symm.trans d) hb)
    | true => exact ihn (right d ha) (right ((ag w diff).symm.trans d) hb)

def earlier (free : V→Bool) (rank : V→Nat) (v w : V) : Prop := free w=false ∧ rank w<rank v
def mayName (free : V→Bool) (rank : V→Nat) (v w : V) : Prop := earlier free rank v w ∨ free w=true
def witness (bank : List Site) (free : V→Bool) (rank : V→Nat) (v : V) (a b : V→Bool) : Prop :=
  ∃ c,(c,v)∈bank ∧ names (mayName free rank v) c ∧ Cone (fun w => ¬earlier free rank v w) c ∧
    ¬ClauseSat a c ∧ ¬ClauseSat b c

theorem locate {bank free rank k c} (tr : Schedule bank free rank k c) {v : V}
    (ex : free v=false) (uniq : Function.Injective rank) {a b : V→Bool}
    (ag : ∀w,w≠v → a w=b w) (raw : ∀r∈PHP 5 4,ClauseSat a r ∨ ClauseSat b r)
    (support : names (mayName free rank v) c) (ha : ¬ClauseSat a c) (hb : ¬ClauseSat b c) :
    witness bank free rank v a b := by
  induction tr with
  | raw ax => exact ((raw _ ax).elim ha hb).elim
  | @step k p n w mem pp nn ok tp tn ihp ihn =>
    by_cases eq : w=v
    · subst w
      have saf : ∀z,free z=true ∨ (if free v then k else rank v)≤rank z → ¬earlier free rank v z := by
        intro z h g
        rcases h with e|zlarge
        · simp [g.1] at e
        · simp [ex] at zlarge
          exact (Nat.not_lt_of_ge zlarge) g.2
      have here : ¬earlier free rank v v := fun e => (Nat.lt_irrefl _) e.2
      exact ⟨_,mem,support,.step here pp nn (coneAlong tp saf) (coneAlong tn saf),ha,hb⟩
    by_cases used : mayName free rank v w
    · obtain ⟨pname,nname⟩:=parents support used
      have lp {x : V→Bool} (d : x w=false) (h : ¬ClauseSat x (join p n w)) : ¬ClauseSat x p := by
        rintro ⟨l,m,y⟩
        have ne : l≠(w,true) := by rintro rfl; change x w=true at y; simp_all
        exact h ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,m⟩),y⟩
      have ln {x : V→Bool} (d : x w=true) (h : ¬ClauseSat x (join p n w)) : ¬ClauseSat x n := by
        rintro ⟨l,m,y⟩
        have ne : l≠(w,false) := by rintro rfl; change x w=false at y; simp_all
        exact h ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,m⟩),y⟩
      cases d : a w with
      | false => exact ihp pname (lp d ha) (lp ((ag w eq).symm.trans d) hb)
      | true => exact ihn nname (ln d ha) (ln ((ag w eq).symm.trans d) hb)
    · have off : free w=false := by cases b : free w <;> simp_all [mayName]
      have no : ¬rank w<rank v := fun h => used (Or.inl ⟨off,h⟩)
      have ne : rank w≠rank v := fun e => eq (uniq e)
      have lt : rank v<rank w := by omega
      have absent : ∀z, free z=true ∨ (if free w then k else rank w)≤rank z → z≠v := by
        intro z h e
        subst z
        simp [off,ex] at h
        omega
      exact (splitCone (.step eq pp nn (coneAlong tp absent) (coneAlong tn absent)) ag raw ha hb).elim

theorem atEmpty {bank free rank k v a b} (tr : Schedule bank free rank k (∅ : C))
    (ex : free v=false) (uniq : Function.Injective rank) (ag : ∀w,w≠v → a w=b w)
    (raw : ∀r∈PHP 5 4,ClauseSat a r ∨ ClauseSat b r) : witness bank free rank v a b := by
  exact locate tr ex uniq ag raw (by intro l m; simp at m) (by simp [ClauseSat]) (by simp [ClauseSat])
end PEqualNP.Outside.L_pcx_166_Retired
