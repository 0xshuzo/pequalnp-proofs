import PEqualNP.Defs
open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9471.SmallPrice
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
def axs : Finset C := {clauseOf 7 0, clauseOf 56 0, clauseOf 448 0, clauseOf 1536 0, clauseOf 0 9, clauseOf 0 18, clauseOf 0 36, clauseOf 0 65, clauseOf 0 72, clauseOf 0 130, clauseOf 0 144, clauseOf 0 260, clauseOf 0 288, clauseOf 0 513, clauseOf 0 520, clauseOf 0 576, clauseOf 0 1026, clauseOf 0 1040, clauseOf 0 1152, clauseOf 0 2052, clauseOf 0 2080, clauseOf 0 2304}
def Raw : Set C := ↑axs
def ons : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,256,0,0,256,0,0,256,256,32,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,32,32,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,1024,1024,1024,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,512,512,512,512,4,4]
def offs : Array Nat := #[0,2048,256,2304,128,2176,64,2112,32,2080,288,2336,160,2208,96,2144,16,2064,272,2320,144,2192,80,2128,8,2056,264,2312,136,2184,72,2120,4,2052,260,2308,132,2180,68,2116,36,2084,292,2340,292,2084,164,2212,2212,100,2148,2148,2276,2308,20,2068,276,2324,148,2196,84,2132,2324,12,2060,268,2316,140,2188,76,2124,2316,2332,2336,2,2050,258,2306,130,2178,66,2114,34,2082,290,2338,162,2210,98,2146,18,2066,274,2322,146,2194,146,2194,658,2706,82,2130,10,2058,266,2314,138,2186,74,2122,2338,1,2049,257,2305,129,2177,65,2113,33,2081,289,2337,161,2209,97,2145,17,2065,273,2321,145,2193,81,2129,9,2057,265,2313,137,2185,73,2121,73,2121,1097,3145,2337,2339]
def frontA : Array Nat := #[111,74,32,24,16,8,6,4,2,98,96,1]
def frontB : Array Nat := #[111,74,73,24,16,53,6,4,45,143,145,1]
def cert : Nat → Nat → Nat → Nat
  | 0, 1, 1 => 148
  | 0, 2, 2 => 147
  | 0, 3, 3 => 135
  | 0, 4, 4 => 127
  | 0, 5, 5 => 119
  | 0, 6, 6 => 117
  | 0, 7, 7 => 115
  | 0, 8, 8 => 113
  | 0, 9, 9 => 143
  | 0, 10, 10 => 145
  | 0, 11, 11 => 112
  | 0, 13, 13 => 148
  | 0, 14, 14 => 147
  | 0, 15, 15 => 135
  | 0, 16, 16 => 127
  | 0, 17, 17 => 119
  | 0, 18, 18 => 117
  | 0, 19, 19 => 115
  | 0, 20, 20 => 113
  | 0, 21, 21 => 143
  | 0, 22, 22 => 145
  | 0, 23, 23 => 112
  | 1, 0, 0 => 148
  | 1, 2, 2 => 110
  | 1, 3, 3 => 102
  | 1, 4, 4 => 90
  | 1, 5, 5 => 82
  | 1, 6, 6 => 80
  | 1, 7, 7 => 78
  | 1, 8, 8 => 76
  | 1, 9, 9 => 98
  | 1, 10, 10 => 96
  | 1, 11, 11 => 75
  | 1, 12, 12 => 148
  | 1, 14, 14 => 110
  | 1, 15, 15 => 102
  | 1, 16, 16 => 90
  | 1, 17, 17 => 82
  | 1, 18, 18 => 80
  | 1, 19, 19 => 78
  | 1, 20, 20 => 76
  | 1, 21, 21 => 98
  | 1, 22, 22 => 96
  | 1, 23, 23 => 75
  | 2, 0, 0 => 111
  | 2, 1, 1 => 74
  | 2, 3, 3 => 24
  | 2, 4, 4 => 16
  | 2, 6, 6 => 6
  | 2, 7, 7 => 4
  | 2, 9, 9 => 98
  | 2, 10, 10 => 145
  | 2, 12, 12 => 147
  | 2, 13, 13 => 110
  | 2, 15, 15 => 63
  | 2, 16, 16 => 54
  | 2, 18, 18 => 38
  | 2, 19, 19 => 36
  | 2, 21, 21 => 143
  | 2, 22, 22 => 96
  | 3, 0, 0 => 135
  | 3, 1, 1 => 102
  | 3, 2, 2 => 63
  | 3, 4, 4 => 72
  | 3, 5, 5 => 71
  | 3, 6, 6 => 30
  | 3, 7, 7 => 28
  | 3, 8, 8 => 26
  | 3, 9, 9 => 143
  | 3, 10, 10 => 145
  | 3, 11, 11 => 25
  | 3, 12, 12 => 135
  | 3, 13, 13 => 102
  | 3, 14, 14 => 63
  | 3, 16, 16 => 72
  | 3, 17, 17 => 71
  | 3, 18, 18 => 30
  | 3, 19, 19 => 28
  | 3, 20, 20 => 26
  | 3, 21, 21 => 143
  | 3, 22, 22 => 145
  | 3, 23, 23 => 25
  | 4, 0, 0 => 127
  | 4, 1, 1 => 90
  | 4, 2, 2 => 54
  | 4, 3, 3 => 72
  | 4, 5, 5 => 62
  | 4, 6, 6 => 22
  | 4, 7, 7 => 20
  | 4, 8, 8 => 18
  | 4, 9, 9 => 98
  | 4, 10, 10 => 96
  | 4, 11, 11 => 17
  | 4, 12, 12 => 127
  | 4, 13, 13 => 90
  | 4, 14, 14 => 54
  | 4, 15, 15 => 72
  | 4, 17, 17 => 62
  | 4, 18, 18 => 22
  | 4, 19, 19 => 20
  | 4, 20, 20 => 18
  | 4, 21, 21 => 98
  | 4, 22, 22 => 96
  | 4, 23, 23 => 17
  | 5, 0, 0 => 111
  | 5, 1, 1 => 74
  | 5, 3, 3 => 24
  | 5, 4, 4 => 16
  | 5, 6, 6 => 6
  | 5, 7, 7 => 4
  | 5, 9, 9 => 98
  | 5, 10, 10 => 145
  | 5, 12, 12 => 119
  | 5, 13, 13 => 82
  | 5, 15, 15 => 71
  | 5, 16, 16 => 62
  | 5, 18, 18 => 14
  | 5, 19, 19 => 12
  | 5, 21, 21 => 143
  | 5, 22, 22 => 96
  | 6, 0, 0 => 117
  | 6, 1, 1 => 80
  | 6, 2, 2 => 38
  | 6, 3, 3 => 30
  | 6, 4, 4 => 22
  | 6, 5, 5 => 14
  | 6, 7, 7 => 52
  | 6, 8, 8 => 51
  | 6, 9, 9 => 143
  | 6, 10, 10 => 145
  | 6, 11, 11 => 7
  | 6, 12, 12 => 117
  | 6, 13, 13 => 80
  | 6, 14, 14 => 38
  | 6, 15, 15 => 30
  | 6, 16, 16 => 22
  | 6, 17, 17 => 14
  | 6, 19, 19 => 52
  | 6, 20, 20 => 51
  | 6, 21, 21 => 143
  | 6, 22, 22 => 145
  | 6, 23, 23 => 7
  | 7, 0, 0 => 115
  | 7, 1, 1 => 78
  | 7, 2, 2 => 36
  | 7, 3, 3 => 28
  | 7, 4, 4 => 20
  | 7, 5, 5 => 12
  | 7, 6, 6 => 52
  | 7, 8, 8 => 48
  | 7, 9, 9 => 98
  | 7, 10, 10 => 96
  | 7, 11, 11 => 5
  | 7, 12, 12 => 115
  | 7, 13, 13 => 78
  | 7, 14, 14 => 36
  | 7, 15, 15 => 28
  | 7, 16, 16 => 20
  | 7, 17, 17 => 12
  | 7, 18, 18 => 52
  | 7, 20, 20 => 48
  | 7, 21, 21 => 98
  | 7, 22, 22 => 96
  | 7, 23, 23 => 5
  | 8, 0, 0 => 111
  | 8, 1, 1 => 74
  | 8, 3, 3 => 24
  | 8, 4, 4 => 16
  | 8, 6, 6 => 6
  | 8, 7, 7 => 4
  | 8, 9, 9 => 98
  | 8, 10, 10 => 145
  | 8, 12, 12 => 113
  | 8, 13, 13 => 76
  | 8, 15, 15 => 26
  | 8, 16, 16 => 18
  | 8, 18, 18 => 51
  | 8, 19, 19 => 48
  | 8, 21, 21 => 143
  | 8, 22, 22 => 96
  | 9, 0, 1 => 148
  | 9, 0, 4 => 127
  | 9, 0, 7 => 115
  | 9, 0, 22 => 145
  | 9, 2, 2 => 32
  | 9, 3, 1 => 102
  | 9, 3, 4 => 72
  | 9, 3, 7 => 28
  | 9, 3, 22 => 145
  | 9, 5, 5 => 8
  | 9, 6, 1 => 80
  | 9, 6, 4 => 22
  | 9, 6, 7 => 52
  | 9, 6, 22 => 145
  | 9, 8, 8 => 2
  | 9, 11, 11 => 1
  | 9, 14, 14 => 73
  | 9, 17, 17 => 53
  | 9, 20, 20 => 45
  | 9, 23, 23 => 44
  | 10, 0, 1 => 148
  | 10, 0, 4 => 127
  | 10, 0, 7 => 115
  | 10, 2, 2 => 32
  | 10, 3, 1 => 102
  | 10, 3, 4 => 72
  | 10, 3, 7 => 28
  | 10, 5, 5 => 8
  | 10, 6, 1 => 80
  | 10, 6, 4 => 22
  | 10, 6, 7 => 52
  | 10, 8, 8 => 2
  | 10, 11, 11 => 1
  | 10, 14, 14 => 73
  | 10, 17, 17 => 53
  | 10, 20, 20 => 45
  | 10, 21, 1 => 98
  | 10, 21, 4 => 98
  | 10, 21, 7 => 98
  | 10, 23, 23 => 44
  | 11, 0, 0 => 112
  | 11, 1, 1 => 75
  | 11, 2, 2 => 33
  | 11, 3, 3 => 25
  | 11, 4, 4 => 17
  | 11, 5, 5 => 9
  | 11, 6, 6 => 7
  | 11, 7, 7 => 5
  | 11, 8, 8 => 3
  | 11, 9, 9 => 99
  | 11, 10, 10 => 146
  | 11, 12, 12 => 112
  | 11, 13, 13 => 75
  | 11, 14, 14 => 73
  | 11, 15, 15 => 25
  | 11, 16, 16 => 17
  | 11, 17, 17 => 53
  | 11, 18, 18 => 7
  | 11, 19, 19 => 5
  | 11, 20, 20 => 45
  | 11, 21, 21 => 144
  | 11, 22, 22 => 97
  | _, _, _ => 0
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
theorem finiteRaw : ∀ i : I, ∀ d ∈ axs, Safe (board i) d := by decide +kernel
theorem fixed : ∀ x : V, board (ea x) x ≠ none ∧ board (eb x) x ≠ none := by decide +kernel
def Result (x : V) (p q : L) : Prop :=
  let s := board (cut x p q)
  (∀ z, cap x p q z → Holds s (negLit z)) ∨
  (s x ≠ none ∧ (Holds s p ∨ Holds s q ∨ (p≠q ∧ s p.1=none ∧ s q.1=none)))
local instance (x : V) (p q : L) : Decidable (Result x p q) := by unfold Result; infer_instance
theorem finiteCuts : ∀ (x : V) (p q : L), board (ea x) p.1=none → board (eb x) q.1=none →
    cap x p q p → cap x p q q → Result x p q := by decide +kernel
theorem raws (i : I) : ∀ d∈Raw, Safe (board i) d := finiteRaw i

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

end PEqualNP.Outside.L_meta_9471.SmallPrice
