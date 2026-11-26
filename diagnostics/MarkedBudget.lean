import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9248.Locality

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

theorem safe_run {s : Val} (bs : BaseSafe s) {rs : List C} (run : IsRUPRun (PHP 5 4) rs)
    (no : ∀ c ∈ rs, ¬ Single s c) : ∀ c ∈ rs, Safe s c := by
  induction run with
  | nil => simp
  | @learn rs c prev rup ih =>
    have old := ih (fun d hd => no d (List.mem_cons_of_mem _ hd))
    have g : ∀ d ∈ PHP 5 4 ∪ {d | d ∈ rs}, Safe s d := by
      rintro d (h|h)
      · exact bs d h
      · exact old d h
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · by_contra bad
      exact no _ List.mem_cons_self (single_of_not_safe bad (rup_not_dead g rup))
    · exact old d hd

def KeepGame (P : Val → Prop) : Nat → Val → Prop
  | 0,s => P s
  | n+1,s => P s ∧ ∀ v, s v = none → ∃ t, Ext s t ∧ t v ≠ none ∧ KeepGame P n t

theorem ext_trans {s t u : Val} (a : Ext s t) (b : Ext t u) : Ext s u :=
  fun i j eq => b i j (a i j eq)

theorem avoidKept {P : Val → Prop} (k : Nat) (s : Val) (g : KeepGame P k s) (cs : Finset C) (small : cs.card ≤ k) :
    ∃ t, Ext s t ∧ P t ∧ ∀ c ∈ cs, ¬ Single t c := by
  classical
  induction k generalizing s cs with
  | zero =>
    have e : cs = ∅ := Finset.card_eq_zero.mp (by omega)
    subst cs
    exact ⟨s,fun _ _ h => h,g,by simp⟩
  | succ k ih =>
    by_cases hit : ∃ c ∈ cs, Single s c
    · obtain ⟨c,hc,a,ha,ua,forced⟩ := hit
      obtain ⟨t,st,ta,gt⟩ := g.2 a.1 ua
      obtain ⟨u,tu,bu,ok⟩ := ih t gt (cs.erase c) (by rw [Finset.card_erase_of_mem hc]; omega)
      have su := ext_trans st tu
      refine ⟨u,su,bu,?_⟩
      intro d hd
      by_cases eq : d = c
      · subst d
        rintro ⟨z,hz,uz,_⟩
        by_cases ez : z = a
        · subst z
          obtain ⟨b,eb⟩ := Option.ne_none_iff_exists'.mp ta
          have := tu a.1 b eb
          simp_all
        · have ea := forced z hz ez
          have := su z.1 (!z.2) ea
          simp_all
      · exact ok d (Finset.mem_erase.mpr ⟨eq,hd⟩)
    · push Not at hit
      exact ⟨s,fun _ _ h => h,g.1,hit⟩


theorem safe_not_single {s : Val} {c : C} (bs : Safe s c) : ¬Single s c := by
  rintro ⟨l,hl,un,rest⟩
  rcases bs with ⟨z,hz,yes⟩ | ⟨a,am,b,bm,ne,an,bn⟩
  · by_cases eq : z=l
    · subst z
      simp [Holds,un] at yes
    · exact clash_holds yes (rest _ hz eq)
  · by_cases eq : a=l
    · have bad := rest _ bm (fun e => ne (eq.trans e.symm))
      simp [Holds,negLit,bn] at bad
    · have bad := rest _ am eq
      simp [Holds,negLit,an] at bad

-- Once a set of marked physical clauses stays safe throughout the game,
-- one ordinary decision suffices for each remaining distinct nonempty clause.
theorem marked_budget {cs : List C} (run : IsRUPRun (PHP 5 4) cs)
    (out : (∅ : C)∈cs) (marks : Finset C)
    (members : marks ⊆ cs.toFinset.erase ∅) {k : Nat}
    (game : ∃s, KeepGame (fun t => BaseSafe t ∧ ∀d∈marks, Safe t d) k s) :
    k+marks.card+2 ≤ cs.length := by
  classical
  by_contra! short
  let cache := (cs.toFinset.erase ∅) \ marks
  have hm : (∅ : C)∈cs.toFinset := List.mem_toFinset.mpr out
  have sz := Finset.card_sdiff_add_card_eq_card members
  have listBound := List.toFinset_card_le (l:=cs)
  rw [Finset.card_erase_of_mem hm] at sz
  have small : cache.card≤k := by
    dsimp [cache]
    omega
  obtain ⟨s,g⟩ := game
  obtain ⟨t,_,⟨base,kept⟩,others⟩ := avoidKept k s g cache small
  have nosingle : ∀c∈cs, ¬Single t c := by
    intro c hc
    by_cases empty : c=∅
    · subst c; simp [Single]
    by_cases listed : c∈marks
    · exact safe_not_single (kept c listed)
    · exact others c (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨empty,List.mem_toFinset.mpr hc⟩,listed⟩)
  have bad := safe_run base run nosingle ∅ out
  simp [Safe] at bad

def games (cs : List C) (k n : Nat) : Prop :=
  ∃ marks : Finset C, marks.card=n ∧ marks⊆cs.toFinset.erase ∅ ∧
    ∃s, KeepGame (fun t => BaseSafe t ∧ ∀d∈marks, Safe t d) k s

theorem census9 {cs : List C} (run : IsRUPRun (PHP 5 4) cs) (out : (∅ : C)∈cs)
    (classification : games cs 5 2 ∨ games cs 4 3) : 9≤cs.length := by
  rcases classification with ⟨m,r,h,g⟩ | ⟨m,r,h,g⟩
  · have b := marked_budget run out m h g
    omega
  · have b := marked_budget run out m h g
    omega
end PEqualNP.Outside.L_meta_9248.Locality
