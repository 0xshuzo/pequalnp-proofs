import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166_Pivot
open PEqualNP.ProofComplexity
abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev C := Clause V
abbrev Entry := C × Option (V × C)

def merge (p n : C) (w : V) : C := p.erase (w,true) ∪ n.erase (w,false)

inductive Valid : List Entry → Prop
  | nil : Valid []
  | ax {t : List Entry} {c : C} : Valid t → c∈PHP 5 4 → Valid ((c,none)::t)
  | res {t : List Entry} {p n : C} {w : V} : Valid t →
      p∈t.map Prod.fst → n∈t.map Prod.fst → (w,true)∈p → (w,false)∈n →
      Valid ((merge p n w,some (w,n))::t)

theorem traceOf {π : List C} (h : IsDerivation (PHP 5 4) π) :
    ∃t : List Entry, Valid t ∧ t.map Prod.fst=π := by
  induction h with
  | nil => exact ⟨[],Valid.nil,rfl⟩
  | ax prev ax ih =>
    obtain ⟨t,valid,rfl⟩:=ih
    exact ⟨_,Valid.ax valid ax,rfl⟩
  | res prev hp hn step ih =>
    obtain ⟨t,valid,rfl⟩:=ih
    obtain ⟨v,pp,nn,rfl⟩:=step
    exact ⟨_,Valid.res valid hp hn pp nn,rfl⟩

def Used (v : V) (n : C) (t : List Entry) : Prop :=
  ∃e∈t, e.2=some (v,n)

theorem usedTail {v : V} {n : C} {t : List Entry} {e : Entry} (h : Used v n t) :
    Used v n (e::t) := by
  obtain ⟨z,m,eq⟩:=h
  exact ⟨z,List.mem_cons_of_mem _ m,eq⟩

def board (v : V) (k : Hole) (w : V) : Bool :=
  if w.1=v.1 then decide (w.2=v.2) else
    decide (w.2.val=((w.1.val-(if v.1.val<w.1.val then 1 else 0))+k.val)%4)

set_option maxRecDepth 8000 in
theorem boardRows : ∀v : V, ∀k : Hole, ∀r : Row, ∃h : Hole, board v k (r,h)=true := by decide +kernel
set_option maxRecDepth 8000 in
theorem boardEdges : ∀v : V, ∀k : Hole, ∀a b : Row, ∀h : Hole, a≠b →
    board v k (a,h)=true → board v k (b,h)=true → (a,h)=v ∨ (b,h)=v := by decide +kernel
set_option maxRecDepth 8000 in
theorem boardOn : ∀v : V, ∀k : Hole, board v k v=true := by decide +kernel
set_option maxRecDepth 8000 in
theorem boardHits : ∀v w : V, ∀s : Bool,
    (w.1≠v.1 ∨ (s=false ∧ w≠v) ∨ (s=true ∧ w=v)) →
    ∃k : Hole, board v k w=s := by decide +kernel

theorem rawBarrier {v : V} {k : Hole} {d : C} (ax : d∈PHP 5 4) :
    ClauseSat (board v k) d ∨ (v,false)∈d := by
  rcases ax with ⟨r,rfl⟩|⟨a,b,h,ne,rfl⟩
  · obtain ⟨j,on⟩:=boardRows v k r
    exact Or.inl ⟨((r,j),true),Finset.mem_image_of_mem _ (Finset.mem_univ j),on⟩
  · by_cases off : board v k (a,h)=false
    · exact Or.inl ⟨((a,h),false),by simp,off⟩
    by_cases off2 : board v k (b,h)=false
    · exact Or.inl ⟨((b,h),false),by simp,off2⟩
    have on1 : board v k (a,h)=true := by cases hh : board v k (a,h) <;> simp_all
    have on2 : board v k (b,h)=true := by cases hh : board v k (b,h) <;> simp_all
    rcases boardEdges v k a b h ne on1 on2 with h1|h2
    · right; rw [←h1]; simp
    · right; rw [←h2]; simp

theorem satMerge {a : V → Bool} {p n : C} {w : V}
    (hp : ClauseSat a p) (hn : ClauseSat a n) : ClauseSat a (merge p n w) := by
  obtain ⟨l,mem,on⟩:=hp
  by_cases eq : l=(w,true)
  · subst l
    obtain ⟨s,sm,sv⟩:=hn
    have ne : s≠(w,false) := by intro h; subst s; change a w=true at on; change a w=false at sv; simp_all
    exact ⟨s,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,sm⟩),sv⟩
  · exact ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,mem⟩),on⟩

theorem guardedTrace {v : V} {n0 : C} {k : Hole} {t : List Entry} (valid : Valid t)
    (same : ∀n, Used v n t → n=n0) (satisfied : ClauseSat (board v k) n0) :
    ∀d∈t.map Prod.fst, ClauseSat (board v k) d ∨ (v,false)∈d := by
  induction valid with
  | nil => simp
  | @ax t c prev ax ih =>
    intro d mem
    rcases List.mem_cons.mp mem with rfl|old
    · exact rawBarrier ax
    · exact ih (fun n h=>same n (usedTail h)) d old
  | @res t p n w prev mp mn pp nn ih =>
    have prior:=ih (fun z h=>same z (usedTail h))
    intro d mem
    rcases List.mem_cons.mp mem with rfl|old
    · by_cases eq : w=v
      · subst w
        have en : n=n0 := same n ⟨_,List.mem_cons_self,rfl⟩
        have ns : ClauseSat (board v k) n := en.symm ▸ satisfied
        obtain ⟨l,lm,on⟩:=ns
        have ne : l≠(v,false) := by
          intro h; subst l
          change board v k v=false at on
          simp [boardOn] at on
        exact Or.inl ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,lm⟩),on⟩
      · rcases prior _ mp with sp|neg
        · rcases prior _ mn with sn|neg
          · exact Or.inl (satMerge sp sn)
          · exact Or.inr (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp [Ne.symm eq],neg⟩))
        · exact Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp,neg⟩))
    · exact prior d old

def guards (v : V) (c : C) : Prop := ∀w : V, w.1=v.1 → (w,true)∈c → (v,true)∈c

theorem rawGuards {v : V} {c : C} (hc : c∈PHP 5 4) : guards v c := by
  rcases hc with ⟨r,rfl⟩|⟨i,j,h,ne,rfl⟩
  · intro w eq mem
    obtain ⟨k,_,hk⟩:=Finset.mem_image.mp mem
    have row : r=v.1 := (congrArg (fun l : Literal V=>l.1.1) hk).trans eq
    exact Finset.mem_image.mpr ⟨v.2,Finset.mem_univ _,by rw [row]⟩
  · intro w _ mem
    simp at mem

theorem mergeGuards {v w : V} {p n : C} (ne : w≠v) (hp : guards v p) (hn : guards v n) :
    guards v (merge p n w) := by
  intro x row mem
  rcases Finset.mem_union.mp mem with l|r
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨by simp [Ne.symm ne],hp x row (Finset.mem_erase.mp l).2⟩)
  · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp,hn x row (Finset.mem_erase.mp r).2⟩)

theorem guardsOrFirst {v : V} {n0 : C} {t : List Entry} (valid : Valid t)
    (same : ∀n, Used v n t → n=n0) :
    (guards v n0 ∧ (v,false)∈n0) ∨
    ((∀n, ¬Used v n t) ∧ ∀c∈t.map Prod.fst, guards v c) := by
  induction valid with
  | nil => right; simp [Used]
  | @ax t c prev ax ih =>
    rcases ih (fun n h=>same n (usedTail h)) with ok|⟨unused,prior⟩
    · exact Or.inl ok
    right
    constructor
    · rintro n ⟨e,em,eq⟩
      rcases List.mem_cons.mp em with rfl|old
      · simp at eq
      · exact unused n ⟨e,old,eq⟩
    · intro d mem
      rcases List.mem_cons.mp mem with rfl|old
      · exact rawGuards ax
      · exact prior _ old
  | @res t p n w prev mp mn pp nn ih =>
    rcases ih (fun n h=>same n (usedTail h)) with ok|⟨unused,prior⟩
    · exact Or.inl ok
    by_cases eq : w=v
    · subst w
      have en : n=n0 := same n ⟨_,List.mem_cons_self,rfl⟩
      exact Or.inl (en ▸ And.intro (prior n mn) nn)
    right
    constructor
    · rintro z ⟨e,em,ee⟩
      rcases List.mem_cons.mp em with rfl|old
      · have ev : w=v := congrArg Prod.fst (Option.some.inj ee)
        exact eq ev
      · exact unused z ⟨e,old,ee⟩
    · intro d mem
      rcases List.mem_cons.mp mem with rfl|old
      · exact mergeGuards eq (prior p mp) (prior n mn)
      · exact prior _ old

theorem singleNegative {t : List Entry} (valid : Valid t) (empty : (∅ : C)∈t.map Prod.fst)
    {v : V} {n0 : C} (once : Used v n0 t) (same : ∀n, Used v n t → n=n0) :
    n0 = {(v,false)} := by
  obtain ⟨guard,mem⟩ : guards v n0 ∧ (v,false)∈n0 := by
    rcases guardsOrFirst valid same with yes|⟨no,_⟩
    · exact yes
    · exact False.elim (no n0 once)
  have misses (k : Hole) : ¬ ClauseSat (board v k) n0 := by
    intro sat
    rcases guardedTrace valid same sat ∅ empty with h|h <;> simpa [ClauseSat] using h
  have avoid (w : V) (s : Bool) (m : (w,s)∈n0)
      (h : w.1≠v.1 ∨ (s=false ∧ w≠v) ∨ (s=true ∧ w=v)) : False := by
    obtain ⟨k,on⟩:=boardHits v w s h
    exact misses k ⟨(w,s),m,on⟩
  apply Finset.Subset.antisymm
  · intro l hl
    obtain ⟨w,s⟩:=l
    by_cases sameRow : w.1=v.1
    · cases s
      · by_cases eq : w=v
        · subst w; simp
        · exact False.elim (avoid w false hl (Or.inr (Or.inl ⟨rfl,eq⟩)))
      · exact False.elim (avoid v true (guard w sameRow hl) (Or.inr (Or.inr ⟨rfl,rfl⟩)))
    · exact False.elim (avoid w s hl (Or.inl sameRow))
  · simpa using mem

end PEqualNP.Outside.L_pcx_166_Pivot
