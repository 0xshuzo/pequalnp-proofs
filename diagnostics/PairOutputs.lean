import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166_Pairs
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

theorem badPos {a : V→Bool} {p n : C} {w : V}
    (none : ¬ClauseSat a (merge p n w)) (off : a w=false) : ¬ClauseSat a p := by
  rintro ⟨l,mem,on⟩
  have ne : l≠(w,true) := by intro eq; subst l; change a w=true at on; simp_all
  exact none ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,mem⟩),on⟩
theorem badNeg {a : V→Bool} {p n : C} {w : V}
    (none : ¬ClauseSat a (merge p n w)) (on : a w=true) : ¬ClauseSat a n := by
  rintro ⟨l,mem,off⟩
  have ne : l≠(w,false) := by intro eq; subst l; change a w=false at off; simp_all
  exact none ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,mem⟩),off⟩

def Exposed (a b : V→Bool) (v : V) (t : List Entry) : Prop :=
  ∃ r n, (r,some (v,n))∈t ∧ ¬ClauseSat a r ∧ ¬ClauseSat b r
theorem up {a b : V→Bool} {v : V} {t : List Entry} {e : Entry} :
    Exposed a b v t → Exposed a b v (e::t) := by
  rintro ⟨r,n,m,h,k⟩; exact ⟨r,n,List.mem_cons_of_mem _ m,h,k⟩
theorem separate {v : V} {a b : V→Bool} (agree : ∀w, w≠v → a w=b w)
    (raw : ∀c∈PHP 5 4,ClauseSat a c ∨ ClauseSat b c)
    {t : List Entry} (valid : Valid t) :
    ∀c∈t.map Prod.fst, ¬ClauseSat a c → ¬ClauseSat b c → Exposed a b v t := by
  induction valid with
  | nil => simp
  | @ax t c prev ax ih =>
    intro d mem na nb
    rcases List.mem_cons.mp mem with rfl|old
    · exact ((raw _ ax).elim na nb).elim
    · exact up (ih _ old na nb)
  | @res t p n w prev mp mn pp nn ih =>
    intro d mem na nb
    rcases List.mem_cons.mp mem with rfl|old
    · by_cases eq : w=v
      · subst w; exact ⟨_,n,List.mem_cons_self,na,nb⟩
      · cases on : a w with
        | false =>
          have boff := (agree w eq).symm.trans on
          exact up (ih p mp (badPos na on) (badPos nb boff))
        | true =>
          have bon := (agree w eq).symm.trans on
          exact up (ih n mn (badNeg na on) (badNeg nb bon))
    · exact up (ih _ old na nb)

def left (v : V) (place : Row→Hole) (z : V) : Bool :=
  decide (z.1≠v.1 ∧ z.2=place z.1)
def right (v : V) (place : Row→Hole) (z : V) : Bool :=
  left v place z || decide (z=v)
def Noncolliding (v : V) (place : Row→Hole) :=
  ∀i j : Row, i≠v.1 → j≠v.1 → place i=place j → i=j
theorem privateRaw (v : V) (place : Row→Hole) (inj : Noncolliding v place)
    (c : C) (mem : c∈PHP 5 4) : ClauseSat (left v place) c ∨ ClauseSat (right v place) c := by
  rcases mem with ⟨i,rfl⟩|⟨i,j,h,ne,rfl⟩
  · right
    by_cases eq : i=v.1
    · subst i
      exact ⟨((v.1,v.2),true),Finset.mem_image_of_mem _ (Finset.mem_univ _),by simp [right]⟩
    · exact ⟨((i,place i),true),Finset.mem_image_of_mem _ (Finset.mem_univ _),by simp [right,left,eq]⟩
  · left
    by_cases hi : left v place (i,h)=false
    · exact ⟨((i,h),false),by simp,hi⟩
    by_cases hj : left v place (j,h)=false
    · exact ⟨((j,h),false),by simp,hj⟩
    have ai : i≠v.1 ∧ h=place i := by simpa [left] using hi
    have aj : j≠v.1 ∧ h=place j := by simpa [left] using hj
    exact (ne (inj i j ai.1 aj.1 (ai.2.symm.trans aj.2))).elim
theorem allPairs {π : List C} (hπ : IsRefutation (PHP 5 4) π) :
    ∃t, Valid t ∧ t.map Prod.fst=π ∧ ∀v place, Noncolliding v place →
      Exposed (left v place) (right v place) v t := by
  obtain ⟨t,val,eq⟩:=traceOf hπ.1
  refine ⟨t,val,eq,?_⟩
  intro v place inj
  have ag : ∀w, w≠v → left v place w=right v place w := by
    intro w ne; simp [right,ne]
  exact separate ag (privateRaw v place inj) val ∅ (eq.symm ▸ hπ.2)
    (by simp [ClauseSat]) (by simp [ClauseSat])
end PEqualNP.Outside.L_pcx_166_Pairs
