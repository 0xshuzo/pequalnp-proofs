import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9471.StrictPhysical

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
def BaseSafe (s : Val) := ∀ c ∈ PHP 6 5, Safe s c

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
def RowRule (s : Val) : Prop := ∀ i : Fin 6, (∃ j : Fin 5, s (i,j)=some true) ∨
  ∃ j k : Fin 5, j≠k ∧ s (i,j)=none ∧ s (i,k)=none
def ColumnRule (s : Val) : Prop := ∀ (i k : Fin 6) (j : Fin 5), i≠k →
  s (i,j)=some true → s (k,j)=some false

theorem rowCriterion (s : Val) (i : Fin 6) :
    Safe s (Finset.univ.image (fun j : Fin 5 => ((i,j),true))) ↔
    (∃ j : Fin 5, s (i,j)=some true) ∨
    ∃ j k : Fin 5, j≠k ∧ s (i,j)=none ∧ s (i,k)=none := by
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


def helper : C := Finset.univ.filter (fun l : L => l.2=true ∧ l.1.1.val≤1 ∧ l.1.2≠1)
def target : C := {(((3 : Fin 6),(2 : Fin 5)),false),(((4 : Fin 6),(3 : Fin 5)),false),
  (((5 : Fin 6),(4 : Fin 5)),false)}
def board : Val := fun v =>
  if v.1.val<3 ∧ v.2.val<2 then none else some (decide (v.1.val=1+v.2.val ∧ 2≤v.2.val))

theorem helperRUP : IsRUP (PHP 6 5) helper := by
  let A := negLit '' (↑helper : Set L)
  have forced (p : Fin 6) (hp : p.val≤1) : UPForces (PHP 6 5) A ((p,(1 : Fin 5)),true) := by
    let row : C := Finset.univ.image (fun h : Fin 5 => ((p,h),true))
    apply UPForces.unit (D:=row)
    · exact Or.inl ⟨p,rfl⟩
    · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
    · intro u hu ne
      obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hu
      apply UPForces.hyp
      refine ⟨((p,h),true),?_,rfl⟩
      have d : h≠1 := by rintro rfl;exact ne rfl
      simp [helper,hp,d]
  let cl : C := {(((0 : Fin 6),(1 : Fin 5)),false),(((1 : Fin 6),(1 : Fin 5)),false)}
  refine ⟨cl,Or.inr ⟨0,1,1,by decide,rfl⟩,?_⟩
  intro u hu
  simp only [cl,Finset.mem_insert,Finset.mem_singleton] at hu
  rcases hu with rfl|rfl
  · exact forced 0 (by decide)
  · exact forced 1 (by decide)

theorem counterBoard : BaseSafe board := by
  apply (boardCriterion board).2
  constructor
  · unfold RowRule
    decide +kernel
  · unfold ColumnRule
    decide +kernel

theorem noSecond : ¬IsRUP (PHP 6 5 ∪ {helper}) target := by
  intro learned
  have dead : ∀ l∈target,Holds board (negLit l) := by
    unfold target
    decide +kernel
  have safe : ∀ c∈PHP 6 5 ∪ {helper},Safe board c := by
    rintro c (old|new)
    · exact counterBoard c old
    · have eq : c=helper := new
      subst c
      right
      exact ⟨(((0 : Fin 6),(0 : Fin 5)),true),by decide,(((1 : Fin 6),(0 : Fin 5)),true),
        by decide,by decide,rfl,rfl⟩
  exact rup_not_dead safe learned dead
end PEqualNP.Outside.L_meta_9471.StrictPhysical

namespace PEqualNP.Outside.L_meta_9471.Boxes
open PEqualNP.ProofComplexity PEqualNP.Search
abbrev P := Fin 6
abbrev H := Fin 5
abbrev V := P × H
abbrev L := Literal V
abbrev C := Clause V
abbrev Box := H → P → Prop

def atVal (p : P) (l : L) : Prop := decide (p=l.1.1)=l.2

theorem opposite (p : P) (l : L) : atVal p (negLit l) ↔ ¬atVal p l := by
  rcases l with ⟨⟨a,h⟩,b⟩
  cases b <;> by_cases e : p=a <;> simp [atVal,negLit,e]

def encode (c : C) : Box := fun h p => ∃ l∈c,l.1.2=h ∧ atVal p l

def live (D : Box) := ∀ h, ∃ p, D h p
def openCell (D b : Box) (h : H) := ∃p,D h p ∧ b h p
def stable (D b : Box) :=
  (∃h,∀p,D h p → b h p) ∨ ∃h k,h≠k ∧ openCell D b h ∧ openCell D b k
def forces (D : Box) (l : L) := ∀ p,D l.1.2 p → atVal p l

theorem openAt {D : Box} {c : C} {h : H} (o : openCell D (encode c) h) :
    ∃ l∈c, l.1.2=h ∧ ∃p,D l.1.2 p ∧ atVal p l := by
  obtain ⟨p,pd,l,lc,eq,val⟩ := o
  exact ⟨l,lc,eq,p,eq.symm ▸ pd,val⟩

theorem propagate {D : Box} (inh : live D) {G : Set C}
    (ok : ∀ c∈G,stable D (encode c)) {A : Set L}
    (assumeVal : ∀ l∈A,forces D l) {l : L} (f : UPForces G A l) : forces D l := by
  induction f with
  | hyp a => exact assumeVal _ a
  | @unit c l hc hl rest ih =>
    have unique {k : L} (hk : k∈c) {q : P} (qd : D k.1.2 q) (yes : atVal q k) : k=l := by
      by_contra ne
      exact (opposite q k).mp (ih k hk ne q qd) yes
    intro p pd
    rcases ok c hc with ⟨h,all⟩ | ⟨h,k,ne,oh,ok⟩
    · by_cases eq : h=l.1.2
      · obtain ⟨a,ac,ae,yes⟩ := all p (eq.symm ▸ pd)
        have al := unique ac (by simpa only [ae,eq] using pd) yes
        exact al ▸ yes
      · obtain ⟨q,qd⟩ := inh h
        obtain ⟨a,ac,ae,yes⟩ := all q qd
        have al := unique ac (ae.symm ▸ qd) yes
        exact (eq (ae.symm.trans (congrArg (fun t : L => t.1.2) al))).elim
    · obtain ⟨u,uc,uh,q,qd,uy⟩ := openAt oh
      obtain ⟨v,vc,vk,r,rd,vy⟩ := openAt ok
      have uv := (unique uc qd uy).trans (unique vc rd vy).symm
      exact (ne ((uh.symm.trans (congrArg (fun t : L => t.1.2) uv)).trans vk)).elim

def Step (B : Set Box) (b : Box) :=
  ∀ D, live D → (∀ a∈B,stable D a) → ∃h,openCell D b h

theorem projectStep {G : Set C} {c : C} (s : IsRUP G c) : Step (encode '' G) (encode c) := by
  classical
  intro D inhabited ok
  by_contra! dead
  have base (d : C) (hd : d∈G) := ok (encode d) ⟨d,hd,rfl⟩
  have assumptions (k : L) (hk : k∈negLit '' (↑c : Set L)) : forces D k := by
    obtain ⟨a,ha,rfl⟩ := hk
    intro p pd
    apply (opposite p a).mpr
    intro yes
    exact dead a.1.2 ⟨p,pd,a,ha,rfl,yes⟩
  obtain ⟨d,hd,unsat⟩ := s
  have invalid (o : ∃ h,openCell D (encode d) h) : False := by
    obtain ⟨h,oh⟩ := o
    obtain ⟨a,ha,_,p,pd,yes⟩ := openAt oh
    exact (opposite p a).mp (propagate inhabited base assumptions (unsat a ha) p pd) yes
  apply invalid
  rcases base d hd with ⟨h,all⟩|⟨h,k,_,oh,_⟩
  · obtain ⟨q,qd⟩ := inhabited h
    exact ⟨h,q,qd,all q qd⟩
  · exact ⟨h,oh⟩

inductive Run (G : Set Box) : List Box → Prop
  | nil : Run G []
  | add {ds b} : Run G ds → Step (G ∪ {a | a∈ds}) b → Run G (b::ds)

theorem project {G : Set C} {cs : List C} (r : IsRUPRun G cs) : Run (encode '' G) (cs.map encode) := by
  induction r with
  | nil => exact .nil
  | @learn ds c hist step ih =>
    apply Run.add ih
    have e : encode '' (G ∪ {a | a∈ds}) = encode '' G ∪ {a | a∈ds.map encode} := by
      ext b
      constructor
      · rintro ⟨a,ha,rfl⟩
        rcases ha with h | h
        · exact Or.inl ⟨a,h,rfl⟩
        · exact Or.inr (List.mem_map.mpr ⟨a,h,rfl⟩)
      · rintro (⟨a,h,rfl⟩|h)
        · exact ⟨a,Or.inl h,rfl⟩
        · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
          exact ⟨a,Or.inr ha,rfl⟩
    rw [←e]
    exact projectStep step

theorem originalBound (h : ∃ cs : List C, IsRUPRun (PHP 6 5) cs ∧ ∅∈cs ∧ cs.length≤20) :
    ∃ bs : List Box, Run (encode '' PHP 6 5) bs ∧ encode ∅∈bs ∧ bs.length≤20 := by
  obtain ⟨cs,h,ending,len⟩ := h
  exact ⟨cs.map encode,project h,List.mem_map.mpr ⟨∅,ending,rfl⟩,by simpa using len⟩



namespace Check
def bits (b : Nat) : Box := fun h p => b.testBit (6*h.val+p.val)=true
def inside (D : Box) (b : Nat) := ∀ h p,D h p → bits b h p
def disj (u v : Nat) (h : H) := ∀ p : P,¬(bits u h p ∧ bits v h p)
instance (u v : Nat) (h : H) : Decidable (disj u v h) := by unfold disj bits; infer_instance

def relax (u a v : Nat) (j : H) := (∀ h : H,h≠j → disj u a h) ∧
    ∀ h p,bits u h p → (h=j → bits a h p) → bits v h p
instance (u a v : Nat) (j : H) : Decidable (relax u a v j) := by
  unfold relax disj bits
  infer_instance

theorem relaxSound {D : Box} (inh : live D) {u a v : Nat} {j : H}
    (prev : inside D u) (st : stable D (bits a)) (r : relax u a v j) : inside D v := by
  have only (h : H) (oh : openCell D (bits a) h) : h=j := by
    by_contra ne
    obtain ⟨p,pd,pa⟩ := oh
    exact r.1 h ne p ⟨prev h p pd,pa⟩
  have last (p : P) (pd : D j p) : bits a j p := by
    rcases st with ⟨h,all⟩|⟨h,k,ne,oh,ok⟩
    · obtain ⟨q,qd⟩ := inh h
      obtain rfl := only h ⟨q,qd,all q qd⟩
      exact all p pd
    · exact (ne ((only h oh).trans (only k ok).symm)).elim
  intro h p pd
  apply r.2 h p (prev h p pd)
  intro eq
  subst h
  exact last p pd

structure Narrow where
  source : Nat
  slot : H
  next : Nat
  deriving DecidableEq
def walk (bank : List Nat) (u : Nat) : List Narrow → Bool
  | [] => decide (∃ h : H,∀p : P, (u.testBit (6*h.val+p.val))=false)
  | r::rs => decide (r.source∈bank ∧ relax u r.source r.next r.slot) && walk bank r.next rs

theorem walkSound {bank : List Nat} {D : Box} (inh : live D)
    (st : ∀ a∈bank,stable D (bits a)) {u : Nat} {rs : List Narrow}
    (prev : inside D u) (ok : walk bank u rs=true) : False := by
  induction rs generalizing u with
  | nil =>
    obtain ⟨h,off⟩ : ∃ h : H,∀p : P, (u.testBit (6*h.val+p.val))=false := of_decide_eq_true ok
    obtain ⟨p,pd⟩ := inh h
    exact Bool.noConfusion ((prev h p pd).symm.trans (off p))
  | cons r rs ih =>
    change (decide (r.source∈bank ∧ relax u r.source r.next r.slot) && walk bank r.next rs)=true at ok
    simp only [Bool.and_eq_true,decide_eq_true_eq] at ok
    exact ih (relaxSound inh prev (st _ ok.1.1) ok.1.2) ok.2

structure Line where
  goal : Nat
  start : Nat
  path : List Narrow

def lineOK (bank : List Nat) (l : Line) := decide (∀ h : H,∀p : P,
    l.goal.testBit (6*h.val+p.val)=false → l.start.testBit (6*h.val+p.val)=true) &&
    walk bank l.start l.path

theorem lineSound {bank : List Nat} {G : Set Box} (avail : ∀ a∈bank,bits a∈G)
    {l : Line} (ok : lineOK bank l=true) : Step G (bits l.goal) := by
  classical
  simp only [lineOK,Bool.and_eq_true,decide_eq_true_eq] at ok
  intro D inh st
  by_contra! dead
  apply walkSound inh (fun a ha => st _ (avail a ha)) (u:=l.start) (rs:=l.path) _ ok.2
  intro h p pd
  apply ok.1
  cases v : l.goal.testBit (6*h.val+p.val)
  · rfl
  · exact (dead h ⟨p,pd,v⟩).elim

def rawCodes : List Nat := [17043521,34087042,68174084,136348168,272696336,545392672]
def rawEncoded : Set Box := {a|∃ n∈rawCodes,a=bits n}
def example0 : Line := ⟨51130371,1022611452,[⟨17043521,1,1022607484⟩, ⟨34087042,0,1022607424⟩]⟩
def example1 : Line := ⟨532639744,541102079,[⟨51130371,0,541102019⟩, ⟨68174084,1,541098243⟩, ⟨17043521,0,541098241⟩, ⟨34087042,0,541098240⟩]⟩

abbrev helper := PEqualNP.Outside.L_meta_9471.StrictPhysical.helper
abbrev target := PEqualNP.Outside.L_meta_9471.StrictPhysical.target

theorem helperEncoding : encode helper=bits example0.goal := by
  funext h p
  apply propext
  have e : ∀ (j : H) (v : P), (∃ l∈helper,l.1.2=j ∧ decide (v=l.1.1)=l.2) ↔
      (example0.goal.testBit (6*j.val+v.val)=true) := by decide +kernel
  exact e h p
theorem targetEncoding : encode target=bits example1.goal := by
  funext h p
  apply propext
  have e : ∀ (j : H) (v : P), (∃ l∈target,l.1.2=j ∧ decide (v=l.1.1)=l.2) ↔
      (example1.goal.testBit (6*j.val+v.val)=true) := by decide +kernel
  exact e h p

theorem explicitGap : IsRUP (PHP 6 5) helper ∧
    ¬IsRUP (PHP 6 5 ∪ {helper}) target ∧ Step (rawEncoded ∪ {encode helper}) (encode target) := by
  refine ⟨PEqualNP.Outside.L_meta_9471.StrictPhysical.helperRUP,PEqualNP.Outside.L_meta_9471.StrictPhysical.noSecond,?_⟩
  rw [helperEncoding,targetEncoding]
  apply lineSound (l:=example1) (bank:=example0.goal::rawCodes) _ (by decide +kernel)
  intro a ha
  rcases List.mem_cons.mp ha with eq|old
  · exact Or.inr (by simp [eq])
  · exact Or.inl ⟨a,old,rfl⟩
end Check
end PEqualNP.Outside.L_meta_9471.Boxes
