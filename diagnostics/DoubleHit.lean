import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9471.Waves

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


abbrev Raw := PHP 6 5
def blank : Val := fun _ => none
def place (q w : V) : Option Bool :=
  if w=q then some true else if w.1=q.1 ∨ w.2=q.2 then some false else none
def test (l : L) (w : V) : Option Bool :=
  if l.2 then (if w=l.1 then some false else none) else place l.1 w
def move (s : Val) (v : V) (b : Bool) : Val := fun w =>
  if w=v then some b else if b=true ∧ w.2=v.2 then some false else s w
def fixed (q : V) (l : L) : Bool := decide (place q l.1 = some l.2)
def hit (q : V) (c : C) : Bool := decide (∃ l ∈ c, fixed q l = true)

local instance (s : Val) : Decidable (RowRule s) := by unfold RowRule; infer_instance
local instance (s : Val) : Decidable (ColumnRule s) := by unfold ColumnRule; infer_instance
local instance (s t : Val) : Decidable (Ext s t) := by unfold Ext; infer_instance
set_option synthInstance.maxSize 4096
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem testRaw : ∀ l, RowRule (test l) ∧ ColumnRule (test l) := by decide +kernel

theorem testBranch : ∀ l v b, test l v = none →
    RowRule (move (test l) v b) ∧ ColumnRule (move (test l) v b) ∧ Ext (test l) (move (test l) v b) := by
  decide +kernel

theorem testWave (l : L) : Stable (Wave Raw) (test l) := by
  apply safe_of_branches ((boardCriterion _).2 (testRaw l))
  intro v free b
  obtain ⟨r,c,e⟩ := testBranch l v b free
  exact ⟨_,e,by simp [move],(boardCriterion _).2 ⟨r,c⟩⟩

theorem blankWave : Stable (Wave Raw) blank := by
  have rows : RowRule blank ∧ ColumnRule blank := by decide +kernel
  have next : ∀ v b, RowRule (move blank v b) ∧ ColumnRule (move blank v b) := by decide +kernel
  apply safe_of_branches ((boardCriterion _).2 rows)
  intro v _ b
  exact ⟨_,by simp [Ext,blank],by simp [move],(boardCriterion _).2 (next v b)⟩

theorem kills : ∀ l : L, Holds (test l) (negLit l) := by
  unfold Holds
  decide +kernel

theorem common : ∀ l k : L, Holds (test l) (negLit k) →
    ∃ q : V, fixed q l = true ∧ fixed q k = true := by
  unfold Holds
  decide +kernel

theorem widthSafe {s : Val} {d : C} (wide : 1 < d.card) (allow : ∀ k ∈ d, ¬ Holds s (negLit k)) :
    Safe s d := by
  by_cases yes : ∃ l ∈ d, Holds s l
  · exact Or.inl yes
  · obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp wide
    exact Or.inr ⟨i,hi,j,hj,ne,unknown_of_neither (fun a => yes ⟨i,hi,a⟩) (allow i hi),
      unknown_of_neither (fun a => yes ⟨j,hj,a⟩) (allow j hj)⟩

theorem allWide {G : Set C} (b : Stable G blank) (t : ∀ l, Stable G (test l)) {cs : List C}
    (run : IsRUPRun G cs) (sep : ∀ q, cs.countP (hit q) ≤ 1) : ∀ c ∈ cs, 1 < c.card := by
  induction run with
  | nil => simp
  | @learn cs c before step ih =>
    have tailSep : ∀ q, cs.countP (hit q) ≤ 1 := by
      intro q
      have h := sep q
      rw [List.countP_cons] at h
      split at h <;> omega
    have wide := ih tailSep
    have nonempty : c ≠ ∅ := by
      rintro rfl
      apply rup_not_dead (s:=blank) (G:=G ∪ {d | d ∈ cs}) _ step (by simp)
      rintro d (h|hd)
      · exact b d h
      · exact widthSafe (wide _ hd) (by simp [Holds,blank])
    have nonunit (l : L) : c ≠ {l} := by
      rintro rfl
      apply rup_not_dead (s:=test l) (G:=G ∪ {d | d ∈ cs}) _ step (by simpa using kills l)
      rintro d (h|hd)
      · exact t l d h
      · apply widthSafe (wide _ hd)
        intro k hk bad
        obtain ⟨q,hl,hkq⟩ := common l k bad
        have one : hit q {l}=true := by simp [hit,hl]
        have two : 0 < cs.countP (hit q) :=
          List.countP_pos_iff.mpr ⟨d,hd,decide_eq_true ⟨k,hk,hkq⟩⟩
        have h := sep q
        rw [List.countP_cons_of_pos one] at h
        omega
    intro d hd
    rcases List.mem_cons.mp hd with eq|hm
    · subst d
      by_contra! hn
      have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr nonempty)
      obtain ⟨l,hl⟩ := Finset.card_eq_one.mp (show c.card = 1 by omega)
      exact nonunit l hl
    · exact wide d hm

theorem twoHits {cs : List C} (run : IsRUPRun (Wave Raw) cs) (empty : (∅ : C) ∈ cs) :
    ∃ q, 2 ≤ cs.countP (hit q) := by
  by_contra! no
  have sep : ∀ q, cs.countP (hit q) ≤ 1 := fun q => by have := no q; omega
  have bad := allWide blankWave testWave run sep ∅ empty
  simpa using bad

end PEqualNP.Outside.L_meta_9471.Waves
