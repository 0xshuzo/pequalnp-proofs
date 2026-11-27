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

theorem twoUnused (s : Val) (safe : BaseSafe s) :
    ∃ j k : Fin 5, j≠k ∧ (∀ i : Fin 6, s (i,j)≠some true) ∧
      (∀ i : Fin 6, s (i,k)≠some true) := by
  classical
  obtain ⟨rows,cols⟩ := (boardCriterion s).1 safe
  have missing : ∃ i : Fin 6, ∀ j : Fin 5, s (i,j)≠some true := by
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
  have unused (u : Fin 5) (openCell : s (i,u)=none) (v : Fin 6) : s (v,u)≠some true := by
    intro h
    by_cases same : v=i
    · subst v
      exact miss u h
    · have ban := cols v i u same h
      rw [openCell] at ban
      contradiction
  exact ⟨j,k,ne,unused j first,unused k second⟩

end PEqualNP.Outside.L_meta_9471.Waves

namespace PEqualNP.Outside.L_meta_9471.Waves
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

theorem atMostThree (s : Val) (safe : BaseSafe s) : (trueSupport s).card≤3 := by
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
  have jk : k∈(Finset.univ : Finset (Fin 5)).erase j :=
    Finset.mem_erase.mpr ⟨ne.symm,Finset.mem_univ _⟩
  rw [Finset.card_image_of_injOn inj,Finset.card_erase_of_mem jk,
    Finset.card_erase_of_mem (Finset.mem_univ j)] at bound
  simpa using bound


abbrev Raw := PHP 6 5
def emptyBoard : Val := fun _ => none
def move (s : Val) (v : V) (b : Bool) : Val := fun w =>
  if w=v then some b else if b=true ∧ w.2=v.2 then some false else s w


def openCols (s : Val) (i : Fin 6) : Finset (Fin 5) := Finset.univ.filter (fun j => s (i,j)=none)
def Slack (k : Nat) (s : Val) : Prop := ColumnRule s ∧ ∀ i : Fin 6,
    (∃ j : Fin 5, s (i,j)=some true) ∨ k+2 ≤ (openCols s i).card
def play (s : Val) (v : V) (b : Bool) (w : V) : Option Bool :=
  match s w with
  | some t => some t
  | none => if w=v then some b else if b=true ∧ w.2=v.2 then some false else none

theorem playExt (s : Val) (v : V) (b : Bool) : Ext s (play s v b) := by
  intro w t ht
  simp [play,ht]

theorem cameTrue {s : Val} {v w : V} {b : Bool} (h : play s v b w=some true) :
    s w=some true ∨ (w=v ∧ b=true) := by
  cases e : s w with
  | some t => left; simpa [play,e] using h
  | none =>
    right
    by_cases eq : w=v
    · subst w
      exact ⟨rfl,by simpa [play,e] using h⟩
    · by_cases t : b=true ∧ w.2=v.2 <;> simp [play,e,eq,t] at h

theorem playCols {s : Val} {v : V} {b : Bool} (blank : s v=none) (cols : ColumnRule s) :
    ColumnRule (play s v b) := by
  intro i k j diff yes
  rcases cameTrue yes with old|⟨eq,bit⟩
  · exact playExt s v b (k,j) false (cols i k j diff old)
  · subst v
    subst b
    have dk : (k,j) ≠ (i,j) := fun a => diff.symm (congrArg Prod.fst a)
    cases old : s (k,j) with
    | none => simp [play,old,dk]
    | some t =>
      cases t with
      | false => simp [play,old]
      | true =>
        have bad := cols k i j diff.symm old
        rw [blank] at bad
        contradiction

theorem stepSlack {s : Val} {v : V} {k : Nat} (b : Bool) (hs : Slack (k+1) s) (blank : s v=none) :
    Slack k (play s v b) := by
  refine ⟨playCols blank hs.1,?_⟩
  intro i
  rcases hs.2 i with ⟨j,hit⟩|many
  · exact Or.inl ⟨j,playExt s v b _ _ hit⟩
  · right
    have sub : (openCols s i).erase v.2 ⊆ openCols (play s v b) i := by
      intro j hj
      obtain ⟨ne,inside⟩ := Finset.mem_erase.mp hj
      have val := (Finset.mem_filter.mp inside).2
      have diff : (i,j) ≠ v := fun eq => ne (congrArg Prod.snd eq)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [play,val,diff,ne]⟩
    have card := Finset.card_le_card sub
    by_cases mem : v.2∈openCols s i
    · rw [Finset.card_erase_of_mem mem] at card
      omega
    · rw [Finset.erase_eq_of_notMem mem] at card
      omega

def layer : Nat → Set C
  | 0 => Raw
  | k+1 => Wave (layer k)

theorem survives (k : Nat) (s : Val) (hs : Slack k s) : Stable (layer k) s := by
  induction k generalizing s with
  | zero =>
    apply (boardCriterion _).2
    refine ⟨?_,hs.1⟩
    intro i
    rcases hs.2 i with yes|many
    · exact Or.inl yes
    · obtain ⟨j,jm,t,tm,ne⟩ := Finset.one_lt_card.mp (show 1<(openCols s i).card by omega)
      exact Or.inr ⟨j,t,ne,(Finset.mem_filter.mp jm).2,(Finset.mem_filter.mp tm).2⟩
  | succ k ih =>
    have lo : Slack k s := by
      refine ⟨hs.1,?_⟩
      intro i
      rcases hs.2 i with yes|many
      · exact Or.inl yes
      · exact Or.inr (by omega)
    apply safe_of_branches (ih s lo)
    intro v free b
    exact ⟨play s v b,playExt s v b,by simp [play,free],ih _ (stepSlack b hs free)⟩

theorem firstFourSafe : Stable (layer 3) emptyBoard := by
  apply survives
  constructor
  · simp [ColumnRule,emptyBoard]
  · intro i
    right
    simp [openCols,emptyBoard]

theorem notFourth : ¬ IsRUP (layer 3) (∅ : C) := by
  intro h
  exact rup_not_dead firstFourSafe h (by simp)
theorem hasUnknown (s : Val) (hs : BaseSafe s) : ∃ v : V, s v=none := by
  classical
  have cols := ((boardCriterion s).1 hs).2
  have rows := ((boardCriterion s).1 hs).1
  have missing : ∃ i : Fin 6, ∀ j : Fin 5, s (i,j) ≠ some true := by
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
  exact ⟨(i,j),first⟩

theorem increases {s t : Val} (ex : Ext s t) {v : V} (blank : s v=none)
    (bit : t v=some true) : (trueSupport s).card < (trueSupport t).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ex x true (Finset.mem_filter.mp hx).2⟩
  · intro eq
    have mem : v∈trueSupport t := Finset.mem_filter.mpr ⟨Finset.mem_univ _,bit⟩
    rw [←eq] at mem
    have sm := (Finset.mem_filter.mp mem).2
    change s v=some true at sm
    rw [blank] at sm
    contradiction

theorem loseOne (G : Set C) (extendsRaw : Raw ⊆ G) (n : Nat)
    (price : ∀ s, Stable G s → (trueSupport s).card≤n) :
    ∀ s, Stable (Wave G) s → (trueSupport s).card<n := by
  intro s good
  obtain ⟨same,rep⟩ := (stableWave G s).1 good
  obtain ⟨v,empty⟩ := hasUnknown s (fun c hc => same _ (extendsRaw hc))
  obtain ⟨t,ex,on,better⟩ := rep v empty true
  exact Nat.lt_of_lt_of_le (increases ex empty on) (price t better)


theorem emptyAtFifth : IsRUP (layer 4) (∅ : C) := by
  classical
  by_contra fail
  obtain ⟨s,stable,_⟩ := capture (c:=∅) (by simp [Proper]) fail
  have p1 := loseOne Raw (fun _ hx => hx) 3 atMostThree
  have p2 := loseOne (layer 1) (fun _ hx => Or.inl hx) 2
    (fun t ht => Nat.le_of_lt_succ (p1 t ht))
  have p3 := loseOne (layer 2) (fun _ hx => Or.inl (Or.inl hx)) 1
    (fun t ht => Nat.le_of_lt_succ (p2 t ht))
  have p4 := loseOne (layer 3) (fun _ hx => Or.inl (Or.inl (Or.inl hx))) 0
    (fun t ht => Nat.le_of_lt_succ (p3 t ht))
  exact Nat.not_lt_zero _ (p4 s stable)

end PEqualNP.Outside.L_meta_9471.Waves
