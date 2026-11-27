import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9248.Waves

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

theorem unique_unknown {s : Val} {c : C} (sg : Single s c) {a b : L}
    (ha : a∈c) (hb : b∈c) (ua : s a.1=none) (ub : s b.1=none) : a=b := by
  obtain ⟨p,hp,up,rest⟩ := sg
  have eq (l : L) (m : l∈c) (u : s l.1=none) : l=p := by
    by_contra ne
    have h := rest l m ne
    simp [Holds,negLit,u] at h
  exact (eq a ha ua).trans (eq b hb ub).symm

theorem disqualify {s t : Val} {c : C} {v : V}
    (sm : ∀ x, t x=none → s x=none) (un : s v=none) (assigned : t v≠none)
    (ss : Single s c) (st : Single t c) {l : L} (mem : l∈c) : l.1≠v := by
  intro eq
  obtain ⟨p,hp,openP,unused⟩ := st
  have e := unique_unknown ss mem hp (by simpa only [eq] using un) (sm _ openP)
  rw [← e,eq] at openP
  exact assigned openP

def Obstructs (K : Set Val) : Prop :=
  ∃ s∈K, ∀ v, s v=none → ∃ a∈K, ∃ b∈K,
    (∀ x, b x=none → a x=none) ∧ a v=none ∧ b v≠none

theorem noCommon {K : Set Val} (h : Obstructs K) (c : C) :
    ¬ ∀ s∈K, Single s c := by
  intro common
  obtain ⟨s,hs,blocks⟩ := h
  obtain ⟨l,hl,free,_⟩ := common s hs
  obtain ⟨a,ha,b,hb,sm,un,assigned⟩ := blocks l.1 free
  exact disqualify sm un assigned (common a ha) (common b hb) hl rfl

theorem stabRun {G : Set C} {s : Val} {cs : List C}
    (base : Stable G s) (run : IsRUPRun G cs)
    (avoid : ∀ c∈cs, ¬Single s c) : ∀ c∈cs, Safe s c := by
  induction run with
  | nil => simp
  | @learn pre c prev learnt ih =>
    have prior := ih (fun d hd => avoid d (List.mem_cons_of_mem _ hd))
    have enlarged : Stable (G ∪ {d | d∈pre}) s := by
      rintro d (h|h)
      · exact base d h
      · exact prior d h
    intro d mem
    rcases List.mem_cons.mp mem with rfl|old
    · by_contra bad
      exact avoid _ List.mem_cons_self (single_of_not_safe bad (rup_not_dead enlarged learnt))
    · exact prior d old

def anchors (G : Set C) (a : C) (cell : V) : Set Val :=
  {s | Stable G s ∧ Safe s a ∧ s cell≠none}

theorem fourImpossible (G : Set C) (a : C) (v : V)
    (blocks : Obstructs (anchors G a v)) (b : C) (sign : Bool) :
    ¬ IsRUPRun G [∅,{(v,sign)},b,a] := by
  intro run
  apply noCommon blocks b
  intro t ht
  obtain ⟨good,first,fixed⟩ := ht
  by_contra nb
  have avoid : ∀ c∈[∅,{(v,sign)},b,a], ¬Single t c := by
    intro c mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · simp [Single]
    · rintro ⟨p,hp,openP,_⟩
      have e : p=(v,sign) := Finset.mem_singleton.mp hp
      subst p
      exact fixed openP
    · exact nb
    · exact noSingle first
  have broken := stabRun good run avoid ∅ List.mem_cons_self
  simp [Safe] at broken

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


abbrev Core := Fin 24
abbrev Stored := Fin 601
abbrev CaseKey := Fin 1
def num (v : V) : Nat := 4*v.1.val+v.2.val
def data : Array (Nat × Nat) := #[(0,105),(0,139817),(2,139817),(0,655361),(0,655365),(0,70081),(16,70081),(0,559109),(0,559237),(0,794657),(0,794913),(0,795169),(0,671809),(0,672833),(0,557189),(0,786977),(0,791073),(0,656449),(0,526469),(0,49697),(0,115233),(0,541761),(0,533025),(0,270881),(4,279659),(2,139881),(2,139885),(4,279657),(128,559225),(16,69993),(16,70121),(128,559209),(0,361),(384,628857),(0,617),(516,418923),(0,1129),(1026,418413),(0,2153),(2064,627177),(0,4201),(4224,625017),(0,8297),(8196,411243),(0,16489),(16386,403053),(0,32873),(32784,596457),(0,65641),(65664,563577),(0,131177),(131076,288363),(0,262249),(262146,157293),(0,524393),(524304,104937),(4,419435),(2,139821),(4,419433),(0,139833),(16,209705),(0,139881),(66,419373),(0,139945),(128,698921),(0,140073),(256,209465),(0,140841),(0,141865),(2048,697001),(0,143913),(4096,205625),(0,156201),(0,172585),(32768,666281),(0,205353),(65536,144185),(0,401961),(0,664105),(524288,174761),(6,419433),(2,139833),(18,209705),(2,139945),(130,698921),(2,140073),(258,209465),(2,140841),(2,141865),(2050,697001),(2,143913),(4098,205625),(2,156201),(2,172585),(32770,666281),(2,205353),(65538,144185),(2,401961),(2,664105),(524290,174761),(0,655363),(2,664097),(65540,939345),(0,655369),(8,690305),(0,655377),(262160,742725),(0,655393),(32,664067),(0,655425),(65600,939285),(0,655489),(128,690185),(0,655617),(262400,742485),(0,655873),(512,663587),(0,656385),(66560,938325),(0,657409),(2048,688265),(0,659457),(266240,738645),(0,663553),(8192,655907),(0,671745),(81920,922965),(0,688129),(32768,657545),(262144,738373),(65536,659729),(65536,921873),(262144,672837),(8,690311),(2,664101),(2,664109),(8,690309),(0,655381),(0,655397),(40,699015),(0,655429),(0,655493),(130,698925),(0,655621),(0,655877),(520,698535),(0,656389),(0,657413),(2050,697005),(0,659461),(0,663557),(8200,690855),(0,671749),(0,688133),(32770,666285),(65536,659733),(65536,921877),(0,70083),(18,209889),(0,70085),(4,349633),(0,70089),(8,629185),(32,209875),(16,70113),(32,209859),(0,70593),(528,209379),(0,71105),(1024,348613),(0,72129),(2048,627145),(0,78273),(8208,201699),(0,86465),(16384,333253),(0,102849),(32768,596425),(0,201153),(131088,78819),(0,332225),(262144,87493),(0,594369),(524288,104905),(16,70083),(16,70085),(20,349633),(16,70089),(24,629185),(48,209859),(16,70593),(16,71105),(1040,348613),(16,72129),(2064,627145),(16,78273),(16,86465),(16400,333253),(16,102849),(32784,596425),(16,201153),(16,332225),(262160,87493),(16,594369),(524304,104905),(8,559239),(2,698917),(2,698925),(8,559237),(0,559125),(16,628997),(0,559141),(0,559173),(64,838661),(0,559365),(256,628757),(0,559621),(0,560133),(1024,837701),(0,563205),(4096,624917),(0,567301),(0,575493),(16384,822341),(0,624645),(65536,563477),(0,690181),(131080,567975),(0,821253),(262144,576581),(2,699045),(2,699053),(0,559253),(16,629125),(0,559269),(0,559301),(64,838789),(0,559493),(256,628885),(0,559749),(0,560261),(1024,837829),(0,563333),(4096,625045),(0,567429),(0,575621),(16384,822469),(0,624773),(65536,563605),(0,690309),(0,821381),(262144,576709),(0,794659),(65538,930609),(0,794661),(4,812129),(0,794665),(8,829601),(0,794673),(131088,865059),(0,794721),(64,812069),(0,794785),(128,829481),(131328,864819),(66048,930099),(0,795681),(1024,811109),(0,796705),(2048,827561),(0,798753),(135168,860979),(0,811041),(16384,795749),(0,827425),(32768,796841),(131072,860707),(65536,799025),(65536,930097),(131072,795171),(0,794915),(0,794917),(4,812385),(0,794921),(8,829857),(0,794929),(0,794977),(64,812325),(0,795041),(128,829737),(0,795425),(0,795937),(1024,811365),(0,796961),(2048,827817),(0,799009),(0,811297),(16384,796005),(0,827681),(32768,797097),(131072,860963),(131072,795427),(0,795171),(0,795173),(4,812641),(0,795177),(8,830113),(0,795185),(0,795233),(64,812581),(0,795297),(128,829993),(0,796193),(1024,811621),(0,797217),(2048,828073),(0,799265),(0,811553),(16384,796261),(0,827937),(32768,797353),(65536,799537),(65536,930609),(0,671811),(2,680545),(0,671813),(0,671817),(8,706753),(0,671825),(0,671841),(32,680515),(0,671937),(128,706633),(0,672065),(0,672321),(512,680035),(0,673857),(2048,704713),(0,675905),(0,680001),(8192,672355),(0,704577),(32768,673993),(65536,676177),(65536,938321),(0,672835),(2,681569),(0,672837),(0,672841),(8,707777),(0,672849),(0,672865),(32,681539),(0,672961),(128,707657),(0,673089),(0,673345),(512,681059),(0,674881),(2048,705737),(0,676929),(0,681025),(8192,673379),(0,705601),(32768,675017),(65536,677201),(65536,939345),(2,696997),(2,697005),(0,557205),(16,627077),(0,557221),(0,557253),(64,836741),(0,557445),(256,626837),(0,557701),(0,558213),(1024,835781),(0,561285),(4096,622997),(0,565381),(0,573573),(16384,820421),(0,622725),(65536,561557),(0,688261),(0,819333),(262144,574661),(0,786979),(0,786981),(4,804449),(0,786985),(8,821921),(0,786993),(0,787041),(64,804389),(0,787105),(128,821801),(0,787233),(0,788001),(1024,803429),(0,789025),(2048,819881),(73728,922419),(0,803361),(16384,788069),(0,819745),(32768,789161),(65536,791345),(65536,922417),(0,791075),(0,791077),(4,808545),(0,791081),(8,826017),(0,791089),(0,791137),(64,808485),(0,791201),(128,825897),(0,791329),(0,792097),(1024,807525),(0,793121),(2048,823977),(0,807457),(16384,792165),(0,823841),(32768,793257),(131072,864803),(131072,799267),(0,656451),(2,665185),(0,656453),(0,656457),(8,691393),(0,656465),(0,656481),(32,665155),(0,656577),(128,691273),(0,656705),(0,656961),(512,664675),(0,658497),(2048,689353),(0,660545),(0,664641),(8192,656995),(0,689217),(32768,658633),(65536,660817),(65536,922961),(2,666277),(2,666285),(0,526485),(16,596357),(0,526501),(0,526533),(64,806021),(0,526725),(256,596117),(0,526981),(0,527493),(1024,805061),(0,530565),(4096,592277),(0,534661),(0,542853),(16384,789701),(0,592005),(65536,530837),(0,657541),(0,788613),(262144,543941),(0,49699),(4098,254769),(0,49701),(4,312929),(0,49705),(8,576161),(0,49713),(8208,250659),(0,49761),(64,312869),(0,49825),(128,576041),(0,49953),(8448,250419),(0,50721),(1024,311909),(0,51745),(2048,574121),(8192,184867),(4096,115505),(4096,123697),(8192,180771),(73728,185139),(0,180769),(135168,123699),(0,311841),(262144,50789),(0,573985),(524288,51881),(0,115235),(0,115237),(4,378465),(0,115241),(8,641697),(0,115249),(0,115297),(64,378405),(0,115361),(128,641577),(0,115489),(0,116257),(1024,377445),(0,117281),(2048,639657),(8192,250403),(8192,246307),(0,246305),(0,377377),(262144,116325),(0,639521),(524288,117417),(0,541763),(0,541765),(4,803905),(0,541769),(8,576705),(0,541777),(16,611649),(0,541793),(0,541889),(128,576585),(0,542017),(256,611409),(0,542273),(0,543809),(2048,574665),(0,545857),(4096,607569),(0,549953),(0,574529),(32768,543945),(0,607297),(65536,546129),(131072,550499),(0,803905),(262144,541765),(0,533027),(0,533029),(0,533033),(8,567969),(0,533041),(16,602913),(0,533089),(0,533153),(128,567849),(0,533281),(256,602673),(0,534049),(0,535073),(2048,565929),(0,537121),(4096,598833),(0,549409),(0,565793),(32768,535209),(0,598561),(65536,537393),(0,664097),(131072,533027),(262144,550501),(0,270883),(2,401953),(0,270885),(4,288353),(0,270889),(0,270897),(16,340769),(0,270945),(64,288293),(0,271009),(0,271137),(256,340529),(0,271905),(1024,287333),(0,272929),(0,274977),(4096,336689),(0,287265),(16384,271973),(0,303649),(0,336417),(65536,275249),(0,401953),(131072,270883),(524288,305833)]
def moveIds : Array Nat := #[0,0,24,25,26,27,0,0,28,29,0,0,0,0,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,1,1,56,2,57,58,1,1,59,60,1,1,61,62,63,64,65,66,1,1,67,37,68,69,70,71,1,1,72,45,73,74,75,76,1,1,77,53,78,79,2,2,2,2,57,80,2,2,81,82,2,2,25,62,83,84,85,86,2,2,87,37,88,89,90,91,2,2,92,45,93,94,95,96,2,2,97,53,98,99,3,3,100,101,4,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,3,3,131,132,3,3,4,4,133,134,4,4,135,136,137,106,138,139,140,110,141,142,143,114,144,145,146,118,147,148,149,122,150,151,152,126,153,154,129,155,4,4,156,132,4,4,5,5,157,158,159,160,161,162,163,6,164,165,5,5,5,5,5,5,166,167,168,169,170,171,5,5,172,173,174,175,176,177,5,5,178,179,180,181,182,183,6,6,184,158,185,186,187,188,6,6,164,189,6,6,6,6,6,6,190,167,191,192,193,194,6,6,195,173,196,197,198,199,6,6,200,179,201,202,203,204,7,7,205,206,7,7,207,208,209,210,211,139,212,213,8,142,214,215,216,145,217,218,7,7,219,220,221,151,222,223,7,7,224,225,226,227,228,229,7,7,8,8,205,230,8,8,231,208,232,233,234,139,235,236,8,8,237,238,239,145,240,241,8,8,242,243,244,151,245,246,8,8,247,248,249,227,250,251,8,8,9,9,252,253,254,255,256,257,258,259,9,9,260,261,262,263,10,264,11,265,266,267,268,269,270,271,9,9,272,273,274,275,276,277,278,279,9,9,9,9,10,10,280,253,281,282,283,284,285,259,10,10,286,287,288,289,10,10,290,265,291,292,293,294,295,271,10,10,296,297,298,299,300,277,278,301,10,10,10,10,11,11,302,253,303,304,305,306,307,259,11,11,308,309,310,311,290,264,11,11,312,313,314,315,316,271,11,11,317,318,319,320,276,321,322,279,11,11,11,11,12,12,323,324,325,102,326,327,328,106,329,330,12,12,331,332,333,114,334,335,13,118,336,337,338,122,339,340,12,12,341,342,129,343,12,12,344,132,12,12,13,13,345,346,347,102,348,349,350,106,351,352,13,13,353,354,355,114,356,357,13,13,358,359,360,122,361,362,13,13,363,364,129,365,13,13,366,132,13,13,14,14,205,367,14,14,368,208,369,370,371,139,372,373,14,14,374,375,376,145,377,378,8,148,379,380,381,151,382,383,14,14,384,385,386,227,387,388,14,14,15,15,389,253,390,391,392,393,394,259,15,15,395,396,397,398,399,264,15,15,400,401,402,403,16,271,11,404,405,406,407,408,276,409,410,279,15,15,15,15,16,16,411,253,412,413,414,415,416,259,16,16,417,418,419,420,421,264,16,16,422,423,424,425,16,16,316,404,426,427,428,429,430,409,410,431,16,16,16,16,17,17,432,433,434,102,435,436,437,106,438,439,17,17,440,441,442,114,443,444,17,17,445,446,447,122,448,449,13,126,450,451,129,452,17,17,453,132,17,17,18,18,205,454,18,18,455,208,456,457,458,139,459,460,18,18,461,462,463,145,464,465,18,18,466,467,468,151,469,470,8,154,471,472,473,227,474,475,18,18,19,19,476,477,478,479,480,481,482,483,19,19,484,485,486,487,488,489,19,19,490,491,492,493,494,495,496,497,19,19,19,19,20,498,499,500,501,502,503,504,20,20,505,477,506,507,508,509,510,483,20,20,511,512,513,514,515,489,20,20,516,517,518,519,520,495,496,521,20,20,20,20,20,20,522,500,523,524,525,526,21,21,527,346,528,529,530,531,532,533,534,352,21,21,535,536,537,538,539,357,21,21,540,541,542,543,544,362,21,21,545,546,547,548,13,549,550,551,21,21,22,22,552,101,553,304,554,555,556,557,22,22,558,309,559,560,561,562,22,22,563,313,564,565,566,567,22,22,568,318,569,570,571,572,573,574,11,575,22,22,23,23,576,577,578,579,580,306,581,582,23,23,583,584,585,311,586,587,23,23,588,589,590,315,591,592,23,23,593,594,595,320,596,597,598,599,23,23,11,600]
def read (i : Stored) : Val := fun v =>
  let p := data[i.val]!
  if p.1.testBit (num v) then some true else if p.2.testBit (num v) then some false else none
def oldId (i : Core) : Stored := ⟨i.val%601,Nat.mod_lt _ (by decide)⟩
def nextId (i : Core) (v : V) (b : Bool) : Stored :=
  ⟨moveIds[40*i.val+2*num v+(if b then 1 else 0)]!%601,Nat.mod_lt _ (by decide)⟩

local instance (s : Val) : Decidable (RowRule s) := by unfold RowRule; infer_instance
local instance (s : Val) : Decidable (ColumnRule s) := by unfold ColumnRule; infer_instance
local instance (s t : Val) : Decidable (Ext s t) := by unfold Ext; infer_instance

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rawOK : ∀ i : Stored, RowRule (read i) ∧ ColumnRule (read i) := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem movesOK : ∀ (i : Core) (v : V) (b : Bool), read (oldId i) v=none →
  Ext (read (oldId i)) (read (nextId i v b)) ∧ read (nextId i v b) v=some b := by decide +kernel

theorem coverRaw (i : Core) : Stable (Wave (PHP 5 4)) (read (oldId i)) := by
  apply safe_of_branches ((boardCriterion _).2 (rawOK _))
  intro v unknown b
  have h := movesOK i v b unknown
  exact ⟨_,h.1,h.2,(boardCriterion _).2 (rawOK _)⟩

def records : Array (Nat × Nat × Nat × Nat) := #[(19,0,0,0)]
def paired : Array (Nat × Nat) := #[(0,0),(1,2),(3,4),(0,0),(5,6),(0,0),(0,0),(7,8),(9,10),(9,11),(12,13),(14,8),(15,16),(15,11),(17,13),(18,8),(19,20),(21,13),(22,11),(23,11)]
def first (k : CaseKey) : C := Finset.univ.filter (fun l : L =>
  let e := records[k.val]!
  (if l.2 then e.1 else e.2.1).testBit (num l.1))
def anchor (k : CaseKey) : V :=
  let h := records[k.val]!.2.2.1
  (⟨(h/4)%5,Nat.mod_lt _ (by decide)⟩,⟨h%4,Nat.mod_lt _ (by decide)⟩)
def refId (k : CaseKey) : Core := ⟨records[k.val]!.2.2.2%24,Nat.mod_lt _ (by decide)⟩
def pairId (k : CaseKey) (v : V) (b : Bool) : Core :=
  let p := paired[20*k.val+num v]!
  ⟨(if b then p.2 else p.1)%24,Nat.mod_lt _ (by decide)⟩
def approved (k : CaseKey) (i : Core) : Prop := Safe (read (oldId i)) (first k) ∧ read (oldId i) (anchor k)≠none
local instance (k : CaseKey) (i : Core) : Decidable (approved k i) := by unfold approved Safe Holds; infer_instance
def goodPair (k : CaseKey) (v : V) : Prop :=
  let a := pairId k v false
  let b := pairId k v true
  approved k a ∧ approved k b ∧ (∀ x, read (oldId b) x=none → read (oldId a) x=none)
  ∧ read (oldId a) v=none ∧ read (oldId b) v≠none

set_option synthInstance.maxSize 4096 in
local instance (k : CaseKey) (v : V) : Decidable (goodPair k v) := by unfold goodPair; infer_instance
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem refs : ∀ k, approved k (refId k) := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem pairs : ∀ k v, read (oldId (refId k)) v=none → goodPair k v := by decide +kernel

theorem fourCases (k : CaseKey) (b : C) (sign : Bool) :
    ¬ IsRUPRun (Wave (PHP 5 4)) [∅,{(anchor k,sign)},b,first k] := by
  apply fourImpossible
  have belongs (i : Core) (h : approved k i) :
      read (oldId i) ∈ anchors (Wave (PHP 5 4)) (first k) (anchor k) :=
    ⟨coverRaw _,h.1,h.2⟩
  refine ⟨_,belongs _ (refs k),?_⟩
  intro v hv
  obtain ⟨a,c,small,free,assigned⟩ := pairs k v hv
  exact ⟨_,belongs _ a,_,belongs _ c,small,free,assigned⟩

end PEqualNP.Outside.L_meta_9248.Waves
