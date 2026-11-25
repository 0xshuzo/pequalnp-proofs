import PEqualNP.Defs
namespace PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev Cl := Clause V
abbrev Row := Fin 60
def fullMask : Nat := 1152921504606846975
def rows : Array Nat := #[672,784,1120,1288,2128,2184,644,770,1092,1281,2114,2177,532,546,1036,1057,2058,2065,84,98,140,161,266,273,1289,2185,1121,2129,1100,2122,673,785,652,778,596,610,786,2130,674,2186,660,2193,1122,1290,1108,1297,1164,1185,676,1124,788,1292,802,1313,2132,2188,2146,2209,2314,2321]
def ones : Array Nat := #[729761264001255936,364805838240031872,58354402365559104,326590701323239464,595657351441551378,230673451842052101,90657122719368468,180640694878079073,881623687009141386,5912485265682627,12099026304418572,1134909993020230704]
def zeros : Array Nat := #[423160240605591039,788115666366815103,1094567102241287871,826330803283607511,557264153165295597,922248052764794874,1062264381887478507,972280809728767902,271297817597705589,1147009019341164348,1140822478302428403,18011511586616271]
def labelMasks : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,13194139533312,52776558133248,211106232532992,844424930131968,3377699720527872,13510798882111488,54043195528445952,216172782113783808,864691128455135232]
def lits : List (Literal V) := [((0,0),false),((0,0),true),((0,1),false),((0,1),true),((0,2),false),((0,2),true),((1,0),false),((1,0),true),((1,1),false),((1,1),true),((1,2),false),((1,2),true),((2,0),false),((2,0),true),((2,1),false),((2,1),true),((2,2),false),((2,2),true),((3,0),false),((3,0),true),((3,1),false),((3,1),true),((3,2),false),((3,2),true)]

def port (v : V) : Nat := 3 * v.1.val + v.2.val

def assignment (r : Row) (v : V) : Bool := (rows[r.val]!).testBit (port v)

def keep (l : Literal V) : Nat := if l.2 then zeros[port l.1]! else ones[port l.1]!

def cut (C : Cl) (s : Nat) (l : Literal V) : Nat := if l ∈ C then s &&& keep l else s

def privateMask (C : Cl) : Nat := lits.foldl (cut C) fullMask

theorem fullBit (r : Row) : fullMask.testBit r.val = true := by
  revert r; decide +kernel

theorem keepBit (l : Literal V) (r : Row) :
    (keep l).testBit r.val = true ↔ assignment r l.1 ≠ l.2 := by
  revert l r; decide +kernel

theorem listed (l : Literal V) : l ∈ lits := by
  revert l; decide +kernel

theorem cutList (C : Cl) (s : Nat) (ls : List (Literal V)) (r : Row) :
    (ls.foldl (cut C) s).testBit r.val = true ↔
      s.testBit r.val = true ∧ (∀ l ∈ ls, l ∈ C → assignment r l.1 ≠ l.2) := by
  induction ls generalizing s with
  | nil => simp
  | cons l t ih =>
    rw [List.foldl_cons, ih]
    by_cases h : l ∈ C
    · simp only [cut, if_pos h, Nat.testBit_and, Bool.and_eq_true, keepBit,
        List.mem_cons]
      aesop
    · simp only [cut, if_neg h, List.mem_cons]
      aesop

theorem privateBit (C : Cl) (r : Row) :
    (privateMask C).testBit r.val = true ↔ ¬ClauseSat (assignment r) C := by
  rw [privateMask,cutList]
  simp only [fullBit, true_and]
  constructor
  · rintro h ⟨l,hl,yes⟩
    exact h l (listed l) hl yes
  · intro h l _ hl yes
    exact h ⟨l,hl,yes⟩

def posAx (i : Fin 4) : Cl := Finset.univ.image (fun j : Fin 3 => ((i,j),true))
def negAx (i j : Fin 4) (h : Fin 3) : Cl := {((i,h),false),((j,h),false)}

theorem posListed (i : Fin 4) : privateMask (posAx i) ∈ labelMasks.toList := by
  revert i; decide +kernel

theorem negListed (i j : Fin 4) (h : Fin 3) (ne : i ≠ j) :
    privateMask (negAx i j h) ∈ labelMasks.toList := by
  revert i j h; decide +kernel

theorem axListed {C : Cl} (hc : C ∈ PHP 4 3) : privateMask C ∈ labelMasks.toList := by
  rcases hc with ⟨i,rfl⟩ | ⟨i,j,h,ne,rfl⟩
  · exact posListed i
  · exact negListed i j h ne

def labels : Array Nat := #[0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,20,20,21,21]
def negA : Array Nat := #[0,0,0,0,1,2,2,3,3,3,1,2,2,3,3,3,1,2,2,3,3,3]
def negB : Array Nat := #[0,0,0,0,0,0,1,0,1,2,0,0,1,0,1,2,0,0,1,0,1,2]
def negH : Array Nat := #[0,1,2,3,0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2]
def neighborData : Array Nat := #[199070,207135,203418,211672,223579,227801,52219084800,56447205376,53358886912,57669582848,60757901312,61897703424,14252007158185984,14806229738061824,14559458097102848,15126668658081792,16499065327976448,16789198958755840,4035837755673286803456,4181123879652259004416,4111894546180319739904,4260585391477584035840,4329814724949523300352,4405871515456556236800,2359299,2883589,1030792151042,1168231104516,962074771456,1099514249216,378302368699121664,414331165718085633,360287970191212544,396316767210438656,324259997804396544,342274465033355264,117440576,167772416,57174604644352,70368744177984,52776658796544,74766975238144,21905508587530092672,25364273101350633664,20752587083057463296,26517194606108475392,23058491664788094976,24211417567441453056,6442450944,8589942784,3377699720531968,3940649673961472,3659182213431296,4222134314336256,1328165573307087732736,1475739525896764149760,1401952549612663341056,1549526502203413495808,1623317982086067912704,1697105239855882829824]

abbrev Label := Fin 22

def labelOf (r : Row) : Label := Fin.ofNat 22 labels[r.val]!

def axiomAt (b : Label) : Cl :=
  if b.val < 4 then posAx (Fin.ofNat 4 b.val)
  else negAx (Fin.ofNat 4 (negA[b.val]!)) (Fin.ofNat 4 (negB[b.val]!)) (Fin.ofNat 3 (negH[b.val]!))

def otherRow (r : Row) (v : V) : Row :=
  Fin.ofNat 60 ((neighborData[r.val]! >>> (6*port v)) % 64)

theorem posAxNamed : ∀ i : Fin 4, ∃ a : Label, axiomAt a = posAx i := by decide +kernel
theorem negAxNamed : ∀ i j : Fin 4, ∀ h : Fin 3, i ≠ j → ∃ a : Label, axiomAt a = negAx i j h := by decide +kernel

theorem axNamed {C : Cl} (ax : C ∈ PHP 4 3) : ∃ a : Label, axiomAt a = C := by
  rcases ax with ⟨i,rfl⟩ | ⟨i,j,h,ne,rfl⟩
  · exact posAxNamed i
  · exact negAxNamed i j h ne

theorem privateByName : ∀ r : Row, ∀ b : Label,
    (privateMask (axiomAt b)).testBit r.val = decide (labelOf r = b) := by decide +kernel

theorem axiomFlag (r : Row) (b : Label) :
    ¬ClauseSat (assignment r) (axiomAt b) ↔ labelOf r = b := by
  rw [← privateBit,privateByName,decide_eq_true_eq]

theorem everyLabel : ∀ b : Label, ∃ r : Row, labelOf r = b := by decide +kernel

theorem nameUnique {a b : Label} (eq : axiomAt a = axiomAt b) : a = b := by
  obtain ⟨r,h⟩ := everyLabel a
  have yes := (axiomFlag r a).2 h
  rw [eq,axiomFlag] at yes
  exact h.symm.trans yes

theorem neighborVar : ∀ r : Row, ∀ v : V, ∀ bit : Bool,
    (v,bit) ∈ axiomAt (labelOf r) →
    assignment (otherRow r v) v = bit ∧
    (∀ q : V, q ≠ v → assignment (otherRow r v) q = assignment r q) ∧
    labelOf (otherRow r v) ≠ labelOf r := by decide +kernel

def Taut (C : Cl) : Prop := ∃ v : V, (v,true) ∈ C ∧ (v,false) ∈ C

theorem falseAtFlip (a b : V → Bool) {D : Cl} {v : V} {t : Bool}
    (pivot : (v,t) ∈ D) (clean : ¬Taut D) (changed : b v ≠ t)
    (fixed : ∀ q ≠ v, b q = a q) (prior : ¬ClauseSat a (D.erase (v,t))) :
    ¬ClauseSat b D := by
  rintro ⟨⟨q,z⟩,m,hit⟩
  change b q = z at hit
  by_cases eq : q = v
  · subst q
    cases t <;> cases z
    · exact changed hit
    · exact clean ⟨v,m,pivot⟩
    · exact clean ⟨v,pivot,m⟩
    · exact changed hit
  · have mem : (q,z) ∈ D.erase (v,t) := Finset.mem_erase.mpr ⟨by simp [eq],m⟩
    exact prior ⟨(q,z),mem,(fixed q eq).symm.trans hit⟩

abbrev IndexedClause := Clause (Fin 4 × Fin 3)

/-- Parents are physical lines, identified by their position in the newest-first list. -/
inductive LineReason (F : Set IndexedClause) (rows : List IndexedClause)
    (k : Nat) (R : IndexedClause) : Type where
  | ax (member : R ∈ F)
  | res (i j : Nat) (C D : IndexedClause)
      (earlierLeft : k < i) (earlierRight : k < j)
      (leftLine : rows[i]? = some C) (rightLine : rows[j]? = some D)
      (resolve : IsResolvent C D R)

private theorem address {rows : List IndexedClause} {C : IndexedClause}
    (h : C ∈ rows) : ∃ i : Nat, rows[i]? = some C := by
  induction rows with
  | nil => simp at h
  | cons r rows ih =>
    rcases List.mem_cons.mp h with eq | tail
    · subst r
      exact ⟨0, rfl⟩
    · obtain ⟨i, hi⟩ := ih tail
      exact ⟨i+1, by simpa using hi⟩

private def shiftReason {F rows k R} (x : LineReason F rows k R) (newest : IndexedClause) :
    LineReason F (newest :: rows) (k+1) R := by
  cases x with
  | ax h => exact .ax h
  | res i j C D hi hj hC hD step =>
    exact .res (i+1) (j+1) C D (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj)
      (by simpa using hC) (by simpa using hD) step

private theorem extendReasons {F rows R}
    (front : Nonempty (LineReason F (R :: rows) 0 R))
    (old : ∀ k C, rows[k]? = some C → Nonempty (LineReason F rows k C)) :
    ∀ k C, (R :: rows)[k]? = some C → Nonempty (LineReason F (R :: rows) k C) := by
  intro k C h
  cases k with
  | zero =>
    have eq : R = C := Option.some.inj h
    subst C
    exact front
  | succ k =>
    obtain ⟨reason⟩ := old k C (by simpa using h)
    exact ⟨shiftReason reason R⟩

theorem indexedDerivation {F : Set IndexedClause} {rows : List IndexedClause}
    (h : IsDerivation F rows) :
    ∀ k C, rows[k]? = some C → Nonempty (LineReason F rows k C) := by
  induction h with
  | nil => simp
  | ax _ mem ih => exact extendReasons ⟨.ax mem⟩ ih
  | res _ left right step ih =>
    obtain ⟨i, hi⟩ := address left
    obtain ⟨j, hj⟩ := address right
    exact extendReasons ⟨.res (i+1) (j+1) _ _ (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      (by simpa using hi) (by simpa using hj) step⟩ ih

theorem indexedRefutation {F : Set IndexedClause} {rows : List IndexedClause}
    (h : IsRefutation F rows) :
    ∃ root : Nat, rows[root]? = some ∅ ∧
      Nonempty ((i : Fin rows.length) → LineReason F rows i.val rows[i.val]) := by
  obtain ⟨root, hr⟩ := address h.2
  refine ⟨root, hr, ⟨fun i => Classical.choice (indexedDerivation h.1 i.val rows[i.val] ?_)⟩⟩
  simp [i.isLt]


def linksOf {F rows k C} (r : LineReason F rows k C) : Option (Fin rows.length × Fin rows.length) :=
  match r with
  | .ax _ => none
  | .res i j _ _ _ _ hi hj _ =>
    some (⟨i,(List.getElem?_eq_some_iff.mp hi).1⟩,⟨j,(List.getElem?_eq_some_iff.mp hj).1⟩)

structure Links {n : Nat} (atLine : Fin n → Cl) where
  parent : Fin n → Option (Fin n × Fin n)
  ax : ∀ i, parent i = none → atLine i ∈ PHP 4 3
  rule : ∀ i j k, parent i = some (j,k) →
    i.val < j.val ∧ i.val < k.val ∧ IsResolvent (atLine j) (atLine k) (atLine i)

theorem flatAx {rows : List Cl} {i : Fin rows.length}
    (r : LineReason (PHP 4 3) rows i.val rows[i.val]) (h : linksOf r = none) :
    rows[i.val] ∈ PHP 4 3 := by
  cases r with
  | ax mem => exact mem
  | res => simp [linksOf] at h

theorem flatRes {rows : List Cl} {i j k : Fin rows.length}
    (r : LineReason (PHP 4 3) rows i.val rows[i.val]) (h : linksOf r = some (j,k)) :
    i.val < j.val ∧ i.val < k.val ∧ IsResolvent rows[j.val] rows[k.val] rows[i.val] := by
  cases r with
  | ax => simp [linksOf] at h
  | res u v C D hu hv hC hD rr =>
    change some (_,_) = some (j,k) at h
    obtain rfl := Option.some.inj h
    simpa [(List.getElem?_eq_some_iff.mp hC).2,(List.getElem?_eq_some_iff.mp hD).2] using
      (show i.val < u ∧ i.val < v ∧ IsResolvent C D rows[i.val] from ⟨hu,hv,rr⟩)

def asLinks {rows : List Cl}
    (reas : (i : Fin rows.length) → LineReason (PHP 4 3) rows i.val rows[i.val]) :
    Links (fun i : Fin rows.length => rows[i.val]) where
  parent i := linksOf (reas i)
  ax i := flatAx (reas i)
  rule i j k := flatRes (reas i)

def ReadAt {n : Nat} {C : Fin n → Cl} (g : Links C) (b : Label) (i : Fin n) : Prop :=
  ∃ j k, g.parent i = some (j,k) ∧
    ((g.parent j = none ∧ C j = axiomAt b) ∨ (g.parent k = none ∧ C k = axiomAt b))

theorem badParent (a : V → Bool) {C D R : Cl} (h : IsResolvent C D R) (bad : ¬ClauseSat a R) :
    ¬ClauseSat a C ∨ ¬ClauseSat a D := by
  classical
  by_contra! both
  obtain ⟨v,_,_,rfl⟩ := h
  obtain ⟨l,ml,el⟩ := both.1
  obtain ⟨t,mt,et⟩ := both.2
  by_cases left : l = (v,true)
  · have right : t ≠ (v,false) := by
      intro he; subst t; subst l
      change a v = true at el
      change a v = false at et
      simp [el] at et
    exact bad ⟨t,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨right,mt⟩),et⟩
  · exact bad ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨left,ml⟩),el⟩

theorem firstRead {n : Nat} {C : Fin n → Cl} (g : Links C) (r : Row)
    (i : Fin n) (notAx : g.parent i ≠ none) (bad : ¬ClauseSat (assignment r) (C i)) :
    ∃ u, ReadAt g (labelOf r) u ∧ ¬ClauseSat (assignment r) (C u) := by
  classical
  have aux (m : Nat) : ∀ i : Fin n, n-i.val = m → g.parent i ≠ none →
      ¬ClauseSat (assignment r) (C i) →
      ∃ u, ReadAt g (labelOf r) u ∧ ¬ClauseSat (assignment r) (C u) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i eq notAx bad
      cases link : g.parent i with
      | none => exact False.elim (notAx link)
      | some jk =>
        obtain ⟨j,k⟩ := jk
        obtain ⟨hj,hk,step⟩ := g.rule i j k link
        have follow (u : Fin n) (old : i.val < u.val) (endpoint : u = j ∨ u = k)
            (wrong : ¬ClauseSat (assignment r) (C u)) :
            ∃ v, ReadAt g (labelOf r) v ∧ ¬ClauseSat (assignment r) (C v) := by
          by_cases raw : g.parent u = none
          · obtain ⟨b,name⟩ := axNamed (g.ax u raw)
            have lab : labelOf r = b := (axiomFlag r b).1 (by simpa [name] using wrong)
            have nm : C u = axiomAt (labelOf r) := by rw [lab,name]
            refine ⟨i,⟨j,k,link,?_⟩,bad⟩
            rcases endpoint with rfl | rfl
            · exact Or.inl ⟨raw,nm⟩
            · exact Or.inr ⟨raw,nm⟩
          · exact ih (n-u.val) (by have := i.isLt; have := u.isLt; omega) u rfl raw wrong
        rcases badParent (assignment r) step bad with jl | kr
        · exact follow j hj (Or.inl rfl) jl
        · exact follow k hk (Or.inr rfl) kr
  exact aux _ i rfl notAx bad

theorem rootNotAx {n : Nat} {C : Fin n → Cl} (g : Links C) (i : Fin n) (emp : C i = ∅) :
    g.parent i ≠ none := by
  intro raw
  obtain ⟨b,nm⟩ := axNamed (g.ax i raw)
  have nonempty : ∀ a : Label, axiomAt a ≠ ∅ := by decide +kernel
  exact nonempty b (nm.trans emp)

theorem privateCoverage {n : Nat} {C : Fin n → Cl} (g : Links C) (i : Fin n) (emp : C i = ∅)
    (r : Row) : ∃ u, ReadAt g (labelOf r) u ∧ ¬ClauseSat (assignment r) (C u) := by
  apply firstRead g r i (rootNotAx g i emp)
  simp [emp,ClauseSat]

theorem uniqueReadFails {n : Nat} {C : Fin n → Cl} (g : Links C) (i : Fin n) (emp : C i = ∅)
    (b : Label) (u : Fin n) (sole : ∀ j, ReadAt g b j → j = u)
    (r : Row) (lab : labelOf r = b) : ¬ClauseSat (assignment r) (C u) := by
  obtain ⟨j,read,bad⟩ := privateCoverage g i emp r
  rw [lab] at read
  exact sole j read ▸ bad
end PCX150
