import PEqualNP.Defs
set_option linter.concreteInstances false
set_option linter.unusedSectionVars false
namespace PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev Cl := Clause V
inductive ResTree (F : Set Cl) : Cl → Nat → Prop where
  | ax {C : Cl} : C ∈ F → ResTree F C 0
  | res {C D R : Cl} {i j : Nat} : ResTree F C i → ResTree F D j →
      IsResolvent C D R → ResTree F R (i+j+1)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
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


section AbstractTest
variable {Sample Key : Type} (assignment : Sample → V → Bool)
    (inside : Key → Sample → Prop)

def FailsOn (s : Key) (C : Cl) : Prop :=
  ∀ x, inside s x → ¬ClauseSat (assignment x) C

theorem treePotential {F : Set Cl} (weight : Key → Nat)
    (leaf : ∀ C ∈ F, ∀ s, FailsOn assignment inside s C → weight s ≤ 1)
    (branch : ∀ s, 1 < weight s → ∀ v : V, ∃ lo hi : Key,
      (∀ x, inside lo x → inside s x ∧ assignment x v = false) ∧
      (∀ x, inside hi x → inside s x ∧ assignment x v = true) ∧
      weight s ≤ weight lo + weight hi)
    {C : Cl} {n : Nat} (tree : ResTree F C n) :
    ∀ s, FailsOn assignment inside s C → weight s ≤ n+1 := by
  induction tree with
  | ax h =>
    intro s hs
    exact leaf _ h s hs
  | @res C D R i j _ _ hr ihC ihD =>
    intro s hs
    by_cases small : weight s ≤ 1
    · omega
    obtain ⟨v,hC,hD,rfl⟩ := hr
    obtain ⟨lo,hi,hlo,hhi,hw⟩ := branch s (by omega) v
    have left : FailsOn assignment inside lo C := by
      intro x hx sat
      obtain ⟨mx, val⟩ := hlo x hx
      obtain ⟨l, hl, yes⟩ := sat
      have ne : l ≠ (v, true) := by
        rintro rfl
        change assignment x v = true at yes
        simp [val] at yes
      exact hs x mx ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    have right : FailsOn assignment inside hi D := by
      intro x hx sat
      obtain ⟨mx, val⟩ := hhi x hx
      obtain ⟨l, hl, yes⟩ := sat
      have ne : l ≠ (v, false) := by
        rintro rfl
        change assignment x v = false at yes
        simp [val] at yes
      exact hs x mx ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    have h₀ := ihC lo left
    have h₁ := ihD hi right
    omega


end AbstractTest
abbrev KeyID := Fin 3306
def stateMask (i : KeyID) : Nat := (if i.val = 3305 then fullMask else 0) % 2^60
def rawCost (i : KeyID) : Nat := if i.val = 3305 then 43 else 0
opaque child (_ : KeyID) (_ : V) (_ : Bool) : KeyID := 0
def live (i : KeyID) (r : Row) : Prop := (stateMask i).testBit r.val = true

def geometry (i : KeyID) : Prop :=
  1 < rawCost i →
    (labelMasks.toList.all (fun a => decide (stateMask i &&& a ≠ stateMask i))) = true ∧
    ∀ v : V,
      stateMask (child i v false) = stateMask i &&& keep (v,true) ∧
      stateMask (child i v true) = stateMask i &&& keep (v,false) ∧
      rawCost i ≤ rawCost (child i v false) + rawCost (child i v true)

instance (i : KeyID) : Decidable (geometry i) := by
  unfold geometry
  infer_instance

class GeometryWitness : Prop where
  fact : ∀ i : KeyID, geometry i
variable [inputGeometry : GeometryWitness]
include inputGeometry
theorem geometryOK : ∀ i : KeyID, geometry i := GeometryWitness.fact

theorem subsetOfTests (a b : Nat) (small : a < 2^60)
    (h : ∀ r : Row, a.testBit r.val = true → b.testBit r.val = true) :
    a &&& b = a := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  by_cases hk : k < 60
  · cases ha : a.testBit k with
    | false => simp
    | true => simp [h ⟨k,hk⟩ ha]
  · have ha := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 60 ≤ k)))
    simp [ha]

theorem rawLeaf (C : Cl) (hc : C ∈ PHP 4 3) (i : KeyID)
    (h : FailsOn assignment live i C) : rawCost i ≤ 1 := by
  by_contra! large
  have ax := axListed hc
  have notsub := List.all_eq_true.mp ((geometryOK i large).1) _ ax
  have eq := subsetOfTests (stateMask i) (privateMask C)
    (Nat.mod_lt _ (by decide)) (fun r hr => (privateBit C r).2 (h r hr))
  exact (of_decide_eq_true notsub) eq

theorem geomBranch (i : KeyID) (w : 1 < rawCost i) (v : V) :
    (∀ x, live (child i v false) x → live i x ∧ assignment x v = false) ∧
    (∀ x, live (child i v true) x → live i x ∧ assignment x v = true) ∧
    rawCost i ≤ rawCost (child i v false) + rawCost (child i v true) := by
  obtain ⟨lo,hi,sc⟩ := (geometryOK i w).2 v
  refine ⟨?_,?_,sc⟩
  · intro x hx
    change (stateMask (child i v false)).testBit x.val = true at hx
    rw [lo,Nat.testBit_and,Bool.and_eq_true] at hx
    obtain ⟨a,b⟩ := hx
    have hb := (keepBit (v,true) x).1 b
    exact ⟨a,by simpa using hb⟩
  · intro x hx
    change (stateMask (child i v true)).testBit x.val = true at hx
    rw [hi,Nat.testBit_and,Bool.and_eq_true] at hx
    obtain ⟨a,b⟩ := hx
    have hb := (keepBit (v,false) x).1 b
    exact ⟨a,by simpa using hb⟩

theorem rawTree {C : Cl} {n : Nat} (tree : ResTree (PHP 4 3) C n)
    (i : KeyID) (h : FailsOn assignment live i C) : rawCost i ≤ n+1 := by
  exact treePotential assignment live rawCost rawLeaf
    (fun s hs v => ⟨_,_,geomBranch s hs v⟩) tree i h

theorem base42 {n : Nat} (tree : ResTree (PHP 4 3) ∅ n) : 42 ≤ n := by
  have h := rawTree tree (3305 : KeyID)
    (by intro x _ hx; simpa [ClauseSat] using hx)
  have nr : rawCost (3305 : KeyID) = 43 := by decide +kernel
  omega

def Supported (m : Nat) : Prop :=
  (∃ i : KeyID, 1 < rawCost i ∧ m = stateMask i) ∨
    (∃ a ∈ labelMasks.toList, m &&& a = m)

def terminalCheck (i : KeyID) : Prop :=
  rawCost i ≤ 1 → labelMasks.toList.any (fun a => stateMask i &&& a == stateMask i) = true

instance (i : KeyID) : Decidable (terminalCheck i) := by unfold terminalCheck; infer_instance

class TerminalWitness : Prop where
  fact : ∀ i : KeyID, terminalCheck i
variable [inputTerminal : TerminalWitness]
include inputTerminal
theorem terminalOK : ∀ i : KeyID, terminalCheck i := TerminalWitness.fact

theorem knownSupported (i : KeyID) : Supported (stateMask i) := by
  by_cases large : 1 < rawCost i
  · exact Or.inl ⟨i,large,rfl⟩
  · obtain ⟨a,ha,ok⟩ := List.any_eq_true.mp (terminalOK i (by omega))
    exact Or.inr ⟨a,ha,eq_of_beq ok⟩

theorem cutSupported {m : Nat} (supp : Supported m) (l : Literal V) :
    Supported (m &&& keep l) := by
  rcases supp with ⟨i,large,rfl⟩ | ⟨a,ha,eq⟩
  · obtain ⟨v,b⟩ := l
    obtain ⟨lo,hi,_⟩ := (geometryOK i large).2 v
    cases b
    · rw [← hi]; exact knownSupported _
    · rw [← lo]; exact knownSupported _
  · right
    refine ⟨a,ha,?_⟩
    calc
      (m &&& keep l) &&& a = (m &&& a) &&& keep l := by ac_rfl
      _ = m &&& keep l := by rw [eq]

theorem privateSupported (C : Cl) : Supported (privateMask C) := by
  have h0 : stateMask (3305 : KeyID) = fullMask := by decide +kernel
  have start : Supported fullMask := h0 ▸ knownSupported (3305 : KeyID)
  have loop (ls : List (Literal V)) (m : Nat) (h : Supported m) :
      Supported (ls.foldl (cut C) m) := by
    induction ls generalizing m with
    | nil => exact h
    | cons l ls ih =>
      apply ih
      by_cases present : l ∈ C
      · simpa [cut,present] using cutSupported h l
      · simpa [cut,present] using h
  exact loop lits fullMask start
def convolve (ps : List Nat) (L R : Nat → Nat) (k : Nat) : Nat :=
  ps.foldr (fun p z => (L p &&& R (k-p)) ||| z) 0

theorem convolve_bit (ps : List Nat) (L R : Nat → Nat) (k t : Nat) :
    (convolve ps L R k).testBit t = true ↔
    ∃ p ∈ ps, (L p).testBit t = true ∧ (R (k-p)).testBit t = true := by
  induction ps with
  | nil => simp [convolve]
  | cons p ps ih =>
    change (((L p &&& R (k-p)) ||| convolve ps L R k).testBit t = true) ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_and, Bool.and_eq_true, ih]
    simp only [List.mem_cons]
    aesop

theorem testBit_subset {a b t : Nat} (h : a &&& b = a) (hit : a.testBit t = true) :
    b.testBit t = true := by
  have hh := congrArg (fun n : Nat => n.testBit t) h
  simpa [Nat.testBit_and,hit] using hh

theorem treeThreshold {Sample Key : Type} (assignment : Sample → V → Bool)
    (inside : Key → Sample → Prop) {F : Set Cl} (test : Key → Nat → Prop)
    (leaf : ∀ C ∈ F, ∀ s k, test s k →
      (∀ x, inside s x → ¬ClauseSat (assignment x) C) → k ≤ 1)
    (branch : ∀ s k, 1 < k → test s k → ∀ v : V,
      ∃ lo hi : Key, ∃ p ≤ k,
      (∀ x, inside lo x → inside s x ∧ assignment x v = false) ∧
      (∀ x, inside hi x → inside s x ∧ assignment x v = true) ∧
      test lo p ∧ test hi (k-p))
    {C : Cl} {n : Nat} (tree : ResTree F C n) :
    ∀ s k, test s k → (∀ x, inside s x → ¬ClauseSat (assignment x) C) → k ≤ n+1 := by
  induction tree with
  | ax h =>
    intro s k hit hs
    exact leaf _ h s k hit hs
  | @res C D R i j _ _ hr ihC ihD =>
    intro s k hit hs
    by_cases small : k ≤ 1
    · omega
    obtain ⟨v,_,_,rfl⟩ := hr
    obtain ⟨lo,hi,p,hp,hlo,hhi,hpL,hpR⟩ := branch s k (by omega) hit v
    have left : ∀ x, inside lo x → ¬ClauseSat (assignment x) C := by
      intro x hx sat
      obtain ⟨mx, val⟩ := hlo x hx
      obtain ⟨l, hl, yes⟩ := sat
      have ne : l ≠ (v, true) := by
        rintro rfl
        change assignment x v = true at yes
        simp [val] at yes
      exact hs x mx ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    have right : ∀ x, inside hi x → ¬ClauseSat (assignment x) D := by
      intro x hx sat
      obtain ⟨mx, val⟩ := hhi x hx
      obtain ⟨l, hl, yes⟩ := sat
      have ne : l ≠ (v, false) := by
        rintro rfl
        change assignment x v = false at yes
        simp [val] at yes
      exact hs x mx ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    have h₀ := ihC lo p hpL left
    have h₁ := ihD hi (k-p) hpR right
    omega

def Cont (m a : Nat) := m &&& a = m

theorem contRefl (m : Nat) : Cont m m := by simp [Cont]

theorem contTrans {s m a : Nat} (sm : Cont s m) (ma : Cont m a) : Cont s a := by
  unfold Cont at *
  calc
    s &&& a = (s &&& m) &&& a := by rw [sm]
    _ = s &&& (m &&& a) := Nat.and_assoc .. 
    _ = s := by rw [ma,sm]

def Basal (C : Cl) := ∃ a ∈ labelMasks.toList, Cont (privateMask C) a

def Fits (C : Cl) (i : KeyID) : Prop :=
  privateMask C = stateMask i ∨ (i = 0 ∧ Basal C)

theorem anyFits (C : Cl) : ∃ i : KeyID, Fits C i := by
  rcases privateSupported C with ⟨i,_,eq⟩ | hl
  · exact ⟨i,Or.inl eq⟩
  · exact ⟨0,Or.inr ⟨rfl,hl⟩⟩

theorem isBasalOfAx {C : Cl} (h : C ∈ PHP 4 3) : Basal C :=
  ⟨privateMask C, axListed h, contRefl _⟩

theorem containsOfFails {s : KeyID} {C : Cl}
    (h : FailsOn assignment live s C) : Cont (stateMask s) (privateMask C) :=
  subsetOfTests (stateMask s) (privateMask C) (Nat.mod_lt _ (by decide))
    (fun r hr => (privateBit C r).2 (h r hr))

theorem rawSmall {i : KeyID} {a : Nat} (ha : a ∈ labelMasks.toList)
    (h : Cont (stateMask i) a) : rawCost i ≤ 1 := by
  by_contra! big
  have ex := List.all_eq_true.mp ((geometryOK i big).1) a ha
  exact (of_decide_eq_true ex) h

theorem failsId {C : Cl} {s : KeyID} (h : privateMask C = stateMask s) :
    FailsOn assignment live s C := by
  intro r hr
  apply (privateBit C r).1
  simpa [live,h] using hr

theorem chargeRaw {A : Cl} {i : Nat} {s : KeyID} (fit : Fits A s)
    (tree : ResTree (PHP 4 3) A i) : rawCost s ≤ i+1 := by
  rcases fit with eq | ⟨rfl,_⟩
  · exact rawTree tree s (failsId eq)
  · have z : rawCost (0 : KeyID) = 0 := by decide +kernel
    omega

def permV (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3)) (v : V) : V :=
  (p v.1,h v.2)

def permLit (f : V → V) (l : Literal V) : Literal V := (f l.1,l.2)

def permCl (f : V → V) (C : Cl) : Cl := C.image (permLit f)

theorem permLitInj {f : V → V} (hf : Function.Injective f) :
    Function.Injective (permLit f) := by
  rintro ⟨u,b⟩ ⟨v,c⟩ he
  have h1 : f u = f v := congrArg Prod.fst he
  have h2 : b = c := congrArg Prod.snd he
  exact Prod.ext (hf h1) h2

theorem permErase {f : V → V} (hf : Function.Injective f) (C : Cl) (l : Literal V) :
    permCl f (C.erase l) = (permCl f C).erase (permLit f l) := by
  ext t
  simp only [permCl,Finset.mem_image,Finset.mem_erase]
  constructor
  · rintro ⟨x,⟨ne,m⟩,rfl⟩
    exact ⟨fun eq => ne (permLitInj hf eq),x,m,rfl⟩
  · rintro ⟨ne,x,m,rfl⟩
    exact ⟨x,⟨fun e => ne (congrArg (permLit f) e),m⟩,rfl⟩

theorem permRes {f : V → V} (hf : Function.Injective f) {C D R : Cl}
    (hr : IsResolvent C D R) : IsResolvent (permCl f C) (permCl f D) (permCl f R) := by
  obtain ⟨v,pc,pd,rfl⟩ := hr
  refine ⟨f v,Finset.mem_image_of_mem _ pc,Finset.mem_image_of_mem _ pd,?_⟩
  change Finset.image _ (_ ∪ _) = _
  rw [Finset.image_union]
  change permCl f (C.erase (v,true)) ∪ permCl f (D.erase (v,false)) = _
  rw [permErase hf,permErase hf]
  rfl

theorem permTree {f : V → V} (hf : Function.Injective f) {F G : Set Cl}
    (hleaf : ∀ C ∈ F, permCl f C ∈ G) {C : Cl} {n : Nat} (tree : ResTree F C n) :
    ResTree G (permCl f C) n := by
  induction tree with
  | ax h => exact .ax (hleaf _ h)
  | res _ _ hr ihC ihD => exact .res ihC ihD (permRes hf hr)

theorem permVInj (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3)) :
    Function.Injective (permV p h) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ eq
  exact Prod.ext (p.injective (congrArg Prod.fst eq)) (h.injective (congrArg Prod.snd eq))

theorem phpRename (p : Equiv.Perm (Fin 4)) (h : Equiv.Perm (Fin 3))
    (C : Cl) (hc : C ∈ PHP 4 3) : permCl (permV p h) C ∈ PHP 4 3 := by
  rcases hc with ⟨i,rfl⟩ | ⟨i,j,k,ne,rfl⟩
  · left
    refine ⟨p i,?_⟩
    ext t
    simp only [permCl, Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,⟨k,rfl⟩,rfl⟩
      exact ⟨h k,rfl⟩
    · rintro ⟨k,rfl⟩
      exact ⟨((i,h.symm k),true),⟨_,rfl⟩,by simp [permLit,permV]⟩
  · right
    refine ⟨p i,p j,h k,fun eq => ne (p.injective eq),?_⟩
    simp [permCl,permLit,permV]

theorem permSat (f : V → V) (a : V → Bool) (C : Cl) :
    ClauseSat a (permCl f C) ↔ ClauseSat (fun v => a (f v)) C := by
  constructor
  · rintro ⟨l,hl,yes⟩
    obtain ⟨x,m,rfl⟩ := Finset.mem_image.mp hl
    exact ⟨x,m,yes⟩
  · rintro ⟨x,m,yes⟩
    exact ⟨_,Finset.mem_image_of_mem _ m,yes⟩
def pigeonCode : Array Nat := #[228,180,216,120,156,108,225,177,201,57,141,45,210,114,198,54,78,30,147,99,135,39,75,27]
def pigeonBack : Array Nat := #[228,180,216,156,120,108,225,177,210,147,114,99,201,141,198,135,78,75,57,45,54,39,30,27]
def holeCode : Array Nat := #[36,24,33,9,18,6]
def holeBack : Array Nat := #[36,24,33,18,9,6]
def rowCode : Array Nat := #[2198837046507322820568735172000296395497111703639031655214989481031415655662858396551046983622524691475603520,1751495602169449824780452133844769261384469437309448667367654039628175301793608141872959730519764771391422465,2162705622156956155524194547248590888843364879373837413591619490913386944305282635826338639645551936198148290,1715364177819083159735809129730843131986073819471931100523090420239297245396045951445411734776632419853275460,1304154157831576828992066716327021504527178377407542354299124968954085602884371457492032825650845255046549635,1268022733481210163947526091575315997873431553142348112675754978836056891526795696767324481673872499769094405,2198800641771726253250707320465942554279185016594663310005348741055887738735616140179568159580534921302900994,1751459197433853257462424282310415420166542750265080322158013302462541279881224401334981705059951840900944004,2162669217421359588268829423501870164537016355595968494234636225938324839775538840543397839612222205546471744,1715327773083486592480444005984122407679738565042812419371631092935723283340774336944491482312232462352662721,1304117753095980261674038864792667663309264959711924247295008169459939723446459897736075347759962097707134981,1267986328745613596692160967828595273567096298713229431524295654342376824486382598099905027791649381950705731,2124316537260600494142276225985762821656081576118724669733229319233394180619356984075646928639684086222827521,1676975092922727498353993187830235687543439309789141874980332026933548879362571463694417987818059670813167680,2088185117216383693514290327342421074640151814892582745180871313328258436370956336279045191942337167630536835,1640843672878510697725904909825585180485604620029637053619285659928883381981406549648261505397249836046352645,1229633648584854502565607770313399793388892114926196183418746373534173824973021677063634301272972339228983490,1193502228540637701937621871670058046372962353700054258866388367629038080724621029267032564575625420636692804,1975239118337709010085950063352810578613197282388068326106013607169353334563758778745274388559557359545897092,1527897673999836014297667025197283444500555016058485531353127824194902014167474469048468775057698322500563202,1939107698293492466124497182854715701421424260743574694038673203172185170469049759541468194209248434056609797,1491766253955619470336111765337879807321228318361604692303136252188241691517557842361766397403378639111725123,1080556229661963018509281607680447550400359073676515529617590873210958535215982551868766978251828527555678528,1044424809617746474547828727182352673208586052032021897550250469213790371121273532664960783901519602066391233,2124261932310280447055910984613154715288115871713679142613971431610607091347220736304312767823281456694694211,1676920487972407451267627946457627581175473605384096154766647502342654613353330208144149640622463753550037189,2088130507959914038740566105794329195370103950296632619328276518401011772540835065260937990202006732983775489,1640789063622041042952180688276581438567177412224452234291320087813841791544128431113113522641234524264747136,1229579043634534455479242528939879824372547067311915769729691071755484632356623573996325173061691544831008836,1193447619284168047163897650121054304454535145894869246443996158545889313550237902952950395440416821120090114,1975220915969910726411270455638725378776336080712071737486647883310065473380912190369985677465974863948955845,1527879471632037730622987417483198244663693814382488942733762103145508047999486396506680862546292664422113603,1939089495925694182512480302928263618496141222334077531271964954313363121683701632254717507124325979037388868,1491748051587821186724094885411427724395958549300857767741951941000907785206681895857036257887385956136529922,1080538027294164734834601999966362350563511141349269179203749089833052711522466660108999613309352641521254657,1044406607249948190935811847255900590283316282971274972989066160836350359825256101993731442967703756609687680,2162696249821217618215137618282995761805161463866772981130851447475637340800225444037497314043350055714587078,1715354805483344622426854580127468627692519200776777090509640401564992565131648333805728082158219725487513991,2198810031874538205786337851733305993786506436760379594905215505798982709291159549457813515004465490815640136,1751468587536665209997967732733084514545648867620989517048076244078750713463380194436207742229573977018757834,1268013361145471626638484461127247148451661631637387012652501139844760569303868978784122309383328211690631689,1304127143198792214209684694577557380433006604530993626426865198168105937794803084204438510344443646791684747,2162659845085621050897109766748641920587234776822404635921210707500109423872983187666018490001360285541884552,1715318400747748055108826728593114786474592513732408745299999664399358543219264593267750056698406794997035530,2198773627138941638530972727986585269480157912982510675548232240823920604761415754174872714971135760163963590,1751432182801068642742602608986363790239313613191870835896616916775176751408108579935287489765174019518145095,1267976956409875059320456609592893307233748213941768905648384340350614689865957419028164831492445054351217035,1304090738463195646954319570830836656126671350101874945275405873674425870754389985537019056462220528973296073,2088148730248386322847157488169095820099443502422772316256782546407451147321330618454388234966394114945114956,1640807285910513327058874450013568685986801239333567340454230222273419817968228610745497577768619405767672589,2124280150291551560626515861477365528579478683274669652896233942145309951827300222046484204705313261532529614,1676938705953678564838145746212133679777492313717985267479331836141553906186498272444310633629483123614995536,1193465841572640331270504334748336837184814869776882955037328116269663772327426661143324006692789267850138511,1229597261615805569049862708056606545664850050628780291676779512007522576833396264735419976431708414437553169,1939034924356446161973037722428118249679070272085899030364715574215734146730267298179943166399746031654094034,1491693480018573166184754684272591115566428008996694054609305446895448421906748734635186199986180033315955859,1975166344400662705871638418667566757905110779369202385636264384988801260777591896887449588588281864074896724,1527824900062789710083268303402335131725854571888943527714847372592778209399781316469307308338860636620010966,1044352035680700170396384569007359489387171801516435196687888434499425370528938154217043919736758805861070101,1080483455724916714294985265246807997613212308799738551959437245272492484576262752924550341925294638281872791,2088102942139388143930239303145358379784864289527010106431496045039017256246435451384908089207300857216156686,1640761497801515148141956264989831245672222026437014215857427198752011980122300301150773270614309792594580368,2124216724193760037683344587314480528423792752118522164690614993398036746676223013009172693956336820257088588,1676875279855887041894974468314259271805678614404307852534484762957025887585907207953618610832181507743351757,1193420053463642152353586145989609989054107888722799903701296968311001121031984496095219187490154480080843537,1229533835518014046106691430158732137693036351314311961960415916670020611461772057719483792239190443121775439,1939016721988647878298358114714033049842209070409902441745349850356446285547420709804654531381241050656744852,1491675277650774882510075076558505915729566807320697465989939725846054455738760662093398214859292399040279830,1975148142032864422259621538741114674979827740959705222869556136129979211992243769600699050193918899852494290,1527806697694991426471251423475883048800584802828196603153663061405444303088905369964577241438349929842042195,1044333833312901886721704961293274289550323869189188846274046651121519546835422262457276406103723429029827735,1080465253357118430682968385320355914687942539738991627398252936895052473280245322253320924916401278225577173,2049769017687769198774296095871862879950363614674724004859160418165910413665732485389370083724623815345475975,1602427573349896202986013057716335745837721348345932124924921847642319308253556609437569121868834222960587206,2013655235633397048354468337086480609433124061406872803171889749674944929377962466961166477364705736372285961,1566313791295524052566082923304634345717448066126632804050541251991343398650119758852982758356784110775329419,1155086129012023207197627643934489482122045353065692125803573349958717777525713901329385402860912597363630664,1118972346957651056777799885149107211604805799797840924116302681467752293237943882901181796500994518390440650,1900691598764877714717969933238910636907479320944067661231944706101869567610134280058997543644497088668545546,1453350154427004718929686895083383502794837054615275781297717644903672443058459614791619909108472874647982728,1864577816710505820964675192598775236214396507257864752029691639518871663476055890223589479631617002798358923,1417236372372632825176289778816928972553071764458600442734391844250701708186271051566487650362912913840701897,1006008710089131723141301481301537239133512311816011472002417849635502487768674776134518079839768785690325702,969894928034759829388006740661401838440429498129808562800164783052504583634596386299110015826888699820139079,2013628221001663996420698542154562246258413374902465330775022384609788926674071089124768462874129532607591181,1566286776663791000632415503999035112145771111813260548066908209578450478618965123858776201146200763976979276,2049759645350979098616611641571195714376265618793414984485485764560883615207442614353150673813388057092608911,1602418201013106102828241526306875728277023114275691220575527075831482959690085679355340038170814081020511249,1118945332325918004844045388734715126046528607295536784156949520849049823101608188860965565503626787904881614,1155076756675233107039958488151348594164380851186486437867412900800144511634979714089347776442885312389899344,1864514415109723835546578776413584675838040144565592044882955412418071926083007768850323394307481449316570259,1417172970771850839758295738258057541725397881476387262221983434200479082557485247748464823363761391525262546,1900645839460090243861734198761396943701897714887947717225516207404374924157734289194116057696356659634976021,1453304395122217248073364083497077180225385372446649480811042612282707262903368723380336712880191594025526679,969831526433977843969925622993737778248885539035089025807509839078811421303119681934685478547596325915813204,1005962950784344252285081045341550046112743109357444698150070634065114419377846202278478141936471536234218966,1826134695818644807751099469635627096105108833648673131742230043640777399983596765429136884189061556701565840,1378793251480771811962816431480099961992466567319881251855145179256325879961500316543495155415592500460844046,1790020913765324220117047051926670495158031346393876241172074392092987805390868376840287167564225331034915601,1342679469427451224328661638144824454119436765671037459372259690432550844364064685715966739038703773850592079,931451807142898816174431017698253920953871986597042470055330477595888918934696625419174726890070943276520524,895338025089578228540378599989297320006794499342245579485174826048099324341968236830325010265234717609870285,1789975705648278029351782440560796836846970999684607877491578102972791278694617592814587532548672764108174614,1342634261310405033563499402405269702734328736595403094830617634080592416029586064459708349598183921753609620,1826107129998644694333470881053855974534985309588611842319156499867061856923040731849100147612675348892837015,1378765685660771698545100765789536211112824219628289295730731607160825771106727807646883162537283038358357205,895292816972532037775129287140949939312167646635080548242192741374356330213273140257491364522791611219129810,931424241322898702756817727634009077000181956539084513069771138268626908441696279292003979586794196003792211,2049705029364047540089040521009871174485745384418284613124256769149514923720683221674452257112448407058281161,1602363585026174544300757482854344040373103118088701625324075036695308050256370909896024959599939576777433675,2013573605014732437892937965122224454313738789432644108470659270975127914455647551877635754208861346136363655,1566232160676859442104552547604476920133542413436889250929187933995690927721922065262592538646669186860102150,1155022140688301548512372065336596506192906742092946767782603699715871063522645423280981744037747417501172170,1118890716338986446316269509448949786020900147107306263129006201541484054257609753484165241134160356579254664,1900664013023677819444399992035441837973965593416677207996933220848973305754374675740125166755141814312542795,1453322568685804823656116953879914703861323327087094413291189637498161484902527098258556181523768487649510089,1864532592980512581664852162256158877439776061470089020414347706887479263598514118871415271131180592189977034,1417191148642639585876466744739323205962323550513294784379819787182756921384475530006515273892820618731884936,1005981124347931827867731536363079032383870816130300177256661717793439142688488509393656184285408514191417991,969849704304766590088183706583796071849681284183711989674076203831945100532627952524946288661447292068852230,2013564232677942337735442967292570540793795144646025939040118735593736608858045275349172227448492174172279887,1566222788340069341947159929137043406681152881556030048466061398632125313594401117862016796848732323880420305,2049678014732314488155081269606939559256880346819186289784255285860723679441529455664156783872655510621975565,1602336570394441492366711150606718302693117461585947667454173757835144395789266292220165060489272951018689420,1118881344002196346158789810136822150117389996322791426135979870606546029942137954418025073465349764277134160,1154995126056568496578428112451191168580475198495951776880116420873533100525622134733009629889513100726829838,1864478012527202072103561778861245210851139925528918274353972540911165638159030533768918669622432367612868053,1417136568189329076315278740705718076738497662439713298598573925726167789210861478804641741093714930326119767,1900609432571418872731358221033573705812915335660369347963196428592666144757550212255683140110237590217381267,1453267988233545876942988105768342079688023650009836418073352056283562811292264454231123691095441373117379858,969795123851456080526908625440486450613605976789180368708729553417064455745575720780082292078918713226118358,1005926543895672881154705067612814945575381386920631442317953441098564962344095399266846762566723935830631572,1826116493450846524076419861921541896268247631972676543122864319781489538800750177053848249170556576811254737,1378775049112973528288136823766014762155605365643884663235779458206931913793512244001707170288704865128473679,1790002711397525936505030172000218412232748307984379078405366143234165756605520249553536629169862368976245584,1342661267059652940716644758218372371194166996610290534811075379245216938053188739211236672138193068129317646,931433604775100532499751409984168721117024054269796119641488694217983095241180733659407213257035564281545741,895319822721779944928361720062845237081524730281498654923990517670659313045950806159095593256341356446536588,1789957503280479745677102832846711637010109798008611288872212379113503417511771004439298897530167784217863511,1342616058942606749888819794691184502897467534919406506211251913031198449861597991917920364471296286421239253,1826088927630846410721454001127403891609702271179114679552448251008239808137692604562349609218312386834166998,1378747483292973414933083885863084128187554450567542371169547295973491864795851861142153095636772332637082772,895274614604733754100449679426864739475319714307834197828350957996450506519757248497723850889756232224155027,931406038955100419144800847707556994074912187478337588508586829891186897145678848620774562577900834840458514]

abbrev Orient := Fin 144
def pF (o : Orient) (i : Fin 4) : Fin 4 := Fin.ofNat 4 ((pigeonCode[o.val/6]! >>> (2*i.val)) % 4)
def pB (o : Orient) (i : Fin 4) : Fin 4 := Fin.ofNat 4 ((pigeonBack[o.val/6]! >>> (2*i.val)) % 4)
def hF (o : Orient) (i : Fin 3) : Fin 3 := Fin.ofNat 3 ((holeCode[o.val%6]! >>> (2*i.val)) % 4)
def hB (o : Orient) (i : Fin 3) : Fin 3 := Fin.ofNat 3 ((holeBack[o.val%6]! >>> (2*i.val)) % 4)

theorem pigeonInv : ∀ o : Orient, ∀ i : Fin 4, pB o (pF o i) = i ∧ pF o (pB o i) = i := by decide +kernel
theorem holeInv : ∀ o : Orient, ∀ i : Fin 3, hB o (hF o i) = i ∧ hF o (hB o i) = i := by decide +kernel
def pPerm (o : Orient) : Equiv.Perm (Fin 4) := ⟨pF o,pB o,fun i => (pigeonInv o i).1,fun i => (pigeonInv o i).2⟩
def hPerm (o : Orient) : Equiv.Perm (Fin 3) := ⟨hF o,hB o,fun i => (holeInv o i).1,fun i => (holeInv o i).2⟩

def rowBack (o : Orient) (r : Row) : Row := Fin.ofNat 60 ((rowCode[o.val]! >>> (6*r.val)) % 64)
def orientV (o : Orient) := permV (pPerm o) (hPerm o)
class ActionWitness : Prop where
  fact : ∀ o : Orient, ∀ r : Row, ∀ v : V,
    assignment r (orientV o v) = assignment (rowBack o r) v
variable [inputAction : ActionWitness]
include inputAction
theorem rowAction : ∀ o : Orient, ∀ r : Row, ∀ v : V,
    assignment r (orientV o v) = assignment (rowBack o r) v := ActionWitness.fact

theorem orientMask (o : Orient) (C : Cl) (r : Row) :
    (privateMask (permCl (orientV o) C)).testBit r.val = true ↔
    (privateMask C).testBit (rowBack o r).val = true := by
  rw [privateBit,privateBit,permSat]
  have e : (fun v => assignment r (orientV o v)) = assignment (rowBack o r) :=
     funext (rowAction o r)
  rw [e]
def orbitReps : Array Nat := #[0,61,211,212,391,392,396,631,633,635,647,920,921,922,926,1301,1303,1304,1306,1307,1366,1721,1726,1937,1939,1940,1941,2297,2441,2443,2444,2451,2693,2705,2849,2885,2957,2958,2961,2962,3083,3095,3131,3203,3227,3239,3257,3293,3305]
def orbitCodes : Array Nat := #[0]

abbrev Orbit := Fin 49
def rep (z : Orbit) : KeyID := Fin.ofNat 3306 orbitReps[z.val]!
def tag (i : KeyID) : Nat := (orbitCodes[i.val/16]! >>> (14*(i.val%16))) % 16384
def which (i : KeyID) : Orbit := Fin.ofNat 49 (tag i % 64)
def spin (i : KeyID) : Orient := Fin.ofNat 144 (tag i / 64)
class OrientationWitness : Prop where
  fact : ∀ i : KeyID, 1 < rawCost i → ∀ r : Row,
    (stateMask i).testBit (rowBack (spin i) r).val =
    (stateMask (rep (which i))).testBit r.val
variable [inputOrientation : OrientationWitness]
include inputOrientation
theorem aligns : ∀ i : KeyID, 1 < rawCost i → ∀ r : Row,
    (stateMask i).testBit (rowBack (spin i) r).val =
    (stateMask (rep (which i))).testBit r.val := OrientationWitness.fact

theorem limited (C : Cl) : privateMask C < 2^60 := by
  have cutSmall (s : Nat) (l : Literal V) : cut C s l ≤ s := by
    unfold cut
    split
    · exact Nat.and_le_left
    · exact le_rfl
  have loop (ls : List (Literal V)) (s : Nat) : ls.foldl (cut C) s ≤ s := by
    induction ls generalizing s with
    | nil => exact le_rfl
    | cons l ls ih => exact (ih (cut C s l)).trans (cutSmall s l)
  exact lt_of_le_of_lt (loop lits fullMask) (by decide)

theorem eqFromRows {a b : Nat} (ha : a < 2^60) (hb : b < 2^60)
    (e : ∀ r : Row, a.testBit r.val = true ↔ b.testBit r.val = true) : a=b := by
  have h1 := subsetOfTests a b ha (fun r => (e r).1)
  have h2 := subsetOfTests b a hb (fun r => (e r).2)
  calc
    a = a &&& b := h1.symm
    _ = b &&& a := Nat.and_comm _ _
    _ = b := h2

theorem rotateFit {C : Cl} {i : KeyID} (gt : 1 < rawCost i) (e : privateMask C = stateMask i) :
    Fits (permCl (orientV (spin i)) C) (rep (which i)) := by
  left
  apply eqFromRows (limited _) (Nat.mod_lt _ (by decide))
  intro r
  rw [orientMask,e,aligns i gt r] <;> rfl

def lane (a : Orbit) (b : KeyID) : Nat := 49*b.val+a.val
def laneMask : Nat := 2^(49*3306)-1
def tile : Nat := 2^49-1

def packing (scale : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => packing scale f n ||| (f n <<< (scale*n))

def flags (r : Nat) : Nat :=
  packing 1 (fun i => if (stateMask (rep (Fin.ofNat 49 i))).testBit r then 1 else 0) 49

def singleCol (r : Nat) : Nat :=
  let f := flags r
  packing 49 (fun _ => f) 3306

def doubleCol (r : Nat) : Nat :=
  packing 49 (fun b => if (stateMask (Fin.ofNat 3306 b)).testBit r then tile else 0) 3306

def colA : Array Nat := Array.ofFn (fun r : Fin 60 => singleCol r.val)
def colB : Array Nat := Array.ofFn (fun r : Fin 60 => doubleCol r.val)

def upperBox (m : Nat) (cols : Array Nat) : Nat :=
  (List.range 60).foldl (fun x r => if m.testBit r then x &&& cols[r]! else x) laneMask
def allowed (m : Nat) : Nat := laneMask ^^^ (upperBox m colA ||| upperBox m colB)

class TestGrid where
  matrix : Array (Array Nat)
variable [grid : TestGrid]
include grid
def jt : Array (Array Nat) := grid.matrix

def atCell (row : Array Nat) (k : Nat) : Nat := if h : k < row.size then row[k] else 0
def rowOf (t : Array (Array Nat)) (s : KeyID) : Array Nat := t.getD s.val #[]
def setOf (t : Array (Array Nat)) (s : KeyID) (k : Nat) := atCell (rowOf t s) k

def atRoot (t : Array (Array Nat)) (a : Orbit) (b : KeyID) : Prop :=
  ∃ p : Fin 44, (setOf t b p.val).testBit a.val = true ∧
    (setOf t 3305 (41 - rawCost (rep a) - max 1 p.val)).testBit (lane a b) = true

instance (t : Array (Array Nat)) (a : Orbit) (b : KeyID) : Decidable (atRoot t a b) := by
  unfold atRoot; infer_instance

def jointEnd : Prop := ∀ a b, atRoot jt a b
instance : Decidable jointEnd := by unfold jointEnd; infer_instance


def vectorLaw (s : KeyID) : Prop :=
  (rowOf jt s).size = rawCost s + 1 ∧
  ∀ k : Fin (rowOf jt s).size, 1 < k.val → setOf jt s k.val ≠ 0 →
    (setOf jt s k.val &&& (upperBox (stateMask s) colA ||| upperBox (stateMask s) colB) = 0) ∧
    ∀ v, Cont (setOf jt s k.val) (convolve (List.range (k.val+1))
      (setOf jt (child s v false)) (setOf jt (child s v true)) k.val)

instance (s : KeyID) : Decidable (vectorLaw s) := by unfold vectorLaw Cont; infer_instance

theorem packingHit (scale : Nat) (f : Nat → Nat) {n i a : Nat} (small : i < n)
    (hit : (f i).testBit a = true) : (packing scale f n).testBit (scale*i+a) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [packing,Nat.testBit_or,Bool.or_eq_true]
    by_cases e : i = n
    · subst n; right
      rw [Nat.testBit_shiftLeft]
      simp [hit]
    · exact Or.inl (ih (by omega))

theorem keyRound (i : KeyID) : Fin.ofNat 3306 i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)
theorem orbRound (a : Orbit) : Fin.ofNat 49 a.val = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem boxHit (m : Nat) (cols : Array Nat) (a : Orbit) (b : KeyID)
    (every : ∀ r ∈ List.range 60, m.testBit r = true → (cols[r]!).testBit (lane a b) = true) :
    (upperBox m cols).testBit (lane a b) = true := by
  have init : laneMask.testBit (lane a b) = true := by
    rw [laneMask,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    unfold lane
    have := a.isLt; have := b.isLt
    omega
  have loop (rs : List Nat) (acc : Nat) (hacc : acc.testBit (lane a b) = true)
      (h : ∀ i ∈ rs, m.testBit i = true → (cols[i]!).testBit (lane a b) = true) :
      (rs.foldl (fun y i => if m.testBit i then y &&& cols[i]! else y) acc).testBit (lane a b) = true := by
    induction rs generalizing acc with
    | nil => exact hacc
    | cons i is ih =>
      simp only [List.foldl_cons]
      apply ih
      · split
        · next t => simp [Nat.testBit_and,hacc,h i (by simp) t]
        · exact hacc
      · exact fun q hq => h q (List.mem_cons_of_mem _ hq)
  exact loop _ _ init every

theorem firstBox {m : Nat} (a : Orbit) (b : KeyID) (sub : Cont m (stateMask (rep a))) :
    (upperBox m colA).testBit (lane a b) = true := by
  apply boxHit
  intro r hr one
  have small := List.mem_range.mp hr
  have rd : colA[r]! = singleCol r := by
    rw [getElem!_pos colA r (by simpa [colA] using small)]
    simp [colA]
  rw [rd]
  apply packingHit 49 _ b.isLt
  have singled : ((fun i => if (stateMask (rep (Fin.ofNat 49 i))).testBit r then (1:Nat) else 0) a.val).testBit 0 = true := by
    simp [orbRound,testBit_subset sub one]
  simpa [flags] using (packingHit 1 (fun i : Nat => if (stateMask (rep (Fin.ofNat 49 i))).testBit r then (1:Nat) else 0) (n:=49) (i:=a.val) (a:=0) a.isLt singled)

theorem secondBox {m : Nat} (a : Orbit) (b : KeyID) (sub : Cont m (stateMask b)) :
    (upperBox m colB).testBit (lane a b) = true := by
  apply boxHit
  intro r hr one
  have small := List.mem_range.mp hr
  have rd : colB[r]! = doubleCol r := by
    rw [getElem!_pos colB r (by simpa [colB] using small)]
    simp [colB]
  rw [rd]
  apply packingHit 49 _ b.isLt
  change (if (stateMask (Fin.ofNat 3306 b.val)).testBit r then tile else 0).testBit a.val = true
  rw [keyRound,testBit_subset sub one]
  change (2^49-1 : Nat).testBit a.val = true
  rw [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
  exact a.isLt

theorem fitFail {C : Cl} {i : KeyID} (f : Fits C i) : FailsOn assignment live i C := by
  rcases f with h | ⟨rfl,_⟩
  · exact failsId h
  · intro r hr
    have e : stateMask (0 : KeyID) = 0 := by decide +kernel
    simp [live,e] at hr

theorem fitGrants {C : Cl} {i : KeyID} (f : Fits C i) :
    Basal C ∨ Cont (privateMask C) (stateMask i) := by
  rcases f with eq | ⟨_,base⟩
  · exact Or.inr (eq ▸ contRefl _)
  · exact Or.inl base

theorem replayJoint (law : ∀ s, vectorLaw s) (a : Orbit) (b : KeyID) {F : Set Cl}
    (admitted : ∀ C ∈ F, Basal C ∨ Cont (privateMask C) (stateMask (rep a)) ∨
      Cont (privateMask C) (stateMask b)) {C : Cl} {n : Nat} (tree : ResTree F C n)
    (x : KeyID) (k : Nat) (test : (setOf jt x k).testBit (lane a b) = true)
    (fails : FailsOn assignment live x C) : k ≤ n+1 := by
  let T := fun s q => (setOf jt s q).testBit (lane a b) = true
  have inrow (s : KeyID) (q : Nat) (h : T s q) : q < (rowOf jt s).size := by
    by_contra no
    change (setOf jt s q).testBit (lane a b) = true at h
    simp [setOf,atCell,no] at h
  refine treeThreshold assignment live T ?_ ?_ tree x k test fails
  · intro D m s q yes ill
    by_cases big : 1 < q
    · have bound := inrow s q yes
      have nz : setOf jt s q ≠ 0 := by intro e; change (setOf jt s q).testBit _ = true at yes; simp [e] at yes
      have cell := (law s).2 ⟨q,bound⟩ big nz
      have fit := containsOfFails ill
      rcases admitted D m with ⟨l,hl,sub⟩ | raw | afterB
      · have lim := rawSmall hl (contTrans fit sub)
        rw [(law s).1] at bound
        omega
      · have g := firstBox a b (contTrans fit raw)
        have eq := congrArg (fun v : Nat => v.testBit (lane a b)) cell.1
        change (setOf jt s q).testBit (lane a b) = true at yes
        simp [Nat.testBit_and,Nat.testBit_or,yes,g] at eq
      · have g := secondBox a b (contTrans fit afterB)
        have eq := congrArg (fun v : Nat => v.testBit (lane a b)) cell.1
        change (setOf jt s q).testBit (lane a b) = true at yes
        simp [Nat.testBit_and,Nat.testBit_or,yes,g] at eq
    · omega
  · intro s q big yes v
    have bound := inrow s q yes
    have nz : setOf jt s q ≠ 0 := by intro e; change (setOf jt s q).testBit _ = true at yes; simp [e] at yes
    have link := ((law s).2 ⟨q,bound⟩ big nz).2 v
    have z := testBit_subset link yes
    obtain ⟨p,hp,lo,hi⟩ := (convolve_bit _ _ _ _ _).1 z
    rw [(law s).1] at bound
    have geom := geomBranch s (by omega) v
    exact ⟨_,_,p,by simpa using List.mem_range.mp hp,geom.1,geom.2.1,lo,hi⟩

theorem jointPair (law : ∀ s, vectorLaw s) (scores : jointEnd)
    {A B : Cl} (a : Orbit) (b : KeyID) (fa : Fits A (rep a)) (fb : Fits B b)
    {i j k : Nat} (x : ResTree (PHP 4 3) A i) (y : ResTree (insert A (PHP 4 3)) B j)
    (z : ResTree (insert B (insert A (PHP 4 3))) ∅ k) : 38 ≤ i+j+k := by
  obtain ⟨p,one,two⟩ := scores a b
  have lib : ∀ C ∈ insert A (PHP 4 3),
      Basal C ∨ Cont (privateMask C) (stateMask (rep a)) := by
    intro C c
    rcases c with rfl | ax
    · exact fitGrants fa
    · exact Or.inl (isBasalOfAx ax)
  have cA := chargeRaw fa x
  have cB : p.val ≤ j+1 :=
    replayJoint law a 0 (fun C h => (lib C h).imp_right Or.inl) y b p.val
      (by simpa [lane] using one) (fitFail fb)
  have cZ : 41 - rawCost (rep a) - max 1 p.val ≤ k+1 := by
    refine replayJoint law a b ?_ z 3305 _ two ?_
    · intro C h
      rcases h with rfl | h
      · exact (fitGrants fb).imp_right Or.inr
      · exact (lib C h).imp_right Or.inl
    · intro r _ h; simpa [ClauseSat] using h
  omega

theorem tree38_of_joint (law : ∀ s, vectorLaw s) (scores : jointEnd)
    {A B : Cl} {i j k : Nat} (t1 : ResTree (PHP 4 3) A i) (t2 : ResTree (insert A (PHP 4 3)) B j)
    (t3 : ResTree (insert B (insert A (PHP 4 3))) ∅ k) : 38 ≤ i+j+k := by
  have dispatch {A B : Cl} (z : Orbit) (fit : Fits A (rep z))
      (x : ResTree (PHP 4 3) A i) (y : ResTree (insert A (PHP 4 3)) B j)
      (w : ResTree (insert B (insert A (PHP 4 3))) ∅ k) : 38 ≤ i+j+k := by
    obtain ⟨b,m⟩ := anyFits B
    exact jointPair law scores z b fit m x y w
  rcases privateSupported A with ⟨s,large,ea⟩ | base
  · let o := spin s
    let f := orientV o
    have inj : Function.Injective f := permVInj (pPerm o) (hPerm o)
    have raws := phpRename (pPerm o) (hPerm o)
    have ins : ∀ C ∈ insert A (PHP 4 3), permCl f C ∈ insert (permCl f A) (PHP 4 3) := by
      intro C m; rcases m with rfl | ax
      · exact Or.inl rfl
      · exact Or.inr (raws _ ax)
    have ins2 : ∀ C ∈ insert B (insert A (PHP 4 3)),
        permCl f C ∈ insert (permCl f B) (insert (permCl f A) (PHP 4 3)) := by
      intro C m; rcases m with rfl | ax
      · exact Or.inl rfl
      · exact Or.inr (ins _ ax)
    apply dispatch (which s) (rotateFit large ea) (permTree inj raws t1) (permTree inj ins t2)
    simpa [permCl] using permTree inj ins2 t3
  · apply dispatch 0 _ t1 t2 t3
    right
    exact ⟨by decide +kernel,base⟩

end PCX150
