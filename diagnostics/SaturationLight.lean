import PEqualNP.Defs

namespace PCX150.Sparse

abbrev Point := Fin 60
abbrev Query := Fin 12
abbrev Label := Fin 22
abbrev Box := Sum Label (Fin 2)

inductive TestTree where
  | leaf
  | cut (v : Query) (no yes : TestTree)

def leaves : TestTree → Nat
  | .leaf => 1
  | .cut _ t u => leaves t + leaves u

def half (bit : Point → Query → Bool) (s : Set Point) (v : Query) (b : Bool) : Set Point :=
  {p | p ∈ s ∧ bit p v = b}

def Valid (bit : Point → Query → Bool) (term : Box → Set Point) : TestTree → Set Point → Prop
  | .leaf,s => ∃ i, s ⊆ term i
  | .cut v t u,s => Valid bit term t (half bit s v false) ∧ Valid bit term u (half bit s v true)

theorem coverExists (bit : Point → Query → Bool) (term : Box → Set Point)
    {t : TestTree} {s : Set Point} (h : Valid bit term t s) :
    ∃ f : Finset Box, f.card ≤ leaves t ∧ ∀ p ∈ s, ∃ i ∈ f, p ∈ term i := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,hi⟩ := h
    exact ⟨{i},by simp [leaves],fun p hp => ⟨i,by simp,hi hp⟩⟩
  | cut v t u ht hu =>
    obtain ⟨a,ha,ca⟩ := ht h.1
    obtain ⟨b,hb,cb⟩ := hu h.2
    refine ⟨a ∪ b,(Finset.card_union_le _ _).trans (Nat.add_le_add ha hb),?_⟩
    intro p hp
    cases m : bit p v with
    | false =>
      obtain ⟨i,hi,hit⟩ := ca p ⟨hp,m⟩
      exact ⟨i,Finset.mem_union_left _ hi,hit⟩
    | true =>
      obtain ⟨i,hi,hit⟩ := cb p ⟨hp,m⟩
      exact ⟨i,Finset.mem_union_right _ hi,hit⟩

def box (tag : Point → Label) (A B : Set Point) : Box → Set Point
  | .inl i => {p | tag p = i}
  | .inr i => if i = 0 then A else B

noncomputable def liveTags (tag : Point → Label) (s : Set Point) : Finset Label := by
  classical
  exact Finset.univ.filter (fun k => ∃ p ∈ s, tag p = k)

theorem ofLive {tag : Point → Label} {s : Set Point} {i : Label}
    (hi : i ∈ liveTags tag s) : ∃ p ∈ s, tag p = i := by
  classical
  unfold liveTags at hi
  exact (Finset.mem_filter.mp hi).2

noncomputable def residual (tag : Point → Label) (s A B : Set Point) (x y : Bool) : Finset Box := by
  classical
  exact ((liveTags tag {p | p ∈ s ∧ (x = true → p ∉ A) ∧ (y = true → p ∉ B)}).map
      ⟨Sum.inl,Sum.inl_injective⟩) ∪
    (if x then {Sum.inr 0} else ∅) ∪ (if y then {Sum.inr 1} else ∅)

theorem cheapLower (bit : Point → Query → Bool) (tag : Point → Label)
    {t : TestTree} {s A B : Set Point} (h : Valid bit (box tag A B) t s) (k : Nat)
    (hk : ∀ x y : Bool, k ≤ (residual tag s A B x y).card) : k ≤ leaves t := by
  classical
  obtain ⟨f,hf,cover⟩ := coverExists _ _ h
  let x := decide ((Sum.inr 0 : Box) ∈ f)
  let y := decide ((Sum.inr 1 : Box) ∈ f)
  have subset : residual tag s A B x y ⊆ f := by
    intro u hu
    simp only [residual,Finset.mem_union] at hu
    rcases hu with (lab | fst) | snd
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp lab
      obtain ⟨p,⟨ps,pa,pb⟩,eq⟩ := ofLive hi
      obtain ⟨b,mem,hit⟩ := cover p ps
      cases b with
      | inl j =>
        change tag p = j at hit
        have ji : j=i := hit.symm.trans eq
        simpa [ji] using mem
      | inr j =>
        fin_cases j
        · exact False.elim (pa (by simpa [x] using mem) (by simpa [box] using hit))
        · exact False.elim (pb (by simpa [y] using mem) (by simpa [box] using hit))
    · by_cases hx : (Sum.inr 0 : Box) ∈ f
      · have e : u = Sum.inr 0 := by simpa [x,hx] using fst
        simpa [e] using hx
      · simp [x,hx] at fst
    · by_cases hy : (Sum.inr 1 : Box) ∈ f
      · have e : u = Sum.inr 1 := by simpa [y,hy] using snd
        simpa [e] using hy
      · simp [y,hy] at snd
  exact (hk x y).trans ((Finset.card_le_card subset).trans hf)

end PCX150.Sparse


namespace PCX150.SmallChart

abbrev Sample := Fin 60
abbrev Var := Fin 12
abbrev Tag := Fin 22
abbrev Key := Fin 48

structure Domain where
  val : Sample → Var → Bool
  tag : Sample → Tag

structure Aut (B : Domain) where
  s : Equiv.Perm Sample
  v : Equiv.Perm Var
  a : Equiv.Perm Tag
  bit : ∀ x q, B.val (s x) (v q) = B.val x q
  label : ∀ x, B.tag (s x) = a (B.tag x)

def Aut.unit (B : Domain) : Aut B :=
  ⟨Equiv.refl _,Equiv.refl _,Equiv.refl _,fun _ _ => rfl,fun _ => rfl⟩

def Aut.thenDo {B : Domain} (f g : Aut B) : Aut B where
  s := f.s.trans g.s
  v := f.v.trans g.v
  a := f.a.trans g.a
  bit x q := (g.bit _ _).trans (f.bit x q)
  label x := (g.label _).trans (congrArg g.a (f.label x))

def acted {B : Domain} (f : Aut B) (u : Set Sample) : Set Sample :=
  {x | f.s.symm x ∈ u}

def branch (B : Domain) (u : Set Sample) (q : Var) (b : Bool) : Set Sample :=
  {x | x ∈ u ∧ B.val x q = b}

def plain (B : Domain) (u : Set Sample) : Prop := ∃ a, ∀ x ∈ u, B.tag x = a

structure Chart (B : Domain) where
  state : Key → Set Sample
  wt : Key → Nat
  root : Key
  start : state root = Set.univ
  rich : ∀ k, ¬ plain B (state k)
  next : Key → Var → Bool → Option Key
  proper : ∀ k q b, match next k q b with
    | none => plain B (branch B (state k) q b)
    | some j => ∃ f : Aut B, branch B (state k) q b = acted f (state j)
  subadd : ∀ k q, wt k ≤ ((next k q false).map wt).getD 1 + ((next k q true).map wt).getD 1

theorem actedChain {B : Domain} (f g : Aut B) (u : Set Sample) :
    acted g (acted f u) = acted (f.thenDo g) u := rfl

theorem branchAct {B : Domain} (f : Aut B) (u : Set Sample) (q : Var) (b : Bool) :
    branch B (acted f u) q b = acted f (branch B u (f.v.symm q) b) := by
  ext x
  have eq := f.bit (f.s.symm x) (f.v.symm q)
  simp only [Equiv.apply_symm_apply] at eq
  change (_ ∧ B.val x q = b) ↔ (_ ∧ B.val (f.s.symm x) (f.v.symm q) = b)
  rw [eq]
  rfl

theorem actedPlain {B : Domain} (f : Aut B) {s : Set Sample} (h : plain B s) : plain B (acted f s) := by
  obtain ⟨a,ha⟩ := h
  refine ⟨f.a a,?_⟩
  intro x hx
  simpa [ha _ hx] using f.label (f.s.symm x)

theorem actedRich {B : Domain} (f : Aut B) {s : Set Sample} (h : ¬ plain B s) : ¬ plain B (acted f s) := by
  rintro ⟨a,ha⟩
  apply h
  refine ⟨f.a.symm a,?_⟩
  intro x hx
  apply f.a.injective
  rw [Equiv.apply_symm_apply,←f.label]
  exact ha _ (by simpa [acted] using hx)

def Classified {B : Domain} (c : Chart B) (s : Set Sample) : Prop :=
  plain B s ∨ ∃ k, ∃ f : Aut B, s = acted f (c.state k)

theorem classifyBranch {B : Domain} {c : Chart B} {s : Set Sample}
    (h : Classified c s) (q : Var) (b : Bool) : Classified c (branch B s q b) := by
  rcases h with ⟨a,h⟩ | ⟨k,f,rfl⟩
  · exact Or.inl ⟨a,fun x hx => h x hx.1⟩
  · rw [branchAct]
    have hi := c.proper k (f.v.symm q) b
    cases e : c.next k (f.v.symm q) b with
    | none =>
      rw [e] at hi
      exact Or.inl (actedPlain f hi)
    | some j =>
      rw [e] at hi
      obtain ⟨g,hg⟩ := hi
      exact Or.inr ⟨j,g.thenDo f,by rw [hg,actedChain]⟩

theorem chartAll {B : Domain} (c : Chart B) (qs : List (Var × Bool)) :
    Classified c (qs.foldl (fun s q => branch B s q.1 q.2) Set.univ) := by
  have walk (xs : List (Var × Bool)) (s : Set Sample) (h : Classified c s) :
      Classified c (xs.foldl (fun t q => branch B t q.1 q.2) s) := by
    induction xs generalizing s with
    | nil => exact h
    | cons a tail ih => exact ih _ (classifyBranch h _ _)
  apply walk
  exact Or.inr ⟨c.root,Aut.unit B,by rw [c.start]; rfl⟩

inductive Tree
  | leaf
  | node (v : Var) (no yes : Tree)

def leaves : Tree → Nat
  | .leaf => 1
  | .node _ l r => leaves l + leaves r

theorem leafPos (t : Tree) : 1 ≤ leaves t := by
  induction t with
  | leaf => decide
  | node q l r h k => simp only [leaves]; omega

def rawValid (B : Domain) : Tree → Set Sample → Prop
  | .leaf,s => plain B s
  | .node q l r,s => rawValid B l (branch B s q false) ∧ rawValid B r (branch B s q true)

theorem rawLower {B : Domain} (c : Chart B) (t : Tree) (k : Key) (f : Aut B)
    (good : rawValid B t (acted f (c.state k))) : c.wt k ≤ leaves t := by
  induction t generalizing k f with
  | leaf => exact False.elim (actedRich f (c.rich k) good)
  | node q l r hl hr =>
    let u := f.v.symm q
    have one (b : Bool) (sub : Tree) (ih : ∀ j (g : Aut B), rawValid B sub (acted g (c.state j)) → c.wt j ≤ leaves sub)
        (ok : rawValid B sub (branch B (acted f (c.state k)) q b)) :
        ((c.next k u b).map c.wt).getD 1 ≤ leaves sub := by
      cases e : c.next k u b with
      | none => exact leafPos sub
      | some j =>
        have hg := c.proper k u b
        rw [e] at hg
        obtain ⟨g,he⟩ := hg
        have hi : branch B (acted f (c.state k)) q b = acted (g.thenDo f) (c.state j) := by
          rw [branchAct]; change acted f (branch B (c.state k) u b) = _
          rw [he,actedChain]
        exact ih j _ (hi ▸ ok)
    exact (c.subadd k u).trans (Nat.add_le_add (one false l hl good.1) (one true r hr good.2))

end PCX150.SmallChart

namespace PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev Cl := Clause V
inductive ResTree (F : Set Cl) : Cl → Nat → Prop where
  | ax {C : Cl} : C ∈ F → ResTree F C 0
  | res {C D R : Cl} {i j : Nat} : ResTree F C i → ResTree F D j →
      IsResolvent C D R → ResTree F R (i+j+1)
end PCX150

namespace PCX150.Sparse
open PCX150.SmallChart (Domain Aut)

def renamed {B : Domain} (f : Aut B) : TestTree → TestTree
  | .leaf => .leaf
  | .cut q l r => .cut (f.v q) (renamed f l) (renamed f r)

theorem sameLeaves {B : Domain} (f : Aut B) (t : TestTree) : leaves (renamed f t) = leaves t := by
  induction t with
  | leaf => rfl
  | cut q l r hl hr => simp [renamed,leaves,hl,hr]

theorem smaller {bit : Point → Query → Bool} {base newer : Box → Set Point}
    {t : TestTree} {s d : Set Point} (h : Valid bit base t s) (sub : d ⊆ s)
    (relax : ∀ i, ∃ j, ∀ p ∈ d, p ∈ base i → p ∈ newer j) : Valid bit newer t d := by
  induction t generalizing s d with
  | leaf =>
    obtain ⟨i,all⟩ := h
    obtain ⟨j,hj⟩ := relax i
    exact ⟨j,fun p hp => hj p hp (all (sub hp))⟩
  | cut q l r hl hr =>
    constructor
    · exact hl h.1 (fun _ hd => ⟨sub hd.1,hd.2⟩)
        (fun i => (relax i).imp (fun _ h p hp => h p hp.1))
    · exact hr h.2 (fun _ hd => ⟨sub hd.1,hd.2⟩)
        (fun i => (relax i).imp (fun _ h p hp => h p hp.1))

theorem moveTree {B : Domain} (f : Aut B) {t : TestTree} {s : Set Point}
    {old newT : Box → Set Point} (good : Valid B.val old t s)
    (go : ∀ i, ∃ j, ∀ p ∈ s, p ∈ old i → f.s p ∈ newT j) :
    Valid B.val newT (renamed f t) (SmallChart.acted f s) := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,full⟩ := good
    obtain ⟨j,hj⟩ := go i
    refine ⟨j,?_⟩
    intro p hp
    simpa using hj (f.s.symm p) hp (full hp)
  | cut q l r hl hr =>
    have step (b : Bool) : half B.val (SmallChart.acted f s) (f.v q) b =
        SmallChart.acted f (half B.val s q b) := by
      change SmallChart.branch B (SmallChart.acted f s) (f.v q) b = _
      rw [SmallChart.branchAct,Equiv.symm_apply_apply]
      try rfl
    constructor
    · rw [step]
      exact hl good.1 (fun i => (go i).imp (fun _ h p hp => h p hp.1))
    · rw [step]
      exact hr good.2 (fun i => (go i).imp (fun _ h p hp => h p hp.1))

theorem transferTree {F : Set PCX150.Cl} (vCode : PCX150.V → Query) (bit : Point → Query → Bool)
    (A : Point → PCX150.V → Bool) (correct : ∀ p v, bit p (vCode v) = A p v)
    (term : Box → Set Point) (raw : ∀ C ∈ F, ∃ i, ∀ p, ¬PEqualNP.ProofComplexity.ClauseSat (A p) C → p ∈ term i)
    {C : PCX150.Cl} {n : Nat} (h : PCX150.ResTree F C n) (s : Set Point)
    (f : ∀ p ∈ s, ¬PEqualNP.ProofComplexity.ClauseSat (A p) C) :
    ∃ t : TestTree, leaves t = n+1 ∧ Valid bit term t s := by
  induction h generalizing s with
  | ax hc =>
    obtain ⟨i,hi⟩ := raw _ hc
    exact ⟨.leaf,rfl,i,fun p hp => hi p (f p hp)⟩
  | @res C D R i j _ _ hr ihC ihD =>
    obtain ⟨v,pc,pd,rfl⟩ := hr
    have left : ∀ p ∈ half bit s (vCode v) false, ¬PEqualNP.ProofComplexity.ClauseSat (A p) C := by
      intro p hp sat
      obtain ⟨l,hl,yes⟩ := sat
      have ne : l ≠ (v,true) := by
        rintro rfl
        change A p v = true at yes
        have val : bit p (vCode v) = false := hp.2
        rw [correct,yes] at val
        contradiction
      exact f p hp.1 ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    have right : ∀ p ∈ half bit s (vCode v) true, ¬PEqualNP.ProofComplexity.ClauseSat (A p) D := by
      intro p hp sat
      obtain ⟨l,hl,yes⟩ := sat
      have ne : l ≠ (v,false) := by
        rintro rfl
        change A p v = false at yes
        have val : bit p (vCode v) = true := hp.2
        rw [correct,yes] at val
        contradiction
      exact f p hp.1 ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    obtain ⟨l,lc,lv⟩ := ihC _ left
    obtain ⟨r,rc,rv⟩ := ihD _ right
    exact ⟨.cut (vCode v) l r,by simp only [leaves,lc,rc]; omega,lv,rv⟩

end PCX150.Sparse

namespace PCX150.Sparse
open PCX150.SmallChart (Domain Aut acted)

structure Triple where
  points : Set Point
  a : Set Point
  b : Set Point

def admissible (g : Domain) (s : Triple) (t : TestTree) :=
  Valid g.val (box g.tag s.a s.b) t s.points

def restricted (g : Domain) (s : Triple) (q : Query) (b : Bool) : Triple :=
  ⟨half g.val s.points q b,s.a,s.b⟩

structure Embed (g : Domain) (hard easy : Triple) where
  turn : Aut g
  keep : hard.points ⊆ acted turn easy.points
  accepts : ∀ i, ∃ j, ∀ p ∈ hard.points,
    turn.s.symm p ∈ box g.tag easy.a easy.b i → p ∈ box g.tag hard.a hard.b j

theorem embedTree {g : Domain} {hard easy : Triple} (f : Embed g hard easy) {t : TestTree}
    (h : admissible g easy t) : admissible g hard (renamed f.turn t) := by
  let pre : Set Point := {p | f.turn.s p ∈ hard.points}
  have inc : pre ⊆ easy.points := by
    intro p hp
    have w := f.keep hp
    change f.turn.s.symm (f.turn.s p) ∈ easy.points at w
    simpa using w
  have localGood := smaller h inc (newer := box g.tag easy.a easy.b)
    (fun i => ⟨i,fun _ _ hi => hi⟩)
  have eq : acted f.turn pre = hard.points := by
    ext p
    change f.turn.s (f.turn.s.symm p) ∈ hard.points ↔ p ∈ hard.points
    simp
  change Valid _ _ _ hard.points
  rw [←eq]
  apply moveTree f.turn localGood
  intro i
  obtain ⟨j,hj⟩ := f.accepts i
  exact ⟨j,fun p hp ha => hj _ hp (by simpa using ha)⟩

structure Rule (g : Domain) (K : Type) where
  item : K → Triple
  weight : K → Nat
  base : ∀ i, admissible g (item i) .leaf → weight i ≤ 1
  kw : K → Query → Bool → Nat
  fork : ∀ i q, weight i ≤ kw i q false + kw i q true
  child : ∀ i q b, let s := restricted g (item i) q b
    (∀ t, admissible g s t → kw i q b ≤ leaves t) ∨
    ∃ j, Nonempty (Embed g (item j) s) ∧ kw i q b ≤ weight j

theorem soundRules {g : Domain} {K : Type} (rule : Rule g K) :
    ∀ t i, admissible g (rule.item i) t → rule.weight i ≤ leaves t := by
  have count (n : Nat) : ∀ (t : TestTree), leaves t = n →
      ∀ i, admissible g (rule.item i) t → rule.weight i ≤ leaves t := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro t eq i good
      cases t with
      | leaf => exact rule.base i good
      | cut q l r =>
        have pos (u : TestTree) : 0 < leaves u := by
          induction u with
          | leaf => decide
          | cut v a b ha hb => simp only [leaves]; omega
        have left := pos l
        have right := pos r
        change leaves l + leaves r = n at eq
        have each (b : Bool) (sub : TestTree) (lt : leaves sub < n)
            (valid : admissible g (restricted g (rule.item i) q b) sub) :
            rule.kw i q b ≤ leaves sub := by
          rcases rule.child i q b with cheap | ⟨j,⟨emb⟩,hw⟩
          · exact cheap sub valid
          · obtain hg := embedTree emb valid
            have z := ih (leaves sub) lt (renamed emb.turn sub) (sameLeaves _ _) j hg
            exact hw.trans (by simpa [sameLeaves] using z)
        exact (rule.fork i q).trans (Nat.add_le_add (each false l (by omega) good.1) (each true r (by omega) good.2))
  exact fun t => count (leaves t) t rfl

end PCX150.Sparse

namespace PCX150
open PEqualNP.ProofComplexity
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


end PCX150

namespace PCX150.Chart48
open PCX150.SmallChart
abbrev G := Fin 5
abbrev ID := Fin 144
def vars : Array Nat := #[205163979670851,205150245839376,148896472117776,204132939153921,188667281092896]
def samp : Array Nat := #[2162696249821217618215137618282995761805161463866772981130851447475637340800225444037497314043350055714587078,2124316537260600494142276225985762821656081576118724669733229319233394180619356984075646928639684086222827521,2198800641771726253250707320465942554279185016594663310005348741055887738735616140179568159580534921302900994,2162705622156956155524194547248590888843364879373837413591619490913386944305282635826338639645551936198148290,1751495602169449824780452133844769261384469437309448667367654039628175301793608141872959730519764771391422465]
def tags : Array Nat := #[876760607630163527048800059361281,838692637284318602340861100524608,875377867290620207656823162997792,877989843170706854949760033458208,626749673298397928820772366813216]
def rm : Array Nat := #[4296015872,1125902054326274,2155872258,309238177792,12890144768,1125970773803010,1125970782191618,281479272726593,9183121115218432,282575562080321,3231711235,282578784354369,282575564177473,4503917454958720,282853662261313,2322172853895240,36030450582421600,36310276291690593,4503986174435456,4503676940984450,36311375803318369,582090322712985730,4785384918097921,2603647830605897,36311100925411425,38350969872859240,36312200437039201,2330977826258952,281789586743361,36311100925485153,4785384918098113,11821949374219020,4516905440780430,595604368724987922,4503989410865283,14500669728268293,7116327023042761,329045085298696417,326590700467601640,230673451842052101,14500669728269253,331376049949597929,7683709651673549,12099026320933644,13700304749503119,16831647554528205,1094567102241287871,1152921504606846975]
def weight : Array Nat := #[2,3,3,4,2,4,5,5,5,5,3,6,6,6,7,7,7,6,7,7,7,8,8,8,7,8,8,9,9,8,9,11,9,12,10,13,13,13,13,14,14,17,17,15,19,23,29,43]
def words : Array Nat := #[0,1,2,3,4,5,17,25,33,41,10,26,34,42,19,35,43,44,37,81,209,273,337,153,281,345,353,297,202,266,330,154,282,346,354,298,83,275,339,355,299,300,1617,2129,2641,1233,2257,2769,2833,2385,665,2201,2713,2841,2393,2401,1226,2250,2762,2826,2378,666,2202,2714,2842,2394,2402,2131,2643,2835,2387,2403,9809,18001,22097,22609,19025,5329,17617,21713,22737,19153,19217,17049,21145,22681,19097,19225,5322,17610,21706,22730,19146,19210,17050,21146,22682,19098,19226,22611,19027,19219,42577,140881,173649,181841,153169,153681,136401,169169,181457,152785,153809,180889,152217,153753,136394,169162,181450,152778,153802,180890,152218,153754,153683,1091153,1353297,1451601,1222225,1230417,1447121,1217745,1230033,1229465,1447114,1217738,1230026,1229466,11576913,9741905,9840209,9835729,9835722,78685777]
def lab : Array Nat := #[0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,20,20,21,21]
def cols : Array Nat := #[729761264001255936,364805838240031872,58354402365559104,326590701323239464,595657351441551378,230673451842052101,90657122719368468,180640694878079073,881623687009141386,5912485265682627,12099026304418572,1134909993020230704]
def bound : Array Nat := #[538268735057276698148032818307065219936903198283014953358923956780677536819942850242890304553205760,538269256538488514384162552750189572805310722771986366288709298208732214187473396149793011380771008,538269778019701066356742971929272630059099925246598489253571807271743014621838164853091315805585471,538270299500912616876428557405068801697147823820519045138883596591678061623432465554701140674723843,538270820982124235337354173631657741024772027126547668620610255679296665656388669061398013175382020,538271342463336052047768193837752383089907752242692546395786392885910448225350855798839468521148289,538271863944547936346488009801479095892403172781576928675046442073576755926889218454545644415618945,538272385425760867626625862102760796386165762760920307356322518129707788065031296522250603579031559,538272905156500766443108513065369317041708568762534647923702093842356658266821308496139630627913791,538273428388183589711373858776294641910844417093252293990782242762315493497379666978810459928388483,538273949869395936318810126124100462754281549497740041727918895024651978388697535735100951101505599,538274471350608276166304277679751488401409621333068263696017456929647368976690433886918836004831243,538274992831819242604754295200724777820590550881968340029989257580498113508706476668366657917297539,538275514313031127374979499056138697359851683567541417956217325286840594361260696013447673142034445,538276035794243360747015885429852572826124209140990971426163743953392211972732415128892094171561998,538276842588900287613713764195706676224167049845152584474167342240539335744210017514414202831224847,8210935981313464207303642673531011776159086553216937335900125457581773914996661784973199784971059216,73272902932604610420036870157536400652326913083632616291714030090161894913919217964180355688980004881,538278121719090549454486549973880444008146386409356623949437032032239010812143567593609866739957778,538278643200302728876672835513910814295334555055533520541678671153582469755608023022124445167763475,73272905018529455885907656347384293463288078410724482762143185079522703273336082389609338014490673172,12021642714081996388115187691064001916994023436508337678951193881981524391710541908729120294496652232,538280207643938154942151045426220907057630261879816340006700076160044125805351317254509978543194958,538281014437471369034359396148358135313611030222761666854009352164581083121773775918976271943450647,8210773800657187842450702043769927230216753452307810061477961553333273806060039908740084927428542488,73272907389770475404473780227855937336046598631729832801657986665000761855547474412156408208504635417,8210741468822175688784375851528141942691348369779297262523972806564205865176036145723393182467604506,538282829913949782613786499879044261729609061098369591742339269591925191358496908223301606507012762,538283336531209696326906865238153228120465319417122620678190038468416364577908582197572683783217879,57990787607173543562964587864197087933400489757722923477508596161155880340703112137034694538963173405,538284379493634094889820409844606642196500385101432414835725334096532331681857928452251746026129177,538284899956389227892558916924470067998783345048157735682045083732086557518399686318372247782424785,538285612073333914880439379573525300777569415246909905287533586520290764107308491195536593292083232,30190551819297157306895627107820570633510844730208030420894227934123905195516278548573050516125466772,538286465418481162181876574068358400235743343515935276248182275721255525554892449177559713509868126,538287040467347836282951397718802103372519239556242708545061451746137386737772233427339712742507354,538287508670333174588038310469759840636637503503260196428721042124965305636376612286265543067942948,4990481836010083953925990327928264829233735805677075544831425634814654689694087535748976141975666725,4992350824958676661032061808363270825607902639635285870905867626945799892419716024126815405891108902,11474540664384530795261838669345740386371263272951364135411814884895652401053664882877597379849396571,538289788556211066945809738712428459099483457395296971423289575173983144375503294890033704447744288,4989684491526541388212128843925278606681550665566138576901749021922556716775820252848002954007920681,538290664624789112969384686648112981552147623688536516881619820731295230805674216305742156875677738,538291225208098235941059780703506472209378715478932681606304621642847993992222289527826165924201634,538291870566129617220051072053606863194104989936617742843622682016438733782703720838793512483216162,538292329154972782007624731635222049671277488321919676363157486963497117172870256396228987355217962,33654634875485059881322937237765257811134583756154723274761472150882025045230030582607602805856913707,6348845023310766790018526439914031813924028716646621184500080589437918446272198264846895864862065838]

def bits (s : Nat) : Set Sample := {p : Sample | s.testBit p.val = true}
def geo : Domain :=
  ⟨fun r v => cols[v.val]!.testBit r.val,fun r => Fin.ofNat 22 lab[r.val]!⟩
def vs (g : G) (v : Var) : Var := Fin.ofNat 12 ((vars[g.val]! >>> (4*v.val)) % 16)
def rs (g : G) (r : Sample) : Sample := Fin.ofNat 60 ((samp[g.val]! >>> (6*r.val)) % 64)
def ls (g : G) (k : Tag) : Tag := Fin.ofNat 22 ((tags[g.val]! >>> (5*k.val)) % 32)
theorem gInv : ∀ g : G, (∀ q : Var, vs g (vs g q)=q) ∧
    (∀ r : Sample,rs g (rs g r) = r) ∧ (∀ k : Tag,ls g (ls g k)=k) := by decide +kernel
theorem gRule : ∀ g : G, ∀ r : Sample,
    geo.tag (rs g r) = ls g (geo.tag r) ∧
    ∀ v : Var, geo.val (rs g r) (vs g v) = geo.val r v := by decide +kernel
def gen (g : G) : Aut geo where
  s := ⟨rs g,rs g,(gInv g).2.1,(gInv g).2.1⟩
  v := ⟨vs g,vs g,(gInv g).1,(gInv g).1⟩
  a := ⟨ls g,ls g,(gInv g).2.2,(gInv g).2.2⟩
  bit r v := (gRule g r).2 v
  label r := (gRule g r).1

def assemble (w : Nat) : Nat → Aut geo
  | 0 => Aut.unit geo
  | d+1 =>
    let t := (w >>> (3*d)) % 8
    let prev := assemble w d
    if t=0 then prev else prev.thenDo (gen (Fin.ofNat 5 (t-1)))

def backward (w : Nat) : Nat → Sample → Sample
  | 0,r => r
  | d+1,r =>
    let t := (w >>> (3*d)) % 8
    if t=0 then backward w d r else backward w d (rs (Fin.ofNat 5 (t-1)) r)

theorem backApply (w d : Nat) (r : Sample) : (assemble w d).s.symm r = backward w d r := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih =>
    simp only [assemble,backward]
    split
    · apply ih
    · exact ih _

def orient (o : ID) := assemble words[o.val]! 9
def slot (k : Key) (q : Var) (b : Bool) : Nat :=
  (bound[k.val]! >>> (14*(2*q.val+b.toNat))) % 16384
def index (code : Nat) : Key := Fin.ofNat 48 (code%64)
def turn (code : Nat) : ID := Fin.ofNat 144 (code/64)
def mono (code : Nat) : Tag := Fin.ofNat 22 (code/64)
def node (k : Key) := bits rm[k.val]!
def next (k : Key) (q : Var) (b : Bool) : Option Key :=
  let d := slot k q b
  if d%64=63 then none else some (index d)

def pointTest (k : Key) (q : Var) (b : Bool) (r : Sample) : Prop :=
  let d := slot k q b
  let keep := (rm[k.val]!.testBit r.val && (geo.val r q == b))
  if d % 64 = 63 then keep = true → geo.tag r = mono d
  else keep = rm[(index d).val]!.testBit (backward words[(turn d).val]! 9 r).val
instance (k : Key) (q : Var) (b : Bool) (r : Sample) : Decidable (pointTest k q b r) := by
  unfold pointTest; dsimp only; split <;> infer_instance

theorem allSteps : ∀ (k : Key) (q : Var) (b : Bool) (r : Sample), pointTest k q b r := by decide +kernel
theorem allCost : ∀ (k : Key) (q : Var), weight[k.val]! ≤ ((next k q false).map (fun (j : Key) => weight[j.val]!)).getD 1 +
    ((next k q true).map (fun (j : Key) => weight[j.val]!)).getD 1 := by decide +kernel

def witnessRow (k : Key) (a : Tag) : Prop :=
  ∃ r : Sample, rm[k.val]!.testBit r.val = true ∧ geo.tag r ≠ a
instance (k : Key) (a : Tag) : Decidable (witnessRow k a) := by unfold witnessRow; infer_instance
theorem spread : ∀ k a, witnessRow k a := by decide +kernel

def chart : Chart geo where
  state := node
  wt k := weight[k.val]!
  root := 47
  start := by
    ext r
    have h : ∀ p : Sample, rm[47]!.testBit p.val = true := by decide +kernel
    exact iff_of_true (h r) trivial
  rich k := by
    rintro ⟨a,ha⟩
    obtain ⟨r,inside,ne⟩ := spread k a
    exact ne (ha r inside)
  next := next
  proper k q b := by
    let d := slot k q b
    have facts := allSteps k q b
    by_cases hom : d%64=63
    · simp only [next,show slot k q b % 64 = 63 from hom,ite_true]
      refine ⟨mono d,?_⟩
      intro r h
      have both : (rm[k.val]!.testBit r.val && (geo.val r q == b)) = true := by
        have hl : rm[k.val]!.testBit r.val = true := h.1
        simp [hl,h.2]
      have e := facts r
      change (if d%64=63 then _ else _) at e
      rw [if_pos hom] at e
      exact e both
    · simp only [next,show ¬slot k q b % 64 = 63 from hom,ite_false]
      refine ⟨orient (turn d),?_⟩
      ext r
      have e := facts r
      change (if d%64=63 then _ else _) at e
      rw [if_neg hom] at e
      change (_ ∧ geo.val r q = b) ↔ (rm[(index d).val]!.testBit ((assemble words[(turn d).val]! 9).s.symm r).val = true)
      rw [backApply,←e]
      simp [node,bits]
  subadd := allCost

theorem rootWeight : chart.wt chart.root = 43 := by decide +kernel
end PCX150.Chart48

namespace PCX150.Chart48
open PCX150.SmallChart
set_option maxRecDepth 10000
def alongCode : Array Nat := #[21542142465,38789383680,56036622346,68971138567,73015430152,303041801,94842913043,107776907011,111687505156,4749596165,129337398018,142270930716,146064540701,9179301150,163831546660,167554327832,13556327961,17870299674,176180175643,189702736390,202635619626,206262110251,26594969900,224196888370,227751244559,30971343888,35285970961,236377747730,250065074187,253574589196,43960118285,271624047421,275063258681,48336027450,52651102523,283690209852,293185860110,296591691587,61308080196,65616823605,305212311094,77599294007,319053580308,322446105877,82884304406,340612551757,343934324297,87259762506,91575294539,352561732428,362174817303,365463214163,100232272212,104540558631,374083376680,116406047273,388044954712,391313709344,121804577313,126120315682,399941323811,409601333279,412839387230,134773875039,139085373531,421462761820,150900713821,425811923749,156302791718,160614590307,434435598436,172455716183,448408332902,451679053614,182169921583,186485652272,460306660401,469966677549,473204731500,195139219309,199450717801,481828106090,211266058091,486177260339,216668128308,220979934577,494800942706,232821060423,504464031032,507752429940,242521487989,246830298688,516373116737,258695785282,520718873662,264044311871,268356108409,529342546298,280250973048,289851142469,533724820038,301813417852,543268818248,546674657661,311391046270,315701821264,555297308753,327684283730,559643065678,332915834447,337227632770,568266740099,349239936129,358722200405,572648547414,370801923973,577010228825,380230328154,384542137222,585633913991,396669847650,406031926880,590010943329,418229084809,431166686565,594424392807,440426392936,444738201994,603048077963,457035189360,466229496430,607426612079,478594429069,491531369587,500607646070,611857431159,513090025614,526024216187,539278869119,616303133568,551895466383,564830506884,582078138760,599325052300]
def invName : Array Nat := #[0,1,2,3,4,5,10,7,8,9,6,14,12,13,11,15,16,18,17,19,36,29,30,28,24,25,27,26,23,21,22,31,37,38,35,34,20,32,33,40,39,41,50,43,44,61,67,68,60,59,42,57,58,54,53,55,56,51,52,49,48,45,62,63,70,69,66,46,47,65,64,71,88,83,84,76,75,77,94,95,100,99,93,73,74,92,91,87,72,89,90,86,85,82,78,79,97,96,101,81,80,98,102,116,117,114,113,107,108,109,122,121,124,106,105,120,103,104,119,118,115,111,110,123,112,125,126,135,134,133,131,130,137,129,128,127,136,132,139,138,142,141,140,143]
def follow (o : ID) (g : G) : ID := Fin.ofNat 144 ((alongCode[o.val]! >>> (8*g.val)) % 256)
def inverse (o : ID) : ID := Fin.ofNat 144 invName[o.val]!

theorem followBoard : ∀ (o : ID) (g : G) (r : Sample),
    backward words[(follow o g).val]! 9 r = backward words[o.val]! 9 (rs g r) := by decide +kernel
theorem invertBoard : ∀ (o : ID) (r : Sample),
    backward words[(inverse o).val]! 9 (backward words[o.val]! 9 r) = r := by decide +kernel
theorem zeroBoard : ∀ (r : Sample), backward words[0]! 9 r = r := by decide +kernel

theorem followAct (o : ID) (g : G) (s : Set Sample) :
    acted (gen g) (acted (orient o) s) = acted (orient (follow o g)) s := by
  ext r
  change ((assemble words[o.val]! 9).s.symm (rs g r) ∈ s) ↔
    ((assemble words[(follow o g).val]! 9).s.symm r ∈ s)
  rw [backApply,backApply,followBoard]

theorem zeroAct (s : Set Sample) : acted (orient 0) s = s := by
  ext r
  change ((assemble words[0]! 9).s.symm r ∈ s) ↔ r ∈ s
  rw [backApply,zeroBoard]

theorem invertAct (o : ID) (s : Set Sample) : acted (orient o) (acted (orient (inverse o)) s) = s := by
  ext r
  change ((assemble words[(inverse o).val]! 9).s.symm ((assemble words[o.val]! 9).s.symm r) ∈ s) ↔ r ∈ s
  rw [backApply,backApply,invertBoard]

theorem composeAct (o p : ID) (s : Set Sample) :
    ∃ u : ID, acted (orient o) (acted (orient p) s) = acted (orient u) s := by
  have go (w d : Nat) : ∃ u : ID, acted (assemble w d) (acted (orient p) s) = acted (orient u) s := by
    induction d with
    | zero => exact ⟨p,rfl⟩
    | succ d ih =>
      obtain ⟨u,hu⟩ := ih
      simp only [assemble]
      split
      · exact ⟨u,hu⟩
      · rename_i h
        let g := Fin.ofNat 5 (((w >>> (3*d))%8)-1)
        exact ⟨follow u g,by rw [←actedChain,hu]; exact followAct u g s⟩
  exact go _ _

theorem nextName (k : Key) (q : Var) (b : Bool) :
    plain geo (branch geo (node k) q b) ∨ ∃ (j : Key) (o : ID), branch geo (node k) q b = acted (orient o) (node j) := by
  let d := slot k q b
  have facts := allSteps k q b
  by_cases hom : d%64=63
  · left
    have h := chart.proper k q b
    change (match next k q b with | none => _ | some j => _) at h
    rw [show next k q b = none by simp [next,show slot k q b % 64 = 63 from hom]] at h
    exact h
  · right
    refine ⟨index d,turn d,?_⟩
    ext r
    have e := facts r
    change (if d%64=63 then _ else _) at e
    rw [if_neg hom] at e
    change (_ ∧ geo.val r q = b) ↔ (rm[(index d).val]!.testBit ((assemble words[(turn d).val]! 9).s.symm r).val = true)
    rw [backApply,←e]
    simp [node,bits]

def named (s : Set Sample) := plain geo s ∨ ∃ (k : Key) (o : ID), s = acted (orient o) (node k)

theorem namedBranch {s : Set Sample} (h : named s) (q : Var) (b : Bool) : named (branch geo s q b) := by
  rcases h with ⟨a,mono⟩ | ⟨k,o,rfl⟩
  · exact Or.inl ⟨a,fun r hr => mono r hr.1⟩
  · rw [branchAct]
    rcases nextName k ((orient o).v.symm q) b with mono | ⟨j,p,eq⟩
    · exact Or.inl (actedPlain _ mono)
    · obtain ⟨u,hu⟩ := composeAct o p (node j)
      exact Or.inr ⟨j,u,by rw [eq,hu]⟩

theorem allNamed (qs : List (Var × Bool)) :
    named (qs.foldl (fun s q => branch geo s q.1 q.2) Set.univ) := by
  have walk (xs : List (Var × Bool)) (s : Set Sample) (h : named s) :
      named (xs.foldl (fun t q => branch geo t q.1 q.2) s) := by
    induction xs generalizing s with
    | nil => exact h
    | cons a tail ih => exact ih _ (namedBranch h _ _)
  apply walk
  exact Or.inr ⟨47,0,by rw [zeroAct]; exact chart.start.symm⟩

end PCX150.Chart48

namespace PCX150.PrivateGame
open PEqualNP.ProofComplexity
open PCX150.SmallChart (Sample Var Tag Key Domain Aut acted branch plain)
open PCX150.Chart48 (geo)
open PCX150.Sparse (TestTree Triple Valid box half)

def wire (v : V) : Var := Fin.ofNat 12 (port v)
theorem coord : ∀ p v, geo.val p (wire v) = assignment p v := by decide +kernel
def falsifiers (C : Cl) : Set Sample := {p | ¬ ClauseSat (assignment p) C}
theorem emptyMask : falsifiers ∅ = Set.univ := by
  ext p
  simp [falsifiers,ClauseSat]
theorem insertMask (C : Cl) (l : Literal V) :
    falsifiers (insert l C) = branch geo (falsifiers C) (wire l.1) (!l.2) := by
  ext p
  change (¬ ClauseSat (assignment p) (insert l C)) ↔ (¬ ClauseSat (assignment p) C) ∧ geo.val p (wire l.1) = (!l.2)
  rw [coord]
  have test : assignment p l.1 = (!l.2) ↔ assignment p l.1 ≠ l.2 := by
    cases assignment p l.1 <;> cases l.2 <;> decide
  rw [test]
  unfold ClauseSat
  simp only [Finset.mem_insert]
  aesop

theorem clauseNamed (C : Cl) : Chart48.named (falsifiers C) := by
  induction C using Finset.induction_on with
  | empty => rw [emptyMask]; exact Chart48.allNamed []
  | insert l C fresh ih => rw [insertMask]; exact Chart48.namedBranch ih _ _

theorem labelBook : ∀ n ∈ labelMasks.toList, ∃ k : Tag, ∀ r : Sample,
    n.testBit r.val = true → geo.tag r = k := by decide +kernel

theorem rawOwner {C : Cl} (ax : C ∈ PHP 4 3) : plain geo (falsifiers C) := by
  obtain ⟨k,tk⟩ := labelBook _ (axListed ax)
  exact ⟨k,fun p hp => tk p ((privateBit C p).2 hp)⟩

theorem treeRaw {A : Cl} {i : Nat} (pa : ResTree (PHP 4 3) A i) :
    ∃ t : TestTree, Sparse.leaves t = i+1 ∧
      Valid geo.val (box geo.tag ∅ ∅) t (falsifiers A) := by
  apply Sparse.transferTree (F := PHP 4 3) wire geo.val assignment coord
  · intro C ch
    obtain ⟨k,hk⟩ := rawOwner ch
    exact ⟨Sum.inl k,fun p hp => hk p hp⟩
  · exact pa
  · exact fun _ hp => hp

theorem treeOne {A B : Cl} {j : Nat} (pb : ResTree (insert A (PHP 4 3)) B j) :
    ∃ t : TestTree, Sparse.leaves t=j+1 ∧
      Valid geo.val (box geo.tag (falsifiers A) ∅) t (falsifiers B) := by
  apply Sparse.transferTree (F := insert A (PHP 4 3)) wire geo.val assignment coord
  · intro C ch
    rcases ch with rfl | ax
    · exact ⟨Sum.inr 0,fun p hp => by simpa [box,falsifiers] using hp⟩
    · obtain ⟨k,hk⟩ := rawOwner ax
      exact ⟨Sum.inl k,fun p hp => hk p hp⟩
  · exact pb
  · exact fun _ hp => hp

theorem treeTwo {A B : Cl} {k : Nat} (pc : ResTree (insert B (insert A (PHP 4 3))) ∅ k) :
    ∃ t : TestTree, Sparse.leaves t=k+1 ∧
      Valid geo.val (box geo.tag (falsifiers A) (falsifiers B)) t Set.univ := by
  apply Sparse.transferTree (F := insert B (insert A (PHP 4 3))) wire geo.val assignment coord
  · intro C ch
    rcases ch with rfl | rfl | ax
    · exact ⟨Sum.inr 1,fun p hp => by simpa [box,falsifiers] using hp⟩
    · exact ⟨Sum.inr 0,fun p hp => by simpa [box,falsifiers] using hp⟩
    · obtain ⟨i,hi⟩ := rawOwner ax
      exact ⟨Sum.inl i,fun p hp => hi p hp⟩
  · exact pc
  · intro p _ hp; simpa [ClauseSat] using hp


abbrev Choice := Fin 49
def candidate (a : Choice) : Set Sample := if a.val=0 then ∅ else Chart48.bits (Chart48.rm[a.val-1]!)
def price (a : Choice) := if a.val=0 then 0 else Chart48.weight[a.val-1]!
def code (k : Key) : Choice := ⟨k.val+1,by have := k.isLt; omega⟩
theorem priced (k : Key) : price (code k) = Chart48.chart.wt k := by simp [price,code,Chart48.chart]
theorem coded (k : Key) : candidate (code k) = Chart48.node k := by simp [candidate,code,Chart48.node]
theorem candidateZero : candidate 0 = ∅ := by rfl

def Match (real cur : Set Sample) := cur ⊆ real ∧ (real ⊆ cur ∨ plain geo real)
theorem matchSame (r : Set Sample) : Match r r := ⟨(fun _ h => h),Or.inl (fun _ h => h)⟩
theorem match0 {r : Set Sample} (h : plain geo r) : Match r ∅ := ⟨Set.empty_subset _,Or.inr h⟩

theorem actEmpty (f : Aut geo) : acted f (∅ : Set Sample) = ∅ := rfl
theorem actUniv (f : Aut geo) : acted f (Set.univ : Set Sample) = Set.univ := rfl

theorem twiceInv (o : Chart48.ID) (s : Set Sample) :
    acted (Chart48.orient (Chart48.inverse o)) (acted (Chart48.orient o) s) = s := by
  have inj (f : Aut geo) : Function.Injective (acted f) := by
    intro u v h
    ext r
    have e := Set.ext_iff.mp h (f.s r)
    simpa [SmallChart.acted] using e
  apply inj (Chart48.orient o)
  exact Chart48.invertAct o _

theorem namesPair {a b : Set Sample} (ha : Chart48.named a) (hb : Chart48.named b) :
    ∃ (f : Chart48.ID) (x y : Choice) (o : Chart48.ID),
      Match (acted (Chart48.orient f) a) (candidate x) ∧
      Match (acted (Chart48.orient f) b) (acted (Chart48.orient o) (candidate y)) := by
  have oneB (f : Chart48.ID) : ∃ y o, Match (acted (Chart48.orient f) b) (acted (Chart48.orient o) (candidate y)) := by
    rcases hb with hp | ⟨j,q,rfl⟩
    · exact ⟨0,0,by rw [candidateZero,actEmpty]; exact match0 (SmallChart.actedPlain _ hp)⟩
    · obtain ⟨n,eq⟩ := Chart48.composeAct f q (Chart48.node j)
      exact ⟨code j,n,by rw [coded,eq]; exact matchSame _⟩
  rcases ha with pure | ⟨j,q,rfl⟩
  · obtain ⟨y,o,hm⟩ := oneB 0
    exact ⟨0,0,y,o,by rw [candidateZero]; exact match0 (SmallChart.actedPlain _ pure),hm⟩
  · obtain ⟨y,o,hm⟩ := oneB (Chart48.inverse q)
    exact ⟨Chart48.inverse q,code j,y,o,by rw [twiceInv,coded]; exact matchSame _,hm⟩

theorem canMove (f : Aut geo) (s x y a b : Set Sample) (t : TestTree)
    (h : Valid geo.val (box geo.tag x y) t s)
    (ax : Match (acted f x) a) (byy : Match (acted f y) b) :
    Valid geo.val (box geo.tag a b) (Sparse.renamed f t) (acted f s) := by
  apply Sparse.moveTree f h
  intro i
  cases i with
  | inl i =>
    refine ⟨Sum.inl (f.a i),?_⟩
    intro p _ h
    change geo.tag p = i at h
    exact (f.label p).trans (congrArg f.a h)
  | inr i =>
    fin_cases i
    · rcases ax.2 with sub | ⟨j,pure⟩
      · refine ⟨Sum.inr 0,?_⟩
        intro p hp hx
        have h0 : p ∈ x := by simpa [box] using hx
        have z := sub (show f.s p ∈ acted f x by simpa [SmallChart.acted] using h0)
        simpa [box] using z
      · refine ⟨Sum.inl j,?_⟩
        intro p hp hx
        have h0 : p ∈ x := by simpa [box] using hx
        exact pure _ (by simpa [SmallChart.acted] using h0)
    · rcases byy.2 with sub | ⟨j,pure⟩
      · refine ⟨Sum.inr 1,?_⟩
        intro p hp hx
        have h0 : p ∈ y := by simpa [box] using hx
        have z := sub (show f.s p ∈ acted f y by simpa [SmallChart.acted] using h0)
        simpa [box] using z
      · refine ⟨Sum.inl j,?_⟩
        intro p hp hx
        have h0 : p ∈ y := by simpa [box] using hx
        exact pure _ (by simpa [SmallChart.acted] using h0)

theorem shrink {bit : Sample → Var → Bool} {term : Sparse.Box → Set Sample}
    {s d : Set Sample} {t : TestTree} (h : Valid bit term t s) (inc : d ⊆ s) : Valid bit term t d :=
  Sparse.smaller h inc (fun i => ⟨i,fun _ _ hp => hp⟩)

def converted : TestTree → SmallChart.Tree
  | .leaf => .leaf
  | .cut q l r => .node q (converted l) (converted r)
theorem ccost (t : TestTree) : SmallChart.leaves (converted t) = Sparse.leaves t := by
  induction t with
  | leaf => rfl
  | cut q l r hl hr => simp [converted,SmallChart.leaves,Sparse.leaves,hl,hr]

theorem noExtra {s : Set Sample} {t : TestTree} (h : Valid geo.val (box geo.tag ∅ ∅) t s) :
    SmallChart.rawValid geo (converted t) s := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,hi⟩ := h
    cases i with
    | inl i => exact ⟨i,fun _ hp => hi hp⟩
    | inr i =>
      refine ⟨0,?_⟩
      intro p hp
      have z := hi hp
      fin_cases i <;> simp [box] at z
  | cut q l r hl hr => exact ⟨hl h.1,hr h.2⟩

theorem charge (a : Choice) (t : TestTree) (h : Valid geo.val (box geo.tag ∅ ∅) t (candidate a)) :
    price a ≤ Sparse.leaves t := by
  by_cases z : a.val=0
  · simp [price,z]
  · let k : Key := ⟨a.val-1,by have := a.isLt; omega⟩
    have eq : code k = a := by apply Fin.ext; dsimp [code,k]; omega
    rw [←eq,coded] at h
    rw [←eq,priced,←ccost]
    exact SmallChart.rawLower Chart48.chart (converted t) k (SmallChart.Aut.unit _) (noExtra h)

def scoreClaim := ∀ (a b : Choice) (o : Chart48.ID) (t u : TestTree),
    Valid geo.val (box geo.tag (candidate a) ∅) t (acted (Chart48.orient o) (candidate b)) →
    Valid geo.val (box geo.tag (candidate a) (acted (Chart48.orient o) (candidate b))) u Set.univ →
    41 ≤ price a + Sparse.leaves t + Sparse.leaves u

theorem allThree (test : scoreClaim) {A B : Cl} {i j k : Nat}
    (pa : ResTree (PHP 4 3) A i) (pb : ResTree (insert A (PHP 4 3)) B j)
    (pc : ResTree (insert B (insert A (PHP 4 3))) ∅ k) : 38 ≤ i+j+k := by
  obtain ⟨f,a,b,o,ma,mb⟩ := namesPair (clauseNamed A) (clauseNamed B)
  let ren := Chart48.orient f
  have emp : Match (acted ren ∅) ∅ := by rw [actEmpty]; exact matchSame _
  obtain ⟨x,hx,vx⟩ := treeRaw pa
  obtain ⟨y,hy,vy⟩ := treeOne pb
  obtain ⟨z,hz,vz⟩ := treeTwo pc
  have first := charge a (Sparse.renamed ren x) (shrink (canMove ren _ _ _ _ _ _ vx emp emp) ma.1)
  have snd := shrink (canMove ren _ _ _ _ _ _ vy ma emp) mb.1
  have third := canMove ren _ _ _ _ _ _ vz ma mb
  rw [actUniv] at third
  have total := test a b o _ _ snd third
  simp only [Sparse.sameLeaves,hx,hy,hz] at first total
  omega

end PCX150.PrivateGame
namespace PCX150.Bands

structure Part where
  destination : Nat
  distance : Nat
  down : Bool
  deriving Inhabited, DecidableEq

def readBit (p : Part) (r : Nat) : Option Nat :=
  if p.down then some (p.distance + r) else
  if p.distance ≤ r then some (r-p.distance) else none

def applyPart (p : Part) (m : Nat) : Nat :=
  p.destination &&& (if p.down then m >>> p.distance else m <<< p.distance)

def roll (ps : List Part) (m : Nat) : Nat :=
  ps.foldr (fun p t => applyPart p m ||| t) 0

theorem testPart (p : Part) (m r : Nat) :
    (applyPart p m).testBit r = (p.destination.testBit r &&
      ((readBit p r).map (fun x => m.testBit x)).getD false) := by
  by_cases b : p.down = true
  · simp [applyPart,readBit,b,Nat.testBit_and,Nat.testBit_shiftRight,Nat.add_comm]
  · by_cases d : p.distance ≤ r <;>
      simp [applyPart,readBit,b,d,Nat.testBit_and,Nat.testBit_shiftLeft]

theorem rollBit (ps : List Part) (m r : Nat) :
    (roll ps m).testBit r = true ↔
      ∃ p ∈ ps, p.destination.testBit r = true ∧ ∃ x, readBit p r = some x ∧ m.testBit x = true := by
  induction ps with
  | nil => simp [roll]
  | cons p ps ih =>
    change ((applyPart p m ||| roll ps m).testBit r = true) ↔ _
    rw [Nat.testBit_or,Bool.or_eq_true,testPart,Bool.and_eq_true,ih]
    simp only [List.mem_cons]
    cases h : readBit p r with
    | none => simp [h]
    | some k => simp [h]

def routes (ps : List Part) (r src : Nat) : Prop :=
  (∃ p ∈ ps, p.destination.testBit r = true) ∧
  ∀ p ∈ ps, p.destination.testBit r = true → readBit p r = some src

instance (ps : List Part) (r src : Nat) : Decidable (routes ps r src) := by
  unfold routes
  infer_instance

theorem rollCorrect {ps : List Part} {r src : Nat} (h : routes ps r src) (m : Nat) :
    (roll ps m).testBit r = m.testBit src := by
  apply Bool.eq_iff_iff.mpr
  rw [rollBit]
  constructor
  · rintro ⟨p,mem,y,x,hx,val⟩
    rw [h.2 p mem y] at hx
    have e := Option.some.inj hx
    simpa [e] using val
  · intro bit
    obtain ⟨p,mem,y⟩ := h.1
    exact ⟨p,mem,y,src,h.2 p mem y,bit⟩

end PCX150.Bands

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart PCX150.Bands
def quickGen (g : Nat) (m : Nat) : Nat :=
  match g with
  | 0 => ((m <<< 6) &&& 4032) ||| ((m <<< 2) &&& 229739669779120128) ||| ((m <<< 1) &&& 576601524162699264) ||| (m &&& 844631138893824) ||| ((m >>> 1) &&& 288300762081349632) ||| ((m >>> 2) &&& 57434917444780032) ||| ((m >>> 6) &&& 63)
  | 1 => ((m <<< 6) &&& 258048) ||| ((m <<< 3) &&& 4194304) ||| ((m <<< 2) &&& 868280810792288256) ||| ((m <<< 1) &&& 36037595259469866) ||| (m &&& 13514098222301184) ||| ((m >>> 1) &&& 18018797629734933) ||| ((m >>> 2) &&& 217070202698072064) ||| ((m >>> 3) &&& 524288) ||| ((m >>> 6) &&& 4032)
  | 2 => ((m <<< 6) &&& 16515072) ||| ((m <<< 4) &&& 270281964446023680) ||| ((m <<< 3) &&& 1040) ||| ((m <<< 2) &&& 2340) ||| ((m <<< 1) &&& 563087425929216) ||| (m &&& 864902286227275776) ||| ((m >>> 1) &&& 281543712964608) ||| ((m >>> 2) &&& 585) ||| ((m >>> 3) &&& 130) ||| ((m >>> 4) &&& 16892622777876480) ||| ((m >>> 6) &&& 258048)
  | 3 => ((m <<< 12) &&& 281406257233920) ||| ((m <<< 2) &&& 3195660) ||| ((m <<< 1) &&& 768426686428612640) ||| ((m >>> 1) &&& 384213343214306320) ||| ((m >>> 2) &&& 798915) ||| ((m >>> 12) &&& 68702699520)
  | 4 => ((m <<< 12) &&& 1152640029630136320) ||| ((m <<< 2) &&& 12782640) ||| ((m <<< 1) &&& 45802332290) ||| ((m >>> 1) &&& 22901166145) ||| ((m >>> 2) &&& 3195660) ||| ((m >>> 12) &&& 281406257233920)
  | _ => m

def useWord (w : Nat) : Nat → Nat → Nat
  | 0,m => m
  | d+1,m =>
    let z := (w >>> (3*d))%8
    let t := useWord w d m
    if z=0 then t else quickGen (z-1) t

def permute (o m : Nat) := useWord words[o]! 9 m

def parts (g : G) : List Part :=
  match g.val with
  | 0 => [⟨4032,6,false⟩,⟨229739669779120128,2,false⟩,⟨576601524162699264,1,false⟩,⟨844631138893824,0,true⟩,⟨288300762081349632,1,true⟩,⟨57434917444780032,2,true⟩,⟨63,6,true⟩]
  | 1 => [⟨258048,6,false⟩,⟨4194304,3,false⟩,⟨868280810792288256,2,false⟩,⟨36037595259469866,1,false⟩,⟨13514098222301184,0,true⟩,⟨18018797629734933,1,true⟩,⟨217070202698072064,2,true⟩,⟨524288,3,true⟩,⟨4032,6,true⟩]
  | 2 => [⟨16515072,6,false⟩,⟨270281964446023680,4,false⟩,⟨1040,3,false⟩,⟨2340,2,false⟩,⟨563087425929216,1,false⟩,⟨864902286227275776,0,true⟩,⟨281543712964608,1,true⟩,⟨585,2,true⟩,⟨130,3,true⟩,⟨16892622777876480,4,true⟩,⟨258048,6,true⟩]
  | 3 => [⟨281406257233920,12,false⟩,⟨3195660,2,false⟩,⟨768426686428612640,1,false⟩,⟨384213343214306320,1,true⟩,⟨798915,2,true⟩,⟨68702699520,12,true⟩]
  | 4 => [⟨1152640029630136320,12,false⟩,⟨12782640,2,false⟩,⟨45802332290,1,false⟩,⟨22901166145,1,true⟩,⟨3195660,2,true⟩,⟨281406257233920,12,true⟩]
  | _ => []
theorem paths : ∀ (g : G) (r : Sample), routes (parts g) r.val (rs g r).val := by decide +kernel
theorem genAsRoll (g : G) (m : Nat) : quickGen g.val m = roll (parts g) m := by
  fin_cases g <;> simp [quickGen,parts,roll,applyPart,Nat.and_comm,Nat.or_assoc]

theorem genExact (g : G) (m : Nat) (r : Sample) :
    (quickGen g.val m).testBit r.val = m.testBit (rs g r).val := by
  rw [genAsRoll]
  exact rollCorrect (paths g r) m

theorem wordExact (w d m : Nat) (ok : ∀ k < d, (w >>> (3*k))%8 ≤ 5) (r : Sample) :
    (useWord w d m).testBit r.val = m.testBit (backward w d r).val := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih =>
    let t := (w >>> (3*d))%8
    have hr : ∀ k < d, (w >>> (3*k))%8 ≤ 5 := fun k h => ok k (by omega)
    have lim : t ≤ 5 := ok d (by omega)
    simp only [useWord,backward]
    by_cases h : t=0
    · rw [if_pos h,if_pos h]
      exact ih hr r
    · rw [if_neg h,if_neg h]
      let g := Fin.ofNat 5 (t-1)
      have ge : g.val = t-1 := Nat.mod_eq_of_lt (by omega)
      have bit := genExact g (useWord w d m) r
      rw [ge] at bit
      exact bit.trans (ih hr (rs g r))

theorem digits : ∀ (o : ID) (k : Fin 9), (words[o.val]! >>> (3*k.val)) % 8 ≤ 5 := by decide +kernel

theorem actionBit (o : ID) (m : Nat) (r : Sample) :
    (permute o.val m).testBit r.val = m.testBit ((orient o).s.symm r).val := by
  rw [orient,backApply]
  exact wordExact _ _ _ (fun k h => digits o ⟨k,h⟩) _

theorem actionSet (o : ID) (m : Nat) :
    bits (permute o.val m) = acted (orient o) (bits m) := by
  ext r
  change (_ = true) ↔ (_ = true)
  rw [actionBit]
end PCX150.Scalar

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart
def big : Nat := 2^7056-1
def R (a : Nat) := if a=0 then 0 else rm[a-1]!
abbrev Bank := Fin 49
def lane (b : Bank) (o : Chart48.ID) := 49*o.val+b.val
def dataB (b : Bank) (o : ID) := acted (orient o) (PrivateGame.candidate b)
theorem foldBits (xs : List Nat) (f : Nat → Nat) (i acc : Nat) :
    (xs.foldl (fun a e => a ||| f e) acc).testBit i = true ↔
      acc.testBit i = true ∨ ∃ j ∈ xs, (f j).testBit i = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true]
    simp only [List.mem_cons]
    aesop

theorem posLane (b : Bank) (o : Chart48.ID) : lane b o < 7056 := by
  unfold lane; have := b.isLt; have := o.isLt; omega
theorem liveWide (b : Bank) (o : Chart48.ID) : big.testBit (lane b o) = true := by
  rw [big,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
  exact posLane b o

theorem stripe (m : Nat) (i : Nat) (b : Bank) (o : Chart48.ID) (tiny : m<2^49) :
    (m <<< (49*i)).testBit (lane b o) = true ↔ i=o.val ∧ m.testBit b.val = true := by
  rw [Nat.testBit_shiftLeft]
  have lim := b.isLt
  unfold lane
  by_cases eq : i=o.val
  · subst i; simp
  · by_cases below : i<o.val
    · have bound : 49 ≤ 49*o.val+b.val-49*i := by omega
      have no := Nat.testBit_lt_two_pow (lt_of_lt_of_le tiny (Nat.pow_le_pow_right (by decide : 0 < 2) bound))
      simp [eq,show 49*i ≤ 49*o.val+b.val by omega,no]
    · simp [eq,show ¬49*i ≤ 49*o.val+b.val by omega]

end PCX150.Scalar
namespace PCX150.Scalar.Local
open Chart48 SmallChart
theorem chosenSet (a : Bank) : bits (R a.val) = PrivateGame.candidate a := by
  by_cases z : a.val=0
  · ext r; simp [bits,R,PrivateGame.candidate,z]
  · simp [R,PrivateGame.candidate,z]
end PCX150.Scalar.Local
namespace PCX150.Scalar
open Chart48 SmallChart
private def groupSteps : Array Nat := #[562040988810,20,27,673,0,773,98971,10,35,2,13,8542,35,0,0,0,28,22,15,160,111899,0,24,12,9,15,0,0,12,10,15,802,288385,0,1123,2,275,797,50519,340,860895,275,12,30279,287130,8799,793,8783,0]
private def groupTurns : Array Nat := #[1,2,3,4,5,6,8,9,12,13,15,19,24,25,31,34,41,42,43,44,46,55,56,62,63,66,71,87,90,102,108,125,126,136,141]
private def rotationCodes : Array Nat := #[0x18241e1d1c02050403130908070a0001,0x3d0d0c0b1211100f322c2b2a061b1a19,0x4a494d16151437363544430e3c3b3a39,0x5f5e1f23222120582928275453174c4b,0x6d6c2d31302f2e6657646326255d5c5b,0x3f3e42414075743847727134336b6a69,0x83824f4e5251507e7d487c4645787a79,0x8a6867658961606287865a5985565581,0x8c88848f807f7b8e7776738d6f6e708b,0x250305041f13161517010d0c0e000602,0xb2c2b38313034330709082d0a232226,0x4f4e141e1d48424645100f3212113f3e,0x2120584c4b5a591c5256551918241b1a,0x2f2e663c3b68672a6528275453296160,0x75746b77763a393d7336354443376f6e,0x51507e7d5d807f4a494d4772717b4140,0x696d6c85628786885c5b5f5e57646384,0x8d898f8183828e787a797c708b8a8c6a,0x41f2120021c19180114100f000b0703,0xe3a390a363509082d2f2e062a282705,0x1615174a49134712113f3e3d41400d0c,0x2625245c5b1e1d48571b1a4f4e4d5150,0x3433326a692c2b382961605f5e622322,0x4443783c3b686766376f6e6d6c703130,0x56555453814c4b5a59587b7a79424645,0x767574896564635d807f7e7d84838252,0x8e8f858887867c8c8b8a8d7372716b77,0x3252302201d1b01181512000f0c0804,0x3e3c0a39093736073331062e2b052928,0x51144e4c1349111047460e430d42410b,0x611f5e1e5d5c1c591a19575617531652,0x6f2d6c2c6b6a2a672726656424222162,0x7a3d3b3a787738743534737232302f70,0x4f84834d4b4a8180487d45447c403f7b,0x8c8b6663605f895b5a88875855548550,0x8a86827f7e8f7976758e716e6d8d6968,0x27260222211e011a19160011100d0905,0x3f0a3b3a370807353406302f2c290403,0x14504f134b4a12470f0e4544420c0b40,0x1f605f5d1d1c5b5a1b57181755545215,0x2d6e6d6b2b2a69682865252463236220,0x3d793c7839387675367333327131702e,0x844e4d824c8149487f7e467c43417b3e,0x67668a6461895e5c8859588656855351,0x8b8783808f7d7a778e74726f8d6c6a8c,0x33322c2b38000d0c0e0a161517130206,0x5805041f23222625241e1d4801313034,0x68676609082d5256555453034c4b5a59,0x75740b12113f3e3d4246454443073c3b,0x7e7d141b1a4f4e4d737271100f6b7776,0x21202961605f5e1c65646319185d807f,0x8b8a2f2e376f6e6d6c2a852827888786,0x824a49478e41407b7a793a397c36358c,0x8178708d6a6962895c5b578f51508483,0x7433c0a390c12000f2b1b01181d0408,0x5e23022005292803534c134915093736,0x6a2a6c31062e1a19576424251e5d5c1c,0x7a3d3e0d42410b741110477232332c6b,0x834d4e165251147d35447c460e3b3a78,0x611f22216287585927548556174b4a81,0x6d8d6f2d302f708b66676326655b5f89,0x8f804845793f7b40758e773871347369,0x7f766e8a688c60865a8855824f84507e,0x35440a3b3a0d0011102c011a191e0509,0x5f0222212904032754134b4a16370807,0x2a696d06302f1b57182463265d1d1c5b,0x3d793f420c0b407512470f3271346b2b,0x4d824f521514507e367c430e453c7839,0x1f6023622058865a28855317554c8149,0x8d6c2d6e31702e668a686465255c895e,0x7d487f467a7b3e418e7438767273336a,0x80776f8b8c67618788595683844e518f,0xe0f12003e2b3106330823022504150c,0x204c135916525617181b014e1d0d4246,0x6f2d2e3c0a672226652803530529611f,0x410b742c6b7738393034733607430937,0x51147d1e5d8048494510477232113f7b,0x87584b5a885c1c5e55195764241a4f84,0x2f708b663b688c6a2a6c275485602162,0x81834d7140758e763a787a3d35447c6e,0x82798a696d8d865b5f8963507e8f7f4a,0x451000113f2c0630340902222605160d,0x21134b5a5215175519011a4f1e420c0e,0x2d6e2f0a3b6823652503275429041f60,0xb40756b2b38763a3173330735443708,0x14507e5d1d487f4a46470f3271127b3e,0x58864c88591c5b5f56571824631b844e,0x702e668a3c8c672a696d288553616220,0x494d8272418e747778393d79367c436f,0x837a8b6a8d6c875c895e64518f7d8081,0x3e410b0c393607082e28030420180f,0x255c1c1d19571b014e51141549104712,0x3106336a2a2b270529611f5e21622302,0x460e433a783c0a673509376f2d6c2f70,0x5617534a814c1359113f7b7a3d400d42,0x64245b1e5d80487d1a4f84834d501652,0x34737232692c6b773874605f89222665,0x8887587945447c3b688c8b666e6d8d30,0x868a7176758e637f7e8f825554854b5a,0x5317161558011e1d24022c2b32060a13,0x3809083d3c3b44430e0d0c66004c4b54,0x7e7d4805044d6b727134330731307574,0x5a591c1b1a5f5e1f5d64632625032322,0x68672a12116d6c2d8556551918528786,0x3a39377a793f3e0b7c4645100f428b8a,0x807f4a492983824f4e147336358e7776,0x6e2f2e57885c5b89616021206528278f,0x706281845150787b4140478c6a698d6f,0x15e5c1c1d2028030449360708390f18,0x43410b0c104712006c6a2a2b2e19571b,0x4c13535114153509377a3d3e3a783c0a,0x642425216223027d270529834d4e4a81,0x7232332f703106741a5f89611f5b1e5d,0x460e400d428b6667116d8d6f2d692c6b,0x54855617501652875859793f7b3b447c,0x8e773860632665227e8f8048824f844b,0x767f55865a88458a688c6e7134733075,0x1a5f1c5b1e210327054a0735093a1019,0x440b400d470f00116d2a692c2f571801,0x134b541450163637083d793f78390a3b,0x246326622002227e2829044d824f8149,0x327134702e0630751b895e1f605c5d1d,0xe4541420c668a68128d6c2d6e6a6b2b,0x8553175551521558865a7a7b3e3c7c43,0x74387661646525238f7d487f83844e4c,0x778056878859468b8c676f727333318e,0x2002262503484f4e14173f3e0b0e2d1f,0x68672a6f6e2f2e0634330738616021,0x1918015a591c7b41400d0c664645100f,0x5044d807f4a49138451501615585655,0x9083d77763a390a6223227e7d652827,0x6d6c8c6a692c2b327031307574733635,0x1b1a5f5e885c5b1e1d24428b8a471211,0x3b44438f298382814c4b545352878657,0x7c85895d64638d6b72718e377a79783c,0x26272905604b5216551a420d45113022,0x406b2c76063173343537096e3b022365,0x844f505d1e7f0c0e4647107100127b3f,0x622186134c885a5b151756571963011b,0x702f8a0a3c8c68692503288554041f61,0x8e752b3877783a793307367c44082d6f,0x14518f7e1d4880814a820f32723e0b41,0x6a8d6d53205887591c5c895f1824644e,0x6c5e7d494d8374393d7a432e668b672a,0x28652223625d1a1b5752111247423729,0x7b3b3c7808093536733031706b040527,0x5051844b4c81000f1045467c0c0d4041,0x6061891d1e5b5c880118195556851516,0x6e6f8d2b2c696a8c0325266364022021,0x797a0a393a76778e0733347172062e2f,0x4e4f828313494a7f808f0e43440b3e3f,0x688a8b241f5e5f1c595a868717535414,0x66584d487d7e3d387475322d6c6d2a67,0x6c2d2f2e66073a393d0b4a494d141c2a,0x481918245c5b5f5e1f212058036a696d,0x757438100f328183824f4e0151507e7d,0x68670a363544430e787a793f3e004140,0x5a591328275453178d6f6e0908708b8a,0x1e1d5764632625028961600504628786,0x77762c2b477271343306841b1a8f807f,0x551615378c3c3b7c46450d0c7b12118e,0x52426b7331305d65232229884c4b8556,0x3233310674083c0a430c4c1353151d2b,0x591b015e1e5d64242523027d042c6b72,0x8b666712006c4b548556171816528758,0x77383909377a3d3e3b447c460e0f0d42,0x8048490529834d4e713473360730758e,0x5c1c1a5f89611f206326652803227e8f,0x688c6a2a116d8d6f2d2e551957865a88,0x84511435763a78793f7b410b4510478a,0x5040696e2f705b602162277f4a81824f,0x7134063075090a3b440d134b54161e2c,0x5a011a5f5d1d24632602227e056b2b32,0x668a6800116d4c855317551952155886,0x38763a37083d793f3c7c430e4510420c,0x487f4a29044d824f7273330735318e74,0x1c5b1b895e1f60216465250327238f7d,0x8c672a69128d6c2d6e2f565718878859,0x4e1450367778397a7b3e0b4046470f8b,0x51416a6f702e5c616220288081498384,0x2d6c6a2a670f410b3e3951144e49202e,0x7d2803252162611f5e5c1c59182f706f,0x773874360733504f84834d044a818048,0x8b660c1047460e43403f7b7a3d083a78,0x87581519575617536e6d8d120069688c,0x230227266564241d605f891b015b5a88,0x758e310635347372322b8205297f7e8f,0x854c13118a0d4245447c3c0a79093776,0x4b3b30712c6b22631e5d1a8616525554,0x367c3b3c78421112476b1a1b575d2937,0x8922236204052728854b4c8152080935,0x696a8d3031700118196364651d1e5b5c,0x797a7b0c0d40418e000f107172732b2c,0x828384151650518f07434445460a393a,0x6061022021868788035354555613494a,0x6c6d6e6f062e2f8a8b8c2425261c5e5f,0x7e7f800e3d3e3f0b747576773233342a,0x48382d6667681f58595a174d4e4f147d,0x74063433322d6867660e5a5958174838,0x134f4e4d807f7e7d022625241f777675,0x44430a3f3e3d88878616151456555453,0x2c2b2a6f6e6d6c008c8b8a0d0c0b4645,0x1e1d1c61605f5e018e31302f2e737271,0x4a498483820504038f23222120656463,0x3c3b3a397b7a79090807525150854c4b,0x1a1918706b6a698d1211100f4241407c,0x57477837363581292827625d5c5b891b,0xb0c460e0f676f2d2e33611f20254e3e,0x48048494f84511415561718593f7b41,0x36070877383960216223027d26652803,0x12006c688c6a2a2b6e2f703106743473,0x1b015e5a885c1c1d400d428b66451047,0x834d7f4a814c13535016528758551957,0x9377a3d763a783c0a43227e8f270529,0x5d64248a116d8d692c6b723230758e35,0x6371793b447c824b5485861a5f895b1e,0x400d0e4510682d6e2f341f6021264f3f,0x5487f4a844e1450161755195a7b3e0b,0x7350938763a61622002227e65250327,0x116d8c672a692c6f702e0630757333,0x11a5f88591c5b1e41420c668a46470f,0x4d82808149134b545152155886565718,0x37083d797778390a3b44238f7d282904,0x1d24638b128d6c6a6b2b3271318e7436,0x64727a3c7c43834c8553871b895e5c5d,0x464711127b6b30317337222365295242,0x624b4c8815165556571a1b845d0c0d45,0x6e6f703b3c8c02252627288504056061,0x40418e2b2c76777806333435367c0809,0x50518f1d1e7f80810e0f107172003e3f,0x868713595a5b5c891718196364014e4f,0x2e2f8a8b0a6768696a8d0353541f2021,0x4a8283320b747538393a797a0743442d,0x4d3d662a6c6d581c5e5f24147d7e4849,0x127b4041427835363770272829625747,0x655b5c5d18191a1b84505152810f1011,0x303173696a6b03040560618920212223,0x45467c393a3b3c8c0708096e6f8d2e2f,0x555685494a4b4c88003e3f797a0b0c0d,0x63641c1d1e7f808f014e4f8283141516,0x333471722a2b2c76778e1f5e5f022526,0x5a86873d0e43440a67688a8b2d6c6d06,0x58663238747524487d7e4d1753541359,0x1b895b5c5d6227282981353637784757,0x7c4041420f1011128d696a6b7018191a,0x4b4c85505152070809797a7b393a3b3c,0x636465202122238f030405828384494a,0x7172732e2f30318e015e5f60611c1d1e,0x45460b0c0d8a8b8c006c6d6e6f2a2b2c,0x535455561415168687883d3e3f0a4344,0x7576771f242526027d7e7f804d4e4f13,0x38481758595a0e6667682d3233340674,0x86161755544f487f7e2638767534685a,0x2c2d6e6d8c67668a0d0e45443f885958,0x24631e1f605f778e7406302f73333271,0x134b4a844e4d8205808f7d0222216525,0xa3b3a7b3e3d79098752151450568553,0x2a696f8d6c0011108b420c0b40467c43,0x5d1d1c5b61895e011a1931702e726b2b,0x80735514c8149832904032723622064,0x36285c1b57186a12470f413c78397a37,0x672a6d6c2d327574383d7e7d484d5866,0x1454531787865a591c5f5e1f248b8a68,0x3f3e0b44430e8f807f4a491383824f4e,0x2f2e0672713433078e77763a390a7a79,0x21200264632625038c6a692c2b8d6f6e,0x1615855655191801885c5b1e1d896160,0x41400d0c7c4645100f00814c4b845150,0x2705046b7031307336350908783c3b7b,0x29374247121152571b1a5d6223226528,0x2a678b662e437a3d3974834d497d5e6c,0x4e6424185f895c1c59875820536d8d6a,0x410b3e72320f824a8180481d7e8f5114,0x6f2d08447c360733793a7877382b758e,0x611f04548528032569688c3c0a8a2f70,0x1b016319575617155b5a884c13862162,0x3f7b1200711047460e0c7f1e5d504f84,0x6523023b6e09373534733106762c6b40,0x223011450d421a5516524b6005292726,0x4849834d4e538758595e8b66676c747d,0x2e723233758e7738397a3d3e437e8f80,0x611f206424258a688c6a2a2b6d8d6f2d,0x5114155485561718865a885c1c1d5f89,0x410b0c447c460e0f7f4a814c13824f84,0x3106713473360708763a783c0a793f7b,0x21622302632665280304692c6b6e2f70,0x4712004b5016525519571b015b1e5d60,0x111a22270529303509373b400d424510,0x7f4a4d824f5458865a5f668a686d757e,0x2f3271348e7438763a3d793f448f7d48,0x1f60212463268b8c672a692c8d6c2d6e,0x14501685531755198788591c5b1e895e,0xb400d7c430e4510808149134b83844e,0x6307273330735097778390a3b7a7b3e,0x622002226465250327056a6b2b6f702e,0xf00114c515215565718011a5c5d1d61,0x121b23282904313637083c41420c4647,0x8752555685847f808f6576778e738c88,0x6b6e6f8d67688a8b4245467c7b595a86,0x63645d60618938747530317033347172,0x4b4c814e4f828329487d7e2223622526,0x3b3c783e3f797a375815165051175354,0x696a2d6c6d111247660c0d40410e4344,0x1d1e5b5c1f5e5f1a1b57062e2f322b2c,0x935361413494a4d0405272802202124,0x7031c0118192a000f100b0a393a3d08,0x6a8c8a8b707c797a788e8283818f898d,0x846364575e5f5b5c88868762856c6d69,0x40417b7172474d494a7f805d7d7e5051,0x6e6f3743443536733d393a76776b7475,0x60612953542728652a67683b3c662e2f,0x1a1b2418195556521c595a4b4c582021,0x3e3f1112320f10454642481d1e144e4f,0x2622230a2d08090733343031382b2c0b,0x206000e0c0d01171516131f04050325]

def stageID (a n : Nat) := (groupSteps[a]! >>> (6*n)) % 64
def turnID (i : Nat) := groupTurns[i]!
def sendName (i o : Nat) := (rotationCodes[9*i+o/16]! >>> (8*(o%16))) % 256
def rotateLanes (i w : Nat) := (List.range 144).foldl (fun acc o =>
    acc ||| (((w >>> (49*sendName i o)) % 2^49) <<< (49*o))) 0
def keepStep (a t : Nat) := 0<t && t≤35 && permute (turnID (t-1)) (R a) == R a
def spread (a w : Nat) : Nat → Nat
  | 0 => w
  | n+1 =>
    let old := spread a w n
    let t := stageID a n
    if keepStep a t then old ||| rotateLanes (t-1) old else old

def followName (base : ID) (w : Nat) : Nat → ID
  | 0 => base
  | n+1 => let t := (w >>> (3*n))%8
           if t=0 then followName base w n else follow (followName base w n) (Fin.ofNat 5 (t-1))

theorem traceName (o : ID) (w n : Nat) (s : Set Sample) :
    acted (assemble w n) (acted (orient o) s) = acted (orient (followName o w n)) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [assemble,followName]
    split
    · exact ih
    · rw [←actedChain,ih,followAct]

abbrev TurnIndex := Fin 35

def rawChase (o w : Nat) : Nat → Nat
  | 0 => o
  | n+1 =>
    let t := (w >>> (3*n))%8
    let p := rawChase o w n
    if t=0 then p else ((alongCode[p]! >>> (8*((t-1)%5))) % 256) % 144

theorem followChase (o : ID) (w n : Nat) : (followName o w n).val = rawChase o.val w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [followName,rawChase]
    split
    · exact ih
    · change ((alongCode[(followName o w n).val]! >>> _) % 256) % 144 = _
      rw [ih]

def groupRow (j : Nat) := turnID j < 144 &&
  (List.range 144).all (fun o => sendName j o < 144 && rawChase o words[turnID j]! 9 == sendName j o)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow0 : groupRow 0=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow1 : groupRow 1=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow2 : groupRow 2=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow3 : groupRow 3=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow4 : groupRow 4=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow5 : groupRow 5=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow6 : groupRow 6=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow7 : groupRow 7=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow8 : groupRow 8=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow9 : groupRow 9=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow10 : groupRow 10=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow11 : groupRow 11=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow12 : groupRow 12=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow13 : groupRow 13=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow14 : groupRow 14=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow15 : groupRow 15=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow16 : groupRow 16=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow17 : groupRow 17=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow18 : groupRow 18=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow19 : groupRow 19=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow20 : groupRow 20=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow21 : groupRow 21=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow22 : groupRow 22=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow23 : groupRow 23=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow24 : groupRow 24=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow25 : groupRow 25=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow26 : groupRow 26=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow27 : groupRow 27=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow28 : groupRow 28=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow29 : groupRow 29=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow30 : groupRow 30=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow31 : groupRow 31=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow32 : groupRow 32=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow33 : groupRow 33=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem turnRow34 : groupRow 34=true := by decide +kernel

private def rowSequence : Nat → Nat → Prop
  | 0,_ => True
  | n+1,j => groupRow j=true ∧ rowSequence n (j+1)
private theorem takeRow (n j k : Nat) : rowSequence n j → k<n → groupRow (j+k)=true := by
  induction n generalizing j k with
  | zero => omega
  | succ n ih =>
    intro h bound
    cases k with
    | zero => exact h.1
    | succ k =>
      have z := ih (j+1) k h.2 (Nat.lt_of_succ_lt_succ bound)
      have eq : j+1+k=j+k.succ := by omega
      rwa [eq] at z
theorem rotationHints (j : TurnIndex) (o : ID) : turnID j.val<144 ∧ sendName j.val o.val<144 ∧
    (followName o words[turnID j.val]! 9).val=sendName j.val o.val := by
  have allRows : rowSequence 35 0 := ⟨turnRow0,turnRow1,turnRow2,turnRow3,turnRow4,turnRow5,turnRow6,turnRow7,turnRow8,turnRow9,turnRow10,turnRow11,turnRow12,turnRow13,turnRow14,turnRow15,turnRow16,turnRow17,turnRow18,turnRow19,turnRow20,turnRow21,turnRow22,turnRow23,turnRow24,turnRow25,turnRow26,turnRow27,turnRow28,turnRow29,turnRow30,turnRow31,turnRow32,turnRow33,turnRow34,trivial⟩
  have row : groupRow j.val=true := by simpa only [Nat.zero_add] using takeRow _ 0 j.val allRows j.isLt
  unfold groupRow at row
  have h := Bool.and_eq_true_iff.mp row
  have pair := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h.2 o.val (List.mem_range.mpr o.isLt))
  exact ⟨of_decide_eq_true h.1,of_decide_eq_true pair.1,(followChase _ _ _).trans (eq_of_beq pair.2)⟩

def actionIndex (j : TurnIndex) : ID := ⟨turnID j.val,(rotationHints j 0).1⟩
def sendIndex (j : TurnIndex) (o : ID) : ID := ⟨sendName j.val o.val,(rotationHints j o).2.1⟩

theorem shiftIndex (j : TurnIndex) (o : ID) (s : Set Sample) :
    acted (orient (actionIndex j)) (acted (orient o) s)=acted (orient (sendIndex j o)) s := by
  change acted (assemble words[turnID j.val]! 9) (acted (orient o) s) = _
  rw [traceName]
  have eq : followName o words[turnID j.val]! 9=sendIndex j o := Fin.ext (rotationHints j o).2.2
  rw [eq]

theorem laneBefore (j : TurnIndex) (w : Nat) (b : Bank) (o : ID)
    (h : (rotateLanes j.val w).testBit (lane b o)=true) :
    w.testBit (lane b (sendIndex j o))=true := by
  rw [rotateLanes,foldBits] at h
  rcases h with bad | ⟨i,_,cell⟩
  · simp at bad
  · obtain ⟨eq,src⟩ := (stripe _ i b o (Nat.mod_lt _ (by decide : 0<2^49))).1 cell
    subst i
    rw [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight] at src
    simpa only [b.isLt,decide_true,Bool.true_and,lane,sendIndex] using src
end PCX150.Scalar

namespace PCX150.Scalar.Local
open Chart48 SmallChart PrivateGame
open Sparse (TestTree Valid box leaves)

def pointPrice (a b : Bank) (o : ID) := ∀ (t u : TestTree),
  Valid geo.val (box geo.tag (candidate a) ∅) t (dataB b o) →
  Valid geo.val (box geo.tag (candidate a) (dataB b o)) u Set.univ →
  41 ≤ price a + leaves t + leaves u

theorem sameCost (a b : Bank) (o : ID) (j : TurnIndex) (fixed : permute (turnID j.val) (R a.val)=R a.val) :
    pointPrice a b (sendIndex j o) → pointPrice a b o := by
  let f := orient (actionIndex j)
  have mb : acted f (dataB b o) = dataB b (sendIndex j o) := shiftIndex j o (candidate b)
  have ma : acted f (candidate a)=candidate a := by
    change acted (orient (actionIndex j)) (candidate a)=candidate a
    rw [←chosenSet,←actionSet]
    exact congrArg bits fixed
  have fa : Match (acted f (candidate a)) (candidate a) := by rw [ma]; exact matchSame _
  have fb : Match (acted f (dataB b o)) (dataB b (sendIndex j o)) := by rw [mb]; exact matchSame _
  have fe : Match (acted f ∅) ∅ := by rw [actEmpty]; exact matchSame _
  intro ready t u ht hu
  have st := canMove f _ _ _ _ _ _ ht fa fe
  rw [mb] at st
  have su := canMove f _ _ _ _ _ _ hu fa fb
  rw [actUniv] at su
  simpa only [Sparse.sameLeaves] using ready _ _ st su

theorem propagatePrices (a b : Bank) (w : Nat)
    (initial : ∀o : ID, w.testBit (lane b o)=true → pointPrice a b o) (n : Nat) :
    ∀ o : ID, (spread a.val w n).testBit (lane b o)=true → pointPrice a b o := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    intro o h
    unfold spread at h
    dsimp only at h
    split at h
    · rename_i used
      rw [Nat.testBit_or,Bool.or_eq_true] at h
      rcases h with h | h
      · exact ih o h
      · let tag := stageID a.val n
        have q := used
        change keepStep a.val tag=true at q
        unfold keepStep at q
        simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at q
        let j : TurnIndex := ⟨tag-1,by have := q.1.2; omega⟩
        exact sameCost a b o j q.2 (ih (sendIndex j o) (laneBefore j _ b o h))
    · exact ih o h

end PCX150.Scalar.Local
