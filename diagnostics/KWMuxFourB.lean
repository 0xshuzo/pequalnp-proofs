import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9939.Rectangles
variable {I : Type} [DecidableEq I]

structure View (I : Type) where
  pos : Finset I
  neg : Finset I
def band (a b : View I) : View I := ⟨a.pos∩b.pos,a.neg∪b.neg⟩
def bor (a b : View I) : View I := ⟨a.pos∪b.pos,a.neg∩b.neg⟩
inductive Tree (I : Type)
  | pin : View I → Tree I
  | both : Tree I → Tree I → Tree I
  | either : Tree I → Tree I → Tree I

def evaluate : Tree I → View I
  | .pin a => a
  | .both a b => band (evaluate a) (evaluate b)
  | .either a b => bor (evaluate a) (evaluate b)
def leaves : Tree I → Nat
  | .pin _ => 1
  | .both a b | .either a b => leaves a + leaves b
def allowed (B : View I → Prop) : Tree I → Prop
  | .pin a => B a
  | .both a b | .either a b => allowed B a ∧ allowed B b

-- The two coordinates track accepted lower-extreme and rejected upper-extreme
-- assignments at the eight addresses. Either operation partitions one side.
structure Price (I : Type) [DecidableEq I] (B : View I → Prop) where
  value : Finset I → Finset I → Nat
  leaf : ∀ a, B a → ∀ x⊆a.pos, ∀ y⊆a.neg, value x y≤1
  splitX : ∀ x z y, Disjoint x z → value (x∪z) y≤value x y+value z y
  splitY : ∀ x y z, Disjoint y z → value x (y∪z)≤value x y+value x z

theorem price_sound {B : View I → Prop} (p : Price I B) (f : Tree I) (bank : allowed B f) :
    ∀x⊆(evaluate f).pos,∀y⊆(evaluate f).neg,p.value x y≤leaves f := by
  induction f with
  | pin a => exact p.leaf a bank
  | both a b ia ib =>
    intro x hx y hy
    let left := y ∩ (evaluate a).neg
    let right := y \ (evaluate a).neg
    have leftSub : left⊆(evaluate a).neg := Finset.inter_subset_right
    have rightSub : right⊆(evaluate b).neg := by
      intro i hi
      have hh := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp (hy hh.1)).resolve_left hh.2
    have combine : left∪right=y := by
      ext i
      simp [left,right]
    have sep : Disjoint left right := by
      rw [Finset.disjoint_left]
      exact fun _ l r => (Finset.mem_sdiff.mp r).2 (Finset.mem_inter.mp l).2
    have la := ia bank.1 x (fun _ h=>(Finset.mem_inter.mp (hx h)).1) left leftSub
    have lb := ib bank.2 x (fun _ h=>(Finset.mem_inter.mp (hx h)).2) right rightSub
    have h := p.splitY x left right sep
    rw [combine] at h
    exact h.trans (Nat.add_le_add la lb)
  | either a b ia ib =>
    intro x hx y hy
    let left := x ∩ (evaluate a).pos
    let right := x \ (evaluate a).pos
    have leftSub : left⊆(evaluate a).pos := Finset.inter_subset_right
    have rightSub : right⊆(evaluate b).pos := by
      intro i hi
      have hh := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp (hx hh.1)).resolve_left hh.2
    have combine : left∪right=x := by
      ext i
      simp [left,right]
    have sep : Disjoint left right := by
      rw [Finset.disjoint_left]
      exact fun _ l r => (Finset.mem_sdiff.mp r).2 (Finset.mem_inter.mp l).2
    have la := ia bank.1 left leftSub y (fun _ h=>(Finset.mem_inter.mp (hy h)).1)
    have lb := ib bank.2 right rightSub y (fun _ h=>(Finset.mem_inter.mp (hy h)).2)
    have h := p.splitX left right y sep
    rw [combine] at h
    exact h.trans (Nat.add_le_add la lb)

theorem one_shared {B : View I → Prop} (h f : Tree I) (pre : allowed B h)
    (tail : allowed (fun v => B v ∨ v=evaluate h) f) (p : Price I B)
    (q : Price I (fun v=>B v ∨ v=evaluate h)) :
    p.value (evaluate h).pos (evaluate h).neg + q.value (evaluate f).pos (evaluate f).neg ≤
      leaves h + leaves f :=
  Nat.add_le_add (price_sound p h pre _ Finset.Subset.rfl _ Finset.Subset.rfl)
    (price_sound q f tail _ Finset.Subset.rfl _ Finset.Subset.rfl)
end PEqualNP.Outside.L_meta_9939.Rectangles

namespace PEqualNP.Outside.L_meta_9939.Price4
open PEqualNP.Outside.L_meta_9939.Rectangles
abbrev Id := Fin 4
def bankRows : Array Nat := #[0x0,0x3221212132212110,0x3221322122112110,0x5331533153314220,0x3232212122211110,0x5353313153423120,0x6453534244323220,0x8563635274525230,0x3322222122111110,0x6543434254323220,0x5533543233113210,0x8653754265325320,0x5554333233321110,0x8675534265533220,0x8765655354323220,0xa885856386535330]
def number (x : Finset Id) : Nat := x.sum (fun i => 2^i.val)
def weight (x y : Finset Id) : Nat :=
  (((bankRows[number x]?.getD 0) >>> (4*number y)) % 16
def datum (i : Id) : View Id := ⟨{i},{i}⟩
def selector (j : Fin 2) (bit : Bool) : View Id :=
  ⟨Finset.univ.filter (fun i => i.val.testBit j.val=bit),
    Finset.univ.filter (fun i => i.val.testBit j.val≠bit)⟩
def primary (v : View Id) : Prop := (∃i,v=datum i) ∨ ∃j b,v=selector j b

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem datum_price : ∀ i : Id, ∀x y : Finset Id,
    x ⊆ (datum i).pos → y ⊆ (datum i).neg → weight x y ≤ 1 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem selector_price : ∀ j : Fin 2, ∀b : Bool, ∀x y : Finset Id,
    x ⊆ (selector j b).pos → y ⊆ (selector j b).neg → weight x y ≤ 1 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem symmetric : ∀ x y : Finset Id,weight x y=weight y x := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem subadd : ∀ x y z : Finset Id, Disjoint y z →
    weight x (y∪z)≤weight x y+weight x z := by decide +kernel
def price : Price Id primary where
  value := weight
  leaf := by
    rintro v (⟨i,rfl⟩|⟨j,b,rfl⟩) x hx y hy
    · exact datum_price i x y hx hy
    · exact selector_price j b x y hx hy
  splitX := by
    intro x z y h
    rw [symmetric (x∪z) y,symmetric x y,symmetric z y]
    exact subadd y x z h
  splitY := subadd
theorem whole (f : Tree Id) (fit : allowed primary f)
    (pos : (evaluate f).pos=Finset.univ) (neg : (evaluate f).neg=Finset.univ) :
    10≤leaves f := by
  have h := price_sound price f fit (evaluate f).pos Finset.Subset.rfl (evaluate f).neg Finset.Subset.rfl
  rw [pos,neg] at h
  have root : price.value Finset.univ Finset.univ=10 := by decide +kernel
  rwa [root] at h
end PEqualNP.Outside.L_meta_9939.Price4
