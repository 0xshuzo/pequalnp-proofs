import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_121.Bridge

open Relation Classical

abbrev Walk (E : ℕ → ℕ → Prop) := Relation.ReflTransGen E

theorem walk_le {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {i j : ℕ} (w : Walk E i j) : j ≤ i := by
  induction w with
  | refl => exact Nat.le_refl _
  | tail _ e ih => exact (Nat.le_of_lt (dec e)).trans ih

theorem walk_sub {E E' : ℕ → ℕ → Prop} (sub : ∀ {i j}, E i j → E' i j)
    {i j : ℕ} (w : Walk E i j) : Walk E' i j := by
  induction w with
  | refl => exact .refl
  | tail _ e ih => exact .tail ih (sub e)

theorem clash {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    {A : ℕ → Prop} (ac : A c) {x : ℕ}
    (wc : Walk (fun i j => E i j ∧ A j) c x) (wd : Walk E d x) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ A m ∧ Walk E c m ∧ Walk E d m := by
  induction wc with
  | refl =>
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · exact False.elim (ne e)
    · have lt : q < r := (walk_le dec wq).trans_lt (dec rd)
      exact ⟨r, q, c, Or.inl rfl, Or.inr wq, rc, eq, (Ne.symm (ne_of_lt lt)),
        ac, .refl, wd⟩
  | @tail u v wu he ih =>
    have wcu : Walk E c u := walk_sub (fun h => h.1) wu
    have lu : u < r := (walk_le dec wcu).trans_lt (dec rc)
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · subst v
      exact ⟨u, r, d, Or.inr wcu, Or.inl rfl, he.1, rd, ne_of_lt lu, he.2,
        .tail wcu he.1, .refl⟩
    · by_cases hp : u = q
      · subst q
        exact ih wq
      · exact ⟨u, q, v, Or.inr wcu, Or.inr wq, he.1, eq, hp, he.2,
          .tail wcu he.1, wd⟩

theorem same_entry {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d z : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)
    {A : ℕ → Prop} (ac : A c) {x : ℕ}
    (wc : Walk (fun i j => E i j ∧ A j) c x) (wd : Walk E d x) : A z := by
  obtain ⟨p, q, m, hp, hq, ep, eq, neq, am, _, _⟩ := clash dec rc rd ne ac wc wd
  exact unique p q m hp hq ep eq neq ▸ am

theorem swap_entry {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d z : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)
    {A : ℕ → Prop} (ad : A d) {x : ℕ}
    (wd : Walk (fun i j => E i j ∧ A j) d x) (wc : Walk E c x) : A z :=
  same_entry dec rd rc ne.symm
    (fun p q m hp hq ep eq hne => unique q p m hq hp eq ep hne.symm) ad wd wc

section semantic

variable {α κ : Type}
variable {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
variable {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
variable (bad : α → κ → Prop) (point : κ → α → Prop) (leaf : κ → ℕ)
variable (B : α → ℕ → Prop) (side : α → Bool)
variable (one : ∀ {a k}, point k a → ∀ j, bad a j ↔ j = k)
variable (branch : ∀ a, B a (if side a then c else d))
variable (route : ∀ a i, B a i →
  ∃ j, bad a j ∧ Walk (fun u v => E u v ∧ B a v) i (leaf j))
variable (points : ∀ k, ∃ a, point k a)

def Common (E : ℕ → ℕ → Prop) (c d : ℕ) (u : ℕ) : Prop :=
  Walk E c u ∧ Walk E d u

def Forced (bad : α → κ → Prop) (point : κ → α → Prop) (side : α → Bool) (a : α) : Prop :=
  (∃ k, point k a ∧ ∃ b, point k b ∧ side b ≠ side a) ∨
  (∀ k, bad a k → ∀ b, point k b → side b ≠ side a)

include branch route one in
theorem criticalSide {a k} (ha : point k a) :
    Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  obtain ⟨j, hj, w⟩ := route a _ (branch a)
  have eq := (one ha j).1 hj
  simpa [eq] using w

include branch route one points in
theorem forced_common {a} (ha : Forced bad point side a) :
    ∃ k, bad a k ∧ Common E c d (leaf k) ∧
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  have mk : ∀ {k b}, bad a k →
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) →
      point k b → side b ≠ side a →
      ∃ k, bad a k ∧ Common E c d (leaf k) ∧
        Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
    intro k b bk wa pb hn
    have wb := criticalSide bad point leaf B side one branch route pb
    refine ⟨k, bk, ?_, wa⟩
    have ua := walk_sub (fun h => h.1) wa
    have ub := walk_sub (fun h => h.1) wb
    cases ea : side a <;> cases eb : side b <;> simp_all [Common]
  rcases ha with ⟨k, ka, b, kb, hn⟩ | ha
  · exact mk ((one ka k).2 rfl) (criticalSide bad point leaf B side one branch route ka) kb hn
  · obtain ⟨k, bk, wa⟩ := route a _ (branch a)
    obtain ⟨b, kb⟩ := points k
    exact mk bk wa kb (ha k bk b kb)

include dec rc rd ne branch route one points in
theorem entry_exists {a} (ha : Forced bad point side a) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ B a m ∧ Common E c d m := by
  obtain ⟨k, _, ⟨wc, wd⟩, w⟩ := forced_common bad point leaf B side one branch route points ha
  cases h : side a
  · simp [h] at w
    obtain ⟨q, p, m, hq, hp, eq, ep, neq, b, rd', rc'⟩ :=
      clash dec rd rc ne.symm (by simpa [h] using branch a) w wc
    exact ⟨p, q, m, hp, hq, ep, eq, neq.symm, b, rc', rd'⟩
  · simp [h] at w
    exact clash dec rc rd ne (by simpa [h] using branch a) w wd

variable {z : ℕ}
variable (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)

include dec rc rd ne unique branch route one in
theorem false_on_common {k a}
    (hc : Common E c d (leaf k)) (ha : point k a) : B a z := by
  have w := criticalSide bad point leaf B side one branch route ha
  cases h : side a
  · simp [h] at w
    exact swap_entry dec rc rd ne unique (by simpa [h] using branch a) w hc.1
  · simp [h] at w
    exact same_entry dec rc rd ne unique (by simpa [h] using branch a) w hc.2

include dec rc rd ne unique branch route one points in
theorem false_on_forced {a}
    (ha : Forced bad point side a) : B a z := by
  obtain ⟨p, q, m, hp, hq, ep, eq, neq, hm, _⟩ :=
    entry_exists dec rc rd ne bad point leaf B side one branch route points ha
  exact unique p q m hp hq ep eq neq ▸ hm


end semantic

end PEqualNP.Outside.L_pcx_121.Bridge
namespace PEqualNP.Outside.L_pcx_121_fiber
open PEqualNP.Outside.L_pcx_121.Bridge
def mask1 (k : Fin 14) : Nat := #[3,5,6,56,448,0,0,0,0,0,0,0,0,0][k.val]!
def mask0 (k : Fin 14) : Nat := #[0,0,0,0,0,9,18,36,65,130,260,72,144,288][k.val]!

def miss (x : Nat) (k : Fin 14) := x &&& mask1 k = 0 ∧ x &&& mask0 k = mask0 k
def priv (k : Fin 14) (x : Nat) := ∀ j : Fin 14, miss x j ↔ j=k
instance (x : Nat) (k : Fin 14) : Decidable (miss x k) := inferInstanceAs (Decidable (x &&& mask1 k = 0 ∧ x &&& mask0 k = mask0 k))
instance (k : Fin 14) (x : Nat) : Decidable (priv k x) := inferInstanceAs (Decidable (∀j : Fin 14, miss x j ↔ j=k))
def bit (v : Fin 9) (x : Nat) := x.testBit v.val
def w (v t : Fin 9) (f : Bool) : Nat := #[70,133,133,70,259,70,70,14,70,21,70,35,133,70,70,133,70,259,70,133,133,70,259,70,70,14,70,21,70,35,133,70,70,133,70,259,70,133,133,70,259,70,70,14,70,21,70,35,133,70,70,133,70,259,84,21,84,98,98,84,84,140,140,84,84,98,140,84,84,140,84,266,84,161,84,14,161,84,84,140,140,84,84,161,140,84,84,140,84,273,98,161,161,98,98,14,98,266,98,273,266,98,266,98,98,161,98,266,84,133,84,98,98,84,84,140,140,84,84,98,140,84,84,140,84,266,84,161,84,70,161,84,84,140,140,84,84,161,140,84,84,140,84,273,98,161,161,98,98,70,98,266,98,273,266,98,266,98,98,161,98,266][2*(9*v.val+t.val)+f.toNat]!
def partner (v t : Fin 9) (f : Bool) : Nat := #[133,70,70,133,70,133,133,21,133,14,133,14,70,133,133,70,133,70,133,70,70,133,133,133,133,21,133,14,133,21,70,133,133,70,133,133,259,259,259,259,70,259,259,35,259,35,259,14,259,259,259,259,259,70,140,14,140,266,266,140,140,84,84,140,140,266,84,140,140,84,140,98,140,273,140,21,273,140,140,84,84,140,140,273,84,140,140,84,140,161,266,273,273,266,266,35,266,98,266,161,98,266,98,266,266,273,266,98,140,70,140,266,266,140,140,84,84,140,140,266,84,140,140,84,140,98,140,273,140,133,273,140,140,84,84,140,140,273,84,140,140,84,140,161,266,273,273,266,266,259,266,98,266,161,98,266,98,266,266,273,266,98][2*(9*v.val+t.val)+f.toNat]!
def owner (v t : Fin 9) (f : Bool) : Fin 14 := #[3,3,3,3,3,3,3,4,3,4,3,4,3,3,3,3,3,3,3,3,3,3,3,3,3,4,3,4,3,4,3,3,3,3,3,3,3,3,3,3,3,3,3,4,3,4,3,4,3,3,3,3,3,3,0,4,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,1,0,2,0,4,2,0,0,0,0,0,0,2,0,0,0,0,0,2,1,2,2,1,1,4,1,1,1,2,1,1,1,1,1,2,1,1,0,3,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,1,0,2,0,3,2,0,0,0,0,0,0,2,0,0,0,0,0,2,1,2,2,1,1,3,1,1,1,2,1,1,1,1,1,2,1,1][2*(9*v.val+t.val)+f.toNat]!

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem sample : ∀v t : Fin 9, ∀ s : Bool,
  priv (owner v t s) (w v t s) ∧ priv (owner v t s) (partner v t s) ∧
  bit v (w v t s) ≠ bit v (partner v t s) ∧ bit t (w v t s)=s := by decide +kernel
theorem spread (v t : Fin 9) (s : Bool) : ∃ x, Forced miss priv (bit v) x ∧ bit t x=s := by
  obtain ⟨one,other,neq,value⟩:=sample v t s
  exact ⟨_,Or.inl ⟨_,one,_,other,(fun eq=>neq eq.symm)⟩,value⟩
def clauseOn (x : Nat) (C : Finset (Fin 9 × Bool)) := ∃ q∈C,bit q.1 x=q.2
theorem forcedNoClause (v : Fin 9) (C : Finset (Fin 9 × Bool)) (ne : C.Nonempty)
    (off : ∀ x, Forced miss priv (bit v) x → ¬clauseOn x C) : False := by
  obtain ⟨⟨t,s⟩,m⟩:=ne
  obtain ⟨x,h,val⟩:=spread v t s
  exact off x h ⟨_,m,val⟩

theorem noSingleJoin {E : Nat → Nat → Prop} {r c d z : Nat} (v : Fin 9)
    (dec : ∀ {i j : Nat}, E i j → j < i) (rc : E r c) (rd : E r d) (ne : c≠d)
    (leaf : Fin 14 → Nat) (B : Nat → Nat → Prop)
    (branch : ∀ x, B x (if bit v x then c else d))
    (route : ∀ x i, B x i → ∃ j, miss x j ∧ Walk (fun u w=>E u w ∧ B x w) i (leaf j))
    (points : ∀ k, ∃x, priv k x)
    (unique : ∀ p q m, (p=r ∨ Walk E c p) → (q=r ∨ Walk E d q) →
      E p m → E q m → p≠q → m=z)
    (C : Finset (Fin 9 × Bool)) (present : C.Nonempty)
    (sem : ∀ x, B x z → ¬clauseOn x C) : False := by
  apply forcedNoClause v C present
  intro x h
  exact sem x (false_on_forced dec rc rd ne miss priv leaf B (bit v)
    (fun hit j => hit j) branch route points unique h)
end PEqualNP.Outside.L_pcx_121_fiber
