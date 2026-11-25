import Mathlib

namespace Relative2732

abbrev V := Fin 14
abbrev PairRank (a b c d : ℕ) := (15*min a b+max a b)*225 + (15*min c d+max c d)

def bit (a b : V) := (54476011632248939714359330176 : ℕ).testBit (14*a.val+b.val)
def edge (x : V → Bool) := decide (∃ a b : V, bit a b=true ∧ x a=true ∧ x b=true)
def neighbor (a b : V) := bit a b || bit b a
def pair (a b : V) (z : V) := decide (z=a ∨ z=b)

set_option maxHeartbeats 4000000 in
private theorem rank227 : ∀ a b c : V, a≠b → a≠c → b≠c →
    PairRank a.val b.val a.val c.val=227 → a=0 ∧ b=1 ∧ c=2 := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem pair_value : ∀ a b : V, edge (pair a b)=neighbor a b := by decide +kernel

private theorem unique_intersection : ∀ v : V, neighbor 0 v=true → neighbor 2 v=true → v=8 := by decide +kernel

theorem stabilizer_fixes_flag (p : Equiv.Perm V)
    (pres : ∀ x : V → Bool, edge (x ∘ p)=edge x)
    (prank : PairRank (p 0).val (p 1).val (p 0).val (p 2).val=227) :
    p 0=0 ∧ p 1=1 ∧ p 2=2 ∧ p 8=8 := by
  obtain ⟨h0,h1,h2⟩ := rank227 (p 0) (p 1) (p 2) (p.injective.ne (by decide))
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) prank
  have fixed (a b : V) : neighbor a b=neighbor (p a) (p b) := by
    have eq : pair (p a) (p b) ∘ p=pair a b := by
      funext z
      simp [pair,Function.comp_def]
    have h := pres (pair (p a) (p b))
    rwa [eq,pair_value,pair_value] at h
  have i0 := fixed 0 8
  have i2 := fixed 2 8
  rw [h0] at i0
  rw [h2] at i2
  exact ⟨h0,h1,h2,unique_intersection (p 8) (i0.symm.trans (by decide)) (i2.symm.trans (by decide))⟩

end Relative2732
