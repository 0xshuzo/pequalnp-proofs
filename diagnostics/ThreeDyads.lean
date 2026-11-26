import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9804_Three
abbrev I := Fin 3
def bit (s i : Nat) : Prop := s.testBit i = true
instance (s i : Nat) : Decidable (bit s i) := by unfold bit; infer_instance
def board (k : Fin 64) (a b : I) : Prop :=
  a=b ∨
  (a=0 ∧ b=1 ∧ bit k.val 0) ∨
  (a=0 ∧ b=2 ∧ bit k.val 1) ∨
  (a=1 ∧ b=0 ∧ bit k.val 2) ∨
  (a=1 ∧ b=2 ∧ bit k.val 3) ∨
  (a=2 ∧ b=0 ∧ bit k.val 4) ∨
  (a=2 ∧ b=1 ∧ bit k.val 5)
instance (k : Fin 64) (a b : I) : Decidable (board k a b) := by unfold board; infer_instance
def thin (k : Fin 64) : Prop := ∀ a b c d : I, a ≠ b → c ≠ d →
  ¬(board k a c ∧ board k a d ∧ board k b c ∧ board k b d)
instance (k : Fin 64) : Decidable (thin k) := by unfold thin; infer_instance
def probe (k : Fin 64) (r : Fin 5) : Nat :=
  match k.val with
  | 0 => ![7, 14, 21, 28, 35] r
  | 1 => ![7, 14, 28, 35, 42] r
  | 2 => ![7, 14, 21, 28, 42] r
  | 3 => ![7, 14, 28, 42, 56] r
  | 4 => ![7, 21, 28, 35, 49] r
  | 6 => ![7, 21, 28, 34, 56] r
  | 8 => ![7, 14, 21, 28, 49] r
  | 9 => ![7, 14, 28, 33, 56] r
  | 10 => ![7, 14, 21, 28, 56] r
  | 12 => ![7, 21, 28, 49, 56] r
  | 16 => ![7, 21, 35, 42, 49] r
  | 17 => ![7, 20, 35, 42, 56] r
  | 20 => ![7, 21, 35, 49, 56] r
  | 24 => ![7, 10, 21, 49, 56] r
  | 25 => ![7, 10, 20, 33, 56] r
  | 32 => ![7, 14, 35, 42, 49] r
  | 33 => ![7, 14, 35, 42, 56] r
  | 34 => ![7, 14, 17, 42, 56] r
  | 36 => ![7, 12, 35, 49, 56] r
  | 38 => ![7, 12, 17, 34, 56] r
  | 48 => ![7, 35, 42, 49, 56] r

  | _ => 0
def edge (k : Fin 64) (s : Nat) : Prop :=
  ∃ a b : I, board k a b ∧ bit s a.val ∧ bit s (b.val+3)
instance (k : Fin 64) (s : Nat) : Decidable (edge k s) := by unfold edge; infer_instance
def splitRow (x y : Nat) : Prop := ∃ i : I,
    (bit x i.val ∨ bit y i.val) ∧ (bit x (i.val+3) ∨ bit y (i.val+3))
instance (x y : Nat) : Decidable (splitRow x y) := by unfold splitRow; infer_instance
set_option maxRecDepth 20000 in
private theorem checked : ∀ k : Fin 64, thin k →
    (∀ r : Fin 5, ¬edge k (probe k r)) ∧
    (∀ a b : Fin 5, a ≠ b → splitRow (probe k a) (probe k b)) := by decide +kernel

def meets (L R : I → Prop) (s : Nat) : Prop :=
  ∃ i : I, (bit s i.val ∧ L i) ∨ (bit s (i.val+3) ∧ R i)

-- Restrict any three disjoint exceptional dyads to their six endpoints. A
-- four-clause monotone CNF accepting all three leaks on at least one independent input.
theorem four_clause_leak (k : Fin 64) (hk : thin k)
    (L R : Fin 4 → I → Prop) (matched : ∀ i j, L j i ∨ R j i) :
    ∃ s, (∀ j, meets (L j) (R j) s) ∧ ¬edge k s := by
  classical
  by_contra h
  obtain ⟨safe,sep⟩ := checked k hk
  have miss (r : Fin 5) : ∃ j : Fin 4, ¬ meets (L j) (R j) (probe k r) := by
    apply Classical.not_forall.mp
    intro hall
    exact h ⟨probe k r,hall,safe r⟩
  choose f hf using miss
  have inj : Function.Injective f := by
    intro a b eqv
    by_contra ne
    obtain ⟨i,x,y⟩ := sep a b ne
    rcases matched i (f a) with m|m
    · rcases x with v|v
      · exact hf a ⟨i,Or.inl ⟨v,m⟩⟩
      · exact hf b ⟨i,Or.inl ⟨v,eqv ▸ m⟩⟩
    · rcases y with v|v
      · exact hf a ⟨i,Or.inr ⟨v,m⟩⟩
      · exact hf b ⟨i,Or.inr ⟨v,eqv ▸ m⟩⟩
  have bad := Fintype.card_le_of_injective f inj
  norm_num at bad

end PEqualNP.Outside.L_meta_9804_Three
