import PEqualNP.Defs
-- General packed decision procedure from L_meta_8405 on project main, itself derived
-- from the L_meta_1673 search engine. The input, sample layout and certificates here are new.

-- The search engine is adapted from PEqualNP.Outside.L_meta_1673 by Trey Kind (pull request 6929, Apache License 2.0).
-- This file declares its own data types (records for the search state and inductive predicates).

namespace PEqualNP.Outside.L_meta_8399
-- Computational declarations are placed first using the organization of public L_meta_8401.
section hz1
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
def Z0 : ℕ → ℕ := fun _ => 0
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
end hz1
inductive Literal (m : Nat) (B : Set Nat) : Nat → Prop
  | wire {w} : w ∈ B → Literal m B w
  | zero : Literal m B 0
  | one : Literal m B m
  | neg {w} : Literal m B w → Literal m B (w ^^^ m)

inductive BinaryBudget (m T : Nat) : Nat → Set Nat → Prop
  | stop {q B} : Literal m B T → BinaryBudget m T q B
  | step {q B a b} (d : Bool) : Literal m B a → Literal m B b →
      BinaryBudget m T q (insert (op d a b) B) → BinaryBudget m T (q+1) B

lemma Literal.widen {m B B' w} (h : Literal m B w) (more : B ⊆ B') : Literal m B' w := by
  induction h with
  | wire hw => exact .wire (more hw)
  | zero => exact .zero
  | one => exact .one
  | neg _ ih => exact .neg ih

lemma Live.notCount {R m T k t S} (h : Live R m T k t S) : t ≤ k := by
  induction h with
  | stop => exact le_rfl
  | un _ ih => omega
  | bi _ _ _ ih => omega

lemma Live.binaryBudget {R m T k t S} (h : Live R m T k t S) :
    ∀ (B : Set Nat), (∀ w ∈ S, Literal m B w) → BinaryBudget m T (k-t) B := by
  induction h with
  | stop =>
    intro B hb
    exact .stop (hb _ (by simp))
  | @un k t a U live ih =>
    intro B hb
    rw [show k + 1 - (t + 1) = k - t by omega]
    apply ih B
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hu
    · exact .neg (hb a (Finset.mem_insert_self _ _))
    · exact hb w (Finset.mem_insert_of_mem hu)
  | @bi k t d a b U _ _ live ih =>
    intro B hb
    rw [Nat.succ_sub live.notCount]
    apply BinaryBudget.step d (hb a (by simp)) (hb b (by simp))
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hu
    · exact .wire (Set.mem_insert _ _)
    · exact (hb w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))).widen (Set.subset_insert _ _)

lemma highNotImpossible {R m T k t S} {B : Set Nat} {d : Bool} {a b : Nat}
    (rawA : Literal m B a) (rawB : Literal m B b)
    (input : ∀ w ∈ S, Literal m (insert (op d a b) B) w)
    (low : ∀ q < 13, ¬ BinaryBudget m T q B)
    (cap : k ≤ 13) (two : 2 ≤ t) : ¬Live R m T k t S := by
  intro live
  apply low (k - t + 1) (by omega)
  exact .step d rawA rawB (live.binaryBudget _ input)

lemma Literal.transfer {m B B' w} (h : Literal m B w) (more : ∀ v ∈ B, Literal m B' v) : Literal m B' w := by
  induction h with
  | wire hw => exact more _ hw
  | zero => exact .zero
  | one => exact .one
  | neg _ ih => exact .neg ih

lemma BinaryBudget.transfer {m T q B} (h : BinaryBudget m T q B) :
    ∀ {B'}, (∀ v ∈ B, Literal m B' v) → BinaryBudget m T q B' := by
  induction h with
  | stop ht => intro B' more; exact .stop (ht.transfer more)
  | @step q B a b d ha hb _ ih =>
    intro B' more
    apply BinaryBudget.step d (ha.transfer more) (hb.transfer more)
    apply ih
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact .wire (Set.mem_insert _ _)
    · exact (more _ hv).widen (Set.subset_insert _ _)

def projectBank (p : Nat) (B : Set Nat) : Set Nat := (fun w => w &&& p) '' B

lemma negate_mask {p m : Nat} (hp : m &&& p = p) (w : Nat) :
    (w ^^^ m) &&& p = (w &&& p) ^^^ p := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun x : Nat => x.testBit i) hp
  simp only [Nat.testBit_and, Nat.testBit_xor] at hi ⊢
  cases hw : w.testBit i <;> cases hm : m.testBit i <;> cases hpbit : p.testBit i <;> simp_all

lemma op_mask (d : Bool) (a b p : Nat) : op d a b &&& p = op d (a &&& p) (b &&& p) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [op, Bool.cond_false, Bool.cond_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases a.testBit i <;> cases b.testBit i <;> cases p.testBit i <;> rfl

lemma Literal.project {p m B w} (h : Literal m B w) (hp : m &&& p = p) :
    Literal p (projectBank p B) (w &&& p) := by
  induction h with
  | wire hw => exact .wire (Set.mem_image_of_mem _ hw)
  | zero => simpa using (Literal.zero (m:=p) (B:=projectBank p B))
  | one => rw [hp]; exact .one
  | neg _ ih => rw [negate_mask hp]; exact .neg ih

lemma BinaryBudget.project {p m T q B} (h : BinaryBudget m T q B) (hp : m &&& p = p) :
    BinaryBudget p (T &&& p) q (projectBank p B) := by
  induction h with
  | stop ht => exact .stop (ht.project hp)
  | @step q B a b d ha hb _ ih =>
    have bank : projectBank p (insert (op d a b) B) = insert (op d (a &&& p) (b &&& p)) (projectBank p B) := by
      simp only [projectBank, Set.image_insert_eq, op_mask]
    rw [bank] at ih
    exact .step d (ha.project hp) (hb.project hp) ih

def FlatOrConst (p i j w : Nat) : Prop := w.testBit i = w.testBit j ∨ w &&& p = 0 ∨ w &&& p = p

lemma Literal.flatOrConst {m B w p i j} (h : Literal m B w) (hp : m &&& p = p) (hm : m.testBit i = m.testBit j)
    (hs : ∀v ∈ B, FlatOrConst p i j v) : FlatOrConst p i j w := by
  induction h with
  | wire hw => exact hs _ hw
  | zero => exact Or.inl (by simp)
  | one => exact Or.inl hm
  | @neg v _ ih =>
    rcases ih with hi | hi | hi
    · exact Or.inl (by simp [Nat.testBit_xor, hi, hm])
    · exact Or.inr (Or.inr (by rw [negate_mask hp, hi, Nat.zero_xor]))
    · exact Or.inr (Or.inl (by rw [negate_mask hp, hi, Nat.xor_self]))

lemma liftedConstGate {m p B} (hp : m &&& p = p) (d : Bool) {a b : Nat}
    (ha : Literal m B a) (hb : Literal m B b) (hc : a &&& p = 0 ∨ a &&& p = p ∨ b &&& p = 0 ∨ b &&& p = p) :
    Literal p (projectBank p B) (op d a b &&& p) := by
  have ab : (a &&& p) &&& p = a &&& p := by rw [Nat.and_assoc, Nat.and_self]
  have bb : (b &&& p) &&& p = b &&& p := by rw [Nat.and_assoc, Nat.and_self]
  have ao : (a &&& p) ||| p = p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_or, Nat.testBit_and]; cases a.testBit i <;> cases p.testBit i <;> rfl
  have bo : (b &&& p) ||| p = p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_or, Nat.testBit_and]; cases b.testBit i <;> cases p.testBit i <;> rfl
  rw [op_mask]
  rcases hc with h | h | h | h <;> cases d <;> simp only [op, Bool.cond_false, Bool.cond_true, h, Nat.and_zero, Nat.zero_and,
    Nat.zero_or, Nat.or_zero, ab, bb, ao, bo, Nat.and_comm p, Nat.or_comm p] <;>
    first | exact .zero | exact .one | exact ha.project hp | exact hb.project hp

lemma BinaryBudget.dropConst {m T q B p i j} (prog : BinaryBudget m T q B)
    (hp : m &&& p = p) (hm : m.testBit i = m.testBit j) (hard : ¬FlatOrConst p i j T) :
    (∀v ∈ B, FlatOrConst p i j v) →
    ∃ k < q, BinaryBudget p (T &&& p) k (projectBank p B) := by
  induction prog with
  | stop ht => exact fun h => False.elim (hard (ht.flatOrConst hp hm h))
  | @step q B a b d ha hb nxt ih =>
    intro base
    have altA := ha.flatOrConst hp hm base
    have altB := hb.flatOrConst hp hm base
    by_cases hc : a &&& p = 0 ∨ a &&& p = p ∨ b &&& p = 0 ∨ b &&& p = p
    · refine ⟨q, by omega, (nxt.project hp).transfer ?_⟩
      rintro v ⟨w,hw,rfl⟩
      rcases Set.mem_insert_iff.mp hw with rfl | hw
      · exact liftedConstGate hp d ha hb hc
      · exact .wire (Set.mem_image_of_mem _ hw)
    · have h1 : a.testBit i = a.testBit j := by unfold FlatOrConst at altA; tauto
      have h2 : b.testBit i = b.testBit j := by unfold FlatOrConst at altB; tauto
      obtain ⟨k,hk,pr⟩ := ih (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl (by cases d <;> simp [op, Nat.testBit_and, Nat.testBit_or, h1, h2])
        · exact base _ hu)
      refine ⟨k+1, by omega, BinaryBudget.step d (ha.project hp) (hb.project hp) ?_⟩
      simpa only [projectBank, Set.image_insert_eq, op_mask] using pr
end PEqualNP.Outside.L_meta_8399
