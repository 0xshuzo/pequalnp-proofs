import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9815.RawSchedule
open PEqualNP.CircuitLowerBounds

structure Instruction where
  slot : Nat
  gate : Gate

def val (g : Gate) (w : Nat → Bool) : Bool := g.op.eval (g.inputs.map w)

def put (j : Nat) (v : Bool) (w : Nat → Bool) : Nat → Bool :=
  fun i => if i = j then v else w i

def exec (g : Instruction) (w : Nat → Bool) : Nat → Bool :=
  put g.slot (val g.gate w) w

def run (program : List Instruction) (w : Nat → Bool) : Nat → Bool :=
  program.foldl (fun bank g => exec g bank) w

theorem unread (g : Gate) (i : Nat) (hi : i ∉ g.inputs) (v : Bool)
    (w : Nat → Bool) : val g (put i v w) = val g w := by
  unfold val
  congr 1
  apply List.map_congr_left
  intro j hj
  have ne : j ≠ i := by intro eq; exact hi (eq ▸ hj)
  simp [put,ne]

theorem independentSwap (a b : Instruction) (different : a.slot ≠ b.slot)
    (aIgnored : a.slot ∉ b.gate.inputs) (bIgnored : b.slot ∉ a.gate.inputs)
    (w : Nat → Bool) : exec b (exec a w) = exec a (exec b w) := by
  unfold exec
  rw [unread _ _ aIgnored, unread _ _ bIgnored]
  funext j
  by_cases h : j = a.slot
  · subst j
    simp [put,different]
  · by_cases k : j = b.slot
    · subst j
      simp [put,h]
    · simp [put,h,k]

def Independent (a b : Instruction) : Prop :=
  a.slot ≠ b.slot ∧ a.slot ∉ b.gate.inputs ∧ b.slot ∉ a.gate.inputs

theorem movePast (a : Instruction) (xs : List Instruction)
    (h : ∀ b ∈ xs, Independent a b) (w : Nat → Bool) :
    run xs (exec a w) = exec a (run xs w) := by
  induction xs generalizing w with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨ne,ab,ba⟩ := h b (by simp)
    change run bs (exec b (exec a w)) = exec a (run bs (exec b w))
    rw [independentSwap a b ne ab ba]
    exact ih (fun c hc => h c (by simp [hc])) _

def Cross (take : Instruction → Bool) : List Instruction → Prop
  | [] => True
  | a :: xs => (take a = false → ∀ b ∈ xs, take b = true → Independent a b) ∧ Cross take xs

theorem distribute (take : Instruction → Bool) (program : List Instruction)
    (cross : Cross take program)
    (w : Nat → Bool) :
    run program w = run (program.filter fun a => !(take a)) (run (program.filter take) w) := by
  induction program generalizing w with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨head,small⟩ := cross
    change run rest (exec a w) = _
    rw [ih small]
    cases ha : take a with
    | true => simp [ha,run,List.foldl_cons]
    | false =>
      have pass : ∀ b ∈ rest.filter take, Independent a b := by
        intro b hb
        obtain ⟨member,yes⟩ := List.mem_filter.mp hb
        exact head ha b member yes
      simp only [List.filter_cons,ha,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
      change run (rest.filter fun b => !(take b)) (run (rest.filter take) (exec a w)) =
        run (rest.filter fun b => !(take b)) (exec a (run (rest.filter take) w))
      rw [movePast a (rest.filter take) pass]

def raw (n : Nat) (g : Instruction) : Bool :=
  g.gate.inputs.all (fun j => decide (j < n))

theorem allRawFirst (n : Nat) (xs : List Instruction)
    (order : xs.Pairwise (fun a b => a.slot < b.slot))
    (fresh : ∀ a ∈ xs, n ≤ a.slot)
    (valid : ∀ a ∈ xs, ∀ j ∈ a.gate.inputs, j < a.slot)
    (w : Nat → Bool) :
    run xs w = run (xs.filter fun a => !(raw n a)) (run (xs.filter (raw n)) w) := by
  apply distribute
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    obtain ⟨before,after⟩ := List.pairwise_cons.mp order
    constructor
    · intro _ b hb rawb
      have lt := before b hb
      have freshA := fresh a (by simp)
      refine ⟨by omega,?_,?_⟩
      · intro readA
        have atom := (List.all_eq_true.mp rawb) a.slot readA
        have : a.slot < n := of_decide_eq_true atom
        omega
      · intro readB
        have := valid a (by simp) b.slot readB
        omega
    · exact ih after (fun b hb => fresh b (by simp [hb]))
        (fun b hb => valid b (by simp [hb]))

end PEqualNP.Outside.L_meta_9815.RawSchedule
