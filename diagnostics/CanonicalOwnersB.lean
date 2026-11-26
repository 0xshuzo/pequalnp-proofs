import PEqualNP.Defs
/-
A checker for LRAT unsatisfiability certificates (RUP steps) written so that the Lean KERNEL can
evaluate it fast: every loop is a raw recursor (`List.rec`, `Nat.rec`, `Trie.rec`) and every
branch a raw `Bool.rec` / `Option.rec` (pattern matching compiles to matchers and `brecOn`, which
measured three times slower in the kernel); there is no HashMap, no USize, no Array, no
well-founded recursion. A certificate accepted by `check` becomes a theorem through
`check_sound` and `decide +kernel`, with no native code.

Representation:
* a literal is a natural number: variable `v` positive is `2 * v`, negative is `2 * v + 1`;
* a formula is a `List (List Nat)`; the certificate gives every clause a key in the store
  (formula clauses through a key list, derived clauses through their first token), so that the
  most used clauses can sit near the root;
* an assignment is `a : Nat → Bool`; literal `l` is true under `a` iff `a (l / 2) = (l % 2 == 0)`;
* a stored clause is ONE natural number, its bitmask (bit `l` set iff `l` is in the clause), in
  a binary trie keyed by key;
* the certificate is a flat token list: per step, the key of the new clause, its literals, `0`,
  then its hints `h1 u1 h2 u2 ... hk`: each `h` a clause key, each `u` the literal that hint makes
  unit (supplied because `Nat.log2` is not a kernel primitive), `hk` the hint that is falsified;
  the step ends there. The run succeeds when an empty clause is derived;
* during a RUP check the only state is ONE bitset `F` of literals known false (it starts as
  the new clause): reading a hint is a few GMP operations (`land`, `xor`, `shiftLeft`, `beq`),
  primitive in the kernel, whatever the clause length;
* a long certificate can be cut into segments, one theorem each (`checkFirst`, `checkSeg`,
  `checkLast`): the clauses still to be used at a cut are stated as a list, which bounds the
  kernel's memory per theorem (its caches live for one declaration) and lets the segments be
  checked in parallel. Soundness never depends on the keys, the unit literals, or the cuts
  being chosen well: a bad choice only makes the checker reject.
-/

namespace PEqualNP.Library.LRAT

-- The definitions use raw recursors, which the code generator does not compile; they are for
-- the kernel only.
noncomputable section

/-- The negation of a literal (flip the low bit). -/
def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

/-- Bit `l` of `T`, written with the kernel's GMP primitives only. -/
def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

/-- `T` with bit `u` set. -/
def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

theorem bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

theorem bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

/-- The truth value of literal `l` under the assignment `a`. -/
def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

/-- A clause is satisfied by `a` when one of its literals is true. -/
def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

/-- A formula (list of clauses) is satisfiable when one assignment satisfies every clause. -/
def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

theorem litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

/-! ## The clause store: a binary trie keyed by clause id -/

/-- Key `0` sits at the root, odd key `2j+1` at key `j` of the left child, even key `2j+2` at
key `j` of the right child. -/
inductive Trie where
  | nil : Trie
  | node (v : Option Nat) (l r : Trie) : Trie

namespace Trie

def get (t : Trie) : Nat → Option Nat :=
  Trie.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def root (t : Trie) : Option Nat := Trie.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t
def left (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ l _ _ _ => l) t
def right (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ _ r _ _ => r) t

/-- Store `o` at key `k`; `fuel` bounds the depth (64 is plenty). Out of fuel: no change. -/
def set (fuel : Nat) : Trie → Nat → Option Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → Option Nat → Trie) (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec (.node t.root t.left (ih t.right (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (.node t.root (ih t.left (Nat.div k (nat_lit 2)) o) t.right)
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (.node o t.left t.right) (Nat.beq k (nat_lit 0))) fuel

/-- Every clause stored in the trie has property `P`. -/
def All (P : Nat → Prop) : Trie → Prop
  | .nil => True
  | .node v l r => (∀ c, v = some c → P c) ∧ All P l ∧ All P r

theorem All.get {P : Nat → Prop} :
    ∀ {t : Trie} {k : Nat} {c : Nat}, All P t → t.get k = some c → P c
  | .nil, _, _, _, h => by simp [Trie.get] at h
  | .node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec (r.get _) (l.get _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact All.get hr h
      · rw [h1] at h; exact All.get hl h
    · rw [h0] at h; exact hv c h

theorem All.root {P : Nat → Prop} {t : Trie} (h : All P t) :
    ∀ c, t.root = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

theorem All.left {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.left := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

theorem All.right {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.right := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

theorem All.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : Trie} (k : Nat) {o : Option Nat},
      All P t → (∀ c, o = some c → P c) → All P (Trie.set fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change All P (Bool.rec (Bool.rec (.node t.root t.left (Trie.set fuel t.right _ o))
      (.node t.root (Trie.set fuel t.left _ o) t.right) _) (.node o t.left t.right) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, All.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, All.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

end Trie

/-! ## Bit lemmas -/

theorem bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

theorem bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

theorem bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

theorem bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

/-! ## Clauses as bitmasks -/

/-- The bitmask of a clause. -/
def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

theorem bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

/-! ## The checker -/

/-- The type of the token machine's continuation: store, key slot, mode, `C`, `F`, `P`. -/
abbrev Cont := Trie → Nat → Bool → Nat → Nat → Nat → Bool

/-! Each branch of the machine is its own constant, so that the kernel instantiates only the
branch taken (measured: same time, a third of the memory). -/

/-- Reading a clause. The first token of a step is the key the new clause will be stored
under (the slot `id` then holds key + 1; `0` means a key is expected). After it, `0` ends the
clause and starts its hints with `F := C`, and a literal joins `C`. -/
def stepRead (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))

/-- `x` is the unit literal claimed for the pending hint: `P` must be exactly `{x}`; then `x`
is true, so its negation joins `F`. -/
def stepUnit (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))

/-- The hint clause is `D`: if every literal of `D` is in `F`, the clause `C` is derived (and if
`C` is empty, the certificate is accepted) and stored under its key; otherwise the literals of
`D` not in `F` wait for the claimed unit literal. -/
def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (db.set 64 (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))

/-- `x` is a hint key: look the clause up (a missing clause rejects). -/
def stepHint (k : Cont) (db : Trie) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) (db.get x)

/-- One token. State: the store `db`, the key slot `id`, the mode (`false`: reading a new
clause into the bitmask `C`; `true`: reading its hints), the bitset `F` of literals known false,
and `P`: `0` when a hint key is expected, otherwise the bitset of literals not false of the last
hint clause, waiting for its unit literal. `k` is the machine on the remaining tokens. -/
def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode

/-- The end of the tokens, when the certificate must have derived the empty clause: reject. -/
def stop : Cont := fun _ _ _ _ _ _ => false

/-- The token machine on a token list, then the continuation `e`. -/
def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks

/-- The machine on the `W`-bit fields of one word (lowest first, up to a sentinel top bit `1`;
`M = 2 ^ W - 1`; at most `fuel` fields), then `k`. No token list is built. -/
def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w

/-- At most this many fields per word. -/
def fuelW : Nat := 1024

/-- The machine on a packed certificate (a list of words of `W`-bit fields), then `e`. -/
def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words

/-- Is the clause of the entry `q :: lits` stored under key `q - 1`? (Entries carry key + 1 so
that no entry token is `0`, the clause separator of `decodeF`.) -/
def entryIn (db : Trie) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q (nat_lit 1)))) e

/-- The end of a segment: every entry `q :: lits` of `B` must be stored under key `q - 1`. -/
def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B

/-- Store the formula's clauses: clause `i` under key `q - 1` where `q` is the `i`-th entry of
`fk`; `q = 0` leaves the clause out. -/
def loadF : List (List Nat) → List Nat → Trie → Trie
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (t.set 64 (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))

/-- Store the entries `q :: lits` of a list of live clauses, under key `q - 1`. -/
def loadB : List (List Nat) → Trie → Trie
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (t.set 64 (Nat.sub q 1) (some (mask lits)))

/-- The checker, one theorem: formula `F` with keys `fk`, certificate as a token list. -/
def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk .nil) 0 false 0 0 0

/-- The checker, one theorem: formula `F` with keys `fk`, packed certificate. -/
def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk .nil) 0 false 0 0 0

/-- First segment of a cut certificate: from the formula to the live clauses `B`. -/
def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk .nil) 0 false 0 0 0

/-- A middle segment: from the live clauses `B` to the live clauses `B'`. -/
def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B .nil) 0 false 0 0 0

/-- The last segment: from the live clauses `B` to the empty clause. -/
def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B .nil) 0 false 0 0 0

/-! ## Soundness -/

section Soundness

variable (a : Nat → Bool)

/-- A bitmask clause is satisfied by `a`. -/
def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

/-- Every literal in the bitset is false under `a`. -/
def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

/-- Every entry `q :: lits` of a list of live clauses has its clause `lits` satisfied. -/
def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail

/-- The invariant of hint mode: if `a` falsifies the clause `C` being derived, then `F` holds
only false literals, and a pending `P` contains a true literal. -/
def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)

/-- A satisfied clause `D` keeps a true literal outside the false literals `F`. -/
theorem witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

/-- A continuation is good for `Q` when it accepts only, from a state satisfying the invariant
(the store holds only clauses `a` satisfies, and the hint-mode invariant), if `Q` holds. -/
def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, db.All (MaskSat a) → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

theorem stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

theorem tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    · -- unit literal
      rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    · -- hint key
      rw [hP] at h
      change Option.rec false (stepClause k db id C F) (db.get x) = true at h
      cases hg : db.get x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := Trie.All.get hdb hg
        change Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine hk db id true C F _ hdb (fun _ hC => ⟨(hinv hC).1, Or.inr ?_⟩) h
          exact witness_U a (hinv hC).1 hD
        · rw [hU] at h
          -- the clause `C` is satisfied by `a`
          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (Trie.All.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

theorem runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

theorem runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

theorem runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

theorem clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

theorem maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

theorem verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q 1)) = true
            at he
          cases hg : db.get (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := Trie.All.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

theorem loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : Trie}, t.All (MaskSat a) →
    (∀ c ∈ F, ClauseSat a c) → (loadF F fk t).All (MaskSat a)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact Trie.All.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

theorem loadB_all : ∀ (B : List (List Nat)) {t : Trie}, t.All (MaskSat a) →
    EntriesSat a B → (loadB B t).All (MaskSat a)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact Trie.All.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness

/-- SOUNDNESS (token list). If the checker accepts the token list `toks` for the formula `F`
(with keys `fk`), then no assignment satisfies every clause of `F`. -/
theorem check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

/-- SOUNDNESS (packed certificate, one theorem). -/
theorem checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

/-- SOUNDNESS of a first segment: every assignment satisfying `F` satisfies the live clauses
`B`. -/
theorem checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

/-- SOUNDNESS of a middle segment. -/
theorem checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

/-- SOUNDNESS of the last segment. -/
theorem checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

/-! ## Packed certificates

Elaborating a long list literal costs about 0.2 ms per number, so certificates are stored as a
list of big numbers ("words"), each holding several `W`-bit fields (lowest first) under a
sentinel top bit; `unpack` turns them back into the token list, lazily, inside the kernel. The
soundness theorem holds for every token list, so `unpack` needs no proof. -/

/-- The fields of one word, prepended to `rest`; `fuel` bounds the number of fields. -/
def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w

/-- The token list of a packed certificate (fields of `W` bits, at most 1024 per word). -/
def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words

/-- A formula from a token list: each clause is its literals followed by `0`. -/
def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks

end

end PEqualNP.Library.LRAT

namespace PEqualNP.Outside.L_pcx_120.Oldest
open PEqualNP.Library.LRAT
def axis : List (Nat × Bool) := [(7,false), (56,false), (448,false), (3584,false), (9,true), (65,true), (72,true), (513,true), (520,true), (576,true), (18,true), (130,true), (144,true), (1026,true), (1040,true), (1152,true), (36,true), (260,true), (288,true), (2052,true), (2080,true), (2304,true)]
def violates (x : Nat) (s : Nat × Bool) : Bool := (x &&& s.1) == (if s.2 then s.1 else 0)
def sumDirs (a : Nat) : List Nat → Nat
  | [] => 0
  | b::bs => (a ^^^ b) ^^^ sumDirs a bs

theorem zeroDirs (v : Nat → Bool) (lin : ∀ a b, v (a ^^^ b) = Bool.xor (v a) (v b))
    (z : v 0 = false) (a : Nat) (bs : List Nat) (h : ∀ b ∈ bs, v a = v b) :
    v (sumDirs a bs) = false := by
  induction bs with
  | nil => exact z
  | cons b rest ih =>
    have e := h b (by simp)
    have t := ih (fun y hy => h y (by simp [hy]))
    simp only [sumDirs,lin,t,e]
    cases v b <;> rfl

def labels (x : Nat) : List Nat :=
  ((List.range 22).filter (fun i => violates x (axis.getD i (0,false)))).map (fun i => i+1)

def AllOn (c : Nat → Bool) (s : List Nat) : Prop := ∀ i ∈ s, c i=true
def AnyOn (c : Nat → Bool) (s : List Nat) : Prop := ∃ i ∈ s, c i=true
def sub (a b : List Nat) : Bool := a.all (fun i => b.contains i)

theorem sub_mem {a b : List Nat} (h : sub a b=true) {i : Nat} (hi : i∈a) : i∈b := by
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h _ hi)

structure Span where
  members : List Nat
  a : Nat
  dirs : List (List Nat)

def spanGood (w : Span) : Bool :=
  sub (labels w.a) w.members && (List.range 12).all (fun i =>
    let ds := w.dirs.getD i []
    ds.all (fun b => sub (labels b) w.members) && sumDirs w.a ds == (1 <<< i))

structure Tri where
  lo : List Nat
  hi : List Nat
  a : Nat
  b : Nat
  c : Nat

def triGood (t : Tri) : Bool :=
  (sub (labels t.a) t.lo && sub (labels t.b) t.lo) &&
  (sub (labels t.c) t.lo && sub (labels (t.a ^^^ t.b ^^^ t.c)) t.hi)

structure Group where
  included : List Nat
  excluded : List Nat
def Matches (c : Nat → Bool) (g : Group) : Prop :=
  AllOn c g.included ∧ ∀ i ∈ g.excluded, c i=false

structure FlatOwner (chosen : Nat → Bool) (region : Nat → Prop) : Prop where
  exclusive : ∀ x, AllOn chosen (labels x) → region x
  upper : ∀ x, region x → AnyOn chosen (labels x)
  closed : ∀ x y z, region x → region y → region z → region (x ^^^ y ^^^ z)
  normal : ∃ v : Nat → Bool, (∀ x y, v (x ^^^ y)=Bool.xor (v x) (v y)) ∧ v 0=false ∧
    (∃ i<12, v (1 <<< i)=true) ∧ (∀ x y, region x → region y → v x=v y)

theorem span_excludes {chosen region} (O : FlatOwner chosen region) {w : Span}
    (H : spanGood w=true) : ¬ AllOn chosen w.members := by
  intro J
  obtain ⟨v,lin,zero,⟨i,hi,nz⟩,flat⟩ := O.normal
  simp only [spanGood,Bool.and_eq_true,List.all_eq_true] at H
  have ha := O.exclusive w.a (fun j hj => J j (sub_mem H.1 hj))
  obtain ⟨hd,he⟩ := H.2 i (List.mem_range.mpr hi)
  have z := zeroDirs v lin zero w.a (w.dirs.getD i []) (fun b hb => flat _ _ ha
    (O.exclusive b (fun j hj => J j (sub_mem (hd b hb) hj))))
  rw [beq_iff_eq.mp he,nz] at z
  contradiction

theorem tri_implies {chosen region} (O : FlatOwner chosen region) {t : Tri}
    (H : triGood t=true) (J : AllOn chosen t.lo) : AnyOn chosen t.hi := by
  simp only [triGood,Bool.and_eq_true] at H
  have r {x : Nat} (h : sub (labels x) t.lo=true) : region x :=
    O.exclusive x (fun j hj => J j (sub_mem h hj))
  obtain ⟨i,hi,onv⟩ := O.upper _ (O.closed _ _ _ (r H.1.1) (r H.1.2) (r H.2.1))
  exact ⟨i,sub_mem H.2.2 hi,onv⟩

def negs (xs : List Nat) := xs.map (fun i => 2*i+1)
def poss (xs : List Nat) := xs.map (fun i => 2*i)

theorem reject_neg (a : Nat → Bool) (xs : List Nat) (no : ¬ AllOn a xs) : ClauseSat a (negs xs) := by
  classical
  change ¬ ∀ i ∈ xs, a i=true at no
  push_neg at no
  obtain ⟨i,hi,off⟩ := no
  refine ⟨2*i+1,List.mem_map.mpr ⟨i,hi,rfl⟩,?_⟩
  have d : (2*i+1)/2=i := by omega
  have e : (2*i+1)%2=1 := by omega
  cases b : a i <;> simp_all [litVal,d,e]

theorem accept_pos (a : Nat → Bool) (xs : List Nat) (yes : AnyOn a xs) : ClauseSat a (poss xs) := by
  obtain ⟨i,hi,onv⟩ := yes
  refine ⟨2*i,List.mem_map.mpr ⟨i,hi,rfl⟩,?_⟩
  have d : (2*i)/2=i := by omega
  have e : (2*i)%2=0 := by omega
  simp [litVal,d,e,onv]

theorem clause_or {a : Nat → Bool} {l r : List Nat} (h : ClauseSat a l ∨ ClauseSat a r) :
    ClauseSat a (l++r) := by
  rcases h with ⟨i,hi,h⟩ | ⟨i,hi,h⟩
  · exact ⟨i,List.mem_append.mpr (Or.inl hi),h⟩
  · exact ⟨i,List.mem_append.mpr (Or.inr hi),h⟩

def spanClause (w : Span) := negs w.members
def triClause (t : Tri) := negs t.lo ++ poss t.hi
def exactClause (g : Group) := negs g.included ++ poss g.excluded
set_option maxRecDepth 16384 in
def spans : List Span := [
⟨[1, 2],640,[[1280, 1281], [768, 770], [644], [1280, 1288], [768, 784], [672], [896, 1088, 1280], [768, 896], [896], [1280, 1792], [768, 1792], [768, 1088, 1792, 2112]]⟩,
⟨[1, 3],528,[[1056, 1057], [544, 546], [532], [560, 1032, 1056], [544, 560], [560], [1056, 1120], [544, 672], [784], [1056, 1568], [544, 1568], [544, 1032, 1568, 2056]]⟩,
⟨[2, 3],514,[[518, 1025, 1028], [516, 518], [518], [1028, 1036], [516, 532], [546], [1028, 1092], [516, 644], [770], [1028, 1540], [516, 1540], [516, 1025, 1540, 2049]]⟩,
⟨[1, 4],80,[[160, 161], [96, 98], [84], [112, 136, 160], [96, 112], [112], [160, 224], [96, 224], [96, 136, 224, 264], [160, 672], [96, 1120], [2128]]⟩,
⟨[2, 4],66,[[70, 129, 132], [68, 70], [70], [132, 140], [68, 84], [98], [132, 196], [68, 196], [68, 129, 196, 257], [132, 644], [68, 1092], [2114]]⟩,
⟨[3, 4],10,[[14, 17, 20], [12, 14], [14], [20, 28], [12, 28], [12, 17, 28, 33], [20, 84], [12, 140], [266], [20, 532], [12, 1036], [2058]]⟩,
⟨[2, 5, 6],644,[[1092, 1093], [1092, 1093, 2113, 2114], [1089, 1093], [1281, 1289], [2113, 2129], [1089, 1121], [1281, 1345], [770, 1092, 1345, 2113, 2114], [1089, 1345], [770, 1281, 2114, 3137], [2113, 3137], [1089, 3137]]⟩,
⟨[3, 5, 6],532,[[1036, 1037], [1036, 1037, 2057, 2058], [1033, 1037], [1057, 1065], [546, 1036, 1065, 2057, 2058], [1033, 1065], [1057, 1121], [2057, 2185], [1033, 1289], [546, 1057, 2058, 3081], [2057, 3081], [1033, 3081]]⟩,
⟨[3, 6, 8],529,[[532, 533], [532, 533, 545, 546], [533], [532, 561, 1036, 1057], [545, 561], [561], [1057, 1121], [545, 673], [785], [1057, 1569], [545, 1569], [532, 546, 1036, 1569, 2058]]⟩,
⟨[3, 7, 9],522,[[526, 546, 1036, 1057], [524, 526], [526], [532, 540], [524, 540], [532, 540, 546], [1036, 1100], [524, 652], [778], [1036, 1548], [524, 1548], [1036, 1548, 2058]]⟩,
⟨[4, 7, 9],74,[[78, 98, 140, 161], [76, 78], [78], [84, 92], [76, 92], [84, 92, 98], [140, 204], [76, 204], [140, 204, 266], [140, 652], [76, 1100], [2122]]⟩,
⟨[1, 8, 9],648,[[672, 673], [776, 778], [652], [672, 680], [672, 680, 776, 784], [680], [672, 904, 1120, 1288], [776, 904], [904], [1288, 1800], [776, 1800], [672, 784, 1120, 1800, 2128]]⟩,
⟨[4, 6, 11],81,[[82, 83], [83], [82, 83, 84], [84, 113, 140, 161], [97, 113], [113], [161, 225], [97, 225], [82, 84, 97, 140, 225, 266], [84, 97, 140, 161, 266, 786], [97, 1121], [2129]]⟩,
⟨[1, 9, 13],648,[[672, 776, 1120, 1288, 2128, 2193], [776, 778], [652], [656, 664], [664], [656, 664, 672], [672, 904, 1120, 1288], [776, 904], [904], [1288, 1800], [776, 1800], [656, 672, 776, 1120, 1800, 2128]]⟩,
⟨[1, 11, 13],656,[[2192, 2193], [784, 786], [660], [688, 784, 1120, 1288, 2128, 2192], [672, 688], [688], [784, 912, 2128, 2192], [784, 912], [912], [2192, 2704], [672, 1120, 2128, 2704], [2704]]⟩,
⟨[4, 12, 14],84,[[140, 142, 161, 162], [140, 142], [138, 142], [162, 170], [98, 140, 170], [138, 170], [162, 226], [98, 226], [98, 138, 226, 266], [162, 674], [98, 1122], [138, 2186]]⟩,
⟨[6, 8, 13, 14],657,[[660, 661], [660, 661, 1121, 1122], [661], [689, 785, 1122, 1290, 2129, 2193], [673, 689], [689], [785, 913, 2129, 2193], [785, 913], [913], [2193, 2705], [673, 1121, 2129, 2705], [2705]]⟩,
⟨[2, 13, 16],644,[[1156, 1157], [770, 1157, 1281], [1153, 1157], [1156, 1164], [660], [1153, 1185], [1156, 1220], [1092, 1220], [1092, 1153, 1220, 1281], [1156, 1668], [1668], [770, 1092, 1153, 1281, 1668, 2114]]⟩,
⟨[1, 19, 20],672,[[1312, 1313], [800, 802], [2128, 2132], [784, 816, 1288, 1312], [800, 816], [784, 816], [928, 1120, 1312], [800, 928], [928], [1312, 1824], [800, 1824], [784, 1120, 1824, 2128]]⟩,
⟨[2, 19, 20],644,[[770, 1092, 1281, 2118, 2180], [2116, 2118], [2114, 2118], [2180, 2188], [2116, 2132], [770, 802], [2180, 2244], [2116, 2244], [770, 2114, 2244], [2180, 2692], [1092, 2116, 2692], [2692]]⟩,
⟨[1, 17, 21],672,[[2208, 2209], [2144, 2146], [676], [784, 1120, 1288, 2160, 2208], [2144, 2160], [2128, 2160], [2208, 2272], [2144, 2272], [784, 2128, 2272], [2208, 2720], [1120, 2144, 2720], [2720]]⟩,
⟨[4, 17, 21],84,[[98, 102, 161, 164], [100, 102], [98, 102], [116, 140, 164], [100, 116], [116], [164, 228], [100, 228], [98, 140, 228, 266], [164, 676], [100, 1124], [98, 2146]]⟩,
⟨[1, 18, 21],672,[[2208, 2209], [2144, 2146], [784, 788], [784, 1120, 1288, 2160, 2208], [2144, 2160], [2128, 2160], [2208, 2272], [2144, 2272], [784, 2128, 2272], [2208, 2720], [1120, 2144, 2720], [2720]]⟩,
⟨[2, 18, 21],644,[[770, 774, 1281, 1284], [772, 774], [770, 774], [1284, 1292], [772, 788], [2114, 2146], [900, 1092, 1284], [772, 900], [900], [1284, 1796], [772, 1796], [770, 1092, 1796, 2114]]⟩,
⟨[3, 18, 21],532,[[2082, 2083], [2081, 2083], [1036, 1057, 2058, 2083], [2082, 2090], [546, 1036, 1057, 2081, 2090], [2058, 2090], [2082, 2146], [2081, 2209], [788], [2082, 2594], [546, 1057, 2081, 2594], [546, 2594]]⟩,
⟨[4, 18, 21],84,[[98, 140, 161, 270, 276], [268, 270], [266, 270], [276, 284], [268, 284], [98, 266, 284], [276, 340], [140, 268, 340], [340], [276, 788], [268, 1292], [98, 2146]]⟩,
⟨[1, 20, 21],672,[[2208, 2209], [2144, 2146], [2128, 2132], [784, 1120, 1288, 2160, 2208], [2144, 2160], [2128, 2160], [2208, 2272], [2144, 2272], [784, 2128, 2272], [2208, 2720], [1120, 2144, 2720], [2720]]⟩,
⟨[2, 19, 22],644,[[2306, 2307], [2305, 2307], [1092, 1281, 2114, 2307], [2306, 2314], [2305, 2321], [770, 802], [2306, 2370], [770, 1092, 1281, 2305, 2370], [2114, 2370], [2306, 2818], [770, 1281, 2305, 2818], [770, 2818]]⟩,
⟨[3, 20, 22],532,[[546, 1036, 1057, 2062, 2068], [2060, 2062], [2058, 2062], [2068, 2076], [2060, 2076], [546, 2058, 2076], [2068, 2132], [2060, 2188], [2058, 2314], [2068, 2580], [1036, 2060, 2580], [2580]]⟩,
⟨[2, 21, 22],644,[[2306, 2307], [2305, 2307], [1092, 1281, 2114, 2307], [2306, 2314], [2305, 2321], [2114, 2146], [2306, 2370], [770, 1092, 1281, 2305, 2370], [2114, 2370], [2306, 2818], [770, 1281, 2305, 2818], [770, 2818]]⟩,
⟨[3, 21, 22],532,[[2082, 2083], [2081, 2083], [1036, 1057, 2058, 2083], [2082, 2090], [546, 1036, 1057, 2081, 2090], [2058, 2090], [2082, 2146], [2081, 2209], [2058, 2314], [2082, 2594], [546, 1057, 2081, 2594], [546, 2594]]⟩,
⟨[17, 20, 21, 22],676,[[2146, 2150, 2209, 2212], [2148, 2150], [2146, 2150], [2132, 2164, 2188, 2212], [2148, 2164], [2132, 2164], [2212, 2276], [2148, 2276], [2146, 2188, 2276, 2314], [2212, 2724], [1124, 2148, 2724], [2724]]⟩,
⟨[18, 20, 21, 22],788,[[2132, 2146, 2188, 2209, 2318, 2324], [2316, 2318], [2314, 2318], [2324, 2332], [2316, 2332], [2132, 2146, 2314, 2332], [2324, 2388], [2132, 2188, 2316, 2388], [2132, 2388], [2324, 2836], [1292, 2316, 2836], [2836]]⟩,
⟨[19, 20, 21, 22],802,[[2338, 2339], [2337, 2339], [2188, 2209, 2314, 2339], [2338, 2346], [2132, 2146, 2188, 2209, 2337, 2346], [2314, 2346], [2338, 2402], [2146, 2209, 2337, 2402], [2146, 2402], [2338, 2850], [1313, 2337, 2850], [2850]]⟩
]
set_option maxRecDepth 16384 in
def triples : List Tri := [
⟨[1, 5],[8],672,1288,1289⟩,
⟨[2, 5],[9],644,1281,1289⟩,
⟨[3, 5],[8],532,1036,1289⟩,
⟨[4, 5],[6],98,266,1289⟩,
⟨[2, 6],[8],644,1092,1121⟩,
⟨[3, 6],[10],546,1057,1121⟩,
⟨[4, 6],[7],140,161,1121⟩,
⟨[1, 7],[9],672,1120,1100⟩,
⟨[2, 7],[9],644,1092,1100⟩,
⟨[4, 7],[6],140,161,1100⟩,
⟨[1, 8],[6],672,1120,673⟩,
⟨[2, 8],[6],644,1092,673⟩,
⟨[3, 8],[9],1036,1057,673⟩,
⟨[4, 8],[9],140,161,673⟩,
⟨[1, 9],[7],672,1120,652⟩,
⟨[2, 9],[7],644,1092,652⟩,
⟨[3, 9],[8],1036,1057,652⟩,
⟨[4, 9],[10],84,140,652⟩,
⟨[1, 10],[7],784,1288,596⟩,
⟨[2, 10],[8],1092,1281,596⟩,
⟨[3, 10],[7],532,1036,596⟩,
⟨[4, 10],[9],84,140,596⟩,
⟨[1, 11],[12],672,784,786⟩,
⟨[2, 11],[13],644,770,786⟩,
⟨[3, 11],[14],532,1036,786⟩,
⟨[4, 11],[13],140,266,786⟩,
⟨[6, 11],[14],1121,2129,2130⟩,
⟨[7, 11],[15],1100,2122,2130⟩,
⟨[8, 11],[12],673,785,786⟩,
⟨[9, 11],[13],652,778,786⟩,
⟨[10, 11],[18],596,786,594⟩,
⟨[1, 12],[11],672,784,674⟩,
⟨[2, 12],[14],644,1092,674⟩,
⟨[3, 12],[13],532,546,674⟩,
⟨[5, 12],[14],1289,2185,2186⟩,
⟨[7, 12],[16],1100,2122,2186⟩,
⟨[8, 12],[11],673,785,674⟩,
⟨[9, 12],[17],652,674,650⟩,
⟨[10, 12],[13],596,610,674⟩,
⟨[1, 13],[15],672,1120,660⟩,
⟨[2, 13],[11],644,770,660⟩,
⟨[3, 13],[12],532,546,660⟩,
⟨[4, 13],[12],84,98,660⟩,
⟨[5, 13],[15],1289,2185,2193⟩,
⟨[6, 13],[16],1121,2129,2193⟩,
⟨[8, 13],[17],673,660,657⟩,
⟨[9, 13],[11],652,778,660⟩,
⟨[10, 13],[12],596,610,660⟩,
⟨[1, 14],[12],672,1120,1122⟩,
⟨[2, 14],[12],644,1092,1122⟩,
⟨[3, 14],[15],532,546,1122⟩,
⟨[4, 14],[15],84,98,1122⟩,
⟨[5, 14],[12],1289,2185,1290⟩,
⟨[6, 14],[11],1121,2129,1122⟩,
⟨[7, 14],[17],1100,1122,1098⟩,
⟨[9, 14],[10],778,1122,1290⟩,
⟨[10, 14],[15],596,610,1122⟩,
⟨[1, 15],[13],672,1120,1108⟩,
⟨[2, 15],[13],644,1092,1108⟩,
⟨[3, 15],[14],532,546,1108⟩,
⟨[4, 15],[14],84,98,1108⟩,
⟨[5, 15],[13],1289,2185,1297⟩,
⟨[6, 15],[17],1121,1108,1105⟩,
⟨[7, 15],[11],1100,2122,1108⟩,
⟨[8, 15],[10],785,1108,1297⟩,
⟨[10, 15],[14],596,610,1108⟩,
⟨[1, 16],[13],784,1288,1164⟩,
⟨[2, 16],[14],644,770,1164⟩,
⟨[3, 16],[13],532,1036,1164⟩,
⟨[4, 16],[15],84,140,1164⟩,
⟨[5, 16],[18],1289,1164,1161⟩,
⟨[6, 16],[7],1121,1164,1185⟩,
⟨[7, 16],[12],1100,2122,1164⟩,
⟨[8, 16],[9],673,1164,1185⟩,
⟨[9, 16],[14],652,778,1164⟩,
⟨[1, 17],[18],672,784,676⟩,
⟨[2, 17],[19],644,770,676⟩,
⟨[3, 17],[20],546,2058,676⟩,
⟨[4, 17],[19],140,266,676⟩,
⟨[6, 17],[20],1121,2129,1124⟩,
⟨[7, 17],[21],1100,2122,1124⟩,
⟨[8, 17],[18],673,785,676⟩,
⟨[9, 17],[19],652,778,676⟩,
⟨[10, 17],[12],610,676,612⟩,
⟨[12, 17],[20],674,2186,676⟩,
⟨[13, 17],[21],660,2193,676⟩,
⟨[14, 17],[18],1122,1290,1124⟩,
⟨[15, 17],[19],1108,1297,1124⟩,
⟨[16, 17],[8],1185,676,1188⟩,
⟨[1, 18],[17],672,784,788⟩,
⟨[2, 18],[20],770,2114,788⟩,
⟨[3, 18],[19],532,546,788⟩,
⟨[5, 18],[20],1289,2185,1292⟩,
⟨[7, 18],[22],1100,2122,1292⟩,
⟨[8, 18],[17],673,785,788⟩,
⟨[9, 18],[13],652,788,780⟩,
⟨[10, 18],[19],596,610,788⟩,
⟨[11, 18],[20],786,2130,788⟩,
⟨[13, 18],[22],660,2193,788⟩,
⟨[14, 18],[17],1122,1290,1292⟩,
⟨[15, 18],[8],1297,788,1300⟩,
⟨[16, 18],[19],1164,1185,1292⟩,
⟨[1, 19],[21],784,2128,802⟩,
⟨[2, 19],[17],644,770,802⟩,
⟨[3, 19],[18],532,546,802⟩,
⟨[4, 19],[18],84,98,802⟩,
⟨[5, 19],[21],1289,2185,1313⟩,
⟨[6, 19],[22],1121,2129,1313⟩,
⟨[8, 19],[12],673,802,801⟩,
⟨[9, 19],[17],652,778,802⟩,
⟨[10, 19],[18],596,610,802⟩,
⟨[11, 19],[21],786,2130,802⟩,
⟨[12, 19],[22],674,2186,802⟩,
⟨[14, 19],[6],1122,1313,1314⟩,
⟨[15, 19],[17],1108,1297,1313⟩,
⟨[16, 19],[18],1164,1185,1313⟩,
⟨[1, 20],[17],672,2128,2132⟩,
⟨[2, 20],[18],770,2114,2132⟩,
⟨[3, 20],[21],532,546,2132⟩,
⟨[4, 20],[21],84,98,2132⟩,
⟨[5, 20],[18],1289,2185,2188⟩,
⟨[6, 20],[17],1121,2129,2132⟩,
⟨[7, 20],[15],1100,2132,2124⟩,
⟨[9, 20],[10],652,2132,2188⟩,
⟨[10, 20],[21],596,610,2132⟩,
⟨[11, 20],[18],786,2130,2132⟩,
⟨[12, 20],[17],674,2186,2188⟩,
⟨[13, 20],[10],660,2132,2196⟩,
⟨[15, 20],[22],1108,1297,2132⟩,
⟨[16, 20],[15],1164,2132,2188⟩,
⟨[1, 21],[19],784,2128,2146⟩,
⟨[2, 21],[17],644,2114,2146⟩,
⟨[3, 21],[17],1036,2058,2146⟩,
⟨[4, 21],[20],84,98,2146⟩,
⟨[5, 21],[19],1289,2185,2209⟩,
⟨[6, 21],[14],1121,2146,2145⟩,
⟨[7, 21],[17],1100,2122,2146⟩,
⟨[8, 21],[10],673,2146,2209⟩,
⟨[10, 21],[20],596,610,2146⟩,
⟨[11, 21],[19],786,2130,2146⟩,
⟨[12, 21],[8],674,2209,2210⟩,
⟨[13, 21],[17],660,2193,2209⟩,
⟨[14, 21],[22],1122,1290,2146⟩,
⟨[16, 21],[14],1185,2146,2209⟩,
⟨[1, 22],[21],1120,1288,2314⟩,
⟨[2, 22],[18],1092,2114,2314⟩,
⟨[3, 22],[18],532,2058,2314⟩,
⟨[4, 22],[20],84,266,2314⟩,
⟨[5, 22],[14],1289,2314,2313⟩,
⟨[6, 22],[7],2129,2314,2321⟩,
⟨[7, 22],[18],1100,2122,2314⟩,
⟨[8, 22],[9],785,2314,2321⟩,
⟨[9, 22],[20],652,778,2314⟩,
⟨[11, 22],[8],786,2321,2322⟩,
⟨[12, 22],[19],674,2186,2314⟩,
⟨[13, 22],[12],2193,2314,2321⟩,
⟨[14, 22],[21],1122,1290,2314⟩,
⟨[15, 22],[14],1297,2314,2321⟩,
⟨[4, 6],[5],98,266,1121⟩,
⟨[5, 6, 7],[18],1289,1100,1097⟩,
⟨[1, 6],[5],1120,1288,1121⟩,
⟨[2, 6],[10],770,1281,1121⟩,
⟨[5, 7, 8],[10],2185,2122,673⟩,
⟨[6, 7, 8],[9],1121,1100,673⟩,
⟨[5, 6, 9],[10],2185,2129,652⟩,
⟨[1, 7],[10],784,1288,1100⟩,
⟨[2, 7],[5],1092,1281,1100⟩,
⟨[6, 7, 9],[8],1121,1100,652⟩,
⟨[3, 8],[5],546,2058,673⟩,
⟨[5, 8, 9],[18],1289,652,649⟩,
⟨[6, 8, 9],[7],1121,673,652⟩,
⟨[7, 8, 9],[6],1100,673,652⟩,
⟨[5, 6, 10],[9],2185,2129,596⟩,
⟨[3, 7],[6],1036,1057,1100⟩,
⟨[5, 7, 10],[8],1289,1100,596⟩,
⟨[5, 8, 10],[7],1289,785,596⟩,
⟨[6, 8, 10],[17],1121,596,593⟩,
⟨[7, 8, 10],[5],1100,785,596⟩,
⟨[4, 9],[8],140,161,652⟩,
⟨[5, 9, 10],[6],2185,652,596⟩,
⟨[6, 9, 10],[5],2129,652,596⟩,
⟨[7, 9, 10],[20],2122,596,586⟩,
⟨[1, 11],[14],784,1120,786⟩,
⟨[8, 11],[6],785,786,2130⟩,
⟨[2, 11],[15],770,1092,786⟩,
⟨[9, 11],[7],778,786,2130⟩,
⟨[3, 12],[16],546,1036,674⟩,
⟨[4, 12],[11],84,140,2186⟩,
⟨[10, 12],[7],610,674,2186⟩,
⟨[11, 12, 13],[18],786,660,658⟩,
⟨[6, 11],[8],2129,786,2130⟩,
⟨[2, 12],[16],770,1281,674⟩,
⟨[5, 12],[8],2185,674,2186⟩,
⟨[11, 13, 14],[16],2130,2193,1122⟩,
⟨[12, 13, 14],[15],674,660,1122⟩,
⟨[7, 11],[9],2122,786,2130⟩,
⟨[11, 12, 15],[16],2130,2186,1108⟩,
⟨[1, 13],[16],784,1288,660⟩,
⟨[5, 13],[9],2185,660,2193⟩,
⟨[12, 13, 15],[14],674,660,1108⟩,
⟨[3, 14],[11],532,1036,1290⟩,
⟨[4, 14],[16],98,140,1122⟩,
⟨[10, 14],[9],610,1122,1290⟩,
⟨[11, 14, 15],[18],786,1108,1106⟩,
⟨[12, 14, 15],[13],674,1122,1108⟩,
⟨[13, 14, 15],[12],660,1122,1108⟩,
⟨[7, 12],[10],2122,674,2186⟩,
⟨[11, 12, 16],[15],2130,2186,1164⟩,
⟨[11, 13, 16],[14],786,660,1164⟩,
⟨[11, 14, 16],[13],786,1290,1164⟩,
⟨[12, 14, 16],[17],674,1164,1162⟩,
⟨[13, 14, 16],[11],660,1290,1164⟩,
⟨[11, 15, 16],[12],2130,1108,1164⟩,
⟨[12, 15, 16],[11],2186,1108,1164⟩,
⟨[13, 15, 16],[20],2193,1164,1169⟩,
⟨[1, 17],[20],672,2128,676⟩,
⟨[8, 17],[6],673,676,1124⟩,
⟨[14, 17],[12],1122,676,1124⟩,
⟨[2, 17],[21],644,2114,676⟩,
⟨[9, 17],[7],652,676,1124⟩,
⟨[15, 17],[13],1108,676,1124⟩,
⟨[3, 18],[22],532,2058,788⟩,
⟨[4, 18],[17],98,266,1292⟩,
⟨[10, 18],[7],596,788,1292⟩,
⟨[16, 18],[13],1164,788,1292⟩,
⟨[17, 18, 19],[12],676,802,804⟩,
⟨[6, 17],[8],1121,676,1124⟩,
⟨[12, 17],[14],674,676,1124⟩,
⟨[2, 18],[22],1092,2114,1292⟩,
⟨[5, 18],[8],1289,788,1292⟩,
⟨[11, 18],[14],786,788,1292⟩,
⟨[17, 19, 20],[22],1124,1313,2132⟩,
⟨[18, 19, 20],[21],788,802,2132⟩,
⟨[7, 17],[9],1100,676,1124⟩,
⟨[13, 17],[15],660,676,1124⟩,
⟨[17, 18, 21],[22],1124,1292,2146⟩,
⟨[1, 19],[22],1120,2128,1313⟩,
⟨[5, 19],[9],1289,802,1313⟩,
⟨[11, 19],[15],786,802,1313⟩,
⟨[18, 19, 21],[20],788,802,2146⟩,
⟨[4, 20],[22],84,266,2132⟩,
⟨[10, 20],[9],596,2132,2188⟩,
⟨[17, 20, 21],[12],676,2146,2148⟩,
⟨[18, 20, 21],[19],788,2132,2146⟩,
⟨[19, 20, 21],[18],802,2132,2146⟩,
⟨[7, 18],[10],1100,788,1292⟩,
⟨[17, 18, 22],[21],1124,1292,2314⟩,
⟨[12, 19],[16],674,802,1313⟩,
⟨[17, 19, 22],[20],676,802,2314⟩,
⟨[17, 20, 22],[19],676,2188,2314⟩,
⟨[18, 20, 22],[11],788,2314,2316⟩,
⟨[19, 20, 22],[17],802,2188,2314⟩,
⟨[14, 21],[16],1122,2146,2209⟩,
⟨[17, 21, 22],[18],1124,2146,2314⟩,
⟨[18, 21, 22],[17],1292,2146,2314⟩,
⟨[19, 21, 22],[14],1313,2314,2337⟩,
⟨[9, 14],[4],778,1122,1802⟩,
⟨[9, 20],[4],652,2132,2700⟩,
⟨[14, 21],[4],1122,2146,3170⟩,
⟨[6, 11],[1],2129,786,2131⟩,
⟨[7, 11],[2],2122,786,2138⟩,
⟨[7, 12],[3],2122,674,2250⟩,
⟨[6, 17],[1],1121,676,1125⟩,
⟨[12, 17],[1],674,676,678⟩,
⟨[7, 17],[2],1100,676,1132⟩,
⟨[13, 17],[2],660,676,692⟩,
⟨[7, 18],[3],1100,788,1356⟩,
⟨[13, 18],[3],660,788,916⟩
]
set_option maxRecDepth 16384 in
def groups : List Group := [
⟨[],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[1],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[3],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[4],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[7],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[8],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[9],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[10],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[11],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[12],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[17],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,
⟨[18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,
⟨[19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22]⟩,
⟨[20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,
⟨[21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩,
⟨[22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,
⟨[5, 6],[1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 7],[1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6, 7],[1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 8],[1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6, 8],[1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[7, 8],[1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 9],[1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6, 9],[1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[7, 9],[1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[8, 9],[1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 10],[1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6, 10],[1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[7, 10],[1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[8, 10],[1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[9, 10],[1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 11],[1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6, 12],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 12],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[7, 13],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[12, 13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[8, 14],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[12, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[13, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[9, 15],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[12, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[13, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[14, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[10, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[12, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[13, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 17],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,
⟨[11, 17],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,
⟨[6, 18],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,
⟨[12, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,
⟨[17, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22]⟩,
⟨[7, 19],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22]⟩,
⟨[13, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22]⟩,
⟨[17, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22]⟩,
⟨[18, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 22]⟩,
⟨[8, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,
⟨[14, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩,
⟨[17, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 21, 22]⟩,
⟨[18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,
⟨[19, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22]⟩,
⟨[9, 21],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩,
⟨[15, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩,
⟨[17, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 22]⟩,
⟨[18, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 22]⟩,
⟨[19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,
⟨[20, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22]⟩,
⟨[10, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,
⟨[16, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,
⟨[17, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21]⟩,
⟨[18, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21]⟩,
⟨[19, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩,
⟨[20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21]⟩,
⟨[21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩,
⟨[5, 6, 8],[1, 2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 7, 9],[1, 2, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6, 7, 10],[1, 2, 3, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[8, 9, 10],[1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 12, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 13, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[12, 13, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[14, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 11, 17],[1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,
⟨[6, 12, 18],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,
⟨[7, 13, 19],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22]⟩,
⟨[8, 14, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩,
⟨[17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,
⟨[9, 15, 21],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩,
⟨[17, 19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,
⟨[10, 16, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,
⟨[18, 19, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,
⟨[20, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,
⟨[1, 5, 6, 8],[2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2, 5, 7, 9],[1, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6, 7, 8, 9],[1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[3, 6, 7, 10],[1, 2, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 7, 8, 10],[1, 2, 3, 4, 6, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 6, 9, 10],[1, 2, 3, 4, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[4, 8, 9, 10],[1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[1, 11, 12, 14],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2, 11, 13, 15],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[12, 13, 14, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[3, 12, 13, 16],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 13, 14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 12, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 22]⟩,
⟨[4, 14, 15, 16],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,
⟨[1, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,
⟨[2, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,
⟨[18, 19, 20, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 22]⟩,
⟨[3, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,
⟨[17, 19, 20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21]⟩,
⟨[17, 18, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20]⟩,
⟨[4, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,
⟨[1, 5, 6, 8, 11, 12, 14],[2, 3, 4, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2, 5, 7, 9, 11, 13, 15],[1, 3, 4, 6, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[3, 6, 7, 10, 12, 13, 16],[1, 2, 4, 5, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[4, 8, 9, 10, 14, 15, 16],[1, 2, 3, 5, 6, 7, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,
⟨[1, 5, 6, 8, 17, 18, 20],[2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,
⟨[1, 11, 12, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩,
⟨[2, 5, 7, 9, 17, 19, 21],[1, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,
⟨[2, 11, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22]⟩,
⟨[3, 6, 7, 10, 18, 19, 22],[1, 2, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,
⟨[3, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 20, 21]⟩,
⟨[4, 8, 9, 10, 20, 21, 22],[1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,
⟨[4, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19]⟩,
⟨[1, 5, 6, 8, 11, 12, 14, 17, 18, 20],[2, 3, 4, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩,
⟨[2, 5, 7, 9, 11, 13, 15, 17, 19, 21],[1, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22]⟩,
⟨[3, 6, 7, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 8, 9, 11, 14, 15, 17, 20, 21]⟩,
⟨[4, 8, 9, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 11, 12, 13, 17, 18, 19]⟩
]
set_option maxRecDepth 16384 in
def keys : List Nat := [
257,
258,
161,
259,
260,
261,
162,
163,
262,
263,
264,
265,
266,
267,
164,
165,
268,
269,
270,
271,
272,
273,
166,
167,
168,
169,
69,
70,
170,
46,
47,
89,
90,
91,
171,
92,
115,
48,
274,
172,
173,
275,
276,
277,
116,
278,
117,
279,
174,
175,
176,
177,
280,
281,
178,
179,
282,
118,
283,
119,
284,
180,
285,
286,
33,
181,
120,
287,
182,
288,
34,
31,
289,
290,
71,
183,
121,
184,
291,
122,
49,
185,
186,
93,
292,
187,
50,
16,
51,
188,
189,
293,
294,
123,
190,
72,
17,
124,
125,
126,
191,
295,
192,
296,
24,
193,
52,
73,
74,
127,
297,
128,
194,
129,
195,
130,
298,
94,
131,
196,
132,
299,
133,
300,
134,
301,
197,
95,
75,
96,
302,
198,
97,
98,
135,
303,
304,
305,
306,
199,
136,
137,
200,
201,
202,
138,
139,
203,
204,
205,
206,
307,
32,
18,
53,
54,
19,
207,
20,
55,
35,
21,
25,
8,
140,
141,
142,
208,
209,
143,
36,
76,
99,
210,
56,
37,
308,
77,
26,
144,
211,
27,
10,
38,
145,
11,
28,
12,
146,
39,
29,
7,
40,
212,
22,
213,
309,
310,
311,
312,
100,
313,
314,
214,
315,
316,
317,
78,
318,
319,
320,
321,
101,
215,
216,
217,
322,
41,
323,
324,
147,
218,
148,
219,
220,
221,
102,
325,
326,
57,
327,
328,
149,
329,
58,
222,
330,
223,
331,
224,
225,
332,
333,
334,
226,
335,
336,
337,
150,
338,
103,
104,
227,
105,
79,
228,
339,
59,
106,
340,
341,
107,
60,
108,
109,
342,
343,
344,
229,
230,
345,
151,
152,
346,
347,
231,
348,
349,
350,
153,
351,
61,
80,
352,
232,
353,
233,
354,
355,
234,
110,
9,
111,
356,
357,
154,
358,
359,
235,
155,
360,
236,
361,
362,
363,
364,
365,
366,
367,
368,
369,
370,
371,
372,
373,
374,
375,
376,
377,
378,
379,
380,
381,
382,
383,
384,
385,
386,
387,
388,
389,
390,
391,
392,
393,
394,
395,
396,
397,
398,
399,
400,
401,
402,
403,
404,
405,
406,
407,
408,
409,
410,
411,
412,
413,
414,
415,
416,
417,
418,
419,
420,
421,
422,
423,
424,
425,
426,
427,
428,
429,
430,
431,
432,
433,
434,
435,
436,
437,
438,
439,
440,
441,
442,
443,
444,
445,
446,
447,
448,
449,
450,
451,
452,
453,
454,
455,
456,
457,
458,
459,
460,
461,
462,
463,
464,
465,
466,
467,
468,
469,
470,
471,
472,
473,
474,
475,
476,
477,
478,
479,
480,
481,
482,
483,
484,
485,
486,
487,
488,
489,
490,
491,
492,
493,
494,
495,
496,
497,
498,
499,
500,
501
]
set_option maxRecDepth 16384 in
def words : List Nat := [
0x1034350642203c2306c2408c5802c3405c36094590002d0ac29084ec7d010190122c8050b4070b803110271680d0d4190880f08c1b090231600b0d0170d8251641e01c081b81c130000b42b0a421055f5,
0x10d0170d8251641f0181d3a0213b0000b42b0a4147dde4021cf000200781c06818058140880c0980a038290082b018040b424048107d9f004cce0444b055f50206e0704c078070142d01c2e00c4409c5a,
0x11642316003110050b4070b8000b42b0a4ed190117bc00090220801e0701a060160380c02806010020b42b0a4150242604df87d8133381112c050b4070b803110271680d0d4190880f08c1b090231600b,
0x10b8151880b0240d2381f018211301702c0322c273a41d1b8090681b098190dc110281306c293b4000b42b091f97e00802012398147dc1f0181d3a0213b0170d80b0d01b0900f08c190880d0d42716825,
0x106c1b09819244000b428098257e9e30896203c98091f906c2600c8b0643705c0b09ce90844c07c060348e02c090440a0746e0546204c1b0241a0a4ed01c2e0142d0002d0ac1d6f4235840f240050b407,
0x1018040b422085fc5f8156dc000a0260902a0601e0701a058120400e0200c02802018040b422081fb6e80d094235780f260214b8154b4074b005214030640b0241f0181d0702b074090681702c1102813,
0x10a8180781c0681604810038080300a008060a02d098047f9fc081fb000260902a0601e0701a058120400e0200c02802018280b404089fd734146e0000a0260901e0701a060160a812040080380c02802,
0x105c0b0440a04c1b0144508c4f098500002d0a0241bdfe0342503c9001cd20148f095fa06c260649100c1902c0907c060741c0ac1d0241a05c0b0440a04c1b0002d0a026141b9084840545d089fd00024,
0x11a4241bc26140000b4280680e801e1019ce00028088200781c0681805814048100a8250280809c040082d0380c7fdbb06c260643c03425084cc054c903c9001cd200c1902c0907c060741c0ac1d0241a,
0x10f0211a4030640b0241f0181d0702b074090681702c110281306c051142313c26140241bc000b428068ee7fc150e80d094030640b0241f0181d0702b074090681702c110281306c051142313c190f021,
0x107c060741c0ac1d0002d0a0ef7cc0c13414380030640b0241f0181d0702b074090681702c110281306c051142313c063ac241bc200f0180981a3b826140000b42803e017b40c1340659c142600e80019,
0x104c0d0940f0481f0181d0700523c2539c1702c1102813020090442b074283bc000b427809ee0543a0342503e010803c018eb06026068ee0906f08c4f014450985005c0b0440a04c1b0241a00c1902c09,
0x10002d001bc08d5f0649109e020148f094e705c0b0440a0342506c1404c080840703c12054130241101ca90a0ef07c0602c090741c00c190002d0aa03788190f022580030640b024072a42101c1b05015,
0x11f8000a42400e066b023198108102d000000a8200781c0681805814048240380402808018260a40c00a056b8225f02d000000902a0801e0701a06016050120300e0100a020060982900810812030ac1d,
0x1032096b4117242d0000009824074200781a03016050120380a02029018040082a088188202208c6a06205000200782a0680205814048240380402808018260a41c032070d423594000a402034f033423,
0x1000250081d1c209034f000e060153205c3602c3401c1f03c120840707c1804c080241106c14054130b4000002a0a42609029820190882320c1c81c000782a0680205814048240380408008018260a40a,
0x10a42d000000a829098160300a00a0b6bc111280707c0f0482101c1f06013020090441b0501504c050ec1926c1d1c0240a42d000000a829098160300a008228282208c6a000290701926d660606708861,
0x1064b4088cd00a0b01c1f03c120840707c1804c080241106c14054130143b090290b4000002a0a4260580c02a0c72811198228281926c1d1c00707c0f0482101c1f06013020090441b0501504c050ec24,
0x17a40a054191a810550023c01d03c220d40c8340707c0f0482101c1f06013020090441b0501504c050ec240a42d000000a829098163c44a08c660406b02a0c090290002a0a4260580c835de074b904473,
0x103c120840707c1804c080241106c14054130b4000002a0a42683df102815040db01c1f03c120840707c1804c080241106c14054130143b0087006067088610706c058f1090290b4000002a0a4260360e,
0x107c18054130241101c1f0b4000002a0a40131c106c02d00000090220801e0701a010160501209c0e0300a020060a42a00818841ea02c6b044280360e0606700870088610706c058f10143b0902901c1f,
0x10280809c040a80206e125ec0f6a02d000000a024088200781c0181805814048100300a020270102a0081a846100955608d55074ca0648a05c890348802c870150e00d0d09a0f06c1404c080840703c12,
0x13200d2200b21c09318054c0034bc290042d000000a8240882700a1206a1100024088200781c0181805814048100300a020270a02a0100284dc8039a90b40000028090220801e07018058140481003006,
0x1090220801e070160602a050120300a02006010020401a85591039750b4000002809824088200781c058140482a0180c02808010180081006e1484c1131c2133015324074c41f32c1d328192281722413,
0x1060020500686184039700b4000002809824060200781c06816048140080c028080a80408806046178541b8500009824088200781c058140482a0a00c028080101800806042165a00f5bc2d000000a026,
0x10901e07016098120a8280300a0200406002080148684d0396b0b4000002809824088200781c06818058140482a02004028020301001e1985c1b1e41085800090220801e07016098120a8280300a02004,
0x109824088180781c06816048060a00c028080a804008150821c630105c82d000000a026090220601e0701a05812018150300a0202a010020800e86cb103c4d0000c054073ca1906cb60447401a1800022,
0x101008054f33c8066742d000000a026090220781c0a818058120400e0300a0202101002068158761c01cf206cb80521a000240781c058260482a0a00c0282201018008080809c62c115000e86c2d00000,
0x10a8040082106e1f5e0072fc0f0cc11120202702900427008153cc2d000000a824088160300a0081c0601e048040201a87a1d06cb803c33044480809c0a40109c020002a090220580c028020701807812,
0x10701a06016050020280e030060a812010098861f06a1e054f30444803c330809c0001e07016098120a8280300a088240600201008880b6019a00b40000028098240881e0701805814048100380c02808,
0x10250301ca0012220b400000160981c0a8280300a0882406002078123d221054b20852706c7803d1401d04022200001c058260782a0a00c02822090180081201222458105b02d000000a026090220801e,
0x10300a0202a010020500689187054d80453b0250701d0606c300844901451048f40a40109c020b4000002a090220580c02802070180780f88c63038ae0000a04c051456a0852606c46055180451503d13,
0x104c0e0300a0a02a0100202006899c10418d0b4000002809824088200781c068180582a0380c028130180400808056254e4102bc000281301c9d620105c42d000000a026090220801e0701a0601604c0e,
0x1014510844906c30048f4000260702a0a00c028220901600818078f5758142c010190088982d00000090220801e0701a0601604c0e0300a0a02a098020100689e250522400026090220801e0701a06016,
0x100028098240881c0a81805814048100380c028080181f008040822966005144211241b0c0071e8092f40f1ec111f0151f41e3d429004270082d000000a824088160300a0081c060138a22701c9d03e23,
0x1090160081c0609e4941b118048a800090220702a06016050120400e0300a020260a0020181f8ada206c95082290b40000026090220702a06016050120400e0300a020060a00207c048a99b069770b400,
0x10880606a2d6681b52021540151f40f1ec071e8051dc1108413078093641827829004270082d000000a824088160300a0081c07e2c8ac138a0111f0151f40f1ec092f4071e81e3d4000982a0a00c02822,
0x105828048100100c02808064020881401a2f7102064c2d000000a026090220a81e07016050120400e0300a02019010020181b8b99f081740b40000028098240a80e0781c05814048100100c0280806402,
0x10442104c1e024d90609e0a40109c0207e2c0002a090220580c028020700e8c5da080920691e01a2f0b400000240a8260781c05828048100100c02808064020880e052308b81a8b400098240a80e0781c,
0x1064716581b514070e40929011084130781524c0f0c805370213841c0f427008290042d000000a824088160300a0081907a32134062640e8c418278000a8280300a08824058260081c0f6300549301477,
0x1714206702d000000a0260902207c1a06016050120a80e0300a0740601002040088cdd90694a07a32014dc05493084e104c1e04421024a403c3201c390703d09c020a4010b4000002a090220580c02802,
0x10280207cf68d0111f0155240f0c8070e4051701b37c1c0f42700829004191c4000a824088160300a0081f04a3577420374088cc2d00000098240881f06818058140a02a0380c0281d018040081204234,
0x1170191c4152f0131b4092e81f3d81c0f427008290042d000000a824088160300a008118d9e804064080dd0206d050bb04a3506cdf03c3201c390145c064710703d09c020a4010b4000002a090220580c,
0x10854e06a370b400000260901e0200406016050120400e0300a074280a822018028e1a1081760b4000002809824078080101805814048100380c0281d0182a0880206a37650211201b1e40f0c8070e405,
0x140409408111cc1d2e4192d0132b41545c023dc27008290042d000000a824088160300a0381e8e6380463604c6d054bc024ba07cf60145c0647101c3903c320703d000280302a0882405826028023dd97,
0x10801e0701a060160400b0300e020060a802010128ecaa044730000c02c030fcd8051370491203a3907e3a008f7000280a822090160980c0283e2542051c1a490000a00307e3a5a4212f81b4840540007,
0x109824088200781c068180582a0400e030080180202c1404cf88ec0516c090bc2105c030fc071c81d0c4191941b2dc0a0f82700829004000a82408816030100381e04a3c624145b42d000000a02609022,
0x1008290042d000000a8240881603012040f9250130c0000580b06c403e015358128f01b2dc090bc2105c030fc071c81d0c4191940a0f82700829004000a82408816030100381e8f4ae011850b40000028,
0x14d0090bc2105c030fc1f11c1b1000516c071d01d0c419084103e40a0f827008290042d000000a824088160301203e3e600154f41d0c40e8f4071c819194090bc2105c030fc1f11c1b1000516c0a0f827,
0x10a026090220801e0701a060160501003008018130082a02c0f901820553e03e3e074310642101c74040f90145b0242f0841700c3f07c4706c400283e09c020a4010b4000002a090220580c04a3f75014,
0x1904072bc113541d1b41535819078128fc1f11c1b100030fc2105c090bc0a0f8000a8220902809816030169000e3e00009824088200781c068180582a0401303008018020a00b05241744046fc2d00000,
0x1000000a026090220801e0701a06016050120200e02c060a80d0100290dd505136044d500cad07c10014a101ca20841706c40064b50740f024ac03cd30301609c020a4010b4000002a090220580b04e42,
0x1908092b0192d41b1002105c0f34c07288052841f0401d03c0c0582700829004000a8240881602c2a740102a80290c2d0000009824088200781c0681805814048080380b0a02a03406012446f8105fc2d,
0x1080180181491d810453503a450b40000026090220801e0701a060160a0120282a020060080d05004919830416e0b4000002809824088200781c06818058140480a0a808018020340403a45910154f013,
0x10002a090220581206820060069258a03dc00b4000002809824088200781c06818058120180a0200d010020a81504248918053501f0401d03c030540909c0b0a80c0582700829004000a824088160481a,
0x10824b74c0e2c4142ac1141405280069241f0401d03c030540909c0b0a80c05827008290042d000000a824088160481a0801892a48015110453f0524707c100740f00c150242702c2a0301609c020a401,
0x1058123e8990603301cbf038c00824b0301609c020a4010002a090220581206a4c63c15480072480f47c11084051dc189281f0401d03c030540909c0b0a80c05827008290042d000000a824088160481a,
0x1054d70301609c020a4010145101c9d048fa02c2a0b4000002a090220580f935e701899050e006033038c008122044790144606a4c07c100740f00c150242702c2a0301609c020a4010b4000002a09022,
0x10242700c1502c2a0740f07c100301600022090280a8260582b4e8106182d000000a026090220801e0701a06016050130080a020060102a0340e939d20413807c1000c15024270641e06c30084490740f,
0x10300a0764f7940a05418470211201b42c134200f2cc05350072ac1c46c0258c1036c1f0400942415080160ac27008290042d000000a8240880d1064e03e4d01c9d01451054d70844906c300641e048fa,
0x109c020a4010002a090220481a080199459000d410764f0b40000026090220801e06814048100381905c080a0040a80c0180a941c200dd70b4000002809824088200781a050120400e06417020060102a,
0x10a81a06014048100380c018080080405c0a07e536541c5cc2d000000a026090220801805c1a050120400e0302a02006010020281e94a5001c9202c6507d4605420044280344103c3801475024760582b,
0x16381d0c41f11c0a9502d00000090220801805c1a050120400e0302a0202801026008069565307a5200026090220801805c1a050120400e0302a02028010020180a950de071990b400000280982408820,
0x10a026090220081c06821050120400e0300a020060a8170101895e5500d190665105420044280344101c5203c3801475024760582b09c020a4010002a090220481a0825648c1f3781c468000901701c52,
0x12f820958091d8051d415080110a00d104071480f0e0160ac2700829004000a82408812068fb7701e52c1895c2d0000009824088020701a08414048100380c028280182a05c080125853c1e6782d00000,
0x10700806014048100380c028020182a05c1b0125a76c1c5301f2540543015080110a00d104071480f0e00b2500328c091e019368160ac27008290041a3ec2d000000a82408812086599601d5340b05c03,
0x12501a3ec0f0e015080110a00d10407148160ac2700829004000a82408812971d8079420125a0b40000026090220801c02018050120400e0300a0a0060a8170081b96dc3079920b400000280982408820,
0x19742700829004000a824088fc7980a18c04590210cc1e2cc03428092c01d2ec0e50c190781a4741297007148110a00d10415080160ac2d00000090280a82209a5d96c1d51021964091e0193680328c0b,
0x10380c0a8020180408c260226068c0a5e42d000000a0260901e0701a0602a050120080e0301008c06010200201697dc6029a40b40000028098240801e0701a06014048100380c0a8020180408c0805e5e,
0x100c7e088fc0a4010b4000002a090fd98009304031f8071fc0d2001d20c212101120405388131a00f3081f1381b30c151741920829004223f0000a82409a6197c17978000a0240801e0701a0601404810,
0x12080d200052140b31017314290040738c150e80f178211a41317c1b180243f42d000000a823989aa05c8902c87024c609a610545d07c4e04c68014e2084840748306cc3064820448103cc20348001c7f,
0x1000000a02a088200781c0680805814048020281003806010250980d991a60617a0b400000280a8200781c068080581404802038100282201804094260326369c093041d19c111982754c1f1380354419,
0x10a4010b4000002a00dab0648a0348809a650b400000200781c0680805814048020381002822018040942a0a2669900c98c000a8200781c0680805814048020381002822018040942809a6571c186942d,
0x10342d000000942899c4c0a80307405000210348e0a803074050000d031330b4000a8030001d0166607c8602552074610444a00d2b08e6204c5f084690543a01ce306c6005cc503c5e02cc401485090fd,
0x13941b1800f178092a00729c05298032942a00c0d0301d014210342d000000940e6d02756403294052980729c092a0171b0150e80f1781317c1b180190dc0b1ac1f21811128233942a00c0d0301d01421,
0x10940e074050a8030b400000220a4fe12c106d825038210341d0140d0302d0002a00c000781a0601605012098080a40e088040180202a68780265702899c1f2180b1ac190dc111281317c150e8171b023,
0x101028008139a9b20797d0b4000940e074050340c0840d0a803000220281a06016050260400e0a00801804008129a668054e605c3602c3404c080649b09d5d0255a07c1800c4403c2306c240148c01c8d,
0x101c8d024cf064370444b054620a4fe0a8030002209a6c9a8129a4000281a06016050220400e0a00801804098029adb107dcb0b4000940e0840d074050340c0a803000260881006016050080380a06806,
0x1088040000314db505c9702c9600d5807ccb04cc809a6c064370444b05462024cf0a4fe01c8d0148c06c2403c230a8030340c074050840d0940e0b400000220126b05cd102cd000c8b03c2306c240148c,
0x1088040001a05812078270380a9b47f088040a4420000715c5d088040642c000151595b0642c0a80308804000291086a0740508804000190b0810940e0880400011155100a80308804000091510f0a803,
0x115415158190b01d0142103425038291082d0000009c1a3fe6d02c9604c6805c9707c4e08804000270680e9b9df011cc0b4000a4420940e0840d074050642c05456044550340c0245401c5700c530a803,
0x1058460109a068ff088040a80300c5301c57024540340c04455054560642c074050840d0940e0a4420b4000002703e6f7ac0a18c043a81255c0e9b81725c1f138220102a00c0314c0715c091500d03011,
0x104c6803e6f058460109a078e4068ff088040002710c96029ec0b4000a4420940e0840d074050642c05456044550340c0245401c5700c530a803088040000507c2706c170480e9c1f20286304838078e4,
0x100c0f9d40527c009dc9a088040149f0001b9d8ea088040149f0000f9d52a0880409c430001f9d1290880409c43000139cd280880409c430000527cd10a80309c43000179c8d00a80309c430000b9c670,
0x16cc2d000291082710c25038210341f9d01d0141b9d8179c8151580b9c4139cc111540314c0d0300715c09150190b0220102a
]
def formula := (spans.map spanClause ++ triples.map triClause) ++ groups.map exactClause
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem all_spans : spans.all spanGood=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem all_triples : triples.all triGood=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem impossible : ¬ FormulaSat formula :=
  checkW_sound formula keys 10 words (by decide +kernel)

theorem first_owner {chosen region} (O : FlatOwner chosen region) :
    ∃ g∈groups, Matches chosen g := by
  classical
  by_contra h
  apply impossible
  refine ⟨chosen,?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hp | he
  · rcases List.mem_append.mp hp with hs | ht
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hs
      exact reject_neg _ _ (span_excludes O (List.all_eq_true.mp all_spans _ hw))
    · obtain ⟨t,hw,rfl⟩ := List.mem_map.mp ht
      apply clause_or
      by_cases yes : AllOn chosen t.lo
      · exact Or.inr (accept_pos _ _ (tri_implies O (List.all_eq_true.mp all_triples _ hw) yes))
      · exact Or.inl (reject_neg _ _ yes)
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp he
    apply clause_or
    by_cases first : AllOn chosen g.included
    · right
      apply accept_pos
      by_contra no
      apply h
      refine ⟨g,hg,first,?_⟩
      intro i hi
      cases eq : chosen i
      · rfl
      · exact False.elim (no ⟨i,hi,eq⟩)
    · exact Or.inl (reject_neg _ _ first)
end PEqualNP.Outside.L_pcx_120.Oldest
namespace PEqualNP.Outside.L_pcx_118.Linear

def smear (s a : Nat) : Nat := a ^^^ (a >>> s)

def parity (a q : Nat) : Bool :=
  (smear 1 (smear 2 (smear 4 (smear 8 (a &&& q))))).testBit 0

theorem smear_xor (s a b : Nat) :
    smear s (a ^^^ b) = smear s a ^^^ smear s b := by
  simp only [smear, Nat.shiftRight_xor_distrib]
  ac_rfl

theorem parity_left (a b q : Nat) :
    parity (a ^^^ b) q = (parity a q ^^ parity b q) := by
  simp only [parity, Nat.and_xor_distrib_right, smear_xor, Nat.testBit_xor]

theorem parity_right (a b q : Nat) :
    parity q (a ^^^ b) = (parity q a ^^ parity q b) := by
  simp only [parity, Nat.and_xor_distrib_left, smear_xor, Nat.testBit_xor]

def span : List Nat -> List Nat
  | [] => [0]
  | b :: bs => let xs := span bs; xs ++ xs.map (fun x => x ^^^ b)

theorem span_map (g : Nat -> Nat) (g0 : g 0 = 0)
    (gxor : ∀ x y, g (x ^^^ y) = g x ^^^ g y)
    (bs : List Nat) (x : Nat) (hx : x ∈ span bs) :
    g x ∈ span (bs.map g) := by
  induction bs generalizing x with
  | nil =>
    simp [span] at hx
    subst x
    simp [span, g0]
  | cons b bs ih =>
    simp only [span, List.map_cons, List.mem_append, List.mem_map] at hx ⊢
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Or.inl (ih x hx)
    · exact Or.inr ⟨g y, ih y hy, (gxor y b).symm⟩

theorem span_filter (bs : List Nat) (x : Nat) (hx : x ∈ span bs) :
    x ∈ span (bs.filter (fun b => b != 0)) := by
  induction bs generalizing x with
  | nil => simpa using hx
  | cons b bs ih =>
    simp only [span, List.mem_append, List.mem_map] at hx
    by_cases hb : b = 0
    · subst b
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false]
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact ih x hx
      · simpa using ih y hy
    · have hb' : (b != 0) = true := by simpa using hb
      simp only [List.filter_cons, hb', ite_true, span, List.mem_append, List.mem_map]
      rcases hx with hx | ⟨y, hy, rfl⟩
      · exact Or.inl (ih x hx)
      · exact Or.inr ⟨y, ih y hy, rfl⟩

def correct (a b x : Nat) : Nat := if parity a x then x ^^^ b else x

theorem correct_zero (a b : Nat) : correct a b 0 = 0 := by
  simp [correct, parity, smear]

theorem correct_xor (a b x y : Nat) :
    correct a b (x ^^^ y) = correct a b x ^^^ correct a b y := by
  cases hx : parity a x <;> cases hy : parity a y <;>
    simp [correct, parity_right, hx, hy] <;> try ac_rfl
  calc
    x ^^^ y = (x ^^^ y) ^^^ (b ^^^ b) := by simp
    _ = _ := by ac_rfl

def basisStep (a : Nat) (bs : List Nat) : List Nat :=
  match bs.find? (parity a) with
  | none => bs
  | some b => (bs.map (correct a b)).filter (fun v => v != 0)

theorem step_sound (a : Nat) (bs : List Nat) (q : Nat)
    (hmem : q ∈ span bs) (heven : parity a q = false) :
    q ∈ span (basisStep a bs) := by
  unfold basisStep
  split
  next => exact hmem
  next b _ =>
    have h := span_map (correct a b) (correct_zero a b) (correct_xor a b) bs q hmem
    exact span_filter _ _ (by simpa [correct, heven] using h)

open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3

def idx (v : V) : Nat := 3 * v.1.val + v.2.val
def assignment (a : Nat) (v : V) : Bool := a.testBit (idx v)
def formMask (S : Finset V) : Nat := S.fold (· ^^^ ·) 0 (fun v => 2 ^ idx v)

theorem idx_lt (v : V) : idx v < 12 := by
  have h₁ := v.1.isLt
  have h₂ := v.2.isLt
  unfold idx
  omega

theorem idx_inj : Function.Injective idx := by
  intro v w h
  have hv := v.2.isLt
  have hw := w.2.isLt
  unfold idx at h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem mask_insert (S : Finset V) {v : V} (h : v ∉ S) :
    formMask (insert v S) = 2 ^ idx v ^^^ formMask S := by
  simp [formMask, Finset.fold_insert h]

theorem mask_lt (S : Finset V) : formMask S < 4096 := by
  change formMask S < 2 ^ 12
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert v S h ih =>
    rw [mask_insert S h]
    exact Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by decide : 1 < 2) (idx_lt v)) ih

theorem bit_mask (S : Finset V) (v : V) :
    (formMask S).testBit (idx v) = decide (v ∈ S) := by
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert w S h ih =>
    rw [mask_insert S h, Nat.testBit_xor, Nat.testBit_two_pow, ih]
    by_cases hw : v = w
    · subst w
      simp [h]
    · have hidx : idx w ≠ idx v := fun e => hw (idx_inj e.symm)
      simp [hidx, hw]

theorem mask_nz {S : Finset V} (h : S.Nonempty) : formMask S ≠ 0 := by
  obtain ⟨v,hv⟩ := h
  intro hz
  have h' := bit_mask S v
  simp [hz,hv] at h'

theorem parity_unit (a j : Nat) (hj : j < 12) : parity a (2 ^ j) = a.testBit j := by
  have hb : a &&& (2 ^ j) = if a.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases h : j = i
    · subst i
      cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow]
    · cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow, h]
  have hp : ∀ k : Fin 12, parity (2 ^ k.val) (2 ^ k.val) = true := by decide +kernel
  have hs := hp ⟨j,hj⟩
  unfold parity at hs ⊢
  rw [hb]
  cases ht : a.testBit j
  · simp [smear]
  · simpa only [ht, ite_true, Nat.and_self] using hs

theorem parity_form (a : Nat) (S : Finset V) :
    parity a (formMask S) = decide (Odd (S.filter (fun v => assignment a v = true)).card) := by
  induction S using Finset.induction_on with
  | empty => simp [formMask,parity,smear]
  | @insert v S h ih =>
    rw [mask_insert S h, parity_right, parity_unit _ _ (idx_lt v), ih]
    change (assignment a v ^^ _) = _
    cases hv : assignment a v with
    | false => simp [Finset.filter_insert,hv]
    | true =>
      have hv' : v ∉ S.filter (fun w => assignment a w = true) := by
        intro hh
        exact h (Finset.mem_filter.mp hh).1
      rw [Finset.filter_insert, if_pos hv, Finset.card_insert_of_notMem hv']
      cases hd : decide (Odd (S.filter (fun w => assignment a w = true)).card) with
      | false =>
        have ho : ¬ Odd (S.filter (fun w => assignment a w = true)).card := of_decide_eq_false hd
        have he : Odd ((S.filter (fun w => assignment a w = true)).card + 1) := by
          rw [Nat.odd_iff] at ho ⊢
          omega
        simp [he]
      | true =>
        have ho : Odd (S.filter (fun w => assignment a w = true)).card := of_decide_eq_true hd
        have he : ¬ Odd ((S.filter (fun w => assignment a w = true)).card + 1) := by
          rw [Nat.odd_iff] at ho ⊢
          omega
        simp [he]

theorem linEqSat_iff (a : Nat) (e : LinEq V) :
    LinEqSat (assignment a) e ↔ parity a (formMask e.1) = e.2 := by
  rw [parity_form]
  unfold LinEqSat
  cases he : e.2 <;> simp [he]
def axioms : List (Nat × Bool) := [(7, false), (56, false), (448, false), (3584, false), (9, true), (18, true), (36, true), (65, true), (130, true), (260, true), (513, true), (1026, true), (2052, true), (72, true), (144, true), (288, true), (520, true), (1040, true), (2080, true), (576, true), (1152, true), (2304, true)]

def support (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit (idx v))

def clauseOf (row : Nat × Bool) : Clause V := (support row.1).image (fun v => (v,!row.2))

def linearOf (row : Nat × Bool) : LinClause V := linOfClause (clauseOf row)

theorem idx_cover (n : Nat) (h : n < 12) : ∃ v : V, idx v = n := by
  let v : V := (⟨n/3, by omega⟩, ⟨n%3, by omega⟩)
  exact ⟨v, by change 3 * (n/3) + n%3 = n; omega⟩

theorem singleton_sat (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases hv : a v <;> cases s <;> simp [LinEqSat, Finset.filter_singleton, hv]

theorem linear_iff (a : V → Bool) (C : Clause V) :
    LinClauseSat a (linOfClause C) ↔ ClauseSat a C := by
  simp only [LinClauseSat, linOfClause, Finset.mem_image, ClauseSat]
  constructor
  · rintro ⟨q, ⟨⟨v,s⟩, hs, rfl⟩, hq⟩
    exact ⟨(v,s), hs, (singleton_sat _ _ _).1 hq⟩
  · rintro ⟨⟨v,s⟩, hs, hv⟩
    exact ⟨({v},s), ⟨(v,s), hs, rfl⟩, (singleton_sat _ _ _).2 hv⟩

theorem false_on_spec (a : Nat) (row : Nat × Bool) (hh : row.1 < 4096) :
    (a &&& row.1 = if row.2 then row.1 else 0) ↔
      ¬ LinClauseSat (assignment a) (linearOf row) := by
  rw [linearOf, linear_iff]
  have ht : ClauseSat (assignment a) (clauseOf row) ↔
      ∃ v ∈ support row.1, assignment a v = !row.2 := by
    constructor
    · rintro ⟨l, hl, h⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
      exact ⟨v,hv,h⟩
    · rintro ⟨v,hv,h⟩
      exact ⟨(v,!row.2), Finset.mem_image.mpr ⟨v,hv,rfl⟩, h⟩
  rw [ht]
  push_neg
  have he : ∀ v : V, assignment a v ≠ !row.2 ↔ assignment a v = row.2 := by
    intro v
    cases h₁ : assignment a v <;> cases row.2 <;> simp
  simp only [he]
  constructor
  · intro h v hv
    have hm : row.1.testBit (idx v) = true := (Finset.mem_filter.mp hv).2
    have eq := congrArg (fun k : Nat => k.testBit (idx v)) h
    cases hs : row.2 <;> simpa [Nat.testBit_and, hm, hs, assignment] using eq
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hm : row.1.testBit i = true
    · have hi : i < 12 := by
        by_contra hn
        have hp : 2 ^ 12 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        have hw : row.1 < 2 ^ i := lt_of_lt_of_le hh hp
        simp [Nat.testBit_lt_two_pow hw] at hm
      obtain ⟨v,rfl⟩ := idx_cover i hi
      have hv : v ∈ support row.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩
      have hs := h v hv
      cases hr : row.2 <;> simp_all [Nat.testBit_and, assignment]
    · have hn : row.1.testBit i = false := by
        cases ht : row.1.testBit i <;> simp_all
      cases hr : row.2 <;> simp [Nat.testBit_and, hn, hr]

def pigeon (i : Fin 4) : Clause V := Finset.univ.image (fun j : Fin 3 => ((i,j),true))
def collision (i k : Fin 4) (j : Fin 3) : Clause V := {((i,j),false),((k,j),false)}

def axHas (C : Clause V) : Bool := axioms.any (fun row => clauseOf row == C)

theorem all_rows_small : axioms.all (fun row => decide (row.1 < 4096)) = true := by decide +kernel
theorem all_pigeon : ∀ i, axHas (pigeon i) = true := by decide +kernel
theorem all_collision : ∀ i k j, i ≠ k → axHas (collision i k j) = true := by decide +kernel
theorem label_distinct : (axioms.map clauseOf).Nodup := by decide +kernel

theorem php_covered {C : Clause V} (h : C ∈ PHP 4 3) : ∃ row ∈ axioms, clauseOf row = C := by
  have hc : axHas C = true := by
    rcases h with ⟨i,rfl⟩ | ⟨i,k,j,hne,rfl⟩
    · exact all_pigeon i
    · exact all_collision i k j hne
  exact ⟨_, (List.any_eq_true.mp hc).choose_spec.1, beq_iff_eq.mp (List.any_eq_true.mp hc).choose_spec.2⟩

def codeAssignment (a : V → Bool) : Nat :=
  formMask (Finset.univ.filter (fun v => a v = true))

theorem assignment_code (a : V → Bool) : assignment (codeAssignment a) = a := by
  funext v
  simp [assignment, codeAssignment, bit_mask]

theorem code_lt (a : V → Bool) : codeAssignment a < 4096 := mask_lt _

noncomputable def forms (C : LinClause V) : List Nat :=
  ((C.toList.map (fun e => formMask e.1)).filter (fun f => f != 0))

theorem forms_mem (C : LinClause V) (f : Nat) :
    f ∈ forms C ↔ (∃ e ∈ C, formMask e.1 = f) ∧ f ≠ 0 := by
  simp [forms]

theorem forms_lt (C : LinClause V) (f : Nat) (h : f ∈ forms C) : f < 4096 ∧ f ≠ 0 := by
  obtain ⟨⟨e, _, rfl⟩, hz⟩ := (forms_mem _ _).1 h
  exact ⟨mask_lt _,hz⟩

def possible (p : Nat) (xs : List Nat) (a : Nat) : Bool :=
  xs.all (fun q => parity p q == parity a q)

theorem possible_clause {C : LinClause V} {p : Nat}
    (hp : ¬ LinClauseSat (assignment p) C) (a : Nat) :
    possible p (forms C) a = true ↔ ¬ LinClauseSat (assignment a) C := by
  have hp' : ∀ e ∈ C, parity p (formMask e.1) ≠ e.2 := by
    intro e he h
    exact hp ⟨e, he, (linEqSat_iff _ _).2 h⟩
  constructor
  · intro ha he
    obtain ⟨e, he, hs⟩ := he
    have hh := (linEqSat_iff _ _).1 hs
    apply hp' e he
    by_cases hz : formMask e.1 = 0
    · have hpar : parity p (formMask e.1) = parity a (formMask e.1) := by
        simp [hz, parity, smear]
      exact hpar.trans hh
    · have hf : formMask e.1 ∈ forms C := (forms_mem _ _).2 ⟨⟨e,he,rfl⟩,hz⟩
      have hpar := beq_iff_eq.1 (List.all_eq_true.1 ha _ hf)
      exact hpar.trans hh
  · intro ha
    apply List.all_eq_true.mpr
    intro f hf
    obtain ⟨⟨e, he, rfl⟩, _⟩ := (forms_mem _ _).1 hf
    apply beq_iff_eq.mpr
    have hn : parity a (formMask e.1) ≠ e.2 := by
      intro hi
      exact ha ⟨e, he, (linEqSat_iff _ _).2 hi⟩
    have hm := hp' e he
    have eq_of_ne : ∀ x y z : Bool, x ≠ z → y ≠ z → x = y := by decide
    exact eq_of_ne _ _ _ hm hn

theorem possible_nonempty {C : LinClause V} {p : Nat}
    (hp : ¬ LinClauseSat (assignment p) C)
    (hs : ∃ a : V → Bool, LinClauseSat a C) :
    forms C ≠ [] := by
  obtain ⟨a,ha⟩ := hs
  intro h
  have hh : possible p (forms C) (codeAssignment a) = true := by simp [possible,h]
  have contra := (possible_clause hp _).1 hh
  rw [assignment_code] at contra
  exact contra ha
end PEqualNP.Outside.L_pcx_118.Linear
namespace PEqualNP.Outside.L_pcx_120.Oldest
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Linear

def indexedRow (i : Fin 22) := axis.getD i.val (0,false)
def physicalAx (i : Fin 22) := linearOf (indexedRow i)

theorem smallRow : ∀ i : Fin 22, (indexedRow i).1 < 4096 := by decide +kernel
theorem rowIndex : axioms.all (fun row => decide (∃ k : Fin 22, row = indexedRow k)) = true := by decide +kernel
theorem isAx : ∀ i : Fin 22, (∃ p : Fin 4, clauseOf (indexedRow i) = pigeon p) ∨
    ∃ p q : Fin 4, ∃ h : Fin 3, p ≠ q ∧ clauseOf (indexedRow i) = collision p q h := by
  decide +kernel

theorem allAx : (linOfClause '' PHP 4 3) = Set.range physicalAx := by
  ext D
  constructor
  · rintro ⟨A,ha,rfl⟩
    obtain ⟨row,hr,eq⟩ := php_covered ha
    obtain ⟨k,same⟩ : ∃ k : Fin 22, row=indexedRow k := of_decide_eq_true (List.all_eq_true.mp rowIndex _ hr)
    exact ⟨k,by simpa [physicalAx,linearOf,←same,eq]⟩
  · rintro ⟨i,rfl⟩
    refine ⟨clauseOf (indexedRow i),?_,rfl⟩
    rcases isAx i with ⟨p,e⟩ | ⟨p,q,h,ne,e⟩
    · exact Or.inl ⟨p,e⟩
    · exact Or.inr ⟨p,q,h,ne,e⟩

theorem grid_false (x : Nat) (i : Fin 22) :
    (¬ LinClauseSat (assignment x) (physicalAx i)) ↔ i.val+1∈labels x := by
  have v : violates x (indexedRow i)=true ↔ ¬LinClauseSat (assignment x) (physicalAx i) := by
    simpa only [violates,beq_iff_eq,physicalAx] using false_on_spec x (indexedRow i) (smallRow i)
  rw [←v]
  simp only [labels,List.mem_map,List.mem_filter,List.mem_range]
  constructor
  · intro h
    exact ⟨i.val,⟨i.isLt,h⟩,rfl⟩
  · rintro ⟨j,⟨_,h⟩,e⟩
    have eq : j=i.val := by omega
    simpa only [eq,indexedRow] using h

def privatePoints : List Nat := [672, 644, 532, 84, 1289, 1121, 1100, 673, 652, 596, 786, 674, 660, 1122, 1108, 1164, 676, 788, 802, 2132, 2146, 2314]
theorem privatePoint : ∀ i j : Fin 22,
    ((labels (privatePoints.getD i.val 0)).contains (j.val+1)) = decide (i=j) := by decide +kernel

theorem grid_essential (i : Fin 22) : ∃ a, ∀ j,
    ¬ LinClauseSat a (physicalAx j) ↔ j=i := by
  refine ⟨assignment (privatePoints.getD i.val 0),?_⟩
  intro j
  rw [grid_false,←List.contains_iff_mem,privatePoint]
  simp [eq_comm]

structure Ren where
  pigeons : List (Fin 4)
  holes : List (Fin 3)
  labels : List (Fin 22)
deriving instance DecidableEq for Group

def transport (r : Ren) (v : V) : V := (r.pigeons.getD v.1.val 0,r.holes.getD v.2.val 0)
def renamed (r : Ren) (i : Fin 22) := r.labels.getD i.val 0
def shifted (r : Ren) (A : PEqualNP.ProofComplexity.Clause V) := A.image (fun l => (transport r l.1,l.2))
def isoGood (r : Ren) : Bool := decide (∀ v w : V, transport r v=transport r w → v=w) &&
    decide (∀ i : Fin 22, shifted r (clauseOf (indexedRow i)) = clauseOf (indexedRow (renamed r i)))
theorem ren_preserves {r : Ren} (good : isoGood r=true) (a : V→Bool) (i : Fin 22) :
    LinClauseSat a (physicalAx (renamed r i)) ↔ LinClauseSat (a ∘ transport r) (physicalAx i) := by
  have h : ∀ i : Fin 22, shifted r (clauseOf (indexedRow i)) = clauseOf (indexedRow (renamed r i)) :=
    by
    simp only [isoGood,Bool.and_eq_true] at good
    exact of_decide_eq_true good.2
  simp only [physicalAx,linearOf,linear_iff,←h i,shifted,PEqualNP.ProofComplexity.ClauseSat,Finset.mem_image]
  constructor
  · rintro ⟨_,⟨l,hl,rfl⟩,sat⟩
    exact ⟨l,hl,sat⟩
  · rintro ⟨l,hl,sat⟩
    exact ⟨_,⟨l,hl,rfl⟩,sat⟩
structure Frame where
  first : Group
  ren : Ren
  representative : List Nat

def fits (q : Frame) : Bool :=
  decide (∀ i : Fin 22, (i.val+1∈q.first.included ↔ (renamed q.ren i).val+1∈q.representative)) &&
  decide (∀ i : Fin 22, i.val+1∈q.first.included ∨ i.val+1∈q.first.excluded)
def r0 : Ren := ⟨[0, 1, 2, 3],[0, 1, 2],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩
def r1 : Ren := ⟨[0, 1, 2, 3],[0, 2, 1],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 17, 18, 19, 20, 21, 10, 11, 12, 13, 14, 15]⟩
def r2 : Ren := ⟨[0, 1, 2, 3],[1, 0, 2],[0, 1, 2, 3, 10, 11, 12, 13, 14, 15, 4, 5, 6, 7, 8, 9, 16, 17, 18, 19, 20, 21]⟩
def r3 : Ren := ⟨[0, 1, 2, 3],[1, 2, 0],[0, 1, 2, 3, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 4, 5, 6, 7, 8, 9]⟩
def r4 : Ren := ⟨[0, 1, 2, 3],[2, 0, 1],[0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]⟩
def r6 : Ren := ⟨[0, 1, 3, 2],[0, 1, 2],[0, 1, 3, 2, 4, 7, 8, 5, 6, 9, 10, 13, 14, 11, 12, 15, 16, 19, 20, 17, 18, 21]⟩
def r8 : Ren := ⟨[0, 1, 3, 2],[1, 0, 2],[0, 1, 3, 2, 10, 13, 14, 11, 12, 15, 4, 7, 8, 5, 6, 9, 16, 19, 20, 17, 18, 21]⟩
def r9 : Ren := ⟨[0, 1, 3, 2],[1, 2, 0],[0, 1, 3, 2, 10, 13, 14, 11, 12, 15, 16, 19, 20, 17, 18, 21, 4, 7, 8, 5, 6, 9]⟩
def r12 : Ren := ⟨[0, 2, 1, 3],[0, 1, 2],[0, 2, 1, 3, 5, 4, 6, 7, 9, 8, 11, 10, 12, 13, 15, 14, 17, 16, 18, 19, 21, 20]⟩
def r13 : Ren := ⟨[0, 2, 1, 3],[0, 2, 1],[0, 2, 1, 3, 5, 4, 6, 7, 9, 8, 17, 16, 18, 19, 21, 20, 11, 10, 12, 13, 15, 14]⟩
def r14 : Ren := ⟨[0, 2, 1, 3],[1, 0, 2],[0, 2, 1, 3, 11, 10, 12, 13, 15, 14, 5, 4, 6, 7, 9, 8, 17, 16, 18, 19, 21, 20]⟩
def r15 : Ren := ⟨[0, 2, 1, 3],[1, 2, 0],[0, 2, 1, 3, 11, 10, 12, 13, 15, 14, 17, 16, 18, 19, 21, 20, 5, 4, 6, 7, 9, 8]⟩
def r16 : Ren := ⟨[0, 2, 1, 3],[2, 0, 1],[0, 2, 1, 3, 17, 16, 18, 19, 21, 20, 5, 4, 6, 7, 9, 8, 11, 10, 12, 13, 15, 14]⟩
def r18 : Ren := ⟨[0, 2, 3, 1],[0, 1, 2],[0, 2, 3, 1, 5, 7, 9, 4, 6, 8, 11, 13, 15, 10, 12, 14, 17, 19, 21, 16, 18, 20]⟩
def r19 : Ren := ⟨[0, 2, 3, 1],[0, 2, 1],[0, 2, 3, 1, 5, 7, 9, 4, 6, 8, 17, 19, 21, 16, 18, 20, 11, 13, 15, 10, 12, 14]⟩
def r20 : Ren := ⟨[0, 2, 3, 1],[1, 0, 2],[0, 2, 3, 1, 11, 13, 15, 10, 12, 14, 5, 7, 9, 4, 6, 8, 17, 19, 21, 16, 18, 20]⟩
def r21 : Ren := ⟨[0, 2, 3, 1],[1, 2, 0],[0, 2, 3, 1, 11, 13, 15, 10, 12, 14, 17, 19, 21, 16, 18, 20, 5, 7, 9, 4, 6, 8]⟩
def r22 : Ren := ⟨[0, 2, 3, 1],[2, 0, 1],[0, 2, 3, 1, 17, 19, 21, 16, 18, 20, 5, 7, 9, 4, 6, 8, 11, 13, 15, 10, 12, 14]⟩
def r24 : Ren := ⟨[0, 3, 1, 2],[0, 1, 2],[0, 3, 1, 2, 7, 4, 8, 5, 9, 6, 13, 10, 14, 11, 15, 12, 19, 16, 20, 17, 21, 18]⟩
def r26 : Ren := ⟨[0, 3, 1, 2],[1, 0, 2],[0, 3, 1, 2, 13, 10, 14, 11, 15, 12, 7, 4, 8, 5, 9, 6, 19, 16, 20, 17, 21, 18]⟩
def r27 : Ren := ⟨[0, 3, 1, 2],[1, 2, 0],[0, 3, 1, 2, 13, 10, 14, 11, 15, 12, 19, 16, 20, 17, 21, 18, 7, 4, 8, 5, 9, 6]⟩
def r36 : Ren := ⟨[1, 0, 2, 3],[0, 1, 2],[1, 0, 2, 3, 4, 6, 5, 8, 7, 9, 10, 12, 11, 14, 13, 15, 16, 18, 17, 20, 19, 21]⟩
def r37 : Ren := ⟨[1, 0, 2, 3],[0, 2, 1],[1, 0, 2, 3, 4, 6, 5, 8, 7, 9, 16, 18, 17, 20, 19, 21, 10, 12, 11, 14, 13, 15]⟩
def r38 : Ren := ⟨[1, 0, 2, 3],[1, 0, 2],[1, 0, 2, 3, 10, 12, 11, 14, 13, 15, 4, 6, 5, 8, 7, 9, 16, 18, 17, 20, 19, 21]⟩
def r39 : Ren := ⟨[1, 0, 2, 3],[1, 2, 0],[1, 0, 2, 3, 10, 12, 11, 14, 13, 15, 16, 18, 17, 20, 19, 21, 4, 6, 5, 8, 7, 9]⟩
def r40 : Ren := ⟨[1, 0, 2, 3],[2, 0, 1],[1, 0, 2, 3, 16, 18, 17, 20, 19, 21, 4, 6, 5, 8, 7, 9, 10, 12, 11, 14, 13, 15]⟩
def r42 : Ren := ⟨[1, 0, 3, 2],[0, 1, 2],[1, 0, 3, 2, 4, 8, 7, 6, 5, 9, 10, 14, 13, 12, 11, 15, 16, 20, 19, 18, 17, 21]⟩
def r44 : Ren := ⟨[1, 0, 3, 2],[1, 0, 2],[1, 0, 3, 2, 10, 14, 13, 12, 11, 15, 4, 8, 7, 6, 5, 9, 16, 20, 19, 18, 17, 21]⟩
def r45 : Ren := ⟨[1, 0, 3, 2],[1, 2, 0],[1, 0, 3, 2, 10, 14, 13, 12, 11, 15, 16, 20, 19, 18, 17, 21, 4, 8, 7, 6, 5, 9]⟩
def r48 : Ren := ⟨[1, 2, 0, 3],[0, 1, 2],[1, 2, 0, 3, 6, 4, 5, 8, 9, 7, 12, 10, 11, 14, 15, 13, 18, 16, 17, 20, 21, 19]⟩
def r49 : Ren := ⟨[1, 2, 0, 3],[0, 2, 1],[1, 2, 0, 3, 6, 4, 5, 8, 9, 7, 18, 16, 17, 20, 21, 19, 12, 10, 11, 14, 15, 13]⟩
def r50 : Ren := ⟨[1, 2, 0, 3],[1, 0, 2],[1, 2, 0, 3, 12, 10, 11, 14, 15, 13, 6, 4, 5, 8, 9, 7, 18, 16, 17, 20, 21, 19]⟩
def r51 : Ren := ⟨[1, 2, 0, 3],[1, 2, 0],[1, 2, 0, 3, 12, 10, 11, 14, 15, 13, 18, 16, 17, 20, 21, 19, 6, 4, 5, 8, 9, 7]⟩
def r52 : Ren := ⟨[1, 2, 0, 3],[2, 0, 1],[1, 2, 0, 3, 18, 16, 17, 20, 21, 19, 6, 4, 5, 8, 9, 7, 12, 10, 11, 14, 15, 13]⟩
def r54 : Ren := ⟨[1, 2, 3, 0],[0, 1, 2],[1, 2, 3, 0, 6, 8, 9, 4, 5, 7, 12, 14, 15, 10, 11, 13, 18, 20, 21, 16, 17, 19]⟩
def r55 : Ren := ⟨[1, 2, 3, 0],[0, 2, 1],[1, 2, 3, 0, 6, 8, 9, 4, 5, 7, 18, 20, 21, 16, 17, 19, 12, 14, 15, 10, 11, 13]⟩
def r56 : Ren := ⟨[1, 2, 3, 0],[1, 0, 2],[1, 2, 3, 0, 12, 14, 15, 10, 11, 13, 6, 8, 9, 4, 5, 7, 18, 20, 21, 16, 17, 19]⟩
def r57 : Ren := ⟨[1, 2, 3, 0],[1, 2, 0],[1, 2, 3, 0, 12, 14, 15, 10, 11, 13, 18, 20, 21, 16, 17, 19, 6, 8, 9, 4, 5, 7]⟩
def r58 : Ren := ⟨[1, 2, 3, 0],[2, 0, 1],[1, 2, 3, 0, 18, 20, 21, 16, 17, 19, 6, 8, 9, 4, 5, 7, 12, 14, 15, 10, 11, 13]⟩
def r60 : Ren := ⟨[1, 3, 0, 2],[0, 1, 2],[1, 3, 0, 2, 8, 4, 7, 6, 9, 5, 14, 10, 13, 12, 15, 11, 20, 16, 19, 18, 21, 17]⟩
def r62 : Ren := ⟨[1, 3, 0, 2],[1, 0, 2],[1, 3, 0, 2, 14, 10, 13, 12, 15, 11, 8, 4, 7, 6, 9, 5, 20, 16, 19, 18, 21, 17]⟩
def r63 : Ren := ⟨[1, 3, 0, 2],[1, 2, 0],[1, 3, 0, 2, 14, 10, 13, 12, 15, 11, 20, 16, 19, 18, 21, 17, 8, 4, 7, 6, 9, 5]⟩
def r66 : Ren := ⟨[1, 3, 2, 0],[0, 1, 2],[1, 3, 2, 0, 8, 6, 9, 4, 7, 5, 14, 12, 15, 10, 13, 11, 20, 18, 21, 16, 19, 17]⟩
def r68 : Ren := ⟨[1, 3, 2, 0],[1, 0, 2],[1, 3, 2, 0, 14, 12, 15, 10, 13, 11, 8, 6, 9, 4, 7, 5, 20, 18, 21, 16, 19, 17]⟩
def r69 : Ren := ⟨[1, 3, 2, 0],[1, 2, 0],[1, 3, 2, 0, 14, 12, 15, 10, 13, 11, 20, 18, 21, 16, 19, 17, 8, 6, 9, 4, 7, 5]⟩
def r72 : Ren := ⟨[2, 0, 1, 3],[0, 1, 2],[2, 0, 1, 3, 5, 6, 4, 9, 7, 8, 11, 12, 10, 15, 13, 14, 17, 18, 16, 21, 19, 20]⟩
def r73 : Ren := ⟨[2, 0, 1, 3],[0, 2, 1],[2, 0, 1, 3, 5, 6, 4, 9, 7, 8, 17, 18, 16, 21, 19, 20, 11, 12, 10, 15, 13, 14]⟩
def r74 : Ren := ⟨[2, 0, 1, 3],[1, 0, 2],[2, 0, 1, 3, 11, 12, 10, 15, 13, 14, 5, 6, 4, 9, 7, 8, 17, 18, 16, 21, 19, 20]⟩
def r75 : Ren := ⟨[2, 0, 1, 3],[1, 2, 0],[2, 0, 1, 3, 11, 12, 10, 15, 13, 14, 17, 18, 16, 21, 19, 20, 5, 6, 4, 9, 7, 8]⟩
def r76 : Ren := ⟨[2, 0, 1, 3],[2, 0, 1],[2, 0, 1, 3, 17, 18, 16, 21, 19, 20, 5, 6, 4, 9, 7, 8, 11, 12, 10, 15, 13, 14]⟩
def r78 : Ren := ⟨[2, 0, 3, 1],[0, 1, 2],[2, 0, 3, 1, 5, 9, 7, 6, 4, 8, 11, 15, 13, 12, 10, 14, 17, 21, 19, 18, 16, 20]⟩
def r79 : Ren := ⟨[2, 0, 3, 1],[0, 2, 1],[2, 0, 3, 1, 5, 9, 7, 6, 4, 8, 17, 21, 19, 18, 16, 20, 11, 15, 13, 12, 10, 14]⟩
def r80 : Ren := ⟨[2, 0, 3, 1],[1, 0, 2],[2, 0, 3, 1, 11, 15, 13, 12, 10, 14, 5, 9, 7, 6, 4, 8, 17, 21, 19, 18, 16, 20]⟩
def r81 : Ren := ⟨[2, 0, 3, 1],[1, 2, 0],[2, 0, 3, 1, 11, 15, 13, 12, 10, 14, 17, 21, 19, 18, 16, 20, 5, 9, 7, 6, 4, 8]⟩
def r82 : Ren := ⟨[2, 0, 3, 1],[2, 0, 1],[2, 0, 3, 1, 17, 21, 19, 18, 16, 20, 5, 9, 7, 6, 4, 8, 11, 15, 13, 12, 10, 14]⟩
def r96 : Ren := ⟨[2, 3, 0, 1],[0, 1, 2],[2, 3, 0, 1, 9, 5, 7, 6, 8, 4, 15, 11, 13, 12, 14, 10, 21, 17, 19, 18, 20, 16]⟩
def r97 : Ren := ⟨[2, 3, 0, 1],[0, 2, 1],[2, 3, 0, 1, 9, 5, 7, 6, 8, 4, 21, 17, 19, 18, 20, 16, 15, 11, 13, 12, 14, 10]⟩
def r98 : Ren := ⟨[2, 3, 0, 1],[1, 0, 2],[2, 3, 0, 1, 15, 11, 13, 12, 14, 10, 9, 5, 7, 6, 8, 4, 21, 17, 19, 18, 20, 16]⟩
def r99 : Ren := ⟨[2, 3, 0, 1],[1, 2, 0],[2, 3, 0, 1, 15, 11, 13, 12, 14, 10, 21, 17, 19, 18, 20, 16, 9, 5, 7, 6, 8, 4]⟩
def r100 : Ren := ⟨[2, 3, 0, 1],[2, 0, 1],[2, 3, 0, 1, 21, 17, 19, 18, 20, 16, 9, 5, 7, 6, 8, 4, 15, 11, 13, 12, 14, 10]⟩
def r108 : Ren := ⟨[3, 0, 1, 2],[0, 1, 2],[3, 0, 1, 2, 7, 8, 4, 9, 5, 6, 13, 14, 10, 15, 11, 12, 19, 20, 16, 21, 17, 18]⟩
def r110 : Ren := ⟨[3, 0, 1, 2],[1, 0, 2],[3, 0, 1, 2, 13, 14, 10, 15, 11, 12, 7, 8, 4, 9, 5, 6, 19, 20, 16, 21, 17, 18]⟩
def r111 : Ren := ⟨[3, 0, 1, 2],[1, 2, 0],[3, 0, 1, 2, 13, 14, 10, 15, 11, 12, 19, 20, 16, 21, 17, 18, 7, 8, 4, 9, 5, 6]⟩
def r120 : Ren := ⟨[3, 1, 0, 2],[0, 1, 2],[3, 1, 0, 2, 8, 7, 4, 9, 6, 5, 14, 13, 10, 15, 12, 11, 20, 19, 16, 21, 18, 17]⟩
def r122 : Ren := ⟨[3, 1, 0, 2],[1, 0, 2],[3, 1, 0, 2, 14, 13, 10, 15, 12, 11, 8, 7, 4, 9, 6, 5, 20, 19, 16, 21, 18, 17]⟩
def r123 : Ren := ⟨[3, 1, 0, 2],[1, 2, 0],[3, 1, 0, 2, 14, 13, 10, 15, 12, 11, 20, 19, 16, 21, 18, 17, 8, 7, 4, 9, 6, 5]⟩
def r126 : Ren := ⟨[3, 1, 2, 0],[0, 1, 2],[3, 1, 2, 0, 8, 9, 6, 7, 4, 5, 14, 15, 12, 13, 10, 11, 20, 21, 18, 19, 16, 17]⟩
def r128 : Ren := ⟨[3, 1, 2, 0],[1, 0, 2],[3, 1, 2, 0, 14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 4, 5, 20, 21, 18, 19, 16, 17]⟩
def r129 : Ren := ⟨[3, 1, 2, 0],[1, 2, 0],[3, 1, 2, 0, 14, 15, 12, 13, 10, 11, 20, 21, 18, 19, 16, 17, 8, 9, 6, 7, 4, 5]⟩
def canonical : List (List Nat) := [[], [1], [5], [5, 6], [5, 6, 8], [1, 5, 6, 8], [7, 8], [6, 7, 8, 9], [5, 11], [1, 5, 6, 8, 11, 12, 14], [5, 11, 17], [1, 5, 6, 8, 11, 12, 14, 17, 18, 20]]
def catalogue : List Frame := [
⟨⟨[],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[]⟩,
⟨⟨[1],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[1]⟩,
⟨⟨[2],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r36,[1]⟩,
⟨⟨[3],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r48,[1]⟩,
⟨⟨[4],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r54,[1]⟩,
⟨⟨[5],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[5]⟩,
⟨⟨[6],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r12,[5]⟩,
⟨⟨[7],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r72,[5]⟩,
⟨⟨[8],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r18,[5]⟩,
⟨⟨[9],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r78,[5]⟩,
⟨⟨[10],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r96,[5]⟩,
⟨⟨[11],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r2,[5]⟩,
⟨⟨[12],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r14,[5]⟩,
⟨⟨[13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r74,[5]⟩,
⟨⟨[14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r20,[5]⟩,
⟨⟨[15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,r80,[5]⟩,
⟨⟨[16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,r98,[5]⟩,
⟨⟨[17],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,r3,[5]⟩,
⟨⟨[18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,r15,[5]⟩,
⟨⟨[19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22]⟩,r75,[5]⟩,
⟨⟨[20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,r21,[5]⟩,
⟨⟨[21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩,r81,[5]⟩,
⟨⟨[22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,r99,[5]⟩,
⟨⟨[5, 6],[1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[5, 6]⟩,
⟨⟨[5, 7],[1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r36,[5, 6]⟩,
⟨⟨[6, 7],[1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r48,[5, 6]⟩,
⟨⟨[5, 8],[1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r6,[5, 6]⟩,
⟨⟨[6, 8],[1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r24,[5, 6]⟩,
⟨⟨[7, 8],[1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[7, 8]⟩,
⟨⟨[5, 9],[1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r42,[5, 6]⟩,
⟨⟨[6, 9],[1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r6,[7, 8]⟩,
⟨⟨[7, 9],[1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r108,[5, 6]⟩,
⟨⟨[8, 9],[1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r54,[5, 6]⟩,
⟨⟨[5, 10],[1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r24,[7, 8]⟩,
⟨⟨[6, 10],[1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r60,[5, 6]⟩,
⟨⟨[7, 10],[1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r120,[5, 6]⟩,
⟨⟨[8, 10],[1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r66,[5, 6]⟩,
⟨⟨[9, 10],[1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r126,[5, 6]⟩,
⟨⟨[5, 11],[1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[5, 11]⟩,
⟨⟨[6, 12],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r12,[5, 11]⟩,
⟨⟨[11, 12],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r2,[5, 6]⟩,
⟨⟨[7, 13],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r72,[5, 11]⟩,
⟨⟨[11, 13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r38,[5, 6]⟩,
⟨⟨[12, 13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r50,[5, 6]⟩,
⟨⟨[8, 14],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r18,[5, 11]⟩,
⟨⟨[11, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r8,[5, 6]⟩,
⟨⟨[12, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r26,[5, 6]⟩,
⟨⟨[13, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r2,[7, 8]⟩,
⟨⟨[9, 15],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,r78,[5, 11]⟩,
⟨⟨[11, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,r44,[5, 6]⟩,
⟨⟨[12, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,r8,[7, 8]⟩,
⟨⟨[13, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,r110,[5, 6]⟩,
⟨⟨[14, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22]⟩,r56,[5, 6]⟩,
⟨⟨[10, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,r96,[5, 11]⟩,
⟨⟨[11, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,r26,[7, 8]⟩,
⟨⟨[12, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,r62,[5, 6]⟩,
⟨⟨[13, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,r122,[5, 6]⟩,
⟨⟨[14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22]⟩,r68,[5, 6]⟩,
⟨⟨[15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩,r128,[5, 6]⟩,
⟨⟨[5, 17],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,r1,[5, 11]⟩,
⟨⟨[11, 17],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,r4,[5, 11]⟩,
⟨⟨[6, 18],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,r13,[5, 11]⟩,
⟨⟨[12, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,r16,[5, 11]⟩,
⟨⟨[17, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22]⟩,r3,[5, 6]⟩,
⟨⟨[7, 19],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22]⟩,r73,[5, 11]⟩,
⟨⟨[13, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22]⟩,r76,[5, 11]⟩,
⟨⟨[17, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22]⟩,r39,[5, 6]⟩,
⟨⟨[18, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 22]⟩,r51,[5, 6]⟩,
⟨⟨[8, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,r19,[5, 11]⟩,
⟨⟨[14, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩,r22,[5, 11]⟩,
⟨⟨[17, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 21, 22]⟩,r9,[5, 6]⟩,
⟨⟨[18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,r27,[5, 6]⟩,
⟨⟨[19, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22]⟩,r3,[7, 8]⟩,
⟨⟨[9, 21],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩,r79,[5, 11]⟩,
⟨⟨[15, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩,r82,[5, 11]⟩,
⟨⟨[17, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 22]⟩,r45,[5, 6]⟩,
⟨⟨[18, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 22]⟩,r9,[7, 8]⟩,
⟨⟨[19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,r111,[5, 6]⟩,
⟨⟨[20, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22]⟩,r57,[5, 6]⟩,
⟨⟨[10, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,r97,[5, 11]⟩,
⟨⟨[16, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,r100,[5, 11]⟩,
⟨⟨[17, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21]⟩,r27,[7, 8]⟩,
⟨⟨[18, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21]⟩,r63,[5, 6]⟩,
⟨⟨[19, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩,r123,[5, 6]⟩,
⟨⟨[20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21]⟩,r69,[5, 6]⟩,
⟨⟨[21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩,r129,[5, 6]⟩,
⟨⟨[5, 6, 8],[1, 2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[5, 6, 8]⟩,
⟨⟨[5, 7, 9],[1, 2, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r36,[5, 6, 8]⟩,
⟨⟨[6, 7, 10],[1, 2, 3, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r48,[5, 6, 8]⟩,
⟨⟨[8, 9, 10],[1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r54,[5, 6, 8]⟩,
⟨⟨[11, 12, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r2,[5, 6, 8]⟩,
⟨⟨[11, 13, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,r38,[5, 6, 8]⟩,
⟨⟨[12, 13, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,r50,[5, 6, 8]⟩,
⟨⟨[14, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,r56,[5, 6, 8]⟩,
⟨⟨[5, 11, 17],[1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,r0,[5, 11, 17]⟩,
⟨⟨[6, 12, 18],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,r12,[5, 11, 17]⟩,
⟨⟨[7, 13, 19],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22]⟩,r72,[5, 11, 17]⟩,
⟨⟨[8, 14, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩,r18,[5, 11, 17]⟩,
⟨⟨[17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,r3,[5, 6, 8]⟩,
⟨⟨[9, 15, 21],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩,r78,[5, 11, 17]⟩,
⟨⟨[17, 19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,r39,[5, 6, 8]⟩,
⟨⟨[10, 16, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,r96,[5, 11, 17]⟩,
⟨⟨[18, 19, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,r51,[5, 6, 8]⟩,
⟨⟨[20, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,r57,[5, 6, 8]⟩,
⟨⟨[1, 5, 6, 8],[2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[1, 5, 6, 8]⟩,
⟨⟨[2, 5, 7, 9],[1, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r36,[1, 5, 6, 8]⟩,
⟨⟨[6, 7, 8, 9],[1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[6, 7, 8, 9]⟩,
⟨⟨[3, 6, 7, 10],[1, 2, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r48,[1, 5, 6, 8]⟩,
⟨⟨[5, 7, 8, 10],[1, 2, 3, 4, 6, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r12,[6, 7, 8, 9]⟩,
⟨⟨[5, 6, 9, 10],[1, 2, 3, 4, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r18,[6, 7, 8, 9]⟩,
⟨⟨[4, 8, 9, 10],[1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r54,[1, 5, 6, 8]⟩,
⟨⟨[1, 11, 12, 14],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r2,[1, 5, 6, 8]⟩,
⟨⟨[2, 11, 13, 15],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,r38,[1, 5, 6, 8]⟩,
⟨⟨[12, 13, 14, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22]⟩,r2,[6, 7, 8, 9]⟩,
⟨⟨[3, 12, 13, 16],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,r50,[1, 5, 6, 8]⟩,
⟨⟨[11, 13, 14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 17, 18, 19, 20, 21, 22]⟩,r14,[6, 7, 8, 9]⟩,
⟨⟨[11, 12, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 22]⟩,r20,[6, 7, 8, 9]⟩,
⟨⟨[4, 14, 15, 16],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,r56,[1, 5, 6, 8]⟩,
⟨⟨[1, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,r3,[1, 5, 6, 8]⟩,
⟨⟨[2, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,r39,[1, 5, 6, 8]⟩,
⟨⟨[18, 19, 20, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 22]⟩,r3,[6, 7, 8, 9]⟩,
⟨⟨[3, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,r51,[1, 5, 6, 8]⟩,
⟨⟨[17, 19, 20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21]⟩,r15,[6, 7, 8, 9]⟩,
⟨⟨[17, 18, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20]⟩,r21,[6, 7, 8, 9]⟩,
⟨⟨[4, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,r57,[1, 5, 6, 8]⟩,
⟨⟨[1, 5, 6, 8, 11, 12, 14],[2, 3, 4, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,r0,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[2, 5, 7, 9, 11, 13, 15],[1, 3, 4, 6, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,r36,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[3, 6, 7, 10, 12, 13, 16],[1, 2, 4, 5, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,r48,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[4, 8, 9, 10, 14, 15, 16],[1, 2, 3, 5, 6, 7, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,r54,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[1, 5, 6, 8, 17, 18, 20],[2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,r1,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[1, 11, 12, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩,r4,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[2, 5, 7, 9, 17, 19, 21],[1, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,r37,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[2, 11, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22]⟩,r40,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[3, 6, 7, 10, 18, 19, 22],[1, 2, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,r49,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[3, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 20, 21]⟩,r52,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[4, 8, 9, 10, 20, 21, 22],[1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,r55,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[4, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19]⟩,r58,[1, 5, 6, 8, 11, 12, 14]⟩,
⟨⟨[1, 5, 6, 8, 11, 12, 14, 17, 18, 20],[2, 3, 4, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩,r0,[1, 5, 6, 8, 11, 12, 14, 17, 18, 20]⟩,
⟨⟨[2, 5, 7, 9, 11, 13, 15, 17, 19, 21],[1, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22]⟩,r36,[1, 5, 6, 8, 11, 12, 14, 17, 18, 20]⟩,
⟨⟨[3, 6, 7, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 8, 9, 11, 14, 15, 17, 20, 21]⟩,r48,[1, 5, 6, 8, 11, 12, 14, 17, 18, 20]⟩,
⟨⟨[4, 8, 9, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 11, 12, 13, 17, 18, 19]⟩,r54,[1, 5, 6, 8, 11, 12, 14, 17, 18, 20]⟩
]

set_option maxRecDepth 32768 in
theorem exhaust : catalogue.map Frame.first=groups := by decide +kernel
set_option maxRecDepth 32768 in
theorem fitsEvery : catalogue.all (fun q => fits q && canonical.contains q.representative)=true := by decide +kernel
theorem safe0 : isoGood r0=true := by decide +kernel
theorem safe36 : isoGood r36=true := by decide +kernel
theorem safe48 : isoGood r48=true := by decide +kernel
theorem safe54 : isoGood r54=true := by decide +kernel
theorem safe12 : isoGood r12=true := by decide +kernel
theorem safe72 : isoGood r72=true := by decide +kernel
theorem safe18 : isoGood r18=true := by decide +kernel
theorem safe78 : isoGood r78=true := by decide +kernel
theorem safe96 : isoGood r96=true := by decide +kernel
theorem safe2 : isoGood r2=true := by decide +kernel
theorem safe14 : isoGood r14=true := by decide +kernel
theorem safe74 : isoGood r74=true := by decide +kernel
theorem safe20 : isoGood r20=true := by decide +kernel
theorem safe80 : isoGood r80=true := by decide +kernel
theorem safe98 : isoGood r98=true := by decide +kernel
theorem safe3 : isoGood r3=true := by decide +kernel
theorem safe15 : isoGood r15=true := by decide +kernel
theorem safe75 : isoGood r75=true := by decide +kernel
theorem safe21 : isoGood r21=true := by decide +kernel
theorem safe81 : isoGood r81=true := by decide +kernel
theorem safe99 : isoGood r99=true := by decide +kernel
theorem safe6 : isoGood r6=true := by decide +kernel
theorem safe24 : isoGood r24=true := by decide +kernel
theorem safe42 : isoGood r42=true := by decide +kernel
theorem safe108 : isoGood r108=true := by decide +kernel
theorem safe60 : isoGood r60=true := by decide +kernel
theorem safe120 : isoGood r120=true := by decide +kernel
theorem safe66 : isoGood r66=true := by decide +kernel
theorem safe126 : isoGood r126=true := by decide +kernel
theorem safe38 : isoGood r38=true := by decide +kernel
theorem safe50 : isoGood r50=true := by decide +kernel
theorem safe8 : isoGood r8=true := by decide +kernel
theorem safe26 : isoGood r26=true := by decide +kernel
theorem safe44 : isoGood r44=true := by decide +kernel
theorem safe110 : isoGood r110=true := by decide +kernel
theorem safe56 : isoGood r56=true := by decide +kernel
theorem safe62 : isoGood r62=true := by decide +kernel
theorem safe122 : isoGood r122=true := by decide +kernel
theorem safe68 : isoGood r68=true := by decide +kernel
theorem safe128 : isoGood r128=true := by decide +kernel
theorem safe1 : isoGood r1=true := by decide +kernel
theorem safe4 : isoGood r4=true := by decide +kernel
theorem safe13 : isoGood r13=true := by decide +kernel
theorem safe16 : isoGood r16=true := by decide +kernel
theorem safe73 : isoGood r73=true := by decide +kernel
theorem safe76 : isoGood r76=true := by decide +kernel
theorem safe39 : isoGood r39=true := by decide +kernel
theorem safe51 : isoGood r51=true := by decide +kernel
theorem safe19 : isoGood r19=true := by decide +kernel
theorem safe22 : isoGood r22=true := by decide +kernel
theorem safe9 : isoGood r9=true := by decide +kernel
theorem safe27 : isoGood r27=true := by decide +kernel
theorem safe79 : isoGood r79=true := by decide +kernel
theorem safe82 : isoGood r82=true := by decide +kernel
theorem safe45 : isoGood r45=true := by decide +kernel
theorem safe111 : isoGood r111=true := by decide +kernel
theorem safe57 : isoGood r57=true := by decide +kernel
theorem safe97 : isoGood r97=true := by decide +kernel
theorem safe100 : isoGood r100=true := by decide +kernel
theorem safe63 : isoGood r63=true := by decide +kernel
theorem safe123 : isoGood r123=true := by decide +kernel
theorem safe69 : isoGood r69=true := by decide +kernel
theorem safe129 : isoGood r129=true := by decide +kernel
theorem safe37 : isoGood r37=true := by decide +kernel
theorem safe40 : isoGood r40=true := by decide +kernel
theorem safe49 : isoGood r49=true := by decide +kernel
theorem safe52 : isoGood r52=true := by decide +kernel
theorem safe55 : isoGood r55=true := by decide +kernel
theorem safe58 : isoGood r58=true := by decide +kernel
def validMaps : List Ren := [r0,r36,r48,r54,r12,r72,r18,r78,r96,r2,r14,r74,r20,r80,r98,r3,r15,r75,r21,r81,r99,r6,r24,r42,r108,r60,r120,r66,r126,r38,r50,r8,r26,r44,r110,r56,r62,r122,r68,r128,r1,r4,r13,r16,r73,r76,r39,r51,r19,r22,r9,r27,r79,r82,r45,r111,r57,r97,r100,r63,r123,r69,r129,r37,r40,r49,r52,r55,r58]
theorem checks : validMaps.all isoGood=true := by
  simp only [validMaps,List.all_cons,List.all_nil,safe0,safe36,safe48,safe54,safe12,safe72,safe18,safe78,safe96,safe2,safe14,safe74,safe20,safe80,safe98,safe3,safe15,safe75,safe21,safe81,safe99,safe6,safe24,safe42,safe108,safe60,safe120,safe66,safe126,safe38,safe50,safe8,safe26,safe44,safe110,safe56,safe62,safe122,safe68,safe128,safe1,safe4,safe13,safe16,safe73,safe76,safe39,safe51,safe19,safe22,safe9,safe27,safe79,safe82,safe45,safe111,safe57,safe97,safe100,safe63,safe123,safe69,safe129,safe37,safe40,safe49,safe52,safe55,safe58,Bool.true_and]
deriving instance DecidableEq for Ren
set_option maxRecDepth 32768 in
theorem inMaps : catalogue.all (fun q => validMaps.contains q.ren)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem canonical_owner {chosen region} (O : FlatOwner chosen region) :
    ∃ r : Ren, ∃ m∈canonical,
       (∀ a i, LinClauseSat a (physicalAx (renamed r i)) ↔ LinClauseSat (a ∘ transport r) (physicalAx i)) ∧
       (∀ i : Fin 22, chosen (i.val+1)=true ↔ (renamed r i).val+1∈m) := by
  obtain ⟨g,hg,onv,offv⟩ := first_owner O
  rw [← exhaust] at hg
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
  have good := List.all_eq_true.mp fitsEvery q hq
  simp only [Bool.and_eq_true,fits,decide_eq_true_eq,List.contains_iff_mem] at good
  have valid := List.all_eq_true.mp checks q.ren (List.contains_iff_mem.mp (List.all_eq_true.mp inMaps _ hq))
  refine ⟨q.ren,q.representative,good.2,ren_preserves valid,?_⟩
  intro i
  rw [←good.1.1 i]
  constructor
  · intro hi
    exact (good.1.2 i).resolve_right (fun no => by rw [offv _ no] at hi; contradiction)
  · exact onv _
end PEqualNP.Outside.L_pcx_120.Oldest
