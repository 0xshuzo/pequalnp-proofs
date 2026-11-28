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


namespace ProjectiveSharp
open PEqualNP.Library.LRAT
namespace Branch0
set_option maxRecDepth 32768 in
def clauses : List (List Nat) := [
[49,13],[145,13],[145,25],[145,121],[157,145],
[169,13],[169,25],[169,145],[169,157],[205,169],
[217,13],[217,25],[217,73],[217,97],[217,145],
[217,157],[217,169],[217,205],[241,13],[241,25],
[241,109],[241,121],[241,145],[241,157],[241,169],
[241,217],[253,241],[289,157],[289,169],[289,217],
[289,241],[313,13],[313,25],[313,121],[313,145],
[313,157],[313,169],[313,217],[313,241],[313,289],
[325,241],[337,13],[373,253],[373,337],[385,157],
[385,241],[409,13],[409,25],[409,121],[409,169],
[409,217],[409,289],[409,313],[421,145],[421,169],
[421,313],[421,325],[421,409],[445,145],[445,193],
[445,217],[445,361],[445,409],[457,13],[457,145],
[457,217],[457,241],[457,445],[469,13],[469,121],
[469,169],[469,193],[469,217],[469,241],[469,313],
[469,361],[469,445],[469,457],[481,469],[505,145],
[517,241],[517,313],[517,469],[529,145],[529,169],
[529,313],[529,325],[553,313],[589,25],[589,97],
[589,145],[589,157],[589,217],[589,241],[589,313],
[589,409],[589,517],[601,13],[601,73],[601,97],
[601,169],[601,205],[601,241],[601,289],[601,313],
[601,589],[613,13],[613,25],[613,145],[613,157],
[613,169],[613,193],[613,217],[613,241],[613,313],
[613,373],[613,409],[613,445],[613,469],[613,601],
[637,13],[637,145],[637,157],[637,193],[637,289],
[637,409],[637,589],[661,13],[661,145],[661,157],
[661,169],[661,241],[661,313],[661,469],[661,613],
[685,241],[685,409],[697,13],[697,169],[697,469],
[721,253],[721,337],[733,13],[733,25],[733,121],
[733,157],[733,169],[733,193],[733,217],[733,241],
[733,289],[733,313],[733,325],[733,373],[733,409],
[733,445],[733,469],[733,589],[733,601],[733,613],
[733,637],[733,649],[733,697],[733,721],[745,289],
[745,313],[757,13],[757,169],[769,13],[769,169],
[769,733],[793,13],[793,25],[793,61],[793,109],
[793,121],[793,145],[793,157],[793,169],[793,217],
[793,241],[793,289],[793,313],[793,337],[793,385],
[793,409],[793,469],[793,481],[793,505],[793,517],
[793,577],[793,589],[793,601],[793,613],[793,637],
[793,661],[793,697],[793,733],[793,781],[87,3],
[87,63],[125,5],[125,17],[125,41],[125,53],
[125,65],[135,27],[147,3],[147,15],[149,89],
[159,27],[161,89],[161,101],[175,19],[175,91],
[175,103],[175,115],[175,139],[175,151],[175,163],
[183,27],[185,137],[185,161],[195,27],[203,95],
[197,125],[201,153],[211,7],[215,23],[207,27],
[215,47],[215,59],[215,71],[215,107],[213,117],
[215,119],[209,137],[213,141],[209,149],[213,153],
[209,161],[231,3],[233,137],[231,147],[233,149],
[233,161],[235,175],[243,3],[245,161],[247,175],
[279,3],[283,175],[303,15],[305,89],[305,113],
[303,231],[305,233],[315,27],[319,175],[321,249],
[317,281],[317,305],[327,39],[331,175],[327,243],
[329,305],[355,187],[357,213],[359,215],[367,187],
[363,231],[371,239],[365,305],[375,51],[375,99],
[379,175],[375,303],[377,305],[403,55],[405,201],
[403,211],[407,215],[401,281],[401,305],[403,307],
[413,281],[413,305],[439,7],[443,23],[435,27],
[439,43],[443,71],[437,137],[441,141],[441,153],
[437,161],[443,287],[439,307],[447,111],[449,113],
[451,175],[453,213],[449,353],[449,401],[453,441],
[459,111],[461,113],[467,119],[463,211],[465,213],
[467,215],[459,231],[467,239],[461,281],[459,303],
[461,305],[463,307],[465,357],[459,363],[467,371],
[461,401],[463,403],[465,405],[465,441],[471,111],
[479,119],[473,161],[477,213],[471,327],[503,119],
[503,215],[495,327],[515,95],[513,105],[507,111],
[515,119],[509,125],[511,211],[513,213],[515,215],
[515,359],[507,399],[521,137],[521,161],[523,175],
[527,215],[521,305],[519,411],[551,215],[543,231],
[545,413],[567,375],[569,497],[571,511],[579,3],
[579,111],[587,119],[581,137],[579,147],[581,161],
[583,175],[579,279],[587,287],[579,303],[587,323],
[579,351],[579,399],[587,419],[579,495],[591,3],
[593,137],[595,175],[591,231],[593,233],[599,239],
[599,251],[591,279],[593,281],[591,303],[593,305],
[599,323],[591,399],[593,401],[599,419],[603,3],
[603,111],[605,113],[611,119],[605,137],[607,175],
[603,231],[611,239],[605,281],[603,303],[605,305],
[603,351],[603,399],[603,411],[603,447],[605,449],
[603,459],[611,467],[611,479],[605,497],[603,507],
[611,515],[621,9],[621,21],[621,45],[621,57],
[621,69],[621,93],[621,165],[621,189],[621,237],
[621,285],[621,309],[621,369],[621,501],[621,525],
[621,585],[621,597],[621,609],[627,15],[633,117],
[629,125],[627,147],[627,231],[631,307],[631,367],
[631,499],[627,579],[627,603],[639,15],[641,125],
[643,307],[651,15],[653,125],[655,211],[657,213],
[651,231],[655,307],[651,447],[657,453],[651,459],
[655,463],[657,465],[655,475],[655,499],[655,511],
[651,579],[651,591],[651,603],[675,15],[681,105],
[681,117],[677,125],[675,579],[695,23],[687,27],
[689,125],[693,153],[691,175],[693,333],[695,587],
[695,599],[695,611],[693,633],[707,11],[707,143],
[707,155],[707,167],[707,191],[707,311],[707,335],
[707,383],[707,455],[707,575],[707,635],[707,647],
[707,659],[707,683],[711,27],[713,125],[715,175],
[717,321],[719,371],[723,27],[725,125],[729,141],
[729,153],[727,175],[729,201],[731,203],[731,215],
[729,333],[729,381],[729,405],[731,407],[729,417],
[729,441],[731,443],[729,453],[729,573],[729,633],
[735,27],[737,125],[739,175],[741,549],[743,587],
[743,599],[755,23],[747,27],[749,125],[753,141],
[751,175],[759,27],[765,141],[761,161],[763,199],
[761,209],[763,211],[767,215],[767,287],[763,307],
[761,593],[765,645],[767,755],[771,27],[773,149],
[777,213],[773,305],[775,307],[775,463],[779,587],
[783,27],[787,67],[785,149],[787,199],[785,209],
[787,211],[789,213],[785,281],[785,305],[787,307],
[785,377],[785,401],[787,403],[789,405],[787,415],
[787,439],[789,441],[785,449],[785,461],[787,463],
[789,465],[787,511],[789,513],[787,547],[785,593],
[787,679],[789,693],[791,707],[789,729],[789,741],
[2,4,6,8,10,12],[14,16,18,20,22,24],[38,40,42,44,46,48],[50,52,54,56,58,60],[62,64,66,68,70,72],
[86,88,90,92,94,96],[98,100,102,104,106,108],[110,112,114,116,118,120],[134,136,138,140,142,144],[146,148,150,152,154,156],
[158,160,162,164,166,168],[182,184,186,188,190,192],[194,196,198,200,202,204],[206,208,210,212,214,216],[230,232,234,236,238,240],
[242,244,246,248,250,252],[278,280,282,284,286,288],[302,304,306,308,310,312],[314,316,318,320,322,324],[326,328,330,332,334,336],
[350,352,354,356,358,360],[362,364,366,368,370,372],[374,376,378,380,382,384],[398,400,402,404,406,408],[410,412,414,416,418,420],
[434,436,438,440,442,444],[446,448,450,452,454,456],[458,460,462,464,466,468],[470,472,474,476,478,480],[494,496,498,500,502,504],
[506,508,510,512,514,516],[518,520,522,524,526,528],[542,544,546,548,550,552],[566,568,570,572,574,576],[578,580,582,584,586,588],
[590,592,594,596,598,600],[602,604,606,608,610,612],[626,628,630,632,634,636],[638,640,642,644,646,648],[650,652,654,656,658,660],
[674,676,678,680,682,684],[686,688,690,692,694,696],[710,712,714,716,718,720],[722,724,726,728,730,732],[734,736,738,740,742,744],
[746,748,750,752,754,756],[758,760,762,764,766,768],[770,772,774,776,778,780],[782,784,786,788,790,792],[26],
[124],[174],[620],[706]
]
set_option maxRecDepth 32768 in
def keys : List Nat := [
400,182,401,402,183,249,403,82,250,404,184,405,406,407,251,252,185,253,254,408,409,186,410,255,
187,256,411,412,413,414,415,257,416,258,188,189,259,417,260,261,418,419,420,421,422,423,424,425,
426,427,428,429,430,431,432,262,433,434,263,435,153,436,437,438,439,440,264,441,442,443,265,444,
445,446,447,448,449,450,451,452,453,266,454,455,456,267,457,458,459,460,268,461,462,463,464,269,
465,270,466,467,190,468,469,470,271,272,191,471,472,473,273,274,275,474,276,277,475,476,278,192,
477,193,279,478,479,480,481,280,482,483,281,282,484,283,284,485,486,487,488,489,490,491,285,286,
287,492,104,493,494,288,289,127,495,496,194,290,497,291,195,498,196,499,500,501,502,503,292,504,
293,294,505,197,295,506,507,296,198,508,93,199,200,509,154,297,510,511,298,512,513,514,515,155,
299,201,202,300,301,516,302,517,303,518,519,520,521,522,523,128,74,524,525,526,304,527,528,529,
530,531,532,533,534,535,203,536,305,537,538,75,83,539,540,541,542,306,204,205,206,156,307,543,
105,129,544,106,545,84,546,547,308,548,94,549,85,550,130,86,551,552,553,309,554,555,556,557,
310,157,311,558,559,158,312,560,207,561,313,562,563,314,564,565,315,87,316,131,566,567,208,159,
568,569,570,571,572,317,573,107,574,575,576,577,578,579,318,319,580,320,209,581,582,210,160,132,
161,583,584,63,321,585,586,587,588,322,589,323,590,591,324,325,592,593,594,595,596,597,326,598,
599,600,601,602,603,327,328,604,605,162,606,133,607,608,609,610,611,612,88,163,329,613,614,76,
615,616,95,96,617,618,164,619,620,108,70,621,165,622,71,330,623,134,331,332,333,211,624,334,
625,212,335,626,42,627,166,64,336,135,337,628,629,630,136,631,137,138,632,633,338,634,635,636,
637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,109,339,652,213,139,43,653,654,167,
655,656,657,658,659,660,340,214,140,110,341,661,662,97,663,342,664,665,666,215,343,667,668,669,
670,671,672,673,674,216,675,676,344,217,345,168,677,678,679,680,681,682,683,684,685,686,687,688,
689,690,691,692,693,346,347,694,695,46,65,696,348,349,89,218,219,90,169,141,142,350,697,698,
66,699,700,701,702,703,704,705,706,707,351,708,709,352,220,710,711,221,712,713,714,715,716,717,
718,719,720,721,722,723,353,724,354,47,222,725,111,726,355,112,98,727,356,99,223,143,728,224,
225,170,113,729,357,730,731,732,358,359,733,34,734,51,56,735,736,360,226,361,57,13,21,8,
114,171,36,18,227,77,1,228,144,362,172,229,52,115,78,100,58,363,364,116,145,737,738,67,
24,25,37,739,48,365,117,366,26,367,368,230,369,4,44,38,17,35,45
]
set_option maxRecDepth 32768 in
def words : List Nat := [
0x1ad41a0ac00b4c1aac81a0ac00b1d71a801a0ac00abc768e01a0ac006cc4e89c1a0ac004ece68681a0ac0033c2685c1a0ac0030cac8541a0ac002dc758301a0ac0027c088281a0ac0021c0d,0x18247c09400105758207c094000d6e481c7c094000a6e38187c094000443a8147c0940001434b4c1a0ac00c3c04b341a0ac00c0d74b101a0ac00bdce7b041a0ac00bad73ae81a0ac00b7d72,0x1aec7c09400b8578ad87c09400b541bacc7c09400b2577a847c09400ac478a747c09400a9576a4c7c09400a3430a407c09400a06e5a2c7c094009d4279587c094007f4778607c09400314ad,
0x188cae040003dce9884ae040003ac12850ae0400028c0984cae0400025c15848ae0400022c0e844ae040001cc3c840ae0400019d7a83cae0400016ce8838ae0400004c3bb087c09400bb579,0x1a88ae04000acc799c8ae0400097c1d9b0ae0400094c1c998ae0400091c43970ae0400082c92904ae0400070c648c4ae040005eceb8b0ae0400052c918a0ae040004fcea890ae0400046c4f,0x19fe6c08800174ec9fa6c088001157e9f66c088000e6e79f26c088000b6e69ee6c088000543d9ea6c0880002435b0cae04000bbd7daf0ae04000b8d7cadcae04000b5c1ead0ae04000b2d7b,
0x1a266c088009541fa226c0880092444a1e6c0880083493a1a6c088007d57fa166c088005c4aea126c088004d401a0e6c0880047450a0a6c088003b413a066c088002f47aa026c088002940a,0x1ab2c20b00071c65aaec20b0005fcedaaac20b00053c94aa6c20b0004dc02aa2c20b0002fc7ba9ec20b00029c0ba9ac20b00026c16a96c20b00023c0fa92c20b00002c36a2a6c0880098420,0x10da4710e49110110e8130ec150f4a702ca5028a30249f02000c64d6add81b72c20b000c5c05ac6c20b000aad80ac2c20b000a4c31abec20b000a1ee9abac20b0009ec28ab6c20b0008fee8,
0x1314d9318f131d39265d54a64d26a594aa65322954acd11a0e914e4512ca001ca9170eb048ed04d350053700a5f07661082530725507e8d0c2930c4870348b0388f03ccf098050d0090d40b,0x1045cd0f9cb220e7291300025a0624e05dcf181331b65d0a6511168e0bc8803291355d13448d26cd408cd3128060c80315e8ba492f152421080e0de63562573624b55c17a7c0d3101949891,0x11714da8e7929eb41d2b7606b94b14b2454f250730f28d0c2930c53500537008cf09a7509e7b0a0050d0090d40b0dab31e6b11e2af1d8a702ca5028a30249f02000c64d690cee281d20e4ee,
0x123c760e28e0bd492707120691355dd5107532d30000d408d330a8d312a76090060ca8ba66732992f17c6f2880315c0d3107949cd931939265514a1e17fe7d326954acd11a1d950ca001ca9,0x122662061d20e65b34dcb4fc6e0e1cd0f8712047949dd54a6653207532dd13465d0a4880308d26c913165f07661080730f08f03c8b0388703400c6476355ce4c6ea5a9d793ddf939db55546,0x128c0927c089244491c43acc79ac478abc760031935b084ceec0fe62060ee0465b218e7154f131e65320e914ca001ca91725f07661080eb048ed04ca702ca5028a30249f02000c665c4beeb,
0x1358d5bb414256ce24cd4c11709c824c1ed19dc2a275fb9f4c9c352d264d79e4a7ad074add81ae52cc2d609284290cee9144b280072a45c9349a25c1526c16c0d749d4279ec2829c0b2940a,0x14ceec4beeb974292200cc26cf2349b244c54e499c352d1dd48c2d609284290cee9144b280072a45c9349ac0d744d4014dc0221c0d22c0e23c0f29c0b2940a28c0927c089244491c4300319,0x17f24d26a594a8d11a0e914e4512ca001ca9172530725507d1b13d1d140eb048ed04c050d0090d40b0d8cf09a4710e49110a702ca5028a30249f02000c64d6bbad2c197073aeac16d04c000,
0x10a2d306ad506ed7078110e8130ec150f49f020a3024a5028a702c00c640605e512165711918130ee0464f1ad17174e7200020c807128d208cd5bb51f17a4a10a433b80d310d9318f131d21,0x1148d6bb8654bca001edd80e7d3264180a05805f9801997f9817f5514a139264a91706d7e83d7e419499fd1de3fba0675e835b9039b9df55fd7b3ad7f3b54b2454f251350053700a7509e7b,0x1b7df05ae37984634e0338c1ef949763914623d91209794e54927130001f3a35330aa76092791063dae5951657d3694d366731b12f152d80640e0dedb16203965f7945971586b4c43b87017,
0x1739d0b74ef306dc065980ced90859537b1400f131c193505914ef1158ad306ad506ed707b0f013170171901800b69966391973eef1cdfb519ff98d8e0ce3ab8601951938ce39988685a036,0x1b62d306ad506ed707800b69d2989cc971cec56f1a72a85b0740e2ad794796a46f28aa3a7aa55daab600730f0001da431c2a6666f02225a061ca0e6657c5d57c25f076610800074a627325c,0x153dcd919914ec7733197159d327d2f17d8f28d350053700b0f013170171901800b68d798a43466f2066dd3bed9165d1932d306ad506ed707800b69d2989cc971ce65582066dd3bed9085d1,
0x16d46ab601928007b74c16f5b42a5aa6cc4eb4c1ab541bb5c1e27c0828c092940a29c0b002da6d9ba666f300131205396b53318470bc1980cea7595956099318b1200f15bc5cfbbf1158a5d,0x1194b71d4bd1e8bf1ee5f07661080870348b0388f03db31380035e62579b66e9ce971ccb66f4144a801c90030a11a8898ec9f020a3024a5028a702c870348b0388f03c00231b52bc4d6e48d,0x19895e6d9ba73a5c732f55a565921614f5634d9d00e5c018cba1c5cb221bf21cb985a5a060880326576dd5701c96e1696ccc16c891419bc135b52bdc5ae1b92348d0b5678b9d327dc3191c7,
0x19cca61c4d04c43e9d4279ec284d4014dc021cc3c0007690dcdb76f6135b51a9b9508a001dd03bdbd484a919edc066d9bd1d327db31389f020a3024a5028a702ed306ad506ed707800b68d7,0x1c480364833c542165459b6019b76f6c44a96464b1dccc65c5663ca3c3c04c5c05c6406b4c1ab541bb5c1e002da35e43661cdbdc249dc2a9e5524c8001d0389f4c34e47e1e51e1bca24bc5f,0x1224291c54e1bca24bc5f9cca69d4279ec284d4014dc021cc3cb4c1ab541bb5c1e002da1da436d9ba976f9419bc13490031b52bdb92348d0b5b3138870348b0388f03c006d9ba222d9be062,
0x11a930000a001dbd485391f8a919f0f0131701719019b313935005370089f020a3024a5028a702c004b9b66e932c4addbe8249dc2a9e5524c8001d0389f4c34e47e1e51eb7019b66f84c550,0x1c542165459b6019b76fac4c7064d414cd4073af5976f9736f7666f31dccc65c564bc5f57e6963ca3c3c04c5c05c6406b4c1ab541bb5c1e002da35e6290db66eafb37f1400db8137111bdb5,0x11059516499102d8066dd4827d779996b1394109d66c939952f17d8f28e73299350053700b0f013170171901a7509e7b0a0970549b05ad306ad506ed707800b699690d21bf163c400364033,
0x100c570be1b65c5652c9153c94b4c1ab541bb5c1e4d4014dc020a6e30b6e6014340243502c3646c4f47450002da35e6290efd0cd9120993189300031200d330ab110ba76090940531508679,0x10348b0388f03c9f020a3024a5028a702c00b6a4560c8f534d95249c51e2bb60194c00009adeb751c545a24e5000c58f030324ce3e0ae3901c9e6dafb6ee3d4784c486fc466f24bc5f45e67,0x1c640694c1c9541f9d4279ec2825c1526c1621c0d22c0e23c0fb4c1ab541bb5c1e0443a04c3b0543d002da35e56936fe0b6d80648c032dd19c91144a801ca112c89992d306ad506ed707887,
0x14cc2ac442e944459d824250142200cc54219e44165459264402342d9cc6c4bc5424c49b601903837b75229f5e09650f6650c4e5cf275cc2450b065ca05c5265c564d4014dc02c3c04c5c05,0x198420c3c04c5c05c640600196989a2b665c63931bfcbf990189601796e7493cd295c4698c3f944459742997c1d9842094c1c9541f000ef2258f3c0336448264c6263cd24c000c480393817,0x14745025c1526c1694c1c9541f82c92834930443a04c3b0543d000d79591e68ad922539c02759681866872995da695b16603367c8e64c62c4803c446f674cf64482654596848cc542197c1d,
0x1c048e67872c480367636c442e4604c2501445e6e66c8424c499381781890038379650e8450a6950548504274bc0659f05c5283ca1264406848cc54218254794445c3c04c5c05c640646c4f,0x198c3f654599e441c54219d4279ec280443a04c3b0543dc3c04c5c05c64064d4014dc02000d73bd1e68ad92270275a64060180de5b2180f1525f07661080110e8130ec150f40005a629712f,0x129c0b0443a04c3b0543d21c0d22c0e23c0f000d73bd1e68ad9c0c6c9c824038379f5df065a86603364563c4003c4c619dc2a64e354c8004bf014e7004c6ff63cf09742905c5265c5695c46,
0x19f4c0845c6695ae4e4bb2a451274b6065902400c22702c54219e4416848c264402342d05c5283ca14d4014dc02c3c04c5c05c640682c92834939d4279ec2825c1526c1627c0828c092940a,0x1abc76ac478acc790443a04c3b0543db4c1ab541bb5c1e91c4392444002da35cef61072674cf67c8e4c000c480366c844cc2ac442e818909d824250148265b9cc6c4bc5424c492800703837,0x1964c2664c14e47e275eb0651db7019b6703add5768e6a47c5e92842936fe90efd98c3f95c469158305c5265c5674c9f94c1c9541f4d4014dc02c3c04c5c05c64069d4279ec2825c1526c16,
0x102c004f16c9416a93addc103363cd26558293817975509454b7343e6448273c7064c624c000c48034cc2ac442e9d82425014c55669e4a7264d79cc6c4bc5424c49ad07403837ae5f39f4c3,0x15b5722aecd5656f2754038cba1c543530b932a5605ca001ed17d259309757bd457b8c17b0a919ec75c6c95decb5ed712b93b3993f3a8b71d4bd1e8bf1ee530725507c9f020a3024a5028a7,0x12454f250f73a4005214c3e8f83d175c1d355188f3c8e2545ea3f5e952c9153c943dce900148530fa3e0f4b4706212062419a1ca11721a56c20b24a0d24c008399c821a0679a25170556ace,
0x1300719de8c2ec9d5b8ab5d7075cd5ab396db47063d5332e4ca9d4279ec282dc752f47a2fc7b5c4aeb1d71b2577b2d7b001485b16a9c94c9e0fa3e2cc287084d54623cf238951690fd68d4b,0x18189066872845c7695af2a00728708b35593e534500e35170568d4d50d4c3ed4982c928349327c0828c092940a29c0b4ece64fcea0020e4f1485b19c8216a9c94c6827867a57c25dd9f024,0x152e099759d33d6d339492713d8a8e989859894478760f284ef6105b3a05d3b0c32b0c52b4415d4455fa530725507f0f013170171901ad306ad506ed7078eb048ed04c00b68d73c131c2884,
0x123c0f0008c95a4e4e70b3845f4c0574b8ca2a83e59ccd74c61748497465805e57c259f238c7374435871200f1508679105a12314d364c956ed8066ddc127322a4f2916b4dce6047111be51,0x100139c2e7322a4f2912f154931a48d0b4991027910715084970549b05b0f013170171901a7509e7b0a13500537008004c2d9958e7c3045940172200c9650e244bb94c1c9541f21c0d22c0e,0x19f4c04e4bb9d4279ec284d4014dc02001309e12e9c891c34512a0072400c284532261f27c0828c092940a29c0b21c0d22c0e23c0f0008c3a4b0050950b89d45b1000e7c09313186770a932,
0x14dc0221c0d22c0e23c0f3ac123b4130020e898ee3c130b670e050950b89d45b1000e7c09313186770a8970549b05b0f013170171901a7509e7b0a00026278c50929c9332c42a9d8244c800,0x14e0004ccb1825472200c2470db9ebf68d4d95b0c9cc8a87e5f4bc5524c69398113a4b0c54219e4416848c264402342dc3c04c5c05c6406b7d72b8578b8d7c82c928349325c1526c164d401,0x14dc0227c0828c092940a29c0b0443a04c3b0543db4c1ab541bb5c1e002da35cf0c3e60882e06707288eda67c8ec4803896bd66c84c442eb916e8189025014ba5f68a5c98450a69505274bc,
0x10f400b68d7c42cbbf0e5a12e2beec9a0e914c800be4db9fe8f4bc542800703837c05f8a25f24e47e2a4670651db7019b670e4c70a05c5283ca189e5ebfec73bd84bdce7a06e5a1ee94d401,0x16993940ca92e89d3f86d6601965cf0c3c6b4c417148675eaa55daab6017b3ad7f3b70f01317017190193500537008970549b05ad306ad506ed70789f020a3024a5028a702c110e8130ec15,0x123c0f000d435ad93c5855a069a6c634e2a85b176392a7595794e71200d30003110b9332c49405315086791057d36899100654bea3a6a731b12f15093126d8064a001c0e0dedd47ead79181,
0x14c2629700dc44142542e24c7fc400300832c4c6e01c4a34823344cd2200c364ff274fe24599034fd2342d26440c542125c1526c16c3c04c5c05c6406014340243502c3633c2621c0d22c0e,0x124f128ddba134160ddbd26019650d808db7278d3129b9235b52bc8d0b5b3138110e8130ec150f4cf09800350d6b64d0038073c486968184b800994be4e50097c1d984204d4014dc0200132,0x1000d435ad94cb11618292200c97311244b50303201cf198c3f3b81139c6903c4900c7f3a4b02342d3c585346d44c46f21c0d22c0e23c0f014340243502c363ac123b413000d435ad94cb11,
0x1c50cd340232200c364fb244b633c2621c0d22c0e23c0f000d43588c3489dc4e325d8e44b800605a54e4bc2701424f125e6d64c46f2542e264405f4da5eceb5fced4d4014dc0225c1526c16,0x111e3a17d306e84d328aa6f498334fc185961259536023345321660b3255b6e48d6d4af2342d10d6131cdd34c6e6ded7105751157e16ce8174ec6cc4e30cac314ad33c26000d435ad9c4c95,0x1028a702c870348b0388f03c00230d13c832034b701cf13602300c7f03c4924814257142771334c6e2342d26440014340243502c3633c2626c1625c15000d435ad9c4cd061d2e0f967158e1,
0x1014340243502c369d4279ec28c6406c5c05c3c04000d435ad924f1635272090920527d3009d2da7509e7b0a0970549b05800262782527624715144a801c90030a11a0893349f020a3024a5,0x12342d97c1d984203ac123b41325c1526c1621c0d22c0e23c0fc3c04c5c05c6406000d435ad9c5ddc030329f02401cf19ccd403c4900c7f9e4419dc2a4c986c4003c4d87344f22342dc5421,0x1024a5028a702ed306ad506ed707800352da1683f988183b811995d896e8e39c8a270149c8b124f16974292200c247159dc2a4c9862542ec4003c4d87344f23c5853a4b0c54219e44126440,
0x10c807128d208ce914cd11a0a001e5930a4d48921480f147cd97b4a919c0d472dc066d9c5cd7c424560d1b13d1d142530725507e4710e49110eb048ed04c050d0090d40b0d8cf0989f020a3,0x1c3c04c5c05c64060019600ca134e51621f5ba16e4804cb9ebe47c5eb7d72b8578b8d7c46c4f4745000116462e492f18215181325005d1f17a5711a4a108ee0464f1ae4315d17174e720002,0x1c64737ed4680e5363833178e1815d06650c185cb9304292f18b96dd806d9654dec5003c46db6466f4648515e0445c5d90c571660d9144b64d3a7fe57c4c6e7f47716ce8174ec91c4392444,
0x11ae4710e491111b13d1d140cf09a530725507c00350d03bc032871a1311953d1f17a5c0624a10a652fe4d43d21755171764315e5b9c11b13d1d1425f076610824710e49110009880391259,0x122c0e23c0f94c1c9541f33c2627c0828c092940a29c0b000d4340ef00f1b17a4a1091e1324d73521674d808cd3621192165005e59c664512cd7161972a2da16a5711a630fd171764315e4f,0x1002f4c02f8be88d3cce5bfec8bf55f4784c2300cbe6ca4648522445becdc9401734823c0525964bd4859c364b8244512a0072871a93c6b45c5d35c58b685a95c46bdce746c4f4745021c0d,
0x10131701719019c3191c71968d0c2930c65f07661082530725507c870348b0388f03ccf0989f020a3024a5028a702c00350d03bc0dc72ccbf8e5bc96fbf55fbc55ebdce7bad73bb579bbd7d,0x135a5a0624e05d8f3c25d0a651114880308d3cf131bafb3728f54d934eaf936cd208ca001f01492f548e9545e652fa59435c96d59969cd92dca93e0912d4d7161972a2da16a5711a630ff0f,0x10131701719019c3191c71965f07661080870348b0388f03db31389f020a3024a5028a702ccf098050d0090d40b0d800350d03bcf437b1400d940cf11381914f9c018dc5a52900bdbf21e8b,
0x13c25d0a4880331537dc590c8d4f1b8135b51a8a001e65449c96ddbd261996accd3f0a92e0913e8d808db7278d3128060c80dc7003c6e630fccb570d7161972a1bb576da168c32b0c52b70f,0x1013170171901a5f07661080970549b058870348b0388f03db3138050d0090d40b0d8eb048ed04c006e8ee030a13671d8d1940ccc82a993188c73771200f11381914f9c018dbf21e5a0618f,0x100e62063110ba5d0a494050880331537dd1508998f08d4f1b8135b7278060ca5b295cb20d2f154931a403200e604665449d56f1bd26139680f13fc9d3ec913e8e914db51a9350053700b0f,
0x13a45335c5865ca86ed5db685a3bcf44ece64fcea3dce946c4f4745094c1c9541f91c43924443ac123b413014340243502c3633c26000d43400c2871e0f9cc0e530001cf1c133185d322712,0x1000d43400cc7ce3505344f6293e0e24604c3ed4950e6847c5e9581792842965d4935ce515a14859e3f59a3c0119458893c6b90c5745c5d3ce2239c800083201c4a348233671d9144b3d533,0x10083201c4a34823ae5e7964bd3c4ba364b8274f92a0072871e35c58b685a3bcf4abc76ac478acc7994c1c9541f25c1526c163ac123b413014340243502c3633c2627c0828c092940a29c0b,
0x11e2b31e65f07661082530725507e8d0c2930c4870348b0388f03ceb048ed04ccf0989f020a3024a5028a702c00350d0c8074adcd8ad4d795817260149466d256203a01193c6b39c8024c7f,0x120c8d3cce6047131bafb3728f54dcf916f936ce914cd208ca001f01492f548eb979a9545e652fa59435d56e4f13f4d92dca93e0912d40cc7cef3d0d7162da16b0f013170171901aaf1dab1,0x12b0c52b4110e8130ec150f6eb5ceed5e6ef5f49f020a3024a5028a702c003504700f112a715599cc0e6b41d1d3226b7362620625605dd1a5a5d0a651116900bc880328b22e5b2964f291cb,
0x111c002349532cd411c001d4660509986493124c82a80e0dcc7b1417b02fa3cef25bf01496f57dccd64c9d3e41964af1578a801c8c3caf9b18a11a0954c8d0c80cb572da168970549b058c3,0x1000a939f232c08d254003a45bb54d411c00c5496354d411c00a4448960d411c00804b3510d411c0077722344d411c007447c908d411c00714b28b4d411c0059721878d411c002658926cd4,0x14c0007303973c604cc6d74c89a382f98818a2c8b96ca572c834bc554e5027550899510a5518974292200c244514d4014dc027447ca3430a4c31a444897c1d984202349523c0f22c0e21c0d,
0x139f2397429944452200ca551899510964bd755084e5023c4ba244517447c4d4014dc02a3430a4c31a444897c1d9842094c1c9541f3ac123b4133a45b21c0d22c0e23c0f23495000a9c903e,0x1280f500245c9943280f5001d9c94ca280f5000b93d80729c0b2940a28c0927c082a724000a03d43e730394c00073c604cc6da382f72c88a2cd64bd4a968189381798c3f95c4674ca03b811,0x12e4f60025b75728956021cc760e2054247940538001ff591331871200f112a5310f8713406f34d2f219fb545fd1de012cc730f075199350053700b0f0131525b17017190180096dcdc9c4b,
0x1ca65a80873599697fe985853d58d36a382f700632e871a551a815c5725c15a5bf305bb57e736fc877ed51a2d567f477804b359721a3430a4c31a444870c6471c65714b22dc752f47a2fc7b,0x122c0e23c0f23495000ef9972a001311bd3978f1000e940bf131c28f18133501ce0e5d5ca1cdc9e8b559cb2212f219350053700b0f0131525b170171901a8d0c2930c691121d11f00074a5b,0x14bd4a938175bc9d944452e8712200ca551b964bf755155d5144e51330511245d75ce2f74ca095c467447c5c4ae4d4014dc02a3430a4c31a444894c1c9541f2dc752f47a2fc7b2e4f621c0d,
0x170676224291c54e91c4392444917267d57fa3430a4c31a44481cc3c1d46670c6471c65714b221c0d22c0e23c0f234950025dcae49728395a8ab7343e5b4ce4c00073c604cc6da382fa2cd6,0x16fc8739ca51bcd370c6471c65714b21cc3c1d4663ac123b4133a45b0025bcb26b908427b96b7ce9792d487de50a382f1d838a2d541be3f6f863a55e19350b7e5c3725b61e5912400c7c678,0x1a551b755155d5144e5133c5d9305117447c5c4ae4d4014dc02a3430a4c31a44483ac123b4133a45b2dc752f47a2fc7b2e4f600265cb640700631c038725071e4b93c0113bca01de4474b29,
0x1cb83f9887d000ef25e719887d000772d0189772b96f2c9842097c1d9972d002621f64a748395c8ab7343e5b4ce4c00073c604cc6da382fa2c8b72c835ad374bc555bc9d398112e8713bf2a,0x13c011a2e954be4739c831bd3f4d4014dc02a3430a4c31a44481cc3c1d4661dcb43ac123b4133bc973a45b001cbcc5589887d002b7cc2799887d0020362a779887d001dfcbc899887d001d3,0x11cc3c1d4661dcb477f2f77722767254d4014dc02c549626589a3430a4c31a4448abc76ac478acc79adf303ac123b4133bc973a45b001d5cc8004cc6d4c481a382f1c038a55194e5031e4b9,
0x122dc3191c7195c52c8eb048ed04cef25ce916c007028bccc381be4d1c4817596a4c00076d554ccb1a382f9e4a7a2c8b9cc8a4bc5524c69ad07439811ae5e8a551a785c24e5be3c5bd1e5ba,0x104492050f14649d78a940be8bccdc1380950bb1000f131c28f180eb048ed04cef25ce916c970549b058996268d0c2930c6911230f0131525b17017190180073f3441dc818cf0045bf550e7,0x159312630007fd8d18712630004cf3700f1901b170171525b0f01311cd800c498c2a5cc3dc00c47360f9cc3dc004c735341cc3dc001c58b0e5d11f1d3cb9cbcc5d5cc9cfcd000730f71a4e6,
0x1cd5370093500533cdd2fce8004e18e154e6ce4004bf3a044e916cef25ced04ceb048f1ce00039b39515fa1cc6e0e205710792e5fd1de012cdff63603628730f0751987162c772d0003c738,0x5451bb3d7eb3e0033f1ce03629ff636012cdfd1de05cf0007eb3e0e0772d07162c75198730f079cec001bb3d42538638008173c40538638001e73b00131
]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem impossible : ¬FormulaSat clauses := checkW_sound clauses keys 10 words (by decide +kernel)
end Branch0
namespace Branch1
set_option maxRecDepth 32768 in
def clauses : List (List Nat) := [
[37,13],[37,25],[121,37],[157,37],[169,37],
[181,37],[217,37],[241,37],[289,37],[301,37],
[421,37],[445,37],[469,37],[481,37],[505,37],
[541,37],[577,37],[601,37],[613,37],[625,37],
[661,37],[673,37],[709,37],[769,37],[113,5],
[163,7],[161,17],[173,161],[195,111],[195,147],
[207,3],[207,15],[207,159],[239,179],[297,21],
[297,237],[401,209],[401,281],[401,293],[415,283],
[437,149],[435,279],[451,115],[451,175],[451,211],
[451,439],[459,207],[463,235],[463,283],[465,285],
[463,295],[465,297],[461,401],[477,117],[475,151],
[475,163],[471,207],[473,401],[495,207],[497,401],
[531,195],[535,295],[533,413],[567,207],[575,299],
[569,401],[571,451],[591,279],[593,401],[595,499],
[611,11],[611,119],[603,171],[611,179],[603,231],
[603,279],[609,285],[603,291],[605,401],[603,411],
[607,451],[609,465],[609,477],[619,163],[617,173],
[623,239],[621,285],[615,603],[659,23],[653,161],
[651,195],[657,285],[655,451],[659,611],[667,19],
[665,161],[667,163],[665,233],[669,285],[671,575],
[663,603],[701,161],[699,171],[703,451],[705,657],
[729,9],[729,153],[729,165],[729,177],[729,213],
[729,417],[729,441],[729,537],[729,573],[767,167],
[759,195],[765,285],[761,401],[763,451],[765,465],
[765,501],[765,597],[791,155],[791,215],[791,287],
[791,419],[791,443],[791,467],[791,479],[791,503],
[791,539],[791,599],[791,707],[2,4,6,8,10,12],[14,16,18,20,22,24],
[110,112,114,116,118,120],[146,148,150,152,154,156],[158,160,162,164,166,168],[170,172,174,176,178,180],[206,208,210,212,214,216],
[230,232,234,236,238,240],[278,280,282,284,286,288],[290,292,294,296,298,300],[410,412,414,416,418,420],[434,436,438,440,442,444],
[458,460,462,464,466,468],[470,472,474,476,478,480],[494,496,498,500,502,504],[530,532,534,536,538,540],[566,568,570,572,574,576],
[590,592,594,596,598,600],[602,604,606,608,610,612],[614,616,618,620,622,624],[650,652,654,656,658,660],[662,664,666,668,670,672],
[698,700,702,704,706,708],[758,760,762,764,766,768],[194],[400],[450],
[728],[790],[36]
]
set_option maxRecDepth 32768 in
def keys : List Nat := [
53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,
77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,
12,101,36,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,
123,124,125,14,126,15,127,128,129,130,131,132,133,134,135,136,137,37,138,139,140,141,142,143,
144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,16,162,17,163,164,165,
166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,18,38,183,184,7,19,185,
186,20,39,187,188,189,190,191,192,40,193,194,21,8,3,4,5,2,1
]
set_option maxRecDepth 32768 in
def words : List Nat := [
0x11ad9000800764291999000800734171699000800494161659000800464081619000800344c5284c201c00bdc15224c201c00a2c281b8c201c0084cc4144c201c0024cc3140c201c001bcc2,0x11d1c200c008eccd185c200c006dccc181c200c0034ccb17dc200c002bc2a179c200c001ccca2899000800be4181f99000800974c91d99000800944c81cd90008008e4c71b590008007c4c6,0x1276d801000684d3272d801000354d226ed8010002c42c26ad8010002941a266d801000264d1262d801000024d028dc200c00bec19259c200c00afccf22dc200c00a3c2b201c200c0097cce,
0x12b7160040077c2d2b3160040074c1b2af16004006ecda2ab160040068cd92a7160040047c092a3160040035cd829f160040026cd7282d8010008f4d627ed801000864d527ad8010006e4d4,0x10e424000002d42e0e024000002a41c0dc2400000274e20d824000001e4e10d42400000064e00d02400000034df2c71600400b0cde2c3160040095cdd2bf160040086cdc2bb16004007dcdb,0x110c2400000874e810824000007e4e710424000007842f10024000007541e0fc24000006f4e60f82400000694e50f424000004b41d0f024000004840a0ec24000003c4e40e82400000364e3,
0x1360d5348d332cd1314d938c003380512c2400000c041f1282400000b14ee1242400000a84ed1202400000a543011c24000009c4ec1182400000994eb1142400000964ea1102400000904e9,0x14ac222f2413a63d35a3b3363931e373c8008f8321c4ce014008dcf21b0ce014007bcf11a8ce0140075c31188ce0140072c21150ce0140027c2014cce0140003cf0148ce0140000cef2d8d7,0x1052fd0411c0191b02d17034af0a8b10b0b50ba713b0f13909f080a5068a90730107efb066f9062f7055210291f025190212d0752b089250580096dcfa64f424a3e0c800a7cf31ca3e0c800,
0x1bec19c041f494164ac224b41d4640847c094840a0025b73cf5210ac096682fe6f214b31566b20cee2dca2044e9240a1238ab1e8e71f26721ceb18e6d218ed15d280492708d23038a703efe,0x12801128c8f04c8da68c0a64f429c0fbf81405456bf410a7491a448a4a0124700649c2346c0b45c0d48c0ea5c93a2c28a3c2ba543003cf0064e027c202941a2a41ca7cf3a84edbdc15be418,0x14a465474647401373cf566c7f48c0e45c0d84cc4864d586cdc874e8684d368cd9694e5494164ac224b41d4640847c094840a7341772c2174c1b7541e0025b3d888a4827058b3a34240444e,
0x177482744814747d6dccc6e4d46ecda6f4e624cc3264d126cd7274e24640847c094840a7642975c3177c2d7842f7341772c2174c1b7541e002613dc70850bb670b885c6f67c5b4981246806,0x10c000ae8a13f08c9880c002933ec7b9880c000b33e8799880c000773e4789880c0000b3e0be994eb96cf697cce974c9984f700262030b96d45c6cc5d250b54580625c6846c0b7682673813,0x119c71131dc098042c9db1a4071346f30873328773e479385d90a5d70c5df0b5e10bc033bc093400b3e00d37c0028cfd25ec03069009ebd2528d092bf33ec337ac53ba8b0a28f0ae933ee95,
0x1056fd3f800bf8ff1d64e2f51601a531dd1b02df22e9ce04e55299f5295d12911d0425132257376593a9190211f02521029f1319ef3c5f736df939dcd05dcb085d306dd507800bf4fe2d075,0x12a903ae90200104094b50b8b33e8b10b0af0a8ad404002a9033f0a00cc00ae90213ca00cc002b501044a9070a33f4a50689f080a7400002803303efe3fc0029d000530107efb066f9062f7,0x495
]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem impossible : ¬FormulaSat clauses := checkW_sound clauses keys 10 words (by decide +kernel)
end Branch1
namespace Branch2
set_option maxRecDepth 32768 in
def clauses : List (List Nat) := [
[133,13],[133,25],[133,37],[133,121],[157,133],
[169,133],[181,133],[217,133],[241,133],[289,133],
[301,133],[421,133],[445,133],[469,133],[481,133],
[505,133],[541,133],[577,133],[601,133],[613,133],
[625,133],[661,133],[673,133],[709,133],[769,133],
[113,5],[163,7],[161,17],[163,31],[173,161],
[195,27],[195,111],[195,147],[207,3],[207,15],
[207,159],[297,21],[297,237],[401,209],[401,281],
[401,293],[415,283],[437,149],[435,279],[451,115],
[451,175],[451,211],[451,439],[459,207],[463,235],
[463,283],[465,285],[463,295],[465,297],[461,401],
[477,117],[475,151],[475,163],[471,207],[473,401],
[495,207],[497,401],[531,195],[535,295],[533,413],
[567,207],[575,299],[569,401],[571,451],[591,279],
[593,401],[595,499],[611,11],[611,119],[611,179],
[603,231],[603,279],[609,285],[603,291],[605,401],
[603,411],[607,451],[609,465],[609,477],[617,29],
[619,163],[623,239],[621,285],[615,603],[659,23],
[653,161],[651,195],[657,285],[655,451],[659,611],
[667,19],[665,161],[667,163],[665,233],[669,285],
[671,575],[663,603],[701,161],[699,171],[703,451],
[705,657],[729,9],[729,33],[729,153],[729,165],
[729,177],[729,213],[729,417],[729,441],[729,537],
[729,573],[767,167],[759,195],[765,285],[761,401],
[763,451],[765,465],[765,501],[765,597],[791,35],
[791,155],[791,215],[791,287],[791,419],[791,443],
[791,467],[791,479],[791,503],[791,539],[791,599],
[791,707],[2,4,6,8,10,12],[14,16,18,20,22,24],[26,28,30,32,34,36],[110,112,114,116,118,120],
[146,148,150,152,154,156],[158,160,162,164,166,168],[170,172,174,176,178,180],[206,208,210,212,214,216],[230,232,234,236,238,240],
[278,280,282,284,286,288],[290,292,294,296,298,300],[410,412,414,416,418,420],[434,436,438,440,442,444],[458,460,462,464,466,468],
[470,472,474,476,478,480],[494,496,498,500,502,504],[530,532,534,536,538,540],[566,568,570,572,574,576],[590,592,594,596,598,600],
[602,604,606,608,610,612],[614,616,618,620,622,624],[650,652,654,656,658,660],[662,664,666,668,670,672],[698,700,702,704,706,708],
[758,760,762,764,766,768],[194],[400],[450],[728],
[790],[132]
]
set_option maxRecDepth 32768 in
def keys : List Nat := [
49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,
73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,
97,98,12,99,36,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,
119,120,121,122,14,123,15,124,125,126,127,128,129,130,131,132,133,134,37,135,136,137,138,139,
140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,16,160,17,161,
162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,18,183,184,
185,8,19,186,187,20,38,188,189,190,191,192,193,39,194,195,21,7,3,5,4,2,1
]
set_option maxRecDepth 32768 in
def words : List Nat := [
0x119190008007341716190008004941615d9000800464081599000800344c727cc201800bdc15218c201800a2c271b0c20180084cc6140c20180024cc513cc2018001bcc4138c20180006cc3,0x117dc2010006dccf179c20100034cce175c2010002bccd171c2010001cccc2819000800be4181ed9000800974cb1d19000800944ca1c590008008e4c91ad90008007c4c81a5900080076428,0x1266d800c002c4d6262d800c002941a25ed800c00264d525ad800c00084d4256d800c00024d3285c201000bec1924dc201000afcd2221c201000a3c291f5c20100097cd11c9c2010008ecd0,
0x12a7160040068cdf2a3160040047c0929f160040035cde29b160040026cdd297160040008cdc27ad800c008f4db276d800c00864da272d800c006e4d926ed800c00684d826ad800c00354d7,0x10c88400000094e70c48400000064e60c08400000034e52c31600400b0ce42bf160040095ce32bb160040086ce22b716004007dce12b3160040077c2a2af160040074c1b2ab16004006ece0,0x10f084000006f4ee0ec8400000694ed0e884000004b41d0e484000004840a0e084000003c4ec0dc8400000364eb0d884000002d4ea0d484000002a41c0d08400000274e90cc84000001e4e8,
0x11188400000a84f51148400000a542c11084000009c4f410c8400000994f31088400000964f21048400000904f11008400000874f00fc84000007e4ef0f884000007842b0f484000007541e,0x1014007bcf91a0ce0140075c2d180ce0140072c2114cce0140027c20148ce0140003cf8144ce0140000cf72dcd7378d535cd3338d131cd93ac00338051208400000c041f11c8400000b14f6,0x10730107efb066f9062f7055210291f025190212d0752b089250580096dcfa64fc23e3e0b800a7cfb1c23e0b8004ac222f6413c63d36e3b34239326373e8008f82e1bcce014008dcfa1a8ce,
0x12ce6f20a6b2041f130ee2e0a2044e9234a122ce71e667210eb1866d20ced155280492708d23038a703efe052fd0411c01d1b02d17036713d01b30c21350233702539cf13b09f080a5068a9,0x14700749c2346c0b45c0d48c0ea5c90a2c27a3c29a542c03cf8064e627c202941a2a41ca7cfba84f5bdc15be418bec19c041f494164ac224b41d4640847c094840a0025b73cfd202683001c,0x168cdf694ed494164ac224b41d4640847c094840a7341772c2174c1b7541e0025b3f885a4826058b2a34240444b2801128c8c04c8aa68c1a64fc29c0fbf81405454bf410a748ea44874a012,
0x147c094840a7642875c2d77c2a7842b7341772c2174c1b7541e002613fc6e850bc670b985c6d67c5949812468074a463474627401373cfd66c7c48c0e45c0d84cc6864da86ce2874f0684d8,0x19880c0000b400bf994f396cfe97cd1974cb984ff00262030ba6d45a6cc5b250b54580725c6646c0b76825738137747f7447e4747a6dccf6e4d96ece06f4ee24cc5264d526cdd274e946408,0x10a9e10ac033dc0934c0b4000d3940028d05252c030a9009abd2468d092bf34ac3392c53da8b09e8f0a69340e950b000ae8a1410899880c0029340c789880c000b3408779880c0007740476,
0x12891d0425132a5738e593c9190211f02521029f1321ef3e5f7385f93bdcd05dcb085d306dd507800bf5062d07519471125dc094042c5db19c071286f3107333077404793a1d90a1d70b5df,0x1ae90a134a00bc002b509044a9070a3414a50689f080a7420002802f03efe41c0029d080530107efb066f9062f7056fd41800bf9071ce4e2f91601e531d51b02df22edce04e55291f528dd1,0x4922a90bae90a0010c2d8b53a8b3408b1358af334ad424002a90b410a00bc00
]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem impossible : ¬FormulaSat clauses := checkW_sound clauses keys 10 words (by decide +kernel)
end Branch2
namespace Branch3
set_option maxRecDepth 32768 in
def clauses : List (List Nat) := [
[181,13],[181,25],[181,37],[181,121],[181,157],
[181,169],[217,181],[241,181],[289,181],[301,181],
[421,181],[445,181],[469,181],[481,181],[505,181],
[541,181],[577,181],[601,181],[613,181],[625,181],
[661,181],[673,181],[769,181],[113,5],[161,5],
[163,7],[161,17],[163,31],[195,27],[195,111],
[195,147],[207,3],[207,15],[207,159],[283,7],
[297,21],[297,237],[401,209],[401,281],[401,293],
[415,283],[437,149],[437,161],[435,279],[451,115],
[451,211],[451,439],[459,207],[463,235],[463,283],
[465,285],[463,295],[465,297],[461,401],[477,117],
[475,151],[475,163],[471,207],[473,401],[495,207],
[497,401],[531,195],[535,295],[533,413],[567,207],
[575,299],[569,401],[571,451],[591,279],[593,401],
[595,499],[611,11],[611,119],[603,231],[603,279],
[609,285],[603,291],[605,401],[603,411],[607,451],
[609,465],[609,477],[617,29],[619,163],[623,239],
[621,285],[615,603],[659,23],[653,161],[651,195],
[657,285],[655,451],[659,611],[667,19],[665,161],
[667,163],[665,233],[669,285],[671,575],[663,603],
[729,9],[729,33],[729,153],[729,165],[729,213],
[729,417],[729,441],[729,537],[729,573],[767,167],
[759,195],[765,285],[761,401],[763,451],[765,465],
[765,501],[765,597],[791,35],[791,155],[791,215],
[791,287],[791,419],[791,443],[791,467],[791,479],
[791,503],[791,539],[791,599],[2,4,6,8,10,12],[14,16,18,20,22,24],
[26,28,30,32,34,36],[110,112,114,116,118,120],[146,148,150,152,154,156],[158,160,162,164,166,168],[206,208,210,212,214,216],
[230,232,234,236,238,240],[278,280,282,284,286,288],[290,292,294,296,298,300],[410,412,414,416,418,420],[434,436,438,440,442,444],
[458,460,462,464,466,468],[470,472,474,476,478,480],[494,496,498,500,502,504],[530,532,534,536,538,540],[566,568,570,572,574,576],
[590,592,594,596,598,600],[602,604,606,608,610,612],[614,616,618,620,622,624],[650,652,654,656,658,660],[662,664,666,668,670,672],
[758,760,762,764,766,768],[194],[400],[450],[728],
[790],[180]
]
set_option maxRecDepth 32768 in
def keys : List Nat := [
61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,
85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,37,104,105,106,107,
108,12,109,38,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,
130,131,13,132,14,133,134,135,136,137,138,139,140,141,142,143,39,144,40,145,146,147,148,149,
150,151,152,153,154,155,156,157,158,159,160,161,162,15,163,16,164,165,166,167,168,169,170,171,
172,173,174,175,176,177,178,179,41,180,181,182,183,17,184,185,7,18,186,42,19,43,187,188,
189,190,191,192,44,193,20,8,3,5,4,2,1
]
set_option maxRecDepth 32768 in
def words : List Nat := [
0x11b990008007341618d9000800494151899000800464081859000800344c5288c201c00bdc1423cc201c00a2c2c1d8c201c0084cc4168c201c0024cc3164c201c001bcc2160c201c0006cc1,0x11f1c2010008eccc1a5c2010006dc2e1a1c20100034ccb19dc2010001ccca28d9000800be4172119000800974c91f99000800944c81ed90008008e4c71d590008007c4c61cd90008007642d,0x127ed800c006e43127ad800c00684d1276d800c00354d0272d800c002941926ed800c00264cf26ad800c00084ce266d800c0002430291c201000bec18241c201000a3c2f219c20100097ccd,
0x12bf160040077c332bb160040074c1a2b716004006ec322b3160040068cd72af160040047c092ab160040035cd62a7160040026cd52a3160040008cd4286d800c008f4d3282d800c00864d2,0x1108b400000364df104b4000002a41b100b400000274de0fcb4000001e4dd0f8b400000094dc0f4b400000064db0f0b400000034342cb160040095cda2c7160040086cd92c316004007dcd8,0x1130b400000904e412cb400000874e3128b4000007e4e2124b40000078436120b4000007541d11cb4000006f435118b400000694e1114b4000004b41c110b4000004840a10cb4000003c4e0,
0x10140003ce916cce0140000c382dcd7358d5340d332cd1314d937c0033805148b400000c041e144b400000a84e8140b400000a543713cb4000009c4e7138b400000994e6134b400000964e5,0x1a64ed25e3e0e800a7cec1ea3e0e8004ac212f2413923d34e3b3323931e373ac008f83a1e4ce014008dceb1d0ce014007bcea1c8ce0140075c391a8ce0140072c20174ce0140027c1f170ce,0x1181280452709523034a703afe04efd03d1c0191b02d170327139c1b304213382335025370f13809f07ca5064a906f0107afb062f905ef7051210291f025190212d0712b085250540096dcf,
0x1294192a41ba7ceca84e8bdc14be417bec18c041e494154ac214b41c4640847c094840a0025b73cee226682fc1c2d26f22e6b2281f15cee2e0a2040e9254a124ce720a67234eb1ae6d230ed,0x10025b3bc8ea482b058b3a3426044562801028c9404c92a68c0a64ed29c0ebf8130545fbf40fa7496a44274a0114700649c2546c0b45c0c48c0da5c98a2c2ca3c2fa543703ce9064db27c1f,0x1850bb670b985c7767c6449811468064a46d4746c7401273cee66c8548c0d45c0c84cc4864d286cd9874e3684d168cd7694e1494154ac214b41c4640847c094840a7341672c2074c1a7541d,
0x1250b64580625c7046c0b7682a738127748874487474836dc2e6e4316ec326f43524cc3264cf26cd5274de4640847c094840a7642d75c3977c33784367341672c2074c1a7541d002613c078,0x11dcf11e4dd7642d75c3977c337843600c380243002c3b03434000a33cc9198822002933c88198822000773c480988220000b0ecbe994e696cef97ccd974c9984f000262088296d4656cc24,0x17c8ba73812954a77d4a6744a54740f944c895cda964e54640847c094840a7c4c67bcea7dcd87e4e27341672c2074c1a7541d002fd3d0b51d46f1c4537702a0102876c7101c551bcc21ccca,
0x1280230028d3e46628023001b53e05428023000053dc102a41b28cf32941927c1f29cf6000a008c0ebf8f5000a73d813c041ebec18be417bdc14bf4f4002fe3d47d938bd4580694c7f46c0b,0x1a40fc0011d3fc246c8fb001173f85e018fa0011b3f42ba5437a4cf2a3c2fa2c2ca34f9002903f0296f4356ec326e4316dc2e6d4f8001b23ec280343402c3b0243000c38014f7000063e826,0x1019210291f0251d3fd19021173f91b3f40040027
]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem impossible : ¬FormulaSat clauses := checkW_sound clauses keys 10 words (by decide +kernel)
end Branch3
namespace Branch4
set_option maxRecDepth 32768 in
def clauses : List (List Nat) := [
[625,13],[625,25],[625,37],[625,121],[625,157],
[625,169],[625,181],[625,217],[625,241],[625,289],
[625,301],[625,421],[625,445],[625,469],[625,481],
[625,505],[625,541],[625,577],[625,601],[625,613],
[661,625],[673,625],[709,625],[769,625],[113,5],
[163,7],[161,17],[163,31],[173,29],[173,161],
[195,27],[195,111],[195,147],[207,3],[207,15],
[207,159],[239,179],[297,21],[297,237],[401,209],
[401,281],[401,293],[415,283],[437,149],[435,279],
[451,115],[451,175],[451,211],[451,439],[459,207],
[463,235],[463,283],[465,285],[463,295],[465,297],
[461,401],[477,117],[475,151],[475,163],[471,207],
[473,401],[495,207],[497,401],[531,195],[535,295],
[533,413],[567,207],[575,299],[569,401],[571,451],
[591,279],[593,401],[595,499],[611,11],[611,119],
[603,171],[611,179],[603,231],[603,279],[609,285],
[603,291],[605,401],[603,411],[607,451],[609,465],
[609,477],[659,23],[653,161],[651,195],[657,285],
[655,451],[659,611],[667,19],[665,161],[667,163],
[665,233],[669,285],[671,575],[663,603],[701,161],
[699,171],[703,451],[705,657],[729,9],[729,33],
[729,153],[729,165],[729,177],[729,213],[729,417],
[729,441],[729,537],[729,573],[767,167],[759,195],
[765,285],[761,401],[763,451],[765,465],[765,501],
[765,597],[791,35],[791,155],[791,215],[791,287],
[791,419],[791,443],[791,467],[791,479],[791,503],
[791,539],[791,599],[791,707],[2,4,6,8,10,12],[14,16,18,20,22,24],
[26,28,30,32,34,36],[110,112,114,116,118,120],[146,148,150,152,154,156],[158,160,162,164,166,168],[170,172,174,176,178,180],
[206,208,210,212,214,216],[230,232,234,236,238,240],[278,280,282,284,286,288],[290,292,294,296,298,300],[410,412,414,416,418,420],
[434,436,438,440,442,444],[458,460,462,464,466,468],[470,472,474,476,478,480],[494,496,498,500,502,504],[530,532,534,536,538,540],
[566,568,570,572,574,576],[590,592,594,596,598,600],[602,604,606,608,610,612],[650,652,654,656,658,660],[662,664,666,668,670,672],
[698,700,702,704,706,708],[758,760,762,764,766,768],[194],[400],[450],
[728],[790],[624]
]
set_option maxRecDepth 32768 in
def keys : List Nat := [
53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,
77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,
101,102,103,12,104,36,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,
123,124,125,126,127,128,14,129,15,130,131,132,133,134,135,37,136,137,138,139,140,141,142,143,
144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,16,161,17,162,163,164,165,
166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,18,38,184,185,8,19,
186,187,20,39,188,189,190,191,192,40,193,194,21,7,3,5,4,2,1
]
set_option maxRecDepth 32768 in
def words : List Nat := [
0x11a590008007341717590008004941617190008004640816d9000800344c6280c201800bdc1521cc201800a2c281c4c20180084cc5150c20180024cc414cc2018001bcc3148c20180006cc2,0x1191c2010006dccd18dc20100034ccc189c2010002bc2a185c2010001cccb2859000800be4182059000800974ca1e59000800944c91d990008008e4c81c190008007c4c71b9900080076429,0x126ad800c002c42c266d800c002941a262d800c00264d325ed800c00084d225ad800c00024d1289c201000bec19251c201000afcd0225c201000a3c2b20dc20100097ccf1ddc2010008ecce,
0x12ab160040068cdc2a7160040047c092a3160040035cdb29f160040026cda29b160040008cd927ed800c008f4d827ad800c00864d7276d800c006e4d6272d800c00684d526ed800c00354d4,0x10da7000000094e40d67000000064e30d27000000034e22c71600400b0ce12c3160040095ce02bf160040086cdf2bb16004007dcde2b7160040077c2d2b3160040074c1b2af16004006ecdd,0x110270000006f4ea0fe7000000694e90fa70000004b41d0f670000004840a0f270000003c4e80ee7000000364e70ea70000002d42e0e670000002a41c0e27000000274e60de70000001e4e5,
0x112a7000000b14f11267000000a84f01227000000a543011e7000000994ef11a7000000964ee1167000000904ed1127000000874ec10e70000007e4eb10a70000007842f10670000007541e,0x1014008dcf51bcce014007bcf41b4ce0140075c31194ce0140072c2115cce0140027c20158ce0140003cf3154ce0140000cf22dcd736cd5350d3330d1318d939c003380512e7000000c041f,0x13a09f080a5068a90730107efb066f9062f7055210291f025190212d0752b089250580096dcfa64f72423e0c800a7cf61d63e0c8004ac222f6413b63d3623b33a39322373d4008f8321d0ce,
0x173cf8140ac0941c2d0b31601f13cee2e0a2044e9238a1230ab1f4e71fceb198ed169280492708d23038a703efe052fd0411c01d1b02d17034af0a8b10b0b50b81b308213482336425390f1,0x1a748fa44884a0124700749c2346c0b45c0d48c0ea5c91a2c28a3c2ba543003cf3064e327c202941a2a41ca7cf6a84f0bdc15be418bec19c041f494164ac224b41d4640847c094840a0025b,0x186cdf874ec684d568cdc694e9494164ac224b41d4640847c094840a7341772c2174c1b7541e0025b3e486a4827058b3a34240444e2801128c8d04c8ba68c0a64f729c0fbf81405459bf410,
0x126cda274e64640847c094840a7642975c3177c2d7842f7341772c2174c1b7541e002613e873850bc670b985c7267c5e49812468074a468474677401373cf866c8248c0e45c0d84cc5864d7,0x19880c000773f07b9880c0000b3ecbf994ef96cf997ccf974ca984fa00262030ba6d45f6cc60250b64580725c6b46c0b76826738137748574484474806dccd6e4d66ecdd6f4ea24cc4264d3,0x1395d90a5d70c5df0b5e10bc033c8093440b3ec0d3880028d00256c03069009ebd24a8d092bf342c3386c53c68b0a28f0ae933fa950c000ae8a13fc8a9880c002933f87e9880c000b33f47c,
0x104e55295f5291d128d1d0425132657382593b9190211f02521029f131def3d1f7379f93adcd05dcb085d306dd507800bf5012d4751a871131dc098042c9db1b0071346f30c7332c773f079,0x12a9063fca00cc00ae905144a00cc002b504044a9070a3400a50689f080a740c002803303efe4080029d030530107efb066f9062f7056fd40400bf9021e24e2f91601e531e91b02df22edce,0x4932a906ae90500107094b50b8b33f4b10b0af0a8ad41000
]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem impossible : ¬FormulaSat clauses := checkW_sound clauses keys 10 words (by decide +kernel)
end Branch4
namespace Branch5
set_option maxRecDepth 32768 in
def clauses : List (List Nat) := [
[709,13],[709,25],[709,37],[709,121],[709,157],
[709,169],[709,181],[709,217],[709,241],[709,289],
[709,301],[709,421],[709,445],[709,469],[709,481],
[709,505],[709,541],[709,577],[709,601],[709,613],
[709,625],[709,661],[709,673],[769,709],[113,5],
[161,5],[163,7],[161,17],[163,31],[173,161],
[195,27],[195,111],[195,147],[207,3],[207,15],
[207,159],[235,7],[233,161],[231,171],[297,21],
[297,237],[401,209],[401,281],[401,293],[415,283],
[437,149],[435,279],[451,115],[451,175],[451,211],
[451,439],[459,207],[463,235],[463,283],[465,285],
[463,295],[465,297],[461,401],[477,117],[475,151],
[475,163],[471,207],[473,401],[495,207],[497,401],
[531,195],[535,295],[533,413],[567,207],[575,299],
[569,401],[571,451],[591,279],[593,401],[595,499],
[611,11],[611,119],[611,179],[603,231],[611,239],
[603,279],[609,285],[603,291],[605,401],[603,411],
[607,451],[609,465],[609,477],[617,29],[619,163],
[623,239],[621,285],[615,603],[659,23],[653,161],
[651,195],[657,237],[657,285],[655,451],[659,611],
[667,19],[665,161],[667,163],[665,233],[669,285],
[671,575],[663,603],[729,9],[729,33],[729,153],
[729,165],[729,177],[729,213],[729,417],[729,441],
[729,537],[729,573],[767,167],[759,195],[765,285],
[761,401],[763,451],[765,465],[765,501],[765,597],
[791,35],[791,155],[791,215],[791,287],[791,419],
[791,443],[791,467],[791,479],[791,503],[791,539],
[791,599],[2,4,6,8,10,12],[14,16,18,20,22,24],[26,28,30,32,34,36],[110,112,114,116,118,120],
[146,148,150,152,154,156],[158,160,162,164,166,168],[170,172,174,176,178,180],[206,208,210,212,214,216],[230,232,234,236,238,240],
[278,280,282,284,286,288],[290,292,294,296,298,300],[410,412,414,416,418,420],[434,436,438,440,442,444],[458,460,462,464,466,468],
[470,472,474,476,478,480],[494,496,498,500,502,504],[530,532,534,536,538,540],[566,568,570,572,574,576],[590,592,594,596,598,600],
[602,604,606,608,610,612],[614,616,618,620,622,624],[650,652,654,656,658,660],[662,664,666,668,670,672],[758,760,762,764,766,768],
[194],[400],[450],[728],[790],
[708]
]
set_option maxRecDepth 32768 in
def keys : List Nat := [
56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,
80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,
104,105,106,107,108,13,109,36,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,
126,127,128,129,130,131,132,133,14,134,15,135,136,137,138,139,140,141,142,143,144,145,37,146,
147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,16,168,17,
169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,38,185,186,187,188,18,189,190,
39,8,19,191,192,20,40,193,194,195,196,197,198,41,199,21,7,3,5,4,2,1
]
set_option maxRecDepth 32768 in
def words : List Nat := [
0x11b99000800734171899000800494161859000800464081819000800344cb29cc201800bdc15244c201800a2c291d8c20180084cca15cc20180024cc9158c2018001bcc8154c20180006cc7,0x11a5c2010006dcd31a1c20100034cd219dc2010002bcd1199c2010001ccd02a19000800be4182199000800974cf1f99000800944ce1ed90008008e4cd1d590008007c4cc1cd90008007642a,0x128ad800c00354d9286d800c002c4d8282d800c002941a27ed800c00264d727ad800c00084d6276d800c000242c2a5c201000bec19251c201000a3c2b221c20100097cd51f1c2010008ecd4,
0x12cb16004006ece22c7160040068ce12c3160040047c092bf160040035ce02bb160040026cdf2b7160040008cde29ad800c008f4dd296d800c00864dc292d800c006e4db28ed800c00684da,0x10eec400000274e90eac4000001e4e80e6c400000094e70e2c400000064e60dec4000000342e2df160040095ce52db160040086ce42d716004007dce32d3160040077c2d2cf160040074c1b,0x1116c40000078430112c4000007541e10ec4000006f4ed10ac400000694ec106c4000004b41d102c4000004840a0fec4000003c42f0fac400000364eb0f6c4000002d4ea0f2c4000002a41c,
0x132cd93ac003380513ac400000c041f136c400000a84f4132c400000a543112ec4000009c4f312ac400000994f2126c400000964f1122c400000904f011ec400000874ef11ac4000007e4ee,0x13763b35239336373dc008f8341e4ce014008dcf71d0ce014007bcf61c8ce0140075c331a8ce0140072c21168ce0140027c20164ce0140003cf5160ce0140000c322f4d7380d5364d3348d1,0x1036713cc1b31c21358233782539cf10bc9f080a5068a90730107efb066f9062f7055210291f025190212d0752b089250580096dcfa64f926e3e0d000a7cf81ea3e0d0004ac2230a413c23d,
0x14ac224b41d4640847c094840a0025b73cfa22e683141c2e66f2366b2301f14cee098a2044e9264a125ce720e6723ceb1ae6d238ed17d280492708d23038a703efe052fd0411c01d1b03117,0x1a68c6a64f929c0fbf8140545ebf410a749aa44934a0124700749c2346c0c45c0d48c0ea5c9ca2c29a3c2ba543103cf5064e627c202941a2a41ca7cf8a84f4bdc15be418bec19c041f49416,0x173cfa66c8748c0e45c0d84cca864dc86ce4874ef684da68ce1694ec494164ac224b41d4640847c094840a7341772c2174c1b7541e0025b3ec90a4828058b8a3424044522801128c9804c96,
0x16dcd36e4db6ece26f4ed24cc9264d726cdf274e94640847c094840a7642a75c3377c2d784307341772c2174c1b7541e002613f078850c1670be85c7767c6349812468074a46d4746c74013,0x19880b000ef3fc829880b000b33f8819880b000773f4809880b0000b0d4c4994f296cfb97cd5974cf984fc0026202cbf6d4646cc65250bb4580725c7046c0c76827738137748a7448947485,0x10b5e10c0030c8090b00b0d40d0b80028d02098ed248eb16e900a0060968d090e917005140ef3fcf10be8b0a68f0ae93402950c4030c8090b00b0d40d0b800398a1404959880b0029340084,
0x12a91d0425133a57396593c5190211f02521029f1331ef3d9f738df93b9cd05dcb085d306dd507800bf5032e8751bc7113ddc09c04095db1c4071446f32073340773f4793a1d90a9d70cddf,0x139907150a00d8002b506044a9070a3408a50689f080a7414002803603efe4100029d050530107efb066f9062f7056fd40c00bf9041f64e30d1601e531fd1b031f2301ce04e552b1f52add1,0x45d2a90839907001092f0b53a8b33f8b1360af344ad418002a908404a00d800
]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem impossible : ¬FormulaSat clauses := checkW_sound clauses keys 10 words (by decide +kernel)
end Branch5
end ProjectiveSharp
namespace ProjectiveSharp
open PEqualNP.Library.LRAT
def var (i k : Nat) := 6*i+k+1
def assignment (f : Nat → Fin 6) (v : Nat) := (f ((v-1)/6)).val == ((v-1)%6)
theorem readVar (f : Nat → Fin 6) (i k : Nat) (hk : k<6) :
    assignment f (var i k) = decide ((f i).val=k) := by
  have d : (var i k-1)/6=i := by unfold var; omega
  have m : (var i k-1)%6=k := by unfold var; omega
  simp [assignment,d,m]
theorem positiveLit (f : Nat → Fin 6) (i k : Nat) (hk : k<6) :
    litVal (assignment f) (2*var i k) = true ↔ (f i).val=k := by
  have d : 2*var i k/2=var i k := by omega
  have m : (2*var i k)%2=0 := by omega
  simp [litVal,d,m,readVar f i k hk]
theorem negativeLit (f : Nat → Fin 6) (i k : Nat) (hk : k<6) :
    litVal (assignment f) (2*var i k+1) = true ↔ (f i).val≠k := by
  have d : (2*var i k+1)/2=var i k := by omega
  have m : (2*var i k+1)%2=1 := by omega
  simp [litVal,d,m,readVar f i k hk]
abbrev Point := Nat × Nat
abbrev Edge := Nat × Nat × Nat
def board : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def points : List Point := [(0, 2), (0, 3), (0, 4), (0, 8), (0, 10), (0, 19), (2, 0), (2, 3), (2, 10), (2, 12), (2, 17), (3, 0), (3, 4), (3, 17), (4, 2), (4, 8), (5, 19), (5, 20), (6, 0), (6, 3), (6, 8), (6, 12), (6, 15), (6, 16), (7, 15), (7, 16), (9, 0), (9, 4), (9, 6), (9, 12), (9, 13), (11, 4), (11, 6), (11, 12), (11, 15), (11, 19), (11, 20), (13, 4), (13, 6), (13, 8), (13, 10), (13, 16), (13, 19), (15, 3), (15, 4), (15, 6), (15, 10), (15, 18), (16, 3), (16, 6), (16, 13), (17, 0), (17, 2), (17, 6), (17, 12), (17, 15), (17, 19), (18, 0), (18, 3), (18, 8), (18, 10), (18, 15), (18, 20), (20, 10), (20, 12), (20, 18)]
def conflict (i j : Nat) : Bool :=
  let a := points.getD i (0,0)
  let b := points.getD j (0,0)
  (board.getD a.1 0).testBit b.2 || (board.getD b.1 0).testBit a.2
def checked (e : Edge) : Bool := decide(e.1 < 66 ∧ e.2.1 < 66 ∧ e.2.2 < 6 ∧ e.1 ≠ e.2.1) &&
    ((e.2.2==5) || conflict e.1 e.2.1)
def proper (f : Nat → Fin 6) := ∀ e : Edge, checked e=true →
    ¬ ((f e.1).val=e.2.2 ∧ (f e.2.1).val=e.2.2)
def negative (e : Edge) := [2*var e.1 e.2.2+1,2*var e.2.1 e.2.2+1]
def positive (i : Nat) := (List.range 6).map fun k => 2*var i k
def unitC (a : Point) := [2*var a.1 a.2]
def assemble (n : List Edge) (p : List Nat) (u : List Point) :=
  n.map negative ++ p.map positive ++ u.map unitC

theorem allocated (f : Nat → Fin 6) (ok : proper f) (n : List Edge) (p : List Nat) (u : List Point)
    (nc : n.all checked = true) (selected : ∀ a ∈ u, (f a.1).val=a.2) :
    FormulaSat (assemble n p u) := by
  refine ⟨assignment f,?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hp|hu
  · rcases List.mem_append.mp hp with hn|hp
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
      have ce := List.all_eq_true.mp nc e he
      have ck : e.2.2<6 := by
        by_contra h
        simp [checked,h] at ce
      by_cases x : (f e.1).val=e.2.2
      · have y : (f e.2.1).val≠e.2.2 := fun h => ok e ce ⟨x,h⟩
        exact ⟨_,by simp [negative],(negativeLit f _ _ ck).mpr y⟩
      · exact ⟨_,by simp [negative],(negativeLit f _ _ ck).mpr x⟩
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
      refine ⟨2*var i (f i).val,?_,(positiveLit f _ _ (f i).isLt).mpr rfl⟩
      exact List.mem_map.mpr ⟨(f i).val,List.mem_range.mpr (f i).isLt,rfl⟩
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
    have eq := selected a ha
    have hk : a.2<6 := by rw [←eq]; exact (f a.1).isLt
    exact ⟨_,by simp [unitC],(positiveLit f _ _ hk).mpr eq⟩
namespace Branch0
set_option maxRecDepth 32768 in
def n : List Edge := [
(3, 0, 5),(11, 0, 5),(11, 1, 5),(11, 9, 5),(12, 11, 5),(13, 0, 5),(13, 1, 5),(13, 11, 5),(13, 12, 5),(16, 13, 5),(17, 0, 5),(17, 1, 5),
(17, 5, 5),(17, 7, 5),(17, 11, 5),(17, 12, 5),(17, 13, 5),(17, 16, 5),(19, 0, 5),(19, 1, 5),(19, 8, 5),(19, 9, 5),(19, 11, 5),(19, 12, 5),
(19, 13, 5),(19, 17, 5),(20, 19, 5),(23, 12, 5),(23, 13, 5),(23, 17, 5),(23, 19, 5),(25, 0, 5),(25, 1, 5),(25, 9, 5),(25, 11, 5),(25, 12, 5),
(25, 13, 5),(25, 17, 5),(25, 19, 5),(25, 23, 5),(26, 19, 5),(27, 0, 5),(30, 20, 5),(30, 27, 5),(31, 12, 5),(31, 19, 5),(33, 0, 5),(33, 1, 5),
(33, 9, 5),(33, 13, 5),(33, 17, 5),(33, 23, 5),(33, 25, 5),(34, 11, 5),(34, 13, 5),(34, 25, 5),(34, 26, 5),(34, 33, 5),(36, 11, 5),(36, 15, 5),
(36, 17, 5),(36, 29, 5),(36, 33, 5),(37, 0, 5),(37, 11, 5),(37, 17, 5),(37, 19, 5),(37, 36, 5),(38, 0, 5),(38, 9, 5),(38, 13, 5),(38, 15, 5),
(38, 17, 5),(38, 19, 5),(38, 25, 5),(38, 29, 5),(38, 36, 5),(38, 37, 5),(39, 38, 5),(41, 11, 5),(42, 19, 5),(42, 25, 5),(42, 38, 5),(43, 11, 5),
(43, 13, 5),(43, 25, 5),(43, 26, 5),(45, 25, 5),(48, 1, 5),(48, 7, 5),(48, 11, 5),(48, 12, 5),(48, 17, 5),(48, 19, 5),(48, 25, 5),(48, 33, 5),
(48, 42, 5),(49, 0, 5),(49, 5, 5),(49, 7, 5),(49, 13, 5),(49, 16, 5),(49, 19, 5),(49, 23, 5),(49, 25, 5),(49, 48, 5),(50, 0, 5),(50, 1, 5),
(50, 11, 5),(50, 12, 5),(50, 13, 5),(50, 15, 5),(50, 17, 5),(50, 19, 5),(50, 25, 5),(50, 30, 5),(50, 33, 5),(50, 36, 5),(50, 38, 5),(50, 49, 5),
(52, 0, 5),(52, 11, 5),(52, 12, 5),(52, 15, 5),(52, 23, 5),(52, 33, 5),(52, 48, 5),(54, 0, 5),(54, 11, 5),(54, 12, 5),(54, 13, 5),(54, 19, 5),
(54, 25, 5),(54, 38, 5),(54, 50, 5),(56, 19, 5),(56, 33, 5),(57, 0, 5),(57, 13, 5),(57, 38, 5),(59, 20, 5),(59, 27, 5),(60, 0, 5),(60, 1, 5),
(60, 9, 5),(60, 12, 5),(60, 13, 5),(60, 15, 5),(60, 17, 5),(60, 19, 5),(60, 23, 5),(60, 25, 5),(60, 26, 5),(60, 30, 5),(60, 33, 5),(60, 36, 5),
(60, 38, 5),(60, 48, 5),(60, 49, 5),(60, 50, 5),(60, 52, 5),(60, 53, 5),(60, 57, 5),(60, 59, 5),(61, 23, 5),(61, 25, 5),(62, 0, 5),(62, 13, 5),
(63, 0, 5),(63, 13, 5),(63, 60, 5),(65, 0, 5),(65, 1, 5),(65, 4, 5),(65, 8, 5),(65, 9, 5),(65, 11, 5),(65, 12, 5),(65, 13, 5),(65, 17, 5),
(65, 19, 5),(65, 23, 5),(65, 25, 5),(65, 27, 5),(65, 31, 5),(65, 33, 5),(65, 38, 5),(65, 39, 5),(65, 41, 5),(65, 42, 5),(65, 47, 5),(65, 48, 5),
(65, 49, 5),(65, 50, 5),(65, 52, 5),(65, 54, 5),(65, 57, 5),(65, 60, 5),(65, 64, 5),(7, 0, 0),(7, 5, 0),(10, 0, 1),(10, 1, 1),(10, 3, 1),
(10, 4, 1),(10, 5, 1),(11, 2, 0),(12, 0, 0),(12, 1, 0),(12, 7, 1),(13, 2, 0),(13, 7, 1),(13, 8, 1),(14, 1, 2),(14, 7, 2),(14, 8, 2),
(14, 9, 2),(14, 11, 2),(14, 12, 2),(14, 13, 2),(15, 2, 0),(15, 11, 1),(15, 13, 1),(16, 2, 0),(16, 7, 4),(16, 10, 1),(16, 12, 3),(17, 0, 2),
(17, 1, 4),(17, 2, 0),(17, 3, 4),(17, 4, 4),(17, 5, 4),(17, 8, 4),(17, 9, 3),(17, 9, 4),(17, 11, 1),(17, 11, 3),(17, 12, 1),(17, 12, 3),
(17, 13, 1),(19, 0, 0),(19, 11, 1),(19, 12, 0),(19, 12, 1),(19, 13, 1),(19, 14, 2),(20, 0, 0),(20, 13, 1),(20, 14, 2),(23, 0, 0),(23, 14, 2),
(25, 1, 0),(25, 7, 1),(25, 9, 1),(25, 19, 0),(25, 19, 1),(26, 2, 0),(26, 14, 2),(26, 20, 3),(26, 23, 1),(26, 25, 1),(27, 3, 0),(27, 14, 2),
(27, 20, 0),(27, 25, 1),(29, 15, 2),(29, 17, 3),(29, 17, 4),(30, 15, 2),(30, 19, 0),(30, 19, 4),(30, 25, 1),(31, 4, 0),(31, 8, 0),(31, 14, 2),
(31, 25, 0),(31, 25, 1),(33, 4, 2),(33, 16, 3),(33, 17, 2),(33, 17, 4),(33, 23, 1),(33, 25, 1),(33, 25, 2),(34, 23, 1),(34, 25, 1),(36, 0, 2),
(36, 1, 4),(36, 2, 0),(36, 3, 2),(36, 5, 4),(36, 11, 1),(36, 11, 3),(36, 12, 3),(36, 13, 1),(36, 23, 4),(36, 25, 2),(37, 9, 0),(37, 9, 1),
(37, 14, 2),(37, 17, 3),(37, 29, 1),(37, 33, 1),(37, 36, 3),(38, 9, 0),(38, 9, 1),(38, 9, 4),(38, 17, 2),(38, 17, 3),(38, 17, 4),(38, 19, 0),
(38, 19, 4),(38, 23, 1),(38, 25, 0),(38, 25, 1),(38, 25, 2),(38, 29, 3),(38, 30, 0),(38, 30, 4),(38, 33, 1),(38, 33, 2),(38, 33, 3),(38, 36, 3),
(39, 9, 0),(39, 9, 4),(39, 13, 1),(39, 17, 3),(39, 27, 0),(41, 9, 4),(41, 17, 4),(41, 27, 0),(42, 7, 4),(42, 8, 3),(42, 9, 0),(42, 9, 4),
(42, 10, 1),(42, 17, 2),(42, 17, 3),(42, 17, 4),(42, 29, 4),(42, 33, 0),(43, 11, 1),(43, 13, 1),(43, 14, 2),(43, 17, 4),(43, 25, 1),(43, 34, 0),
(45, 17, 4),(45, 19, 0),(45, 34, 1),(47, 31, 0),(47, 41, 1),(47, 42, 2),(48, 0, 0),(48, 9, 0),(48, 9, 4),(48, 11, 1),(48, 12, 0),(48, 13, 1),
(48, 14, 2),(48, 23, 0),(48, 23, 4),(48, 25, 0),(48, 26, 4),(48, 29, 0),(48, 33, 0),(48, 34, 4),(48, 41, 0),(49, 0, 0),(49, 11, 1),(49, 14, 2),
(49, 19, 0),(49, 19, 1),(49, 19, 4),(49, 20, 4),(49, 23, 0),(49, 23, 1),(49, 25, 0),(49, 25, 1),(49, 26, 4),(49, 33, 0),(49, 33, 1),(49, 34, 4),
(50, 0, 0),(50, 9, 0),(50, 9, 1),(50, 9, 4),(50, 11, 1),(50, 14, 2),(50, 19, 0),(50, 19, 4),(50, 23, 1),(50, 25, 0),(50, 25, 1),(50, 29, 0),
(50, 33, 0),(50, 34, 0),(50, 37, 0),(50, 37, 1),(50, 38, 0),(50, 38, 4),(50, 39, 4),(50, 41, 1),(50, 42, 0),(50, 42, 4),(51, 0, 3),(51, 1, 3),
(51, 3, 3),(51, 4, 3),(51, 5, 3),(51, 7, 3),(51, 13, 3),(51, 15, 3),(51, 19, 3),(51, 23, 3),(51, 25, 3),(51, 30, 3),(51, 41, 3),(51, 43, 3),
(51, 48, 3),(51, 49, 3),(51, 50, 3),(52, 1, 0),(52, 9, 3),(52, 10, 1),(52, 12, 0),(52, 19, 0),(52, 25, 2),(52, 30, 2),(52, 41, 2),(52, 48, 0),
(52, 50, 0),(53, 1, 0),(53, 10, 1),(53, 25, 2),(54, 1, 0),(54, 10, 1),(54, 17, 2),(54, 17, 3),(54, 19, 0),(54, 25, 2),(54, 37, 0),(54, 37, 3),
(54, 38, 0),(54, 38, 2),(54, 38, 3),(54, 39, 2),(54, 41, 2),(54, 42, 2),(54, 48, 0),(54, 49, 0),(54, 50, 0),(56, 1, 0),(56, 8, 3),(56, 9, 3),
(56, 10, 1),(56, 48, 0),(57, 1, 4),(57, 2, 0),(57, 10, 1),(57, 12, 3),(57, 14, 2),(57, 27, 3),(57, 48, 4),(57, 49, 4),(57, 50, 4),(57, 52, 3),
(58, 0, 4),(58, 11, 4),(58, 12, 4),(58, 13, 4),(58, 15, 4),(58, 25, 4),(58, 27, 4),(58, 31, 4),(58, 37, 4),(58, 47, 4),(58, 52, 4),(58, 53, 4),
(58, 54, 4),(58, 56, 4),(59, 2, 0),(59, 10, 1),(59, 14, 2),(59, 26, 3),(59, 30, 4),(60, 2, 0),(60, 10, 1),(60, 11, 3),(60, 12, 3),(60, 14, 2),
(60, 16, 3),(60, 16, 4),(60, 17, 4),(60, 27, 3),(60, 31, 3),(60, 33, 3),(60, 33, 4),(60, 34, 3),(60, 36, 3),(60, 36, 4),(60, 37, 3),(60, 47, 3),
(60, 52, 3),(61, 2, 0),(61, 10, 1),(61, 14, 2),(61, 45, 3),(61, 48, 4),(61, 49, 4),(62, 1, 4),(62, 2, 0),(62, 10, 1),(62, 11, 3),(62, 14, 2),
(63, 2, 0),(63, 11, 3),(63, 13, 1),(63, 16, 2),(63, 17, 1),(63, 17, 2),(63, 17, 4),(63, 23, 4),(63, 25, 2),(63, 49, 1),(63, 53, 3),(63, 62, 4),
(64, 2, 0),(64, 12, 1),(64, 17, 3),(64, 25, 1),(64, 25, 2),(64, 38, 2),(64, 48, 4),(65, 2, 0),(65, 5, 2),(65, 12, 1),(65, 16, 2),(65, 17, 1),
(65, 17, 2),(65, 17, 3),(65, 23, 1),(65, 25, 1),(65, 25, 2),(65, 31, 1),(65, 33, 1),(65, 33, 2),(65, 33, 3),(65, 34, 2),(65, 36, 2),(65, 36, 3),
(65, 37, 1),(65, 38, 1),(65, 38, 2),(65, 38, 3),(65, 42, 2),(65, 42, 3),(65, 45, 2),(65, 49, 1),(65, 56, 2),(65, 57, 3),(65, 58, 4),(65, 60, 3),
(65, 61, 3)
]
def p : List Nat := [
0,1,3,4,5,7,8,9,11,12,13,15,
16,17,19,20,23,25,26,27,29,30,31,33,
34,36,37,38,39,41,42,43,45,47,48,49,
50,52,53,54,56,57,59,60,61,62,63,64,
65
]
def units : List Point := [
(2, 0),(10, 1),(14, 2),(51, 3),(58, 4)
]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem valid : n.all checked=true ∧ assemble n p units=clauses := by decide +kernel
theorem forbidden (f : Nat → Fin 6) (ok : proper f) : ¬ ∀ a∈units,(f a.1).val=a.2 := by
  intro h
  apply impossible
  rw [←valid.2]
  exact allocated f ok n p units valid.1 h
end Branch0
namespace Branch1
set_option maxRecDepth 32768 in
def n : List Edge := [
(2, 0, 5),(2, 1, 5),(9, 2, 5),(12, 2, 5),(13, 2, 5),(14, 2, 5),(17, 2, 5),(19, 2, 5),(23, 2, 5),(24, 2, 5),(34, 2, 5),(36, 2, 5),
(38, 2, 5),(39, 2, 5),(41, 2, 5),(44, 2, 5),(47, 2, 5),(49, 2, 5),(50, 2, 5),(51, 2, 5),(54, 2, 5),(55, 2, 5),(58, 2, 5),(63, 2, 5),
(9, 0, 1),(13, 0, 2),(13, 1, 1),(14, 13, 1),(16, 9, 0),(16, 12, 0),(17, 0, 0),(17, 1, 0),(17, 13, 0),(19, 14, 4),(24, 1, 3),(24, 19, 3),
(33, 17, 1),(33, 23, 1),(33, 24, 1),(34, 23, 2),(36, 12, 1),(36, 23, 0),(37, 9, 2),(37, 14, 2),(37, 17, 2),(37, 36, 2),(38, 17, 0),(38, 19, 2),
(38, 23, 2),(38, 23, 3),(38, 24, 2),(38, 24, 3),(38, 33, 1),(39, 9, 3),(39, 12, 2),(39, 13, 2),(39, 17, 0),(39, 33, 1),(41, 17, 0),(41, 33, 1),
(44, 16, 0),(44, 24, 2),(44, 34, 1),(47, 17, 0),(47, 24, 4),(47, 33, 1),(47, 37, 2),(49, 23, 0),(49, 33, 1),(49, 41, 2),(50, 0, 4),(50, 9, 4),
(50, 14, 0),(50, 14, 4),(50, 19, 0),(50, 23, 0),(50, 23, 3),(50, 24, 0),(50, 33, 1),(50, 34, 0),(50, 37, 2),(50, 38, 3),(50, 39, 3),(51, 13, 2),
(51, 14, 1),(51, 19, 4),(51, 23, 3),(51, 50, 0),(54, 1, 4),(54, 13, 1),(54, 16, 0),(54, 23, 3),(54, 37, 2),(54, 50, 4),(55, 1, 2),(55, 13, 1),
(55, 13, 2),(55, 19, 1),(55, 23, 3),(55, 47, 4),(55, 50, 0),(58, 13, 1),(58, 14, 0),(58, 37, 2),(58, 54, 3),(60, 0, 3),(60, 12, 3),(60, 13, 3),
(60, 14, 3),(60, 17, 3),(60, 34, 3),(60, 36, 3),(60, 44, 3),(60, 47, 3),(63, 13, 4),(63, 16, 0),(63, 23, 3),(63, 33, 1),(63, 37, 2),(63, 38, 3),
(63, 41, 3),(63, 49, 3),(65, 12, 4),(65, 17, 4),(65, 23, 4),(65, 34, 4),(65, 36, 4),(65, 38, 4),(65, 39, 4),(65, 41, 4),(65, 44, 4),(65, 49, 4),
(65, 58, 4)
]
def p : List Nat := [
0,1,9,12,13,14,17,19,23,24,34,36,
38,39,41,44,47,49,50,51,54,55,58,63
]
def units : List Point := [
(16, 0),(33, 1),(37, 2),(60, 3),(65, 4),(2, 5)
]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem valid : n.all checked=true ∧ assemble n p units=clauses := by decide +kernel
theorem forbidden (f : Nat → Fin 6) (ok : proper f) : ¬ ∀ a∈units,(f a.1).val=a.2 := by
  intro h
  apply impossible
  rw [←valid.2]
  exact allocated f ok n p units valid.1 h
end Branch1
namespace Branch2
set_option maxRecDepth 32768 in
def n : List Edge := [
(10, 0, 5),(10, 1, 5),(10, 2, 5),(10, 9, 5),(12, 10, 5),(13, 10, 5),(14, 10, 5),(17, 10, 5),(19, 10, 5),(23, 10, 5),(24, 10, 5),(34, 10, 5),
(36, 10, 5),(38, 10, 5),(39, 10, 5),(41, 10, 5),(44, 10, 5),(47, 10, 5),(49, 10, 5),(50, 10, 5),(51, 10, 5),(54, 10, 5),(55, 10, 5),(58, 10, 5),
(63, 10, 5),(9, 0, 1),(13, 0, 2),(13, 1, 1),(13, 2, 2),(14, 13, 1),(16, 2, 0),(16, 9, 0),(16, 12, 0),(17, 0, 0),(17, 1, 0),(17, 13, 0),
(24, 1, 3),(24, 19, 3),(33, 17, 1),(33, 23, 1),(33, 24, 1),(34, 23, 2),(36, 12, 1),(36, 23, 0),(37, 9, 2),(37, 14, 2),(37, 17, 2),(37, 36, 2),
(38, 17, 0),(38, 19, 2),(38, 23, 2),(38, 23, 3),(38, 24, 2),(38, 24, 3),(38, 33, 1),(39, 9, 3),(39, 12, 2),(39, 13, 2),(39, 17, 0),(39, 33, 1),
(41, 17, 0),(41, 33, 1),(44, 16, 0),(44, 24, 2),(44, 34, 1),(47, 17, 0),(47, 24, 4),(47, 33, 1),(47, 37, 2),(49, 23, 0),(49, 33, 1),(49, 41, 2),
(50, 0, 4),(50, 9, 4),(50, 14, 4),(50, 19, 0),(50, 23, 0),(50, 23, 3),(50, 24, 0),(50, 33, 1),(50, 34, 0),(50, 37, 2),(50, 38, 3),(50, 39, 3),
(51, 2, 1),(51, 13, 2),(51, 19, 4),(51, 23, 3),(51, 50, 0),(54, 1, 4),(54, 13, 1),(54, 16, 0),(54, 23, 3),(54, 37, 2),(54, 50, 4),(55, 1, 2),
(55, 13, 1),(55, 13, 2),(55, 19, 1),(55, 23, 3),(55, 47, 4),(55, 50, 0),(58, 13, 1),(58, 14, 0),(58, 37, 2),(58, 54, 3),(60, 0, 3),(60, 2, 3),
(60, 12, 3),(60, 13, 3),(60, 14, 3),(60, 17, 3),(60, 34, 3),(60, 36, 3),(60, 44, 3),(60, 47, 3),(63, 13, 4),(63, 16, 0),(63, 23, 3),(63, 33, 1),
(63, 37, 2),(63, 38, 3),(63, 41, 3),(63, 49, 3),(65, 2, 4),(65, 12, 4),(65, 17, 4),(65, 23, 4),(65, 34, 4),(65, 36, 4),(65, 38, 4),(65, 39, 4),
(65, 41, 4),(65, 44, 4),(65, 49, 4),(65, 58, 4)
]
def p : List Nat := [
0,1,2,9,12,13,14,17,19,23,24,34,
36,38,39,41,44,47,49,50,51,54,55,58,
63
]
def units : List Point := [
(16, 0),(33, 1),(37, 2),(60, 3),(65, 4),(10, 5)
]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem valid : n.all checked=true ∧ assemble n p units=clauses := by decide +kernel
theorem forbidden (f : Nat → Fin 6) (ok : proper f) : ¬ ∀ a∈units,(f a.1).val=a.2 := by
  intro h
  apply impossible
  rw [←valid.2]
  exact allocated f ok n p units valid.1 h
end Branch2
namespace Branch3
set_option maxRecDepth 32768 in
def n : List Edge := [
(14, 0, 5),(14, 1, 5),(14, 2, 5),(14, 9, 5),(14, 12, 5),(14, 13, 5),(17, 14, 5),(19, 14, 5),(23, 14, 5),(24, 14, 5),(34, 14, 5),(36, 14, 5),
(38, 14, 5),(39, 14, 5),(41, 14, 5),(44, 14, 5),(47, 14, 5),(49, 14, 5),(50, 14, 5),(51, 14, 5),(54, 14, 5),(55, 14, 5),(63, 14, 5),(9, 0, 1),
(13, 0, 1),(13, 0, 2),(13, 1, 1),(13, 2, 2),(16, 2, 0),(16, 9, 0),(16, 12, 0),(17, 0, 0),(17, 1, 0),(17, 13, 0),(23, 0, 2),(24, 1, 3),
(24, 19, 3),(33, 17, 1),(33, 23, 1),(33, 24, 1),(34, 23, 2),(36, 12, 1),(36, 13, 1),(36, 23, 0),(37, 9, 2),(37, 17, 2),(37, 36, 2),(38, 17, 0),
(38, 19, 2),(38, 23, 2),(38, 23, 3),(38, 24, 2),(38, 24, 3),(38, 33, 1),(39, 9, 3),(39, 12, 2),(39, 13, 2),(39, 17, 0),(39, 33, 1),(41, 17, 0),
(41, 33, 1),(44, 16, 0),(44, 24, 2),(44, 34, 1),(47, 17, 0),(47, 24, 4),(47, 33, 1),(47, 37, 2),(49, 23, 0),(49, 33, 1),(49, 41, 2),(50, 0, 4),
(50, 9, 4),(50, 19, 0),(50, 23, 0),(50, 23, 3),(50, 24, 0),(50, 33, 1),(50, 34, 0),(50, 37, 2),(50, 38, 3),(50, 39, 3),(51, 2, 1),(51, 13, 2),
(51, 19, 4),(51, 23, 3),(51, 50, 0),(54, 1, 4),(54, 13, 1),(54, 16, 0),(54, 23, 3),(54, 37, 2),(54, 50, 4),(55, 1, 2),(55, 13, 1),(55, 13, 2),
(55, 19, 1),(55, 23, 3),(55, 47, 4),(55, 50, 0),(60, 0, 3),(60, 2, 3),(60, 12, 3),(60, 13, 3),(60, 17, 3),(60, 34, 3),(60, 36, 3),(60, 44, 3),
(60, 47, 3),(63, 13, 4),(63, 16, 0),(63, 23, 3),(63, 33, 1),(63, 37, 2),(63, 38, 3),(63, 41, 3),(63, 49, 3),(65, 2, 4),(65, 12, 4),(65, 17, 4),
(65, 23, 4),(65, 34, 4),(65, 36, 4),(65, 38, 4),(65, 39, 4),(65, 41, 4),(65, 44, 4),(65, 49, 4)
]
def p : List Nat := [
0,1,2,9,12,13,17,19,23,24,34,36,
38,39,41,44,47,49,50,51,54,55,63
]
def units : List Point := [
(16, 0),(33, 1),(37, 2),(60, 3),(65, 4),(14, 5)
]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem valid : n.all checked=true ∧ assemble n p units=clauses := by decide +kernel
theorem forbidden (f : Nat → Fin 6) (ok : proper f) : ¬ ∀ a∈units,(f a.1).val=a.2 := by
  intro h
  apply impossible
  rw [←valid.2]
  exact allocated f ok n p units valid.1 h
end Branch3
namespace Branch4
set_option maxRecDepth 32768 in
def n : List Edge := [
(51, 0, 5),(51, 1, 5),(51, 2, 5),(51, 9, 5),(51, 12, 5),(51, 13, 5),(51, 14, 5),(51, 17, 5),(51, 19, 5),(51, 23, 5),(51, 24, 5),(51, 34, 5),
(51, 36, 5),(51, 38, 5),(51, 39, 5),(51, 41, 5),(51, 44, 5),(51, 47, 5),(51, 49, 5),(51, 50, 5),(54, 51, 5),(55, 51, 5),(58, 51, 5),(63, 51, 5),
(9, 0, 1),(13, 0, 2),(13, 1, 1),(13, 2, 2),(14, 2, 1),(14, 13, 1),(16, 2, 0),(16, 9, 0),(16, 12, 0),(17, 0, 0),(17, 1, 0),(17, 13, 0),
(19, 14, 4),(24, 1, 3),(24, 19, 3),(33, 17, 1),(33, 23, 1),(33, 24, 1),(34, 23, 2),(36, 12, 1),(36, 23, 0),(37, 9, 2),(37, 14, 2),(37, 17, 2),
(37, 36, 2),(38, 17, 0),(38, 19, 2),(38, 23, 2),(38, 23, 3),(38, 24, 2),(38, 24, 3),(38, 33, 1),(39, 9, 3),(39, 12, 2),(39, 13, 2),(39, 17, 0),
(39, 33, 1),(41, 17, 0),(41, 33, 1),(44, 16, 0),(44, 24, 2),(44, 34, 1),(47, 17, 0),(47, 24, 4),(47, 33, 1),(47, 37, 2),(49, 23, 0),(49, 33, 1),
(49, 41, 2),(50, 0, 4),(50, 9, 4),(50, 14, 0),(50, 14, 4),(50, 19, 0),(50, 23, 0),(50, 23, 3),(50, 24, 0),(50, 33, 1),(50, 34, 0),(50, 37, 2),
(50, 38, 3),(50, 39, 3),(54, 1, 4),(54, 13, 1),(54, 16, 0),(54, 23, 3),(54, 37, 2),(54, 50, 4),(55, 1, 2),(55, 13, 1),(55, 13, 2),(55, 19, 1),
(55, 23, 3),(55, 47, 4),(55, 50, 0),(58, 13, 1),(58, 14, 0),(58, 37, 2),(58, 54, 3),(60, 0, 3),(60, 2, 3),(60, 12, 3),(60, 13, 3),(60, 14, 3),
(60, 17, 3),(60, 34, 3),(60, 36, 3),(60, 44, 3),(60, 47, 3),(63, 13, 4),(63, 16, 0),(63, 23, 3),(63, 33, 1),(63, 37, 2),(63, 38, 3),(63, 41, 3),
(63, 49, 3),(65, 2, 4),(65, 12, 4),(65, 17, 4),(65, 23, 4),(65, 34, 4),(65, 36, 4),(65, 38, 4),(65, 39, 4),(65, 41, 4),(65, 44, 4),(65, 49, 4),
(65, 58, 4)
]
def p : List Nat := [
0,1,2,9,12,13,14,17,19,23,24,34,
36,38,39,41,44,47,49,50,54,55,58,63
]
def units : List Point := [
(16, 0),(33, 1),(37, 2),(60, 3),(65, 4),(51, 5)
]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem valid : n.all checked=true ∧ assemble n p units=clauses := by decide +kernel
theorem forbidden (f : Nat → Fin 6) (ok : proper f) : ¬ ∀ a∈units,(f a.1).val=a.2 := by
  intro h
  apply impossible
  rw [←valid.2]
  exact allocated f ok n p units valid.1 h
end Branch4
namespace Branch5
set_option maxRecDepth 32768 in
def n : List Edge := [
(58, 0, 5),(58, 1, 5),(58, 2, 5),(58, 9, 5),(58, 12, 5),(58, 13, 5),(58, 14, 5),(58, 17, 5),(58, 19, 5),(58, 23, 5),(58, 24, 5),(58, 34, 5),
(58, 36, 5),(58, 38, 5),(58, 39, 5),(58, 41, 5),(58, 44, 5),(58, 47, 5),(58, 49, 5),(58, 50, 5),(58, 51, 5),(58, 54, 5),(58, 55, 5),(63, 58, 5),
(9, 0, 1),(13, 0, 1),(13, 0, 2),(13, 1, 1),(13, 2, 2),(14, 13, 1),(16, 2, 0),(16, 9, 0),(16, 12, 0),(17, 0, 0),(17, 1, 0),(17, 13, 0),
(19, 0, 2),(19, 13, 1),(19, 14, 0),(24, 1, 3),(24, 19, 3),(33, 17, 1),(33, 23, 1),(33, 24, 1),(34, 23, 2),(36, 12, 1),(36, 23, 0),(37, 9, 2),
(37, 14, 2),(37, 17, 2),(37, 36, 2),(38, 17, 0),(38, 19, 2),(38, 23, 2),(38, 23, 3),(38, 24, 2),(38, 24, 3),(38, 33, 1),(39, 9, 3),(39, 12, 2),
(39, 13, 2),(39, 17, 0),(39, 33, 1),(41, 17, 0),(41, 33, 1),(44, 16, 0),(44, 24, 2),(44, 34, 1),(47, 17, 0),(47, 24, 4),(47, 33, 1),(47, 37, 2),
(49, 23, 0),(49, 33, 1),(49, 41, 2),(50, 0, 4),(50, 9, 4),(50, 14, 4),(50, 19, 0),(50, 19, 4),(50, 23, 0),(50, 23, 3),(50, 24, 0),(50, 33, 1),
(50, 34, 0),(50, 37, 2),(50, 38, 3),(50, 39, 3),(51, 2, 1),(51, 13, 2),(51, 19, 4),(51, 23, 3),(51, 50, 0),(54, 1, 4),(54, 13, 1),(54, 16, 0),
(54, 19, 3),(54, 23, 3),(54, 37, 2),(54, 50, 4),(55, 1, 2),(55, 13, 1),(55, 13, 2),(55, 19, 1),(55, 23, 3),(55, 47, 4),(55, 50, 0),(60, 0, 3),
(60, 2, 3),(60, 12, 3),(60, 13, 3),(60, 14, 3),(60, 17, 3),(60, 34, 3),(60, 36, 3),(60, 44, 3),(60, 47, 3),(63, 13, 4),(63, 16, 0),(63, 23, 3),
(63, 33, 1),(63, 37, 2),(63, 38, 3),(63, 41, 3),(63, 49, 3),(65, 2, 4),(65, 12, 4),(65, 17, 4),(65, 23, 4),(65, 34, 4),(65, 36, 4),(65, 38, 4),
(65, 39, 4),(65, 41, 4),(65, 44, 4),(65, 49, 4)
]
def p : List Nat := [
0,1,2,9,12,13,14,17,19,23,24,34,
36,38,39,41,44,47,49,50,51,54,55,63
]
def units : List Point := [
(16, 0),(33, 1),(37, 2),(60, 3),(65, 4),(58, 5)
]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem valid : n.all checked=true ∧ assemble n p units=clauses := by decide +kernel
theorem forbidden (f : Nat → Fin 6) (ok : proper f) : ¬ ∀ a∈units,(f a.1).val=a.2 := by
  intro h
  apply impossible
  rw [←valid.2]
  exact allocated f ok n p units valid.1 h
end Branch5
end ProjectiveSharp
