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
structure Later (prev : List Nat) (chosen : Nat → Bool) (region : Nat → Prop) : Prop where
  exclusive : ∀ x, AllOn chosen (labels x) → region x
  upper : ∀ x, region x → AnyOn chosen (labels x) ∨ (∃ i∈labels x, i∈prev)
  closed : ∀ x y z, region x → region y → region z → region (x ^^^ y ^^^ z)
  normal : ∃ v : Nat → Bool, (∀ x y, v (x ^^^ y)=Bool.xor (v x) (v y)) ∧ v 0=false ∧
    (∃ i<12, v (1 <<< i)=true) ∧ (∀ x y, region x → region y → v x=v y)

theorem later_span {prev chosen region} (O : Later prev chosen region) {w : Span}
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

structure Case where
  prior : List Nat
  off : List Nat
  spans : List Span
  trip : List Tri
  groups : List Group

def caseFormula (b : Case) :=
  ((b.off.map (fun i => negs [i]) ++ b.spans.map spanClause) ++ b.trip.map triClause) ++ b.groups.map exactClause

def validTri (prev : List Nat) (t : Tri) := triGood t && t.hi.all (fun i => !prev.contains i)
def caseGood (b : Case) := ((sub b.off b.prior && b.spans.all spanGood) && b.trip.all (validTri b.prior))

theorem later_tri {prev chosen region} (O : Later prev chosen region) {t : Tri}
    (H : validTri prev t=true) (J : AllOn chosen t.lo) : AnyOn chosen t.hi := by
  simp only [validTri,Bool.and_eq_true] at H
  obtain ⟨tr,sep⟩ := H
  simp only [triGood,Bool.and_eq_true] at tr
  have r {x : Nat} (h : sub (labels x) t.lo=true) : region x :=
    O.exclusive x (fun j hj => J j (sub_mem h hj))
  rcases O.upper _ (O.closed _ _ _ (r tr.1.1) (r tr.1.2) (r tr.2.1)) with yes | ⟨i,hi,hp⟩
  · obtain ⟨i,hi,onv⟩ := yes
    exact ⟨i,sub_mem tr.2.2 hi,onv⟩
  · have off := List.all_eq_true.mp sep _ (sub_mem tr.2.2 hi)
    simp at off
    exact False.elim (off hp)

theorem case_conclusion (b : Case) (valid : caseGood b=true) (impossible : ¬ FormulaSat (caseFormula b))
    {chosen region} (disj : ∀ i∈b.prior, chosen i=false) (O : Later b.prior chosen region) :
    ∃ g∈b.groups, Matches chosen g := by
  classical
  simp only [caseGood,Bool.and_eq_true] at valid
  by_contra h
  apply impossible
  refine ⟨chosen,?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hp | he
  · rcases List.mem_append.mp hp with hs | ht
    · rcases List.mem_append.mp hs with hd | hs
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hd
        apply reject_neg
        intro z
        have no := disj i (sub_mem valid.1.1 hi)
        have yes := z i (by simp)
        rw [no] at yes
        contradiction
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hs
        exact reject_neg _ _ (later_span O (List.all_eq_true.mp valid.1.2 _ hw))
    · obtain ⟨t,hw,rfl⟩ := List.mem_map.mp ht
      apply clause_or
      by_cases yes : AllOn chosen t.lo
      · exact Or.inr (accept_pos _ _ (later_tri O (List.all_eq_true.mp valid.2 _ hw) yes))
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
def g0 : Group := ⟨[],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g1 : Group := ⟨[1],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g2 : Group := ⟨[2],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g4 : Group := ⟨[3],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g8 : Group := ⟨[4],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g16 : Group := ⟨[5],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g17 : Group := ⟨[1, 5],[2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g18 : Group := ⟨[2, 5],[1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g32 : Group := ⟨[6],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g48 : Group := ⟨[5, 6],[1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g49 : Group := ⟨[1, 5, 6],[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g64 : Group := ⟨[7],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g80 : Group := ⟨[5, 7],[1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g96 : Group := ⟨[6, 7],[1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g128 : Group := ⟨[8],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g129 : Group := ⟨[1, 8],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g144 : Group := ⟨[5, 8],[1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g160 : Group := ⟨[6, 8],[1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g161 : Group := ⟨[1, 6, 8],[2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g176 : Group := ⟨[5, 6, 8],[1, 2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g192 : Group := ⟨[7, 8],[1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g256 : Group := ⟨[9],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g272 : Group := ⟨[5, 9],[1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g274 : Group := ⟨[2, 5, 9],[1, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g288 : Group := ⟨[6, 9],[1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g320 : Group := ⟨[7, 9],[1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g322 : Group := ⟨[2, 7, 9],[1, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g336 : Group := ⟨[5, 7, 9],[1, 2, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g338 : Group := ⟨[2, 5, 7, 9],[1, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g384 : Group := ⟨[8, 9],[1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g448 : Group := ⟨[7, 8, 9],[1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g480 : Group := ⟨[6, 7, 8, 9],[1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g512 : Group := ⟨[10],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g516 : Group := ⟨[3, 10],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g520 : Group := ⟨[4, 10],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g528 : Group := ⟨[5, 10],[1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g544 : Group := ⟨[6, 10],[1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g548 : Group := ⟨[3, 6, 10],[1, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g576 : Group := ⟨[7, 10],[1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g580 : Group := ⟨[3, 7, 10],[1, 2, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g608 : Group := ⟨[6, 7, 10],[1, 2, 3, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g612 : Group := ⟨[3, 6, 7, 10],[1, 2, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g640 : Group := ⟨[8, 10],[1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g704 : Group := ⟨[7, 8, 10],[1, 2, 3, 4, 5, 6, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g720 : Group := ⟨[5, 7, 8, 10],[1, 2, 3, 4, 6, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g768 : Group := ⟨[9, 10],[1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g776 : Group := ⟨[4, 9, 10],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g800 : Group := ⟨[6, 9, 10],[1, 2, 3, 4, 5, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g816 : Group := ⟨[5, 6, 9, 10],[1, 2, 3, 4, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g896 : Group := ⟨[8, 9, 10],[1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g904 : Group := ⟨[4, 8, 9, 10],[1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g1024 : Group := ⟨[11],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g1040 : Group := ⟨[5, 11],[1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g2048 : Group := ⟨[12],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g2080 : Group := ⟨[6, 12],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g3072 : Group := ⟨[11, 12],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g4096 : Group := ⟨[13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g4160 : Group := ⟨[7, 13],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g5120 : Group := ⟨[11, 13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g6144 : Group := ⟨[12, 13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g8192 : Group := ⟨[14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g8320 : Group := ⟨[8, 14],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g9216 : Group := ⟨[11, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g10240 : Group := ⟨[12, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g10241 : Group := ⟨[1, 12, 14],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g10401 : Group := ⟨[1, 6, 8, 12, 14],[2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g11264 : Group := ⟨[11, 12, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g11265 : Group := ⟨[1, 11, 12, 14],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g11281 : Group := ⟨[1, 5, 11, 12, 14],[2, 3, 4, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g11313 : Group := ⟨[1, 5, 6, 11, 12, 14],[2, 3, 4, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g11393 : Group := ⟨[1, 8, 11, 12, 14],[2, 3, 4, 5, 6, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g11425 : Group := ⟨[1, 6, 8, 11, 12, 14],[2, 3, 4, 5, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g11440 : Group := ⟨[5, 6, 8, 11, 12, 14],[1, 2, 3, 4, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g12288 : Group := ⟨[13, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22]⟩
def g16384 : Group := ⟨[15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g16640 : Group := ⟨[9, 15],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g17408 : Group := ⟨[11, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g18432 : Group := ⟨[12, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g20480 : Group := ⟨[13, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g20482 : Group := ⟨[2, 13, 15],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g20802 : Group := ⟨[2, 7, 9, 13, 15],[1, 3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g21504 : Group := ⟨[11, 13, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g21506 : Group := ⟨[2, 11, 13, 15],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g21522 : Group := ⟨[2, 5, 11, 13, 15],[1, 3, 4, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g21778 : Group := ⟨[2, 5, 9, 11, 13, 15],[1, 3, 4, 6, 7, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g21826 : Group := ⟨[2, 7, 9, 11, 13, 15],[1, 3, 4, 5, 6, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g21842 : Group := ⟨[2, 5, 7, 9, 11, 13, 15],[1, 3, 4, 6, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩
def g24576 : Group := ⟨[14, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22]⟩
def g30720 : Group := ⟨[12, 13, 14, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22]⟩
def g32768 : Group := ⟨[16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g33280 : Group := ⟨[10, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g33792 : Group := ⟨[11, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g34816 : Group := ⟨[12, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g36864 : Group := ⟨[13, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g36868 : Group := ⟨[3, 13, 16],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g37444 : Group := ⟨[3, 7, 10, 13, 16],[1, 2, 4, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g38912 : Group := ⟨[12, 13, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g38916 : Group := ⟨[3, 12, 13, 16],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g39428 : Group := ⟨[3, 10, 12, 13, 16],[1, 2, 4, 5, 6, 7, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g39460 : Group := ⟨[3, 6, 10, 12, 13, 16],[1, 2, 4, 5, 7, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g39492 : Group := ⟨[3, 7, 10, 12, 13, 16],[1, 2, 4, 5, 6, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g39524 : Group := ⟨[3, 6, 7, 10, 12, 13, 16],[1, 2, 4, 5, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩
def g40960 : Group := ⟨[14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22]⟩
def g45056 : Group := ⟨[13, 14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 17, 18, 19, 20, 21, 22]⟩
def g46080 : Group := ⟨[11, 13, 14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 17, 18, 19, 20, 21, 22]⟩
def g49152 : Group := ⟨[15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩
def g49160 : Group := ⟨[4, 15, 16],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩
def g49928 : Group := ⟨[4, 9, 10, 15, 16],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩
def g51200 : Group := ⟨[12, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 17, 18, 19, 20, 21, 22]⟩
def g52224 : Group := ⟨[11, 12, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 22]⟩
def g57344 : Group := ⟨[14, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩
def g57352 : Group := ⟨[4, 14, 15, 16],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩
def g57864 : Group := ⟨[4, 10, 14, 15, 16],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩
def g58120 : Group := ⟨[4, 9, 10, 14, 15, 16],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩
def g58248 : Group := ⟨[4, 8, 9, 10, 14, 15, 16],[1, 2, 3, 5, 6, 7, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩
def g65536 : Group := ⟨[17],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩
def g65552 : Group := ⟨[5, 17],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩
def g66560 : Group := ⟨[11, 17],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩
def g66576 : Group := ⟨[5, 11, 17],[1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩
def g131072 : Group := ⟨[18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩
def g131104 : Group := ⟨[6, 18],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩
def g133120 : Group := ⟨[12, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩
def g133152 : Group := ⟨[6, 12, 18],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩
def g196608 : Group := ⟨[17, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22]⟩
def g262144 : Group := ⟨[19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22]⟩
def g262208 : Group := ⟨[7, 19],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22]⟩
def g266240 : Group := ⟨[13, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22]⟩
def g266304 : Group := ⟨[7, 13, 19],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22]⟩
def g327680 : Group := ⟨[17, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22]⟩
def g393216 : Group := ⟨[18, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 22]⟩
def g524288 : Group := ⟨[20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩
def g524416 : Group := ⟨[8, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩
def g532480 : Group := ⟨[14, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩
def g532608 : Group := ⟨[8, 14, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩
def g589824 : Group := ⟨[17, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 21, 22]⟩
def g655360 : Group := ⟨[18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩
def g655361 : Group := ⟨[1, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩
def g655521 : Group := ⟨[1, 6, 8, 18, 20],[2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩
def g665601 : Group := ⟨[1, 12, 14, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩
def g665761 : Group := ⟨[1, 6, 8, 12, 14, 18, 20],[2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩
def g720896 : Group := ⟨[17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩
def g720897 : Group := ⟨[1, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩
def g720913 : Group := ⟨[1, 5, 17, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩
def g720945 : Group := ⟨[1, 5, 6, 17, 18, 20],[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩
def g721025 : Group := ⟨[1, 8, 17, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩
def g721057 : Group := ⟨[1, 6, 8, 17, 18, 20],[2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩
def g721072 : Group := ⟨[5, 6, 8, 17, 18, 20],[1, 2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩
def g731137 : Group := ⟨[1, 12, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩
def g731297 : Group := ⟨[1, 6, 8, 12, 14, 17, 18, 20],[2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩
def g732160 : Group := ⟨[11, 12, 14, 17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩
def g732161 : Group := ⟨[1, 11, 12, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩
def g732177 : Group := ⟨[1, 5, 11, 12, 14, 17, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩
def g732209 : Group := ⟨[1, 5, 6, 11, 12, 14, 17, 18, 20],[2, 3, 4, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩
def g732289 : Group := ⟨[1, 8, 11, 12, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩
def g732321 : Group := ⟨[1, 6, 8, 11, 12, 14, 17, 18, 20],[2, 3, 4, 5, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩
def g732336 : Group := ⟨[5, 6, 8, 11, 12, 14, 17, 18, 20],[1, 2, 3, 4, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩
def g786432 : Group := ⟨[19, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22]⟩
def g1048576 : Group := ⟨[21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩
def g1048832 : Group := ⟨[9, 21],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩
def g1064960 : Group := ⟨[15, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩
def g1065216 : Group := ⟨[9, 15, 21],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩
def g1114112 : Group := ⟨[17, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 22]⟩
def g1179648 : Group := ⟨[18, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 22]⟩
def g1310720 : Group := ⟨[19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩
def g1310722 : Group := ⟨[2, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩
def g1311042 : Group := ⟨[2, 7, 9, 19, 21],[1, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩
def g1331202 : Group := ⟨[2, 13, 15, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩
def g1331522 : Group := ⟨[2, 7, 9, 13, 15, 19, 21],[1, 3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩
def g1376256 : Group := ⟨[17, 19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩
def g1376258 : Group := ⟨[2, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩
def g1376274 : Group := ⟨[2, 5, 17, 19, 21],[1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩
def g1376530 : Group := ⟨[2, 5, 9, 17, 19, 21],[1, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩
def g1376578 : Group := ⟨[2, 7, 9, 17, 19, 21],[1, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩
def g1376594 : Group := ⟨[2, 5, 7, 9, 17, 19, 21],[1, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩
def g1396738 : Group := ⟨[2, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 22]⟩
def g1397058 : Group := ⟨[2, 7, 9, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 18, 20, 22]⟩
def g1397762 : Group := ⟨[2, 11, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22]⟩
def g1397778 : Group := ⟨[2, 5, 11, 13, 15, 17, 19, 21],[1, 3, 4, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22]⟩
def g1398034 : Group := ⟨[2, 5, 9, 11, 13, 15, 17, 19, 21],[1, 3, 4, 6, 7, 8, 10, 12, 14, 16, 18, 20, 22]⟩
def g1398082 : Group := ⟨[2, 7, 9, 11, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20, 22]⟩
def g1398098 : Group := ⟨[2, 5, 7, 9, 11, 13, 15, 17, 19, 21],[1, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22]⟩
def g1572864 : Group := ⟨[20, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22]⟩
def g1966080 : Group := ⟨[18, 19, 20, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 22]⟩
def g2097152 : Group := ⟨[22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩
def g2097664 : Group := ⟨[10, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩
def g2129920 : Group := ⟨[16, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩
def g2130432 : Group := ⟨[10, 16, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩
def g2162688 : Group := ⟨[17, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21]⟩
def g2228224 : Group := ⟨[18, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21]⟩
def g2359296 : Group := ⟨[19, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩
def g2359300 : Group := ⟨[3, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩
def g2359876 : Group := ⟨[3, 7, 10, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩
def g2396164 : Group := ⟨[3, 13, 16, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 18, 20, 21]⟩
def g2396740 : Group := ⟨[3, 7, 10, 13, 16, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18, 20, 21]⟩
def g2490368 : Group := ⟨[18, 19, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩
def g2490372 : Group := ⟨[3, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩
def g2490884 : Group := ⟨[3, 10, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩
def g2490916 : Group := ⟨[3, 6, 10, 18, 19, 22],[1, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩
def g2490948 : Group := ⟨[3, 7, 10, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩
def g2490980 : Group := ⟨[3, 6, 7, 10, 18, 19, 22],[1, 2, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩
def g2527236 : Group := ⟨[3, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 20, 21]⟩
def g2527812 : Group := ⟨[3, 7, 10, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 12, 14, 15, 17, 20, 21]⟩
def g2529284 : Group := ⟨[3, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 20, 21]⟩
def g2529796 : Group := ⟨[3, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 14, 15, 17, 20, 21]⟩
def g2529828 : Group := ⟨[3, 6, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 7, 8, 9, 11, 14, 15, 17, 20, 21]⟩
def g2529860 : Group := ⟨[3, 7, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 14, 15, 17, 20, 21]⟩
def g2529892 : Group := ⟨[3, 6, 7, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 8, 9, 11, 14, 15, 17, 20, 21]⟩
def g2621440 : Group := ⟨[20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21]⟩
def g2883584 : Group := ⟨[19, 20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21]⟩
def g2949120 : Group := ⟨[17, 19, 20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21]⟩
def g3145728 : Group := ⟨[21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩
def g3145736 : Group := ⟨[4, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩
def g3146504 : Group := ⟨[4, 9, 10, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩
def g3194888 : Group := ⟨[4, 15, 16, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20]⟩
def g3195656 : Group := ⟨[4, 9, 10, 15, 16, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 19, 20]⟩
def g3276800 : Group := ⟨[18, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20]⟩
def g3342336 : Group := ⟨[17, 18, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20]⟩
def g3670016 : Group := ⟨[20, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩
def g3670024 : Group := ⟨[4, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩
def g3670536 : Group := ⟨[4, 10, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩
def g3670792 : Group := ⟨[4, 9, 10, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩
def g3670920 : Group := ⟨[4, 8, 9, 10, 20, 21, 22],[1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩
def g3719176 : Group := ⟨[4, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19]⟩
def g3719944 : Group := ⟨[4, 9, 10, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 19]⟩
def g3727368 : Group := ⟨[4, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19]⟩
def g3727880 : Group := ⟨[4, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 17, 18, 19]⟩
def g3728136 : Group := ⟨[4, 9, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 17, 18, 19]⟩
def g3728264 : Group := ⟨[4, 8, 9, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 11, 12, 13, 17, 18, 19]⟩
def s0 : Span := ⟨[1, 2],640,[[1280, 1281], [768, 770], [644], [1280, 1288], [768, 784], [672], [896, 1088, 1280], [768, 896], [896], [1280, 1792], [768, 1792], [768, 1088, 1792, 2112]]⟩
def s1 : Span := ⟨[1, 3],528,[[1056, 1057], [544, 546], [532], [560, 1032, 1056], [544, 560], [560], [1056, 1120], [544, 672], [784], [1056, 1568], [544, 1568], [544, 1032, 1568, 2056]]⟩
def s2 : Span := ⟨[2, 3],514,[[518, 1025, 1028], [516, 518], [518], [1028, 1036], [516, 532], [546], [1028, 1092], [516, 644], [770], [1028, 1540], [516, 1540], [516, 1025, 1540, 2049]]⟩
def s3 : Span := ⟨[1, 4],80,[[160, 161], [96, 98], [84], [112, 136, 160], [96, 112], [112], [160, 224], [96, 224], [96, 136, 224, 264], [160, 672], [96, 1120], [2128]]⟩
def s4 : Span := ⟨[2, 4],66,[[70, 129, 132], [68, 70], [70], [132, 140], [68, 84], [98], [132, 196], [68, 196], [68, 129, 196, 257], [132, 644], [68, 1092], [2114]]⟩
def s5 : Span := ⟨[3, 4],10,[[14, 17, 20], [12, 14], [14], [20, 28], [12, 28], [12, 17, 28, 33], [20, 84], [12, 140], [266], [20, 532], [12, 1036], [2058]]⟩
def s6 : Span := ⟨[2, 5, 6],644,[[1092, 1093], [1092, 1093, 2113, 2114], [1089, 1093], [1281, 1289], [2113, 2129], [1089, 1121], [1281, 1345], [770, 1092, 1345, 2113, 2114], [1089, 1345], [770, 1281, 2114, 3137], [2113, 3137], [1089, 3137]]⟩
def s7 : Span := ⟨[3, 5, 6],532,[[1036, 1037], [1036, 1037, 2057, 2058], [1033, 1037], [1057, 1065], [546, 1036, 1065, 2057, 2058], [1033, 1065], [1057, 1121], [2057, 2185], [1033, 1289], [546, 1057, 2058, 3081], [2057, 3081], [1033, 3081]]⟩
def s22 : Span := ⟨[4, 5, 9],84,[[140, 141], [140, 141, 265, 266], [137, 141], [161, 169], [98, 140, 169, 265, 266], [137, 169], [98, 161, 266, 393], [265, 393], [137, 393], [140, 652], [265, 1289], [137, 2185]]⟩
def s24 : Span := ⟨[2, 6, 9],644,[[1092, 1093], [1092, 1093, 2113, 2114], [1089, 1093], [652], [2113, 2129], [1089, 1121], [1281, 1345], [770, 1092, 1345, 2113, 2114], [1089, 1345], [770, 1281, 2114, 3137], [2113, 3137], [1089, 3137]]⟩
def s26 : Span := ⟨[4, 6, 9],81,[[84, 85], [84, 85, 97, 98], [85], [84, 113, 140, 161], [97, 113], [113], [161, 225], [97, 225], [84, 98, 140, 225, 266], [140, 652], [97, 1121], [2129]]⟩
def s28 : Span := ⟨[4, 7, 9],74,[[78, 98, 140, 161], [76, 78], [78], [84, 92], [76, 92], [84, 92, 98], [140, 204], [76, 204], [140, 204, 266], [140, 652], [76, 1100], [2122]]⟩
def s31 : Span := ⟨[2, 8, 9],641,[[644, 645], [644, 645, 769, 770], [645], [644, 652], [769, 785], [673], [644, 897, 1092, 1281], [769, 897], [897], [1281, 1793], [769, 1793], [644, 770, 1092, 1793, 2114]]⟩
def s44 : Span := ⟨[3, 8, 10],529,[[532, 533], [532, 533, 545, 546], [533], [532, 561, 1036, 1057], [545, 561], [561], [532, 596], [545, 673], [785], [1057, 1569], [545, 1569], [532, 546, 1036, 1569, 2058]]⟩
def s47 : Span := ⟨[2, 9, 10],578,[[582, 770, 1092, 1281], [580, 582], [582], [644, 652], [580, 596], [610], [644, 708], [580, 708], [644, 708, 770], [1092, 1604], [580, 1604], [1092, 1604, 2114]]⟩
def s50 : Span := ⟨[6, 7, 9, 10],586,[[590, 610, 1100, 1121], [588, 590], [590], [596, 604], [588, 604], [596, 604, 610], [652, 716], [588, 716], [652, 716, 778], [1100, 1612], [588, 1612], [1100, 1612, 2122]]⟩
def s55 : Span := ⟨[4, 5, 11],82,[[86, 137, 140], [84, 86], [86], [114, 137, 161], [98, 114], [114], [84, 98, 140, 161, 265, 338], [137, 265, 338], [338], [84, 98, 140, 161, 265, 786], [265, 1289], [2130]]⟩
def s82 : Span := ⟨[2, 11, 12],642,[[646, 770, 1092, 1281, 2114, 2178], [644, 646], [646], [2178, 2186], [770, 786], [674], [770, 898, 2114, 2178], [770, 898], [898], [2178, 2690], [644, 1092, 2114, 2690], [2690]]⟩
def s83 : Span := ⟨[3, 11, 12],530,[[534, 546, 1036, 1057, 2058, 2066], [532, 534], [534], [546, 562, 2058, 2066], [546, 562], [562], [2066, 2130], [546, 674], [786], [2066, 2578], [532, 1036, 2058, 2578], [2578]]⟩
def s103 : Span := ⟨[3, 11, 13],530,[[534, 546, 1036, 1057, 2058, 2066], [532, 534], [534], [546, 562, 2058, 2066], [546, 562], [562], [2066, 2130], [532, 660], [786], [2066, 2578], [532, 1036, 2058, 2578], [2578]]⟩
def s108 : Span := ⟨[1, 12, 13],656,[[2192, 2193], [672, 674], [660], [688, 784, 1120, 1288, 2128, 2192], [672, 688], [688], [784, 912, 2128, 2192], [784, 912], [912], [2192, 2704], [672, 1120, 2128, 2704], [2704]]⟩
def s131 : Span := ⟨[2, 11, 14],644,[[1092, 1094, 1281, 1282], [1092, 1094], [1090, 1094], [1282, 1290], [770, 786], [1090, 1122], [1282, 1346], [770, 1092, 1346], [1090, 1346], [1282, 1794], [770, 1794], [770, 1090, 1794, 2114]]⟩
def s132 : Span := ⟨[4, 11, 14],82,[[86, 98, 140, 161, 266, 274], [84, 86], [86], [98, 114, 266, 274], [98, 114], [114], [274, 338], [84, 140, 266, 338], [338], [274, 786], [98, 1122], [2130]]⟩
def s137 : Span := ⟨[3, 12, 14],532,[[1036, 1038, 1057, 1058], [1036, 1038], [1034, 1038], [1058, 1066], [546, 1036, 1066], [1034, 1066], [1058, 1122], [546, 674], [1034, 1290], [1058, 1570], [546, 1570], [546, 1034, 1570, 2058]]⟩
def s138 : Span := ⟨[4, 12, 14],84,[[140, 142, 161, 162], [140, 142], [138, 142], [162, 170], [98, 140, 170], [138, 170], [162, 226], [98, 226], [98, 138, 226, 266], [162, 674], [98, 1122], [138, 2186]]⟩
def s146 : Span := ⟨[4, 13, 14],84,[[148, 149], [98, 149, 161], [145, 149], [148, 156], [140, 156], [140, 145, 156, 161], [148, 212], [212], [98, 140, 145, 161, 212, 266], [148, 660], [98, 1122], [145, 2193]]⟩
def s162 : Span := ⟨[11, 12, 13, 14],658,[[660, 662, 2193, 2194], [660, 662], [662], [690, 786, 1122, 1290, 2130, 2194], [674, 690], [690], [786, 914, 2130, 2194], [786, 914], [914], [2194, 2706], [674, 1122, 2130, 2706], [2706]]⟩
def s177 : Span := ⟨[1, 11, 15],672,[[1296, 1297], [784, 786], [1104, 1108], [1120, 1136, 1288, 1296], [1120, 1136], [1104, 1136], [1296, 1360], [784, 1120, 1360], [1104, 1360], [1296, 1808], [784, 1808], [784, 1104, 1808, 2128]]⟩
def s178 : Span := ⟨[4, 11, 15],82,[[86, 98, 140, 161, 266, 274], [84, 86], [86], [98, 114, 266, 274], [98, 114], [114], [274, 338], [84, 140, 266, 338], [338], [274, 786], [84, 1108], [2130]]⟩
def s183 : Span := ⟨[1, 12, 15],672,[[1296, 1297], [674], [1104, 1108], [1120, 1136, 1288, 1296], [1120, 1136], [1104, 1136], [1296, 1360], [784, 1120, 1360], [1104, 1360], [1296, 1808], [784, 1808], [784, 1104, 1808, 2128]]⟩
def s184 : Span := ⟨[2, 12, 15],642,[[646, 770, 1092, 1281, 2114, 2178], [644, 646], [646], [2178, 2186], [1092, 1108], [674], [770, 898, 2114, 2178], [770, 898], [898], [2178, 2690], [644, 1092, 2114, 2690], [2690]]⟩
def s185 : Span := ⟨[3, 12, 15],532,[[1044, 1045], [546, 1045, 1057], [1041, 1045], [1044, 1052], [1036, 1052], [1036, 1041, 1052, 1057], [1044, 1108], [546, 674], [1041, 1297], [1044, 1556], [1556], [546, 1036, 1041, 1057, 1556, 2058]]⟩
def s186 : Span := ⟨[4, 12, 15],84,[[140, 142, 161, 162], [140, 142], [138, 142], [162, 170], [98, 140, 170], [138, 170], [162, 226], [98, 226], [98, 138, 226, 266], [162, 674], [1108], [138, 2186]]⟩
def s200 : Span := ⟨[4, 13, 15],84,[[148, 149], [98, 149, 161], [145, 149], [148, 156], [140, 156], [140, 145, 156, 161], [148, 212], [212], [98, 140, 145, 161, 212, 266], [148, 660], [1108], [145, 2193]]⟩
def s210 : Span := ⟨[2, 14, 15],644,[[1092, 1094, 1281, 1282], [1092, 1094], [1090, 1094], [1282, 1290], [1092, 1108], [1090, 1122], [1282, 1346], [770, 1092, 1346], [1090, 1346], [1282, 1794], [770, 1794], [770, 1090, 1794, 2114]]⟩
def s240 : Span := ⟨[1, 11, 16],672,[[1184, 1185], [784, 786], [1160, 1164], [1184, 1192], [784, 1192, 1288], [1160, 1192], [1184, 1248], [1120, 1248], [1120, 1160, 1248, 1288], [1184, 1696], [1696], [784, 1120, 1160, 1288, 1696, 2128]]⟩
def s242 : Span := ⟨[3, 11, 16],530,[[534, 546, 1036, 1057, 2058, 2066], [532, 534], [534], [546, 562, 2058, 2066], [546, 562], [562], [2066, 2130], [1036, 1164], [786], [2066, 2578], [532, 1036, 2058, 2578], [2578]]⟩
def s253 : Span := ⟨[1, 12, 16],672,[[1184, 1185], [674], [1160, 1164], [1184, 1192], [784, 1192, 1288], [1160, 1192], [1184, 1248], [1120, 1248], [1120, 1160, 1248, 1288], [1184, 1696], [1696], [784, 1120, 1160, 1288, 1696, 2128]]⟩
def s273 : Span := ⟨[3, 14, 16],532,[[1036, 1038, 1057, 1058], [1036, 1038], [1034, 1038], [1058, 1066], [546, 1036, 1066], [1034, 1066], [1058, 1122], [1036, 1164], [1034, 1290], [1058, 1570], [546, 1570], [546, 1034, 1570, 2058]]⟩
def s278 : Span := ⟨[5, 11, 14, 16],786,[[1164, 1165], [1164, 1165, 1289, 1290], [1161, 1165], [1185, 1193], [1122, 1193, 2130, 2185], [1161, 1193], [1122, 1185, 1290, 1417], [1289, 1417], [1161, 1417], [1122, 1185, 1290, 2130, 3209], [2185, 3209], [1161, 3209]]⟩
def s284 : Span := ⟨[11, 12, 14, 16],674,[[1164, 1166, 1185, 1186], [1164, 1166], [1162, 1166], [1186, 1194], [786, 1194, 1290], [1162, 1194], [1186, 1250], [1122, 1250], [1122, 1162, 1250, 1290], [1186, 1698], [1698], [786, 1122, 1162, 1290, 1698, 2130]]⟩
def s304 : Span := ⟨[11, 13, 15, 16],660,[[1172, 1173], [786, 1173, 1297], [1169, 1173], [1172, 1180], [1164, 1180], [1164, 1169, 1180, 1185], [1172, 1236], [1108, 1236], [1108, 1169, 1236, 1297], [1172, 1684], [1684], [786, 1108, 1169, 1297, 1684, 2130]]⟩
def s324 : Span := ⟨[4, 11, 17],82,[[86, 161, 164], [84, 86], [86], [114, 140, 164], [98, 114], [114], [164, 228], [84, 98, 228], [98, 140, 228, 266], [164, 676], [84, 98, 1124], [2130]]⟩
def s916 : Span := ⟨[1, 19, 20],672,[[1312, 1313], [800, 802], [2128, 2132], [784, 816, 1288, 1312], [800, 816], [784, 816], [928, 1120, 1312], [800, 928], [928], [1312, 1824], [800, 1824], [784, 1120, 1824, 2128]]⟩
def s917 : Span := ⟨[2, 19, 20],644,[[770, 1092, 1281, 2118, 2180], [2116, 2118], [2114, 2118], [2180, 2188], [2116, 2132], [770, 802], [2180, 2244], [2116, 2244], [770, 2114, 2244], [2180, 2692], [1092, 2116, 2692], [2692]]⟩
def s989 : Span := ⟨[1, 9, 21],648,[[784, 1120, 1288, 2128, 2209], [776, 778], [652], [672, 680], [672, 680, 776, 784], [680], [672, 904, 1120, 1288], [776, 904], [904], [1288, 1800], [776, 1800], [672, 784, 1120, 1800, 2128]]⟩
def s1031 : Span := ⟨[1, 15, 21],672,[[1296, 1297], [1104, 1120, 2128, 2146], [1104, 1108], [1120, 1136, 1288, 1296], [1120, 1136], [1104, 1136], [1296, 1360], [784, 1120, 1360], [1104, 1360], [1296, 1808], [784, 1808], [784, 1104, 1808, 2128]]⟩
def s1073 : Span := ⟨[1, 17, 21],672,[[2208, 2209], [2144, 2146], [676], [784, 1120, 1288, 2160, 2208], [2144, 2160], [2128, 2160], [2208, 2272], [2144, 2272], [784, 2128, 2272], [2208, 2720], [1120, 2144, 2720], [2720]]⟩
def s1122 : Span := ⟨[2, 18, 21],644,[[770, 774, 1281, 1284], [772, 774], [770, 774], [1284, 1292], [772, 788], [2114, 2146], [900, 1092, 1284], [772, 900], [900], [1284, 1796], [772, 1796], [770, 1092, 1796, 2114]]⟩
def s1247 : Span := ⟨[1, 20, 21],672,[[2208, 2209], [2144, 2146], [2128, 2132], [784, 1120, 1288, 2160, 2208], [2144, 2160], [2128, 2160], [2208, 2272], [2144, 2272], [784, 2128, 2272], [2208, 2720], [1120, 2144, 2720], [2720]]⟩
def s1248 : Span := ⟨[2, 20, 21],644,[[770, 1092, 1281, 2118, 2180], [2116, 2118], [2114, 2118], [2180, 2188], [2116, 2132], [2114, 2146], [2180, 2244], [2116, 2244], [770, 2114, 2244], [2180, 2692], [1092, 2116, 2692], [2692]]⟩
def s1513 : Span := ⟨[2, 19, 22],644,[[2306, 2307], [2305, 2307], [1092, 1281, 2114, 2307], [2306, 2314], [2305, 2321], [770, 802], [2306, 2370], [770, 1092, 1281, 2305, 2370], [2114, 2370], [2306, 2818], [770, 1281, 2305, 2818], [770, 2818]]⟩
def s1578 : Span := ⟨[3, 20, 22],532,[[546, 1036, 1057, 2062, 2068], [2060, 2062], [2058, 2062], [2068, 2076], [2060, 2076], [546, 2058, 2076], [2068, 2132], [2060, 2188], [2058, 2314], [2068, 2580], [1036, 2060, 2580], [2580]]⟩
def s1645 : Span := ⟨[2, 21, 22],644,[[2306, 2307], [2305, 2307], [1092, 1281, 2114, 2307], [2306, 2314], [2305, 2321], [2114, 2146], [2306, 2370], [770, 1092, 1281, 2305, 2370], [2114, 2370], [2306, 2818], [770, 1281, 2305, 2818], [770, 2818]]⟩
def s1646 : Span := ⟨[3, 21, 22],532,[[2082, 2083], [2081, 2083], [1036, 1057, 2058, 2083], [2082, 2090], [546, 1036, 1057, 2081, 2090], [2058, 2090], [2082, 2146], [2081, 2209], [2058, 2314], [2082, 2594], [546, 1057, 2081, 2594], [546, 2594]]⟩
def s1710 : Span := ⟨[16, 19, 21, 22],802,[[2338, 2339], [1185, 1313, 2209, 2339], [1164, 1185, 2314, 2339], [2338, 2346], [1185, 1313, 2209, 2314, 2321, 2346], [2314, 2346], [1185, 1441, 2146, 2338], [1313, 1441], [1185, 1441], [2338, 2850], [1185, 2209, 2850], [2850]]⟩
def s1722 : Span := ⟨[17, 20, 21, 22],676,[[2146, 2150, 2209, 2212], [2148, 2150], [2146, 2150], [2132, 2164, 2188, 2212], [2148, 2164], [2132, 2164], [2212, 2276], [2148, 2276], [2146, 2188, 2276, 2314], [2212, 2724], [1124, 2148, 2724], [2724]]⟩
def s1723 : Span := ⟨[18, 20, 21, 22],788,[[2132, 2146, 2188, 2209, 2318, 2324], [2316, 2318], [2314, 2318], [2324, 2332], [2316, 2332], [2132, 2146, 2314, 2332], [2324, 2388], [2132, 2188, 2316, 2388], [2132, 2388], [2324, 2836], [1292, 2316, 2836], [2836]]⟩
def s1724 : Span := ⟨[19, 20, 21, 22],802,[[2338, 2339], [2337, 2339], [2188, 2209, 2314, 2339], [2338, 2346], [2132, 2146, 2188, 2209, 2337, 2346], [2314, 2346], [2338, 2402], [2146, 2209, 2337, 2402], [2146, 2402], [2338, 2850], [1313, 2337, 2850], [2850]]⟩
def t1 : Tri := ⟨[2, 5],[9],644,1281,1289⟩
def t3 : Tri := ⟨[4, 5],[6],98,266,1289⟩
def t4 : Tri := ⟨[1, 6],[8],672,1120,1121⟩
def t5 : Tri := ⟨[2, 6],[8],644,1092,1121⟩
def t6 : Tri := ⟨[3, 6],[10],546,1057,1121⟩
def t7 : Tri := ⟨[4, 6],[7],140,161,1121⟩
def t8 : Tri := ⟨[1, 7],[9],672,1120,1100⟩
def t9 : Tri := ⟨[2, 7],[9],644,1092,1100⟩
def t10 : Tri := ⟨[3, 7],[10],532,1036,1100⟩
def t11 : Tri := ⟨[4, 7],[6],140,161,1100⟩
def t12 : Tri := ⟨[1, 8],[6],672,1120,673⟩
def t13 : Tri := ⟨[2, 8],[6],644,1092,673⟩
def t14 : Tri := ⟨[3, 8],[9],1036,1057,673⟩
def t15 : Tri := ⟨[4, 8],[9],140,161,673⟩
def t16 : Tri := ⟨[1, 9],[7],672,1120,652⟩
def t17 : Tri := ⟨[2, 9],[7],644,1092,652⟩
def t18 : Tri := ⟨[3, 9],[8],1036,1057,652⟩
def t19 : Tri := ⟨[4, 9],[10],84,140,652⟩
def t20 : Tri := ⟨[1, 10],[7],784,1288,596⟩
def t21 : Tri := ⟨[2, 10],[8],1092,1281,596⟩
def t22 : Tri := ⟨[3, 10],[7],532,1036,596⟩
def t23 : Tri := ⟨[4, 10],[9],84,140,596⟩
def t24 : Tri := ⟨[1, 11],[12],672,784,786⟩
def t25 : Tri := ⟨[2, 11],[13],644,770,786⟩
def t26 : Tri := ⟨[3, 11],[14],532,1036,786⟩
def t27 : Tri := ⟨[4, 11],[13],140,266,786⟩
def t28 : Tri := ⟨[6, 11],[14],1121,2129,2130⟩
def t29 : Tri := ⟨[7, 11],[15],1100,2122,2130⟩
def t30 : Tri := ⟨[8, 11],[12],673,785,786⟩
def t31 : Tri := ⟨[9, 11],[13],652,778,786⟩
def t32 : Tri := ⟨[10, 11],[18],596,786,594⟩
def t33 : Tri := ⟨[1, 12],[11],672,784,674⟩
def t34 : Tri := ⟨[2, 12],[14],644,1092,674⟩
def t35 : Tri := ⟨[3, 12],[13],532,546,674⟩
def t36 : Tri := ⟨[4, 12],[13],84,98,674⟩
def t37 : Tri := ⟨[5, 12],[14],1289,2185,2186⟩
def t38 : Tri := ⟨[7, 12],[16],1100,2122,2186⟩
def t39 : Tri := ⟨[8, 12],[11],673,785,674⟩
def t40 : Tri := ⟨[9, 12],[17],652,674,650⟩
def t41 : Tri := ⟨[10, 12],[13],596,610,674⟩
def t42 : Tri := ⟨[1, 13],[15],672,1120,660⟩
def t43 : Tri := ⟨[2, 13],[11],644,770,660⟩
def t44 : Tri := ⟨[3, 13],[12],532,546,660⟩
def t45 : Tri := ⟨[4, 13],[12],84,98,660⟩
def t46 : Tri := ⟨[5, 13],[15],1289,2185,2193⟩
def t47 : Tri := ⟨[6, 13],[16],1121,2129,2193⟩
def t48 : Tri := ⟨[8, 13],[17],673,660,657⟩
def t49 : Tri := ⟨[9, 13],[11],652,778,660⟩
def t50 : Tri := ⟨[10, 13],[12],596,610,660⟩
def t51 : Tri := ⟨[1, 14],[12],672,1120,1122⟩
def t52 : Tri := ⟨[2, 14],[12],644,1092,1122⟩
def t53 : Tri := ⟨[3, 14],[15],532,546,1122⟩
def t54 : Tri := ⟨[4, 14],[15],84,98,1122⟩
def t55 : Tri := ⟨[5, 14],[12],1289,2185,1290⟩
def t56 : Tri := ⟨[6, 14],[11],1121,2129,1122⟩
def t57 : Tri := ⟨[7, 14],[17],1100,1122,1098⟩
def t58 : Tri := ⟨[9, 14],[10],778,1122,1290⟩
def t59 : Tri := ⟨[10, 14],[15],596,610,1122⟩
def t60 : Tri := ⟨[1, 15],[13],672,1120,1108⟩
def t61 : Tri := ⟨[2, 15],[13],644,1092,1108⟩
def t62 : Tri := ⟨[3, 15],[14],532,546,1108⟩
def t63 : Tri := ⟨[4, 15],[14],84,98,1108⟩
def t64 : Tri := ⟨[5, 15],[13],1289,2185,1297⟩
def t65 : Tri := ⟨[6, 15],[17],1121,1108,1105⟩
def t66 : Tri := ⟨[7, 15],[11],1100,2122,1108⟩
def t67 : Tri := ⟨[8, 15],[10],785,1108,1297⟩
def t68 : Tri := ⟨[10, 15],[14],596,610,1108⟩
def t69 : Tri := ⟨[1, 16],[13],784,1288,1164⟩
def t70 : Tri := ⟨[2, 16],[14],644,770,1164⟩
def t71 : Tri := ⟨[3, 16],[13],532,1036,1164⟩
def t72 : Tri := ⟨[4, 16],[15],84,140,1164⟩
def t73 : Tri := ⟨[5, 16],[18],1289,1164,1161⟩
def t74 : Tri := ⟨[6, 16],[7],1121,1164,1185⟩
def t75 : Tri := ⟨[7, 16],[12],1100,2122,1164⟩
def t76 : Tri := ⟨[8, 16],[9],673,1164,1185⟩
def t77 : Tri := ⟨[9, 16],[14],652,778,1164⟩
def t79 : Tri := ⟨[2, 17],[19],644,770,676⟩
def t80 : Tri := ⟨[3, 17],[20],546,2058,676⟩
def t81 : Tri := ⟨[4, 17],[19],140,266,676⟩
def t82 : Tri := ⟨[6, 17],[20],1121,2129,1124⟩
def t83 : Tri := ⟨[7, 17],[21],1100,2122,1124⟩
def t84 : Tri := ⟨[8, 17],[18],673,785,676⟩
def t85 : Tri := ⟨[9, 17],[19],652,778,676⟩
def t86 : Tri := ⟨[10, 17],[12],610,676,612⟩
def t87 : Tri := ⟨[12, 17],[20],674,2186,676⟩
def t88 : Tri := ⟨[13, 17],[21],660,2193,676⟩
def t89 : Tri := ⟨[14, 17],[18],1122,1290,1124⟩
def t90 : Tri := ⟨[15, 17],[19],1108,1297,1124⟩
def t91 : Tri := ⟨[16, 17],[8],1185,676,1188⟩
def t93 : Tri := ⟨[2, 18],[20],770,2114,788⟩
def t94 : Tri := ⟨[3, 18],[19],532,546,788⟩
def t95 : Tri := ⟨[4, 18],[19],84,98,788⟩
def t96 : Tri := ⟨[5, 18],[20],1289,2185,1292⟩
def t97 : Tri := ⟨[7, 18],[22],1100,2122,1292⟩
def t98 : Tri := ⟨[8, 18],[17],673,785,788⟩
def t99 : Tri := ⟨[9, 18],[13],652,788,780⟩
def t100 : Tri := ⟨[10, 18],[19],596,610,788⟩
def t101 : Tri := ⟨[11, 18],[20],786,2130,788⟩
def t102 : Tri := ⟨[13, 18],[22],660,2193,788⟩
def t103 : Tri := ⟨[14, 18],[17],1122,1290,1292⟩
def t104 : Tri := ⟨[15, 18],[8],1297,788,1300⟩
def t105 : Tri := ⟨[16, 18],[19],1164,1185,1292⟩
def t106 : Tri := ⟨[1, 19],[21],784,2128,802⟩
def t107 : Tri := ⟨[2, 19],[17],644,770,802⟩
def t108 : Tri := ⟨[3, 19],[18],532,546,802⟩
def t109 : Tri := ⟨[4, 19],[18],84,98,802⟩
def t110 : Tri := ⟨[5, 19],[21],1289,2185,1313⟩
def t111 : Tri := ⟨[6, 19],[22],1121,2129,1313⟩
def t112 : Tri := ⟨[8, 19],[12],673,802,801⟩
def t113 : Tri := ⟨[9, 19],[17],652,778,802⟩
def t114 : Tri := ⟨[10, 19],[18],596,610,802⟩
def t115 : Tri := ⟨[11, 19],[21],786,2130,802⟩
def t116 : Tri := ⟨[12, 19],[22],674,2186,802⟩
def t117 : Tri := ⟨[14, 19],[6],1122,1313,1314⟩
def t118 : Tri := ⟨[15, 19],[17],1108,1297,1313⟩
def t119 : Tri := ⟨[16, 19],[18],1164,1185,1313⟩
def t120 : Tri := ⟨[1, 20],[17],672,2128,2132⟩
def t121 : Tri := ⟨[2, 20],[18],770,2114,2132⟩
def t122 : Tri := ⟨[3, 20],[21],532,546,2132⟩
def t123 : Tri := ⟨[4, 20],[21],84,98,2132⟩
def t124 : Tri := ⟨[5, 20],[18],1289,2185,2188⟩
def t125 : Tri := ⟨[6, 20],[17],1121,2129,2132⟩
def t126 : Tri := ⟨[7, 20],[15],1100,2132,2124⟩
def t127 : Tri := ⟨[9, 20],[10],652,2132,2188⟩
def t128 : Tri := ⟨[10, 20],[21],596,610,2132⟩
def t129 : Tri := ⟨[11, 20],[18],786,2130,2132⟩
def t130 : Tri := ⟨[12, 20],[17],674,2186,2188⟩
def t131 : Tri := ⟨[13, 20],[10],660,2132,2196⟩
def t132 : Tri := ⟨[15, 20],[22],1108,1297,2132⟩
def t133 : Tri := ⟨[16, 20],[15],1164,2132,2188⟩
def t134 : Tri := ⟨[1, 21],[19],784,2128,2146⟩
def t135 : Tri := ⟨[2, 21],[17],644,2114,2146⟩
def t138 : Tri := ⟨[5, 21],[19],1289,2185,2209⟩
def t139 : Tri := ⟨[6, 21],[14],1121,2146,2145⟩
def t140 : Tri := ⟨[7, 21],[17],1100,2122,2146⟩
def t141 : Tri := ⟨[8, 21],[10],673,2146,2209⟩
def t142 : Tri := ⟨[10, 21],[20],596,610,2146⟩
def t143 : Tri := ⟨[11, 21],[19],786,2130,2146⟩
def t145 : Tri := ⟨[13, 21],[17],660,2193,2209⟩
def t146 : Tri := ⟨[14, 21],[22],1122,1290,2146⟩
def t147 : Tri := ⟨[16, 21],[14],1185,2146,2209⟩
def t148 : Tri := ⟨[1, 22],[21],1120,1288,2314⟩
def t150 : Tri := ⟨[3, 22],[18],532,2058,2314⟩
def t151 : Tri := ⟨[4, 22],[20],84,266,2314⟩
def t152 : Tri := ⟨[5, 22],[14],1289,2314,2313⟩
def t153 : Tri := ⟨[6, 22],[7],2129,2314,2321⟩
def t154 : Tri := ⟨[7, 22],[18],1100,2122,2314⟩
def t155 : Tri := ⟨[8, 22],[9],785,2314,2321⟩
def t156 : Tri := ⟨[9, 22],[20],652,778,2314⟩
def t158 : Tri := ⟨[12, 22],[19],674,2186,2314⟩
def t159 : Tri := ⟨[13, 22],[12],2193,2314,2321⟩
def t160 : Tri := ⟨[14, 22],[21],1122,1290,2314⟩
def t161 : Tri := ⟨[15, 22],[14],1297,2314,2321⟩
def t162 : Tri := ⟨[4, 6],[5],98,266,1121⟩
def t163 : Tri := ⟨[5, 6, 7],[18],1289,1100,1097⟩
def t164 : Tri := ⟨[1, 6],[5],1120,1288,1121⟩
def t165 : Tri := ⟨[2, 6],[10],770,1281,1121⟩
def t166 : Tri := ⟨[5, 7, 8],[10],2185,2122,673⟩
def t167 : Tri := ⟨[6, 7, 8],[9],1121,1100,673⟩
def t168 : Tri := ⟨[5, 6, 9],[10],2185,2129,652⟩
def t169 : Tri := ⟨[1, 7],[10],784,1288,1100⟩
def t170 : Tri := ⟨[2, 7],[5],1092,1281,1100⟩
def t171 : Tri := ⟨[6, 7, 9],[8],1121,1100,652⟩
def t173 : Tri := ⟨[5, 8, 9],[18],1289,652,649⟩
def t174 : Tri := ⟨[6, 8, 9],[7],1121,673,652⟩
def t175 : Tri := ⟨[7, 8, 9],[6],1100,673,652⟩
def t176 : Tri := ⟨[5, 6, 10],[9],2185,2129,596⟩
def t177 : Tri := ⟨[3, 7],[6],1036,1057,1100⟩
def t178 : Tri := ⟨[5, 7, 10],[8],1289,1100,596⟩
def t179 : Tri := ⟨[5, 8, 10],[7],1289,785,596⟩
def t180 : Tri := ⟨[6, 8, 10],[17],1121,596,593⟩
def t181 : Tri := ⟨[7, 8, 10],[5],1100,785,596⟩
def t182 : Tri := ⟨[4, 9],[8],140,161,652⟩
def t183 : Tri := ⟨[5, 9, 10],[6],2185,652,596⟩
def t184 : Tri := ⟨[6, 9, 10],[5],2129,652,596⟩
def t185 : Tri := ⟨[7, 9, 10],[20],2122,596,586⟩
def t186 : Tri := ⟨[1, 11],[14],784,1120,786⟩
def t187 : Tri := ⟨[8, 11],[6],785,786,2130⟩
def t188 : Tri := ⟨[2, 11],[15],770,1092,786⟩
def t189 : Tri := ⟨[9, 11],[7],778,786,2130⟩
def t190 : Tri := ⟨[3, 12],[16],546,1036,674⟩
def t191 : Tri := ⟨[4, 12],[11],84,140,2186⟩
def t192 : Tri := ⟨[10, 12],[7],610,674,2186⟩
def t193 : Tri := ⟨[11, 12, 13],[18],786,660,658⟩
def t194 : Tri := ⟨[6, 11],[8],2129,786,2130⟩
def t195 : Tri := ⟨[2, 12],[16],770,1281,674⟩
def t196 : Tri := ⟨[5, 12],[8],2185,674,2186⟩
def t197 : Tri := ⟨[11, 13, 14],[16],2130,2193,1122⟩
def t198 : Tri := ⟨[12, 13, 14],[15],674,660,1122⟩
def t199 : Tri := ⟨[7, 11],[9],2122,786,2130⟩
def t200 : Tri := ⟨[11, 12, 15],[16],2130,2186,1108⟩
def t201 : Tri := ⟨[1, 13],[16],784,1288,660⟩
def t202 : Tri := ⟨[5, 13],[9],2185,660,2193⟩
def t203 : Tri := ⟨[12, 13, 15],[14],674,660,1108⟩
def t204 : Tri := ⟨[3, 14],[11],532,1036,1290⟩
def t205 : Tri := ⟨[4, 14],[16],98,140,1122⟩
def t206 : Tri := ⟨[10, 14],[9],610,1122,1290⟩
def t207 : Tri := ⟨[11, 14, 15],[18],786,1108,1106⟩
def t208 : Tri := ⟨[12, 14, 15],[13],674,1122,1108⟩
def t209 : Tri := ⟨[13, 14, 15],[12],660,1122,1108⟩
def t210 : Tri := ⟨[7, 12],[10],2122,674,2186⟩
def t211 : Tri := ⟨[11, 12, 16],[15],2130,2186,1164⟩
def t212 : Tri := ⟨[11, 13, 16],[14],786,660,1164⟩
def t213 : Tri := ⟨[11, 14, 16],[13],786,1290,1164⟩
def t214 : Tri := ⟨[12, 14, 16],[17],674,1164,1162⟩
def t215 : Tri := ⟨[13, 14, 16],[11],660,1290,1164⟩
def t216 : Tri := ⟨[11, 15, 16],[12],2130,1108,1164⟩
def t217 : Tri := ⟨[12, 15, 16],[11],2186,1108,1164⟩
def t218 : Tri := ⟨[13, 15, 16],[20],2193,1164,1169⟩
def t219 : Tri := ⟨[1, 17],[20],672,2128,676⟩
def t220 : Tri := ⟨[8, 17],[6],673,676,1124⟩
def t221 : Tri := ⟨[14, 17],[12],1122,676,1124⟩
def t222 : Tri := ⟨[2, 17],[21],644,2114,676⟩
def t223 : Tri := ⟨[9, 17],[7],652,676,1124⟩
def t224 : Tri := ⟨[15, 17],[13],1108,676,1124⟩
def t225 : Tri := ⟨[3, 18],[22],532,2058,788⟩
def t227 : Tri := ⟨[10, 18],[7],596,788,1292⟩
def t228 : Tri := ⟨[16, 18],[13],1164,788,1292⟩
def t229 : Tri := ⟨[17, 18, 19],[12],676,802,804⟩
def t230 : Tri := ⟨[6, 17],[8],1121,676,1124⟩
def t231 : Tri := ⟨[12, 17],[14],674,676,1124⟩
def t232 : Tri := ⟨[2, 18],[22],1092,2114,1292⟩
def t233 : Tri := ⟨[5, 18],[8],1289,788,1292⟩
def t234 : Tri := ⟨[11, 18],[14],786,788,1292⟩
def t235 : Tri := ⟨[17, 19, 20],[22],1124,1313,2132⟩
def t236 : Tri := ⟨[18, 19, 20],[21],788,802,2132⟩
def t237 : Tri := ⟨[7, 17],[9],1100,676,1124⟩
def t238 : Tri := ⟨[13, 17],[15],660,676,1124⟩
def t239 : Tri := ⟨[17, 18, 21],[22],1124,1292,2146⟩
def t240 : Tri := ⟨[1, 19],[22],1120,2128,1313⟩
def t241 : Tri := ⟨[5, 19],[9],1289,802,1313⟩
def t242 : Tri := ⟨[11, 19],[15],786,802,1313⟩
def t243 : Tri := ⟨[18, 19, 21],[20],788,802,2146⟩
def t244 : Tri := ⟨[4, 20],[22],84,266,2132⟩
def t245 : Tri := ⟨[10, 20],[9],596,2132,2188⟩
def t246 : Tri := ⟨[17, 20, 21],[12],676,2146,2148⟩
def t247 : Tri := ⟨[18, 20, 21],[19],788,2132,2146⟩
def t248 : Tri := ⟨[19, 20, 21],[18],802,2132,2146⟩
def t249 : Tri := ⟨[7, 18],[10],1100,788,1292⟩
def t250 : Tri := ⟨[17, 18, 22],[21],1124,1292,2314⟩
def t251 : Tri := ⟨[12, 19],[16],674,802,1313⟩
def t252 : Tri := ⟨[17, 19, 22],[20],676,802,2314⟩
def t253 : Tri := ⟨[17, 20, 22],[19],676,2188,2314⟩
def t254 : Tri := ⟨[18, 20, 22],[11],788,2314,2316⟩
def t255 : Tri := ⟨[19, 20, 22],[17],802,2188,2314⟩
def t256 : Tri := ⟨[14, 21],[16],1122,2146,2209⟩
def t257 : Tri := ⟨[17, 21, 22],[18],1124,2146,2314⟩
def t258 : Tri := ⟨[18, 21, 22],[17],1292,2146,2314⟩
def t260 : Tri := ⟨[9, 14],[4],778,1122,1802⟩
def t261 : Tri := ⟨[9, 20],[4],652,2132,2700⟩
def t262 : Tri := ⟨[14, 21],[4],1122,2146,3170⟩
def t263 : Tri := ⟨[6, 11],[1],2129,786,2131⟩
def t264 : Tri := ⟨[7, 11],[2],2122,786,2138⟩
def t265 : Tri := ⟨[7, 12],[3],2122,674,2250⟩
def t267 : Tri := ⟨[12, 17],[1],674,676,678⟩
def t268 : Tri := ⟨[7, 17],[2],1100,676,1132⟩
def t269 : Tri := ⟨[13, 17],[2],660,676,692⟩
def t270 : Tri := ⟨[7, 18],[3],1100,788,1356⟩
def t271 : Tri := ⟨[13, 18],[3],660,788,916⟩
def t272 : Tri := ⟨[8, 11, 12],[5],785,786,2186⟩
def t273 : Tri := ⟨[8, 17, 18],[5],673,676,1292⟩
def t274 : Tri := ⟨[12, 17, 18],[11],674,676,788⟩
def t277 : Tri := ⟨[4, 7],[17],98,1100,74⟩
def t278 : Tri := ⟨[2, 8],[10],1092,1281,785⟩
def t279 : Tri := ⟨[14, 19],[9],1290,802,1314⟩
def t280 : Tri := ⟨[2, 8],[17],644,673,641⟩
def t281 : Tri := ⟨[8, 11],[1],673,786,787⟩
def t282 : Tri := ⟨[8, 17],[1],673,676,677⟩
def t283 : Tri := ⟨[3, 9],[17],546,652,522⟩
def t284 : Tri := ⟨[2, 10],[18],770,596,578⟩
def t285 : Tri := ⟨[16, 17],[9],1164,676,1188⟩
def t286 : Tri := ⟨[15, 18],[10],1108,788,1300⟩
def t287 : Tri := ⟨[12, 21],[10],674,2146,2210⟩
def t288 : Tri := ⟨[11, 22],[9],786,2314,2322⟩
def t289 : Tri := ⟨[1, 5],[6],1120,1288,1289⟩
def t290 : Tri := ⟨[3, 5],[9],546,1057,1289⟩
def t291 : Tri := ⟨[1, 9],[10],1120,1288,778⟩
def t292 : Tri := ⟨[2, 9],[5],644,1281,652⟩
def t294 : Tri := ⟨[3, 10],[6],532,1057,596⟩
def t295 : Tri := ⟨[6, 16],[13],1121,2129,1185⟩
def t296 : Tri := ⟨[6, 22],[19],1121,2129,2321⟩
def t297 : Tri := ⟨[1, 9],[17],672,652,648⟩
def t298 : Tri := ⟨[9, 11],[2],652,786,794⟩
def t299 : Tri := ⟨[10, 12],[3],596,674,738⟩
def t300 : Tri := ⟨[5, 12],[1],1289,2186,2187⟩
def t301 : Tri := ⟨[6, 13],[10],2129,660,2193⟩
def t302 : Tri := ⟨[9, 17],[2],652,676,684⟩
def t303 : Tri := ⟨[10, 18],[3],596,788,852⟩
def t304 : Tri := ⟨[5, 18],[1],1289,1292,1293⟩
def t305 : Tri := ⟨[6, 19],[10],1121,802,1313⟩
def t306 : Tri := ⟨[3, 5],[18],532,1289,1033⟩
def t307 : Tri := ⟨[4, 5],[18],140,1289,137⟩
def t308 : Tri := ⟨[1, 10],[17],672,596,592⟩
def t309 : Tri := ⟨[16, 17],[1],1185,676,1189⟩
def t310 : Tri := ⟨[14, 19],[5],1290,1313,1314⟩
def t311 : Tri := ⟨[11, 22],[1],786,2321,2323⟩
def t312 : Tri := ⟨[5, 13],[2],1289,2193,2201⟩
def t313 : Tri := ⟨[10, 14],[4],596,1122,1634⟩
def t314 : Tri := ⟨[5, 19],[2],1289,1313,1321⟩
def t315 : Tri := ⟨[10, 20],[4],596,2132,2644⟩
def t316 : Tri := ⟨[1, 12],[14],672,1120,674⟩
def t317 : Tri := ⟨[8, 12],[1],673,674,675⟩
def t318 : Tri := ⟨[2, 13],[15],644,1092,660⟩
def t319 : Tri := ⟨[9, 13],[2],652,660,668⟩
def t320 : Tri := ⟨[6, 14],[1],1121,1122,1123⟩
def t321 : Tri := ⟨[7, 15],[2],1100,1108,1116⟩
def t322 : Tri := ⟨[4, 12],[17],140,674,138⟩
def t323 : Tri := ⟨[3, 14],[17],1036,1122,1034⟩
def t324 : Tri := ⟨[18, 20, 22],[14],1292,2314,2316⟩
def t325 : Tri := ⟨[3, 13],[16],532,1036,660⟩
def t326 : Tri := ⟨[4, 13],[17],161,660,145⟩
def t327 : Tri := ⟨[10, 13],[3],596,660,724⟩
def t328 : Tri := ⟨[3, 15],[17],1057,1108,1041⟩
def t329 : Tri := ⟨[4, 15],[16],84,140,1108⟩
def t330 : Tri := ⟨[10, 15],[4],596,1108,1620⟩
def t331 : Tri := ⟨[2, 16],[18],1281,1164,1153⟩
def t332 : Tri := ⟨[7, 16],[3],1100,1164,1228⟩
def t333 : Tri := ⟨[9, 16],[4],652,1164,1676⟩
def t334 : Tri := ⟨[10, 17],[13],596,676,612⟩
def t335 : Tri := ⟨[16, 21],[20],1164,1185,2209⟩
def t336 : Tri := ⟨[13, 22],[18],660,2193,2321⟩
def t337 : Tri := ⟨[15, 22],[20],1108,1297,2321⟩
def t338 : Tri := ⟨[17, 18, 19],[13],676,788,804⟩
def t339 : Tri := ⟨[17, 20, 21],[13],676,2132,2148⟩
def t340 : Tri := ⟨[15, 20],[16],1108,2132,2188⟩
def t341 : Tri := ⟨[18, 20, 22],[15],1292,2132,2316⟩
def t342 : Tri := ⟨[19, 21, 22],[16],1313,2209,2337⟩
def t344 : Tri := ⟨[9, 12],[19],778,674,650⟩
def t345 : Tri := ⟨[8, 13],[18],785,660,657⟩
def t346 : Tri := ⟨[7, 14],[21],2122,1122,1098⟩
def t347 : Tri := ⟨[6, 15],[20],2129,1108,1105⟩
def t348 : Tri := ⟨[1, 18],[20],784,2128,788⟩
def t349 : Tri := ⟨[8, 18],[1],673,788,789⟩
def t350 : Tri := ⟨[14, 18],[1],1122,1292,1294⟩
def t351 : Tri := ⟨[2, 19],[21],770,2114,802⟩
def t352 : Tri := ⟨[9, 19],[2],652,802,810⟩
def t353 : Tri := ⟨[15, 19],[2],1108,1313,1329⟩
def t354 : Tri := ⟨[1, 20],[18],784,2128,2132⟩
def t355 : Tri := ⟨[6, 20],[1],1121,2132,2133⟩
def t356 : Tri := ⟨[12, 20],[1],674,2188,2190⟩
def t357 : Tri := ⟨[2, 21],[19],770,2114,2146⟩
def t358 : Tri := ⟨[3, 21],[20],532,546,2146⟩
def t359 : Tri := ⟨[7, 21],[2],1100,2146,2154⟩
def t360 : Tri := ⟨[13, 21],[2],660,2209,2225⟩
def t361 : Tri := ⟨[4, 6],[20],84,2129,81⟩
def t362 : Tri := ⟨[3, 8],[18],532,785,529⟩
def t363 : Tri := ⟨[6, 8, 10],[20],2129,596,593⟩
def t364 : Tri := ⟨[4, 12],[19],266,674,138⟩
def t365 : Tri := ⟨[3, 14],[21],2058,1122,1034⟩
def t366 : Tri := ⟨[12, 14, 16],[20],2186,1164,1162⟩
def t367 : Tri := ⟨[4, 18],[13],140,788,268⟩
def t368 : Tri := ⟨[3, 20],[15],1036,2132,2060⟩
def t369 : Tri := ⟨[4, 7],[21],161,2122,74⟩
def t370 : Tri := ⟨[3, 9],[19],1057,778,522⟩
def t371 : Tri := ⟨[2, 10],[19],770,610,578⟩
def t372 : Tri := ⟨[4, 13],[21],161,2193,145⟩
def t373 : Tri := ⟨[3, 15],[19],1057,1297,1041⟩
def t374 : Tri := ⟨[2, 16],[19],770,1185,1153⟩
def t375 : Tri := ⟨[3, 19],[22],546,2058,802⟩
def t376 : Tri := ⟨[4, 19],[16],161,1313,289⟩
def t377 : Tri := ⟨[10, 19],[3],596,802,866⟩
def t378 : Tri := ⟨[16, 19],[3],1164,1313,1441⟩
def t379 : Tri := ⟨[3, 21],[16],1057,2209,2081⟩
def t380 : Tri := ⟨[4, 21],[22],98,266,2146⟩
def t381 : Tri := ⟨[10, 21],[4],596,2146,2658⟩
def t382 : Tri := ⟨[16, 21],[4],1185,2146,3233⟩
def t383 : Tri := ⟨[2, 22],[13],644,2321,2305⟩
def t384 : Tri := ⟨[3, 22],[19],546,2058,2314⟩
def t385 : Tri := ⟨[4, 22],[21],98,266,2314⟩
def t386 : Tri := ⟨[7, 22],[3],1100,2314,2378⟩
def t387 : Tri := ⟨[9, 22],[4],652,2314,2826⟩
def t388 : Tri := ⟨[13, 22],[3],2193,2314,2449⟩
def t389 : Tri := ⟨[15, 22],[4],1297,2314,3345⟩
def t390 : Tri := ⟨[7, 9, 10],[22],2122,778,586⟩
def t391 : Tri := ⟨[13, 15, 16],[22],2193,1297,1169⟩
def c1 : Case := ⟨[1],[1],[
s2,s4,s5,s22,s26,s28,s44,s55,s131,s132,s138,s162,
s284,s324,s917,s1122,s1248,s1513,s1578,s1645,s1646,s1722,s1723,s1724
],[
t1,t6,t9,t10,t14,t15,t17,t19,t22,t23,t25,t26,
t27,t28,t29,t30,t31,t32,t34,t35,t37,t39,t43,t44,
t45,t47,t48,t49,t50,t52,t54,t55,t56,t58,t59,t61,
t62,t63,t64,t65,t66,t67,t68,t71,t72,t73,t74,t75,
t76,t77,t79,t80,t81,t82,t83,t84,t85,t86,t87,t88,
t89,t91,t93,t96,t97,t98,t99,t100,t101,t102,t103,t105,
t107,t109,t110,t111,t112,t113,t114,t115,t116,t117,t118,t119,
t121,t122,t123,t124,t125,t126,t127,t128,t129,t130,t131,t132,
t133,t135,t138,t139,t140,t141,t142,t143,t145,t146,t147,t150,
t151,t152,t153,t154,t155,t156,t158,t159,t160,t161,t162,t163,
t165,t166,t167,t168,t170,t171,t173,t174,t175,t176,t177,t178,
t179,t180,t181,t182,t183,t184,t185,t187,t188,t189,t190,t191,
t192,t193,t194,t195,t196,t197,t198,t199,t200,t202,t203,t204,
t205,t206,t207,t208,t209,t210,t211,t212,t213,t214,t215,t216,
t217,t218,t220,t221,t222,t223,t224,t225,t227,t228,t229,t230,
t231,t232,t233,t234,t235,t236,t237,t239,t241,t242,t243,t245,
t246,t247,t248,t249,t250,t251,t252,t253,t254,t255,t256,t257,
t258,t260,t261,t262,t265,t270,t271,t272,t273,t274,t277,t280,
t283,t286,t287,t288,t290,t292,t294,t296,t298,t299,t301,t302,
t307,t315,t318,t322,t323,t335,t336,t337,t340,t342,t344,t346,
t352,t353,t359,t360,t367,t371,t374,t375,t379,t380,t381,t382,
t383,t384,t385,t386,t387
],[
g0,g2,g4,g8,g16,g32,g64,g128,g256,g512,g1024,g2048,
g4096,g8192,g16384,g32768,g65536,g131072,g262144,g524288,g1048576,g2097152,g48,g80,
g96,g144,g160,g192,g272,g288,g320,g384,g528,g544,g576,g640,
g768,g1040,g2080,g3072,g4160,g5120,g6144,g8320,g9216,g10240,g12288,g16640,
g17408,g18432,g20480,g24576,g33280,g33792,g34816,g36864,g40960,g49152,g65552,g66560,
g131104,g133120,g196608,g262208,g266240,g327680,g393216,g524416,g532480,g589824,g655360,g786432,
g1048832,g1064960,g1114112,g1179648,g1310720,g1572864,g2097664,g2129920,g2162688,g2228224,g2359296,g2621440,
g3145728,g176,g336,g608,g896,g11264,g21504,g38912,g57344,g66576,g133152,g266304,
g532608,g720896,g1065216,g1376256,g2130432,g2490368,g3670016,g338,g480,g612,g720,g816,
g904,g21506,g30720,g38916,g46080,g52224,g57352,g1376258,g1966080,g2490372,g2949120,g3342336,
g3670024,g11440,g721072,g732160,g21842,g39524,g58248,g1376594,g1397762,g2490980,g2529284,g3670920,
g3727368,g732336,g1398098,g2529892,g3728264
]⟩
def k1 : List Nat := [
1,238,151,239,104,240,241,242,243,77,78,152,
153,154,244,245,246,247,60,155,50,51,79,80,
81,156,157,248,249,250,251,158,159,160,161,252,
33,162,34,253,163,254,9,61,164,62,39,165,
166,167,255,168,40,82,105,256,63,52,64,257,
106,107,169,108,109,83,110,111,258,259,170,84,
112,85,41,260,171,261,113,114,115,262,116,53,
117,21,86,118,87,88,119,89,263,90,91,120,
264,265,172,121,122,173,266,174,7,54,55,123,
175,267,42,43,65,124,25,176,26,56,44,22,
35,13,177,178,268,179,125,180,181,182,269,126,
270,183,14,15,271,16,184,127,92,27,28,272,
273,185,274,275,276,186,277,128,278,279,280,187,
281,282,283,284,93,285,286,188,23,287,189,190,
94,288,289,129,191,95,290,291,57,292,130,293,
66,192,294,96,295,193,131,296,297,298,194,299,
300,301,302,195,132,133,97,98,134,67,68,303,
135,196,69,304,136,305,306,197,307,308,198,309,
310,311,312,313,314,315,58,70,316,199,317,200,
318,319,201,36,202,320,321,203,322,204,323,324,
325,71,99,137,17,326,138,205,206,327,139,328,
329,330,331,332,333,100,207,334,208,209,210,45,
29,335,140,46,47,141,211,212,336,337,338,339,
213,101,214,30,215,31,340,341,342,343,344,345,
346,347,348,349,350,351,352,353,354,355,356,357,
358,359,360,361,362,363,364,365,366,367,368,369,
370,371,372,373,374,375,376,377,378,379,380,381,
382,383,384,385,386,387,388,389,390,391,392,393,
394,395,396,397,398,399,400,401,402,403,404,405,
406,407,408,409,410,411,412,413,414,415,416,417,
418,419,420,421,422,423,424,425,426,427,428,429,
430,431,432,433,434,435,436,437,438,439,440,441,
442,443,444,445,446,447,448,449,450,451,452,453,
454,455,456,457,458,459,460,461,462,463,464,465,
466,467,468,469,470,471,472,473,474,475,476
]
def w1 : List Nat := [
0x106016050120400e0300a0200401dde55003000000b02a0a026090220801e0701a06016050120400e0300a02006015dd54c03000000b02a0a026090220801e0701a06016050120400e0300a02006011dc,0x1000000b02a0a026090220801e0701a06016050120400e030080180402de055803000000b02a0a026090220801e0701a06016050120400e0300a01804025df55403000000b02a0a026090220801e0701a,0x1050120380c0280801804045e356403000000b02a0a026090220801e0701a06016050120400c028080180403de256003000000b02a0a026090220801e0701a06016050120400e0280801804035e155c03,0x10b02a0a026090220801e0701a06016048100380c0280801804055e556c03000000b02a0a026090220801e0701a06016050100380c028080180404de456803000000b02a0a026090220801e0701a06016,0x10380c028080180406de857803000000b02a0a026090220801e0701a05814048100380c0280801804065e757403000000b02a0a026090220801e0701a06014048100380c028080180405de65700300000,0x10a026090220801c0681805814048100380c028080180407dea58003000000b02a0a026090220801e0681805814048100380c0280801804075e957c03000000b02a0a026090220801e070180581404810,0x10280801804095ed58c03000000b02a0a026090200781c0681805814048100380c028080180408dec58803000000b02a0a026090220781c0681805814048100380c0280801804085eb58403000000b02a,0x1088200781c0681805814048100380c02808018040a5ef59403000000b02a0a024088200781c0681805814048100380c028080180409dee59003000000b02a0a026088200781c0681805814048100380c,0x10100d02df25a003000000a82809824088200781c0681805814048100380c02808018040b5f159c03000000b02809824088200781c0681805814048100380c02808018040adf059803000000b02a09824,0x10801e0701a06016050120400a020060100f035f45a803000000b02a0a026090220801e0701a06016050120400c020060100f02df35a403000000b02a0a026090220801e0701a06016050120400e02006,0x103df75b403000000b02a0a026090220801e0701a06016050120380a0200601011035f65b003000000b02a0a026090220801e0701a06016050120380c020060101102df55ac03000000b02a0a02609022,0x10701a06016050100380a0200601013035f95bc03000000b02a0a026090220801e0701a06016050100380c020060101302df85b803000000b02a0a026090220801e0701a06016050120300a0200601011,
0x15c803000000b02a0a026090220801e0701a060160500e0300a0200601013045fb5c403000000b02a0a026090220801e0701a06016050100300a020060101303dfa5c003000000b02a0a026090220801e,0x106016048100300a020060101503dfe5d003000000b02a0a026090220801e0701a06016048100380a0200601015035fd5cc03000000b02a0a026090220801e0701a06016048100380c020060101502dfc,0x1000000b02a0a026090220801e0701a060160400e0300a020060101504e005d803000000b02a0a026090220801e0701a060160480e0300a0200601015045ff5d403000000b02a0a026090220801e0701a,0x10400e0300a020060101905e035e403000000b02a0a026090220801e0701a05814048100380a0200601019036025e003000000b02a0a026090220801e0701a06014048100380c020060101702e015dc03,0x10b02a0a026090220801e07018050120400e0300a020060101b05e055ec03000000b02a0a026090220801e0701805814048100300a020060101b03e045e803000000b02a0a026090220801e0701a05012,0x10300a020060101d05e085f803000000b02a0a026090220801e06818058140480e0300a020060101d046075f403000000b02a0a026090220801e07016050120400e0300a020060101b066065f00300000,0x10a026090220801e06016050120400e0300a020060101d06e0a60003000000b02a0a026090220801e06816050120400e0300a020060101d066095fc03000000b02a0a026090220801e06818050120400e,0x1020060101f0660d60c03000000b02a0a026090220801c06818050120400e0300a020060101f05e0c60803000000b02a0a026090220801c06818058140400e0300a020060101f04e0b60403000000b02a,0x1090220801a06016050120400e0300a020060101f0760f61403000000b02a0a026090220801c06016050120400e0300a020060101f06e0e61003000000b02a0a026090220801c06816050120400e0300a,0x1010210661262003000000b02a0a026090220781c06818050120400e0300a020060102105e1161c03000000b02a0a026090220781c06818058120400e0300a02006010210561061803000000b02a0a026,0x10781a06016050120400e0300a02006010210761462803000000b02a0a026090220781c06016050120400e0300a020060102106e1362403000000b02a0a026090220781c06816050120400e0300a02006,0x105e1763403000000b02a0a026090200781c0681805814048100380c020060102302e1663003000000b02a0a026090220701a06016050120400e0300a020060102107e1562c03000000b02a0a02609022,
0x106816050120400e0300a02006010250661963c03000000b02a0a026088200781c0681805814048100380a02006010250361863803000000b02a0a026090200781c06818050120400e0300a0200601023,0x164803000000b02a0a024088200781c0681805814048100300a020060102703e1b64403000000b02a0a0260801e0701a06016050120400e0300a020060102508e1a64003000000b02a0a026088200781c,0x1050120400e0300a02006010270961e65003000000b02a0a0240801e0701a06016050120400e0300a020060102708e1d64c03000000b02a0a024088200781c06016050120400e0300a020060102706e1c,0x1000000b02a09824088200781a06016050120400e0300a02006010290762065803000000b02a09824088200781c06818058140480e0300a02006010290461f65403000000b02a0a0220801e0701a06016,0x10400e0300a020060102909e2366403000000b02a098220801e0701a06016050120400e0300a02006010290962266003000000b02a098240801e0701a06016050120400e0300a020060102908e2165c03,0x10b02809824088200701a06016050120400e0300a020060102b07e2566c03000000b02809824088200781c06818058140400e0300a020060102b04e2466803000000b02a090220801e0701a0601605012,0x10300a020060102b09e2867803000000b028098220801e0701a06016050120400e0300a020060102b0962767403000000b028098240801e0701a06016050120400e0300a020060102b08e266700300000,0x109824088200781c06818058120400e0300a020060102d0562a68003000000b026090220801e0701a06016050120400e0300a020060102b0a62967c03000000b028090220801e0701a06016050120400e,0x1020060102d0962d68c03000000a828098240801e0701a06016050120400e0300a020060102d08e2c68803000000a828098240881e0701a06016050120400e0300a020060102d0862b68403000000a828,0x10801e0701a06016050120400e0300a020060102d0a62f69403000000a828090220801e0701a06016050120400e0300a020060102d09e2e69003000000a828098220801e0701a06016050120400e0300a,0x104c0f02e326a003000000b02a0a026090220801e0701a060160501203808018040440d02e3169c03000000a026090220801e0701a06016050120400e0300a020060102d0ae3069803000000a82609022,0x10801e0701a060160380c028080180405413046346a803000000b02a0a026090220801e0701a060160481002808018040540f036336a403000000b02a0a026090220801e0701a06016050100300801804,
0x1066376b403000000b02a0a026090220801c06014048100380c028080180407c1b05e366b003000000b02a0a026090220801e06814048100380c02808018040741905e356ac03000000b02a0a02609022,0x106818050120400e030080180408c1702e396bc03000000b02a0a026090220681805814048100380c02808018040841f076386b803000000b02a0a026090220781c05814048100380c02808018040841b,0x16c803000000b02a0a024088200781c06016050120400c028080180409c1b03e3b6c403000000b02a0a026088200781c06816050120400e0280801804094190363a6c003000000b02a0a026090200781c,0x1050100380c02808018040ac1f04e3e6d003000000b02a098200781c0681805814048100380c02808018040a42508e3d6cc03000000b02a09824088200781a06016050120380c02808018040a41d0463c,0x1000000a828098240881e0701a06016048100380c02808018040b421056406d803000000b028090200781c0681805814048100380c02808018040ac2708e3f6d403000000b02809824088200701a06016,0x105010030080181303c0b016436e4030000009824088200781c0681805814048100380c02808018040b42b0a6426e003000000a828088200781c0681805814048100380c02808018040b427096416dc03,0x10b02a0a026090220801e0701a0601604810028080101503c0d01e456ec03000000b02a0a026090220801e0701a060160500a02006010130440f036446e803000000b02a0a026090220801e0701a06016,0x1028060101504c11026486f803000000b02a0a026090220801e0701a060160400e020060101504c0d02e476f403000000b02a0a026090220801e0701a060160480c02006010150440f02e466f00300000,0x10a0260902208016050120400e0300a020060101f0741b0664a70003000000b02a0a026090220801c06014048100380c028080181f06c17016496fc03000000b02a0a026090220801e0701a060160380c,0x10102107c1905e4d70c03000000b02a0a0260902207818050120400e0300a02006010210741b05e4c70803000000b02a0a026090220781c05814048100380c028080102106c1901e4b70403000000b02a,0x10781c0681805814048100380c028080182b09c230164f71403000000b02a0a026090220681805814048100380c028060102107c1d0264e71003000000b02a0a026090220701a050120400e0300a02006,0x10a42708e5272003000000a828088200781c0681805814048100380c028080102d09c2501e5171c03000000b0220801e0701a06016050120400e0300a020060102b0a4270965071803000000b02809020,
0x10681805814048100380c028060102d0ac290265472803000000a0260801e0701a06016050120400e0300a020060102d0ac2508e5372403000000a8240801e0701a06016050120400e0300a020060102d,0x105e5773403000000b02a098200781c06818058140480e0200601029094230440d02e5673003000000b02a0a026090220801e068140480e020060101d064170440d02e5572c030000009824088200781c,0x1058120400a020040841b0641503c0d01e5973c03000000b02a0a026090220801c060140400c0200607c1b05c1303c0b0165873803000000b02a098200781a050120400e0300a02006010290942307419,0x174803000000b028090200781c06818058140400c020060ac2708c1303c0b0165b74403000000b02a0a02609022068180580e0300a018040841f0741504c110265a74003000000b02a0a026090220781c,0x10300a020040b4270942106c1901e5e75003000000a828088200781c06818058120400a020040b4270941503c0d01e5d74c03000000b0280902007018050120400e0300a020060ac2708c1f06c170165c,0x100000098240881a06016050120400e0300a018040b42b0a42107c1d02660758030000009824088200781c068180580e0300a018040b42b0a41504c110265f75403000000a8280881e07016050120400e,0x109c250841b0641503c0d01e6376403000000b028090200701805010030080182b09c2307c1b05c1303c0b0166276003000000b02a098200781a0501203808018040a42508c1d064170440d02e6175c03,0x10dc190ac231380b1002513c1e0301c1f408350000b42b0a4210566576c0300000098240881a060160380c028060102d0ac290841f0741504c110266476803000000a8280881e0701604810028080102d,0x1010240481099a6004caf0447c05665020d40707d0780c01c3206c2e0340e03c2d0143109c5005c370642b08c4e02c400944f0002d0ac29084d79901017012280070c81b0b80d0380f0b4050c42714017,0x10002d0ac293626604caf0447c01c3206c2e0340e03c2d0143109c5005c370642b08c4e02c400944f074c707cd0084d70002d0ac290526795008908000801e0701a0601605022028260a40e0302b0b406,0x10440f05c1004cb706488054b309cd1084ce02c0d074c9024b60a4d80002d0ac249a25f0405c0214a049350526707cd0074c7084d702c400642b05c3709c500944f08c4e01c3206c2e0340e03c2d01431,0x10002d0a0260966994c224f8249a00b0342734419220170401103c1d32421338152cc1f33c132dc092d8293600d0381b0b80f0b4070c8050c4000b42b07e3008d3d01c3206c2e0340e03c2d0143107ccf,
0x10b4220866b7c4158a8000a0260902a0601e0701a048160400e0200c028040182d088209aa2d08d3a085070550602c0d07c1b0741a0440f05c1004c1e0241d0ac1f034cd03cd601cd50146406c5b0647e,0x10902a0601e0701a048160400e0200c028040a02d098069b66b0826a000260902a0601e0701a048160400e0200c028040a02d018229b2400522b00028098240781c068180582a04810038080300a01006,0x103c1704013078090742b07c050ec231142611c000b428090659b4259a4051900f3581b16c073540d334191f80b0341f06c1d0681103c1704013078090742b07c000b428098478b021154151cc229b000,0x10ec23114190e42110c241942611c000b4280680e9be5101a4100028088200781c0681805814048100a8250280809c040b40e0326e8b8190e40d038212b8152b41b5340f438074340b0341f06c1d06811,0x19740c2e806500144e40e9bc190e42110c0b0341f06c1d0681103c1704013078090742b07c050ec231142611c24194000b428068d99b8151080d0380b0341f06c1d0681103c1704013078090742b07c05,0x10984702c0d07c1b0741a0440f05c1004c1e0241d0ac1f0002d0a0da98c0c2e8142080b0341f06c1d0681103c1704013078090742b07c050ec231140632824194200e41816c1a3642611c000b42803e70,0x1948190e4224f00b0341103c0726825318170401307809074210300d0380f0601f06c1d068051901b05415064283682b07c000b4279c65e054420340e03e7008039018ca0605b068d90906508c450143b,0x106818058140480a0380409808018290400c9ce720ac1f0002d0062f08d3b0647e09e71014640340e0840c094c606c150541903c1801c9a0a0da05c100440f04c1e07c1b02c0d0241d0741a0002d0aa72,0x1062761ec0c87c2d0040009824088200781c0682a058140480e02829020060101804675218221ec0c9cc000a8200781c06824058140480a038040980801829060109d221089ef0b401000240a8200781c,0x1090220801e0681d058140480e0300a020060a829010189e0c30882b062760001e0a81a09016050120280e08026020060a404072779d4231c8109d0000801e0a81a09016050120280e01026020060a41c,0x19e4170dc0b10005428070a41b05415064210301308c090a80f0601f0882d004000a82909824122780642b08c1403433072770002a06824058140481e038200980801829028049e6200463c0b40100026,0x107c22014440648d0743a090480b4010002a0a4260580a08e7b2180c8f42d00400098200781c06818058140482a0380a09408018040a4230427a30c220ac000a41c0648d5081820c221dc00094160743a,
0x1004000a8290981636e22044760347b08e7b01c2906c15054190840c04c230242a03c1807c22014440648d0743a090480b4010002a0a4260580a9f27a044cb01c2906c15054190840c04c230242a03c18,0x10a42602e7e0580d9842d00400098200781a0501203808018040a42508c1d064170a81102e7d9580c308221d8104bc0a9f0192341d0e8070a41b05415064210301308c090a80f0601f08805110241202d,0x10a426a0086032570b401000260801e06814048100381908c08018040a42505c2a0740a9fe7d0405e01c2906c15054190840c04c230242a03c1807c2201444060830887707087058db090480b4010002a,0x1008ac042230b40100024088200781c0680405814048270380c028080182a0a418a067f044cb02e7e060830887707087058db014440904801c2906c15054190840c04c230242a03c1807c220b4010002a,0x17b82d004000a0220801e070140601609c12090100300a020060a80406a82a04254c4234c01d0d8190d4170180d1e40b1e0053d026a000f0601308c210301f0881b05415064090a8070a42d004000a829,0x10a4020b4010002a09016070180882705e8306a82000220801e070140601609c12090100300a020280a806012848ec0e8702d004000a024088200781c0601605012040060300a020270a80406e8386c0e,0x1088200781c03018058140482a02808018040401aa1a04039e80b4010002809824088200601c058140482a03006028080101e0401ba1684044ac084ae054ad01d4f07c7a04d090347902c78024ab01508,0x10200407806032897dc0e78c2d004000a026090180801e0701a058120502a0180a020040880c04688a181ba140009824088200601c058140482a0a006028080101e03010a1ddc03de20b4010002809824,0x10a026090220801e0701a06016050120280d0202a010060428b4480e7d82d004000a026090220801e0701a06016050120340a0202a010060468aa201b29c10a1c00090220801807016050120a8280980a,0x1090120a8280980a02004078200508ea301b3f80ca2400088200601c058240482a0a026028080101e05006a368b0468a00026090220801e0701a06016050120a00a0202a0100d01a8c7d00e7842d00400,0x10701a060160482a0180a02015010100368e9140c3300e27c113c41b144142382705c290082d004000a8240581c0602207812028040202001cdc7780d2700f3e01b294113e406a342d004000881807016,0x17942d004000a026090220601e0701a04816030060540a0202a0102004290a38114681b144142382705c2900807370000a8240581c060220781202804020200368f8cc0e7f42d004000a026090220801e,
0x10400e0300a020210101a05692a440da3c073701b14414238000601c058240482a0a026028220101e0202023dff03d1b042900b40100026090220601e0701a04816030060a00a0202a01015082917f80e,0x1008153742d004000a8240581c0602207812028040201aa4e9206c51044540345303c6f0808f09c170a4020002a09016070180881e0480a01008054dd27c068402d004000a026090220781c0a81805812,0x13740d14c111500f1bc2023c0007016090120a8280980a0881807804022952940684c2d004000a026090220781c06016050120400e0300a0202a0102106e947ac07404111500d14c0f1bc2023c2705c29,0x104544084d3054d20249601ced012960b401000240582a0a026070220601e0480aa5ddf044fa054a003d430350f0850206ca601cee022950b40100016090120a8280981c088180780a01296a501aa4c15,0x1018040500ca6911039f50b4010002809824088200781c06818058140482a02c080180403011a65f3039e00b4010002809824088200781c068180580b048080a8140180403010a61dd03cf7034b806d4b,0x1a6800090220801e0701a0601602c120202a0a006098040529c8c4107c82d004000a026090220801e0701a060160501202c2a020060100e0369ba6410a600009824088200781c068180580b048080a828,0x10a8280902601804a7e460411803a9d0b40100026090220801e0701a060160480c0540b020280a8060129e464107f02d004000a026090220801e0701a060160480c0540b020060a80403a9da6c0f4400c,0x119c111fc121242705c290082d004000a8240581c060220780b01015a829f084a90254901d4506c810149b02a97000160a8280981c088180901e04849a780d45c14a7000088200781c068180580b04808,0x10a0071181b09c0919c111fc121242705c29008000a8240581c060220780b012a28c80e7e02d004000a026090220801e0701a06016050100a80b0200604c04032a191c0f2ec0c470210a0071181b09c09,0x10002809824088200781c06818058140a804028080181303010a8e430389d034b8054d2012a20447f024670842801c4606c270484909c170a4020b4010002a09016070180881e02cdea840d44c15a8021,0x1030df01c460148902cde06c2708428048490a40209c170b4010002a09016070180881e02014046a47ec0f45810a8c2d0040009824088200781c06818058280a80402808018130500c37de403dfa0b401,0x1028260182404c08a9e00046340b4010002809824088200781c068180580c0200a04c060102a0540ea99f903d14046a4030df0b40100024088200781c06818058280a804028260181302014a964403915,
0x1118210a012124000a8280981c0581809022078e092010170142780f3c00d3bc08a9c2d004000801e0701a060160a02a0100a098220900604ea8a980f2ec0d47414a9400088200781c06818058280a804,0x1090220702a06016050120400e0300a0200607c04082aa82c0b1ac052741b09c210a0071a8092a00d1b00f148111b4151b81e3802705c290082d004000a8240581c0602204ea9aa0052240b3781b09c07,0x106ca40001607c05386ab082aa00026090220702a06016050120400e030280200607c0a012ac4b41a8542d004000a026090220700a06016050120400e0301f020060a804086ab8381a7a82d004000a026,0x10a4020002a0901607018088e2ab40538413aa4111b4151b80f1480d1b0092a0071a81e380000a02a070160602409822ab86b06c8102aac000240881c0a81805814048100380c0a0080181f09804ab469,0x1abc09410072a80d1c029008151cc21154111c805210131800f1c41f1841b1d022388000a8240581c06026ac1ec02e160b40100028040240801e0701a06016050120300e08c2a0180402026abeae09c17,0x179c2d004000a02a090220181e07016050120400e0980a020190100c06ab18740b1e0092ac26ac01f1841318005210211541b1d0151cc111c80f1c40d1c0072a822388290082d004000a8240581c06066,0x10582a048100a02602808064040500ead2b206ab10002a090220181e0701605012040280980a020190100e032b38dc208182d004000a026090220a81e07016050120400e0180a020190100c06eb284820,0x1080bd018e3060660b4010002a090160701e052b5ad0152280f4fc050f00b0f411098230d02900809174130b0270d4181982d004000a8240581c0780638e0206d4708453032b30b40100024088060781c,0x112a59030cc0391f052b5080bd068a3018e30143c02c3d0442608c340a4020245d04c2c09c35060660b4010002a090160701eada4b0349c03c820143c02c3d0442608c340a4020245d04c2c09c35068a3,0x1228071040b17811098052f821304230501c1282d004000a8240581907eb78341b490214b0151b80f1480d1b0071a81ead8130b009174270d4230d0110980b0f4050f018198290082d004000a8240581c,0x1020220181d0401aae20906d2207eb7014be02c5e0548a04c2c084c104426024970a40208c1409c360343301c4103c1c0704a0b4010002a09016064909281a498290080f0700925c130b0270d80d0cc15,0x10901e0280406016050260a80e030280880607412022ba828214a81aae02d00400098240780a01018058140482a0380c0a0220181d02010ae614081e90b40100028098240780a01018058140482a0380c,
0x100028098240881f02818058140482a0380c0681d0180404008aeeba04cc805500024ff0a40208c1409c360343301c4103c1c0146802c3e064900704a0002a09016078e481c211501b29c10ae42d00400,0x1055250a40208c1409c360343301c4103c1c0146802c3e06cc0078e40704a064900002a0901604abd938202fc08aec2d00400098240881f02818058140a02a0380c0681d0180404810af2380820f0b401,0x10540802c3e03480044a2058090b4010002a0901d0601aafa5a0405c080bf020c80503f04abd06cc0078e402c3e014680649003c1c01c4109c3608c14034330704a0a4020b4010002a09016026bc0446d,0x102abf930204841aaf80d200112880b0f829008270181f17c0718c230500f0700513009134130fc15020160242d004000a8240741839608085290a40209c0607c5f01c6308c1403c1c0144c0244d04c3f,0x10144c03c1c01c6307c5f08c140a4020540809c06058090b4010002a0901d0923503480045410a40209c0607c5f01c6308c1403c1c0144c0244d04c3f0540806c9808499060e5058090b4010002a0901d,0x100400098240880a0301c04014048190380605c080a02a06804b0527082030b40100028098240880a0301c04014048190380605c080682a0101eb0255030160405e02abf0849906c98060e504c3f0244d,0x1074240642f03c38024a1058090b4010002a09022048040281a07ec2b040f208130b0095301b480230d00b0f4050f029008150202701807080110580d0841d09016024000a8240642f9342048c1eb002d,0x101c200441603421074240642f03c38058090002a09022048040281ab1211081e60b4010002809824088180701706814048100380c0282a018040201eb0e0c0852b0a4020540809c0601c200441603421,0x1008150202701807080110580d0841d090190bc0f0e016024000a824088120100ab1a3607a050b4010002809824088200301c06014048100380a0102a018170201bb16c307ec2024a10a4020540809c06,0x10342107424058090642f0b4010002a0902204ac88041f1ac212a41b204093c80ab1829008150202701807080110580d0841d090190bc0f0e0160242d004000a82408812012c7b14214a0092981ab1029,0x1078fc0249e068fd01146038bc0842804ac80a4020540809c0601c20044160342107424058090642f0b4010002a09022b264902c9b068fb0791e084d302496012c703c380a4020540809c0601c2004416,0x11841318005210211541b1d00f1c422b24190bc11058070800d0841d09027018150201602429008000a8242461702e390b40100028040240801e0701a060140480c03817020060102a09823b2a58028b9,
0x1088200781c0682a058140480a03825020060101809acc86811308274b80d1c0051d40b15807214092301d0e817164290082110c131601b1681f188151080f15c242442d004000a81808ecbb28093cc1f,0x1214092301d0e817164290082110c131601b1681f188151080f15c242442d004000a818b3a1e0347909acc0b401000100a0200781c0682a058140480a038250200601022062cd7b40d8602d004000a010,0x110c1d0e81510809230072141b168171640f15c0b158051d424244290082d004000a8038640d8e82d004000a026088200781c02816050120400e06808018040942a066cfb34111d823b2c051d40b15807,0x1044135402a00c210280001c125482a00c0901c00054051f42a00c1d010000840a42c2a00c1d01000034115442d0042a00c00024074302d0042a00c0007404b3c270d4230d01109818b381f1881316021,0x105812038040780ab422704c5807c6209d3408d3206c5a05c5903c5702c56014f501c120a803024070341104413054050640b074040840a0b40100028094302202a00c15014000640b1f02a00c1501400,0x1074040640b054050441303411024070a80301c12000220a01a05824038040480ab44b109d330a8030001202c4b7c0278a02d004210281d0101902c150141104c0d0440901c070482a00c00090220a01a,0x124a2407e3e0b4010840a074040640b054050441303411024070a80301c120000a0902206816038040a01309ad3b440b12c250c0052c00f2c81b2d42a00c000a01608812b4a2509c8b07ad00b4010840a,0x1b525b028b907c5206c2709905011480386009430088920a80301c12024070341104413054050640b074040840a0b401000280581339ad302cb109d4e04ad206cb503cb2014b0094300a8030002805822,0x104c0d0440901c070481902c2a00c000680a0381205823090280101eb564f07ce106ca4099030943002c4b03cc404ce6088920a80301c12024070341104413054050640b074040840a0b4010002805805,0x1314262d01639c2a00c070480901c0d0441104c150141902c1d010210282d004000a012b5ad507c6106c2e016d403cc402c4b04ce608892094300a80300028058e78fc268982d004210281d0101501411,0x100c2809400014939880a2240e2f012b581a1a4221e80422c1e314262d01639c250c02a00c070480901c0d0441104c150141902c1d010210282d004000a0259700b12c0f0e0250c0221e81a1a40422c1e,0x102c1b3a01d0101f3a421028233a8000909512c132500002cec0b42a00c0524c0003ceb08c0901c280940004c944d81902c2a00c280940008cea0882d004280940007ce905415014280940006ce83d82a,
0x10240701c12014930a8030a02505ed809ad7002d921c1d010242540005ed84dc280942a00c242540009ad78a4274e0170dc0524c070482d0042a00c0d044280940b3b00901c1104c13250150140f3ac19,0x6500b40108cea0840a07ce90740406ce80640b090950540504c940441303ceb0341102cec
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check1 : ¬ FormulaSat (caseFormula c1) := checkW_sound _ k1 10 w1 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good1 : caseGood c1=true := by decide +kernel
theorem next1 {chosen region} (disj : ∀ i∈c1.prior, chosen i=false) (O : Later c1.prior chosen region) : ∃ g∈c1.groups, Matches chosen g := case_conclusion _ good1 check1 disj O
def c16 : Case := ⟨[5],[5],[
s0,s1,s2,s3,s4,s5,s24,s26,s28,s50,s82,s83,
s177,s178,s184,s240,s242,s916,s917,s1122,s1247,s1248,s1513,s1578,
s1645,s1646,s1722,s1723,s1724
],[
t4,t5,t6,t9,t11,t12,t13,t14,t15,t17,t19,t21,
t22,t23,t24,t25,t26,t27,t29,t30,t31,t32,t33,t38,
t39,t41,t42,t43,t44,t45,t47,t48,t49,t50,t51,t52,
t54,t56,t58,t59,t60,t61,t62,t63,t66,t67,t68,t69,
t70,t71,t72,t74,t75,t76,t77,t79,t80,t81,t82,t83,
t85,t86,t87,t88,t90,t91,t93,t94,t95,t97,t99,t100,
t101,t102,t104,t105,t106,t111,t112,t114,t115,t116,t117,t118,
t119,t120,t121,t122,t123,t125,t126,t127,t128,t129,t130,t131,
t132,t133,t134,t135,t139,t141,t142,t143,t145,t146,t147,t148,
t150,t151,t153,t154,t155,t156,t158,t159,t160,t161,t167,t169,
t171,t174,t175,t177,t180,t182,t185,t188,t189,t190,t192,t193,
t194,t195,t197,t198,t199,t200,t201,t203,t204,t205,t206,t207,
t208,t209,t210,t211,t212,t213,t214,t215,t216,t217,t218,t219,
t220,t221,t223,t224,t227,t228,t229,t232,t234,t235,t236,t239,
t240,t242,t243,t245,t246,t247,t248,t249,t250,t251,t252,t253,
t254,t255,t256,t257,t258,t260,t261,t262,t263,t264,t265,t269,
t270,t271,t280,t283,t285,t286,t287,t288,t294,t295,t296,t297,
t298,t299,t301,t308,t311,t315,t316,t317,t323,t328,t330,t331,
t335,t336,t337,t340,t342,t344,t346,t347,t348,t349,t350,t351,
t352,t353,t354,t355,t356,t357,t359,t360,t361,t364,t375,t376,
t377,t378,t379,t380,t381,t382,t383,t384,t385,t386,t387
],[
g0,g1,g2,g4,g8,g32,g64,g128,g256,g512,g1024,g2048,
g4096,g8192,g16384,g32768,g65536,g131072,g262144,g524288,g1048576,g2097152,g96,g160,
g192,g288,g320,g384,g544,g576,g640,g768,g2080,g3072,g4160,g5120,
g6144,g8320,g9216,g10240,g12288,g16640,g17408,g18432,g20480,g24576,g33280,g33792,
g34816,g36864,g40960,g49152,g66560,g131104,g133120,g196608,g262208,g266240,g327680,g393216,
g524416,g532480,g589824,g655360,g786432,g1048832,g1064960,g1114112,g1179648,g1310720,g1572864,g2097664,
g2129920,g2162688,g2228224,g2359296,g2621440,g3145728,g161,g322,g608,g704,g800,g896,
g11264,g21504,g38912,g57344,g133152,g266304,g532608,g720896,g1065216,g1376256,g2130432,g2490368,
g3670016,g480,g612,g904,g11265,g21506,g30720,g38916,g46080,g52224,g57352,g720897,
g1376258,g1966080,g2490372,g2949120,g3342336,g3670024,g11425,g21826,g721057,g1376578,g39524,g58248,
g732161,g1397762,g2490980,g2529284,g3670920,g3727368,g732321,g1398082,g2529892,g3728264
]⟩
def k16 : List Nat := [
1,148,149,238,150,239,240,151,152,241,242,79,
80,153,113,243,154,155,244,245,156,81,157,61,
158,51,52,82,83,84,159,246,247,114,248,85,
249,160,250,86,251,252,253,161,23,254,255,162,
62,37,256,38,24,115,42,257,163,116,117,164,
165,118,53,166,119,87,167,54,258,168,259,120,
88,89,55,63,90,169,170,171,121,172,91,64,
56,260,261,262,122,173,65,174,14,123,43,263,
264,265,266,124,57,125,10,126,175,44,267,176,
177,268,178,179,180,269,270,271,272,45,46,273,
25,181,26,182,183,27,39,15,127,184,274,128,
185,275,276,277,129,28,278,186,29,279,16,187,
188,92,30,31,280,189,281,282,283,93,284,94,
285,66,47,130,95,96,190,131,286,287,67,288,
289,290,97,191,291,98,292,192,193,293,294,295,
132,296,133,297,194,195,196,58,298,299,197,198,
300,68,199,301,302,303,304,305,306,307,308,309,
310,311,312,69,70,313,200,314,201,315,316,134,
32,202,22,317,203,318,319,204,320,71,72,99,
135,205,206,321,207,208,322,100,323,209,7,324,
101,210,325,102,326,136,211,327,212,213,214,17,
103,73,215,137,48,328,216,138,329,104,33,217,
40,59,139,18,330,331,332,333,334,335,336,218,
105,219,34,220,35,337,338,339,340,341,342,343,
344,345,346,347,348,349,350,351,352,353,354,355,
356,357,358,359,360,361,362,363,364,365,366,367,
368,369,370,371,372,373,374,375,376,377,378,379,
380,381,382,383,384,385,386,387,388,389,390,391,
392,393,394,395,396,397,398,399,400,401,402,403,
404,405,406,407,408,409,410,411,412,413,414,415,
416,417,418,419,420,421,422,423,424,425,426,427,
428,429,430,431,432,433,434,435,436,437,438,439,
440,441,442,443,444,445,446,447,448,449,450,451,
452,453,454,455,456,457,458,459,460,461,462,463,
464,465,466
]
def w16 : List Nat := [
0x106016050120400e0300801802015d45440b000000b02a0a026090220801e0701a06016050120400e030080180400dd35400b000000b02a0a026090220801e0701a06016050120400e0300801804009d2,0x1000000b02a0a026090220801e0701a06016050120400e0300601002025d654c0b000000b02a0a026090220801e0701a06016050120400e030080100201dd55480b000000b02a0a026090220801e0701a,0x1050120380c0200601002045d95580b000000b02a0a026090220801e0701a06016050120400c020060100203dd85540b000000b02a0a026090220801e0701a06016050120400e0200601002035d75500b,0x10b02a0a026090220801e0701a06016048100380c0200601002055db5600b000000b02a0a026090220801e0701a06016050100380c020060100204dda55c0b000000b02a0a026090220801e0701a06016,0x10380c020060100206dde56c0b000000b02a0a026090220801e0701a05814048100380c0200601002065dd5680b000000b02a0a026090220801e0701a06014048100380c020060100205ddc5640b00000,0x10a026090220801c0681805814048100380c020060100207de05740b000000b02a0a026090220801e0681805814048100380c0200601002075df5700b000000b02a0a026090220801e070180581404810,0x10200601002095e35800b000000b02a0a026090200781c0681805814048100380c020060100208de257c0b000000b02a0a026090220781c0681805814048100380c0200601002085e15780b000000b02a,0x1088200781c0681805814048100380c02006010020a5e55880b000000b02a0a024088200781c0681805814048100380c020060100209de45840b000000b02a0a026088200781c0681805814048100380c,0x10080f035e85940b000000a82809824088200781c0681805814048100380c02006010020b5e75900b000000b02809824088200781c0681805814048100380c02006010020ade658c0b000000b02a09824,0x10801e0701a060160501203008018040081103dea59c0b000000b02a0a026090220801e0701a0601605012038080180400811035e95980b000000b02a0a026090220801e0701a06016050120400801804,0x1045ed5a80b000000b02a0a026090220801e0701a060160501003008018040081303dec5a40b000000b02a0a026090220801e0701a0601605010038080180400813035eb5a00b000000b02a0a02609022,0x10701a060160481003008018040081503def5b00b000000b02a0a026090220801e0701a0601604810038080180400815035ee5ac0b000000b02a0a026090220801e0701a060160500e030080180400813,
0x15bc0b000000b02a0a026090220801e0701a060160400e03008018040081504df15b80b000000b02a0a026090220801e0701a060160480e030080180400815045f05b40b000000b02a0a026090220801e,0x1058140481003008018040081b03df45c40b000000b02a0a026090220801e0701a050120400e03008018040081905df35c00b000000b02a0a026090220801e0701a0581404810038080180400819035f2,0x1000000b02a0a026090220801e07016050120400e03008018040081b065f65cc0b000000b02a0a026090220801e07018050120400e03008018040081b05df55c80b000000b02a0a026090220801e07018,0x10400e03008018040081d065f95d80b000000b02a0a026090220801e06818050120400e03008018040081d05df85d40b000000b02a0a026090220801e06818058140480e03008018040081d045f75d00b,0x10b02a0a026090220801c06818058140400e03008018040081f04dfb5e00b000000b02a0a026090220801e06016050120400e03008018040081d06dfa5dc0b000000b02a0a026090220801e0681605012,0x103008018040081f06dfe5ec0b000000b02a0a026090220801c06816050120400e03008018040081f065fd5e80b000000b02a0a026090220801c06818050120400e03008018040081f05dfc5e40b00000,0x10a026090220781c06818058120400e030080180400821056005f40b000000b02a0a026090220801a06016050120400e03008018040081f075ff5f00b000000b02a0a026090220801c06016050120400e,0x1018040082106e036000b000000b02a0a026090220781c06816050120400e030080180400821066025fc0b000000b02a0a026090220781c06818050120400e03008018040082105e015f80b000000b02a,0x1090220701a06016050120400e03008018040082107e056080b000000b02a0a026090220781a06016050120400e030080180400821076046040b000000b02a0a026090220781c06016050120400e03008,0x100825066086140b000000b02a0a026088200781c068180581404810038080180400825036076100b000000b02a0a026090200781c06818050120400e03008018040082305e0660c0b000000b02a0a026,0x10781c06818058140481003008018040082703e0a61c0b000000b02a0a0260801e0701a06016050120400e03008018040082508e096180b000000b02a0a026088200781c06816050120400e0300801804,0x10960d6280b000000b02a0a0240801e0701a06016050120400e03008018040082708e0c6240b000000b02a0a024088200781c06016050120400e03008018040082706e0b6200b000000b02a0a02408820,
0x106016050120400e0300801804008290760f6300b000000b02a09824088200781c06818058140480e0300801804008290460e62c0b000000b02a0a0220801e0701a06016050120400e030080180400827,0x163c0b000000b02a098220801e0701a06016050120400e030080180400829096116380b000000b02a098240801e0701a06016050120400e03008018040082908e106340b000000b02a09824088200781a,0x1050120400e03008018040082b07e146440b000000b02809824088200781c06818058140400e03008018040082b04e136400b000000b02a090220801e0701a06016050120400e03008018040082909e12,0x1000000b028098220801e0701a06016050120400e03008018040082b0961664c0b000000b028098240801e0701a06016050120400e03008018040082b08e156480b000000b02809824088200701a06016,0x10400e03008018040082d056196580b000000b026090220801e0701a06016050120400e03008018040082b0a6186540b000000b028090220801e0701a06016050120400e03008018040082b09e176500b,0x10a828098240801e0701a06016050120400e03008018040082d08e1b6600b000000a828098240881e0701a06016050120400e03008018040082d0861a65c0b000000a82809824088200781c0681805812,0x103008018040082d0a61e66c0b000000a828090220801e0701a06016050120400e03008018040082d09e1d6680b000000a828098220801e0701a06016050120400e03008018040082d0961c6640b00000,0x10a026090220801e0701a060160501203808018040440d00e206740b000000a026090220801e0701a06016050120400e03008018040082d0ae1f6700b000000a826090220801e0701a06016050120400e,0x1010020541103e236800b000000b02a0a026090220801e0701a060160481002006010020540f0362267c0b000000b02a0a026090220801e0701a0601605010030080180204c0f016216780b000000b02a,0x1090220801e0701a060160380c020060100205413046256880b000000b02a0a026090220801e0701a060160400e020060100205413036246840b000000b02a0a026090220801e0701a060160480c02006,0x10841b066286940b000000b02a0a026090220801c06014048100380c020060100207c1b05e276900b000000b02a0a026090220801e06814048100380c02006010020741905e2668c0b000000b02a0a026,0x10781c06816050120400e0200601002094190362a69c0b000000b02a0a026090220681805814048100380c02006010020841f076296980b000000b02a0a026090220781c05814048100380c0200601002,
0x108e2d6a80b000000b02a09824088200781a06016050120380c02006010020a41d0462c6a40b000000b02a0a024088200781c06016050120400c020060100209c1b03e2b6a00b000000b02a0a02608820,0x105814048100380c02006010020ac2708e2f6b00b000000b02809824088200701a06016050100380c02006010020ac1f04e2e6ac0b000000b02a098200781c0681805814048100380c02006010020a425,0x16bc0b000000a828088200781c0681805814048100380c02006010020b427096316b80b000000a828098240881e0701a06016048100380c02006010020b421056306b40b000000b028090200781c06818,0x10601604810020040081503c0d01e346c40b000000b02a0a026090220801e0701a060160500801804008130440f036336c00b0000009824088200781c0681805814048100380c02006010020b42b0a632,0x1000000b02a0a026090220801e06814048100380c020060101d0641700e366cc0b000000b02a0a026090220801e0701a060160380c018040081504c11026356c80b000000b02a0a026090220801e0701a,0x10380c020040082106c1901e396d80b000000b02a0a0260902208016050120400e03008018040081f0741b066386d40b000000b02a0a026090220801c06014048100380c020060081f06c17016376d00b,0x10b02a0a026090220701a050120400e03008018040082107c1905e3b6e00b000000b02a0a0260902207818050120400e0300801804008210741b05e3a6dc0b000000b02a0a026090220781c0581404810,0x1020060082b09c230163e6ec0b000000b02a098200781c0681805814048100380c02006010290942300e3d6e80b000000b02a0a026090220681805814048100380c018040082107c1d0263c6e40b00000,0x1088200781c0681805814048100380c020040082d09c2501e406f40b000000b0220801e0701a06016050120400e03008018040082b0a4270963f6f00b000000b028090200781c0681805814048100380c,0x10082d0ac29026437000b000000a0260801e0701a06016050120400e03008018040082d0ac2508e426fc0b000000a8240801e0701a06016050120400e03008018040082d0a42708e416f80b000000a828,0x1090220801c060140400c020060081f06c1704c0f016457080b000000b02a0a026090220801e068140480e020060101d064170440d00e447040b0000009824088200781c0681805814048100380c01804,0x103c0d01e487140b000000b028090200781c06818058140400c020060082b09c2304c0f016477100b000000b02a098200781c06818058140480e0200601029094230440d00e4670c0b000000b02a0a026,
0x1050120400e03008018040a42508c1d0641700e4a71c0b000000b02a0a02609022068180580e03006010020841f0741504c11026497180b000000b02a0a026090220781c0581204008010020841b06415,0x101e4d7280b000000a828088200781c068180581204008010020b4270941503c0d01e4c7240b000000b0280902007018050120400e03008018020ac2708c1f06c170164b7200b000000b02a098200781a,0x10400e03006010020b42b0a42107c1d0264f7300b0000009824088200781c068180580e03006010020b42b0a41504c110264e72c0b000000a8280881e07016050120400e03008010020b4270942106c19,0x173c0b000000b02809020070180501003008018020ac2708c1f06c1704c0f016517380b000000b02a098200781a0501203808018040a42508c1d064170440d00e507340b00000098240881a0601605012,0x10381c20008364000b42b0a421056547440b00000098240881a060160380c018040082d0ac290841f0741504c11026537400b000000a8280881e0701604810020040082d09c250841b0641503c0d01e52,0x105654020d9070800780e01c3306c3a0341c03c270143208c510945209c530642005c0600c500002d0ac29084dc94c1017412280070cc1b0e80d0700f09c050c823144251482714c1908017018031401e,0x101c3306c3a0341c03c270143208c510945209c530642005c0600c50074c807cd4084dc0002d0ac290525690c088c8000801e0701a0601605022098290080e0302b018040b424048109564f04cb40447f,0x106486054b800c7e09cd5084d20a4dd0002d0ac2495e4e0405d02143049320525607cd4074c8084dc05c060642009c530945208c5100c5001c3306c3a0341c03c27014320002d0ac293765504cb40447f,0x195c031f82735419218173301103c1d32421348152e01f34c132e8092e4293740d0701b0e80f09c070cc050c8000b42b08e1f08d3a01c3306c3a0341c03c270143207cd3074c9024b90440f05ccc04cba,0x10902a0601e0701a048160400e0200c008060102d088209661c08d370842b0547c05c0600c1b07c1e0741d0440f04c22024210ac23034ce03cdb01cda0146806c5b064bb0002d0a02609658908224ec24,0x10200c008060a02d098049725a08259000260902a0601e0701a048160400e0200c008060a02d0102296e300521a00028098240781c068180582a048100380803002018040b4220865a79c15864000a026,0x10f02311426124000b4280906997025960051a00f36c1b16c073680d338192ec170180306c1f0781d0741103c13088090842b08c000b4280984986c21418152b42296c000902a0601e0701a048160400e,
0x1124000b4280680e97a4001a3100028088200781c0681805814048100a82502027010020b40e0325d874191100d070214341542c1b5180f45807454170180306c1f0781d0741103c13088090842b08c05,0x111021314170180306c1f0781d0741103c13088090842b08c050f02311426124241a4000b428068de974153100d070170180306c1f0781d0741103c13088090842b08c050f0231141911021314241a426,0x10440f04c22024210ac230002d0a0df9480c17014300170180306c1f0781d0741103c13088090842b08c050f0231140632c241a4201101816c1a37826124000b42803e5f9300c170064f8144d80e97819,0x12740f0602531c170180d19c190800306c210381f0781d074051a01b068150642837c2b08c000b4279824d054c40341c03e5f08044018cb0605b068de0906908c450143c0984905c0600c1b07c1e0741d,0x131c1b068150640f060072742837c1103c130881f07817018090841d0740306c000b42a9893808a1e000040801e0701a0601605012040080080e030290182a0b42409a61904224e41103c130880908407,0x10002a0801e0101a06016050120080e03008018260a42407264840227942d004000902a0801e0101a06016050120080e03008018260a41c042639882b08c000b40198427980051a021038190800d19c25,0x1004000a829098240ee6508c390726400020078040681805814048020382a02006098290302499a2c0420f0b40100026090220801e06818058140480c038080a4060102a0081d9960e08cc3042630b401,0x1004000a829098180580c00a68844238b42d00400098200781c06818058140482a0380c02006010250a41000a67998190800d19c0543c172d403520070b01b06815064210381307c090b40f0601f0982d,0x1074760890e0445400a6801c2c06c1a054190840e04c1f0242d03c1807c26014430903b0b4010002a0a426060160326999c1d0bc11220070b01b06815064210381307c090b40f0601f0980510c240ec2d,0x10b4010002a0a4260326b0bc1c31803058169a8240ec000a82909818382460409e0743508910008670326901c2c06c1a054190840e04c1f0242d03c1807c26014430903b0b4010002a0a426060169aa3d,0x100820060e0014430903b01c2c06c1a054190840e04c1f0242d03c1807c260b4010002a0a4269b24a0445401c2c06c1a054190840e04c1f0242d03c1807c26014430903b088b6070640581700820060e0,0x10400803027018040081a03a6d848112c0254b4234b01d2cc192c8172c40d2bc053d0033cc269b00f0601307c210381f0981b06815064090b4070b02d004000a82900a50040bd0326b0581707064088b6,
0x1000280902a0801e0701805814048100200c01827010020881b9be0a08cac03a6d0b401000280801e0702a06016050120400803027018040082406a6e790238302d004000a0240801e0702a0601605012,0x10b4010002a09c03834234ac1b1f40f1ec249c02d004000781c0a81805814048100200c09c0601028080029c66f08c7a06a6e000200781c0a81805814048100200c09c0601028008249c22b03a0b0b401,0x1030040202005006040259ce09089e30b40100028098200781c0681805814048100a80c0200601002038259ca710254a0854c0554b044b001d4907c8904cd701547074b3064b205cb1034af00d0a0a402,0x1098200781c02018058140481001002030060a02a0901a9d5e2089d20b40100024098200781c02018058140481001002030060a02a0680e9d27206c7d03c7b0a40209c030b4010002a060160081c07812,0x10202005006042789d8231e81a9d4000801e070080601605012098040080c018280a810092777780f7d02d004000a026090220801e07018058140482a03008018040081006e76760232b00e9d02d00400,0x1042780a40209c030002a060160081c078120300402020050069e9d903dea0b4010002809824088200781c04418058140480c0202a010020181a9e677096730a40209c030002a060160081c0781203004,0x176c2d004000a026090220601e0701a0481601815030080a804008200427c7540f17025420234101b1d01127c069e8290082700c2d004000a818058020701e0480c01008080149ee7906c750948808cc3,0x10002a060160081c07812030040202022e7d0427c00026090220601e0701a0481601828030080a804008150827e88c0e7c02d004000a026090220801e0701a0601604815030080a804008060467d7bc0e,0x10942b09c0308c470443f0808b0002a060160081c078120300402015384cd01a000b40100028098240881e0702a06016048100380c0202101002068159fe7e01ccd0947c08cad06ca50527b0a40209c03,0x10b40100028098240881e0701805814048100380c0202a010020841ba05e101caa0a40203c5a0942b09c0308c470443f0808b054e10b4010002a060160081c07812030040201aa027f06ca50a40203c5a,0x142423414211e01b28c0f3dc073bc08a08290082700c2d004000a818058020701e0480c01283a041aa0015384110fc2311c250ac0f1682022c290082700c000a818058020701e0480c01008a087401a03,0x11a82d004000a818058020701e048113893f040f50000d08805231d40950708d03084a906c73054fb044f803c71024ee01ced012830a40209c030b4010002a060160081c078120306a758113e41528025,
0x10701a0601604012034080a8040081401a857a00e75c2d004000a026050220801e0701a0601604012034080a80400806092847a41b1d40f45c252201546c210fc0727c2700c0922805230231e4290080c,0x10002809824088200781c06818058120402a0200d0100205406a1e8501cf609c030248a0148c08c790a402044e206ca40306a0002a060160081c0781208014a1a0703c7b092840b401000260a0220801e,0x10002a060160081c078120828aa2006a1c0009824088200781c0a018058120402a0200d0100206815a24fc03e340b401000280980d088200781c068180581204008010020542a09007a2222039ee0b401,0x1a31eb056240b4010002809824088200781c068180582a0340801804008130400ea2cab03c5a0828a0306a00018058020702a0781212a890947c0528606ca409c030248a0148c08c790a4020306a044e2,0x1a300925c0525829008210dc250e01b0d00711823100121282700c2d004000a818058020701e0348da2c1146429008210dc250e01b0d007118231002700c052580925c12128000a818058020701e0340e,0x147011468093c029008210dc250e01b0d00711823100121282700c0d234000a818058020701e03ce3884047b02d004000a026090220801e0701a06016050100302a018130080803e8d8cc10460153c40e,0x102290a380917429008210dc250e01b0d007118231002700c0d234051540f38c12128000a818058020701e0428f7c4147682d004000a026090220801e0701a0601604c0e0302a01804008080428ea3415,0x1128290082700c000a818058020701e1ae35050fa022900b40100026090220801e0701a060160440e030130a02a0080601291894147b42d004000a026090220801e0701a060160440e030130182a00804,0x10081c0801aa49fb014550843706c3401c570245803c3608c2a09c0309462034480a4020443e054590786b0b4010002a060160081c04c8ea4410a3c051540f38c0d23407118250e023100210dc1b0d012,0x11600f0d8230a82700c251880d12029008110f8151641e1ac132382d004000a8180580207020a4de00147701c570245803c3608c2a09c0309462034480a4020443e054590786b04c8e0b4010002a06016,0x1238110f80d12025188230a8151640f0d8091600715c1e1ac290082700c000a818058020706c3041a8142d004000a0260902207012060160501007c0e030080182a00804086947f8051cc1aa480715c09,0x10580207c12a5dff024be086950b401000260902206818058140a01d0380c018040082a07c12042968a4098f02d004000a0260902206818058140481d0380c018040082a07c1008695a50052a420a4c13,
0x12f8082141440412a5c1b2fc290082700c051580d0d407180230e40f198250bc1c1b02d004000a8180580207ce4a58110f815488290082700c051580d0d407180230e40f198250bc1b2fc1c1b0000a818,0x10fc290082700c051580d0d407180230e40f198250bc1529c13214092981f3901c1b0000a81805802046991d41a7dc2d004000a026090220a81e02018058140480e0301d0180400820046989241017420,0x10880e0301d018280a80400a9c49c1a8102d004000a026090220781006016050120200e0301d018040a8020869b7e81a77c2d004000a0260901e0400806016050120880e0301d018040a8020829aa6021,0x11d8212a01b2880223c2d004000a8180581e0329da7011a64132141529c092981f390250bc0f198230e4071800d0d4051581c1b0290082700c000a8180580223e9b0829a000260901e040080601605012,0x10409e0329d084a806ca209c030149301c9402495094d604ccf03cbc054d008cc20a402074760088f0b4010002a0601607a9e74c111502700c0524c0725009254253581333c0f2f01534023308290081d,0x108c2a09c03024700746109409058280a4020002a0601f06c12a8237012270b401000280982408820070180502a0401b030080181f008170480ea7cc1081200690207a9e0088f0a4020002a060160a220,0x10a02d004000a81807c4b914045040e0b812a80110900d05403058150942121007194230a82700c091c01d18425024160a0290082d004000a81807c1ba869f03c42044240341500c16054250848401c65,0x10801a072a3770238182d004000a026090200781706818050120400e030080a80400806072a27f00f4f0133fc051dc1ba841d184091c00719421210230a82700c110900d0540305815094250242900816,0x109c03044240341500c1605425094090a4020144104c2e03c3d07c4b058280b4010002a0602006aa4a88073f82700c110900d0540305815094250242900805104130b80f0f41f12c09284160a0000a818,0x101c9a080e5058280b4010002a0601ba95f501c740751d08c7a024a306aa409c03044240341500c1605425094090a4020144104c2e03c3d07c4b058280b4010002a06020395f801d4408c39072a3024a1,0x11e02311c20394130b8051040f0f41f12c15094250240d0541109003058160a0290082700c2d004000a81804a3a0712509c03044240341500c1605425094090a4020144108c4704c2e03c3d0247807c4b,0x10144e03c4204c1009c030546301c4f06c5f094090a402044d106012034150002a05c0207aa78981c7cc2d004000a026090220a80c0081a050120400e05c08018040642007aa68041d4981ba940726809,
0x10601207c9808499008e60b4010002a05c0caa23b0811f0746107aa703415044d10241108c0d0144e03c4204c1009c030546301c4f06c5f094090a402060120b4010002a05c0239aa6085240241108c0d,0x12641f2601c190023981b17c1518c0f108250240713c0513813040090442700c2303418048290082d004000a8170c236044540241108c0d0144e03c4204c1009c030546301c4f06c5f094090a40207064,0x1040090442700c23034290080305c110a4170c00720405208151780f1c818048000a81e0801a036aa7c8258a82d004000a026088200781005819050120a80e02006010020680d072a9910102f40caa021,0x1048000a81e0801aab5f90942f072ab0b401000280a8220801e00816050120400e01008018190981a032ac820247742d004000a01a0a8220801e00816050120400e01008018190980c072abaa41d0d413,0x10c0180482d004000a81e080905080c7d82d004000a026090220801e07016050120400e018080642a0080406eaeab00daa813040090442700c23034290080305c110a4170c00720405208151780f1c818,0x10a4020002a0781b03ab08a0078e42d004000a00e090220781c0581b0481008419020040082a0980c052afab81d478251f41aab41517805208072040f1c813040090442700c23034290080305c110a417,0x1060120a4020002a0781bac85c036480b401000280980f0881e0701604810020040082106c190a82405407ac6af034ab0545e04c100241100c170442905c30014870942b09c03074830809008c0d06012,0x12a81bac81d20c0521c250ac2024013040090442700c23034290080305c110a4170c0180482d004000a81eaceb1018ca050c003ab004c100241100c170442905c30014870942b09c03074830809008c0d,0x10002a012380712106ab40b40100026090220800c07c16050120400e0080801804064280aab548c1c7f42d004000a026090220800c07c16050120400e00808018040642a06ab48080f3280d5001540007,0x10740500021029110a804074050000d04d4e0b4010a8040000901d140b4010a8040001d016b5094ae05545014f20344801c650852803c3607ab30442900c1705c3008c0d0241104c100601209c030a402,0x101c140840a0a804000260901a0581f038040082808ab64f42244c051cc2a010000581b130860a80405408000190307f0a804054080001102d4d0a8040840a000070514f0a8040240700015020800a804,0x10201102c0d04c0901c070502a010000a0220101e068160380209824adeb609c8908d2a01477094ae0a42603c3606c4c0440b0b401000160081f1b61404e2e0b401074050640c054080440b0240703413,
0x10240701c140a804000040781a0580e008220a0e7858130e024adc2d004210281d01419030150201102c0d04c0901c070502a01000088040781a0580e0082809ab87981384c2d004210281d0141903015,0x10a426aea3f0913504c1f0a0e703c2706c4c07c6d0a80401c1402407034130440b054080640c074050840a0b401000160080408827ae61704cd70953109ab80b4010840a074050640c054080440b03413,0x10a804000240781a05812038040082808ebcae827ae41307c2839c0901c000781a0580e0080408abb4d024860210281d01419030150201102c0901c0d04c070502d0042a010000881e068160480203804,0x1004000580203abeaf40f09c1b1301f1b42a0100005802010e8af0294cc254b8134a422aec2d004190302a01000068160780203804af61509e2f0b4010840a074050640c054080440b034130240701c14,0x107c6d06c4c0a80401c1402407034130440b054080640c074050840a0b4010001600abf8f8131541b1301f1b42526c29270222dc26360043a02a010070500901c0d04c1102c15020190301d014210282d,0x13a4890786e0984d000041bd30058310984d0001e1b8c6074050583100025249120a8040583100026136bf00c91000160c47e09d2f0a8040b40100003246470487103abe098d8088b70a49c0949b010e8,0x1058310786e088e90984d0a80400c9101c1402407034130106f0440b068eb054080640c074050840a094920a4ea0b4010000e3b0fd058310106f0001a3acb50583109492000293a90c0786e0984d00022,0x19442d004293a825248210281d01419030150201102c0d04c0901c07050032442a01026134223a41e1b81a3ac160c4041bc12b000e3b000b04710106f038ec00012b024b04c2e
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check16 : ¬ FormulaSat (caseFormula c16) := checkW_sound _ k16 10 w16 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good16 : caseGood c16=true := by decide +kernel
theorem next16 {chosen region} (disj : ∀ i∈c16.prior, chosen i=false) (O : Later c16.prior chosen region) : ∃ g∈c16.groups, Matches chosen g := case_conclusion _ good16 check16 disj O
def c48 : Case := ⟨[5, 6],[5, 6],[
s0,s1,s2,s3,s4,s5,s28,s31,s44,s47,s103,s177,
s178,s186,s200,s242,s304,s324,s916,s917,s1031,s1073,s1247,s1513,
s1578,s1645,s1646,s1722,s1723,s1724
],[
t9,t10,t14,t15,t17,t19,t22,t23,t24,t25,t26,t27,
t29,t31,t32,t33,t35,t39,t41,t42,t43,t44,t48,t49,
t50,t51,t52,t53,t54,t58,t59,t60,t61,t63,t66,t67,
t69,t71,t72,t75,t76,t79,t80,t81,t83,t84,t85,t86,
t87,t88,t89,t90,t91,t93,t94,t95,t97,t99,t100,t101,
t102,t103,t105,t106,t112,t113,t114,t115,t116,t118,t119,t120,
t121,t122,t123,t126,t127,t128,t129,t130,t131,t132,t133,t134,
t135,t140,t141,t142,t143,t145,t146,t147,t148,t150,t151,t154,
t155,t156,t158,t159,t160,t161,t169,t182,t185,t186,t188,t189,
t190,t191,t192,t193,t195,t197,t198,t199,t200,t201,t203,t207,
t208,t209,t210,t211,t212,t213,t214,t215,t216,t217,t218,t219,
t221,t224,t227,t228,t229,t232,t234,t235,t236,t238,t239,t240,
t242,t243,t245,t246,t247,t248,t249,t250,t251,t252,t253,t254,
t255,t256,t257,t258,t260,t261,t262,t270,t271,t277,t279,t280,
t281,t282,t283,t284,t285,t286,t287,t288,t297,t298,t299,t308,
t311,t315,t321,t326,t328,t329,t330,t331,t333,t335,t336,t337,
t340,t342,t344,t345,t346,t348,t349,t350,t351,t352,t353,t354,
t356,t357,t359,t360,t375,t376,t377,t378,t379,t380,t381,t382,
t383,t384,t385,t386,t387
],[
g0,g1,g2,g4,g8,g64,g128,g256,g512,g1024,g2048,g4096,
g8192,g16384,g32768,g65536,g131072,g262144,g524288,g1048576,g2097152,g129,g192,g320,
g384,g576,g640,g768,g3072,g4160,g5120,g6144,g8320,g9216,g10240,g12288,
g16640,g17408,g18432,g20480,g24576,g33280,g33792,g34816,g36864,g40960,g49152,g66560,
g133120,g196608,g262208,g266240,g327680,g393216,g524416,g532480,g589824,g655360,g786432,g1048832,
g1064960,g1114112,g1179648,g1310720,g1572864,g2097664,g2129920,g2162688,g2228224,g2359296,g2621440,g3145728,
g322,g448,g580,g704,g896,g11264,g21504,g38912,g57344,g266304,g532608,g720896,
g1065216,g1376256,g2130432,g2490368,g3670016,g904,g11265,g21506,g30720,g38916,g46080,g52224,
g57352,g720897,g1376258,g1966080,g2490372,g2949120,g3342336,g3670024,g11393,g721025,g21826,g39492,
g1376578,g2490948,g58248,g732161,g1397762,g2529284,g3670920,g3727368,g732289,g1398082,g2529860,g3728264
]⟩
def k48 : List Nat := [
1,2,199,200,201,96,66,202,203,204,205,206,
122,67,68,123,124,207,125,208,209,210,97,69,
70,51,126,41,42,71,72,73,98,211,212,127,
128,213,214,99,215,74,216,217,43,129,44,130,
218,219,220,131,100,132,221,75,101,222,133,134,
135,223,76,77,78,136,32,52,137,138,139,140,
53,224,225,226,141,227,79,102,142,103,143,11,
144,228,229,104,145,80,105,18,106,230,45,231,
146,232,233,147,148,107,234,235,236,54,55,37,
149,38,56,81,39,33,20,108,150,237,109,151,
110,152,238,111,21,239,153,240,15,154,155,82,
22,23,241,83,242,243,46,34,156,244,245,157,
246,247,248,249,250,251,112,84,252,253,85,254,
255,256,158,257,258,259,260,159,113,261,160,161,
262,114,263,264,265,86,87,266,267,268,269,88,
270,271,272,273,57,58,274,162,275,163,276,277,
164,47,165,278,166,279,167,280,24,281,115,282,
59,35,116,168,117,283,169,284,25,285,170,171,
16,172,26,173,174,175,286,176,177,178,89,287,
288,289,179,90,290,180,91,291,92,292,36,48,
293,294,295,296,297,298,299,181,93,182,27,183,
28,300,301,302,303,304,305,306,307,308,309,310,
311,312,313,314,315,316,317,318,319,320,321,322,
323,324,325,326,327,328,329,330,331,332,333,334,
335,336,337,338,339,340,341,342,343,344,345,346,
347,348,349,350,351,352,353,354,355,356,357,358,
359,360,361,362,363,364,365,366,367,368,369,370,
371,372,373,374,375,376,377,378,379,380,381,382,
383,384,385,386,387,388,389,390,391,392,393,394,
395,396,397,398,399,400,401,402,403,404,405,406,
407,408,409,410,411,412,413,414,415,416,417,418,
419
]
def w48 : List Nat := [
0x105814048100380801802015a54b00d0040b000000b02a0a026090220801e0701a06016050120400e02006010036912b0340102c000002c0a82809824088200781c0681805814048100380801804009a3,0x10a82809824088200781c0681805814048100380601002025a74b80d0040b000000b02a0a026090220801e0701a06016050120400e02004008076992d0340102c000002c0a82809824088200781c06818,0x1008136a9310340102c000002c0a82809824088200781c06818058140480e0200601002045a94c00d0040b000000b02a0a026090220801e0701a060160501204008018040080f6a12f0340102c000002c,0x10701a06014048100380801804008176b1330340102c000002c0a82809824088200781c06818058120400e0200601002055ab4c80d0040b000000b02a0a026090220801e0701a06016050100380801804,0x1000000b02a0a026090220801e07018058140481003808018040081b6b9350340102c000002c0a82809824088200781c06816050120400e0200601002065ad4d00d0040b000000b02a0a026090220801e,0x10200601002085b14e00d0040b000000b02a0a026090220801c06818058140481003808018040081f6c1370340102c000002c0a82809824088200781a06016050120400e0200601002075af4d80d0040b,0x10801e0701a06016050120400e0200601002095b34e80d0040b000000b02a0a026090200781c0681805814048100380801804008236c9390340102c000002c0a828098240881e0701a06016050120400e,0x10340102c000002c0a826090220801e0701a06016050120400e02006010020a5b54f00d0040b000000b02a0a024088200781c0681805814048100380801804008276d13b0340102c000002c0a82809822,0x1050120380801804044036e13f0340102c000002a0a026090220801e0701a06016050120400e02006010020b5b74f80d0040b000000b02809824088200781c06818058140481003808018040082b6d93d,0x10a026090220801e0701a0601605010020060100204c0f6e9410340102c000002c0a82809824088200781c068180581404808018040081103db95000d0040b000000b02a0a026090220801e0701a06016,0x1045bd5100d0040b000000b02a0a026090220801e0701a060160481002006010020540f6f1430340102c000002c0a82809824088200781c0681805814038080180400813045bb5080d0040b000000b02a,0x1068140481003808018040081905dbf5180d0040b000000b02a0a026090220801e0701a060160400e0200601002054136f9450340102c000002c0a82809824088200781c0681805812038080180400815,
0x10002c0a82809824088200781c060140481003808018040081b05dc15200d0040b000000b02a0a026090220801e070180581404810020060100206c0f701470340102c000002c0a82809824088200781c,0x101002074177114b0340102c000002c0a82809824088200781a060160501203808018040081d045c35280d0040b000000b02a0a026090220801e07016050120400e020060100206c19709490340102c00,0x10801e06016050120400e02006010020741b7194d0340102c000002c0a82809824088200781a058140481003808018040081d065c55300d0040b000000b02a0a026090220801e06818050120400e02006,0x10040b000000b02a0a026090220801c06818050120400e020060100207c177214f0340102c000002c0a82809824088200701a060160501003808018040081f04dc75380d0040b000000b02a0a02609022,0x103808018040081f075cb5480d0040b000000b02a0a026090220801c06016050120400e020060100207c1b729510340102c000002c0a82809824088200701a058140481003808018040081f065c95400d,0x1098240881e0701a060140481003808018040082105dcd5500d0040b000000b02a0a026090220781c06818058120400e020060100208415731530340102c000002c0a8280982408820068180581404810,0x1741570340102c000002c0a828098240881e07018058140481003808018040082106dcf5580d0040b000000b02a0a026090220781c06816050120400e020060100208419739550340102c000002c0a828,0x1050120400e020060100208c17749590340102c000002c0a828098240881c06818058140481003808018040082107dd15600d0040b000000b02a0a026090220781a06016050120400e02006010020841d,0x10b02a0a0260801e0701a06016050120400e0200601002094237515b0340102c000002c0a828098220801e0701a0581404810038080180400825065d35680d0040b000000b02a0a026090200781c06818,0x10082708dd75780d0040b000000b02a0a024088200781c06016050120400e020060100209c1b7595d0340102c000002c0a828090220801e0701a060160501204008018040082703dd55700d0040b00000,0x10701a0601605012038080180400829045d95800d0040b000000b02a0a0220801e0701a06016050120400e020060100209c257615f0340102c000002c0a828090200781c0681805814048100380801804,0x102c000002c0a826090200781c06818058140481003808018040082908ddb5880d0040b000000b02a09824088200781a06016050120400e02006010020a41d769610340102c000002c0a826090220801e,
0x102006010020ac13779650340102c000002c0a824088200781c06818058140481003808018040082909ddd5900d0040b000000b02a098220801e0701a06016050120400e02006010020a4257716303401,0x10801e0701a06016050120400e02006010020ac23781670340102c000002c0a026090220801c06818058140481003808018040082b07ddf5980d0040b000000b02809824088200781c06818058140400e,0x15a80d0040b000000b028090220801e0701a06016050120400e02006010020ac27789690340102c000002c0a026088200781c06818058140481003808018040082b095e15a00d0040b000000b02809824,0x10481003808018040082d085e55b00d0040b000000a82809824088200781c06818058120400e02006010020b4157916b0340102c000002c09824088200781c06818058140481003808018040082b0a5e3,0x10a026088200781c06818058140481003808018040082d095e75b80d0040b000000a828098240801e0701a06016050120400e02006010020b4237996d0340102c000002a0a026090220781c0681805814,0x10b42b7a9710340102c000002a09824088200781c06818058140481003808018040082d0a5e95c00d0040b000000a828090220801e0701a06016050120400e02006010020b4277a16f0340102c000002a,0x10701a060160500801804008130440f7b1730340102c000002c0a82809824088200781c0681805814040080180204c0f015eb5c80d0040b000000a026090220801e0701a06016050120400e0200601002,0x1000000b02a0a026090220801e0701a060160480801804008150440f7b9750340102c000002c0a82809824088200781c068180581204008010020540f01ded5d00d0040b000000b02a0a026090220801e,0x10100207c1b05df15e00d0040b000000b02a0a026090220801e068140481003808018040081d064177c1770340102c000002c0a82809824088200781c068180580e020060100205413045ef5d80d0040b,0x10881a06016050120400e02006010020841f075f35e80d0040b000000b02a0a026090220781c058140481003808018040082106c197c9790340102c000002c0a828098240882007018050120400e02006,0x10340102c000002c0a826090220801e06818058140480e02006010020a41d045f55f00d0040b000000b02a0a024088200781c060160501204008018040082706c0f7d17b0340102c000002c0a82809824,0x103808018040082b09c237e17f0340102c000002c0a026090220801c06818058140400e02006010020ac1f04df75f80d0040b000000b02a098200781c068180581404810038080180400829094237d97d,
0x1088200781c06818058140481003808018040082d09c257e9810340102c000002a0a026090220781c06818058120400e02006010020b421055f96000d0040b000000b028090200781c068180581404810,0x100dfd6100d0040b000000b02a0a026090220801e0701a06016038060100205413044097f1830340102c0000026090220801e0701a06016050120400e02006010020b42b0a5fb6080d0040b000000a828,0x10481003808018040081f0741b065ff6180d0040b000000b02a0a026090220801c0601404810038080180207c1b05c057f9850340102c000002c0a82809824088200781a050120400e020060101d06417,0x10002c0a828098240881e06014048100380801804008210741b05e016200d0040b000000b02a0a026090220781c058140481003808010020841b06407801870340102c000002c0a828098240882005814,0x10a42508c038118b0340102c000002c0a828098240881a06016050120400e018040082107c1d026036280d0040b000000b02a0a026090220701a050120400e02006010020841f06417809890340102c00,0x106016050120400e02006010020ac2909c258198d0340102c000002c0a0240801e0701a06016050120400e020060082b09c23016056300d0040b000000b02a098200781c0681805814048100380801804,0x10040b000000a8240801e0701a06016050120400e02006010020b42909c238218f0340102c000002a0a0220801e0701a06016050120400e020040082d09c2501e076380d0040b000000b0220801e0701a,0x1018040741905c1100e0b6480d0040b0000009824088200781c06818058140481003806010020b42b0a409829910340102c0000028098200781c06818058140481003808018040082d0ac2508e096400d,0x109824088200701805010020060081f06c1704c0f0160d6500d0040b000000b02a098200781c06818058140480e02006010290942304403831930340102c000002c0a82809824088200781a0501203808,0x1841970340102c000002c0a0240801e0701a0601605010020060082b09c2304c0f0160f6580d0040b000000b02a0a026090220781c0581204008010020841b0641503c07839950340102c000002c0a828,0x10200601029094230741905c03849990340102c000002c0a828098240881a0601603806010020841f0741504c11026116600d0040b000000a828088200781c068180581204008010020b4270941503c07,0x10a8280881e07016050120400e020040082d09c250841b064078519b0340102c000002c0a0240801c060140481003808018020ac2708c1f06c17016136680d0040b000000b02a098200781a050120400e,
0x105c1100e176780d0040b00000098240881a06016050120400e018040082d0ac290841f074098599d0340102c0000026090220801e0701a0601603806010020b42b0a41504c11026156700d0040b00000,0x104008010020b4270942106c190540f01e196800d0040b000000b028090200701805010020060082b09c2307c1b05c1303c058619f0340102c000002c0a8260801e068140480e02006010290942307419,0x111427120170dc2511c19140231181e04c1c1b8082d0000b42b0a4210561b6880d0040b00000098240881a0601603806010020b42b0a42107c1d0541304409869a10340102c000002a0a0220781c05812,0x10a4020382b018040b424048108721604c940446c0561b020b40706e0781301c2903c2306c2f0142800c4509c4805c37094470645008c460002d0ac29084b78681014812188070a40f08c1b0bc050a003,0x1114070a40f08c1b0bc050a0000b42b0a4b887013250111b0070a40f08c1b0bc050a00311427120170dc2511c19140231181d2881f2c0212dc000b42b0a4148760a021fb000200781c068180581408826,0x144c070a40f08c1b0bc050a01f2bc1d29009260110381729c13264191cc15258031ac272c4212b8292e0000b42b0921e854101480847012430148741f2c01d288212dc19140170dc271202511c2311803,0x106c090682b0700f2d8072d4051701b14419268000b4280982587e09089140921e00c6b09cb10647305ca70440e074a4084ae0549607caf04c99024980a4b806c2f03c2301c29014280002d0ac1c7a823,0x1794000a0260901e0701a060160a8120400803802018040b422086216dc15790000a0260902a0601e0701a048160400803802018040b4220822079c23440210b0151a017060030501f0581d0541103813,0x10440e04c1b0241a0ac1c0002d0a0260ede60848f0546508a22000240a8180781c06812058100200e008060a02d0980488e2108220000260902a0601e0701a048160400803802018280b40408a227e414,0x10440e04c1b0241a0ac1c0143208c390983b0002d0a02417438061e800028090220801e0701a018160a81204004020270082d0500e892230961f0145c03cb606c5101cb50649a05c1800c1407c1607415,0x10682b070050c8230e4190e02128024174260ec000b4280680e89a07019fa00028088200781c068180582a048100940809c040082d0500e89624084e9054e806d1d03cef01cee05c1800c1407c1607415,0x12e4260ec000b42803e27840064541443c0e898190e02128017060030501f0581d054110381306c090682b070050c8230e4260ec24174000b428068b98941527c17060030501f0581d054110381306c09,
0x106051068b90905d08c39014320983b05c1800c1407c16074150440e04c1b0241a0ac1c0002d0a0ba8641415017060030501f0581d054110381306c090682b070050c8230e40629424174200e0181441a,0x1058140481002002038290182a0b42409a2982022448110381306c09068071f40f09025284170601916c030502104c1f0581d054051701b09815094282e82b070000b4278a2140549f03e2708038018a5,0x10080e0200609829070108ae2a0ac1c0002d00a2909e280145c084130645b094a106c260542503c2401c7d0a0ba0440e04c1b07c1605c180241a0741500c140002d0aa2a444227a400010200781c06818,0x10b40200026090220801e06818058140480e02029018040a8020762d76423388108ac2d008000a8200780406818058140480203808018260a4240722c76c226d42d008000902a0801e0101a0601605012,0x109429040028be2e0645b05c37014eb00d2201c3506c26054250841304c2e0243603c2407c200b4020002a0a426090758b4232381c8b0000801e0101a06016050120a80e0200609829008248b9f5041da,0x102006010290940308e318bc1d164112c81916c070d41b098150942104c130b8090d80f0901f080051c4241d42d008000a8290981600a30770237d82d00800098200781c06818058140482a0380801804,0x10102909423074190a81700e338c41d1c019204223a8028c0070d41b098150942104c130b8090d80f0901f080051c4241d42d008000a829098168ca0c042040b402000260801e0701a06016050120a80e,0x1094090d8070d42d008000a82900e330607000859088e50710605a32014710907501c3506c26054250841304c2e0243603c2407c200b4020002a0a4268d212046170b402000260801e068140480e02006,0x10400809c06010020901a8d9b408dd70b40200028090200781c0a818058140481002027018040081a03a35774112441d298254202341c1924c172480534403340268d00f090130b82104c1f0801b09815,0x108c6606a36000200781c0a818058140481002027018040a002092387d00e7582d008000a0240a8200781c06016050120400801827010020881b8ddd508c8c03a350b402000280801e0702a0601605012,0x10963a8e4094942149c154981d29811244074901f168132cc054841924c17248033982900c2d008000a827011d808d0506c6903c90092380b4020001e0702a06016050120400809c0601028080028e637,0x102018058140481001002018280a81a03a3c8e81b1a40f2402900c270102d008000a81e058120100202020050180181c040258edd4089b30b40200028098200781c0681805814048100a808018040080e,
0x10923f6b80f7002d008000a026090220801e07018058140482a02006010020401b8f9a808c8c03a3c0b402000260801e07008060160501204004008060a02a0901a8f5b2089a30b40200024098200781c,0x1008000a026090220801e0702a060160501202006010020441a9063f0963b0a40309c040002a0781604804008080801406006070109023e08c6606a3d000200781c02018058140482601002018280a810,0x1038080a80400806042444781a70c2d008000a026090220801e07418058140480e0202a010020181190e4106cdc094b208d18042400a40309c040002a0781604804008080801406006072426a40f6e42d,0x108c700945903d1f072420a40309c040002a078160480400808080140600691a440464300026090220801e0741805814048280202a0100203806915c6069af0b40200028098240782008818058140481d,0x10401902002010260702492647094e408ce00748506c83044d301a460a40309c040002a07816048040080808014062483480e6982d008000a026090220801e0701a06016050120a804020020400791e45,0x10b402000280982408820078060581404810038080a804008190764b74c1b1a4249242d008000a806088200780e05814048100a00800804098190724a7081a6b42d008000a02a018220801e0381605012,0x10541001e4d26c062a00008015064bc9300726c0f1502323411368189202900c27010000a81e058120100202020050bb92c251641c92800018220801e03816050120a828020020102604019930f7069c5,0x10701a04816018150202a010020801093e4d044cc0a4030744b0946809c0406c6408c65064bc050bb0002a07816048040080808007938d503ded0b4020002809824088200781c06818058120a80801002,0x101002020200f2500424f00026090220601e0701a04816018280202a0100205420945ee039bd0b4020002809824088200781c0681805812054080a80400806046506f00e6ac2d008000a026090220601e,0x1048040080805476730072240f22c1b1902900c250b027010230e8110d0200f01d12c2d008000a81e0581201002020150625294407938231941b190192f0251a01d12c142ec2900c27010000a81e05812,0x195200068d90a4030942c09c04044340749d08c3a0803c03c54054760b4020002a0781604804008080640794e0e038f4018a8068db062520744b0a4030942c09c0408c3a044340803c0b4020002a07816,0x10402202021010020181c95a5401e5303c540749d0a4030942c09c0408c3a044340803c054760002a078160480400808066557c81a7382d008000a026090220781c03816050120402a020210100206406,
0x106c8301a57000240782a038180581404810088260a00400808086587401b4001c9582d00800098240782a038180581404810088080a0040082101a5773c1a6c42d008000a0260901e0a80e0601605012,0x11f8151881b2a80f458193cc2519c23384212281d21807324089642900c270102d008000a81e058120100296a5803c8b06655054760443408c3a0942c0803c0a40309c040002a07816048040080896489,0x1058121de5b074dd064810848803cf006c820551b0952008c9e0245f01cc700a5a0a40309c040002a0781604804971a4045b80b4020002809824088200781c06803058140480e020060a8040625b69c11,0x1024410a4030944f06c4a01c7200c7408c4e064580487709c040b4020002a07816014bd6941d210193d4212b0154641145c2538c2337c1b18c0f184091040732003318049702900c270102d008000a81e,0x10201497daa045bb0b4020002809824088200781c068180582a02013018040081403a5e7b0106e82d008000a026090220801e0701a060160a8080100604c020500f975eb07484084ac0387f054cd044cb,0x10525f000240882007826068180582a0a004018130081c022617bc106f82d008000a026090220801e0701a060160542a04c06010020200e9825e03e5d00026090220801e0701a060160a8280100604c02,0x132808988052f419160031d0071c82513c231381b128121dc2900c270102d008000a81e05830984212b41d28c2900c2513c1b128071c8031d02313819160121dc27010052f4000a81e0580898a6003cf1,0x1008000a81e0082206cbe7041d3d827010050b4130840f0a8150ac090c41105c071e41927025044160c02900c2d008000a81e0082206c2098caa068d808ccf00017024317f01014814350212281d2180f,0x13f40733827010050b4130840f0a8150ac250442900c090c41105c160c01b2f82d008000a81e00822086648041c3f82098c19270071e427010050b4130840f0a8150ac250442900c090c41105c160c02d,0x106a677c01c6fc2d008000a026090220801e0a806050120400e02002010170681999885070d70001e05c071e1ac075c40b4020002809824088200781a0a81404810038080080405c1801a657341d3fc19,0x101c78058300b4020002a078029a6670866406cbe09c040142d04c2103c2a0542b094110a4030243101c7804417058300002a0780208a6899818994000982408828078060a81404810038080080405c20,0x1058300a40309c040002a078107f41182c2d008000a026090220801e068140480e020060101d0642a05c039a9d20848f0748e06c660648d08a680441709c040142d04c2103c2a0542b094110a40302431,
0x13e40703c23028270101d14c250442900c1105c03108150640910c132000f2a4051241e0402d008000a817068209ae6a08488060d6070f206c8208c9e00a6901c78024310542b04c210142d0941103c2a,0x10b402000280982408820070180502a0401b0200605c0207c1203a6c80818404209ac0f2a413200051240703c23028270101d14c250442900c1105c03108150640910c1e0402d008000a817068bf72019,0x105c1d14c250440910c031082900c0703c230281e040270102d008000a81709e6c03cf801c0f08c0a09c040441700c4205419024430847c0646f068bf0745307810094110a4030002a05c129b5fe011f1,0x10626e0b402000260902208004038160501204028020060a81f06c029bcfc071ca0b4020002809824088200100e058140481006c080182a07c020626e834044680e084129b4191bc211f01a2fc1506411,0x103c1f05c2704433094220541900c4c0144d06c5e078100b4020002a02012080199c26f00cfa0850304c4a014630a40301c0f08c0a09c0403c1f05c27044330942205419078100002a0201b179ff0706f,0x108c0a09c0403c1f05c2704433094220541900c4c0144d06c5e078100002a020120827272c1c6c02d008000a0260902207c1a01016050120400e020060a802080189c5c9074fb0a40301c0f08c0a09c04,0x19c82900c0703c23028270100f07c1709c110cc250881506403130051341b1781e040000a80804a747cc1c7442d008000a026090220841a038160502a0400807c0601002048189ce71066700a40301c0f,0x11ec1c21c2519c27010202ac083001e0402d008000a8139d5c7074a3084ad0645804a740144d00c4c06c5e0942204433054190a40301c0f08c0a09c0403c1f05c27078100b4020002a020c09cc1940820,0x180c111f815188139d4202ac2519c1c21c1b1ec191e8051040317c083000f07c1709c0703c230281e040270102900c2d008000a80584410148143782900c0703c230280f07c1709c0317c05104191e81b,0x10580e07c280080408a761cc2a01415018000640d1b02a01415018000440c4a02a014210240001c0b4a82a0140902000054061b82a0141d01c00084094a42d0082a01400024083b42d0082a0140007407,0x118c041681a41026028229dc0007c16306760149509c6a06c9700c600a4200942203c1f0a805054060b4020001f058229dddf04df70b4020640d054060440c0240801c0b08409074070a805000260901a,0x100c600a80501c0b024080440c054060640d07407084090b4020001f04a1304c2100c600a420094220886a068490105a0986d058c10a80501c0b024080440c054060640d07407084090b4020001f03a78,
0x100c4406c55094560a4570a80501c0b024080440c0540605c1d0640d0740707c12084090b4020002309c043090a0986d07c120a80500017076180486103a78068490886a0105a0986d058c1094220a420,0x10301501817074190341d01c1f048210242d0080008c279ea0504c7f00c4406c55094560a457010c20a80501c0b024080440c0540605c1d0640d0740707c12084090b4020002309c0e9e5f804cb303c23,0x17800f08c131380548c279e82915c251581b154031102a0140702c09020110301501817074190341d01c1f048210242d0080008c1e83c121840e9e404308031101b154251582915c2a0140702c0902011,0x19f1b604dde0b4020143f08c1e0840907c120740706c3e0640d05c1d0540603c3d0440c0240801c0b0a80500026008280927b2542a01423078000143f25c2a014230780006c3e3b02a014230780003c3d,0x10f819034170741501811030090200f0f4050fc0702c2a0142d00800008269f5e104c4f0927b0b4020840907c120740706c3e0640d05c1d054060143f0440c03c3d0240801c0b08c1e0a8050000209828,0x1030133101501817074190341b0f81d01c1f04821024230782d008000a4c539c23078261000004cc44242d008261000000cc39f4031ac2a014000984078c130b825434289f023078210241f0481d01c1b,0x108c1e0840907c120740706c3e0640d05c1d054060143f0440c098400240801c0b00cc30a8050a4c50967e0027f42c261002a01429314000967e81824438261002a0140330c050fc0702c090200f0f411,0x5e20b40204cc403c3d
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check48 : ¬ FormulaSat (caseFormula c48) := checkW_sound _ k48 10 w48 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good48 : caseGood c48=true := by decide +kernel
theorem next48 {chosen region} (disj : ∀ i∈c48.prior, chosen i=false) (O : Later c48.prior chosen region) : ∃ g∈c48.groups, Matches chosen g := case_conclusion _ good48 check48 disj O
def c176 : Case := ⟨[5, 6, 8],[5, 6, 8],[
s0,s1,s2,s3,s4,s5,s28,s47,s103,s177,s178,s186,
s200,s242,s273,s304,s324,s916,s917,s1031,s1073,s1247,s1513,s1578,
s1645,s1646,s1722,s1723,s1724
],[
t9,t10,t17,t19,t22,t23,t24,t25,t26,t27,t29,t31,
t32,t33,t35,t41,t42,t43,t44,t49,t50,t51,t52,t53,
t54,t58,t59,t60,t61,t63,t66,t69,t71,t72,t75,t79,
t80,t81,t83,t85,t86,t87,t88,t89,t90,t93,t94,t95,
t97,t99,t100,t101,t102,t103,t105,t106,t113,t114,t115,t116,
t118,t119,t120,t121,t122,t123,t126,t127,t128,t129,t130,t131,
t132,t133,t134,t135,t140,t142,t143,t145,t146,t147,t148,t150,
t151,t154,t156,t158,t159,t160,t161,t169,t185,t186,t188,t189,
t190,t191,t192,t193,t195,t197,t198,t199,t200,t201,t203,t207,
t208,t209,t210,t211,t212,t213,t214,t215,t216,t217,t218,t219,
t221,t224,t227,t228,t229,t232,t234,t235,t236,t238,t239,t240,
t242,t243,t245,t246,t247,t248,t249,t250,t251,t252,t253,t254,
t255,t256,t257,t258,t260,t261,t262,t270,t271,t277,t279,t283,
t284,t285,t286,t287,t288,t297,t298,t299,t308,t311,t315,t321,
t326,t328,t329,t330,t331,t333,t335,t336,t337,t340,t342,t344,
t346,t348,t350,t351,t352,t353,t354,t356,t357,t359,t360,t375,
t376,t377,t378,t379,t380,t381,t382,t383,t384,t385,t386,t387
],[
g0,g1,g2,g4,g8,g64,g256,g512,g1024,g2048,g4096,g8192,
g16384,g32768,g65536,g131072,g262144,g524288,g1048576,g2097152,g320,g576,g768,g3072,
g4160,g5120,g6144,g9216,g10240,g12288,g16640,g17408,g18432,g20480,g24576,g33280,
g33792,g34816,g36864,g40960,g49152,g66560,g133120,g196608,g262208,g266240,g327680,g393216,
g532480,g589824,g655360,g786432,g1048832,g1064960,g1114112,g1179648,g1310720,g1572864,g2097664,g2129920,
g2162688,g2228224,g2359296,g2621440,g3145728,g322,g580,g776,g11264,g21504,g38912,g57344,
g266304,g720896,g1065216,g1376256,g2130432,g2490368,g3670016,g11265,g21506,g30720,g38916,g46080,
g52224,g57352,g720897,g1376258,g1966080,g2490372,g2949120,g3342336,g3670024,g21826,g39492,g58120,
g1376578,g2490948,g3670792,g732161,g1397762,g2529284,g3727368,g1398082,g2529860,g3728136
]⟩
def k176 : List Nat := [
1,2,3,189,117,190,92,62,191,192,193,118,
63,64,119,120,194,195,121,196,197,198,93,65,
66,51,122,46,47,67,68,69,94,199,123,200,
201,95,202,70,203,204,31,124,32,125,205,206,
126,96,127,71,128,207,129,130,131,208,97,72,
73,132,33,133,134,135,74,209,136,210,137,75,
138,139,98,140,12,211,212,99,141,76,142,13,
100,213,41,214,215,216,143,144,101,217,218,219,
52,53,42,145,43,54,77,44,34,20,102,146,
220,147,103,148,221,104,21,222,149,223,150,151,
78,22,23,224,225,226,35,18,105,227,228,152,
229,230,231,232,233,234,106,79,235,236,107,237,
238,239,240,241,242,243,244,153,108,245,154,155,
246,109,247,248,249,80,81,250,251,252,253,82,
254,255,256,257,55,56,258,156,259,157,260,261,
158,48,159,262,160,263,161,110,264,36,37,111,
162,112,265,163,266,24,267,164,165,16,166,25,
167,168,169,268,170,171,172,83,269,270,84,271,
173,85,272,86,273,38,49,274,275,276,277,278,
279,280,174,87,175,26,176,27,281,282,283,284,
285,286,287,288,289,290,291,292,293,294,295,296,
297,298,299,300,301,302,303,304,305,306,307,308,
309,310,311,312,313,314,315,316,317,318,319,320,
321,322,323,324,325,326,327,328,329,330,331,332,
333,334,335,336,337,338,339,340,341,342,343,344,
345,346,347,348,349,350,351,352,353,354,355,356,
357,358,359,360,361,362,363,364,365,366,367,368,
369,370,371,372,373,374,375,376,377,378,379,380,
381,382,383,384,385,386
]
def w176 : List Nat := [
0x105012038080180201584464110080d0040b000000b02a0a026090220801e0701a0601605012038080180400d83460110080d0040b000000b02a0a026090220801e0701a0601605012038080180400982,0x1090220801e0701a060160501203806010020258646c110080d0040b000000b02a0a026090220801e0701a0601605012038080100201d85468110080d0040b000000b02a0a026090220801e0701a06016,0x10040b000000b02a0a026090220801e0701a060160500e020060100204d88474110080d0040b000000b02a0a026090220801e0701a0601605012020060100203d87470110080d0040b000000b02a0a026,0x1010020658b480110080d0040b000000b02a0a026090220801e0701a060140480e020060100205d8a47c110080d0040b000000b02a0a026090220801e0701a060160480e020060100205589478110080d,0x106818058140480e02006010020758d488110080d0040b000000b02a0a026090220801e07018058140480e020060100206d8c484110080d0040b000000b02a0a026090220801e0701a058140480e02006,0x10b02a0a026090220781c06818058140480e02006010020858f490110080d0040b000000b02a0a026090220801c06818058140480e020060100207d8e48c110080d0040b000000b02a0a026090220801e,0x149c110080d0040b000000b02a0a026088200781c06818058140480e020060100209591498110080d0040b000000b02a0a026090200781c06818058140480e020060100208d90494110080d0040b00000,0x10480e02006010020ad944a4110080d0040b000000b02a09824088200781c06818058140480e02006010020a5934a0110080d0040b000000b02a0a024088200781c06818058140480e020060100209d92,0x1090220801e0701a0601605008018040081303d964ac110080d0040b000000a82809824088200781c06818058140480e02006010020b5954a8110080d0040b000000b02809824088200781c0681805814,0x10040b000000b02a0a026090220801e0701a0601603808018040081504d984b4110080d0040b000000b02a0a026090220801e0701a0601604808018040081503d974b0110080d0040b000000b02a0a026,0x10081b05d9b4c0110080d0040b000000b02a0a026090220801e070180581404808018040081b03d9a4bc110080d0040b000000b02a0a026090220801e0701a0501203808018040081905d994b8110080d,0x1068180501203808018040081d05d9d4c8110080d0040b000000b02a0a026090220801e070160501203808018040081b0659c4c4110080d0040b000000b02a0a026090220801e07018050120380801804,
0x10b02a0a026090220801e060160501203808018040081d06d9f4d0110080d0040b000000b02a0a026090220801e068160501203808018040081d0659e4cc110080d0040b000000b02a0a026090220801e,0x14dc110080d0040b000000b02a0a026090220801c068180501203808018040081f05da14d8110080d0040b000000b02a0a026090220801c068180581403808018040081f04da04d4110080d0040b00000,0x103808018040081f075a44e4110080d0040b000000b02a0a026090220801c060160501203808018040081f06da34e0110080d0040b000000b02a0a026090220801c068160501203808018040081f065a2,0x1090220781c068180501203808018040082105da64ec110080d0040b000000b02a0a026090220781c0681805812038080180400821055a54e8110080d0040b000000b02a0a026090220801a0601605012,0x10040b000000b02a0a026090220781c060160501203808018040082106da84f4110080d0040b000000b02a0a026090220781c0681605012038080180400821065a74f0110080d0040b000000b02a0a026,0x10082305dab500110080d0040b000000b02a0a026090220701a060160501203808018040082107daa4fc110080d0040b000000b02a0a026090220781a0601605012038080180400821075a94f8110080d,0x1060160501203808018040082508dad508110080d0040b000000b02a0a026088200781c0681605012038080180400825065ac504110080d0040b000000b02a0a026090200781c06818050120380801804,0x10b02a0a024088200781c060160501203808018040082706daf510110080d0040b000000b02a0a024088200781c068180581404808018040082703dae50c110080d0040b000000b02a0a0260801e0701a,0x151c110080d0040b000000b02a0a0220801e0701a0601605012038080180400827095b1518110080d0040b000000b02a0a0240801e0701a060160501203808018040082708db0514110080d0040b00000,0x1038080180400829095b4524110080d0040b000000b02a098240801e0701a060160501203808018040082908db3520110080d0040b000000b02a09824088200781a0601605012038080180400829075b2,0x1088200781c068180581403808018040082b04db652c110080d0040b000000b02a090220801e0701a060160501203808018040082909db5528110080d0040b000000b02a098220801e0701a0601605012,0x10040b000000b028098240801e0701a060160501203808018040082b08db8534110080d0040b000000b02809824088200701a060160501203808018040082b07db7530110080d0040b000000b02809824,
0x10082b0a5bb540110080d0040b000000b028090220801e0701a060160501203808018040082b09dba53c110080d0040b000000b028098220801e0701a060160501203808018040082b095b9538110080d,0x1060160501203808018040082d085bd548110080d0040b000000a82809824088200781c068180581203808018040082d055bc544110080d0040b000000b026090220801e0701a06016050120380801804,0x10a828098220801e0701a060160501203808018040082d095bf550110080d0040b000000a828098240801e0701a060160501203808018040082d08dbe54c110080d0040b000000a828098240881e0701a,0x155c110080d0040b000000a826090220801e0701a060160501203808018040082d0a5c1558110080d0040b000000a828090220801e0701a060160501203808018040082d09dc0554110080d0040b00000,0x104808010020540f01dc4564110080d0040b000000b02a0a026090220801e0701a06016050080180204c0f015c3560110080d0040b000000a026090220801e0701a060160501203808018040082d0adc2,0x1090220801e068140480e02006010020741905dc656c110080d0040b000000b02a0a026090220801e0701a06016038060100205413025c5568110080d0040b000000b02a0a026090220801e0701a06016,0x10040b000000b02a0a026090220781c058140480e02006010020841b065c8574110080d0040b000000b02a0a026090220801c060140480e020060100207c1b05dc7570110080d0040b000000b02a0a026,0x10a42508dcb580110080d0040b000000b02a0a024088200781c0601605012020060100209c1b03dca57c110080d0040b000000b02a0a0260902206818058140480e02006010020841f075c9578110080d,0x1058140480e02006010020ac2708dcd588110080d0040b000000b02809824088200701a060160500e02006010020ac1f04dcc584110080d0040b000000b02a098200781c06818058140480e0200601002,0x10a828088200781c06818058140480e02006010020b427095cf590110080d0040b000000a828098240881e0701a060160480e02006010020b421055ce58c110080d0040b000000b028090200781c06818,0x159c110080d0040b000000b02a0a026090220801e068140480e020060101d0641700dd1598110080d0040b0000009824088200781c06818058140480e02006010020b42b0a5d0594110080d0040b00000,0x1020040082106c1901dd45a4110080d0040b000000b02a0a02609022080160501203808018040081f0741b065d35a0110080d0040b000000b02a0a026090220801c060140480e020060081f06c17015d2,
0x1090220701a0501203808018040082107c1905dd65ac110080d0040b000000b02a0a0260902207818050120380801804008210741b05dd55a8110080d0040b000000b02a0a026090220781c058140480e,0x10040b000000b02a098200781c06818058140480e02006010290942300dd85b4110080d0040b000000b02a0a0260902206818058140480e018040082107c1d025d75b0110080d0040b000000b02a0a026,0x109c2501ddb5c0110080d0040b000000b0220801e0701a060160501203808018040082b0a427095da5bc110080d0040b000000b028090200781c06818058140480e020060082b09c23015d95b8110080d,0x10501203808018040082d0ac2508ddd5c8110080d0040b000000a8240801e0701a060160501203808018040082d0a42708ddc5c4110080d0040b000000a828088200781c06818058140480e020040082d,0x10b02a0a026090220801c06014020060081f06c1704c0f015df5d0110080d0040b0000009824088200781c06818058140480e018040082d0ac29025de5cc110080d0040b000000a0260801e0701a06016,0x15dc110080d0040b000000b02a0a02609022068180580e018040082107c1d05413025e15d8110080d0040b000000b02a0a026090220781c05812020040082106c190540f01de05d4110080d0040b00000,0x10082d0ac2905413025e45e4110080d0040b000000a828088200781c0681805812020040082d09c250540f01de35e0110080d0040b000000b028090200781c0681805814020060082b09c2304c0f015e2,0x1070180501203808018020ac2708c1f06c17015e65ec110080d0040b000000b02a098200781a0501203808018040a42508c1d0641700de55e8110080d0040b0000009824088200781c068180580e01804,0x10040b00000098240881a060160501203806010020b42b0a42107c1d025e85f4110080d0040b000000a8280881e070160501203808010020b4270942106c1901de75f0110080d0040b000000b02809020,0x105413025eb600110080d0040b000000a8280881e0701604808010020b4270942106c190540f01dea5fc110080d0040b000000b028090200701805008018020ac2708c1f06c1704c0f015e95f8110080d,0x10ac29084b07ac12178070b80f0941b0c0050b40310427110170d42510c19130231081e04c1c19c082b4000b42b0a421055ec604110080d0040b00000098240881a0601603806010020b42b0a42107c1d,0x1084b00002d0ac29051ee7400977800090220801e0701a060160982903806010020b42b050127b5e804c90055ec020ad070670781301c2e03c2506c300142d00c4109c4405c35094430644c08c420002d,
0x10210a048fc051ee07caa0749c084b00644c05c3509c440944308c4200c4101c2e03c2506c300142d0002d0ac292c5ed04c9001c2e03c2506c300142d00c4109c4405c35094430644c08c420749c07caa,0x1278212a0152481f2a41325409250292c41b0c00f094070b8050b4000b42b06dc208d0301c2e03c2506c300142d07ca90749e0249405ca104c950646e0549200c6509cab084a80a4b10002d0ac247bde4,0x10701a0481603808008060102d088207c5bf08d00084280548d05c1700c1407c160741504c1a024190ac1b03caf01cae0145606c4d064960002d0a026095f077422410247bc03194272ac191b8172841d,0x103808008060a02d098047d1f2081f1000260902a0601e0701a0481603808008060a02d010227cdce051bd00028098240781c068180582a0480e02002018040b422085f2654156f0000a0260902a0601e,0x10801e0701a018160a8120100809c020b414039f57d0257c0051580f2bc1b134072b8192581705c030501f0581d05413068090642b06c000b428098386f82108c15224227cc000902a0601e0701a04816,0x173c000a0220801e0701a060160a8120940809c040082d0500e7d9f5084d8054d706d0b03cde01cdd05c1700c1407c160741504c1a024190ac1b0143208c37098380002d0a02415c36061c00002809022,0x105c1700c1407c160741504c1a024190ac1b0143208c3709838090570002d0a01a2c9f60549905c1700c1407c160741504c1a024190ac1b0143208c37064360849a09057098380002d0a01a039f776c06,0x10501f0581d05413068090642b06c000b4282cdea0506a05c1700c1407c160741504c1a024190ac1b0143208c370189f09057080360604d068b2098380002d0a00f7e1e301905050ff039f7064360849a,0x17e9dc0890204c1a0241901c7903c290949b05c170645500c140841307c16074150145606c2b0542a0a0b30ac1b0002d09df979c152640f7e0200d80627c181341a2c82415c230dc050c8260e01705c03,0x10ac1b0002d00dfa09df90145608413064550949b06c2b0542a03c2901c790a0b304c1a07c1605c17024190741500c140002d0a9fb4042270400010200781c0681805814048080080e0a4060a82d09026,0x10243403c2907c210b4030002a0a426090706c82322c1c7f02d00c000102007802068180a8140480e0200609829090167f5b3089930b403000240102007802068180a8140480e02006098290581c7f1fb,0x104c2f0243403c2907c210146c090700b4030002a0a426058027fdb408dcb0b403000260801e0701a0a81605012038080180409429060027f9fd0645505c35014da00d0f01c3306c2b0542a0841304c2f,
0x10bc090d00f0a41f0842d00c000a82909a017601d1ac191f022364027fc070cc1b0ac150a82104c130bc090d00f0a41f084051b0241c02d00c000a82909816801fe074530645501c3306c2b0542a08413,0x1809b5074a0094f808cf70648f05c8e014c500cc409a0103c2904c2f0841307c2106c2b0542a0243401c330b4030002a0a404794181ac0214c223501c3d816800051b0241c0070cc1b0ac150a82104c13,0x10a8200781c06016050120200609c040082206e046b8232200e8082d00c000a8200781c0a018058140480809c06010020901a80db0089920b403000280a8200781c09018058140480809c06010020680e,0x10102d00c000a827015b108cf506c6303c8c092050b4030001e07028060160501202027018040a82000a06810231841a80c000801e07028060160501202027018040a802092057280e6bc2d00c000a024,0x100c000a81e058120100202020050180181c096086b4226442d00c000a0260801e0701a06016050120a808018040080e0960781809448214501544c1d280074441f150132b0054381923c172380335429,0x1010020701b82d8708c8803a090b403000260801e07008060160501201002018280a82406a0a640226082d00c00090260801e07008060160501201002018280a81a03a0981c1b18c0f23029010270142d,0x108a0e830258202901027014000a81e058120100202020050180181c8360b08c6106a0a0002007826020180581404804008060a02a070248318c03d9a0b4030002809824088200782a060160501202006,0x1090220801e0701a0a81605012010080081801e10838231ac2514c0f4301c8342901027014000a81e0581201002020200501801a0f67c1a6342d00c000a0260901e0801d0601605012038080a80400806,0x1010260641c84d9c0698b0b403000280a806088200780e058140481902002010260702484a10094d308c870748106c7e01a0f0a40409c050002a07816048040080808014062113180e6142d00c000a026,0x114c1c84c00018220801e038160a8120a0080080409814066153981a6782d00c000a026090220801e0181605012038080a80400819076146b01b18c248482d00c000a806088200780e058140482802002,0x10a8040082001a193200f7102d00c000a026090220801e0701a0601604808010020a81501e181a006288000801506617854071a00f1a823228188442901027014000a81e0581201002020200521685025,0x12241b1fc1985c252341d180148582901027014000a81e0581201002020200c61901e1800026090220801e0701a0a01604808010020a8180561a65c0e6242d00c000a026090220601e0701a0481605408,
0x1018a2068cd0621b074600a4040942809c0508c23080310b4030002a07816048040080805458694072140f1241b1fc29010250a0270142308c200c41d1802d00c000a81e0581201002020150621b86823,0x1054580002a0781604804008080647169c073301b8702d00c00038240881e0a0160a81205008010020842607019875c801dd40b40300028038240881e070160a8120500801002084260641b871e0038e3,0x1098240881e0a818058140480e02021010020701b87d8f01c850a4040942809c0508c230545803c4906471080310b4030002a0781604804008080701a87a1d03c6a074ef0a4040942809c0508c2308031,0x18800f124191c4151602308c250a0200c429010270142d00c000a81e05812010020222187c1a87829010250a0270142308c151600f124191c4200c4000a81e05812010020201c8807e019a80b40300028,0x10950d08c980245b01c7400a220a40409c050b4030002a078160480488d860545e06ca403d06064e20946208cd1084860748201cbe022210a40409c050b4030002a078160480400a226a41b3c0073081c,0x1064520487209c050b4030002a07816014b46101d20019390212981541c25348233401b17c0f174090f4072f4032f00488c29010270142d00c000a81e058121c983074ce0647c0848403cdf06c7d05509,0x109824088200781c068180582a04c06010020201589596039880b4030002809824088200781c068180582a0100604c0202014891c307480084a60387a054c00243d0a4040944b06c4601c6d00c6f08c4a,0x10002a0781609a26084a70749d0a4040944b06c4601c6d00c6f08c4a064520487209c05014b40002a07816022278941489000098240882007828068180582a0100604c0207008898e0039980b40300028,0x10242701c75064970940c058260a4040b4030002a078020881b082282901a32c2330c0005c0909dc5050c7084860748203cbf02227014b40645200c6f01c6d0944b08c4a06c46048720a40409c050b403,0x1024270582606c590b4030002a07802088211cdd5070ed082280649701c7509c050142204c1103c1e0541f0940c0a40402427058260b4030002a078020881b1659b074e509c050142204c1103c1e0541f,0x100c000a81e008220622a628073282701405088130440f0781507c25030290100909c160981b164211cc2d00c000a81e008220601c8a5a6074ee064ec01cc109c050142204c1103c1e0541f0940c0a404,0x10a40402427058260002a0780208a2c7181c6642d00c000a026090220801e0642a05012038080080405c1a01a2b674072041c8a42701405088130440f0781507c25030290100909c160981b164211cc2d,
0x100c000a81e041ab084230748b06c610648a01c8708a2c09c050142204c1103c1e0541f0940c0a40402427058260b4030002a078028b62b01c680622a0847306c5909c050142204c1103c1e0541f0940c,0x109c0500c3e0744e0940c0a404054180243f04c7b03ca301445078100b4030002a05c1a0822e74421210183241c3841b1f423260071d0028b40909c1507c1304405088250300f0781609829010270142d,0x1000280982408820070180502a06c08018170081f0480e8bdd6060f10822e03ca304c7b0144501c0f08c0b09c0500c3e0744e0940c0a404054180243f078100b4030002a05c1a2d5a1064e801c0f08c0b,0x10601d13825030090fc030f8290100703c2302c1e040270142d00c000a8170b22f03ce701c0f08c0b09c0500c3e054180243f0847806469068b50744e078100940c0a4040002a05c128c1d2011c70b403,0x1169d307069062310b40300026090220800403816050120a0080182a07c1b00a323ac1c68c2d00c000a0260902208004038160501206c080182a07c020623177c044200e044128c0191a4211e01a2d415,0x10a40401c0f08c0b09c0503c2005c2c094240541800c470144806c5a078100b4030002a02012080198ce3200ce9084f304c460145f0a40401c0f08c0b09c0503c2005c2c0942405418078100002a0201b,0x100812062368d0198cc290100703c2302c270140f080170b025090150600311c051201b1681e040000a808048208d5a40718e0b40300028098240881f06804058140480e020060a802080188d1a2074ea,0x105c2c078100b4030002a020b68d8193c8208d4290100703c2302c270140f080170b025090150600311c051201b1681e040000a80804a377241c6a82d00c000a026090220841a038160502a0201f01804,0x10100703c2302c0f080170b00316c050f4191d81b1dc1c20c251882701420294082d81e0402d00c000a8138e1a00749d084a70645204a370144800c4706c5a09424054180a40401c0f08c0b09c0503c20,0x1020000840a4582d00c2a01800024093702d00c2a018000740875c15178138e020294251881c20c1b1dc191d8050f40316c082d80f080170b00703c2302c1e04027014290102d00c000a8067841433c29,0x10001f058228e9b704dcc0b4030640e054070240901c0d0840a074080a806000260901a0580e07c280080408a391b82a0181501c000640e4542a018210280001c0d45c2a01809024000540719c2a0181d,0x108864068450105409866058b70a80601c0d02409054070640e074080840a0b4030001f03a3b17c041501a3d02602c228e80007c162de390149109c6406c9300c5c0a4210942403c200a806054070b403,
0x10002309c042e0fa0986607c120a80600017071e90485d03a3b06845088640105409866058b7094240a42100c5c0a80601c0d02409054070640e074080840a0b4030001f049e604c1100c5c0a42109424,0x1094500a451010b80a80601c0d024090540705c1c0640e0740807c120840a0b4030002309c0e8f1cd04cac03c2500c4006c4f094500a4510a80601c0d024090540705c1c0640e0740807c120840a0b403,0x10241501c17070190381d0201f048210282d00c0008c1d788121740e8f0042e0031001b13c25140291442a01807034090241501c17070190381d0201f048210282d00c0008c278f5d904c7a00c4006c4f,0x105c1c0540703c390240901c0d0a80600026008280923e2442a01823074000143b24c2a018230740006c3a36c2a018230740003c396e00f0941312805440278f429144251401b13c031002a0180703409,0x10182d00c0000826901b904c4b0923e0b4030840a07c120740806c3a0640e05c1c054070143b03c390240901c0d08c1d0a80600002098288fd9404db60b4030143b08c1d0840a07c120740806c3a0640e,0x1028230742d00c000a4bb35823074260f00004cba3e42d00c260f00000cb9900031942a018000983c6ec130bc253f4288fc23074210281f0481d0201b0e819038170701501c090240f0e4050ec070342a,0x105c1c054070143b0983c0240901c0d00cb90a8060a4bb09641002423ec260f02a018292ec0009641768243f8260f02a018032e4050ec07034090240f0e4132e81501c17070190381b0e81d0201f04821,0x5ba0b40304cba03c3908c1d0840a07c120740806c3a0640e
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check176 : ¬ FormulaSat (caseFormula c176) := checkW_sound _ k176 10 w176 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good176 : caseGood c176=true := by decide +kernel
theorem next176 {chosen region} (disj : ∀ i∈c176.prior, chosen i=false) (O : Later c176.prior chosen region) : ∃ g∈c176.groups, Matches chosen g := case_conclusion _ good176 check176 disj O
def c177 : Case := ⟨[1, 5, 6, 8],[1, 5, 6, 8],[
s2,s4,s5,s28,s131,s210,s284,s917,s1248,s1513,s1578,s1645,
s1646,s1722,s1723,s1724
],[
t9,t10,t17,t19,t22,t23,t26,t27,t29,t32,t40,t43,
t44,t49,t50,t52,t53,t54,t58,t59,t61,t63,t68,t71,
t72,t77,t80,t81,t85,t86,t87,t88,t89,t90,t94,t95,
t97,t99,t100,t101,t102,t103,t105,t114,t115,t116,t119,t121,
t122,t123,t126,t127,t128,t129,t130,t131,t132,t133,t135,t142,
t143,t146,t147,t150,t151,t154,t156,t158,t159,t160,t161,t185,
t188,t189,t190,t191,t193,t195,t197,t198,t200,t203,t206,t207,
t208,t209,t210,t211,t212,t213,t214,t215,t216,t217,t218,t221,
t222,t224,t227,t228,t229,t231,t232,t234,t235,t236,t237,t238,
t239,t242,t243,t245,t246,t247,t248,t249,t250,t251,t252,t253,
t254,t255,t256,t257,t258,t260,t261,t262,t265,t270,t271,t274,
t277,t279,t285,t286,t287,t288,t299,t315,t318,t321,t325,t326,
t327,t329,t330,t332,t335,t336,t337,t340,t342,t344,t346,t351,
t352,t353,t357,t359,t360,t370,t371,t373,t374,t375,t376,t377,
t378,t379,t380,t381,t382,t383,t384,t385,t386,t387
],[
g0,g2,g4,g8,g64,g256,g512,g1024,g2048,g4096,g8192,g16384,
g32768,g65536,g131072,g262144,g524288,g1048576,g2097152,g320,g576,g768,g3072,g4160,
g5120,g6144,g9216,g10240,g12288,g16640,g17408,g18432,g20480,g24576,g33280,g33792,
g34816,g36864,g40960,g49152,g66560,g133120,g196608,g262208,g266240,g327680,g393216,g532480,
g589824,g655360,g786432,g1048832,g1064960,g1114112,g1179648,g1310720,g1572864,g2097664,g2129920,g2162688,
g2228224,g2359296,g2621440,g3145728,g322,g580,g776,g11264,g21504,g38912,g57344,g266304,
g720896,g1065216,g1376256,g2130432,g2490368,g3670016,g21506,g30720,g38916,g46080,g52224,g57352,
g1376258,g1966080,g2490372,g2949120,g3342336,g3670024,g21826,g39492,g58120,g732160,g1376578,g2490948,
g3670792,g1397762,g2529284,g3727368,g1398082,g2529860,g3728136
]⟩
def k177 : List Nat := [
1,2,3,4,173,99,174,175,100,59,176,177,
178,50,101,42,43,60,61,62,63,102,64,179,
103,104,65,180,66,67,181,68,182,82,183,184,
69,70,185,71,72,44,45,105,106,73,107,108,
83,109,84,186,85,18,187,188,110,86,87,46,
88,36,51,189,111,112,190,89,37,38,23,113,
24,39,40,25,19,13,90,114,115,191,91,192,
116,193,117,92,74,26,27,194,52,53,118,195,
196,75,197,198,199,200,201,76,202,203,204,205,
206,207,93,94,208,209,119,120,210,211,121,122,
212,123,54,124,213,214,125,126,215,127,216,217,
128,218,219,220,221,47,55,222,129,223,130,224,
225,41,34,131,226,227,132,228,229,133,48,28,
95,14,134,230,135,56,136,137,138,139,140,141,
142,231,143,144,145,146,35,232,96,147,97,29,
20,148,149,21,77,233,234,235,236,237,238,239,
150,78,151,30,152,31,240,241,242,243,244,245,
246,247,248,249,250,251,252,253,254,255,256,257,
258,259,260,261,262,263,264,265,266,267,268,269,
270,271,272,273,274,275,276,277,278,279,280,281,
282,283,284,285,286,287,288,289,290,291,292,293,
294,295,296,297,298,299,300,301,302,303,304,305,
306,307,308,309,310,311,312,313,314,315,316,317,
318,319,320,321,322,323,324,325,326,327,328,329,
330,331,332,333,334,335,336,337,338,339,340,341,
342
]
def w177 : List Nat := [
0x10480e0200401d583c01100c0d0080b00403000000b02a0a026090220801e0701a0601605012038080180555cef044030340202c0100c000002c0a82809824088200781c06818058140480e0200601156,0x10781c0681805814048080180403d5a3c81100c0d0080b00403000000b02a0a026090220801e0701a06016050120380601009564f1044030340202c0100c000002c0a82809824088200781c0681805814,0x10a82809824088200781c068180581203808018040555c3d01100c0d0080b00403000000b02a0a026090220801e0701a060160500e020060101356cf3044030340202c0100c000002c0a8280982408820,0x102c0100c000002c0a82809824088200781c068160501203808018040655e3d81100c0d0080b00403000000b02a0a026090220801e0701a060140480e0200601017574f5044030340202c0100c000002c,0x1584f9044030340202c0100c000002c0a82809824088200781a06016050120380801804075603e01100c0d0080b00403000000b02a0a026090220801e07018058140480e020060101b57cf70440303402,0x10480e020060102358cfb044030340202c0100c000002c0a828098240881e0701a06016050120380801804085623e81100c0d0080b00403000000b02a0a026090220801c06818058140480e020060101f,0x10781c06818058140480e0200601027594fd044030340202c0100c000002c0a828098220801e0701a06016050120380801804095643f01100c0d0080b00403000000b02a0a026090200781c0681805814,0x10b02809824088200781c06818058140480e020060102b59cff044030340202c0100c000002c0a826090220801e0701a060160501203808018040a5663f81100c0d0080b00403000000b02a0a02408820,0x10080b00403000000b02a0a026090220801e0701a06016050080180404c0f5a501044030340202c0100c000002a0a026090220801e0701a060160501203808018040b5684001100c0d0080b0040300000,0x105d6c4101100c0d0080b00403000000b02a0a026090220801e0701a060160380801804054135ad03044030340202c0100c000002c0a82809824088200781c0681805812020060101503d6a4081100c0d,0x10480e020060101b05d6e4181100c0d0080b00403000000b02a0a026090220801e0701805814048080180406c0f5b505044030340202c0100c000002c0a82809824088200781c068140480e0200601019,0x1088200781a060140480e020060101d05d704201100c0d0080b00403000000b02a0a026090220801e0701605012038080180406c195bd07044030340202c0100c000002c0a82809824088200781c06014,
0x10002c0a828098240882007818058140480e020060101d06d724281100c0d0080b00403000000b02a0a026090220801e06816050120380801804074195c509044030340202c0100c000002c0a82809824,0x10340202c0100c000002c0a82809824088200701a060140480e020060101f05d744301100c0d0080b00403000000b02a0a026090220801c0681805814038080180407c135cd0b044030340202c0100c00,0x107c1d5dd0f044030340202c0100c000002c0a828098240882007018058140480e020060101f06d764381100c0d0080b00403000000b02a0a026090220801c0681605012038080180407c195d50d04403,0x1050120380801804084175e511044030340202c0100c000002c0a828098240881e0701a060160480e0200601021055784401100c0d0080b00403000000b02a0a026090220801a06016050120380801804,0x1090220781c060160501203808018040841b5ed13044030340202c0100c000002c0a828098240881e0701a058140480e02006010210657a4481100c0d0080b00403000000b02a0a026090220781c06818,0x1000000b02a0a026090220701a060160501203808018040841f5f515044030340202c0100c000002c0a828098240881e06818058140480e02006010210757c4501100c0d0080b00403000000b02a0a026,0x100c0d0080b00403000000b02a0a026088200781c06816050120380801804094195fd17044030340202c0100c000002c0a828098240801e0701a060140480e020060102305d7e4581100c0d0080b00403,0x10102706d824681100c0d0080b00403000000b02a0a024088200781c0681805814048080180409c0f60519044030340202c0100c000002c0a828098200781c06818058140480e020060102508d8046011,0x1058140480e0200601027095844701100c0d0080b00403000000b02a0a0240801e0701a0601605012038080180409c2360d1b044030340202c0100c000002c0a828090220801e07018058140480e02006,0x1090200781c06818058140480e020060102908d864781100c0d0080b00403000000b02a09824088200781a060160501203808018040a41d6151d044030340202c0100c000002c0a828088200781c06818,0x100c000002c0a824088200781c06818058140480e020060102909d884801100c0d0080b00403000000b02a098220801e0701a060160501203808018040a42561d1f044030340202c0100c000002c0a826,0x1044030340202c0100c000002c0a026090220801c06818058140480e020060102b07d8a4881100c0d0080b00403000000b02809824088200781c068180581403808018040ac1362521044030340202c01,
0x1018040ac2763525044030340202c0100c000002c0a026088200781c06818058140480e020060102b0958c4901100c0d0080b00403000000b028098240801e0701a060160501203808018040ac2362d23,0x1068180581203808018040b41563d27044030340202c0100c000002c09824088200781c06818058140480e020060102b0a58e4981100c0d0080b00403000000b028090220801e0701a060160501203808,0x1098240801e0701a060160501203808018040b42364529044030340202c0100c000002a0a026090220781c06818058140480e020060102d085904a01100c0d0080b00403000000a82809824088200781c,0x100403000000a828090220801e0701a060160501203808018040b42764d2b044030340202c0100c000002a0a026088200781c06818058140480e020060102d095924a81100c0d0080b00403000000a828,0x14b81100c0d0080b00403000000a026090220801e0701a060160501203808018040b42b6552d044030340202c0100c000002a09824088200781c06818058140480e020060102d0a5944b01100c0d0080b,0x10180405413025984c01100c0d0080b00403000000b02a0a026090220801e0701a06016048080101503c0765d2f044030340202c0100c000002c0a82809824088200781c06818058140200604c0f01596,0x10701805012038080180407c1b05d9a4c81100c0d0080b00403000000b02a0a026090220801e068140480e020060101d0641766531044030340202c0100c000002c0a82809824088200781c068180580e,0x10a828098240881a060160501203808018040841f0759c4d01100c0d0080b00403000000b02a0a026090220781c058140480e020060102106c1966d33044030340202c0100c000002c0a8280982408820,0x102c0100c000002c0a8260801e0701a060160501203808018040a42508d9e4d81100c0d0080b00403000000b02a0a024088200781c0601605012020060102706c0f67535044030340202c0100c000002c,0x168539044030340202c0100c000002c0a0240801e0701a060160501203808018040ac2708da04e01100c0d0080b00403000000b02809824088200701a060160500e020060102b07c1367d370440303402,0x1020060102d0ac2968d3b044030340202c0100c000002a0a0220801e0701a060160501203808018040b427095a24e81100c0d0080b00403000000a828098240881e0701a060160480e020060102d08415,0x10801605012038080180407c1d06c196953d044030340202c0100c000002c0a82809824088200701805012038080181f06c17015a44f01100c0d0080b004030000009824088200781c06818058140480e,
0x10b02a0a02609022078180501203808018040841d06c1769d3f044030340202c0100c000002c0a828098240881e0701605012038080102106c1901da64f81100c0d0080b00403000000b02a0a02609022,0x10080b00403000000b02a0a0260902206818058140480e018040841f074096a541044030340202c0100c000002c0a828098240881c068140480e020060102107c1905da85001100c0d0080b0040300000,0x101dac5101100c0d0080b00403000000b0220801e0701a060160501203808018040ac2909c256ad43044030340202c0100c000002c0a0240801e0701a0601605012038080182b09c23015aa5081100c0d,0x1020060102d0ac2508dae5181100c0d0080b00403000000a8240801e0701a060160501203808018040b42909c236b545044030340202c0100c000002a0a0220801e0701a0601605012038080102d09c25,0x10882007018050080181f06c1704c0f015b05201100c0d0080b004030000009824088200781c06818058140480e018040b42b0a4096bd47044030340202c0100c0000028098200781c06818058140480e,0x10002c0a828098240881a06016038060102107c1d05413025b25281100c0d0080b00403000000b02a0a026090220781c05812020040841b0641503c076c549044030340202c0100c000002c0a82809824,0x10340202c0100c000002c0a0240801e0701a06016050080182b09c2304c0f015b45301100c0d0080b00403000000b02a098200781a0501203808018040a42508c1d064176cd4b044030340202c0100c00,0x105c056dd4f044030340202c0100c0000026090220801e0701a06016038060102d0ac2905413025b65381100c0d0080b00403000000a828088200781c0681805812020040b4270941503c076d54d04403,0x10102d0ac290841f074096e551044030340202c0100c000002a0a0220781c058140480e020040b4270942106c1901db85401100c0d0080b00403000000b028090200701805012038080182b09c2307c1b,0x107016048080102d09c250841b0641503c076ed53044030340202c0100c000002c0a0240801c06014020060ac2708c1f06c1704c0f015ba5481100c0d0080b0040300000098240881a060160501203806,0x105c260943c0642708c3b0780c0705a020950002d0ac29084156f555044030340202c0100c000002609022068180580e018040b42b0a42107c1d05413025bc5501100c0d0080b00403000000a8280881e,0x10801e0701a0601609829038060102d0ac14049be6e4131c0156f4082541c1681e030070a80f0701b04c050a4270f417098250f01909c230ec000b42b0a421261bc0486701c2a03c1c06c130142909c3d,
0x1084980642705c2609c3d0943c08c3b01c2a03c1c06c13014290002d0ac29265be04c7001c2a03c1c06c130142909c3d05c260943c0642708c3b0748107c8f084980002d0ac29051bf68c096bc0009022,0x11d0091cc292641b04c0f070070a8050a4000b42b07d9508cdf01c2a03c1c06c130142907c8e074820247305c0d04c740645e0547109c900848d0a4990002d0ac24701b6020e5048d8051bf07c8f07481,0x10580e020040182d088207099208cdc084320545607c1a0741905c0d04c1e0241d0ac1f03c9701c960144d06c490645b0002d0a026095c16b822380247002724019178170341d20821234151c41f23813,0x103808010280b426019c570c2070800098240a8180781c068120580e020040a02d01822711a10519000028098240781c068180582a0480e020040182d0882170d680558f00028098240a8180781c06812,0x10a0220801e0701a01816090120a808010270b40e051c671425704051340f25c1b124072581916c1f0681d0641703413078090742b07c000b42809838644210bc151b022710000902a0601e0701a04816,0x10a01a039c86b006688000a0220801e0701a060160a8120940809c040b414039c7718212f4152f01b398072fc0f3001f0681d0641703413078090742b07c050c4230d8260e0000b4280904e0b81864c00,0x1018e2050db039c80642e0847907c1a0741905c0d04c1e0241d0ac1f0143108c36098380904e0002d0a01a269c70547807c1a0741905c0d04c1e0241d0ac1f0143108c360642e084790904e098380002d,0x11241a26824138230d8050c4260e01f0681d0641703413078090742b07c000b42826dbb050cb07c1a0741905c0d04c1e0241d0ac1f0143108c36018830904e0802e060490689a098380002d0a00f725b5,0x11902826c17034130781f068090741d064000b42a72dad0642e088de01c6403c160948005c0d04c1e0241d0840c07c1a074190144d06c18054170a09b0ac1f0002d09dca6e0151e00f724200b80620c18,0x10a4260901c735660642701c2406c18054170840c04c210242503c1607c120145805c260b4040002a0a4260901c089cc72c2b07c000b404650233741916c277280513421030252001b0601505c0f05807,0x103c1607c120b4040002a0a4260906109c186142d0100009824088200781a0580e05012020290182a0101d739860647a089cc01c2406c18054170840c04c210242503c1607c120145805c260b4040002a,0x10b4040002a0a42608dcf6cc1638c181dc2208c070901b0601505c2103013084090940f0581f048050d4241842d010000a8290981d271ce08c54071cd05c260145801c2406c18054170840c04c2102425,
0x1015870642708dcf05c7b0749c014350906101c2406c18054170840c04c210242503c1607c120b4040002a0a4267419e0647a01c2406c18054170840c04c210242503c1607c120143505c7b0749c09061,0x1018040901a74983089650b404000280a8200781c09018058140480809c060101a039d16201d2102535423350191bc171b8052c0267400f05813084210301f0481b0601505c09094070902d010000a829,0x1755d308c7d069d2000200781c0a018058140480809c060a804091d46740e6082d010000a0240a8200781c06016050120200609c040881b74d8108c7c039d10b4040002a0801e07028060160501202027,0x10a814048080600601025039d6754093a4213ac153a81d210073a01f2481317c0539c191bc171b8290142d010000a8270198408cd306c5703c6d091d40b4040001e070280601605012020270182a08004,0x10901a76563089560b40400024098200781c020180581404806010280a81a039d87581b15c0f1b429014270182d010000a81e070160480402020050060602575d80089640b40400028098200781c06816,0x108c7d069d9000200781c020260581404806010280a818091db57c0f5b42d010000a026090220801e0702a0581404808018040601b7695a08c7c039d80b404000260801e070080601605012018040a02a,0x17742d01000038190a0200781c058140482a0200409822019de5bc1a5782d010000a00e064220801e07016050120a8080102601824775db095d70a40509c060002a0781c05812010080801401818771da,0x101427018000a81e0701604804020200509d1940e5602d010000a026090220801e0701a060160a8120100805007781de03ce108c53061dc0a40509c060002a0781c058120100808014019df5fc1b15c24,0x10801a78de106c870647508c6a0a405094560509d09c060002a0781c0581201008080077886603d970b4040002809824088200781c0682a05812020040541801de17801b21c191d4252e8231a80677c29,0x108c2f0804f0b4040002a0781c058120100805406791e308c6c06c890648501de2094560509d0a40509c060002a0781c05812010080804f5a80e5702d010000a026090220601e0700604816054080a804,0x10b40400028038240881e070160a81205008010210980706de56c4182d80e1981a1a00679029014250c827018230bc2013c2d010000a81e0701604804020152797803c8c06c89064850a4050943209c06,0x10181605012038080a8040841a7a19b0617b0b40400028098240881e07006058140480e0202a0102106de77940f1941a1a029014250c827018230bc2013c15278000a81e070160480402007798b5065a6,
0x10781c05812011eb7a40f2300779815278230bc250c82013c2901427018000a81e0701604804021ea7a01b79c00098240881e07006058140480e0a02a01008085e9588195e82d010000a026090220781c,0x1058057b15703c3e06c860644a0844c0549408cd1094350246201cac011eb0a40509c060b4040002a0781c0581227d590546706c8803ce4064c2094bb08c6b0846901cad021ea0a40509c060b4040002a,0x1068180582a04c0601008055ee5a40e56c2d010000a026090220801e0701a060160a80401813020147b5960383f05494024620a405084480649101c9308c5209c060945506c510489f0b4040002a0781c,0x10002a0781c05850660142c80f2b8087bc2d01000090220801e0701a060160a80409828018137c1ee051ed00026090220801e0701a060160a8040182804c087bcc10396b0b4040002809824088200781c,0x104c3403c41054420942d0a405058500002a0781c08022069f25b0185742d010000a026090220801e0701405c120382a018040201a7c5f0015ec0945506c5108c5201c9306491084480489f0a40509c06,0x10cc130d00f10415108250b429014161402d010000a81e070207d16e064c302488069f209c0601c400143304c3403c41054420942d0a405058500b4040002a0781c080227cdf1024b309c0601c4001433,0x10942d0a405070390b4040002a07817085f55e41b33419330091a4230bc207d015108130d0050cc250b40f104071001614029014270182d010000a81e070395f81b2e41914c091ac227cc270180710005,0x1014270180711015118130a0091140f0881c0e4000a81e05ca0664185c02d010000a026090220801e05c1d05012038080182a0101a7d9a7068ce064af09c0601c440544604c280244503c220146308c54,0x107804080227e572064c5069f70b404000260a02a0801e0101605012038080181d090227e160065710b40400028098240a82007804058140480e0200607422069f77d81b310217d423150250b40518c29,0x10645c081f909c0601c440544604c280244503c2205ca00942308dfa0a405070390b4040002a078047ec770645300028074237e9f8094230a40509c0601c440544604c280244503c220703905ca00002a,0x109c06078150b4040002a074202857706cca0a40501c140143a03c2205c4b0942308c1109c060548b04c280248a078150b4040002a07420061fc2dc1912821130047ec1c0e427018000a81e0557c06c5d,0x12841712c2508c23044270181e054000a81d049fe670096a42d010000a02609022068180582a0740e018040841f048147f5a5068c9061fc04c280548b0248a0a40501c140143a03c2205c4b0942308c11,
0x1054290142d010000a804084187fdb202028050b8049fe06c5d0645c080a105c4b0942303c220143a0a40501c1408c110781509c060b4040002a074307f4153202901407050050e80f088191701b17420,0x10a804066006a016340187fc1b1d81312029014070502304427018090ac2506c150b01d0c00f0dc1e0542d010000a804084a25f41733c070502304427018090ac2506c150b00f0dc131201d0c01b1d81e,0x10a8140381f018040581380976069610b404000280981c0881f0a818080140100e020060901604a015d41b31c17318132d029014070502304427018090ac2506c150b01d0c00f0dc1e054212882d01000,0x10a008018240100e8157406d9a0b4040002809824088200700805012038180182a07c0405e0480812804000981c0881f0a8180801401028020060900e05a031441a5cc2d010000a026090220801c06008,0x10c01912821130270181610c1a11c1e0540428c2d010000a80e81a0506600084a203c370a40501c1408c1109c060242b0941b0542c07430078150002a010a3810130d01680c000702207c2a0602005026,0x10240a2f82d0102a01c00074096c0120f80e8181610c1a11c19128211300428c2506c150b0090ac1d0c023044070501e05427018290142d010000a807690130fc290140705023044090ac2506c150b01d,0x11801610c1a11c2a01c0703809028150201903c1d0242102c2d0100007c0503e071782a01c15020000640f3b02a01c2102c0001c0e3b82a01c0902800054081682a01c1d024000840b3b42d0102a01c00,0x10240a0a80701c0e000260900e0681f010220a016825b704c3f03e07058430986008859068470a4120941b0a80701c0e0240a054080640f0840b074090b4040001f016086e8120f8290482506c2216426,0x102c1f0401d0241903c1502009028070382a01c00098280581a038040882482a0905c7208cd209c9206c1303c37016080941b0a4120a807054080b4040001f0418a04d9f0b4040840b074090640f05408,0x10b4040840b07c10074090640f0240a054080a80701c0e000160680e010260a20c63013154248282d0102102c1f0401d0241903c09028150202a01c0703800098160680e0102808a0b59c136242d01021,0x107c100840b0b404000040a60e834171c80f0701b04c2a01c00010262918e04c21094d908c7f0a20c0b4040840b07c10074090640f054080240a0a80701c0e0001a03804058268358b094d604c5208a0b,0x101c1f0400001020680226342d0102102c1f0401d0241502009028070381903c2a01c000581a03827048040a02483dab090da08c7f03c1c06c1305c7e04c5f098a40a80701c0e0240a054080640f07409,
0x12c42a01c04080000a4aa1802a01c0408000098a91642a01c0408000088a82181f040040800006ca70cc1f040040800005ca60d42d0100408000094a583c2535c298381317c171f8262901b04c0f0702a,0x10240a01c0e0a807088a8094a50102004a10038ab002110f8040800e2ac0004a106a8130fc040802a01c0703809028222a0262a415020252941903c1b29c1d0241f0402102c17298292a82d01000038ab,0x5b40b4040a4aa098a90840b07c100740906ca70640f05ca605408
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check177 : ¬ FormulaSat (caseFormula c177) := checkW_sound _ k177 10 w177 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good177 : caseGood c177=true := by decide +kernel
theorem next177 {chosen region} (disj : ∀ i∈c177.prior, chosen i=false) (O : Later c177.prior chosen region) : ∃ g∈c177.groups, Matches chosen g := case_conclusion _ good177 check177 disj O
def c192 : Case := ⟨[7, 8],[7, 8],[
s0,s1,s2,s3,s4,s5,s6,s7,s82,s83,s146,s177,
s240,s916,s917,s1247,s1513,s1578,s1645,s1646,s1722,s1723,s1724
],[
t1,t3,t6,t19,t23,t24,t25,t26,t27,t31,t32,t33,
t35,t41,t42,t43,t44,t45,t46,t47,t49,t50,t51,t52,
t54,t55,t56,t58,t59,t60,t61,t62,t63,t64,t65,t68,
t69,t70,t71,t72,t73,t77,t79,t80,t81,t82,t85,t86,
t87,t88,t90,t93,t94,t95,t99,t100,t101,t102,t105,t106,
t110,t111,t113,t114,t115,t116,t117,t118,t119,t120,t121,t122,
t123,t124,t125,t127,t128,t129,t130,t131,t132,t133,t134,t135,
t138,t139,t142,t143,t145,t146,t147,t148,t150,t151,t152,t156,
t158,t159,t160,t161,t164,t165,t168,t176,t183,t184,t188,t190,
t193,t195,t197,t198,t200,t201,t202,t203,t204,t205,t206,t207,
t208,t209,t211,t212,t213,t214,t215,t216,t217,t218,t219,t221,
t224,t228,t229,t232,t234,t235,t236,t239,t240,t241,t242,t243,
t245,t246,t247,t248,t250,t251,t252,t253,t254,t255,t256,t257,
t258,t260,t261,t262,t263,t269,t271,t283,t284,t285,t286,t287,
t288,t289,t292,t294,t295,t296,t297,t298,t299,t300,t301,t302,
t303,t304,t305,t306,t308,t311,t314,t315,t316,t323,t327,t328,
t330,t331,t335,t336,t337,t340,t342,t344,t347,t348,t350,t351,
t352,t353,t354,t355,t356,t360,t361,t364,t375,t376,t377,t378,
t379,t380,t381,t382,t383,t384,t385,t387
],[
g0,g1,g2,g4,g8,g16,g32,g256,g512,g1024,g2048,g4096,
g8192,g16384,g32768,g65536,g131072,g262144,g524288,g1048576,g2097152,g48,g272,g288,
g528,g544,g768,g1040,g2080,g3072,g5120,g6144,g9216,g10240,g12288,g16640,
g17408,g18432,g20480,g24576,g33280,g33792,g34816,g36864,g40960,g49152,g65552,g66560,
g131104,g133120,g196608,g266240,g327680,g393216,g532480,g589824,g655360,g786432,g1048832,g1064960,
g1114112,g1179648,g1310720,g1572864,g2097664,g2129920,g2162688,g2228224,g2359296,g2621440,g3145728,g49,
g274,g548,g776,g11264,g21504,g38912,g57344,g66576,g133152,g720896,g1065216,g1376256,
g2130432,g2490368,g3670016,g816,g11265,g21506,g30720,g38916,g46080,g52224,g57352,g720897,
g1376258,g1966080,g2490372,g2949120,g3342336,g3670024,g11313,g21778,g39460,g58120,g720945,g1376530,
g2490916,g3670792,g732161,g1397762,g2529284,g3727368,g732209,g1398034,g2529828,g3728136
]⟩
def k192 : List Nat := [
1,2,132,133,134,135,225,226,136,137,83,84,
227,138,139,228,229,85,53,140,54,55,86,87,
88,141,142,230,231,143,30,89,232,90,91,37,
31,92,93,233,56,57,70,144,234,94,145,111,
71,235,58,42,236,237,146,147,148,149,95,150,
151,152,238,239,240,72,153,112,241,242,43,154,
113,17,59,114,155,156,243,115,116,12,73,117,
244,157,158,245,246,159,160,161,162,247,248,249,
44,45,74,250,163,32,164,165,33,38,18,118,
60,96,119,166,251,252,253,120,22,254,167,13,
168,169,97,23,24,98,255,256,257,258,259,170,
260,99,171,261,172,262,263,173,264,75,174,100,
175,265,121,266,267,268,269,270,122,176,177,178,
46,76,123,271,77,179,272,273,101,274,180,275,
276,277,102,278,279,280,61,62,281,181,282,182,
283,284,285,34,183,25,286,184,185,186,124,103,
125,187,104,63,105,64,188,189,126,47,35,127,
190,287,78,191,192,193,8,194,288,106,289,290,
195,291,292,196,293,197,198,199,19,48,200,39,
294,295,201,296,40,36,65,49,20,297,298,202,
299,300,301,302,203,107,204,26,27,303,304,305,
306,307,308,309,310,311,312,313,314,315,316,317,
318,319,320,321,322,323,324,325,326,327,328,329,
330,331,332,333,334,335,336,337,338,339,340,341,
342,343,344,345,346,347,348,349,350,351,352,353,
354,355,356,357,358,359,360,361,362,363,364,365,
366,367,368,369,370,371,372,373,374,375,376,377,
378,379,380,381,382,383,384,385,386,387,388,389,
390,391,392,393,394,395,396,397,398,399,400,401,
402,403,404,405,406,407,408,409,410,411,412,413,
414,415,416,417,418,419,420
]
def w192 : List Nat := [
0x1058140480c0280801802015a64bc110040f000000b02a0a026090220801e0701a06016050120300a02006010036952e0440103c000002c0a82809824088200781c06818058140480c0280801804009a4,0x10a82809824088200781c06818058140480c0280601002025a84c4110040f000000b02a0a026090220801e0701a06016050120300a020040080769d300440103c000002c0a82809824088200781c06818,0x1008136ad340440103c000002c0a82809824088200781c06818058140480a0200601002035aa4cc110040f000000b02a0a026090220801e0701a060160501203008018040080b6a5320440103c000002c,0x10701a060140480c0280801804008176b5360440103c000002c0a82809824088200781c06818058120300a0200601002055ac4d4110040f000000b02a0a026090220801e0701a060160500c0280801804,0x1000000b02a0a026090220801e07018058140480c02808018040081b6bd380440103c000002c0a82809824088200781c06816050120300a0200601002065ae4dc110040f000000b02a0a026090220801e,0x10200601002085b24ec110040f000000b02a0a026090220801c06818058140480c02808018040081f6c53a0440103c000002c0a82809824088200781a06016050120300a0200601002075b04e4110040f,0x10801e0701a06016050120300a0200601002095b44f4110040f000000b02a0a026090200781c06818058140480c0280801804008236cd3c0440103c000002c0a828098240881e0701a06016050120300a,0x10440103c000002c0a826090220801e0701a06016050120300a02006010020a5b64fc110040f000000b02a0a024088200781c06818058140480c0280801804008276d53e0440103c000002c0a82809822,0x10501202006010020340b6e5420440103c000002a0a026090220801e0701a06016050120300a02006010020b5b8504110040f000000b02809824088200781c06818058140480c02808018040082b6dd40,0x10a026090220801e0701a060160500a020060100204c0d6ed440440103c000002c0a82809824088200781c068180581403008018040081302dba50c110040f000000b02a0a026090220801e0701a06016,0x104dbe51c110040f000000b02a0a026090220801e0701a060160480a02006010020540d6f5460440103c000002c0a82809824088200781c068180581203008018040081502dbc514110040f000000b02a,0x10681605012028080180400819035c0524110040f000000b02a0a026090220801e0701a060140480c020060100205c0b6fd480440103c000002c0a82809824088200781c068180580c028080180400815,
0x10002c0a82809824088200781c060140480c02808018040081b05dc252c110040f000000b02a0a026090220801e0701a050120300a0200601002064177054a0440103c000002c0a82809824088200781c,0x101002074197154e0440103c000002c0a82809824088200781a060140480c02808018040081d05dc4534110040f000000b02a0a026090220801e07016050120300a020060100206c1970d4c0440103c00,0x10801c06818058140300a020060100207c1371d500440103c000002c0a828098240882007818058140480c02808018040081d06dc653c110040f000000b02a0a026090220801e06816050120300a02006,0x10040f000000b02a0a026090220801c06816050120300a020060100207c19725520440103c000002c0a82809824088200701a060140480c02808018040081f05dc8544110040f000000b02a0a02609022,0x1028080180400821055cc554110040f000000b02a0a026090220801a06016050120300a020060100207c1d72d540440103c000002c0a828098240882007018058140480c02808018040081f06dca54c11,0x1098240881e0701a058140480c028080180400821065ce55c110040f000000b02a0a026090220781c06818050120300a020060100208417735560440103c000002c0a828098240881e0701a060160480c,0x17455a0440103c000002c0a828098240881e06818058140480c028080180400821075d0564110040f000000b02a0a026090220781c06016050120300a02006010020841b73d580440103c000002c0a828,0x1050120300a020060100208c1774d5c0440103c000002c0a828098240801e0701a060160501203008018040082302dd256c110040f000000b02a0a026090220701a06016050120300a02006010020841f,0x10b02a0a026088200781c06816050120300a0200601002094197555e0440103c000002c0a828098220801e0701a0601605012028080180400825035d4574110040f000000b02a0a026090200781c06818,0x10082708dd8584110040f000000b02a0a024088200781c06016050120300a020060100209c1b75d600440103c000002c0a828098200781c06818058140480c02808018040082508dd657c110040f00000,0x106818058140480c028080180400829075da58c110040f000000b02a0a0220801e0701a06016050120300a020060100209c25765620440103c000002c0a828090200781c06818058140480c0280801804,0x103c000002c0a826088200781c06818058140480c028080180400829095dc594110040f000000b02a098240801e0701a06016050120300a02006010020a42376d640440103c000002c0a826090220801e,
0x102006010020ac1f77d680440103c000002c0a026090220801e0701a060160500c02808018040082b04dde59c110040f000000b02a090220801e0701a06016050120300a02006010020a4277756604401,0x10801e0701a06016050120300a02006010020ac257856a0440103c000002c0a026090200781c06818058140480c02808018040082b08de05a4110040f000000b02809824088200701a06016050120300a,0x15b4110040f000000b026090220801e0701a06016050120300a02006010020ac2978d6c0440103c000002c0a024088200781c06818058140480c02808018040082b09de25ac110040f000000b02809822,0x10480c02808018040082d08de65bc110040f000000a828098240881e0701a06016050120300a02006010020b4217956e0440103c000002a0a026090220801e0701a060160480c02808018040082d055e4,0x10a024088200781c06818058140480c02808018040082d09de85c4110040f000000a828098220801e0701a06016050120300a02006010020b42579d700440103c000002a0a026090200781c0681805814,0x102c037ad740440103c000002809824088200781c06818058140480c02808018040082d0adea5cc110040f000000a826090220801e0701a06016050120300a02006010020b4297a5720440103c000002a,0x10701a060160480a0200400815034077b5760440103c000002c0a82809824088200781c0681805814030080180204c0b015ec5d4110040f000000b02a0a026090220801e0701a0601605012020060100d,0x1000000b02a0a026090220801e068140480c02808018040081d064177bd780440103c000002c0a82809824088200781c068180580c028060100205413025ee5dc110040f000000b02a0a026090220801e,0x1010020841f075f25ec110040f000000b02a0a026090220781c058140480c02808018040082106c197c57a0440103c000002c0a828098240882007018050120300a020060100207c1b05df05e4110040f,0x10801e0701a058140480a020060100209419035f45f4110040f000000b02a0a026090200781c068180501203008018040082305c0b7cd7c0440103c000002c0a828098240881a06016050120300a02006,0x10440103c000002c0a026090220801c06818058140300a02006010020ac1f04df65fc110040f000000b02a098200781c06818058140480c028080180400829094237d57e0440103c000002c0a82809822,0x102808018040082d09c257e5820440103c000002a0a026090220781c06818058120300a02006010020b421055f8604110040f000000b028090200781c06818058140480c02808018040082b09c237dd80,
0x10a026090220801e0701a060160200601002054130340b7ed840440103c0000026090220801e0701a06016050120300a02006010020b42b0a5fa60c110040f000000a828088200781c06818058140480c,0x1065fe61c110040f000000b02a0a026090220801c060140480c028080180207c1b05c057f5860440103c000002c0a82809824088200781a050120300a020060101d0641700dfc614110040f000000b02a,0x10480c0280801804008210741b05e00624110040f000000b02a0a026090220781c058140480c02808010020841b064077fd880440103c000002c0a8280982408820058140480c02808018040081f0741b,0x10002c0a828098240881a06016050120300a018040082107c1d0260262c110040f000000b02a0a026090220701a050120300a02006010020841f064178058a0440103c000002c0a828098240881e06014,0x10ac2909c258158e0440103c000002c0a0240801e0701a06016050120300a020060082b09c2301604634110040f000000b02a098200781c06818058140480c02808018040a42508c0380d8c0440103c00,0x106016050120300a02006010020b42909c2381d900440103c000002a0a0220801e0701a06016050120300a020040082d09c2501e0663c110040f000000b0220801e0701a06016050120300a0200601002,0x10040f0000009824088200781c06818058140480c02806010020b42b0a409825920440103c0000028098200781c06818058140480c02808018040082d0ac2508e08644110040f000000a8240801e0701a,0x10082106c190540d01e0c654110040f000000b02a0a026090220801c06014030080180207c1b05c1302c0582d940440103c000002c0a82809824088200781a05012020060101d064170340b00e0a64c11,0x10801e0701a06016050120200601029094230340b00e0e65c110040f000000b02a0a02609022068180580c02806010020841f0741504c09835960440103c000002c0a828098240881e070160480a02004,0x18459a0440103c000002a0a0220801e0701a060160480a020040082d09c250540d01e10664110040f000000b028090200781c068180581403008018020ac2708c1302c0583d980440103c000002c0a826,0x1020060082b09c2307c1b05c0584d9c0440103c000002c0a8260801e068140480c02808018040a42508c1d0641700e1266c110040f0000009824088200781c068180580c02806010020b42b0a41504c09,0x1098240881a06016050120300a018040082d0ac290841f074098559e0440103c000002a0a0220781c058140480c02808010020b4270942106c1901e14674110040f000000b0280902007018050120300a,
0x10540d01e18684110040f000000b02809020070180500c020060082b09c2307c1b05c1302c0585da00440103c000002c0a8260801e0681404808018040a42508c1d064170340b00e1667c110040f00000,0x11581e0441c1dc08328000b42b0a4210561a68c110040f00000098240881a060160300a018040082d0ac290841f0741504c09865a20440103c000002a0a0220781c0581202808010020b4270942106c19,0x186e1504ca20561a020ca070770781101c3606c400143508c5509c57034270642305c0700c5402c49094560002d0ac29084cc86412238070d81b100050d4231542715c0d09c1908c1701c031500b12425,0x10b42b0a4cd86c13288070d81b100050d4231542715c0d09c1908c1701c031500b124251581d2d41f31421330000b42b0a414871fa0260900024088200781c06818058260280c0a406010020b42b05012,0x12e81329c191f0152940b0300d1d81d2d809298031d4273182130c29334000b42b0921d8440847c12450148701f3141d2d4213300b1241701c1908c0d09c2715c251582315403150070d81b100050d400,0x11a81b180192a0000b4280982587a080891b0921d00c750347602c0c09cc60647c05cba074b6084c3054a507cc404ca7024a60a4cd06c4001c36014350002d0ac1b7a823468070d81b100050d41f31017,0x10a8120300802802018040b422086206e015790000a0260902a0601e0701a048160300802802018040b4220821f79c2345c211d0151cc1701c030540b0301f05c1d05813068090642b06c0d2ec0732c05,0x10a026105e60847b0547008a21000240a8180781c068120580c0200a008060a02d0980488a200821f000260902a0601e0701a048160300802802018280b40408a217e014794000a0260901e0701a06016,0x1054f506d2401cfd05c0700c1502c0c07c170741604c1a024190ac1b0143408c3d098410002d0a02413a220961e0146a06c6001ccb034bb064a805c0700c1502c0c07c170741604c1a024190ac1b0002d,0x106c050d0230f4190f0211e82413826104000b4280680c891f9054c905c0700c1502c0c07c170741604c1a024190ac1b0143408c3d0643c0847a0904e098410002d0a01a0300688de80643c034be084f6,0x105813068090642b06c050d0230f42610424138000b428068ce47807840000a0220801e0701a060160480a020040082d09c250a81503625818151a00688c1701c030540b0301f05c1d05813068090642b,0x1094210a81b03227860141f81701c030540b0301f05c1d05813068090642b06c050d0230f4062dc24138200f0181801a33826104000b42803626894142f80c890190f0211e81701c030540b0301f05c1d,
0x133c2b06c000b4278a227036260803c018b706060068ce0904e08c3d014340984105c0700c1502c0c07c170741604c1a024190ac1b0002d0a0cf1a014850000a0220781c058070481902808010020b427,0x100c150002d0aa2a460227a400010200781c0681805814048080280c008290182a0b42409a2981c224640b03013068090640722c252d01701c0d09c1908c03054210441f05c1d058051a81b0801507c28,0x176c226d82d00800090040801e0081a06016050120302a02006098290281c8ae2a0ac1b0002d00a2909e280146a084110642303427094b406c200541f01c8b0a0cf04c1a07c1702c0c05c070241907416,0x1070028b62c0642303427014f805ca302c4900d2701c2b06c200541f0841107c2504c210242c0b4020002a0a42609031768230b41c8ac2d00800010200780206818058140480c0a808018260a42402a2c,0x10002a0a426060160300a8be2d0742601c2b06c200541f0841107c2504c210242c0144c090310b4020002a0a426060160300a00a2e770237d42d00800098200782a06818058140480c028080180409429,0x107c210441f09413084090b005130240c42d008000a8290981805a311340319c0a8bc240c4000a829098180580c8c2030746e088f700a2e01c2b06c200541f0841107c2504c210242c0144c090310b402,0x10801507c210441f09413084090b005130240c4222901c1a4160780208c183402d008000a8290980c8c826070b200c1d05a31090310002a0a426060d08380a1841d0a4223e40209c0c8c0070ac1b08015,0x10841107c2506c200541f0242c01c2b0b4020002a0a4038580a1840c8c8160781c1a4222900208c1834005130240c4070ac1b0801507c210441f09413084090b02d008000a82909a338480b19c070ac1b,0x10781c02018058140480c02827018040a00209235760226d42d008000a02a0801e0700806016050120300a09c06010020901a8d1dd0951008d0f074a00649f05c9e0349d02c9c014e400ce309a3304c21,0x14a01f32013498054941d2801927c172780d2740b270033cc2900c2d008000a827011d908d0e06c48092350b402000200781c02018058140480c028270182a0a00400a3675c230e81a8d02d008000a820,0x10a02a0501a8e63706c480a40309c040b4020002a060160081c0300a078120100808006050258e1d6089b40b40200028098200781c0a818058140480c02808018040081a096378d8094a4214a81532407,0x109c040002a060160081c0300a0781201008080060523b6bc230e81a8e42d00800020200781c09818058040480c0080a018280a8240523a6cc226902d00800090080801e0702606016010120300202806,
0x1010080823e1a01469c2d008000a026090220801e0702a06016030120100a02002068078f5ac0947308c7006c900523b0a40309c040b4020002a060160081c0300a0781201008080068f23a096380a403,0x1028280a8040080808640730146c82d008000a0260901e0700606016088120300a0202a010020841a8fcee06c3800018084073463d0949b08cf006c3801a3c0a40309c040002a060160081c0300a07812,0x1022410a40309c040b4020002a060160081c0300a078120124290007344231ec251d0208f82900c27010000a818058020700c0281e048040224173c154841a8fc2d00800098240781c01818058220480c,0x1090220801e0701a060160300a04c060a80201008911a6054b90949a08c6f084ed06c37024e001c85012420a40309c040b4020002a060160081c0300a0781290da80548e094f208cf1084ef06c4501ce1,0x191a450143e01cb80947208c990849806c5d04a430a40309c040002a060160081c0300a078d27b814398089102d0080009824088200781c068180580c028130a02a00806012456f8146ac2d008000a026,0x10a80201021921ca069b10b40200028098240881c0a818058140480c028080181f008040824771c050f8212601b1742900c0724c09250231c42701025198152581e3482d008000a818058020700c02813,0x106c3701249000240881c0a818058140480c02808098280080607e4a9202091c00098240881c0a818058140480c02808018280081f012492c01a7442d008000a0260902207012060160501f0300a02006,0x104a4c6f0146a42d008000a0260902002c0c0701a060160102a02006078020482292cac04c5d0001602c1b1ae4a04e460946608c71054960249401c93078d20a40309c040002a060160081c0300a34c92,0x105814030080182a0080b04e4e930052302900c2701009234072fc2111c251341f1781b1ac0a34c000a818058020700c04a4d748151c02292c2d00800098240800b0301c06818058280a8080181e00804,0x111c251341b1ac2d008000a818058020700b04e4f9381540423264129341f1781b1ac2111c072fc25134092340a34c2900c27010000a818058020700c0c9ec011ba0b4020002809824088200781c06818,0x1070120680609014941b90550004e4f06c6b084470944d01c880148709c0407c2f0243008c2a030320a4030b4020002a060160081c02c4f7ec143fc270101f0bc090c0230a82900c0521c072200c0c821,0x10481a01a526f4052e414940270101f0bc090c0230a82900c0b13c210fc0c0c82d008000a818058020701206806092516a8053f8270101f0bc090c0230a82900c0b13c210fc0c0c82d008000a81805802,
0x10949b0148501a520843f09c0407c2f0243008c2a030320a40302c4f0b4020002a060160081c0481a94dd4054730149a0925109c0407c2f0243008c2a0a40302c4f0843f030320b4020002a060160081c,0x108c2d09426070500b4020002a06016008131b1bb0143e01cb8055020947204a530843f06e5402c4f08c2a0243007c2f030320a40309c040b4020002a060160081c1407e05490000180341b951ed050e5,0x10100207c0895a02080ad0a40309c040144602c390342901c4a08c2d094260546304c6c070500b4020002a060160081a07c099560d080ad078ec0211c050eb06c5d0a40309c040144602c390342901c4a,0x1050220300a07406010020680896256026550a40309c040144602c390342901c4a08c2d094260546304c6c070500002a060160081a07e577c82072c2d008000a026090220a81a06016050120300a07406,0x101446070500a40309c040b4020002a06016008d4960093a81f95c2900c27010051180b0e40d0a407128230b4250981518c131b01c140000a8180580206a59740206c02d008000a0260901e0a81206016,0x1210092182531c132f015300232c41d1b81f2442125c1b3542900c023502d008000a8180580c968b008106078e80002800c1b355c60850d07c78024e206a590546304c6c0942608c2d01c4a0342902c39,0x107020078170681805012030080a8040080602e5b7ac0a1840c9682125c1f2441b3541d1b815300132f02531c232c409218072100520c023502900c270102d008000a818058286940b19c270100520c07,0x10002a0601a078200725e9700b96c00098240a020078170681805012030080a8040081c01a5d6b42374c2d008000a026090200781c0301805012068170202a010020180a971f3089bf0b4020002809824,0x10681e981c401d2008c2d02c390725e09c040341800c1d054240940b0a403014580245904c5a058280b4020002a0601a0782097e5d01ce709c040341800c1d054240940b0a403014580245904c5a05828,0x1980131680916405160270100d06003074150902502c2900c160a02d008000a8180686d7341d42c07344231ec0b11c2097c270100d06003074150902502c2900c051600916413168160a02d008000a818,0x1074150902502c2900c09114230e8070e0211e4160a01d1e01a1b4000a81807c12989fd011f00b402000280982408820070180502a0301f0200606c0205c1202a617201d2b807308211e4231c40b1781e,0x11b4131f4052a41f358160a02d008000a8180826382c0a0f8041f4129881d1e0211e4270100d06003074150902502c2900c160a009114230e8070e01a1b42d008000a81807cd69840b2b0270100d06003,
0x10710a0826304c7d02c8f014a907cd601c3808c3a024450686d054240940b0341800c1d058280a40309c040b4020002a060147081d410270100d06003074150902502c2900c09114230e8070e00b23c1a,0x105c0235e640850904c120241309c0408c10014520542e01c5306c620940b0a40302c2206014034180002a05c0207a657bc1c7042d008000a026090220a80c0281a050120081702006010190801e99200,0x10542e01c5306c620940b0a403070690601407c890848a008d70b4020002a05c0c99a0108105074ae07a650341802c2204c120241309c0408c10014520542e01c5306c620940b0a403060140b4020002a,0x10482a02006010020800d072678280a1840c998212281f2241c1a40235c1b188150b82502c0714c05148130480904c2701023040180502900c2d008000a8170cdfc02c6704c120241309c0408c1001452,0x10801e02816050120082a02006064260101c9a6670742904c120241309c0408c100a40302c2200c1e05c3301c5b0545c014aa060140002a0681e0800d9a1c0095f40b40200028098220781a0281606414,0x104c120241309c0408c100a40302c2200c1e05c3301c5b0545c060140002a0681e0826b714250981c9a42d008000680c088280780a05814048020a80801819098200126a754246b82d008000a01a03022,0x148c0d0fc251d0209ac130480904c27010230402900c0b08803078170cc0716c1517018050000a81a07a6d4301c7382d008000a026090220781a028160501203006020190a802010219b26a03668014aa,0x100c0b0880307818050050dc170cc251201a1fc2d008000a81f361c9075080149209466084af0349507a6d0545c01c5b04c120241309c0408c100a40302c2200c1e05c33060140b4020002a0687f9b005,0x1030149bdc30542e01d03034e904c120241309c0408c100a40302c2200c1e0143705c3309448074ab07cd8060140687f0b4020002a0826e7f81c41c1548807308212bc0d254130480904c270102304029,0x1000240881e028160a8120841c020190100206c260a2710b8071a0149bc00098240881e028160a8120841c020190100206c28032707fc067c42d008000a026090220780a0582a0482107008064040081b,0x10000d0352c0b4020a80500009024fc0b4020a8050001d01a710826e074ab07cd809448014370687f02c2200c1e05c3308c100241304c120601409c040a4030b4020002a0160c0182e0507e032700b402,0x10201903c1d018210282d008000580208c0409a72474223ec050dc2a014000581b0707c0a805054080001903d2b0a8050840a000070392d0a8050240900015020770a8050740600021028760a80507406,
0x108c129cdf702cb309a7204cbd07c4b06c1c094640a4650a80501c0e024090340d054080640f074060840a0b4020001600823010d97800b17c1f12c1b0702519029194132f42a01407038090240d03415,0x11901f12c1b0702a01407038090240d034150201903c1d018210282d008000580208c428100b2301f12c1b0702519029194261bc043642a01407038090240d034150201903c1d018210282d0080005802,0x109cf40947206c1c0143b08c420a805000160081e0a0133685f029de0b4020840a07406054080640f0340d0240901c0e0a8050002607822068160a002010130927483c0a0f8129cc261bc043642919425,0x10840a0b402000160081e0a0db9d40b17c1b070050ec23108133682a01400058020782809a76784246dc2d008210281d0181903c150200d03409024070382a01400048220781a058040a0020980a9d674,0x14581b070050ec23108130842836c2a01407038090240d034150201903c1d018210282d0080005802078279dde202cc10951309a7604cda06c1c0143b08c420a80501c0e024090340d054080640f07406,0x10240901c0e0840a0a805000260902207c1a058040082802a7978c254540b17c279dc130842836c1b070050ec231082d0082a014070380d03409024150201903c1d01821028000580207a788140b30424,0x13e82a0141610c00098449e80320000058431d4274442a0142d0080000c809e42519829094272840b1781e9e0050ec231081b070150202d0082a01400058029e9df04df60b402074060640f054080340d,0x10201903c1d0182102825204293702d00800028df12c1e1442220800068de320261101e14400010dd284261101e144000888228c1610c25204000a4dc4481610c2611000078512c81d0181610c0009481,0x1054080340d0240901c0e00c800a805098440888207851068de05843010dd04a7b028df0027c2cc261100a37c0004a7b84c130f81610c1a37822208261102a0140320007038090241e1440d0340437415,0x6170b4020a4dc094810840a074060640f
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check192 : ¬ FormulaSat (caseFormula c192) := checkW_sound _ k192 10 w192 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good192 : caseGood c192=true := by decide +kernel
theorem next192 {chosen region} (disj : ∀ i∈c192.prior, chosen i=false) (O : Later c192.prior chosen region) : ∃ g∈c192.groups, Matches chosen g := case_conclusion _ good192 check192 disj O
def c480 : Case := ⟨[6, 7, 8, 9],[6, 7, 8, 9],[
s0,s1,s2,s3,s4,s5,s177,s178,s186,s200,s278,s304,
s324,s916,s917,s1031,s1073,s1247,s1513,s1578,s1645,s1646,s1722,s1723,
s1724
],[
t24,t25,t26,t27,t32,t33,t42,t43,t44,t46,t50,t51,
t52,t53,t54,t55,t59,t60,t61,t63,t64,t69,t71,t72,
t73,t79,t80,t81,t86,t88,t89,t90,t93,t94,t95,t96,
t100,t101,t102,t103,t105,t106,t110,t114,t115,t116,t118,t119,
t120,t121,t122,t123,t124,t128,t129,t131,t132,t133,t134,t135,
t138,t142,t143,t145,t146,t147,t148,t150,t151,t152,t158,t159,
t160,t161,t186,t188,t190,t191,t193,t195,t197,t198,t200,t201,
t203,t207,t208,t209,t211,t212,t213,t214,t215,t216,t217,t218,
t219,t221,t224,t228,t229,t232,t234,t235,t236,t238,t239,t240,
t242,t243,t246,t247,t248,t250,t251,t252,t253,t254,t255,t256,
t257,t258,t262,t267,t271,t284,t286,t287,t299,t300,t304,t306,
t307,t308,t309,t310,t311,t312,t314,t325,t326,t328,t329,t330,
t331,t335,t336,t337,t340,t342,t348,t350,t351,t353,t354,t356,
t357,t360,t375,t376,t377,t378,t379,t380,t381,t382,t383,t384,
t385
],[
g0,g1,g2,g4,g8,g16,g512,g1024,g2048,g4096,g8192,g16384,
g32768,g65536,g131072,g262144,g524288,g1048576,g2097152,g17,g18,g516,g520,g528,
g1040,g3072,g5120,g6144,g9216,g10240,g12288,g17408,g18432,g20480,g24576,g33280,
g33792,g34816,g36864,g40960,g49152,g65552,g66560,g133120,g196608,g266240,g327680,g393216,
g532480,g589824,g655360,g786432,g1064960,g1114112,g1179648,g1310720,g1572864,g2097664,g2129920,g2162688,
g2228224,g2359296,g2621440,g3145728,g11264,g21504,g38912,g57344,g66576,g720896,g1376256,g2130432,
g2490368,g3670016,g11265,g21506,g30720,g38916,g46080,g52224,g57352,g720897,g1376258,g1966080,
g2490372,g2949120,g3342336,g3670024,g11281,g21522,g39428,g57864,g720913,g1376274,g2490884,g3670536,
g732161,g1397762,g2529284,g3727368,g732177,g1397778,g2529796,g3727880
]⟩
def k480 : List Nat := [
1,2,3,4,153,89,90,91,92,93,66,67,
154,155,156,157,158,159,160,161,162,94,46,95,
47,48,96,97,98,99,68,163,164,28,69,100,
49,165,166,101,167,168,70,42,102,103,169,170,
171,50,104,172,173,71,174,105,175,106,72,43,
19,176,107,108,177,109,15,73,178,74,179,110,
180,111,112,113,181,114,182,35,36,51,20,115,
21,29,18,75,37,116,117,76,38,183,118,22,
184,119,16,120,77,23,24,78,30,185,186,187,
188,121,189,190,122,123,79,191,192,124,193,194,
195,196,197,198,125,199,80,200,126,201,52,127,
202,203,204,205,206,207,208,209,210,211,212,53,
54,213,128,214,215,216,217,129,130,218,219,55,
81,131,82,83,132,133,220,56,134,17,57,135,
221,136,31,222,39,223,137,224,138,225,139,226,
58,227,84,228,40,229,59,230,231,140,232,233,
234,141,235,60,142,25,236,237,238,239,240,241,
242,243,244,245,246,247,248,249,250,251,252,253,
254,255,256,257,258,259,260,261,262,263,264,265,
266,267,268,269,270,271,272,273,274,275,276,277,
278,279,280,281,282,283,284,285,286,287,288,289,
290,291,292,293,294,295,296,297,298,299,300,301,
302,303,304,305,306,307,308,309,310,311,312,313,
314,315,316,317,318,319,320,321,322,323,324,325,
326,327,328,329,330,331,332,333,334,335,336,337,
338,339
]
def w480 : List Nat := [
0x10280801802015553b01300c110080f0040d000000b02a0a026090220801e0701a060160500a0200601003550eb04c030440203c01034000002c0a82809824088200781c0681805814028080180400953,0x10781c06818058140280601002025573b81300c110080f0040d000000b02a0a026090220801e0701a060160500a0200400807558ed04c030440203c01034000002c0a82809824088200781c0681805814,0x10a82809824088200781c068180580a0200601002055593c01300c110080f0040d000000b02a0a026090220801e0701a0601605008018040080b560ef04c030440203c01034000002c0a8280982408820,0x103c01034000002c0a82809824088200781c068160500a02006010020655b3c81300c110080f0040d000000b02a0a026090220801e0701a06014028080180400817568f104c030440203c01034000002c,0x1578f504c030440203c01034000002c0a82809824088200781a060160500a02006010020755d3d01300c110080f0040d000000b02a0a026090220801e070180581402808018040081b570f304c0304402,0x1028080180400823580f704c030440203c01034000002c0a828098240881e0701a060160500a02006010020855f3d81300c110080f0040d000000b02a0a026090220801c068180581402808018040081f,0x10781c0681805814028080180400827588f904c030440203c01034000002c0a828098220801e0701a060160500a0200601002095613e01300c110080f0040d000000b02a0a026090200781c0681805814,0x10b02809824088200781c068180581402808018040082b590fb04c030440203c01034000002c0a826090220801e0701a060160500a02006010020a5633e81300c110080f0040d000000b02a0a02408820,0x10080f0040d000000b02a0a026090220801e0701a06016050080180402c03598fd04c030440203c01034000002a0a026090220801e0701a060160500a02006010020b5653f01300c110080f0040d00000,0x1025694001300c110080f0040d000000b02a0a026090220801e0701a060160280801002054075a0ff04c030440203c01034000002c0a82809824088200781c0681805814020060080b015673f81300c11,0x105008018040081702d6b4081300c110080f0040d000000b02a0a026090220801e0701a0601602006010020540b5a90104c030440203c01034000002c0a82809824088200781c068180580a0180400815,0x1088200781c0601402808018040081b05d6d4101300c110080f0040d000000b02a0a026090220801e0701a0500a0200601002064175b10304c030440203c01034000002c0a82809824088200781c06818,
0x10002c0a82809824088200781a0601402808018040081d05d6f4181300c110080f0040d000000b02a0a026090220801e070160500a020060100206c195b90504c030440203c01034000002c0a82809824,0x10440203c01034000002c0a8280982408820078180581402808018040081d06d714201300c110080f0040d000000b02a0a026090220801e068160500a0200601002074195c10704c030440203c0103400,0x107c1b5d10b04c030440203c01034000002c0a82809824088200701a0581402808018040081f065734281300c110080f0040d000000b02a0a026090220801c068180500a020060100207c175c90904c03,0x10580a0200601002084155d90d04c030440203c01034000002c0a8280982408820068180581402808018040081f075754301300c110080f0040d000000b02a0a026090220801c060160500a0200601002,0x1090220781c068160500a0200601002084195e10f04c030440203c01034000002c0a828098240881e0701a0601402808018040082105d774381300c110080f0040d000000b02a0a026090220781c06818,0x1000000b02a0a026090220781a060160500a02006010020841d5e91104c030440203c01034000002c0a828098240881e070180581402808018040082106d794401300c110080f0040d000000b02a0a026,0x100c110080f0040d000000b02a0a026090200781c0681805814020060100208c0b5f11304c030440203c01034000002c0a828098240881c068180581402808018040082107d7b4481300c110080f0040d,0x10082508d7f4581300c110080f0040d000000b02a0a026088200781c068160500a0200601002094195f91504c030440203c01034000002c0a828098240801e0701a0601402808018040082305d7d45013,0x10581402808018040082708d814601300c110080f0040d000000b02a0a024088200781c060160500a020060100209c1b6011704c030440203c01034000002c0a828098200781c06818058140280801804,0x1090220801e0681805814028080180400829075834681300c110080f0040d000000b02a0a0220801e0701a060160500a020060100209c256091904c030440203c01034000002c0a828090200781c06818,0x1034000002c0a826088200781c0681805814028080180400829095854701300c110080f0040d000000b02a098240801e0701a060160500a02006010020a4236111b04c030440203c01034000002c0a826,0x104c030440203c01034000002c0a026090220801c068180581402808018040082b07d874781300c110080f0040d000000b02a090220801e0701a060160500a02006010020a4276191d04c030440203c01,
0x1010020ac276292104c030440203c01034000002c0a026088200781c068180581402808018040082b095894801300c110080f0040d000000b028098240801e0701a060160500a02006010020ac236211f,0x1068180580a02006010020b4156312304c030440203c01034000002c09824088200781c068180581402808018040082b0a58b4881300c110080f0040d000000b028090220801e0701a060160500a02006,0x1098240801e0701a060160500a02006010020b4236392504c030440203c01034000002a0a026090220781c068180581402808018040082d0858d4901300c110080f0040d000000a82809824088200781c,0x10040d000000a828090220801e0701a060160500a02006010020b4276412704c030440203c01034000002a0a026088200781c068180581402808018040082d0958f4981300c110080f0040d000000a828,0x14a81300c110080f0040d000000a026090220801e0701a060160500a02006010020b42b6492904c030440203c01034000002a09824088200781c068180581402808018040082d0a5914a01300c110080f,0x1010020841b065954b01300c110080f0040d000000b02a0a026090220801c0601402808018040081f06c176512b04c030440203c01034000002c0a82809824088200781a0500a02006010020741905d93,0x10701a06014020060100208c1702d974b81300c110080f0040d000000b02a0a02609022068180581402808018040082107c1d6592d04c030440203c01034000002c0a828098240881e070160500a02006,0x10a0240801e0701a060160500a02006010020ac2708d994c01300c110080f0040d000000b02a098200781c0681805814028080180400829094236612f04c030440203c01034000002c0a828098240801e,0x103c01034000002a0a0220801e0701a060160500a02006010020b4270959b4c81300c110080f0040d000000a828098240881e0701a0601602808018040082d084156693104c030440203c01034000002c,0x16793504c030440203c01034000002c0a82809824088200781a0500a020060101d0641700d9d4d01300c110080f0040d0000009824088200781c068180581402808018040082d0ac296713304c0304402,0x1010020841b064076813704c030440203c01034000002c0a82809824088200581402808018040081f0741b0659f4d81300c110080f0040d000000b02a0a026090220801c06014028080180207c1b05c05,0x10701a0500a02006010020841f064176893904c030440203c01034000002c0a828098240881e060140280801804008210741b05da14e01300c110080f0040d000000b02a0a026090220781c0581402808,
0x10b02a098200781c068180581402808018040a42508c036913b04c030440203c01034000002c0a828098240881a060160500a018040082107c1d025a34e81300c110080f0040d000000b02a0a02609022,0x10080f0040d000000b0220801e0701a060160500a02006010020ac2909c256993d04c030440203c01034000002c0a0240801e0701a060160500a020060082b09c23015a54f01300c110080f0040d00000,0x108da95001300c110080f0040d000000a8240801e0701a060160500a02006010020b42909c236a13f04c030440203c01034000002a0a0220801e0701a060160500a020040082d09c2501da74f81300c11,0x1018040741905c0b00dab5081300c110080f0040d0000009824088200781c068180581402806010020b42b0a4096a94104c030440203c010340000028098200781c068180581402808018040082d0ac25,0x10881e0701602808010020841b0641501dad5101300c110080f0040d000000b02a0a026090220801c06014020060081f06c1702c056b14304c030440203c01034000002c0a82809824088200781a05008,0x10002c0a8260801e0701a0601605008018040a42508c0b00daf5181300c110080f0040d000000b02a0a02609022068180580a018040082107c1d054096b94504c030440203c01034000002c0a82809824,0x10440203c01034000002a0a0220801e0701a0601602808010020b4270941501db15201300c110080f0040d000000b028090200781c0681805814020060082b09c2302c056c14704c030440203c0103400,0x105c056d14b04c030440203c01034000002c0a8260801e0681402808018040a42508c1d0641700db35281300c110080f0040d0000009824088200781c068180580a018040082d0ac29054096c94904c03,0x10082d0ac290841f074096d94d04c030440203c01034000002a0a0220781c0581402808010020b4270942106c1901db55301300c110080f0040d000000b02809020070180500a020060082b09c2307c1b,0x10701805008018020ac2708c1f06c1702c056e14f04c030440203c01034000002c0a8260801e068140200601029094230741905c0b00db75381300c110080f0040d00000098240881a060160500a01804,0x100000098240881a0601602806010020b42b0a42107c1d054096e95104c030440203c01034000002a0a0220781c0580a020040082d09c250841b0641501db95401300c110080f0040d000000b02809020,0x16f5bb020ea070750781101c2f06c3a0142e08c5f09c610642705c1000c5d02c32094600002d0ac29085bc6e8146d80009022068180581d02806010020b42b0a4210981f025bb5481300c110080f0040d,
0x109c27184251802317c03174070bc1b0e8050b8000b42b0a48e67015230096f400088200781c068180580a0a406010020b42b090266f9b2051aa00024088200781c068180580a0a406010020b42b09809,0x107c89024760a48e06c3a01c2f0142e0002d0ac196482335c070bc1b0e8050b81f22419140151d00b03c1d200091d8031281712c272282122029238000b42b091bf6f81f3801d358216f00b0c81704019,0x102802018040b422081c163c2334c21124151b00906017040030540b03c1f05c1d0582b06407234050ec1b130191dc000b42809825701a9088d8091bf05c4b00c4a02c0f09c8a06450074800848805474,0x1008060a02d09804711c2081c1000260902a0601e0701a0201602802018280b404089c366814634000a0260901e0701a060160a80802802018040b422085c259415630000a0260902a0601e0701a02016,0x1090220801e0701a0a8160100a020270082d01814715c4095c00143b06c4c01c8d064770241805c1000c1502c0f07c17074160ac190002d0a0260f18e0843705469089c3000240a8180781c068080580a,0x103c1f05c1d0582b064050b4230d4190d0211f424150260f0000b42806806719c5084b4054b306cdf01cb70241805c1000c1502c0f07c17074160ac190142d08c350983c0002d0a024150340619000028,0x1718190d0211f40906017040030540b03c1f05c1d0582b064050b4230d4260f024150000b428069c86c41469c000a0220801e0701a0a8160940a020040082d09c1801dc766c1522c0906017040030540b,0x1064000b427729c908034018d90604c069c80905408c350142d0983c0241805c1000c1502c0f07c17074160ac190002d0a08f6e4146d4000a0220781c0581902808010020b427094210a81b01dc971c06,0x1024180741600c150002d0a9cc3502264400010200781c06818058140200a008290182a0b424099cb6a022354090600b03c07178251fc170401909c03054210441f05c1d058050ec1b0501504c2823c2b,0x1058140a808018260a424029ce6102258c2d01000090040801e0081a060160502a02006098290281c735cc0ac190002d011cb09dca0143b08411064270947f06c140541301c5e0a08f07c1702c0f05c10,0x101000098200781c0682a058140280801804094290600273dce06427014b505c7202c3200ce301c220242306c14054130841107c1c0b4040002a0a4260903d60c2313c1c7342d01000010200780206818,0x108871009d001c220242306c14054130841107c1c014330903d0b4040002a0a4260580a745cf074390642701c220242306c14054130841107c1c014330903d0b4040002a0a4260580a009d0614236602d,
0x1751b302db70b404000260801e06814020060102909417074230a803065d36bc1d13c19110221c4021480a744070880908c1b0501504c210441f070050cc240f42d010000a82909816749a40744f06444,0x1324191bc171b80b1b40527c0327826750210441f0701b0501504c0908c070882d010000a829015d306062088b1008390707e059d2014330903d01c220242306c14054130841107c1c0b4040002a0a426,0x1060160500a09c060a8280100275d8008c47069d50b4040002a0801e07008060160500a09c06010280082475981089620b404000280a8200781c0201805814028270180400824069d56181d2142532823,0x1010000a0260801e0702a060160500a020060100206825761d7024e6084e70548b01ce507c53014e2074850646f05c6e02c6d00cb20a4050b4040002a09c06608233201b120247582d010000801e07008,0x1070140601601002098060a02a0900a76d60089530b40400024020200781c050180580400826018280a80a069da7601b12029014270182d010000a81e058060100202020060140700a095d95fc225842d,0x10180400808080180501c7795808d7c0b40400028098240801e0702a0601605008018040081a02ddd76c257642901427018000a81e058060100202020060140700a7715c08c47069da0b404000080801e,0x1785df02c6508c2a09439071de0a40509c060002a07816018040080808018051e05c41a5742d010000a0260901e08022060160502a02006010020740a77ddd06c3809452029dc0a40509c060002a07816,0x10a80a08820078190581402002018040981c091e3784251b0231a41d1981b190147802901427018000a81e058060100202020061e25640b5a82d010000a026090220801e0701a0a816020060100206015,0x105828020020180409819051e62f01a5c02d010000a026090220801e064160502a02006010020281d7957e06c48091e30b4040002a028220801e064160a00800806010260501c7916e0695b0b40400028,0x10580601002020197a195069780b40400028098240881e0702a0580a084080180400819051e77980b1441520823204187882901427018000a81e058060100202020241e509439071e40000a088200782a,0x1071e90b404000260901e0a81802816088210a00601002020147a9790695f0b40400028098240782a0600a05822084080180400814071e979c152081d30829014230dc0b118251242701820240000a81e,0x10781c068180580a018040a802025ed7ac197a00b118230dc25124202402901427018000a81e0580601002021ec5d81d1981b190147a82d010000901e0a81802816088260a00601002084087ad7a06cc3,
0x17c166029540b40400026090220801e00c1a0581401006020280a818071ef7b41b21c0b210192e4251ac232b8212b01d0a4087b02901427018000a81e05806010027b957055690b404000280982408820,0x1011f00a40509c060002a07816018915540b59c2d010000a026090220801e0701a01416050080182a008187c5ef074a6064440846706c63054db094e108cc60245a009ee0a40509c060002a0781601804,0x10245c0744508c680a40502c830946a0189109c060002a07816081f35a0145582d010000a026090220801e0702a01c160100a02002068187c9f1074a7064bb084de054da094af08cad06c300245b00c98,0x17d0182901a2ac207cc0b20c251a8231a01d114091700516403160062442901427018000a81e0581a6b4146802d010000a026090220781c0581902808010020842a01c1b7d1f2064b806cdc00c5801459,0x10541b01c1f0242908c2a0940e0581a0a4050b4040002a0781d008207d96f02c6509c060141d0541b01c1f0242908c2a0940e0a40506c780581a0b4040002a0781d00820061f51141c288000781701c1f,0x1000280982405c200781a0500801804074030a822065f86841a304191ec0b26c207d827018050741506c0707c090a4230a82503816068290142d010000a81e074027dd9302c51061f506c7809c060141d,0x109c060141d0541b0940e0a40501c1f00c4d074550581a0b4040002a07808080197e5f8084670606206c63009f708c2a0242909c060141d0541b0940e0a40501c1f0581a0002a0781d1559d02dab0b404,0x10a814020020180405c1808dfc5b40b2941a7e82d01000098240a8200781c0a002050080180405c18089fb5680b5ac2d010000a0260902a0801e070180081402006010170881a7e96c02c5108c8106cba,0x1078087fdfd065f909c060141d0541b0940e0a40501c1f00c4d074550581a0002a07808081fe7f01b11c227ec000902a0981e07028008140200601017080187f5970297d0b40400028098240801e0701a,0x10801c060140a808018170081f06c0480600021ff0581a0002a0782021c1a28c232740005c098017702c4606cc00647b08c37081fe09c060141d0541b0940e0a40501c1f00c4d074550581a0b4040002a,0x10940e0a405078200002a05c1b24a020120100026090220801c0a0140a808018170081f0601b80dac0299e0b404000280982408820070180502a020060081f05c1b016020e00a6502d010000a02609022,0x1080270182d010000a8170f972064bd01c1e08c1209c0600c4105426024420744e0940e0a4050144302c3106c92078200b4040002a05c20812030647a0849c01c1e08c1209c0600c4105426024420744e,
0x107c1a0281605004020060a80207020818c50617b0b40400028098240882a0680a058140201f018040081c0860568818310208100b0c40510c1b2481d138150982503809108031042901407078230481e,0x1028160500807c06098280100282596081750b40400028098240881d0680a058140201f018040a802062088182181400098240882a0680a058140201f018040a002072075cc185782d010000a02609022,0x10d8150980b0e0050c0170f8031e4211f01e080290141a24c2d010000a8080760a8240b0c4052a4032a029014070782304827018170f8250d8150981e080000a80806893820192f81c81c00090220a81a,0x10a02609022068180581d02806010020841f0a809831740647a0760a00c7902c380847c014300689309436054260a40501c1e08c120782009c0605c3e0b4040002a0220b67c182fc07078230482701825,0x11d42a01c1d020000840a3a42d0102a01c00024092d82d0102a01c0007408830203740b210251ac1c2a81b268192640516c031680882c170f807078230481e0802701829014000a8076b81468c2d01000,0x10001607c2861c0b0c405090271c01b0940328029070250d82a01c1d0202102807034090241502c190302d010000581f08a0d1402a01c1502c000640c3a02a01c210280001c0d2302a01c09024000540b,0x10840a074080640c0540b0240901c0d0a807000240781a0582808c0209c0483db0029a50b4040840a074080640c0540b0240901c0d0a807000240781a058230082809c058383001053068c70981208a0d,0x100ca107c280a8070640c0b4040001608c2b620053900b1cc278402d010210281d020190301502c09024070342a01c000681608c02078280921183c05838000781a05823008280902784086029990b404,0x10ac2a01c07034090241502c190301d020210282d01000058280082484d6402c7307c2806c250142408c2b0a80701c0d024090540b0640c074080840a0b404000160a0020902684a110a4d0094cc06ccb,0x10840a0001609214128273342a01c2d0100000c3f6242733c0b2c02484c1f0a01b09405090230ac2a01c07034090241502c190301d020210282d0100005828008946280b218268481f0a01b0940509023,0x1092140a0940142406c2508c2b07c280a80700c3f01c0d024090540b0640c074080840a0b404000160858b09cd202c3207c2806c250142408c2b0a0940b4040a80701c0d00c3f024090540b0640c07408,0x10000b8544305821010570001a25c7205821094560002925870078400982c0002225453078400982c0000415cce058210982c0001e1007e0740805821000251584b0a80705821000260b1a602c52098d1,
0x1020190301502c0415c0902407034030fc2a01c260b0222541e100160840b8541a25c00859b80b4040a496094560840a074080640c0540b0240901c0d00c3f0a8070982c0889507840068970582101057,0x16d02d0102925825158210281d
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check480 : ¬ FormulaSat (caseFormula c480) := checkW_sound _ k480 10 w480 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good480 : caseGood c480=true := by decide +kernel
theorem next480 {chosen region} (disj : ∀ i∈c480.prior, chosen i=false) (O : Later c480.prior chosen region) : ∃ g∈c480.groups, Matches chosen g := case_conclusion _ good480 check480 disj O
def c1040 : Case := ⟨[5, 11],[5, 11],[
s0,s1,s2,s3,s4,s5,s24,s26,s28,s50,s183,s184,
s186,s210,s253,s273,s916,s917,s1247,s1248,s1513,s1578,s1645,s1646,
s1722,s1723,s1724
],[
t4,t5,t6,t9,t11,t12,t13,t14,t15,t17,t19,t21,
t22,t23,t38,t42,t44,t45,t47,t48,t50,t51,t52,t53,
t54,t57,t59,t60,t61,t63,t67,t68,t69,t70,t71,t72,
t74,t75,t76,t79,t80,t81,t82,t83,t85,t86,t87,t88,
t90,t91,t93,t94,t95,t97,t98,t99,t100,t102,t104,t105,
t106,t111,t112,t113,t114,t116,t117,t119,t120,t121,t122,t123,
t125,t126,t127,t128,t130,t131,t132,t133,t134,t135,t139,t140,
t141,t142,t145,t146,t147,t148,t150,t151,t153,t154,t155,t156,
t158,t159,t160,t161,t167,t169,t171,t174,t175,t177,t180,t182,
t185,t190,t192,t195,t198,t201,t203,t205,t206,t208,t209,t210,
t214,t218,t219,t220,t221,t223,t224,t227,t228,t229,t232,t235,
t236,t237,t238,t239,t240,t243,t245,t246,t247,t248,t249,t250,
t251,t252,t253,t255,t256,t257,t258,t260,t261,t262,t265,t268,
t270,t271,t280,t283,t285,t286,t287,t294,t295,t296,t297,t299,
t301,t308,t315,t316,t317,t318,t319,t320,t321,t324,t328,t329,
t330,t331,t333,t335,t336,t337,t340,t342,t344,t346,t347,t348,
t349,t350,t351,t352,t353,t354,t355,t356,t359,t360,t361,t364,
t375,t376,t377,t378,t379,t380,t381,t382,t383,t384,t385,t386,
t387
],[
g0,g1,g2,g4,g8,g32,g64,g128,g256,g512,g2048,g4096,
g8192,g16384,g32768,g65536,g131072,g262144,g524288,g1048576,g2097152,g96,g160,g192,
g288,g320,g384,g544,g576,g640,g768,g2080,g4160,g6144,g8320,g10240,
g12288,g16640,g18432,g20480,g24576,g33280,g34816,g36864,g40960,g49152,g131104,g133120,
g196608,g262208,g266240,g327680,g393216,g524416,g532480,g589824,g655360,g786432,g1048832,g1064960,
g1114112,g1179648,g1310720,g1572864,g2097664,g2129920,g2162688,g2228224,g2359296,g2621440,g3145728,g161,
g322,g608,g704,g800,g896,g10241,g20482,g38912,g45056,g51200,g57344,g133152,
g266304,g532608,g720896,g1065216,g1376256,g2130432,g2490368,g3670016,g480,g612,g904,g30720,
g38916,g57352,g720897,g1376258,g1966080,g2490372,g2949120,g3342336,g3670024,g10401,g20802,g721057,
g731137,g1376578,g1396738,g39524,g58248,g2490980,g2529284,g3670920,g3727368,g731297,g1397058,g2529892,
g3728264
]⟩
def k1040 : List Nat := [
1,2,198,199,200,201,202,203,130,131,132,204,
107,108,109,205,110,206,207,208,82,133,62,134,
53,54,83,84,85,63,209,210,111,211,86,135,
112,212,64,213,214,215,113,65,136,137,216,87,
66,138,88,217,218,139,140,141,219,114,220,221,
222,223,224,142,143,144,44,24,145,225,226,89,
146,37,147,38,148,8,227,228,229,230,67,90,
55,115,116,45,39,231,149,150,232,233,151,152,
234,235,236,46,47,237,13,153,25,154,26,23,
14,117,238,239,240,118,155,119,241,120,27,242,
156,28,243,15,157,158,91,29,30,159,244,245,
246,160,92,161,93,162,68,48,69,247,248,249,
250,251,252,253,254,94,95,255,163,164,165,256,
166,167,257,70,258,259,260,261,121,262,263,264,
168,265,266,267,268,71,72,269,270,169,271,272,
96,31,170,73,273,274,171,275,49,97,56,122,
172,276,173,50,123,277,278,279,98,174,175,51,
57,99,176,16,74,52,75,100,177,280,178,179,
180,17,281,18,181,182,124,282,283,183,284,101,
32,58,40,102,41,285,286,287,288,289,290,291,
184,103,185,33,186,34,292,293,294,295,296,297,
298,299,300,301,302,303,304,305,306,307,308,309,
310,311,312,313,314,315,316,317,318,319,320,321,
322,323,324,325,326,327,328,329,330,331,332,333,
334,335,336,337,338,339,340,341,342,343,344,345,
346,347,348,349,350,351,352,353,354,355,356,357,
358,359,360,361,362,363,364,365,366,367,368,369,
370,371,372,373,374,375,376,377,378,379,380,381,
382,383,384,385,386,387,388,389,390,391,392,393,
394,395,396,397,398,399,400,401,402,403,404,405,
406,407,408,409,410,411,412
]
def w1040 : List Nat := [
0x1050120400e03008018020159e490170040b000000b02a0a026090220801e0701a06014048100380c02006010036752305c0102c000002c0a82809824088200781c06818050120400e03008018040099c,0x10a82809824088200781c06818050120400e0300601002025a0498170040b000000b02a0a026090220801e0701a06014048100380c020040080767d2505c0102c000002c0a82809824088200781c06818,0x10081168d2905c0102c000002c0a82809824088200781c06818050120400c020060100203da24a0170040b000000b02a0a026090220801e0701a060140481003808018040080d6852705c0102c000002c,0x10701a060120400e0300801804008156952b05c0102c000002c0a82809824088200781c06818050100380c020060100204da44a8170040b000000b02a0a026090220801e0701a060140480e0300801804,0x1000000b02a0a026090220801e07018050120400e03008018040081b69d2d05c0102c000002c0a82809824088200781c06814048100380c0200601002065a64b0170040b000000b02a0a026090220801e,0x10200601002085aa4c0170040b000000b02a0a026090220801c06818050120400e03008018040081f6a52f05c0102c000002c0a82809824088200781a06014048100380c0200601002075a84b8170040b,0x10801e0701a06014048100380c0200601002095ac4c8170040b000000b02a0a026090200781c06818050120400e0300801804008236ad3105c0102c000002c0a828098240881e0701a06014048100380c,0x105c0102c000002c0a826090220801e0701a06014048100380c02006010020a5ae4d0170040b000000b02a0a024088200781c06818050120400e0300801804008276b53305c0102c000002c0a82809822,0x104810020060100203c0d6c53705c0102c000002a0a026090220801e0701a06014048100380c02006010020b5b04d8170040b000000b02809824088200781c06818050120400e03008018040082b6bd35,0x10a026090220801e0701a060140480c02006010020440f6cd3905c0102c000002c0a82809824088200781c0681805012038080180400811035b24e0170040b000000b02a0a026090220801e0701a06014,0x1045b64f0170040b000000b02a0a026090220801e0701a060140400c020060100204c0f6d53b05c0102c000002c0a82809824088200781c0681805010038080180400813035b44e8170040b000000b02a,0x1068180481003008018040081503db84f8170040b000000b02a0a026090220801e0701a060120400e02006010020540d6dd3d05c0102c000002c0a82809824088200781c068180500e030080180400813,
0x10002c0a82809824088200781c068180400e03008018040081504dba500170040b000000b02a0a026090220801e0701a060120380c0200601002054116e53f05c0102c000002c0a82809824088200781c,0x10100206c196f54305c0102c000002c0a82809824088200781c060140481003008018040081b03dbc508170040b000000b02a0a026090220801e0701a050120400e02006010020640d6ed4105c0102c00,0x10801e06814048100380c0200601002074196fd4505c0102c000002c0a82809824088200781a060140480e03008018040081d045be510170040b000000b02a0a026090220801e07014048100380c02006,0x10040b000000b02a0a026090220801c06818050100380c020060100207c137054705c0102c000002c0a828098240882007818050120400e03008018040081d06dc0518170040b000000b02a0a02609022,0x103008018040081f075c4528170040b000000b02a0a026090220801c06014048100380c020060100207c1b70d4905c0102c000002c0a82809824088200701a050120400e03008018040081f065c252017,0x1098240881e0701a050120400e030080180400821065c6530170040b000000b02a0a026090220781c06818048100380c0200601002084157154b05c0102c000002c0a828098240882006818050120400e,0x17254f05c0102c000002c0a828098240881e06818050120400e030080180400821075c8538170040b000000b02a0a026090220781c06014048100380c02006010020841b71d4d05c0102c000002c0a828,0x1048100380c02006010020941972d5105c0102c000002c0a828098220801e0701a0601404810038080180400825035ca540170040b000000b02a0a026090220701a06014048100380c02006010020841f,0x10b02a0a024088200781c06818050120400c020060100209c0f7355305c0102c000002c0a828098200781c06818050120400e03008018040082508dcc548170040b000000b02a0a026088200781c06814,0x100827095d0558170040b000000b02a0a0240801e0701a06014048100380c020060100209c2373d5505c0102c000002c0a828090220801e07018050120400e03008018040082706dce550170040b00000,0x106818050120400e030080180400829075d2560170040b000000b02a09824088200781c06818050120380c02006010020a4117455705c0102c000002c0a828088200781c06818050120400e0300801804,0x102c000002c0a826088200781c06818050120400e030080180400829095d4568170040b000000b02a098240801e0701a06014048100380c02006010020a42374d5905c0102c000002c0a826090220801e,
0x102006010020ac1f75d5d05c0102c000002c0a026090220801e0701a060140400e03008018040082b04dd6570170040b000000b02a090220801e0701a06014048100380c02006010020a4277555b05c01,0x10801e0701a06014048100380c02006010020ac257655f05c0102c000002c0a026090200781c06818050120400e03008018040082b08dd8578170040b000000b02809824088200701a06014048100380c,0x1588170040b000000b026090220801e0701a06014048100380c02006010020ac2976d6105c0102c000002c0a024088200781c06818050120400e03008018040082b09dda580170040b000000b02809822,0x10400e03008018040082d08dde590170040b000000a828098240881e0701a06014048100380c02006010020b4217756305c0102c000002a0a026090220801e0701a060120400e03008018040082d055dc,0x10a024088200781c06818050120400e03008018040082d09de0598170040b000000a828098220801e0701a06014048100380c02006010020b42577d6505c0102c000002a0a026090200781c0681805012,0x10340378d6905c0102c000002809824088200781c06818050120400e03008018040082d0ade25a0170040b000000a826090220801e0701a06014048100380c02006010020b4297856705c0102c000002a,0x10701a0601204008018040081503c0d7956b05c0102c000002c0a82809824088200781c0681805010030080180204c0f015e45a8170040b000000b02a0a026090220801e0701a060140480e0200601011,0x1000000b02a0a026090220801e0701a0601003808018040081504c0d79d6d05c0102c000002c0a82809824088200781c068180480c02006010020541103de65b0170040b000000b02a0a026090220801e,0x10180207c1b015ea5c0170040b000000b02a0a026090220801e06814048100380c020060101d064037a56f05c0102c000002c0a82809824088200781c068180380c020060100205413045e85b8170040b,0x10881e06014048100380c02006010020841d06dec5c8170040b000000b02a0a026090220781c050120400e03008018040082106c197ad7105c0102c000002c0a828098240882007018050120400e03008,0x105c0102c000002c0a828098240881a06014048100380c02006010020841f075ee5d0170040b000000b02a0a026090220701a050120400e03008018040082107c197b57305c0102c000002c0a82809824,0x1030080180400829074117c57705c0102c000002c0a828090220801e07018050120400c020060100209c1b03df05d8170040b000000b02a0a026088200781c06814048100380801804008250640d7bd75,
0x109824088200701a060140400e03008018040082b07c137cd7905c0102c000002c0a8260801e0701a06014048100380c02006010020a42508df25e0170040b000000b02a09824088200781a060140480e,0x1095f65f0170040b000000a828098240881e0701a060120400e03008018040082d084157d57b05c0102c000002c0a0240801e0701a06014048100380c02006010020ac2708df45e8170040b000000b028,0x1068180500801804008130440f035f85f8170040b0000009824088200781c06818050120400e03008018040082d0ac297dd7d05c0102c000002a0a0220801e0701a06014048100380c02006010020b427,0x10002c0a82809824088200781c068180380c018040081504c11025fa600170040b000000b02a0a026090220801e0701a0601204008010020540f034077e57f05c0102c000002c0a82809824088200781c,0x10841f074097f58305c0102c000002c0a828098240881e07014048100380c020040082106c1901dfc608170040b000000b02a0a0260902208014048100380c020060100207c1d06c197ed8105c0102c00,0x106818050120400e03008018020ac2708c057fd8505c0102c000002c0a8260801e0701a06014048100380c02006010290942300dfe610170040b000000b02a0a0260902206818050120400e0300601002,0x10040b000000a828088200781c06818050120400e03008010020b427094078058705c0102c000002c088200781c06818050120400e03008018040082b0a42709600618170040b000000b028090200781c,0x1018040082d0ac2902604628170040b000000a0260801e0701a06014048100380c02006010020b42b0942380d8905c0102c000002a090200781c06818050120400e03008018040082d0a42708e0262017,0x109824088200701805010030080180207c1b04c0f01606630170040b000000b02a0a026090220801e068140480e020060101d06411034038158b05c0102c0000026090220801e0701a06014048100380c,0x18258f05c0102c000002c0a8260801e06814048100380c0200601029094230741900e08638170040b000000b02a098200781c068180501203808018040a42508c110340381d8d05c0102c000002c0a828,0x1020040082106c190540f0340782d9105c0102c000002c0a0240801c06014048100380c020060082b09c2307c1b0160a640170040b000000b028090200781c068180501003008018020ac2708c1303c05,0x10a828088200781c0681804810020040082d09c250540f034078359305c0102c000002c0a828098240881a0600e03006010020841f0741504c110260c648170040b000000b02a0a026090220781c04810,
0x107c1d02610658170040b0000009824088200781c068180380c018040082d0ac29054130440983d9505c0102c000002a0a0220781c050120400e03008010020b4270942106c1901e0e650170040b00000,0x10400c020060082b09c2307c1b04c0f01612660170040b000000b02a098200781a0501203808018040a42508c1d06411034038459705c0102c00000260902206818050120400e03006010020b42b0a421,0x102c000002609022068180380c018040082d0ac290841f0741504c1102614668170040b000000a8280881e0701204008010020b4270942106c190540f0340784d9905c0102c000002c0a0240801c06014,0x109c0d06c0f0e4050d0231482514c271501907c03144000b42b0a4212ea140405c0487001c3506c270341b03c390143408c520945309c540641f00c510780d07077020b70002d0ac29084158559b05c01,0x10143408c520945309c540641f00c51074a807cb2084ba0002d0ac2905217810087dc000801e0701a06014088260a4020380c0ac060102d090120421684013260111d415854082dc1c1dc1e034070d41b,0x109cb3084b00a4bb0002d0ac248620f0405c02116049070521707cb2074a8084ba0641f09c540945308c5200c5101c3506c270341b03c39014340002d0ac292ee1604c980447501c3506c270341b03c39,0x11d0272cc191e4110381d2a4212c0152681f2c4132700926c292ec0d06c1b09c0f0e4070d4050d0000b42b089e208d0e01c3506c270341b03c390143407cb1074a90249b0440e04c9c064790549a00c74,0x1098240a8180781c068120400e0200c008060102d08820869df08d0b084260547200c1a07c1d0741c0440e04c21024200ac22034ac03cb901cb80146606c5a0649d0002d0a0260961980c2243c2486003,0x1048100380803002018280b4260121d86c2086800098240a8180781c068120400e0200c008060a02d01022871f5051dd00028098240781c068180a8120400e0200c008060102d0882186db0055dc00028,0x1084090802b088050f42311c2612c000b4280906787425864051980f2e41b168072e00d2b019274030681f0741d0701103813084090802b088000b4280984b778213881524822870000902a0601e0701a,0x108c4706446084a6090670984b0002d0a01a03a1f804067d8000a0220801e0701a06014048100a82502027010020b40e0321e780191180d06c213a4153a01b45c0f3c8073c4030681f0741d0701103813,0x10a00f8820d0305b019110510a03a1f06446084a600c1a07c1d0741c0440e04c21024200ac220143d08c470984b090670002d0a01a2f21e054a50341b00c1a07c1d0741c0440e04c21024200ac220143d,
0x12f02419c2311c050f42612c030681f0741d0701103813084090802b088000b4282f6130305b050fd00c1a07c1d0741c0440e04c21024200ac220143d08c47018aa09067080460605a068bc0984b0002d,0x10380c0a4060a82d0902688a020890d0440e04c210242001c8503c0c094af034640641f00c1a0840d07c1d0741c0146606c19054180a0bd0ac220002d09e21838152940d06c0f88020118062a8181681a,0x10a41c0422488c2b088000b4028882788405198210341907c0d190252bc1b064150600f03007214282f411038130841f074090801d07003068000b42a88d0c089e1000040801e0701a060140481002002,0x1088200781a060140480c038080a4060102a0081d899d108ca2042240b4020002a0801e0101a06014048020380c02006098290901c895d3089ae0b402000240a8200780406818050120080e0300801826,0x189c1907c0d190053ac0346c070b41b064150602103413078090b80f0301f0582d008000a829098241322608ca307225000200780406818050120080e0a808018260a40c092277c4107482d0080009824,0x1098180322a8a01d1ec112d4070b41b064150602103413078090b80f0301f05805114241302d008000a82909818030028a5d408df20b402000260801e0701a060140482a0380c02006010250a41000a28,0x10322a01c2d06c19054180840d04c1e0242e03c0c07c16014450904c0b4020002a0a426060be7f81d15c223a811154028a4070b41b064150602103413078090b80f0301f05805114241302d008000a829,0x103413078090b80f0301f0582d008000a82909a2c844100f8070b41b064150602103413078090b80f0301f0580511424130222641c1840207c182f82d008000a8290980d8ae07074570403e088ec00864,0x1044950950208d01074970649603494014cf00cce09a2c03c0c04c1e0840d07c1606c19054180242e01c2d0b4020002a0a403820111540d8ac1c184222640207c182f80511424130070b41b0641506021,0x105012040080300609c040082206e2f734232440e8b42d008000a0200781c0a818050120400803027018040082406a2e6b42373c2d008000a0240801e0702a06014048100200c09c06010020680e8b5d5,0x1740234001b1cc0f108248c02d008000781c0a818050120400803027018040a02000a318bc2324c1a8b8000801e0702a06014048100200c09c0601028008248c1f0039ce0b402000280902a0801e07018,0x1050060701009633730226b02d008000a0260801e0701a06014048100a80c0200601002038258ca310251d0851f0551e0449501d1c07cb604d1a0151907497064960349400ce60a4030b4020002a09c04,
0x1098200781c0201805012040040080c018280a82406a356ac226702d00800090260801e07008060140481001002030060a02a0680e8d23206c7303c420a40309c040b4020002a078180480c0100202020,0x100808080140181c042388d82324c1a8d4000801e07008060140482601002030060a02a040248dda703dbc0b4020002809824088200781c060140482a03008018040081006e36688232440e8d02d00800,0x1104252d423288108e02900c27010000a81e060120300400808080140181c8e9a303db30b4020002809824088200781c0a8180501203008018040081106a398dc258cc2900c27010000a81e0601203004,0x10601404828030080a8040080e01a3d7001a6a02d008000a0260901e08022060140481d0380c0202a01002018108f041069be0b4020002809824088200781d060140480e030080a804008060463b8e41b,0x108ce0074d906c880446f01a3e0a40309c040b4020002a078180480c01002020200523f8f4251ec0f4602328c1c8e82900c27010000a81e0601203004008080801401a3e8f0118ec0009824088200781d,0x10a00c0202a0100205420909e6041b80b4020002809824088200781c0681804806030080a8040081503e416e4106942d008000a026090220601e0701a048060540c0202a010020800e9019f03c5b094e4,0x17142d008000a026090220781c0a818048100380c02021010020681590e4201cab0947208c920748c06c890523f0a40309c040002a078180480c01002020201a24103a4000026090220601e0701a04806,0x101c8d0a40303c2b0942609c0408c6004417080680547c0b4020002a078180480c010020201c06a4490c1d2301b2242900c0f0ac2509827010231801105c201a0000a81e0601203004008080547c2ac06,0x1030080a80400806076479141a9102900c0f0ac2509827010231801105c201a0151f0000a81e060120300400808072462200671c2d008000a026090220782a06014048100380c02021010020701b915aa,0x19202900c270102d008000a81e060120300400a4991c073341c918151f01105c23180250980f0ac201a02900c27010000a81e060120300400808921ec069c80b40200028098240881e05018040120840e,0x10002a078180480c1359d0445507457084de03cf306c8705515094b408cfe024c801cc600a490a40309c040b4020002a078180480c0124a6801134c151c02539423384212381d2281b35c0f3480732808,0x105c15280251641b104231602900c0f2780c1342d008000a81e060120440292d12040d00000d088051a59e06cae094e308c90084df074d8054d50448603c6e024c901cc700cc50124a0a40309c040b402,
0x10781c0681804012034080a804008060924c78c1d15c0292c0f2781b10425164152802105c071bc2701009194051a4231602900c0c1342d008000a81e06012044bf6c81d0e02701009194051a4071bc21,0x101009194051a4231602900c1d0e0030f8112fc1b1580c134000a81e0601208014939ca03c420924c0b402000260a0220801e0701a060100480d0202a0100205006935b1039a10b402000280981408820,0x1048100a808034040081a056513580f7e42d008000a026034220801e0701a0601204008010020542a09007941e5039b70b4020002809824088200781c06818048100a808034040081501a4f9340734427,0x101804008130400e94c8f03c2b082520304d0001e0a81804829944251c8149381b1582701009194051a4231602900c1d0e0030f8112fc0c134000a81e06012082529400693c0009824088200781c0a018,0x10482909c040b4020002a078180344e94c113d42900c070c01d0e0030c423090270102118c09208250d81b0c805204120a4000a81e0600d03a546d01579c2d008000a026090220801e0701a0602a03408,0x16d41b0c8070c0030c40920c1d22c2309027010251081127c0d13815284120a42900c2d008000a81e0602003c04955f8040f4054cb03a54094360846306c320743802482014810a40301c3000c3108c24,0x1301a4055ba0b4020002809824088200781c068180a80e030130180400810022567901b2b804954152841127c251081d22c0920c2900c070c0030c423090120a4270100d1382d008000a81e0602003c7d,0x10a81e06020022587a0146d82d008000a026090220801e0a81a060110380c04c06010020700895e560745f0245c0a40301c3000c3108c2409c040344e0943606c320143f03c7d048290002a0781808010,0x10748a02258040c00943606c320143f03c7d0a40301c3000c3108c240482909c040344e0b4020002a078180825995c1d17c2900c070c0030c423090270100d138250d81b0c8050fc0f1f4120a41030000,0x10481008419020040080c0981406e5b71807234090a00512825098031b41105c13040270101d174230942900c150bc1808c2d008000a81e0840c0381a9688e0206308259048290002a0781808dfa050d4,0x10a81e0844f16c061200e9701808c000a81e0840c9765b06a5a0542f024280144a0942600c6d0441704c1009c040745d08c25060230a4030002a078210300e971eb01dfc0b40200028038240881e0702a,0x10341097dbb095ef0b40200028098220801e0641a050120080e020060102a034100725e82c06120144500e23c1a44c0c9741d1741105c031b4051282509813040090a027010230941808c2900c2d00800,
0x197c1b15813040090a027010230942900c0710c05110150bc0f1002113c1808c2d008000a81e0347e9781d0e0030f813040090a027010230942900c0710c05110150bc0f1001808c1b1582113c000a81e,0x100c0710c05110150bc0f1002113c110e80d1f81808c000a81e0081d984f6069bf0b402000280982a0882007802050120400e030080180406424076602b403154000640c0443a8141c18425164022b410,0x1991cb06c73092620b40200026018220801e0a014048100380c020190102a0700298da606dbd0b4020002809806088200781c050120400e03008064040a80209262980251ec13040090a0270102309429,0x10e80d1f8150bc051100710c0f1002113c23094090a0130401808c2900c270102d008000a81e026630766104c100242809c0408c250a40301c43014440542f03c400844f0443a0347e060230002a07802,0x101c0f08c0709c04078090b4020002a06420999fb068fb00c6a0146b0246c04c1003c480443a034110a403094370547a01c0f08c0709c04078090b4020002a06420076657a41c1841b21c252d00299011,0x11781d17420998250dc110e8151e80f12013040091b0051ac031a80703c2301c270100d0441e0242900c2d008000a8190a9c206cf80766500c6a0146b0246c04c1003c480443a034110a403094370547a,0x10082104a6999c150cc0703c2301c270100d0440f0ac190a805128250b01b1781e0242900c000a81000821048089a1ee071c90b40200028098240881a084180a8120400e0301f0180400814022677b41b,0x1054330745f0244908450078090b4020002a0400204c0e9a8630245c04a69000100a802084507f4151c01c36c089a00703c2301c270100d0440f0ac190a805128250b01b1781e0242900c2d008000a810,0x11b80007c1203c808181a1c4041880e9a81d17c0703c2301c270100d0442900c190a8250b0150cc09124211401e0242d008000a810008131fdc106c320143f01c0f08c0709c04034110a4030642a0942c,0x1071a90b40200028098240881f08018050120400e030080182a0080406a6c70c1d3f00703c2301c270100d0442900c190a8250b0150cc09124211400f200131fc1e0242d008000a8100080406e6b18805,0x10cc09124211400703c2301c270100d0442900c190a8250b01e0242d008000a81000a6e9b01b9ac0703c2301c270100d0442900c190a8250b0150cc09124211400f200131fc1e024000a810008049b5c4,0x1048fa02033070dd03c6206c4109459050dc014860426e00e6f0642a0341101c0f08c070780909c040a4030b4020002a0145e080f7068da0a403078090002a00e6f7a81a1c41d330049b40f200131fc15,
0x10540600019054750a8050540600011051200a8050840b0000704d220a8050240a00015018770a805074080002102cee0a805074080000d049210b4020a80500009028f00b4020a8050001d0220c080f9,0x10000207c0e9c67009cb603c6208cff014710a41609437054060b4020000207c1a305f3049d70b4020840b0740805406064150240a044140341201c130a805000260902207c1a0a0020100e9c0790a805,0x1304250dc290582a0140704c090280d0481105015018190541d0202102c2d008000081f0ee0a04c3f0a41609437010270980708876068c10a80501c130240a03412044140540606415074080840b0b402,0x10a0230167282426090044401240c1b0f01f0ec251e02a0140704c090280d0481105015018190541d0202102c2d008000082808c0f30904088760a8050001e06c3c848121b80e9c42601c0409c221d81a,0x10840b07408064150540604414034120240a01c130a8050000e0081e0681208c28090049cdff0989006c3c07c3b0947804ca403cc20a80501c130240a03412044140540606415074080840b0b40200002,0x1010249d9da099af0b4020840b07408064150540604414034120240a01c130a805000040881e0680e0a002090129d6730167204ca403cc20947806c3c07c3b0a8050b402000020a0239d1f4099d80b402,0x10d8249d82d0082102c1d0201905415018110500d048090280704c2a014000781a0382800822012777582739c129d42d0082102c1d02019054090280d048110500704c150182a014000881e0680e0a002,0x1008c4800264201b0f0052102329c130780f0302830c1f0ec2a0140704c090280d0481105015018190541d0202102c2d00800008259e277014ed03cef08e7406c3c07c3b0a805000020a0c37642741813,0x4740a805008c409e790027a4142d008023100009e7976c27424259e00f030130782329c052102830c1b0f01f0ec2d0082a0140704c0d048090281105015018190541d0202102c00
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check1040 : ¬ FormulaSat (caseFormula c1040) := checkW_sound _ k1040 10 w1040 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good1040 : caseGood c1040=true := by decide +kernel
theorem next1040 {chosen region} (disj : ∀ i∈c1040.prior, chosen i=false) (O : Later c1040.prior chosen region) : ∃ g∈c1040.groups, Matches chosen g := case_conclusion _ good1040 check1040 disj O
def c11441 : Case := ⟨[1, 5, 6, 8, 11, 12, 14],[1, 5, 6, 8, 11, 12, 14],[
s2,s4,s5,s28,s200,s917,s1248,s1513,s1578,s1645,s1646,s1722,
s1723,s1724
],[
t9,t10,t17,t19,t22,t23,t61,t71,t72,t80,t81,t85,
t90,t94,t95,t97,t99,t100,t102,t105,t107,t114,t118,t119,
t121,t122,t123,t126,t127,t128,t131,t132,t133,t142,t150,t151,
t154,t156,t185,t218,t222,t227,t228,t232,t235,t236,t237,t239,
t243,t245,t247,t248,t249,t250,t252,t253,t255,t257,t258,t261,
t269,t270,t271,t277,t285,t286,t315,t318,t319,t321,t325,t326,
t327,t329,t330,t332,t333,t334,t335,t336,t337,t338,t339,t340,
t341,t342,t351,t352,t353,t357,t359,t360,t370,t371,t373,t374,
t375,t376,t377,t378,t379,t380,t381,t382,t383,t384,t385,t386,
t387,t388,t389
],[
g0,g2,g4,g8,g64,g256,g512,g4096,g16384,g32768,g65536,g131072,
g262144,g524288,g1048576,g2097152,g320,g576,g768,g4160,g16640,g20480,g33280,g36864,
g49152,g196608,g262208,g266240,g327680,g393216,g589824,g655360,g786432,g1048832,g1064960,g1114112,
g1179648,g1310720,g1572864,g2097664,g2129920,g2162688,g2228224,g2359296,g2621440,g3145728,g322,g580,
g776,g20482,g36868,g49160,g266304,g720896,g1065216,g1376256,g2130432,g2490368,g3670016,g1376258,
g1966080,g2490372,g2949120,g3342336,g3670024,g20802,g37444,g49928,g1376578,g1396738,g2490948,g2527236,
g3670792,g3719176,g1397058,g2527812,g3719944
]⟩
def k11441 : List Nat := [
1,2,3,4,5,6,7,125,41,126,127,128,
129,130,30,71,25,26,42,43,44,45,72,46,
73,74,60,47,75,76,77,131,48,23,132,78,
79,31,61,80,32,81,133,82,134,135,62,63,
33,83,34,27,49,24,84,136,85,137,86,138,
139,140,87,88,35,141,142,89,143,36,144,145,
146,90,147,37,148,149,150,151,50,91,152,92,
153,38,93,154,51,52,53,54,155,94,95,96,
97,98,99,100,156,101,157,158,102,103,104,159,
105,64,106,16,17,65,55,28,56,160,161,162,
163,164,165,166,66,57,107,18,108,19,109,20,
167,168,169,170,171,172,173,174,175,176,177,178,
179,180,181,182,183,184,185,186,187,188,189,190,
191,192,193,194,195,196,197,198,199,200,201,202,
203,204,205,206,207,208,209,210,211,212,213,214,
215,216,217,218,219,220,221,222,223,224,225,226,
227,228,229,230,231,232,233,234,235,236,237,238,
239,240,241,242,243
]
def w11441 : List Nat := [
0x1538740c190285c081101834040b0080c0000160a8502612088401e0d050240e040180af4530740c190285c081101834040b0080c0000160a8502612088401e0d050240e0401808f3,0x1548740c190285c081101834040b0080c0000160a8502612088401e0d050240e0301012f6540740c190285c081101834040b0080c0000160a8502612088401e0d050240e040100ef5,0x1558740c190285c081101834040b0080c0000160a8502612088401e0d0501c080301026f8550740c190285c081101834040b0080c0000160a8502612088401e0d0502408030101ef7,0x1568740c190285c081101834040b0080c0000160a8502612088401e0a0481c080301036fa560740c190285c081101834040b0080c0000160a8502612088401e0d0481c08030102af9,0x1578740c190285c081101834040b0080c0000160a85026120883c1a0a0481c080301042fc570740c190285c081101834040b0080c0000160a8502612088401a0a0481c08030103efb,0x1588740c190285c081101834040b0080c0000160a85026110803c1a0a0481c08030104afe580740c190285c081101834040b0080c0000160a85026120803c1a0a0481c080301046fd,0x1598740c190285c081101834040b0080c0000160a84c24110803c1a0a0481c08030105300590740c190285c081101834040b0080c0000160a85024110803c1a0a0481c08030104eff,0x15a8740c190285c081101834040b0080c0000150a04c24110803c1a0a0481c08030105b025a0740c190285c081101834040b0080c0000160a04c24110803c1a0a0481c08030105701,0x15b8740c190285c081101834040b0080c0000160a8502612088401e0d0481006020541f045b0740c190285c081101834040b0080c0000160a8502612088401e0d05010060204c1f03,0x15c8740c190285c081101834040b0080c0000160a8502612088401e0a04810060206c1f065c0740c190285c081101834040b0080c0000160a8502612088401e0d0381006020542705,0x15d8740c190285c081101834040b0080c0000160a850261208840140903810060207c37085d0740c190285c081101834040b0080c0000160a8502612088401a0a03810060207c2707,0x15e8740c190285c081101834040b0080c0000160a85026120883c1409038100602084370a5e0740c190285c081101834040b0080c0000160a85026120883c1a090381006020842b09,
0x15f8740c190285c081101834040b0080c0000160a8502610078341409038100602094470c5f0740c190285c081101834040b0080c0000160a85026120883414090381006020843f0b,0x1608740c190285c081101834040b0080c0000160a85024110803c140903810060209c370e600740c190285c081101834040b0080c0000160a85024110803c1a0a04810060209c1f0d,0x1618740c190285c081101834040b0080c0000160a850221007834140903810060209c4b10610740c190285c081101834040b0080c0000160a850241007834140903810060209c470f,0x1628740c190285c081101834040b0080c0000160a84c22100783414090381006020a44b12620740c190285c081101834040b0080c0000160a84c24100783414090381006020a44711,0x1638740c190285c081101834040b0080c0000160a04c24110803c1a0a0381006020ac2714630740c190285c081101834040b0080c0000160a84822100783414090381006020a44f13,0x1648740c190285c081101834040b0080c0000160a04c24100783414090381006020ac4716640740c190285c081101834040b0080c0000160a04c24110803414090381006020ac3f15,0x1658740c190285c081101834040b0080c0000160a04822100783414090381006020ac4f18650740c190285c081101834040b0080c0000160a04c22100783414090381006020ac4b17,0x1668740c190285c081101834040b0080c0000150a04c24110803c1a090381006020b42b1a660740c190285c081101834040b0080c0000160984822100783414090381006020ac5319,0x1678740c190285c081101834040b0080c0000150a04c24100783414090381006020b4471c670740c190285c081101834040b0080c0000150a04c24110783414090381006020b4431b,0x1688740c190285c081101834040b0080c0000150a04822100783414090381006020b44f1e680740c190285c081101834040b0080c0000150a04c22100783414090381006020b44b1d,0x1698740c190285c081101834040b0080c0000140984822100783414090381006020b45720690740c190285c081101834040b0080c0000150984822100783414090381006020b4531f,0x16a8740c190285c081101834040b0080c0000160a8502612088401e0d04810040a83c0f226a0740c190285c081101834040b0080c0000160a8502612088401e0d05010060983c0b21,
0x16b8740c190285c081101834040b0080c0000160a850261208840140903810060f86c0b246b0740c190285c081101834040b0080c0000160a8502612088401e0d0380c040a84c1323,0x16c8740c190285c081101834040b0080c0000160a85026120883414090380c041087c13266c0740c190285c081101834040b0080c0000160a85026120883c140903810041086c0f25,0x16d8740c190285c081101834040b0080c0000160a84c200f0682812070200c041489447286d0740c190285c081101834040b0080c0000160a85024110803c14090200c041386c1f27,0x16e8740c190285c081101834040b0080c0000160a048200f0682812070200c041589c472a6e0740c190285c081101834040b0080c0000160a04c24110803414070200c041587c2729,0x16f8740c190285c081101834040b0080c0000150a044200f0682812070200c041689c4b2c6f0740c190285c081101834040b0080c0000150a04c24110783412070200c04168842b2b,0x1708740c190285c081101834040b0080c0000160a048200f0682812070200c2b1388c0b2e700740c190285c081101834040b0080c00001309044200f0682812070200c04168ac532d,0x1718740c190285c081101834040b0080c0000150a044200f068281207020082d138940f30710740c190285c081101834040b0080c000016088401e0d050240e04018082b1489c4b2f,0x1728740c190285c081101834040b0080c000014098401e0d050240e04018082d158944732720740c190285c081101834040b0080c000015090401e0d050240e04018082d1489c4731,0x1738740c190285c081101834040b0080c0000160a85026120884014040183e1b0983c0b34730740c190285c081101834040b0080c00001309044200f068281207018082d158a41333,0x1748740c190285c081101834040b0080c0000160a8502612088340e03010421f0a84c1336740740c190285c081101834040b0080c0000160a85026120883c1204010421b0a83c0f35,0x1758740c190285c081101834040b0080c0000160a048200a0481c08030ac4e230f86c0b38750740c190285c081101834040b0080c0000160a048200f0682808030ac4e230983c0b37,0x1768740c190285c081101834040b0080c0000150a0441e0a0481c08020b44e251086c0f3a760740c190285c081101834040b0080c0000150a044200f0682408020b44e250a83c0f39,
0x1778740c190285c081101834040b0080c000013090441a0a0481c06020b456291087c133c770740c190285c081101834040b0080c00001309044200f0681c06020b456290a84c133b,0x1788740c190285c081101834040b0080c0000150a0441e09020082d13894421b0a83c0f3e780740c190285c081101834040b0080c0000160a048200a0200c2b1388c3e1b0983c0b3d,0x1158a4426d9f84876070c83c1e1b080143023148945427158782e08208005a2b148842b40790740c190285c081101834040b0080c000013090441a07018082d158a4421f0a84c133f,0x10d8400a18118a44a2a138ac3e65109b4002d158a4294296826660012088401e0d098520e030105a2b0a04a833c099482b40041043c17038641e0f0d8400a18118a44a2a138ac002d,0x1038641e0f0d8400a180495026550f9902a531399c4263149b8002d15892873b04264248f0a5083e65109b44e2b128a84629038641e0f0d8400a18000b45629375042652038641e0f,0x1a2c7446921087c2a3c098483e13048445614079ac0a380d9b00e6a000b4502612d1264224b092862733884c6152987cc8132a824a8293706c200f0781c32050c0005a2b0a4804695,0x1090381004140b44c06a4518414500098482a0d078240e04010502d0308a8f2b0a46c0028130903c1a150481c08020185a2210d1a04158d0005026120a8341e090381004030b44420,0x142855081b4d81d0e0f4404c241f09824222b0a0143a23120984c00168a04839a409688051c06cd80f3581cd4130907c2609088ac2800168a04c268e054c4211288a8e00120a8341e,0x1088ac28050e88c4826130907200168a0346fa4854ac130907c2609088ac28050e88c482613084ae241c8005a280d03a9530034b00028110803c1a150484a08138105a14075263c21,0x1120e44624028744c26098483e13048445614000b450709f050b2130907c2609088ac28050e88c4826130806a062d890721a378005a2807d2e72064b850b20ea5084ae130907c2609,0x1168aa9c931147c0024020803c1a0a048100e148185a2a1353662224a04c24072303c4025330842e1f0982422051c06c3415108a0e02b0a0005a27a64e82a5607d2c40350316c346f,0x1078803e301681c002a1489849508888a002d03800542610078341409038100614890094fa70ac28001681e9a27a601470210b894cc1b0d054420f1001c8c283807c2613090242200,
0x104d440a22125400e3d0d8682a211085c2631048f81e200f8c05a07000a85226a944847281681c0026100783414090381006150a40825a8d3c0a86038f4361a0a8844217098c4123e,0x1000a8401e1405024081381808240d5521e227f8b40e00140a8401e12050240813818081a0754e26254688d18054009aa40f1004c62210b87c601b0d05442091f01c7a2d038005429,0x12783c9c24ab0b40e000f0a028120409c0c2a10012af55119683554000803c280a0481027030a80824ab49c1d0e1681c0028120a8401e0a048100613810441baac3446580754c5a07,0x1148244e0a1681c002a0f0480808100500c25acc3044fe1681c0028130803c1a0a0485408030101c25ac55c12a010a882aa103a7c3e3f099a00a9e148245a07000a84e0a8808d381b,0x1830b40e00140984822100782812040a808060dd71ee232c03ab42d038004c200f020281203010502a1206ab6fd113cc5a07000904c200f020281203010502a0d03ab5580d93c1e4e,0x1afbd41e470d8d44a83119300d5e148244e0a1681c002a0f048080810050e35d12d64520913828002a0f0480808100500d5eae08cb41aad800401e040502426020a0540612575f40f,0x1040807504073e45a07000a04c24110183c120a82054041006ac35f0d8d4464c148244a3c0a1c44e0a000a83c12020204007b01241f221681c00281309044200f0a82408020543407,0x19a8b40e001409848220f04810041086c541503d8e120f3006cba29048943e270508c4a201d0b40e00150782404040540d62b088cc41b2e81ec0251e050e2290489c1400150782404,0x1120883c1409038102a020840d659283c8e1a250a412250f89c1423128807415390b40e001507824040401ec9630d1280d62148244a1f138284625100e8002a0f04808080a9c8920f,0x10f04884f60a8ec369a07a604a4d11a08424b039f41166148244e0a1681c002a0f0480967b283cc007b2054e423128943e201d0a4122705000541e0901011667e06e142d038005026,0x1150100c1304052d121070b43632108dc2a36128881228148240e40118bc2442138285a07000a83c0539bd01e2c0d8c842370a8d8468b128881228039f00967148244e0a1681c002a,0x1050943c1b19814e61221000541e045aed214b40004c24110a03c1a150100c1310022d489074145a07000a04c24110803c1a1504c0c0404056d303073e05a07000a04c24110803c1a,
0x10481c36230b09c140f1a07838250f06c662d03800541302026d9230a120424b079f8116b128783633029cc462f039002442148244e0a1681c002a0f072d421308a412072008c5e27,0x1070b442370a8d84a22048a0096d148240e1b118583c1c138285a07000a8264383854be2130826d8250f03c681b198a412070d88c2c1e0e09c142d038005413025b66c1424080bc29,0x1040a8240e0f818081410dbe101a7d8b40e00140984822040a8240e020183e14105ba481a1703c58211b8546c251102450290481c36230b07838270504c862d0380054053a4d0342e,0x10d8783827050a4122d038005408b8094b8152f8a412070d88c2c270504c860f1a014e81e0e0005408b8dbc416e000984822140a8240e020183e080a5c1141a858b40e00140984822,0x1038380026120a0340e0207c4572518a81021068000e0e208a8100905800420d528a81009058002a0c520b40e2a04000120b9305476202f0949a1b3f822e20f1a014e8132188c2c07,0x1070680826125d602138a0b40e210685418090581c1c2a040004c280f03834041208ae9721297046160783c3610029a42a0c1502000281307ee729094545a07108342a0c0482c5408,0x1025deec1fb986c200f07814d22a04000502613c5c468e0987849751681c120b108342a0c150200e0e000781c1a140104d768b04c5e22ba0b40e09058841a15060a8100707000501e,0x11114008751309c540803838120b0a830420d1681c00280f03af177099a036100783c4a231309c5408000a03c043ac60472a1681c120b108342a0c150200e0e000903c1a090a04e0e,0x111144342e020fc4c270f1d8540803838120b0a830420d1681c002807de66e121603af0222806c64043a8944626138a81007070241615060841a2d03800501e3b4b8262d1288c3632,0x1038a02a000f9dc3415060a02a000d915022a040a02a0002912f4261380050159c04c5a0fbc8685c22288107e1e3b094462d038841a15060241607070a810001409ef53d090b04a23,0x13d8004b7b9789122280a8a810052201c1c090583cf4133c854181b2287cee210688cf02d038004e7b078a81005220001e7a1882416280a80026794e86c8a2a040a02a00119e0602d,0xc645a07119e03e77108341e7a0d9142a0c02910120b099e45408038385015139ec4b7b005f120280a8a81027
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check11441 : ¬ FormulaSat (caseFormula c11441) := checkW_sound _ k11441 9 w11441 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good11441 : caseGood c11441=true := by decide +kernel
theorem next11441 {chosen region} (disj : ∀ i∈c11441.prior, chosen i=false) (O : Later c11441.prior chosen region) : ∃ g∈c11441.groups, Matches chosen g := case_conclusion _ good11441 check11441 disj O
def c66576 : Case := ⟨[5, 11, 17],[5, 11, 17],[
s0,s1,s2,s3,s4,s5,s26,s28,s108,s137,s185,s989,
s1247,s1513,s1578,s1645,s1646,s1723,s1724
],[
t4,t6,t7,t8,t9,t10,t12,t15,t16,t17,t18,t19,
t20,t22,t23,t35,t36,t41,t42,t44,t50,t51,t52,t54,
t58,t59,t60,t61,t62,t63,t67,t68,t69,t71,t72,t74,
t75,t76,t77,t93,t95,t97,t99,t100,t102,t104,t105,t108,
t111,t112,t116,t117,t121,t126,t127,t128,t131,t132,t133,t134,
t139,t141,t142,t146,t147,t148,t151,t153,t154,t155,t156,t158,
t159,t160,t161,t165,t167,t171,t174,t175,t177,t182,t185,t190,
t192,t195,t198,t201,t203,t205,t206,t208,t209,t210,t218,t225,
t228,t232,t236,t240,t243,t244,t245,t247,t248,t249,t251,t256,
t260,t261,t262,t265,t278,t279,t284,t286,t287,t291,t295,t296,
t301,t313,t315,t316,t317,t318,t319,t320,t321,t324,t327,t331,
t335,t336,t337,t340,t342,t344,t345,t346,t347,t348,t349,t350,
t351,t352,t353,t354,t355,t356,t357,t358,t359,t360,t362,t363,
t365,t366,t368,t369,t372,t375,t376,t377,t378,t380,t382,t383,
t384,t385,t386,t387,t388
],[
g0,g1,g2,g4,g8,g32,g64,g128,g256,g512,g2048,g4096,
g8192,g16384,g32768,g131072,g262144,g524288,g1048576,g2097152,g96,g160,g192,g288,
g320,g384,g544,g576,g640,g768,g2080,g4160,g6144,g8320,g10240,g12288,
g16640,g18432,g20480,g24576,g33280,g34816,g36864,g40960,g49152,g131104,g133120,g262208,
g266240,g393216,g524416,g532480,g655360,g786432,g1048832,g1064960,g1179648,g1310720,g1572864,g2097664,
g2129920,g2228224,g2359296,g2621440,g3145728,g161,g322,g608,g704,g800,g896,g10241,
g20482,g38912,g45056,g51200,g57344,g133152,g266304,g532608,g655361,g1065216,g1310722,g2130432,
g2490368,g2883584,g3276800,g3670016,g480,g612,g904,g30720,g38916,g57352,g1966080,g2490372,
g3670024,g10401,g20802,g655521,g665601,g1311042,g1331202,g39524,g58248,g665761,g1331522,g2490980,
g2529284,g3670920,g3727368,g2529892,g3728264
]⟩
def k66576 : List Nat := [
1,2,3,176,116,177,117,178,118,179,119,47,
120,121,180,48,49,181,50,51,59,60,61,182,
122,183,62,184,63,185,186,64,123,187,124,125,
126,30,41,42,188,65,66,88,189,190,191,192,
89,193,127,90,91,67,52,92,194,195,43,68,
196,197,198,199,69,93,12,128,129,200,130,70,
9,131,201,71,132,202,72,94,44,133,95,53,
96,97,134,31,203,22,204,23,205,206,98,32,
33,207,208,209,210,211,73,74,135,136,137,212,
213,99,214,138,139,215,216,140,141,142,75,217,
218,76,219,100,220,221,222,223,101,143,102,103,
224,13,225,144,226,227,14,145,54,228,34,146,
77,104,147,78,15,79,80,229,105,230,55,148,
231,149,232,45,16,106,81,82,150,83,107,84,
108,85,109,35,86,151,36,8,152,233,153,154,
110,234,17,155,235,111,37,156,157,158,236,38,
159,39,160,237,238,239,240,241,242,243,244,245,
246,247,248,249,250,251,252,253,254,255,256,257,
258,259,260,261,262,263,264,265,266,267,268,269,
270,271,272,273,274,275,276,277,278,279,280,281,
282,283,284,285,286,287,288,289,290,291,292,293,
294,295,296,297,298,299,300,301,302,303,304,305,
306,307,308,309,310,311,312,313,314,315,316,317,
318,319,320,321,322,323,324,325,326,327,328,329,
330,331,332,333,334,335,336,337,338,339,340,341,
342,343,344,345,346,347,348,349
]
def w66576 : List Nat := [
0x10400e03008018020155f3b423008170040b000000b02a0a026090200781c06818050120400e030080180400d5e3b023008170040b000000b02a0a026090200781c06818050120400e03008018040095d,0x1090200781c06818050120400e0300601002025613bc23008170040b000000b02a0a026090200781c06818050120400e030080100201d603b823008170040b000000b02a0a026090200781c0681805012,0x10040b000000b02a0a026090200781c06818050120400c020060100203d633c423008170040b000000b02a0a026090200781c06818050120400e0200601002035623c023008170040b000000b02a0a026,0x101002055663d023008170040b000000b02a0a026090200781c06818050100380c020060100204d653cc23008170040b000000b02a0a026090200781c06818050120380c0200601002045643c82300817,0x106014048100380c020060100206d683d823008170040b000000b02a0a026090200781c06814048100380c0200601002065673d423008170040b000000b02a0a026090200781c06818048100380c02006,0x10b02a0a026090200701a06014048100380c020060100207d6a3e023008170040b000000b02a0a026090200781a06014048100380c0200601002075693dc23008170040b000000b02a0a026090200781c,0x13ec23008170040b000000b02a0a0260801e0701a06014048100380c02006010020956c3e823008170040b000000b02a0a0260901e0701a06014048100380c02006010020856b3e423008170040b00000,0x10380c02006010020ad6f3f423008170040b000000b02a098240801e0701a06014048100380c02006010020a56e3f023008170040b000000b02a0a0240801e0701a06014048100380c020060100209d6d,0x1090200781c068180501204008018040080f035713fc23008170040b000000a828098240801e0701a06014048100380c02006010020b5703f823008170040b000000b028098240801e0701a0601404810,0x10040b000000b02a0a026090200781c068180501203008018040081103d7340423008170040b000000b02a0a026090200781c06818050120380801804008110357240023008170040b000000b02a0a026,0x1008130457641023008170040b000000b02a0a026090200781c068180501003008018040081303d7540c23008170040b000000b02a0a026090200781c0681805010038080180400813035744082300817,0x1068180481003008018040081503d7841823008170040b000000b02a0a026090200781c06818048100380801804008150357741423008170040b000000b02a0a026090200781c068180500e0300801804,
0x10b02a0a026090200781c068180400e03008018040081504d7a42023008170040b000000b02a0a026090200781c068180480e0300801804008150457941c23008170040b000000b02a0a026090200781c,0x142c23008170040b000000b02a0a026090200781c060140481003008018040081b03d7c42823008170040b000000b02a0a026090200781c06814048100380801804008190357b42423008170040b00000,0x103008018040081d0657f43423008170040b000000b02a0a026090200781a060140480e03008018040081d0457e43023008170040b000000b02a0a026090200781c050120400e03008018040081b0657d,0x1090200701a060140400e03008018040081f04d8143c23008170040b000000b02a0a0260902007818050120400e03008018040081d06d8043823008170040b000000b02a0a026090200781a050120400e,0x10040b000000b02a0a0260902007018050120400e03008018040081f06d8344423008170040b000000b02a0a026090200701a050120400e03008018040081f0658244023008170040b000000b02a0a026,0x1008210658645023008170040b000000b02a0a0260901e0701a060120400e0300801804008210558544c23008170040b000000b02a0a0260902006818050120400e03008018040081f075844482300817,0x1050120400e0300801804008210758845823008170040b000000b02a0a0260901e07018050120400e03008018040082106d8745423008170040b000000b02a0a0260901e0701a050120400e0300801804,0x10b02a0a0260801e0701a06014048100380801804008250358a46023008170040b000000b02a0a0260901c06818050120400e03008018040082107d8945c23008170040b000000b02a0a0260901e06818,0x146c23008170040b000000b02a0a0240801e0701a060140481003008018040082703d8c46823008170040b000000b02a0a0260801e0701a050120400e0300801804008250658b46423008170040b00000,0x10300801804008290458f47423008170040b000000b02a0a0200781c06818050120400e0300801804008270958e47023008170040b000000b02a0a0240801e07018050120400e03008018040082706d8d,0x10781c06818050120400e0300801804008290959147c23008170040b000000b02a098240801e06818050120400e0300801804008290759047823008170040b000000b02a098240801e0701a060140480e,0x10040b000000b028098240801e0701a060140400e03008018040082b04d9348423008170040b000000b02a090200781c06818050120400e03008018040082909d9248023008170040b000000b02a09820,
0x10082b09d9649023008170040b000000b028098200781c06818050120400e03008018040082b0959548c23008170040b000000b028098240801c06818050120400e03008018040082b07d944882300817,0x1060120400e03008018040082d0559849823008170040b000000b026090200781c06818050120400e03008018040082b0a59749423008170040b000000b028090200781c06818050120400e0300801804,0x10a828098200781c06818050120400e03008018040082d0959a4a023008170040b000000a828098240781c06818050120400e03008018040082d0859949c23008170040b000000a828098240801e0701a,0x14ac23008170040b000000a826090200781c06818050120400e03008018040082d0a59c4a823008170040b000000a828090200781c06818050120400e03008018040082d09d9b4a423008170040b00000,0x1030080180204c0f0159f4b423008170040b000000b02a0a026090200781c068180501203808018040440d00d9e4b023008170040b000000a026090200781c06818050120400e03008018040082d0ad9d,0x1090200781c068180480c02006010020541103da14bc23008170040b000000b02a0a026090200781c068180481002006010020540f035a04b823008170040b000000b02a0a026090200781c0681805010,0x10040b000000b02a0a026090200781c068180380c020060100205413045a34c423008170040b000000b02a0a026090200781c068180400e020060100205413035a24c023008170040b000000b02a0a026,0x10841b065a64d023008170040b000000b02a0a0260902007018050120400e030080180207c1b015a54cc23008170040b000000b02a0a026090200781a050120400e03008018040741900da44c82300817,0x1048100380c02006010020841f065a84d823008170040b000000b02a0a0260901e06014048100380c02006010020841d06da74d423008170040b000000b02a0a0260901e07014048100380c0200601002,0x10b02a0a0260801e0701a050120400e020060100209419035aa4e023008170040b000000b02a0a0260901a06014048100380c02006010020841f075a94dc23008170040b000000b02a0a0260901c06814,0x14ec23008170040b000000b02a098240801e06818050120380c02006010020a41d045ac4e823008170040b000000b02a0a0240801e07018050120400c020060100209c1b03dab4e423008170040b00000,0x103008018020ac27015af4f423008170040b000000b028098240801c06818050100380c02006010020ac1f04dae4f023008170040b000000b02a098200781c06818050120400e03008018040a42500dad,
0x10701a06014048100380c02006010020b427095b14fc23008170040b000000a828098240781c06818048100380c02006010020b421055b04f823008170040b000000b028090200781c06818050120400e,0x10040b000000a0260801e0701a06014048100380c02006010020b42b095b350423008170040b000000a8240801e0701a06014048100380c02006010020b42909db250023008170040b000000a8280801e,0x103c0d01db651023008170040b000000b02a0a026090200781c068180500801804008130440f035b550c23008170040b00000098240801e0701a06014048100380c02006010020b42b0a5b45082300817,0x10400e03008018040081f0741b065b851823008170040b000000b02a0a026090200781c068180380c018040081504c11025b751423008170040b000000b02a0a026090200781c06818048100200400815,0x10b02a0a0260901a06014048100380c018040082107c1d025ba52023008170040b000000b02a0a0260901e07014048100380c020040082106c1901db951c23008170040b000000b02a0a0260902005012,0x152c23008170040b000000a8280801e0701a06014048100380c020040082d09c2501dbc52823008170040b000000b0200781c06818050120400e03008018040082b0a427095bb52423008170040b00000,0x10180207c1b04c0f015bf53423008170040b000000b02a0a026090200781a050120380801804074190440d00dbe53023008170040b00000098240801e0701a06014048100380c018040082d0ac29025bd,0x10781a050120400e03008018040a4250741900dc153c23008170040b000000b02a098200781c068180501203808018040a4250440d00dc053823008170040b000000b02a0a02609020070180501003008,0x10040b000000b0280902007018050120400e03008018020ac2707c1b015c354423008170040b000000b028090200781c068180501003008018020ac2704c0f015c254023008170040b000000b02a09820,0x10440d00dc655023008170040b000000b02a0a0260901a0600e03006010020841f0741504c11025c554c23008170040b000000b02a0a0260901e0701204008010020841b0641503c0d01dc45482300817,0x104008010020b4270941503c0d01dc855823008170040b000000b02809020070180501003008018020ac2707c1b04c0f015c755423008170040b000000b02a098200781a0501203808018040a42507419,0x1098240801e0701a0600e03006010020b42b0a41504c11025ca56023008170040b000000a8280781c050120400e03008010020b4270942106c1901dc955c23008170040b000000a8280801e0701a06012,
0x156c23008170040b000000a8280781c04810020040082d09c250841b0641503c0d01dcc56823008170040b000000982406818050120400e03006010020b42b0a42107c1d025cb56423008170040b00000,0x173410124121f4070c81b01c0d0540f08c050c4250e8270ec19088030bc1e0ac1c21408270000b42b0a421055ce57023008170040b0000009824068180380c018040082d0ac290841f0741504c11025cd,0x10ac29051d06f4086d0000781c0681805020098290080e0302b018040b4240481073dcb04c8304434055ce0209c070850782b01c3206c070341503c23014310943a09c3b0642200c2f0002d0ac29084a0,0x1048db051d007c940748e084a00642209c3b0943a00c2f01c3206c070341503c23014310002d0ac29745cf04c830443401c3206c070341503c23014310943a09c3b0642200c2f0748e07c94084a00002d,0x100c8409ce70640d04416074df084360545f07ce604ccc024ca0a5d10341506c0703c2301c32014310002d0ac27674256cc00098200781c06818050120400e03008018040ac2d0a002749ca040490204c,0x10781c06818048100380c020060a8020b404085d5660251701474c000b4040781c06818018120400e030080a02a00826081d4668245c0000982d0101e0701a06006048100380c020280a8020801474dd2,0x1019d7758052740f2781b184073ac0d38c19334030781f0801d07c1105813098090942b09c000b4280982d7542520020750000101e0701a06006048100382d020280a8020302675999055b00002809824,0x10c0260b4000b42806818039d975c21090151b8030781f0801d07c1105813098090942b09c050c0260b40d054000b42806818038067619b095b1000280801e0701a0602a048100380c02027010020b414,0x1285c803048050de0189e090cb0842a039d900c1e07c200741f0441604c26024250ac27014300982d0002d0a01a061da6f02431c2116c151f0067600d054030781f0801d07c1105813098090942b09c05,0x107c1105813098090942b09c000b428771c9054880341500c1e07c200741f0441604c26024250ac2701430090930189f0806406061068a10982d0002d0a00e76c240806401c1d061da0982d0002d0a01a,0x1058130981f080090941d07c03078000b42a779b20999c000200781c0681805012040080080e030290182a0b424011dd7300c1201422c0e76c201900627c2424c181841a284050c0260b4030781f0801d,0x1050120400e030080182a0a404009e0648265b82d00c000a8200781c06818050120400e03008018040a402091df7782b09c000b40377405274210ac190880d1b0253901b11c153240f118072d02877011,
0x10001c06818050120780e080080182a0a410010a2360243202d00c000a4051bdad0905409c4b009e00b4030001e0701a060140481003820020060a829030047859109cd9091df0b403000200781c06818,0x1791e20086c09c45040a20146f01c6d0842b03c4607c5d04c6606c470544c024630b403000290602a0700d78c54095c00b4030001c0801e0601a0a4140480e02006010110982a00c0d7886c00c3c031e1,0x1060140481e0382002006068290a804799ac041900b40300026090200781a060140481d038080a406010020a80c7958f0949500c3e035e309c45040a20b4030001a060140481e03820020060a82907004,0x10600428dbb090dd099e70b4030001e0701a060140481002002038200a4060102b031e83702465c2d00c000801e0701a0601404810020020382b0a4060100c099e7794251480d1382723c0315c1c79000,0x1011ea704110f8270202b0341c19c24150020881828c051bc1b11c071b4210ac0f1181f17413198151300918c2d00c000a40c7a5e80345e0443400c2f074600a9e60b403000140481e038200200606829,0x10b40300004068190801e0740d291ea0146f06c4704c6603c460842b0544c01c6d0246307c5d0b40300029011c60403c031e90905407067008220ac0d09c08060a30b403000120780e080080181a0a414,0x10101a064200781d7b1a40443e094510242803c0c01c1d0ac0d0542904c2c09c08034a40a4040b40300004068190801e074037adbe0403c094510084e0242803c0c01c1d0ac0d0542904c2c09c080a404,0x1050120400e020060102a0080d7b98b091670b4030a40400026050200781c068120400e0a8080180406402031ed5fc2514811248037ac0d290090a00f030070742b034150a4130b027020290102d00c00,0x17bc112480319c1d7b0090a00f030070742b034150a4130b0270202d00c000101a06420079f07b80c7b400050200781c068120980e0a8080180406410009ef6a8245ec2d00c2901000098190801e0701a,0x1064066181f6a02d00c2901000098240701a050120840e0300801804008190a8107c9820445a074d603450094e200c58079f00242803c0c01c1d0ac0d0542904c2c09c080a4040b4030000406819081f1,0x101002040087d1890796b0b4030a4040002607024068180a8120840e030100180400808051f37c81110c1d2640d0d425200030cc207c4130b02b0340f03027020150a4090a007074290102d00c000101a,0x10cc0f0a819018251280d0d42b0d82709029010000101a01821070703041f164087d0000901a0602a048210380c0980601002070107d58507c42051f30b4030a4040001c0901a0602a048210380c09806,
0x16a42d00c29010000982406818050120740e0302a0180400821040087ddba078bd00c3303c2a064060944a034350ac3609c240548a07070044430a4040b403000040680608412025f67d41110c1330c03,0x1050be049f80707009c240ac36034350944a03c2a00c33064060a4040b4030000406806084117dc097d81110c15228030cc0f0a819018251280d0d42b0d8270901c1c029010000101a01821049f86201f,0x10b4030a404000260902006818050120740e03008018040a802041fa5f81f1680f1a42514813194152440922421044272080d1380315c19018290102d00c000101a0182a074117e5c504049078bf02065,0x10180400824021fc5741f5a8290102d00c00098240801a060100481c0380c0a80601002020147edfa045f909c820549104c65094520344e03c690248900c57064060841100004068060a81d0dd6907d84,0x10a4040001a060100481c038200a806010020980c295610547d07c59021fc0b4030a4040002006818040120700e0982a018040080c091fd5981f108147ec2d00c29010000982006818040120700e0302a,0x10b4030a40400026040200341c06818078120382a0180400808091ff62815170091e41f1400c294210441d0dc19018290102d00c000101a0182a0480e00810098257f96c07c7f0545c024c5091fd0b403,0x10481c038200a80601018008108098e0916d0b4030a404000200781c0681809c120400e0302a0180400808052017fc257f81f140091e40c29429010000601a0481c038200a80601002040268017705162,0x1070200a818068120200e09011018040082607a0416815108000701107ca65e4145902d00c29010000981c0802a0601a048080382404406010020301e80e010546e024ea07c6b0348109a000b4030001a,0x10247409c4b094510547b07c58008a70640608411074370a4040b40300004068060a812038118160407ca60949509c45024b804202000120701a0802a018040600e008a75c8153a00c80c2d00c2901000,0x100826036085e01458c2d00c29010000a8240801e0701a0600f0481002006010020980c81d5e0343c0460507c580547b0945109c4b02474008a70b4030a4040001c068200a806010180480e8199e0303e,0x1204268242d00c29010000801e0701a0600f0482a02006010020901082a0803207000240801e0701a0600f0482a020060100204026825a0051710b4030a4040002a090200781c068180401203c0801804,0x18182d00c00068200a80601018070121c60b034cf09c450420a0001e0701a0600f0482a020060102000824831a1051730b4030a40400026090200781c068180441203c08018040a8020320b630151b80d,
0x1048710743706406084110a4040b40300004068060a80f839b5030d20944409c530247607c4f00c9005486048710743706406084110a4040b40300004068060a80f0460d830093a41f13c25318032d80e,0x10b4030a40400026090200781c068180a802038080180404c10036105e8145942d00c2901000098240801e0701a0601303802020060102a0400c83d75034d00460d00c9007c4f05486024760944409c53,0x1000200981c0681804c0e00824018040a80807a1368c145d82d00c2901000098240801e0701a0602a0380804c06010020440c84a100320f00024080260701a0601303802020060102a07810845a205174,0x1072166dc10124142e81f1640d2c8088502d00c29010000701a060130380209006010200982a85581044a6034500544207a130b4030a404000260701a060130380209006010200a80885212034d104211,0x10b403000040680604e186b81e64c2d00c29010000902004c1c068180400e0200c050060102b0980285e1607437064060841100004068060a8a8854032e40f8382714c25110121c4000801a018040602a,0x106014030100382b02006010020921a6501e5bc2d00c2901000008200481c068180500c0400e0ac0801804090268661709c530944400cb3064060841103c230249b0345e07460044340545f0a8a80a404,0x12a48409c4b00a1b0b4030001c068180500c0400e0ac0801804048208719509cda07c7f0921a0b4030a404000120701a06014030100382b020060102000a1b6581f1ac268642d00c2901000080120701a,0x12a4290102d00c000101a03a1e2d40c5802d00c2901000098240801e0701a0602a0481001c0402002038148761c04e18044340345e0545f0249b03c23074600a8a808411064060a4040b4030000406806,0x103048050b703a1e07c7e04c7a09c9a07498044970ac960948d0845b0247500c73018a9064060b4030a4040000406812874151f019018031cc091d42116c27268131e81125c252341f1f81d2602b25806,0x1018040080e07a2187c1f13c130381103c2502c090402b01c071000d08415104031881a0482d00c00010180801c03e206ac265f02d00c29010000a8240801c0301805012040060201b0100203c1e87db6,0x101c071000d08415104031881a0482d00c00010180801c88d8309c6b07a210b4030a404000240801806c14048100a80c02006010020700e8898d099680b4030a4040001c090200601b050120402a03008,0x106014048100380c020060102a06c2100a256002723c0f1a41f35c1c88c03188130381103c2502c090402b01c071000d084151041a048290102d00c0001018082248880f880130381103c2502c090402b,
0x10e00d084151a01a048290102d00c0001006084aa894032ec1f230270900f0a8208900d0841510407100130381103c2502c090402b01c1a048290102d00c00010180e187075a70b4030a404000260901e,0x100004018ab5f41d350130381103c2502c090402b01c030b8270200f030180e00d084151a01a048212a8290102d00c000100607a266981f2301d264130381103c2502c090402b01c030b8270200f03018,0x102c090402b01c030b81a048270201d1dc1f1e02021c062ac180e0290102d00c000100e89db8070d507a26084aa0342103c0c0546804c0e0440f0940b024100ac0700c2e0681209c08060380a4040b403,0x1024192c0040140001c182bc040140000c177100c1201422c0e89c2021c1f1e01d1dc062ac27020030b8180e0090402b01c1103c130382502c1a048290102d00c00010056e40d30815220130381103c25,0x106c2a04a282f00401419050000741c34c040142104c00064143800401415028000441b3380401415028000341a394250240401400084133842502404014000540a310290100401400094092c40401400,0x10100500c1701c18024190341a0441b0540a064140741c08413094090a4040b4030001b0a8ac6940f0f41e134271a8040140305c07060090640d0681106c15028190501d0702104c25024290102d00c00,0x1028190501d0702104c25024290102d00c0006c3971c0e0fc1e134261542a2b0040140305c07060090640d0681106c15028190501d0702104c25024290102d00c0006c138a5bf0383f04a2809c6a0784d,0x100c1701c18024190341a0441b0540a0641406c390741c07c5608413094090a4040b4030002b04a2a300040141b0e40007c5670c0f0f4138a4261542a2b01e134040140305c07060090640d0681106c15,0x10a4040ac720b403000132b86a010050ac72000272b5c20383f04a2a098550100500c1701c18024190341a0441b0540a0641406c390741c07c5608413094090a4040b4030002b1c9af03c3d0985501005,0x10701b0e41905015028272b41106c070600d068090640305c132b80f8ac008b03d0100504cae0000f8ad9f0383f0100500c1701c18024190341a0441b0540a0641406c390741c07c56084130940909cad,0x157c2d00c2b1c82901004014250242104c1f1581d
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check66576 : ¬ FormulaSat (caseFormula c66576) := checkW_sound _ k66576 10 w66576 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good66576 : caseGood c66576=true := by decide +kernel
theorem next66576 {chosen region} (disj : ∀ i∈c66576.prior, chosen i=false) (O : Later c66576.prior chosen region) : ∃ g∈c66576.groups, Matches chosen g := case_conclusion _ good66576 check66576 disj O
def c732337 : Case := ⟨[1, 5, 6, 8, 11, 12, 14, 17, 18, 20],[1, 5, 6, 8, 11, 12, 14, 17, 18, 20],[
s2,s4,s5,s200,s1513,s1645,s1646,s1710
],[
t9,t10,t17,t19,t22,t23,t61,t71,t72,t318,t319,t321,
t325,t327,t329,t330,t332,t333,t342,t351,t352,t353,t357,t359,
t360,t369,t370,t371,t372,t373,t374,t375,t376,t377,t378,t379,
t380,t381,t382,t383,t384,t385,t386,t387,t388,t389,t390,t391
],[
g0,g2,g4,g8,g64,g256,g512,g4096,g16384,g32768,g262144,g1048576,
g2097152,g320,g576,g768,g4160,g16640,g20480,g33280,g36864,g49152,g262208,g266240,
g1048832,g1064960,g1310720,g2097664,g2129920,g2359296,g3145728,g322,g580,g776,g20482,g36868,
g49160,g266304,g1065216,g1310722,g2130432,g2359300,g3145736,g20802,g37444,g49928,g1311042,g1331202,
g2359876,g2396164,g3146504,g3194888,g1331522,g2396740,g3195656
]⟩
def k732337 : List Nat := [
1,2,3,4,5,6,7,8,9,10,26,27,
28,54,23,55,56,80,29,30,31,32,33,34,
49,35,36,37,57,38,39,58,50,59,60,61,
81,82,62,63,83,40,41,64,42,43,65,44,
45,84,85,66,67,86,87,68,51,88,89,20,
69,16,52,17,90,91,92,93,94,95,96,97,
98,99,100,101,102,103,104,105,106,107,108,109,
110,111,112,113,114,115,116,117,118,119,120,121,
122,123,124,125,126,127,128,129,130,131,132,133,
134,135,136,137,138,139,140,141,142,143,144,145,
146
]
def w732337 : List Nat := [
0x1071d061905170411030d020b010300002c2a26201e1a14120e080605935b2909250823071d061905170411030d020b010300002c2a26201e1a14120e08060492,0x10411030d020b010300002c2a26201e1a14120e060409955d2909250823071d061905170411030d020b010300002c2a26201e1a14120e080407945c2909250823,0x1010300002c2a26201e1a140e08060413975f2909250823071d061905170411030d020b010300002c2a26201e1a14120806040f965e2909250823071d06190517,0x126201e14120e0806041b99612909250823071d061905170411030d020b010300002c2a26201e1a120e0806041598602909250823071d061905170411030d020b,0x1080604219b632909250823071d061905170411030d020b010300002c2a26201a14120e0806041f9a622909250823071d061905170411030d020b010300002c2a,0x12909250823071d061905170411030d020b010300002c2a201e1a14120e080604279c642909250823071d061905170411030d020b010300002c2a261e1a14120e,0x11d061905170411030d020b010300002a26201e1a14120e0806042d9e662909250823071d061905170411030d020b010300002c26201e1a14120e0806042b9d65,0x111030d020b010300002c2a26201e1a12080604150fa0682909250823071d061905170411030d020b010300002c2a26201e1a14080604130f9f67290925082307,0x10300002c2a26201e14120806041b0fa26a2909250823071d061905170411030d020b010300002c2a26201e1a0e0806041513a1692909250823071d0619051704,0x12014120e0806041f1ba46c2909250823071d061905170411030d020b010300002c2a26201a140e0806041f13a36b2909250823071d061905170411030d020b01,0x104211ba66e2909250823071d061905170411030d020b010300002c2a261e1a120e0806042115a56d2909250823071d061905170411030d020b010300002c2a26,0x109250823071d061905170411030d020b010300002c2a261a14120e080604211fa76f2909250823071d061905170411030d020b010300002c2a261e14120e0806,
0x1061905170411030d020b010300002c2a201e14120e080604271ba9712909250823071d061905170411030d020b010300002c2a201e1a1412080604270fa87029,0x1030d020b010300002c26201a14120e0806042b1fab732909250823071d061905170411030d020b010300002c26201e1a140e0806042b13aa722909250823071d,0x100002a26201e1a120e0806042d15ad752909250823071d061905170411030d020b010300002c201e1a14120e0806042b27ac742909250823071d061905170411,0x114120e0806042d27af772909250823071d061905170411030d020b010300002a261e1a14120e0806042d21ae762909250823071d061905170411030d020b0103,0x10f05b1792909250823071d061905170411030d020b0103000026201e1a14120e0806042d2bb0782909250823071d061905170411030d020b010300002a201e1a,0x1250823071d061905170411030d020b010300002c2a26201e1a120804150f07b27a2909250823071d061905170411030d020b010300002c2a26201e1a14080613,0x11905170411030d020b010300002c2a262014120e08061f1b05b47c2909250823071d061905170411030d020b010300002c2a26201e1a0e0604151309b37b2909,0x10d020b010300002c2a261a14120e0604211f09b67e2909250823071d061905170411030d020b010300002c2a261e14120e0804211b07b57d2909250823071d06,0x1002c26201a140e0806042b1f13b8802909250823071d061905170411030d020b010300002c2a201e1412080604271b0fb77f2909250823071d06190517041103,0x10e0806042d2115ba822909250823071d061905170411030d020b010300002c201e1a14120e08062b2705b9812909250823071d061905170411030d020b010300,0x109bc842909250823071d061905170411030d020b010300002a201e1a14120e08042d2707bb832909250823071d061905170411030d020b010300002a261e1a12,0x10823071d061905170411030d020b010300002c2a26201408061f1b130f05bd852909250823071d061905170411030d020b0103000026201e1a14120e06042d2b,
0x105170411030d020b010300002c2a261a0e0604211f151309bf872909250823071d061905170411030d020b010300002c2a261e120804211b150f07be86290925,0x1020b010300002c2014120e08062b271f1b05c1892909250823071d061905170411030d020b010300002c201e1a1408062b27130f05c0882909250823071d0619,0x12a1e14120e08042d27211b07c38b2909250823071d061905170411030d020b010300002a201e1a1208042d27150f07c28a2909250823071d061905170411030d,0x1042d2b211f09c58d2909250823071d061905170411030d020b0103000026201e1a0e06042d2b151309c48c2909250823071d061905170411030d020b01030000,0x1c78f2909250823071d061905170411030d020b010300002c201408062b271f1b130f05c68e2909250823071d061905170411030d020b01030000261a14120e06,0x123071d061905170411030d020b01030000261a0e06042d2b211f151309c8902909250823071d061905170411030d020b010300002a1e1208042d27211b150f07,0x1c41221084314ca001a262b0e06042d201ecb0f091f12c900201a262b0e06042d1e14cab009bc00201e1a262b0e06042d1412c950214f002d2b27459129092508,0x136002d2b14c8122114cc1e2308322046002b0e06042d261acdc5131f1e23083220461b2807370f2705362745002d2b14cc1009311ecb00262b0e06042d1a2046,0x1132b14002d2617cf21ce001a04120e082a1e2d2606d0ad149e00041e1a0e1226082d2a0620cfba14ae00261a04120e082a1e2d0621cecd27451b280f27073705,0x12d1a47bb2122152006d1130f1f1009132b1405162617002d1a0ed2af21421541130f1f1009132b1405162617002d1a0e06d1d005571b330f440758130f1f1009,0x1331a47051626171f10130f0913002d2ad4c7141d130f1f1009132b1405162617202606331a47002d0fd3c22122141d06440ed2130f1f1009132b140516261700,0x1270bd61bd5001e14120806272a2004d7a80e9c2d0a001e0814122027062a041ad6b70ea92d0a00201e14120806272a041bd5d42b14002d0ac315200fd3202606,
0x1002a1e26120806042014da990fa22d0a0026201e2a12080604141bd9920f962d0a00262a1e2012080604141ad8d709542142154107531f3e133d05512d0a002a,0x1212a081e06041214dda51b390f3b2048270b2d0a002a06041e081215dcdb1b3914da001e262a080604122048a00e982d0a0026201e2a120806041a15dbd91ad8,0x12a06041308e1590ea12d0a0026201e1a132a06040815e09f0e972d0a0026201e1a132a06040814dfdd15dc0f3b204800262a1e06040812dea61a9b2d0a00260e,0x113e21b400f3f212308492d0a0026062a041e2db3141f21230f3f1b400849270b2d0a002a06041e13e2e1213c1b3812de002a2606041e0849e014df00201e1a26,0x1153a094a1e2d270b2d0a002a060413e4bf141f12e320311b350f251e2d270b2d0a002a0604094ab615210f251b3520311e2d270b2d0a002a06040912e3951521,0x1251e2d00262a06042ee620e5001214080e26062a1f04e75a1aa72d0a00261214080e1f062a0421e6a41a9a2d0a00261214080e1f062a0420e5a3213c1b380f25,0x1270b2d0a002a0613e9bd0e1e12e81a30091a152a212c042e270b2d0a002a061f4bb40f1c091a152a212c1a30042e270b2d0a002a061f12e8e713e4153a094a0f,0x14c941b260519091b13291f2b0f1d062f270b2d0a002a1420ea930f1c13e91b241f4b212c152a091a042e2d0a002a26062fb10e1e091a152a212c1b241f4b042e,0x12b1329091b0519062f2d0a002a26ecbe1a220519091b13291f2b0e20144c062f270b2d0a002a21ebb51a2220ea0f1d0519091b13291f2b062f270b2d0a002a14,0x10e1511090d07122a0c000e1a04261eed552a0c210e000712322a0c090d00210e432a0c090d001511562d0a2a0c00090dec270b002a0cb21b2621eb0e20144c1f,0x12a0c090d26181511210e2d0a000415ef1b280f2705522a0c002618ee1eed001a040e26efb812ab2d0a210e1511090d2a0c0712001a0e04261fee9d13aa2d0a21,0x11a4dc0121c0ef01b24261804150712090d15112a0c210e2d0a001e34b9131e1b2404150712090d2a0c26181511210e2d0a001e0ef0ac1f3e133d1b280f270712,
0x1210e15112a0c1a4d090d07121e34041526180f4e13f100f21e04150f4e0013f1c6121c261804151e341a4d2a0c0712090d1511210e2d0a000f4e3004151e3400,0x1c12d0a
]
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem check732337 : ¬ FormulaSat (caseFormula c732337) := checkW_sound _ k732337 8 w732337 (by decide +kernel)
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem good732337 : caseGood c732337=true := by decide +kernel
theorem next732337 {chosen region} (disj : ∀ i∈c732337.prior, chosen i=false) (O : Later c732337.prior chosen region) : ∃ g∈c732337.groups, Matches chosen g := case_conclusion _ good732337 check732337 disj O
end PEqualNP.Outside.L_pcx_120.Oldest
