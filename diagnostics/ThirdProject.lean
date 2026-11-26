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

structure Many where
  lo : List Nat
  hi : List Nat
  start : Nat
  pairs : List (Nat × Nat)
def finish (a : Nat) : List (Nat × Nat) → Nat
  | [] => a
  | (b,c)::bs => finish (a ^^^ b ^^^ c) bs
def geoGood (t : Many) := (sub (labels t.start) t.lo &&
  t.pairs.all (fun pair => sub (labels pair.1) t.lo && sub (labels pair.2) t.lo)) &&
  sub (labels (finish t.start t.pairs)) t.hi
theorem geo_implies {prev chosen region} (O : Later prev chosen region) {t : Many}
    (valid : geoGood t=true) (sep : t.hi.all (fun i => !prev.contains i)=true)
    (J : AllOn chosen t.lo) : AnyOn chosen t.hi := by
  simp only [geoGood,Bool.and_eq_true] at valid
  have hp {x : Nat} (h : sub (labels x) t.lo=true) := O.exclusive x (fun i hi => J i (sub_mem h hi))
  have chain (ls : List (Nat × Nat)) (all : ∀ y∈ls, region y.1 ∧ region y.2) (a : Nat) (ha : region a) :
      region (finish a ls) := by
    induction ls generalizing a with
    | nil => exact ha
    | cons t ls rec =>
      obtain ⟨b,c⟩ := t
      have h := all (b,c) (by simp)
      exact rec (fun z hz => all z (by simp [hz])) _ (O.closed _ _ _ ha h.1 h.2)
  have conclude := chain t.pairs (fun y hy => by
    have z := List.all_eq_true.mp valid.1.2 _ hy
    simp only [Bool.and_eq_true] at z
    exact ⟨hp z.1,hp z.2⟩) t.start (hp valid.1.1)
  rcases O.upper _ conclude with ⟨i,hi,v⟩ | ⟨i,hi,v⟩
  · exact ⟨_,sub_mem valid.2 hi,v⟩
  · have no := List.all_eq_true.mp sep _ (sub_mem valid.2 hi)
    simp at no
    exact False.elim (no v)
inductive Reason
  | collision (i : Nat)
  | force (t : Many)
def reasonGood : Reason → Bool
  | .collision _ => true
  | .force t => geoGood t
def supports (lo hi : List Nat) : Reason → Bool
  | .collision i => lo.contains i
  | .force t => sub t.lo lo && sub t.hi hi
def separates (prior : List Nat) : Reason → Bool
  | .collision i => prior.contains i
  | .force t => t.hi.all (fun i => !prior.contains i)
structure Block where
  lo : List Nat
  hi : List Nat
  why : List Reason
def justified (priors : List (List Nat)) (b : Block) :=
  b.why.all (fun r => reasonGood r && supports b.lo b.hi r) &&
  priors.all (fun prev => b.why.any (separates prev))
def blockClause (b : Block) := negs b.lo ++ poss b.hi
theorem project_sound {priors b chosen region prev} (O : Later prev chosen region)
    (inset : prev∈priors) (disj : ∀ i∈prev, chosen i=false) (cert : justified priors b=true)
    (lo : AllOn chosen b.lo) : AnyOn chosen b.hi := by
  simp only [justified,Bool.and_eq_true] at cert
  obtain ⟨r,hr,sep⟩ := List.any_eq_true.mp (List.all_eq_true.mp cert.2 _ inset)
  have w := List.all_eq_true.mp cert.1 _ hr
  cases r with
  | collision i =>
    have h : i∈b.lo := List.contains_iff_mem.mp (by simpa [reasonGood,supports] using w)
    have hp : i∈prev := List.contains_iff_mem.mp sep
    have onv := lo i h
    rw [disj _ hp] at onv
    contradiction
  | force t =>
    simp only [reasonGood,supports,Bool.and_eq_true] at w
    obtain ⟨i,hi,onv⟩ := geo_implies O w.1 sep (fun i hi => lo i (sub_mem w.2.1 hi))
    exact ⟨i,sub_mem w.2.2 hi,onv⟩
def rootSpans : List Span := [
⟨[1, 2],640,[[1280, 1281], [768, 770], [644], [1280, 1288], [768, 784], [672], [896, 1088, 1280], [768, 896], [896], [1280, 1792], [768, 1792], [768, 1088, 1792, 2112]]⟩,⟨[1, 3],528,[[1056, 1057], [544, 546], [532], [560, 1032, 1056], [544, 560], [560], [1056, 1120], [544, 672], [784], [1056, 1568], [544, 1568], [544, 1032, 1568, 2056]]⟩,⟨[2, 3],514,[[518, 1025, 1028], [516, 518], [518], [1028, 1036], [516, 532], [546], [1028, 1092], [516, 644], [770], [1028, 1540], [516, 1540], [516, 1025, 1540, 2049]]⟩,⟨[1, 4],80,[[160, 161], [96, 98], [84], [112, 136, 160], [96, 112], [112], [160, 224], [96, 224], [96, 136, 224, 264], [160, 672], [96, 1120], [2128]]⟩,⟨[2, 4],66,[[70, 129, 132], [68, 70], [70], [132, 140], [68, 84], [98], [132, 196], [68, 196], [68, 129, 196, 257], [132, 644], [68, 1092], [2114]]⟩,⟨[3, 4],10,[[14, 17, 20], [12, 14], [14], [20, 28], [12, 28], [12, 17, 28, 33], [20, 84], [12, 140], [266], [20, 532], [12, 1036], [2058]]⟩,⟨[5, 6, 7, 9],652,[[1100, 1101], [1100, 1101, 2121, 2122], [1097, 1101], [1121, 1129], [1121, 1129, 2121, 2129], [1097, 1129], [1289, 1353], [778, 1100, 1353, 2121, 2122], [1097, 1353], [778, 1289, 2122, 3145], [2121, 3145], [1097, 3145]]⟩,⟨[1, 8, 9],648,[[672, 673], [776, 778], [652], [672, 680], [672, 680, 776, 784], [680], [672, 904, 1120, 1288], [776, 904], [904], [1288, 1800], [776, 1800], [672, 784, 1120, 1800, 2128]]⟩,
⟨[4, 5, 10],84,[[140, 141], [140, 141, 265, 266], [137, 141], [161, 169], [98, 140, 169, 265, 266], [137, 169], [98, 161, 266, 393], [265, 393], [137, 393], [596], [265, 1289], [137, 2185]]⟩,⟨[1, 6, 10],592,[[1120, 1121], [608, 610], [596], [624, 784, 1120, 1288], [608, 624], [624], [672, 736], [608, 736], [672, 736, 784], [1120, 1632], [608, 1632], [1120, 1632, 2128]]⟩,⟨[5, 6, 7, 10],596,[[1100, 1101], [1100, 1101, 2121, 2122], [1097, 1101], [1121, 1129], [610, 1100, 1129, 2121, 2122], [1097, 1129], [1289, 1353], [1289, 1353, 2121, 2185], [1097, 1353], [610, 1121, 2122, 3145], [2121, 3145], [1097, 3145]]⟩,⟨[6, 7, 9, 10],586,[[590, 610, 1100, 1121], [588, 590], [590], [596, 604], [588, 604], [596, 604, 610], [652, 716], [588, 716], [652, 716, 778], [1100, 1612], [588, 1612], [1100, 1612, 2122]]⟩,⟨[5, 8, 9, 10],596,[[652, 653], [652, 653, 777, 778], [649, 653], [673, 681], [610, 652, 681, 777, 778], [649, 681], [610, 673, 778, 905], [777, 905], [649, 905], [1289, 1801], [777, 1801], [649, 1289, 1801, 2185]]⟩,⟨[3, 11, 12],530,[[534, 546, 1036, 1057, 2058, 2066], [532, 534], [534], [546, 562, 2058, 2066], [546, 562], [562], [2066, 2130], [546, 674], [786], [2066, 2578], [532, 1036, 2058, 2578], [2578]]⟩,⟨[1, 11, 13],656,[[2192, 2193], [784, 786], [660], [688, 784, 1120, 1288, 2128, 2192], [672, 688], [688], [784, 912, 2128, 2192], [784, 912], [912], [2192, 2704], [672, 1120, 2128, 2704], [2704]]⟩,⟨[2, 11, 14],644,[[1092, 1094, 1281, 1282], [1092, 1094], [1090, 1094], [1282, 1290], [770, 786], [1090, 1122], [1282, 1346], [770, 1092, 1346], [1090, 1346], [1282, 1794], [770, 1794], [770, 1090, 1794, 2114]]⟩,
⟨[4, 11, 14],82,[[86, 98, 140, 161, 266, 274], [84, 86], [86], [98, 114, 266, 274], [98, 114], [114], [274, 338], [84, 140, 266, 338], [338], [274, 786], [98, 1122], [2130]]⟩,⟨[3, 12, 14],532,[[1036, 1038, 1057, 1058], [1036, 1038], [1034, 1038], [1058, 1066], [546, 1036, 1066], [1034, 1066], [1058, 1122], [546, 674], [1034, 1290], [1058, 1570], [546, 1570], [546, 1034, 1570, 2058]]⟩,⟨[1, 13, 14],656,[[2192, 2193], [1120, 1122], [660], [688, 784, 1120, 1288, 2128, 2192], [672, 688], [688], [784, 912, 2128, 2192], [784, 912], [912], [2192, 2704], [672, 1120, 2128, 2704], [2704]]⟩,⟨[2, 13, 14],644,[[1092, 1094, 1281, 1282], [1092, 1094], [1090, 1094], [1282, 1290], [660], [1090, 1122], [1282, 1346], [770, 1092, 1346], [1090, 1346], [1282, 1794], [770, 1794], [770, 1090, 1794, 2114]]⟩,⟨[8, 12, 13, 14],657,[[660, 661], [660, 661, 673, 674], [661], [674, 689, 2186, 2193], [673, 689], [689], [674, 913, 1122, 1290, 2186, 2193], [785, 913], [913], [2193, 2705], [785, 1290, 2186, 2705], [2705]]⟩,⟨[11, 12, 13, 14],658,[[660, 662, 2193, 2194], [660, 662], [662], [690, 786, 1122, 1290, 2130, 2194], [674, 690], [690], [786, 914, 2130, 2194], [786, 914], [914], [2194, 2706], [674, 1122, 2130, 2706], [2706]]⟩,⟨[1, 11, 15],672,[[1296, 1297], [784, 786], [1104, 1108], [1120, 1136, 1288, 1296], [1120, 1136], [1104, 1136], [1296, 1360], [784, 1120, 1360], [1104, 1360], [1296, 1808], [784, 1808], [784, 1104, 1808, 2128]]⟩,⟨[3, 12, 15],532,[[1044, 1045], [546, 1045, 1057], [1041, 1045], [1044, 1052], [1036, 1052], [1036, 1041, 1052, 1057], [1044, 1108], [546, 674], [1041, 1297], [1044, 1556], [1556], [546, 1036, 1041, 1057, 1556, 2058]]⟩,
⟨[1, 14, 15],672,[[1296, 1297], [1120, 1122], [1104, 1108], [1120, 1136, 1288, 1296], [1120, 1136], [1104, 1136], [1296, 1360], [784, 1120, 1360], [1104, 1360], [1296, 1808], [784, 1808], [784, 1104, 1808, 2128]]⟩,⟨[11, 12, 14, 15],674,[[1108, 1110, 1297, 1298], [1108, 1110], [1106, 1110], [1122, 1138, 1290, 1298], [1122, 1138], [1106, 1138], [1298, 1362], [786, 1122, 1362], [1106, 1362], [1298, 1810], [786, 1810], [786, 1106, 1810, 2130]]⟩,⟨[3, 11, 16],530,[[534, 546, 1036, 1057, 2058, 2066], [532, 534], [534], [546, 562, 2058, 2066], [546, 562], [562], [2066, 2130], [1036, 1164], [786], [2066, 2578], [532, 1036, 2058, 2578], [2578]]⟩,⟨[4, 11, 16],82,[[86, 98, 140, 161, 266, 274], [84, 86], [86], [98, 114, 266, 274], [98, 114], [114], [274, 338], [84, 140, 266, 338], [338], [274, 786], [140, 1164], [2130]]⟩,⟨[1, 12, 16],672,[[1184, 1185], [674], [1160, 1164], [1184, 1192], [784, 1192, 1288], [1160, 1192], [1184, 1248], [1120, 1248], [1120, 1160, 1248, 1288], [1184, 1696], [1696], [784, 1120, 1160, 1288, 1696, 2128]]⟩,⟨[4, 12, 16],84,[[140, 142, 161, 162], [140, 142], [138, 142], [162, 170], [98, 140, 170], [138, 170], [162, 226], [98, 226], [98, 138, 226, 266], [162, 674], [140, 1164], [138, 2186]]⟩,⟨[2, 13, 16],644,[[1156, 1157], [770, 1157, 1281], [1153, 1157], [1156, 1164], [660], [1153, 1185], [1156, 1220], [1092, 1220], [1092, 1153, 1220, 1281], [1156, 1668], [1668], [770, 1092, 1153, 1281, 1668, 2114]]⟩,⟨[4, 13, 16],84,[[148, 149], [98, 149, 161], [145, 149], [148, 156], [140, 156], [140, 145, 156, 161], [148, 212], [212], [98, 140, 145, 161, 212, 266], [148, 660], [140, 1164], [145, 2193]]⟩,
⟨[3, 14, 16],532,[[1036, 1038, 1057, 1058], [1036, 1038], [1034, 1038], [1058, 1066], [546, 1036, 1066], [1034, 1066], [1058, 1122], [1036, 1164], [1034, 1290], [1058, 1570], [546, 1570], [546, 1034, 1570, 2058]]⟩,⟨[12, 13, 14, 16],660,[[1164, 1166, 1185, 1186], [1164, 1166], [1162, 1166], [1186, 1194], [674, 1164, 1194], [1162, 1194], [1186, 1250], [1122, 1250], [1122, 1162, 1250, 1290], [1186, 1698], [674, 1698], [674, 1162, 1698, 2186]]⟩,⟨[3, 15, 16],532,[[1044, 1045], [546, 1045, 1057], [1041, 1045], [1044, 1052], [1036, 1052], [1036, 1041, 1052, 1057], [1044, 1108], [1036, 1164], [1041, 1297], [1044, 1556], [1556], [546, 1036, 1041, 1057, 1556, 2058]]⟩,⟨[12, 13, 15, 16],660,[[1172, 1173], [674, 1173, 1185], [1169, 1173], [1172, 1180], [1164, 1180], [1164, 1169, 1180, 1185], [1172, 1236], [1108, 1236], [1108, 1169, 1236, 1297], [1172, 1684], [1684], [674, 1164, 1169, 1185, 1684, 2186]]⟩,⟨[11, 14, 15, 16],786,[[1110, 1122, 1164, 1185, 1290, 1298], [1108, 1110], [1106, 1110], [1122, 1138, 1290, 1298], [1122, 1138], [1106, 1138], [1298, 1362], [1108, 1164, 1290, 1362], [1106, 1362], [1298, 1810], [1810], [1106, 1810, 2130]]⟩,⟨[4, 11, 18],82,[[86, 98, 140, 161, 266, 274], [84, 86], [86], [98, 114, 266, 274], [98, 114], [114], [274, 338], [84, 140, 266, 338], [338], [274, 786], [84, 266, 1292], [2130]]⟩,⟨[3, 17, 19],532,[[546, 550, 1057, 1060], [548, 550], [546, 550], [564, 1036, 1060], [548, 564], [564], [1060, 1124], [548, 676], [546, 802], [1060, 1572], [548, 1572], [546, 1036, 1572, 2058]]⟩,⟨[3, 19, 20],532,[[546, 1036, 1057, 2062, 2068], [2060, 2062], [2058, 2062], [2068, 2076], [2060, 2076], [546, 2058, 2076], [2068, 2132], [2060, 2188], [546, 802], [2068, 2580], [1036, 2060, 2580], [2580]]⟩,
⟨[4, 18, 21],84,[[98, 140, 161, 270, 276], [268, 270], [266, 270], [276, 284], [268, 284], [98, 266, 284], [276, 340], [140, 268, 340], [340], [276, 788], [268, 1292], [98, 2146]]⟩,⟨[4, 19, 21],84,[[290, 291], [289, 291], [140, 161, 266, 291], [290, 298], [98, 140, 161, 289, 298], [266, 298], [290, 354], [98, 161, 289, 354], [98, 354], [290, 802], [289, 1313], [98, 2146]]⟩,⟨[1, 20, 21],672,[[2208, 2209], [2144, 2146], [2128, 2132], [784, 1120, 1288, 2160, 2208], [2144, 2160], [2128, 2160], [2208, 2272], [2144, 2272], [784, 2128, 2272], [2208, 2720], [1120, 2144, 2720], [2720]]⟩,⟨[2, 20, 21],644,[[770, 1092, 1281, 2118, 2180], [2116, 2118], [2114, 2118], [2180, 2188], [2116, 2132], [2114, 2146], [2180, 2244], [2116, 2244], [770, 2114, 2244], [2180, 2692], [1092, 2116, 2692], [2692]]⟩,⟨[7, 19, 20, 21],802,[[2126, 2146, 2188, 2209], [2124, 2126], [2122, 2126], [2132, 2140], [2124, 2140], [2122, 2132, 2140, 2146], [2188, 2252], [2124, 2252], [1100, 1313, 2209, 2252], [1313, 2146, 2188, 2209, 3148], [2124, 3148], [1100, 3148]]⟩,⟨[2, 16, 22],644,[[1156, 1157], [770, 1157, 1281], [1153, 1157], [1156, 1164], [770, 1092, 1153, 2114, 2321], [1153, 1185], [1156, 1220], [1092, 1220], [1092, 1153, 1220, 1281], [1156, 1668], [1668], [770, 1092, 1153, 1281, 1668, 2114]]⟩,⟨[11, 12, 16, 22],674,[[2322, 2323], [2321, 2323], [786, 1164, 1185, 2186, 2323], [2322, 2330], [2314, 2330], [786, 2186, 2330], [2322, 2386], [2130, 2186, 2314, 2386], [2130, 2386], [2322, 2834], [1185, 2321, 2834], [786, 2834]]⟩,⟨[3, 17, 22],532,[[546, 550, 1057, 1060], [548, 550], [546, 550], [564, 1036, 1060], [548, 564], [564], [1060, 1124], [548, 676], [2058, 2314], [1060, 1572], [548, 1572], [546, 1036, 1572, 2058]]⟩,
⟨[4, 17, 22],84,[[98, 102, 161, 164], [100, 102], [98, 102], [116, 140, 164], [100, 116], [116], [164, 228], [100, 228], [98, 140, 228, 266], [164, 676], [100, 1124], [266, 2314]]⟩,⟨[12, 16, 17, 22],674,[[678, 1185, 1188], [676, 678], [678], [1188, 1196], [676, 1185, 1196, 2314, 2321], [1164, 1196], [1188, 1252], [1124, 1252], [1124, 1252, 2186, 2314], [1188, 1700], [676, 1700], [1164, 1700, 2186]]⟩,⟨[4, 18, 22],84,[[98, 140, 161, 270, 276], [268, 270], [266, 270], [276, 284], [268, 284], [98, 266, 284], [276, 340], [140, 268, 340], [340], [276, 788], [268, 1292], [266, 2314]]⟩,⟨[2, 19, 22],644,[[2306, 2307], [2305, 2307], [1092, 1281, 2114, 2307], [2306, 2314], [2305, 2321], [770, 802], [2306, 2370], [770, 1092, 1281, 2305, 2370], [2114, 2370], [2306, 2818], [770, 1281, 2305, 2818], [770, 2818]]⟩,⟨[4, 19, 22],84,[[290, 291], [289, 291], [140, 161, 266, 291], [290, 298], [98, 140, 161, 289, 298], [266, 298], [290, 354], [98, 161, 289, 354], [98, 354], [290, 802], [289, 1313], [266, 2314]]⟩,⟨[16, 17, 19, 22],676,[[1188, 1189], [802, 1189, 1313], [1185, 1189], [1188, 1196], [802, 1196, 1313, 2314, 2321], [1164, 1196], [1188, 1252], [1124, 1252], [1124, 1185, 1252, 1313], [1188, 1700], [1700], [802, 1164, 1700, 2314]]⟩,⟨[3, 20, 22],532,[[546, 1036, 1057, 2062, 2068], [2060, 2062], [2058, 2062], [2068, 2076], [2060, 2076], [546, 2058, 2076], [2068, 2132], [2060, 2188], [2058, 2314], [2068, 2580], [1036, 2060, 2580], [2580]]⟩,⟨[7, 19, 20, 22],802,[[2126, 2132, 2314, 2321], [2124, 2126], [2122, 2126], [2132, 2140], [2124, 2140], [1100, 1313, 2140, 2321], [2188, 2252], [2124, 2252], [2122, 2188, 2252, 2314], [1313, 2132, 2314, 2321, 3148], [2124, 3148], [1100, 3148]]⟩,
⟨[13, 19, 20, 22],660,[[2196, 2197], [2188, 2197, 2314, 2321], [2193, 2197], [2196, 2204], [2188, 2204], [802, 2204, 2314], [2196, 2260], [2132, 2260], [2132, 2193, 2260, 2321], [2196, 2708], [802, 1313, 2188, 2314, 2321, 2708], [2708]]⟩,⟨[2, 21, 22],644,[[2306, 2307], [2305, 2307], [1092, 1281, 2114, 2307], [2306, 2314], [2305, 2321], [2114, 2146], [2306, 2370], [770, 1092, 1281, 2305, 2370], [2114, 2370], [2306, 2818], [770, 1281, 2305, 2818], [770, 2818]]⟩,⟨[3, 21, 22],532,[[2082, 2083], [2081, 2083], [1036, 1057, 2058, 2083], [2082, 2090], [546, 1036, 1057, 2081, 2090], [2058, 2090], [2082, 2146], [2081, 2209], [2058, 2314], [2082, 2594], [546, 1057, 2081, 2594], [546, 2594]]⟩,⟨[9, 18, 21, 22],652,[[782, 788, 2314, 2321], [780, 782], [778, 782], [788, 796], [780, 796], [796, 2209, 2321], [788, 908, 2146, 2209, 2314, 2321], [780, 908], [908], [1292, 1804], [780, 1804], [778, 1292, 1804, 2314]]⟩,⟨[15, 18, 21, 22],788,[[1300, 1301], [1292, 1301, 2314, 2321], [1297, 1301], [1300, 1308], [1292, 1308], [1108, 1308, 2146, 2314], [1300, 1364], [1292, 1364, 2146, 2209, 2314, 2321], [1108, 1364], [1300, 1812], [1812], [1297, 1812, 2321]]⟩,⟨[16, 19, 21, 22],802,[[2338, 2339], [1185, 1313, 2209, 2339], [1164, 1185, 2314, 2339], [2338, 2346], [1185, 1313, 2209, 2314, 2321, 2346], [2314, 2346], [1185, 1441, 2146, 2338], [1313, 1441], [1185, 1441], [2338, 2850], [1185, 2209, 2850], [2850]]⟩,⟨[17, 20, 21, 22],676,[[2146, 2150, 2209, 2212], [2148, 2150], [2146, 2150], [2132, 2164, 2188, 2212], [2148, 2164], [2132, 2164], [2212, 2276], [2148, 2276], [2146, 2188, 2276, 2314], [2212, 2724], [1124, 2148, 2724], [2724]]⟩,⟨[18, 20, 21, 22],788,[[2132, 2146, 2188, 2209, 2318, 2324], [2316, 2318], [2314, 2318], [2324, 2332], [2316, 2332], [2132, 2146, 2314, 2332], [2324, 2388], [2132, 2188, 2316, 2388], [2132, 2388], [2324, 2836], [1292, 2316, 2836], [2836]]⟩,
⟨[19, 20, 21, 22],802,[[2338, 2339], [2337, 2339], [2188, 2209, 2314, 2339], [2338, 2346], [2132, 2146, 2188, 2209, 2337, 2346], [2314, 2346], [2338, 2402], [2146, 2209, 2337, 2402], [2146, 2402], [2338, 2850], [1313, 2337, 2850], [2850]]⟩
]
def t1 : Reason := .force ⟨[1, 9],[10],1120,[(1288, 778)]⟩
def t2 : Reason := .force ⟨[7, 18],[3],1100,[(788, 1356)]⟩
def t3 : Reason := .force ⟨[7, 15, 19],[21],1100,[(2122, 1108), (1297, 1313)]⟩
def t4 : Reason := .force ⟨[10, 13],[3],596,[(660, 724)]⟩
def t5 : Reason := .force ⟨[2, 15],[11],770,[(1092, 1108)]⟩
def t6 : Reason := .force ⟨[9, 17, 19],[5],652,[(676, 1313)]⟩
def t8 : Reason := .force ⟨[9, 19],[2],652,[(802, 810)]⟩
def t9 : Reason := .force ⟨[4, 22],[21],98,[(266, 2314)]⟩
def t10 : Reason := .force ⟨[6, 14],[11],1121,[(2129, 1122)]⟩
def t11 : Reason := .force ⟨[1, 14],[11],784,[(1120, 1122)]⟩
def t12 : Reason := .force ⟨[10, 14],[15],596,[(610, 1122)]⟩
def t13 : Reason := .force ⟨[1, 16],[17],672,[(1164, 1160)]⟩
def t14 : Reason := .force ⟨[6, 19],[22],1121,[(2129, 1313)]⟩
def t15 : Reason := .force ⟨[13, 15, 16],[22],2193,[(1297, 1169)]⟩
def t16 : Reason := .force ⟨[6, 12, 20],[14],1121,[(2129, 2186), (2132, 2188)]⟩
def t17 : Reason := .force ⟨[4, 21],[20],84,[(98, 2146)]⟩
def t19 : Reason := .force ⟨[10, 14],[4],596,[(1122, 1634)]⟩
def t20 : Reason := .force ⟨[8, 11],[6],785,[(786, 2130)]⟩
def t23 : Reason := .force ⟨[1, 5],[6],1120,[(1288, 1289)]⟩
def t25 : Reason := .force ⟨[4, 12],[11],84,[(140, 2186)]⟩
def t27 : Reason := .force ⟨[3, 13],[12],532,[(546, 660)]⟩
def t29 : Reason := .force ⟨[10, 14],[9],610,[(1122, 1290)]⟩
def t31 : Reason := .force ⟨[17, 18, 21],[22],1124,[(1292, 2146)]⟩
def t32 : Reason := .force ⟨[16, 19],[3],1164,[(1313, 1441)]⟩
def t33 : Reason := .force ⟨[7, 19, 21],[9],2122,[(802, 2146)]⟩
def t34 : Reason := .force ⟨[11, 18],[20],786,[(2130, 788)]⟩
def t39 : Reason := .force ⟨[16, 21],[20],1164,[(1185, 2209)]⟩
def t40 : Reason := .force ⟨[1, 7],[20],2128,[(1100, 1096)]⟩
def t41 : Reason := .force ⟨[1, 18],[17],672,[(784, 788)]⟩
def t43 : Reason := .force ⟨[6, 18, 20],[8],2129,[(788, 2132)]⟩
def t44 : Reason := .force ⟨[6, 8, 18],[20],2129,[(785, 788)]⟩
def t45 : Reason := .force ⟨[3, 5],[18],532,[(1289, 1033)]⟩
def t46 : Reason := .force ⟨[2, 13],[15],644,[(1092, 660)]⟩
def t47 : Reason := .force ⟨[7, 17],[9],1100,[(676, 1124)]⟩
def t48 : Reason := .force ⟨[7, 16],[3],1100,[(1164, 1228)]⟩
def t49 : Reason := .force ⟨[4, 7],[21],161,[(2122, 74)]⟩
def t50 : Reason := .force ⟨[4, 8],[10],98,[(161, 673)]⟩
def t51 : Reason := .force ⟨[5, 13],[15],1289,[(2185, 2193)]⟩
def t52 : Reason := .force ⟨[3, 22],[18],532,[(2058, 2314)]⟩
def t53 : Reason := .force ⟨[1, 17],[18],672,[(784, 676)]⟩
def t54 : Reason := .force ⟨[12, 20],[17],674,[(2186, 2188)]⟩
def t55 : Reason := .force ⟨[11, 12, 16],[15],2130,[(2186, 1164)]⟩
def t56 : Reason := .force ⟨[3, 11],[18],532,[(786, 530)]⟩
def t58 : Reason := .force ⟨[10, 12],[3],596,[(674, 738)]⟩
def t59 : Reason := .force ⟨[6, 21],[16],1121,[(2209, 2145)]⟩
def t60 : Reason := .force ⟨[9, 10, 14],[16],652,[(610, 1122)]⟩
def t62 : Reason := .force ⟨[10, 12],[13],596,[(610, 674)]⟩
def t63 : Reason := .force ⟨[10, 18],[3],596,[(788, 852)]⟩
def t64 : Reason := .force ⟨[2, 7],[9],644,[(1092, 1100)]⟩
def t68 : Reason := .force ⟨[4, 14],[15],84,[(98, 1122)]⟩
def t69 : Reason := .force ⟨[8, 19],[15],785,[(1313, 801)]⟩
def t70 : Reason := .force ⟨[11, 20],[18],786,[(2130, 2132)]⟩
def t71 : Reason := .force ⟨[3, 16],[13],532,[(1036, 1164)]⟩
def t73 : Reason := .force ⟨[1, 18],[20],784,[(2128, 788)]⟩
def t74 : Reason := .force ⟨[8, 12, 20],[18],673,[(785, 674), (2186, 2188)]⟩
def t75 : Reason := .force ⟨[12, 19],[16],674,[(802, 1313)]⟩
def t76 : Reason := .force ⟨[5, 13],[9],2185,[(660, 2193)]⟩
def t77 : Reason := .force ⟨[17, 19, 20],[22],1124,[(1313, 2132)]⟩
def t78 : Reason := .force ⟨[5, 18],[8],1289,[(788, 1292)]⟩
def t79 : Reason := .force ⟨[1, 9],[18],784,[(652, 648)]⟩
def t80 : Reason := .force ⟨[3, 17],[21],1036,[(2058, 1124)]⟩
def t81 : Reason := .force ⟨[16, 21],[4],1185,[(2146, 3233)]⟩
def t82 : Reason := .force ⟨[13, 18],[3],660,[(788, 916)]⟩
def t85 : Reason := .force ⟨[2, 18],[20],770,[(2114, 788)]⟩
def t86 : Reason := .force ⟨[9, 22],[4],652,[(2314, 2826)]⟩
def t87 : Reason := .force ⟨[7, 9, 10],[22],2122,[(778, 586)]⟩
def t88 : Reason := .force ⟨[1, 11],[12],672,[(784, 786)]⟩
def t89 : Reason := .force ⟨[10, 11],[18],596,[(786, 594)]⟩
def t91 : Reason := .force ⟨[6, 13],[16],1121,[(2129, 2193)]⟩
def t92 : Reason := .force ⟨[8, 22],[9],785,[(2314, 2321)]⟩
def t93 : Reason := .force ⟨[17, 19, 22],[20],676,[(802, 2314)]⟩
def t94 : Reason := .force ⟨[12, 18, 20],[14],2186,[(1292, 2188)]⟩
def t95 : Reason := .force ⟨[12, 17],[20],674,[(2186, 676)]⟩
def t96 : Reason := .force ⟨[1, 13],[18],784,[(660, 656)]⟩
def t98 : Reason := .force ⟨[12, 19],[3],674,[(802, 930)]⟩
def t99 : Reason := .force ⟨[9, 22],[20],652,[(778, 2314)]⟩
def t101 : Reason := .force ⟨[8, 16],[4],673,[(1164, 1697)]⟩
def t102 : Reason := .force ⟨[8, 18, 20],[6],785,[(788, 2132)]⟩
def t104 : Reason := .force ⟨[12, 21],[1],674,[(2209, 2211)]⟩
def t105 : Reason := .force ⟨[4, 8],[9],140,[(161, 673)]⟩
def t106 : Reason := .force ⟨[10, 18, 19],[6],596,[(788, 1313)]⟩
def t107 : Reason := .force ⟨[3, 21],[20],532,[(546, 2146)]⟩
def t108 : Reason := .force ⟨[1, 10],[17],672,[(596, 592)]⟩
def t109 : Reason := .force ⟨[4, 19],[18],84,[(98, 802)]⟩
def t110 : Reason := .force ⟨[8, 21],[22],673,[(785, 2209)]⟩
def t111 : Reason := .force ⟨[7, 20],[11],2122,[(2132, 2124)]⟩
def t112 : Reason := .force ⟨[6, 11],[14],1121,[(2129, 2130)]⟩
def t113 : Reason := .force ⟨[1, 11],[14],784,[(1120, 786)]⟩
def t115 : Reason := .force ⟨[13, 20],[10],660,[(2132, 2196)]⟩
def t116 : Reason := .force ⟨[5, 8, 9],[18],1289,[(652, 649)]⟩
def t117 : Reason := .force ⟨[14, 19],[10],1122,[(802, 1314)]⟩
def t119 : Reason := .force ⟨[16, 17],[3],1164,[(1124, 1252)]⟩
def t120 : Reason := .force ⟨[10, 15],[14],596,[(610, 1108)]⟩
def t121 : Reason := .force ⟨[18, 19, 21],[20],788,[(802, 2146)]⟩
def t125 : Reason := .force ⟨[12, 14, 20],[18],2186,[(1290, 2188)]⟩
def t126 : Reason := .force ⟨[6, 19],[3],1121,[(1313, 1377)]⟩
def t128 : Reason := .force ⟨[10, 21],[20],596,[(610, 2146)]⟩
def t129 : Reason := .force ⟨[7, 12],[10],2122,[(674, 2186)]⟩
def t130 : Reason := .force ⟨[18, 20, 22],[14],1292,[(2314, 2316)]⟩
def t131 : Reason := .force ⟨[1, 8],[6],672,[(1120, 673)]⟩
def t132 : Reason := .force ⟨[8, 17],[18],673,[(785, 676)]⟩
def t133 : Reason := .force ⟨[7, 14],[21],2122,[(1122, 1098)]⟩
def t135 : Reason := .force ⟨[1, 21],[22],1120,[(1288, 2146)]⟩
def t136 : Reason := .force ⟨[10, 17],[3],596,[(676, 740)]⟩
def t137 : Reason := .force ⟨[15, 18],[1],1297,[(788, 1301)]⟩
def t138 : Reason := .force ⟨[13, 18],[22],660,[(2193, 788)]⟩
def t139 : Reason := .force ⟨[11, 19],[21],786,[(2130, 802)]⟩
def t140 : Reason := .force ⟨[3, 18],[19],532,[(546, 788)]⟩
def t141 : Reason := .force ⟨[2, 22],[18],1092,[(2114, 2314)]⟩
def t143 : Reason := .force ⟨[6, 8, 10],[21],2129,[(673, 593)]⟩
def t144 : Reason := .force ⟨[6, 15],[17],1121,[(1108, 1105)]⟩
def t145 : Reason := .force ⟨[9, 13, 19],[21],652,[(778, 660), (2193, 802)]⟩
def t146 : Reason := .force ⟨[9, 19],[17],652,[(778, 802)]⟩
def t147 : Reason := .force ⟨[5, 19],[2],1289,[(1313, 1321)]⟩
def t149 : Reason := .force ⟨[11, 12, 13],[20],2130,[(660, 658)]⟩
def t153 : Reason := .force ⟨[12, 14, 16],[21],2186,[(1122, 1162)]⟩
def t154 : Reason := .force ⟨[11, 22],[9],786,[(2314, 2322)]⟩
def t155 : Reason := .force ⟨[9, 12],[17],652,[(674, 650)]⟩
def t156 : Reason := .force ⟨[2, 20],[22],1092,[(1281, 2132)]⟩
def t157 : Reason := .force ⟨[13, 17],[15],660,[(676, 1124)]⟩
def t158 : Reason := .force ⟨[7, 11],[2],2122,[(786, 2138)]⟩
def t159 : Reason := .force ⟨[12, 22],[19],674,[(2186, 2314)]⟩
def t160 : Reason := .force ⟨[1, 20],[18],784,[(2128, 2132)]⟩
def t163 : Reason := .force ⟨[4, 18],[11],266,[(788, 268)]⟩
def t164 : Reason := .force ⟨[4, 15],[14],84,[(98, 1108)]⟩
def t165 : Reason := .force ⟨[19, 21, 22],[14],1313,[(2314, 2337)]⟩
def t166 : Reason := .force ⟨[8, 21],[10],673,[(2146, 2209)]⟩
def t168 : Reason := .force ⟨[14, 18],[17],1122,[(1290, 1292)]⟩
def t169 : Reason := .force ⟨[10, 19],[18],596,[(610, 802)]⟩
def t171 : Reason := .force ⟨[13, 15, 19],[21],2193,[(1297, 1313)]⟩
def t172 : Reason := .force ⟨[14, 21],[22],1122,[(1290, 2146)]⟩
def t173 : Reason := .force ⟨[11, 14, 16],[13],786,[(1290, 1164)]⟩
def t174 : Reason := .force ⟨[11, 14, 15],[18],786,[(1108, 1106)]⟩
def t175 : Reason := .force ⟨[7, 11],[9],2122,[(786, 2130)]⟩
def t176 : Reason := .force ⟨[5, 20],[18],1289,[(2185, 2188)]⟩
def t177 : Reason := .force ⟨[8, 17],[1],673,[(676, 677)]⟩
def t179 : Reason := .force ⟨[15, 19],[17],1108,[(1297, 1313)]⟩
def t180 : Reason := .force ⟨[3, 19],[18],532,[(546, 802)]⟩
def t181 : Reason := .force ⟨[10, 15],[4],596,[(1108, 1620)]⟩
def t183 : Reason := .force ⟨[13, 17],[21],660,[(2193, 676)]⟩
def t185 : Reason := .force ⟨[9, 18],[16],652,[(1292, 780)]⟩
def t186 : Reason := .force ⟨[14, 21],[4],1122,[(2146, 3170)]⟩
def t187 : Reason := .force ⟨[2, 21],[17],644,[(2114, 2146)]⟩
def t189 : Reason := .force ⟨[7, 21],[17],1100,[(2122, 2146)]⟩
def t190 : Reason := .force ⟨[16, 18],[19],1164,[(1185, 1292)]⟩
def t191 : Reason := .force ⟨[13, 22],[12],2193,[(2314, 2321)]⟩
def t192 : Reason := .force ⟨[9, 18],[14],778,[(1292, 780)]⟩
def t194 : Reason := .force ⟨[6, 19],[10],1121,[(802, 1313)]⟩
def t195 : Reason := .force ⟨[10, 19],[3],596,[(802, 866)]⟩
def t196 : Reason := .force ⟨[8, 22],[21],673,[(785, 2321)]⟩
def t197 : Reason := .force ⟨[15, 22],[4],1297,[(2314, 3345)]⟩
def t199 : Reason := .force ⟨[2, 7],[5],1092,[(1281, 1100)]⟩
def t200 : Reason := .force ⟨[6, 17],[8],1121,[(676, 1124)]⟩
def t201 : Reason := .force ⟨[9, 13, 15],[7],652,[(660, 1108)]⟩
def t203 : Reason := .force ⟨[5, 18],[20],1289,[(2185, 1292)]⟩
def t204 : Reason := .force ⟨[9, 11],[13],652,[(778, 786)]⟩
def t205 : Reason := .force ⟨[2, 21],[19],770,[(2114, 2146)]⟩
def t207 : Reason := .force ⟨[10, 12, 13],[6],610,[(674, 2193)]⟩
def t208 : Reason := .force ⟨[4, 9],[10],84,[(140, 652)]⟩
def t209 : Reason := .force ⟨[10, 13],[12],596,[(610, 660)]⟩
def t210 : Reason := .force ⟨[2, 19],[17],644,[(770, 802)]⟩
def t211 : Reason := .force ⟨[2, 12],[19],770,[(674, 642)]⟩
def t212 : Reason := .force ⟨[9, 11],[7],778,[(786, 2130)]⟩
def t213 : Reason := .force ⟨[2, 19],[21],770,[(2114, 802)]⟩
def t215 : Reason := .force ⟨[5, 16],[19],1289,[(1185, 1161)]⟩
def t216 : Reason := .force ⟨[14, 18, 20],[12],1290,[(1292, 2188)]⟩
def t218 : Reason := .force ⟨[13, 20],[6],2193,[(2132, 2196)]⟩
def t219 : Reason := .force ⟨[5, 19],[9],1289,[(802, 1313)]⟩
def t220 : Reason := .force ⟨[3, 20],[15],1036,[(2132, 2060)]⟩
def t221 : Reason := .force ⟨[11, 19],[15],786,[(802, 1313)]⟩
def t222 : Reason := .force ⟨[6, 14],[1],1121,[(1122, 1123)]⟩
def t225 : Reason := .force ⟨[15, 18],[10],1108,[(788, 1300)]⟩
def t227 : Reason := .force ⟨[8, 14, 18],[12],673,[(785, 1290), (788, 1292)]⟩
def t228 : Reason := .force ⟨[4, 17],[19],140,[(266, 676)]⟩
def t229 : Reason := .force ⟨[6, 20],[1],1121,[(2132, 2133)]⟩
def t231 : Reason := .force ⟨[15, 20],[22],1108,[(1297, 2132)]⟩
def t232 : Reason := .force ⟨[4, 12],[19],266,[(674, 138)]⟩
def t234 : Reason := .force ⟨[16, 20],[15],1164,[(2132, 2188)]⟩
def t236 : Reason := .force ⟨[6, 11],[8],2129,[(786, 2130)]⟩
def t238 : Reason := .force ⟨[6, 22],[3],2129,[(2314, 2385)]⟩
def t241 : Reason := .force ⟨[8, 12, 18],[20],673,[(785, 674), (2186, 788)]⟩
def t242 : Reason := .force ⟨[6, 15],[19],1121,[(1297, 1105)]⟩
def t243 : Reason := .force ⟨[9, 17],[2],652,[(676, 684)]⟩
def t244 : Reason := .force ⟨[1, 13],[20],2128,[(660, 656)]⟩
def t246 : Reason := .force ⟨[8, 11],[12],673,[(785, 786)]⟩
def t247 : Reason := .force ⟨[16, 18],[3],1164,[(1292, 1420)]⟩
def t250 : Reason := .force ⟨[8, 16],[9],673,[(1164, 1185)]⟩
def t251 : Reason := .force ⟨[6, 17],[1],1121,[(676, 1125)]⟩
def t252 : Reason := .force ⟨[5, 14],[12],1289,[(2185, 1290)]⟩
def t253 : Reason := .force ⟨[3, 6],[10],546,[(1057, 1121)]⟩
def t254 : Reason := .force ⟨[7, 12],[3],2122,[(674, 2250)]⟩
def t255 : Reason := .force ⟨[6, 13],[3],1121,[(2193, 2257)]⟩
def t256 : Reason := .force ⟨[12, 14, 15],[13],674,[(1122, 1108)]⟩
def t257 : Reason := .force ⟨[1, 6],[8],672,[(1120, 1121)]⟩
def t258 : Reason := .force ⟨[12, 20],[1],674,[(2188, 2190)]⟩
def t259 : Reason := .force ⟨[13, 19, 21],[15],2193,[(1313, 2209)]⟩
def t261 : Reason := .force ⟨[2, 6],[19],770,[(1121, 1089)]⟩
def t262 : Reason := .force ⟨[8, 15],[10],785,[(1108, 1297)]⟩
def t263 : Reason := .force ⟨[8, 17],[6],673,[(676, 1124)]⟩
def t264 : Reason := .force ⟨[19, 21, 22],[16],1313,[(2209, 2337)]⟩
def t266 : Reason := .force ⟨[7, 20],[15],1100,[(2132, 2124)]⟩
def t269 : Reason := .force ⟨[2, 6],[10],770,[(1281, 1121)]⟩
def t270 : Reason := .force ⟨[9, 14],[4],778,[(1122, 1802)]⟩
def t271 : Reason := .force ⟨[8, 12],[11],673,[(785, 674)]⟩
def t272 : Reason := .force ⟨[5, 20],[6],2185,[(2132, 2188)]⟩
def t273 : Reason := .force ⟨[10, 20, 21],[8],596,[(2132, 2209)]⟩
def t274 : Reason := .force ⟨[2, 17],[21],644,[(2114, 676)]⟩
def t275 : Reason := .force ⟨[7, 16],[12],1100,[(2122, 1164)]⟩
def t276 : Reason := .force ⟨[11, 13, 16],[14],786,[(660, 1164)]⟩
def t277 : Reason := .force ⟨[15, 22],[20],1108,[(1297, 2321)]⟩
def t279 : Reason := .force ⟨[5, 6, 7],[20],2185,[(1100, 1097)]⟩
def t280 : Reason := .force ⟨[12, 21],[10],674,[(2146, 2210)]⟩
def t281 : Reason := .force ⟨[6, 21],[11],2129,[(2146, 2145)]⟩
def t282 : Reason := .force ⟨[3, 14],[21],2058,[(1122, 1034)]⟩
def t285 : Reason := .force ⟨[8, 21],[4],673,[(2146, 2721)]⟩
def t286 : Reason := .force ⟨[6, 11],[1],2129,[(786, 2131)]⟩
def t287 : Reason := .force ⟨[7, 22],[3],1100,[(2314, 2378)]⟩
def t288 : Reason := .force ⟨[3, 7],[6],1036,[(1057, 1100)]⟩
def t289 : Reason := .force ⟨[2, 13],[11],644,[(770, 660)]⟩
def t293 : Reason := .force ⟨[9, 15, 19],[13],652,[(778, 1297), (802, 1313)]⟩
def t294 : Reason := .force ⟨[8, 15],[16],673,[(785, 1297)]⟩
def t295 : Reason := .force ⟨[3, 7],[10],532,[(1036, 1100)]⟩
def t296 : Reason := .force ⟨[15, 17],[13],1108,[(676, 1124)]⟩
def t297 : Reason := .force ⟨[6, 8, 14],[12],1121,[(673, 1122)]⟩
def t298 : Reason := .force ⟨[18, 19, 20],[21],788,[(802, 2132)]⟩
def t300 : Reason := .force ⟨[15, 17],[2],1108,[(1124, 1140)]⟩
def t301 : Reason := .force ⟨[1, 5],[8],672,[(1288, 1289)]⟩
def t302 : Reason := .force ⟨[5, 12],[1],1289,[(2186, 2187)]⟩
def t303 : Reason := .force ⟨[3, 8],[19],546,[(785, 529)]⟩
def t305 : Reason := .force ⟨[5, 18],[1],1289,[(1292, 1293)]⟩
def t306 : Reason := .force ⟨[16, 20],[21],1164,[(1185, 2188)]⟩
def t308 : Reason := .force ⟨[8, 19],[12],673,[(802, 801)]⟩
def t310 : Reason := .force ⟨[6, 21],[14],1121,[(2146, 2145)]⟩
def t311 : Reason := .force ⟨[2, 11],[13],644,[(770, 786)]⟩
def t313 : Reason := .force ⟨[2, 16],[21],2114,[(1185, 1153)]⟩
def t314 : Reason := .force ⟨[5, 15],[2],1289,[(1297, 1305)]⟩
def t315 : Reason := .force ⟨[17, 21, 22],[18],1124,[(2146, 2314)]⟩
def t316 : Reason := .force ⟨[1, 15],[18],784,[(1108, 1104)]⟩
def t317 : Reason := .force ⟨[8, 12, 14],[6],673,[(674, 1122)]⟩
def t320 : Reason := .force ⟨[4, 16],[15],84,[(140, 1164)]⟩
def t324 : Reason := .force ⟨[11, 22],[3],2130,[(2314, 2386)]⟩
def t325 : Reason := .force ⟨[4, 18],[19],84,[(98, 788)]⟩
def t326 : Reason := .force ⟨[6, 14, 18],[20],1121,[(2129, 1122), (1290, 1292)]⟩
def t327 : Reason := .force ⟨[5, 22],[1],1289,[(2314, 2315)]⟩
def t330 : Reason := .force ⟨[2, 22],[13],644,[(2321, 2305)]⟩
def t331 : Reason := .force ⟨[6, 16],[7],1121,[(1164, 1185)]⟩
def t332 : Reason := .force ⟨[4, 14],[16],98,[(140, 1122)]⟩
def t333 : Reason := .force ⟨[1, 22],[21],1120,[(1288, 2314)]⟩
def t334 : Reason := .force ⟨[9, 17],[7],652,[(676, 1124)]⟩
def t336 : Reason := .force ⟨[3, 5],[19],546,[(1289, 1033)]⟩
def t338 : Reason := .force ⟨[12, 13, 14],[15],674,[(660, 1122)]⟩
def t339 : Reason := .force ⟨[10, 21],[4],596,[(2146, 2658)]⟩
def t341 : Reason := .force ⟨[14, 22],[21],1122,[(1290, 2314)]⟩
def t343 : Reason := .force ⟨[6, 17],[20],1121,[(2129, 1124)]⟩
def t344 : Reason := .force ⟨[3, 10],[6],532,[(1057, 596)]⟩
def t346 : Reason := .force ⟨[3, 22],[19],546,[(2058, 2314)]⟩
def t347 : Reason := .force ⟨[7, 13, 21],[15],1100,[(2122, 2193), (2146, 2209)]⟩
def t348 : Reason := .force ⟨[14, 17],[12],1122,[(676, 1124)]⟩
def t349 : Reason := .force ⟨[5, 16],[18],1289,[(1164, 1161)]⟩
def t350 : Reason := .force ⟨[10, 20],[21],596,[(610, 2132)]⟩
def t351 : Reason := .force ⟨[7, 17],[2],1100,[(676, 1132)]⟩
def t352 : Reason := .force ⟨[9, 16],[14],652,[(778, 1164)]⟩
def t354 : Reason := .force ⟨[4, 21],[22],98,[(266, 2146)]⟩
def t355 : Reason := .force ⟨[1, 14],[12],672,[(1120, 1122)]⟩
def t359 : Reason := .force ⟨[4, 18],[14],266,[(1292, 268)]⟩
def t362 : Reason := .force ⟨[7, 9, 19],[21],2122,[(778, 802)]⟩
def t363 : Reason := .force ⟨[3, 20],[11],2058,[(2132, 2060)]⟩
def t364 : Reason := .force ⟨[4, 22],[20],84,[(266, 2314)]⟩
def t366 : Reason := .force ⟨[10, 18],[19],596,[(610, 788)]⟩
def t367 : Reason := .force ⟨[13, 21],[2],660,[(2209, 2225)]⟩
def t368 : Reason := .force ⟨[18, 20, 21],[19],788,[(2132, 2146)]⟩
def t369 : Reason := .force ⟨[6, 8, 12],[14],1121,[(673, 674)]⟩
def t370 : Reason := .force ⟨[2, 11],[15],770,[(1092, 786)]⟩
def t371 : Reason := .force ⟨[8, 15],[4],785,[(1108, 1809)]⟩
def t373 : Reason := .force ⟨[13, 22],[3],2193,[(2314, 2449)]⟩
def t375 : Reason := .force ⟨[2, 15],[13],644,[(1092, 1108)]⟩
def t376 : Reason := .force ⟨[9, 13, 21],[19],652,[(778, 660), (2193, 2209)]⟩
def t377 : Reason := .force ⟨[16, 18],[13],1164,[(788, 1292)]⟩
def t379 : Reason := .force ⟨[7, 12],[16],1100,[(2122, 2186)]⟩
def t380 : Reason := .force ⟨[18, 20, 22],[16],1292,[(2188, 2316)]⟩
def t381 : Reason := .force ⟨[17, 20, 22],[19],676,[(2188, 2314)]⟩
def t382 : Reason := .force ⟨[5, 21],[2],1289,[(2209, 2217)]⟩
def t383 : Reason := .force ⟨[3, 6],[7],1036,[(1057, 1121)]⟩
def t387 : Reason := .force ⟨[2, 8],[19],770,[(673, 641)]⟩
def t388 : Reason := .force ⟨[8, 12],[1],673,[(674, 675)]⟩
def t389 : Reason := .force ⟨[17, 18, 19],[16],676,[(1292, 804)]⟩
def t390 : Reason := .force ⟨[14, 21],[16],1122,[(2146, 2209)]⟩
def t391 : Reason := .force ⟨[17, 20, 21],[16],1124,[(2188, 2148)]⟩
def t392 : Reason := .force ⟨[11, 18],[1],786,[(788, 790)]⟩
def t394 : Reason := .force ⟨[15, 17],[19],1108,[(1297, 1124)]⟩
def t395 : Reason := .force ⟨[9, 12],[19],778,[(674, 650)]⟩
def t397 : Reason := .force ⟨[11, 21],[2],786,[(2146, 2162)]⟩
def t400 : Reason := .force ⟨[5, 15],[13],1289,[(2185, 1297)]⟩
def t401 : Reason := .force ⟨[16, 17],[2],1164,[(676, 1196)]⟩
def t404 : Reason := .force ⟨[2, 22],[15],1092,[(2321, 2305)]⟩
def t405 : Reason := .force ⟨[3, 9],[22],2058,[(778, 522)]⟩
def t407 : Reason := .force ⟨[1, 17],[20],672,[(2128, 676)]⟩
def t409 : Reason := .force ⟨[7, 9, 21],[19],2122,[(778, 2146)]⟩
def t410 : Reason := .force ⟨[9, 20],[10],652,[(2132, 2188)]⟩
def t411 : Reason := .force ⟨[4, 5],[18],140,[(1289, 137)]⟩
def t412 : Reason := .force ⟨[6, 14, 20],[18],1121,[(2129, 1122), (1290, 2132)]⟩
def t414 : Reason := .force ⟨[19, 21, 22],[12],2209,[(2314, 2337)]⟩
def t415 : Reason := .force ⟨[3, 16],[12],546,[(1036, 1164)]⟩
def t416 : Reason := .force ⟨[5, 12],[14],1289,[(2185, 2186)]⟩
def t417 : Reason := .force ⟨[8, 18],[1],673,[(788, 789)]⟩
def t418 : Reason := .force ⟨[13, 21],[17],660,[(2193, 2209)]⟩
def t420 : Reason := .force ⟨[3, 13],[16],532,[(1036, 660)]⟩
def t421 : Reason := .force ⟨[3, 21],[16],1057,[(2209, 2081)]⟩
def t422 : Reason := .force ⟨[6, 16],[13],1121,[(2129, 1185)]⟩
def t423 : Reason := .force ⟨[4, 17],[12],98,[(676, 100)]⟩
def t424 : Reason := .force ⟨[10, 18],[7],596,[(788, 1292)]⟩
def t425 : Reason := .force ⟨[7, 18],[22],1100,[(2122, 1292)]⟩
def t427 : Reason := .force ⟨[3, 20],[21],532,[(546, 2132)]⟩
def t428 : Reason := .force ⟨[4, 9],[8],140,[(161, 652)]⟩
def t429 : Reason := .force ⟨[2, 5],[7],1092,[(1281, 1289)]⟩
def t431 : Reason := .force ⟨[4, 15],[16],84,[(140, 1108)]⟩
def t432 : Reason := .force ⟨[2, 9],[5],644,[(1281, 652)]⟩
def t434 : Reason := .force ⟨[2, 12],[16],770,[(1281, 674)]⟩
def t435 : Reason := .force ⟨[6, 8, 20],[18],2129,[(785, 2132)]⟩
def t437 : Reason := .force ⟨[7, 17],[21],1100,[(2122, 1124)]⟩
def t438 : Reason := .force ⟨[5, 22],[15],1289,[(2321, 2313)]⟩
def t440 : Reason := .force ⟨[1, 19],[22],1120,[(2128, 1313)]⟩
def t442 : Reason := .force ⟨[1, 13],[16],784,[(1288, 660)]⟩
def t443 : Reason := .force ⟨[13, 15, 21],[19],2193,[(1297, 2209)]⟩
def t444 : Reason := .force ⟨[15, 19],[2],1108,[(1313, 1329)]⟩
def t445 : Reason := .force ⟨[1, 16],[20],2128,[(1164, 1160)]⟩
def t446 : Reason := .force ⟨[5, 19],[21],1289,[(2185, 1313)]⟩
def t448 : Reason := .force ⟨[7, 13, 15],[9],1100,[(660, 1108)]⟩
def t449 : Reason := .force ⟨[13, 22],[18],660,[(2193, 2321)]⟩
def t453 : Reason := .force ⟨[8, 18],[17],673,[(785, 788)]⟩
def t454 : Reason := .force ⟨[8, 16],[15],673,[(785, 1185)]⟩
def t455 : Reason := .force ⟨[13, 20],[1],2193,[(2132, 2197)]⟩
def t458 : Reason := .force ⟨[3, 12],[13],532,[(546, 674)]⟩
def t459 : Reason := .force ⟨[3, 19],[22],546,[(2058, 802)]⟩
def t460 : Reason := .force ⟨[6, 12, 14],[8],1121,[(674, 1122)]⟩
def t462 : Reason := .force ⟨[14, 18],[1],1122,[(1292, 1294)]⟩
def t464 : Reason := .force ⟨[3, 15],[22],2058,[(1297, 1041)]⟩
def t465 : Reason := .force ⟨[1, 15],[16],672,[(784, 1297)]⟩
def t466 : Reason := .force ⟨[1, 12],[11],672,[(784, 674)]⟩
def t467 : Reason := .force ⟨[4, 20],[22],84,[(266, 2132)]⟩
def t469 : Reason := .force ⟨[4, 6],[21],98,[(2129, 81)]⟩
def t470 : Reason := .force ⟨[7, 22],[18],1100,[(2122, 2314)]⟩
def t472 : Reason := .force ⟨[4, 19],[16],161,[(1313, 289)]⟩
def t474 : Reason := .force ⟨[2, 18],[22],1092,[(2114, 1292)]⟩
def t476 : Reason := .force ⟨[10, 14, 15],[8],610,[(1122, 1297)]⟩
def t478 : Reason := .force ⟨[5, 14],[6],1289,[(1122, 1290)]⟩
def t479 : Reason := .force ⟨[7, 9, 15],[13],1100,[(652, 1108)]⟩
def t480 : Reason := .force ⟨[12, 13, 15],[14],674,[(660, 1108)]⟩
def t481 : Reason := .force ⟨[17, 18, 22],[21],1124,[(1292, 2314)]⟩
def t483 : Reason := .force ⟨[1, 12],[14],672,[(1120, 674)]⟩
def t484 : Reason := .force ⟨[2, 14],[19],770,[(1122, 1090)]⟩
def t485 : Reason := .force ⟨[8, 13],[21],673,[(2193, 657)]⟩
def t486 : Reason := .force ⟨[9, 16],[4],652,[(1164, 1676)]⟩
def t489 : Reason := .force ⟨[9, 14],[10],778,[(1122, 1290)]⟩
def t490 : Reason := .force ⟨[1, 21],[12],672,[(2146, 2144)]⟩
def t492 : Reason := .force ⟨[5, 14],[1],1289,[(1290, 1291)]⟩
def t493 : Reason := .force ⟨[9, 17],[19],652,[(778, 676)]⟩
def t494 : Reason := .force ⟨[5, 13],[2],1289,[(2193, 2201)]⟩
def t495 : Reason := .force ⟨[12, 17, 18],[11],674,[(676, 788)]⟩
def t496 : Reason := .force ⟨[7, 11],[15],1100,[(2122, 2130)]⟩
def t497 : Reason := .force ⟨[16, 21],[14],1185,[(2146, 2209)]⟩
def t498 : Reason := .force ⟨[12, 14, 18],[20],2186,[(1290, 1292)]⟩
def t499 : Reason := .force ⟨[2, 10],[21],2114,[(610, 578)]⟩
def t501 : Reason := .force ⟨[9, 11],[2],652,[(786, 794)]⟩
def t502 : Reason := .force ⟨[6, 22],[19],1121,[(2129, 2321)]⟩
def t503 : Reason := .force ⟨[7, 9, 13],[15],1100,[(652, 660)]⟩
def t504 : Reason := .force ⟨[10, 17],[15],596,[(1124, 612)]⟩
def t505 : Reason := .force ⟨[3, 18],[22],532,[(2058, 788)]⟩
def t506 : Reason := .force ⟨[6, 16],[3],1121,[(1164, 1249)]⟩
def t507 : Reason := .force ⟨[9, 19, 21],[7],778,[(802, 2146)]⟩
def t508 : Reason := .force ⟨[3, 12],[16],546,[(1036, 674)]⟩
def t509 : Reason := .force ⟨[7, 18],[10],1100,[(788, 1292)]⟩
def t510 : Reason := .force ⟨[14, 19],[1],1122,[(1313, 1315)]⟩
def t511 : Reason := .force ⟨[16, 19],[18],1164,[(1185, 1313)]⟩
def t513 : Reason := .force ⟨[6, 17, 20],[5],1121,[(1124, 2188)]⟩
def t514 : Reason := .force ⟨[7, 15],[2],1100,[(1108, 1116)]⟩
def t515 : Reason := .force ⟨[6, 20],[17],1121,[(2129, 2132)]⟩
def t517 : Reason := .force ⟨[4, 11],[18],84,[(786, 82)]⟩
def t519 : Reason := .force ⟨[3, 11],[19],546,[(786, 530)]⟩
def t520 : Reason := .force ⟨[9, 20],[4],652,[(2132, 2700)]⟩
def t521 : Reason := .force ⟨[12, 17],[14],674,[(676, 1124)]⟩
def t522 : Reason := .force ⟨[12, 22],[3],674,[(2314, 2442)]⟩
def t523 : Reason := .force ⟨[8, 11],[1],673,[(786, 787)]⟩
def t524 : Reason := .force ⟨[6, 11, 14],[5],2129,[(2130, 1290)]⟩
def t526 : Reason := .force ⟨[14, 17],[18],1122,[(1290, 1124)]⟩
def t527 : Reason := .force ⟨[7, 15],[11],1100,[(2122, 1108)]⟩
def t529 : Reason := .force ⟨[1, 10],[20],2128,[(596, 592)]⟩
def t530 : Reason := .force ⟨[1, 21],[19],784,[(2128, 2146)]⟩
def t531 : Reason := .force ⟨[7, 15, 21],[19],1100,[(2122, 1108), (1297, 2146)]⟩
def t532 : Reason := .force ⟨[4, 5],[19],161,[(1289, 137)]⟩
def t533 : Reason := .force ⟨[11, 20],[12],2130,[(2132, 2188)]⟩
def t534 : Reason := .force ⟨[15, 22],[14],1297,[(2314, 2321)]⟩
def t537 : Reason := .force ⟨[11, 21],[19],786,[(2130, 2146)]⟩
def t538 : Reason := .force ⟨[4, 16],[14],98,[(140, 1164)]⟩
def t540 : Reason := .force ⟨[12, 17],[1],674,[(676, 678)]⟩
def t541 : Reason := .force ⟨[4, 13],[21],161,[(2193, 145)]⟩
def t542 : Reason := .force ⟨[1, 6],[5],1120,[(1288, 1121)]⟩
def t546 : Reason := .force ⟨[9, 13],[2],652,[(660, 668)]⟩
def t548 : Reason := .force ⟨[15, 19, 21],[13],1297,[(1313, 2209)]⟩
def t549 : Reason := .force ⟨[5, 21],[19],1289,[(2185, 2209)]⟩
def t551 : Reason := .force ⟨[2, 5],[9],644,[(1281, 1289)]⟩
def t552 : Reason := .force ⟨[12, 19],[22],674,[(2186, 802)]⟩
def t555 : Reason := .force ⟨[7, 21],[2],1100,[(2146, 2154)]⟩
def priors : List (List Nat) := [
[1, 2],[1, 5],[3, 5],[5, 6],[7, 8],[5, 11],[6, 11],[10, 11],
[1, 5, 6],[2, 5, 6],[4, 5, 6],[5, 6, 7],[5, 6, 8],[1, 7, 8],[5, 7, 8],[1, 5, 11],
[3, 5, 11],[5, 6, 11],[6, 7, 11],[6, 8, 11],[7, 8, 11],[5, 10, 11],[6, 10, 11],[5, 11, 17],
[6, 11, 17],[10, 11, 17],[1, 5, 6, 8],[2, 5, 6, 8],[5, 6, 7, 8],[6, 7, 8, 9],[5, 6, 7, 11],[5, 6, 8, 11],
[5, 7, 8, 11],[5, 6, 10, 11],[6, 7, 10, 11],[5, 6, 11, 12],[5, 7, 11, 12],[5, 8, 11, 12],[7, 8, 11, 12],[5, 9, 11, 12],
[6, 9, 11, 12],[7, 9, 11, 12],[9, 10, 11, 12],[7, 8, 13, 14],[6, 9, 13, 14],[1, 5, 11, 17],[3, 5, 11, 17],[5, 6, 11, 17],
[6, 7, 11, 17],[6, 8, 11, 17],[7, 8, 11, 17],[5, 10, 11, 17],[6, 10, 11, 17],[5, 6, 12, 17],[5, 10, 16, 17],[1, 2, 5, 6, 8],
[1, 5, 6, 7, 8],[1, 6, 7, 8, 9],[5, 6, 7, 8, 9],[1, 5, 6, 8, 11],[6, 7, 8, 9, 11],[3, 6, 7, 10, 11],[5, 6, 7, 10, 11],[5, 7, 8, 10, 11],
[5, 6, 8, 11, 12],[5, 7, 9, 11, 12],[8, 9, 10, 11, 12],[7, 8, 11, 12, 14],[5, 6, 7, 11, 17],[5, 6, 8, 11, 17],[5, 7, 8, 11, 17],[5, 6, 10, 11, 17],
[6, 7, 10, 11, 17],[5, 6, 11, 12, 17],[5, 10, 11, 16, 17],[1, 5, 6, 7, 8, 9],[5, 6, 7, 8, 9, 10],[5, 6, 7, 8, 9, 11],[3, 5, 6, 7, 10, 11],[1, 5, 6, 8, 11, 12],
[2, 5, 7, 9, 11, 12],[6, 7, 8, 9, 11, 12],[5, 6, 9, 10, 11, 12],[4, 8, 9, 10, 11, 12],[5, 6, 8, 11, 12, 14],[1, 7, 8, 11, 12, 14],[5, 7, 9, 11, 12, 14],[6, 7, 8, 9, 13, 14],
[5, 6, 9, 10, 13, 14],[1, 5, 6, 8, 11, 17],[6, 7, 8, 9, 11, 17],[3, 6, 7, 10, 11, 17],[5, 6, 7, 10, 11, 17],[5, 7, 8, 10, 11, 17],[5, 6, 11, 12, 17, 18],[7, 8, 13, 14, 19, 20],
[1, 2, 5, 6, 7, 8, 9],[1, 5, 6, 8, 11, 12, 14],[1, 5, 7, 9, 11, 12, 14],[6, 7, 8, 9, 11, 12, 14],[5, 6, 7, 8, 9, 11, 17],[3, 5, 6, 7, 10, 11, 17],[1, 2, 5, 6, 8, 11, 12, 14],[1, 5, 6, 7, 8, 11, 12, 14],
[1, 2, 5, 7, 9, 11, 12, 14],[1, 6, 7, 8, 9, 11, 12, 14],[6, 7, 8, 9, 12, 13, 14, 15],[5, 7, 8, 10, 12, 13, 14, 15],[1, 5, 6, 8, 11, 12, 14, 17],[3, 6, 7, 10, 12, 13, 16, 17],[1, 5, 6, 7, 8, 9, 11, 12, 14],[1, 5, 6, 7, 8, 11, 12, 13, 14],
[3, 5, 6, 7, 10, 12, 13, 16, 17],[1, 5, 6, 8, 11, 12, 14, 17, 18],[2, 5, 7, 9, 11, 13, 15, 17, 18],[4, 8, 9, 10, 14, 15, 16, 17, 18],[1, 7, 8, 11, 12, 14, 17, 18, 20],[1, 2, 5, 6, 7, 8, 9, 11, 12, 14],[3, 5, 6, 7, 10, 11, 12, 13, 16, 17],[1, 5, 6, 8, 11, 12, 14, 17, 18, 20],
[1, 5, 7, 9, 11, 12, 14, 17, 18, 20],[1, 2, 5, 6, 8, 11, 12, 14, 17, 18, 20],[1, 5, 6, 7, 8, 11, 12, 14, 17, 18, 20],[1, 2, 5, 7, 9, 11, 12, 14, 17, 18, 20],[1, 6, 7, 8, 9, 11, 12, 14, 17, 18, 20],[1, 2, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15],[1, 5, 6, 7, 8, 9, 11, 12, 14, 17, 18, 20],[1, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 20],
[1, 2, 5, 6, 7, 8, 9, 11, 12, 14, 17, 18, 20],[1, 2, 5, 6, 7, 8, 9, 11, 13, 15, 17, 18, 20],[1, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 19, 20],[1, 2, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 20],[1, 2, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]
]
def page0 : List Block := [
⟨[3, 5],[18, 19],[.collision 5,t336,t45]⟩,⟨[4, 5],[18, 19],[.collision 5,t532,t411]⟩,⟨[2, 6],[10, 19],[.collision 6,t261,t269]⟩,⟨[4, 6],[21],[.collision 6,t469]⟩,⟨[1, 7],[20],[.collision 7,t40,.collision 1]⟩,⟨[4, 7],[21],[.collision 7,t49]⟩,⟨[2, 8],[19],[.collision 8,t387]⟩,⟨[3, 8],[19],[.collision 8,t303]⟩,
⟨[1, 9],[10, 18],[t79,.collision 1,.collision 9,t1]⟩,⟨[3, 9],[22],[t405]⟩,⟨[1, 10],[17, 20],[t529,.collision 1,t108]⟩,⟨[2, 10],[21],[t499,.collision 2]⟩,⟨[3, 11],[18, 19],[.collision 11,t56,t519]⟩,⟨[4, 11],[18],[.collision 11,t517,.collision 4]⟩,⟨[6, 11],[1, 14],[.collision 11,.collision 6,t286,t112]⟩,⟨[7, 11],[2, 15],[.collision 11,t496,.collision 7,t158]⟩,
⟨[8, 11],[1, 12],[.collision 11,.collision 8,t246,t523]⟩,⟨[9, 11],[2, 13],[.collision 11,t501,t204]⟩,⟨[10, 11],[18],[.collision 11,t89,.collision 10]⟩,⟨[1, 12],[11, 14],[.collision 12,t483,t466]⟩,⟨[2, 12],[16, 19],[t211,.collision 12,t434]⟩,⟨[3, 12],[13, 16],[t508,.collision 3,t458]⟩,⟨[4, 12],[11, 19],[t232,.collision 12,t25]⟩,⟨[5, 12],[1, 14],[.collision 5,t302,.collision 12,t416]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify0 : page0.all (justified priors)=true := by decide +kernel
def page24 : List Block := [
⟨[7, 12],[3, 10],[.collision 7,t254,t129]⟩,⟨[9, 12],[17, 19],[t395,.collision 12,t155]⟩,⟨[10, 12],[3, 13],[t58,.collision 10,t62]⟩,⟨[1, 13],[16, 20],[t442,.collision 13,t244]⟩,⟨[2, 13],[11, 15],[t46,.collision 13,t289]⟩,⟨[3, 13],[12, 16],[t420,.collision 3,t27]⟩,⟨[4, 13],[21],[t541,.collision 13]⟩,⟨[5, 13],[2, 15],[.collision 5,t494,t51]⟩,
⟨[6, 13],[3, 16],[.collision 6,t91,t255]⟩,⟨[8, 13],[21],[.collision 8,t485]⟩,⟨[10, 13],[3, 12],[t4,.collision 10,t209]⟩,⟨[2, 14],[19],[t484,.collision 14]⟩,⟨[3, 14],[21],[t282,.collision 14]⟩,⟨[4, 14],[15, 16],[t332,t68,.collision 4]⟩,⟨[5, 14],[1, 12],[.collision 5,t492,.collision 14,t252]⟩,⟨[7, 14],[21],[.collision 7,t133]⟩,
⟨[9, 14],[4, 10],[t270,.collision 9,t489]⟩,⟨[10, 14],[4, 15],[t19,.collision 10,t12]⟩,⟨[1, 15],[16, 18],[t465,t316,.collision 15]⟩,⟨[3, 15],[22],[t464]⟩,⟨[4, 15],[14, 16],[t431,t164,.collision 4]⟩,⟨[5, 15],[2, 13],[.collision 5,t314,t400]⟩,⟨[6, 15],[17, 19],[.collision 6,t242,t144]⟩,⟨[8, 15],[4, 10],[.collision 8,t371,t262]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify24 : page24.all (justified priors)=true := by decide +kernel
def page48 : List Block := [
⟨[10, 15],[4, 14],[t181,.collision 10,t120]⟩,⟨[2, 16],[21],[t313,.collision 2]⟩,⟨[5, 16],[18, 19],[.collision 5,t215,t349]⟩,⟨[6, 16],[3, 7],[.collision 6,t506,t331]⟩,⟨[7, 16],[3, 12],[.collision 7,t48,t275]⟩,⟨[8, 16],[4, 9],[.collision 8,t101,t250]⟩,⟨[9, 16],[4, 14],[t486,.collision 9,t352]⟩,⟨[1, 17],[18, 20],[t407,.collision 1,t53]⟩,
⟨[2, 17],[21],[t274,.collision 2]⟩,⟨[3, 17],[21],[t80,.collision 17]⟩,⟨[4, 17],[12, 19],[t228,.collision 17,t423]⟩,⟨[6, 17],[1, 20],[.collision 6,t343,.collision 17,t251]⟩,⟨[7, 17],[21],[.collision 7,t437]⟩,⟨[8, 17],[18],[.collision 8,t132,.collision 17]⟩,⟨[9, 17],[2, 19],[t493,.collision 17,t243]⟩,⟨[10, 17],[3, 15],[t504,.collision 17,t136]⟩,
⟨[12, 17],[1, 20],[t95,.collision 17,t540]⟩,⟨[13, 17],[21],[t183,.collision 13]⟩,⟨[14, 17],[18],[t526,.collision 17]⟩,⟨[15, 17],[2, 19],[t394,.collision 17,t300]⟩,⟨[16, 17],[2, 3],[t119,.collision 17,t401]⟩,⟨[1, 18],[17, 20],[t73,.collision 1,t41]⟩,⟨[2, 18],[22],[t474]⟩,⟨[3, 18],[22],[t505]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify48 : page48.all (justified priors)=true := by decide +kernel
def page72 : List Block := [
⟨[4, 18],[11, 19],[t325,.collision 18,t163]⟩,⟨[5, 18],[1, 20],[.collision 5,t203,.collision 18,t305]⟩,⟨[7, 18],[22],[.collision 7,t425]⟩,⟨[9, 18],[14, 16],[t185,t192,.collision 9]⟩,⟨[10, 18],[3, 19],[t366,.collision 18,t63]⟩,⟨[11, 18],[1, 20],[.collision 11,t34,t392]⟩,⟨[13, 18],[22],[t138]⟩,⟨[15, 18],[1, 10],[t225,t137]⟩,
⟨[16, 18],[3, 19],[t190,.collision 18,t247]⟩,⟨[1, 19],[22],[t440]⟩,⟨[2, 19],[21],[t213,.collision 2]⟩,⟨[3, 19],[22],[t459]⟩,⟨[4, 19],[16, 18],[t472,t109,.collision 4]⟩,⟨[5, 19],[21],[.collision 5,t446]⟩,⟨[6, 19],[22],[.collision 6,t14]⟩,⟨[8, 19],[12, 15],[.collision 8,t69,t308]⟩,
⟨[10, 19],[3, 18],[t195,.collision 10,t169]⟩,⟨[11, 19],[21],[.collision 11,t139]⟩,⟨[12, 19],[22],[t552]⟩,⟨[14, 19],[1, 10],[t117,t510]⟩,⟨[16, 19],[3, 18],[t32,t511]⟩,⟨[2, 20],[22],[t156]⟩,⟨[3, 20],[21],[t427,.collision 20]⟩,⟨[4, 20],[22],[t467]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify72 : page72.all (justified priors)=true := by decide +kernel
def page96 : List Block := [
⟨[5, 20],[6, 18],[.collision 5,t176,.collision 20,t272]⟩,⟨[7, 20],[11, 15],[.collision 7,t266,t111]⟩,⟨[9, 20],[4, 10],[t520,.collision 9,t410]⟩,⟨[10, 20],[21],[t350,.collision 20]⟩,⟨[11, 20],[12, 18],[.collision 11,t70,t533]⟩,⟨[13, 20],[1, 10],[t115,t455]⟩,⟨[15, 20],[22],[t231]⟩,⟨[16, 20],[21],[t306,.collision 20]⟩,
⟨[1, 21],[22],[t135]⟩,⟨[3, 21],[16, 20],[t421,.collision 3,t107]⟩,⟨[4, 21],[22],[t354]⟩,⟨[5, 21],[2, 19],[.collision 5,t382,t549]⟩,⟨[6, 21],[11, 14, 16],[.collision 6,t59,t281,t310]⟩,⟨[8, 21],[22],[.collision 8,t110]⟩,⟨[10, 21],[4, 20],[t339,.collision 10,t128]⟩,⟨[11, 21],[2, 19],[.collision 11,t537,t397]⟩,
⟨[12, 21],[1, 10],[.collision 12,t104,t280]⟩,⟨[14, 21],[22],[t172]⟩,⟨[16, 21],[4, 20],[t81,t39]⟩,⟨[1, 22],[21],[t333,.collision 1]⟩,⟨[2, 22],[13, 15, 18],[t404,.collision 2,t141,t330]⟩,⟨[5, 22],[1, 15],[.collision 5,t438,t327]⟩,⟨[6, 22],[3, 19],[.collision 6,t502,t238]⟩,⟨[7, 22],[3, 18],[.collision 7,t287,t470]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify96 : page96.all (justified priors)=true := by decide +kernel
def page120 : List Block := [
⟨[8, 22],[21],[.collision 8,t196]⟩,⟨[9, 22],[4, 20],[t86,.collision 9,t99]⟩,⟨[11, 22],[3, 9],[.collision 11,t324,t154]⟩,⟨[12, 22],[3, 19],[t159,.collision 12,t522]⟩,⟨[13, 22],[3, 18],[t373,t449]⟩,⟨[14, 22],[21],[t341,.collision 14]⟩,⟨[15, 22],[4, 20],[t197,t277]⟩,⟨[5, 6, 7],[20],[.collision 5,.collision 7,t279]⟩,
⟨[5, 8, 9],[18],[.collision 5,.collision 8,t116]⟩,⟨[6, 8, 10],[21],[.collision 6,t143]⟩,⟨[7, 9, 10],[22],[.collision 7,t87]⟩,⟨[2, 7, 11],[5, 15],[.collision 11,t370,.collision 7,t199]⟩,⟨[1, 8, 11],[12, 14],[.collision 11,.collision 8,t246,t113]⟩,⟨[6, 8, 12],[14],[.collision 6,.collision 8,t369,.collision 12]⟩,⟨[7, 9, 13],[15],[.collision 7,t503,.collision 9]⟩,⟨[9, 11],[2, 7],[.collision 11,t501,t212,.collision 9]⟩,
⟨[10, 12, 13],[3, 6],[t4,.collision 10,t207]⟩,⟨[11, 12, 13],[20],[.collision 11,t149,.collision 13]⟩,⟨[6, 8, 14],[1, 12],[.collision 6,t222,.collision 14,t297]⟩,⟨[6, 11, 14],[1, 5, 8],[.collision 11,.collision 6,t286,t236,t524]⟩,⟨[6, 12, 14],[1, 8, 11],[.collision 6,t222,.collision 14,t10,t460]⟩,⟨[8, 12, 14],[1, 6, 11],[.collision 8,t388,.collision 12,t271,t317]⟩,⟨[12, 13, 14],[15],[.collision 12,t338,.collision 13,.collision 14]⟩,⟨[2, 5, 15],[11, 13],[.collision 5,t400,t5]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify120 : page120.all (justified priors)=true := by decide +kernel
def page144 : List Block := [
⟨[2, 7, 15],[5, 9, 11, 13],[.collision 7,t64,t199,t375,t5]⟩,⟨[7, 9, 15],[2, 13],[.collision 7,t514,t479]⟩,⟨[7, 11],[2, 9],[.collision 11,t158,t175,.collision 7]⟩,⟨[5, 13, 15],[2, 9],[.collision 5,t314,t76]⟩,⟨[7, 13, 15],[2, 9],[.collision 7,t514,t448]⟩,⟨[9, 13, 15],[2, 7],[t546,.collision 9,t201]⟩,⟨[12, 13, 15],[14],[.collision 12,t480,.collision 13,.collision 15]⟩,⟨[10, 14],[4, 9],[t19,.collision 10,t29]⟩,
⟨[11, 14, 15],[18],[.collision 11,t174,.collision 14]⟩,⟨[12, 14, 15],[13],[.collision 12,t256,.collision 14,.collision 15]⟩,⟨[4, 8, 16],[10, 15],[.collision 8,t454,t50]⟩,⟨[11, 12, 16],[15],[.collision 11,t55,.collision 12,.collision 16]⟩,⟨[11, 13, 16],[14],[.collision 11,t276,.collision 13,.collision 16]⟩,⟨[11, 14, 16],[13],[.collision 11,t173,.collision 14,.collision 16]⟩,⟨[12, 14, 16],[21],[.collision 12,t153]⟩,⟨[1, 16],[17, 20],[t445,.collision 1,t13]⟩,
⟨[13, 15, 16],[22],[t15]⟩,⟨[6, 8, 18],[20],[.collision 6,t44,.collision 18,.collision 8]⟩,⟨[8, 12, 18],[1, 20],[.collision 8,t388,.collision 12,t241]⟩,⟨[6, 14, 18],[1, 20],[.collision 6,t222,.collision 14,t326]⟩,⟨[8, 14, 18],[1, 12, 17],[.collision 8,t417,t453,.collision 18,t227]⟩,⟨[12, 14, 18],[20],[.collision 12,t498,.collision 14,.collision 18]⟩,⟨[7, 9, 19],[21],[.collision 7,t362]⟩,⟨[9, 13, 19],[2, 17, 21],[t8,.collision 9,t146,t145]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify144 : page144.all (justified priors)=true := by decide +kernel
def page168 : List Block := [
⟨[7, 15, 19],[2, 21],[.collision 7,t514,t3]⟩,⟨[9, 15, 19],[2, 13, 17],[t8,.collision 9,t146,t293]⟩,⟨[13, 15, 19],[2, 21],[t444,t171,.collision 13]⟩,⟨[9, 17, 19],[2, 7],[t8,.collision 9,t334]⟩,⟨[15, 17],[2, 13],[t300,.collision 17,t296,.collision 15]⟩,⟨[4, 18, 19],[14, 16],[t472,t359,.collision 4]⟩,⟨[10, 18],[3, 7],[t63,.collision 10,t424]⟩,⟨[16, 18, 19],[3, 13],[t32,.collision 16,t377]⟩,
⟨[17, 18, 19],[16],[t389,.collision 17]⟩,⟨[1, 6, 20],[5, 8, 17, 18],[.collision 6,t515,t160,.collision 1,t257,t542]⟩,⟨[5, 6, 20],[1, 18],[.collision 5,t176,.collision 20,t229]⟩,⟨[6, 8, 20],[1, 17, 18],[.collision 6,t229,t515,.collision 20,t435]⟩,⟨[6, 12, 20],[1, 14, 17],[.collision 6,t229,t515,.collision 20,t16]⟩,⟨[8, 12, 20],[1, 18],[.collision 8,t388,.collision 12,t74]⟩,⟨[11, 12, 20],[1, 18],[.collision 11,t70,t258]⟩,⟨[1, 13, 20],[6, 16, 18],[t442,.collision 13,t96,t218]⟩,
⟨[6, 14, 20],[1, 18],[.collision 6,t222,.collision 14,t412]⟩,⟨[12, 14, 20],[1, 17, 18],[.collision 12,t258,t54,.collision 20,t125]⟩,⟨[1, 17],[18],[t53,.collision 17]⟩,⟨[6, 17, 20],[1, 5, 8],[.collision 6,t229,.collision 20,t200,t513]⟩,⟨[12, 17],[1, 14],[.collision 12,t521,t540]⟩,⟨[6, 18, 20],[1, 8, 17],[.collision 6,t229,t515,.collision 20,t43]⟩,⟨[8, 18, 20],[1, 6, 17],[.collision 8,t417,t453,.collision 18,t102]⟩,⟨[11, 18, 20],[1, 12],[.collision 11,t533,t392]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify168 : page168.all (justified priors)=true := by decide +kernel
def page192 : List Block := [
⟨[12, 18, 20],[1, 14, 17],[.collision 12,t258,t54,.collision 20,t94]⟩,⟨[14, 18, 20],[1, 12, 17],[t462,.collision 14,t168,.collision 18,t216]⟩,⟨[17, 19, 20],[22],[t77]⟩,⟨[18, 19, 20],[21],[t298,.collision 18]⟩,⟨[2, 5, 21],[17, 19],[.collision 5,t549,t187]⟩,⟨[2, 7, 21],[5, 9, 17],[.collision 7,t64,t199,t187]⟩,⟨[7, 9, 21],[2, 17, 19],[.collision 7,t555,t189,t409]⟩,⟨[2, 11, 21],[17, 19],[.collision 11,t537,t187]⟩,
⟨[7, 13, 21],[2, 15, 17],[.collision 7,t555,t189,t347]⟩,⟨[9, 13, 21],[2, 19],[t367,.collision 9,t376]⟩,⟨[7, 15, 21],[2, 11, 19],[.collision 7,t514,t527,t531]⟩,⟨[13, 15, 21],[2, 19],[t367,t443,.collision 13]⟩,⟨[7, 17],[2, 9],[.collision 7,t351,t47]⟩,⟨[13, 17],[15],[t157,.collision 13,.collision 17]⟩,⟨[17, 18, 21],[22],[t31]⟩,⟨[5, 19],[2, 9],[.collision 5,t147,t219]⟩,
⟨[7, 19, 21],[2, 9, 17],[.collision 7,t555,t189,t33]⟩,⟨[9, 19, 21],[2, 7, 17],[t8,.collision 9,t146,t507]⟩,⟨[11, 19, 21],[2, 15],[.collision 11,t221,t397]⟩,⟨[13, 19, 21],[2, 15, 17],[t367,.collision 13,t418,t259]⟩,⟨[15, 19, 21],[2, 13, 17],[t444,.collision 15,t179,t548]⟩,⟨[18, 19, 21],[20],[t121,.collision 18,.collision 19]⟩,⟨[3, 20, 21],[11, 15, 16],[t421,.collision 3,t220,t363]⟩,⟨[10, 20, 21],[4, 8],[t339,.collision 10,t273]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify192 : page192.all (justified priors)=true := by decide +kernel
def page216 : List Block := [
⟨[16, 21],[4, 14],[t81,.collision 16,t497]⟩,⟨[17, 20, 21],[16],[t391,.collision 17]⟩,⟨[18, 20, 21],[19],[t368,.collision 20]⟩,⟨[3, 6, 22],[18, 19],[.collision 6,t502,t52]⟩,⟨[3, 7, 22],[18, 19],[.collision 7,t470,t346]⟩,⟨[4, 9, 22],[21],[t9,.collision 9]⟩,⟨[2, 18, 22],[15, 20],[t404,.collision 2,t85]⟩,⟨[7, 18],[3, 10],[.collision 7,t2,t509]⟩,
⟨[13, 18, 22],[3, 12],[t82,.collision 13,t191]⟩,⟨[17, 18, 22],[21],[t481,.collision 17]⟩,⟨[6, 19],[3, 10],[.collision 6,t126,t194]⟩,⟨[12, 19],[3, 16],[t75,.collision 12,t98]⟩,⟨[17, 19, 22],[20],[.collision 17,t93,.collision 19]⟩,⟨[4, 20, 22],[21],[t9,.collision 20]⟩,⟨[15, 22],[4, 14],[t197,.collision 15,t534]⟩,⟨[17, 20, 22],[19],[t381,.collision 20]⟩,
⟨[18, 20, 22],[14, 16],[t380,t130,.collision 18]⟩,⟨[1, 21],[12, 19],[t530,.collision 1,t490]⟩,⟨[8, 21],[4, 10],[.collision 8,t285,t166]⟩,⟨[14, 21],[4, 16],[t186,.collision 14,t390]⟩,⟨[17, 21, 22],[18],[.collision 17,t315]⟩,⟨[19, 21, 22],[12, 14, 16],[t264,t165,t414]⟩,⟨[1, 5, 6, 11],[12, 14],[.collision 11,.collision 6,t112,t88,.collision 5]⟩,⟨[2, 5, 7, 11],[13, 15],[.collision 11,.collision 5,.collision 7,t496,t311]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify216 : page216.all (justified priors)=true := by decide +kernel
def page240 : List Block := [
⟨[2, 5, 9, 11],[15],[.collision 11,.collision 5,t370,.collision 9]⟩,⟨[1, 6, 11, 12],[5, 14],[.collision 11,.collision 6,t112,t542,.collision 12]⟩,⟨[2, 5, 11, 13],[7, 15],[.collision 11,.collision 5,t51,.collision 13,t429]⟩,⟨[2, 9, 11, 13],[15],[.collision 11,t370,.collision 9,.collision 13]⟩,⟨[3, 6, 13],[7, 16],[.collision 6,t91,t383]⟩,⟨[3, 7, 12],[6, 16],[.collision 7,t379,t288]⟩,⟨[3, 10, 13],[16],[t420,.collision 3,.collision 10]⟩,⟨[1, 5, 11, 14],[8, 12],[.collision 11,.collision 5,t88,.collision 14,t301]⟩,
⟨[1, 6, 11, 14],[12],[.collision 11,.collision 6,t88,.collision 14]⟩,⟨[2, 7, 9, 15],[13],[.collision 7,t375,.collision 9]⟩,⟨[4, 8, 15],[9, 16],[.collision 8,t294,t105]⟩,⟨[4, 9, 14],[8, 16],[t332,t428,.collision 4]⟩,⟨[4, 10, 14],[16],[t332,.collision 10]⟩,⟨[9, 10, 14],[4, 16],[t19,.collision 10,t60]⟩,⟨[3, 6, 10, 16],[12, 13],[.collision 6,t422,t415,.collision 10]⟩,⟨[3, 7, 16],[12, 13],[.collision 7,t71,t275]⟩,
⟨[4, 8, 16],[14, 15],[.collision 8,t454,t538]⟩,⟨[4, 9, 10, 16],[15],[t320,.collision 9,.collision 10]⟩,⟨[3, 6, 12, 16],[10, 13],[.collision 6,t422,t253,.collision 12]⟩,⟨[3, 6, 13],[7, 10, 12],[.collision 6,t253,t383,t27,.collision 13]⟩,⟨[4, 9, 14],[15],[t68,.collision 14,.collision 9]⟩,⟨[4, 9, 15],[8, 10, 14],[t208,t428,.collision 9,t164,.collision 15]⟩,⟨[1, 5, 18],[6, 20],[.collision 5,t203,.collision 18,t23]⟩,⟨[1, 6, 17],[5, 20],[.collision 6,t343,.collision 17,t542]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify240 : page240.all (justified priors)=true := by decide +kernel
def page264 : List Block := [
⟨[1, 8, 18],[20],[.collision 8,t73,.collision 1]⟩,⟨[1, 11, 18],[12, 20],[.collision 11,t34,t88]⟩,⟨[1, 14, 18],[20],[t73,.collision 1,.collision 14]⟩,⟨[8, 14, 17],[1, 6, 12],[.collision 8,t177,t263,t348]⟩,⟨[2, 7, 21],[19],[.collision 7,t205]⟩,⟨[2, 13, 21],[19],[t205,.collision 13]⟩,⟨[2, 5, 21],[9, 19],[.collision 5,t549,t551]⟩,⟨[2, 9, 17, 21],[5, 19],[t205,.collision 2,.collision 17,t432]⟩,
⟨[2, 11, 21],[15, 19],[.collision 11,t537,t370]⟩,⟨[2, 15, 17, 21],[11, 19],[t205,.collision 2,.collision 17,t5]⟩,⟨[2, 11, 19],[13, 15, 17],[.collision 11,t221,t210,t311]⟩,⟨[12, 13, 22],[19],[t159,.collision 12,.collision 13]⟩,⟨[3, 12, 22],[18, 19],[t159,.collision 12,t52]⟩,⟨[3, 13, 22],[19],[t346,.collision 13]⟩,⟨[4, 15, 22],[21],[t9,.collision 15]⟩,⟨[3, 6, 22],[10, 19],[.collision 6,t502,t253]⟩,
⟨[3, 7, 18],[19],[.collision 7,t140]⟩,⟨[3, 10, 18],[6, 19],[t140,.collision 18,t344]⟩,⟨[3, 16, 18],[12, 19],[t140,.collision 18,t415]⟩,⟨[3, 6, 19],[7, 10, 18],[.collision 6,t194,t180,t383]⟩,⟨[3, 7, 22],[6, 10, 18],[.collision 7,t470,t295,t288]⟩,⟨[4, 8, 22],[9, 10, 20],[.collision 8,t92,t364,t50]⟩,⟨[4, 9, 21],[10, 20],[t17,t208]⟩,⟨[5, 6, 8, 14],[1, 11],[.collision 5,.collision 6,.collision 8,t222,t10]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify264 : page264.all (justified priors)=true := by decide +kernel
def page288 : List Block := [
⟨[5, 8, 11],[1, 6],[.collision 11,.collision 5,.collision 8,t523,t20]⟩,⟨[5, 7, 15],[2, 11],[.collision 5,.collision 7,t314,t527]⟩,⟨[7, 11, 13, 15],[9],[.collision 11,.collision 7,t175,.collision 13,.collision 15]⟩,⟨[4, 8, 9, 15],[14],[.collision 8,t164,.collision 9]⟩,⟨[10, 14, 15],[4, 8],[t19,.collision 10,t476]⟩,⟨[5, 8, 20],[18],[.collision 5,t176,.collision 20,.collision 8]⟩,⟨[8, 11, 20],[18],[.collision 11,t70,.collision 8]⟩,⟨[5, 14, 20],[18],[.collision 5,t176,.collision 20,.collision 14]⟩,
⟨[1, 6, 14, 20],[12, 17, 18],[.collision 6,t515,t160,.collision 1,t355]⟩,⟨[1, 8, 12, 20],[6, 18],[.collision 8,t74,.collision 12,t131]⟩,⟨[11, 14, 20],[18],[.collision 11,t70,.collision 14]⟩,⟨[5, 6, 8, 20],[1, 17],[.collision 5,.collision 6,.collision 8,t229,t515]⟩,⟨[1, 11, 18],[14, 17],[.collision 11,t113,t41,.collision 18]⟩,⟨[5, 14, 18],[6, 8, 12, 17],[.collision 5,t252,.collision 14,t478,t78,t168]⟩,⟨[6, 14, 18, 20],[8, 12, 17],[.collision 6,t515,t43,.collision 18,t216]⟩,⟨[5, 12, 20],[1, 17],[.collision 5,t302,.collision 12,t54]⟩,
⟨[11, 14, 18],[1, 17],[.collision 11,t392,t168]⟩,⟨[5, 8, 17],[1, 6],[.collision 5,.collision 8,t177,t263]⟩,⟨[5, 7, 9, 19],[2, 17],[.collision 5,.collision 7,t147,t146]⟩,⟨[11, 13, 21],[2, 17],[.collision 11,t397,t418]⟩,⟨[7, 10, 18, 19],[3, 6],[.collision 7,t2,t106]⟩,⟨[4, 14, 21],[16, 20],[t332,t17]⟩,⟨[8, 21, 22],[4, 9],[.collision 8,t285,t92]⟩,⟨[16, 20, 21],[4, 15],[t81,.collision 16,t234]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify288 : page288.all (justified priors)=true := by decide +kernel
def page312 : List Block := [
⟨[1, 5, 8, 11, 12, 14],[],[.collision 11,.collision 5,.collision 8,.collision 1,.collision 12,.collision 14]⟩,⟨[6, 7, 16],[13],[.collision 6,t422,.collision 7]⟩,⟨[1, 5, 8, 14, 18],[11, 12, 17],[.collision 5,.collision 8,t252,t168,t11]⟩,⟨[6, 14, 18, 20],[12, 17],[.collision 6,t515,.collision 20,t216]⟩,⟨[1, 11, 14, 17],[12],[.collision 11,t88,.collision 17,.collision 14]⟩,⟨[5, 12, 17, 18],[1, 11],[.collision 5,t302,.collision 12,t495]⟩,⟨[5, 11, 15, 19],[9, 17],[.collision 11,.collision 5,t179,.collision 15,t219]⟩,⟨[6, 7, 10, 22],[18],[.collision 6,.collision 7,t470,.collision 10]⟩,
⟨[3, 12, 13, 16, 22],[18],[t52,.collision 12,.collision 13,.collision 16]⟩,⟨[4, 8, 9, 21],[20],[.collision 8,t17,.collision 9]⟩,⟨[4, 14, 15, 21],[20],[t17,.collision 14,.collision 15]⟩,⟨[2, 5, 7, 9, 11],[],[.collision 11,.collision 5,.collision 7,.collision 9,.collision 2]⟩,⟨[5, 11, 12, 14, 18],[17],[.collision 11,.collision 5,.collision 14,t168,.collision 12]⟩,⟨[6, 11, 14, 20],[8, 17],[.collision 11,.collision 6,t515,.collision 14,t236]⟩,⟨[8, 11, 12, 18],[6, 17],[.collision 11,.collision 8,t453,.collision 12,t20]⟩,⟨[5, 7, 15, 19, 21],[9, 17],[.collision 5,.collision 7,t189,t33,.collision 15]⟩,
⟨[9, 11, 13, 19],[7, 17],[.collision 11,t146,t212,.collision 13]⟩,⟨[9, 11, 15, 17, 19],[5, 13],[.collision 11,t204,.collision 9,.collision 17,t6,.collision 15]⟩,⟨[7, 10, 12, 22],[18],[.collision 7,t470,.collision 12,.collision 10]⟩,⟨[6, 7, 16, 22],[18],[.collision 6,.collision 7,t470,.collision 16]⟩,⟨[8, 16, 21],[15, 20],[.collision 8,t454,t39]⟩,⟨[10, 14, 20, 21],[8, 15],[t12,.collision 14,.collision 20,t273]⟩
]
set_option maxHeartbeats 0 in
set_option maxRecDepth 131072 in
theorem certify312 : page312.all (justified priors)=true := by decide +kernel
def blocks : List Block := page0 ++ page24 ++ page48 ++ page72 ++ page96 ++ page120 ++ page144 ++ page168 ++ page192 ++ page216 ++ page240 ++ page264 ++ page288 ++ page312
theorem checkedBlocks : blocks.all (justified priors)=true := by
  simp only [blocks,List.all_append,certify0,certify24,certify48,certify72,certify96,certify120,certify144,certify168,certify192,certify216,certify240,certify264,certify288,certify312,Bool.true_and]
def groups : List Group := [
⟨[],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[4],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5],[2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5],[1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 6],[2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6],[1, 2, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 6],[1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 6],[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[7],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 7],[1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 7],[1, 2, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 7],[1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 7],[1, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 7],[1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 7],[1, 2, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[8],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 8],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8],[1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 8],[1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[1, 5, 8],[2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 8],[1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 6, 8],[2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 6, 8],[1, 2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 6, 8],[2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[7, 8],[1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 7, 8],[1, 2, 3, 4, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 7, 8],[1, 2, 3, 4, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[9],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 9],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 9],[1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 9],[1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 9],[1, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 9],[1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 6, 9],[1, 2, 3, 4, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[7, 9],[1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2, 7, 9],[1, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 7, 9],[1, 2, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 7, 9],[1, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 7, 9],[1, 2, 3, 4, 5, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[8, 9],[1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 9],[1, 2, 3, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 8, 9],[1, 2, 3, 4, 5, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[7, 8, 9],[1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[6, 7, 8, 9],[1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[10],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 10],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 10],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 10],[1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 10],[1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 10],[1, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 6, 10],[1, 2, 3, 4, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[7, 10],[1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 7, 10],[1, 2, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 7, 10],[1, 2, 3, 4, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 7, 10],[1, 2, 3, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 7, 10],[1, 2, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[8, 10],[1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 10],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 8, 10],[1, 2, 3, 4, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[7, 8, 10],[1, 2, 3, 4, 5, 6, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 7, 8, 10],[1, 2, 3, 4, 6, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[9, 10],[1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 9, 10],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 9, 10],[1, 2, 3, 4, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 9, 10],[1, 2, 3, 4, 5, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 6, 9, 10],[1, 2, 3, 4, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[8, 9, 10],[1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[4, 8, 9, 10],[1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[11],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 11],[2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 11],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 11],[1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 11],[2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 11],[1, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 6, 11],[2, 3, 4, 5, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2, 9, 11],[1, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[12],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 12],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[8, 12],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 12],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 11, 12],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 11, 12],[2, 3, 4, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 6, 11, 12],[2, 3, 4, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[8, 11, 12],[1, 2, 3, 4, 5, 6, 7, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 8, 11, 12],[2, 3, 4, 5, 6, 7, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 8, 11, 12],[2, 3, 4, 6, 7, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[7, 13],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[9, 13],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 11, 13],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2, 5, 7, 11, 13],[1, 3, 4, 6, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[12, 13],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 12, 13],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 7, 12, 13],[1, 2, 4, 5, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 14],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 14],[2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 14],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[1, 6, 14],[2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 6, 14],[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[8, 14],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 8, 14],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 8, 14],[2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 6, 8, 14],[2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 6, 8, 14],[2, 3, 4, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[1, 11, 14],[2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 8, 11, 14],[2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 8, 11, 14],[2, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[12, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 12, 14],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 12, 14],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 12, 14],[2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 6, 12, 14],[2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[1, 5, 6, 12, 14],[2, 3, 4, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 8, 12, 14],[2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 8, 12, 14],[2, 3, 4, 6, 7, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 8, 12, 14],[1, 2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 6, 8, 12, 14],[2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 6, 8, 12, 14],[2, 3, 4, 7, 9, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 12, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 11, 12, 14],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[5, 11, 12, 14],[1, 2, 3, 4, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 11, 12, 14],[2, 3, 4, 6, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 6, 11, 12, 14],[2, 3, 4, 5, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 6, 11, 12, 14],[1, 2, 3, 4, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 5, 6, 11, 12, 14],[2, 3, 4, 7, 8, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[8, 11, 12, 14],[1, 2, 3, 4, 5, 6, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[1, 8, 11, 12, 14],[2, 3, 4, 5, 6, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[6, 8, 11, 12, 14],[1, 2, 3, 4, 5, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[1, 6, 8, 11, 12, 14],[2, 3, 4, 5, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 6, 8, 11, 12, 14],[1, 2, 3, 4, 7, 9, 10, 13, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[13, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 13, 14],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 15],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[7, 15],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[9, 15],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2, 9, 15],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 11, 15],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 11, 15],[1, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 7, 11, 15],[1, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 7, 11, 15],[1, 3, 4, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 9, 11, 15],[1, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 9, 11, 15],[1, 3, 4, 6, 7, 8, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[12, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 12, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[13, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 13, 15],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 13, 15],[1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 7, 13, 15],[1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 7, 13, 15],[1, 3, 4, 6, 8, 9, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 9, 13, 15],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2, 5, 9, 13, 15],[1, 3, 4, 6, 7, 8, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[7, 9, 13, 15],[1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 7, 9, 13, 15],[1, 3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 7, 9, 13, 15],[1, 3, 4, 6, 8, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 13, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 11, 13, 15],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 5, 11, 13, 15],[1, 3, 4, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 9, 11, 13, 15],[1, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[2, 5, 9, 11, 13, 15],[1, 3, 4, 6, 7, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[7, 9, 11, 13, 15],[1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[2, 7, 9, 11, 13, 15],[1, 3, 4, 5, 6, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[5, 7, 9, 11, 13, 15],[1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[14, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 14, 15],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 9, 14, 15],[1, 2, 3, 5, 6, 7, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[13, 14, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 17, 18, 19, 20, 21, 22]⟩,
⟨[12, 13, 14, 15],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22]⟩,⟨[16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 16],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 16],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 16],[1, 2, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 9, 16],[1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[10, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 10, 16],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[4, 10, 16],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[12, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 12, 16],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 7, 12, 16],[1, 2, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 10, 12, 16],[1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 10, 12, 16],[1, 2, 4, 5, 7, 8, 9, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 7, 10, 12, 16],[1, 2, 4, 5, 6, 8, 9, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[13, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 13, 16],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 7, 13, 16],[1, 2, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 7, 13, 16],[1, 2, 4, 5, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 10, 13, 16],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 10, 13, 16],[1, 2, 4, 5, 7, 8, 9, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 7, 10, 13, 16],[1, 2, 4, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 7, 10, 13, 16],[1, 2, 4, 5, 8, 9, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[12, 13, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 12, 13, 16],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 12, 13, 16],[1, 2, 4, 5, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 7, 12, 13, 16],[1, 2, 4, 5, 6, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 7, 12, 13, 16],[1, 2, 4, 5, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 10, 12, 13, 16],[1, 2, 4, 5, 6, 7, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 10, 12, 13, 16],[1, 2, 4, 5, 7, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 7, 10, 12, 13, 16],[1, 2, 4, 5, 6, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[6, 7, 10, 12, 13, 16],[1, 2, 3, 4, 5, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[3, 6, 7, 10, 12, 13, 16],[1, 2, 4, 5, 8, 9, 11, 14, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 14, 16],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 10, 14, 16],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 10, 14, 16],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[13, 14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 13, 14, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 17, 18, 19, 20, 21, 22]⟩,
⟨[15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 15, 16],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 15, 16],[1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 10, 15, 16],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 10, 15, 16],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 9, 10, 15, 16],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩,⟨[11, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 17, 18, 19, 20, 21, 22]⟩,⟨[12, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 17, 18, 19, 20, 21, 22]⟩,
⟨[11, 12, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 22]⟩,⟨[14, 15, 16],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 14, 15, 16],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 14, 15, 16],[1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 9, 14, 15, 16],[1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 9, 14, 15, 16],[1, 2, 3, 5, 6, 7, 10, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 10, 14, 15, 16],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 10, 14, 15, 16],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,
⟨[4, 9, 10, 14, 15, 16],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,⟨[8, 9, 10, 14, 15, 16],[1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,⟨[4, 8, 9, 10, 14, 15, 16],[1, 2, 3, 5, 6, 7, 11, 12, 13, 17, 18, 19, 20, 21, 22]⟩,⟨[17],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,⟨[5, 17],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,⟨[11, 17],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,⟨[5, 11, 17],[1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22]⟩,⟨[18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,
⟨[6, 18],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,⟨[8, 18],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,⟨[12, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,⟨[6, 12, 18],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19, 20, 21, 22]⟩,⟨[14, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 19, 20, 21, 22]⟩,⟨[17, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22]⟩,⟨[1, 17, 18],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22]⟩,⟨[1, 5, 6, 17, 18],[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22]⟩,
⟨[8, 17, 18],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22]⟩,⟨[1, 11, 12, 17, 18],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 19, 20, 21, 22]⟩,⟨[1, 5, 6, 11, 12, 17, 18],[2, 3, 4, 7, 8, 9, 10, 13, 14, 15, 16, 19, 20, 21, 22]⟩,⟨[14, 17, 18],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 19, 20, 21, 22]⟩,⟨[19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22]⟩,⟨[7, 19],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22]⟩,⟨[9, 19],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22]⟩,⟨[13, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22]⟩,
⟨[7, 13, 19],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22]⟩,⟨[15, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 20, 21, 22]⟩,⟨[17, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22]⟩,⟨[18, 19],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 22]⟩,⟨[20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[6, 20],[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 5, 6, 20],[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,
⟨[8, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 8, 20],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 6, 8, 20],[2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[12, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 11, 12, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 5, 6, 11, 12, 20],[2, 3, 4, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[14, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 14, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩,
⟨[8, 14, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 8, 14, 20],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 12, 14, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[1, 6, 8, 12, 14, 20],[2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 17, 18, 19, 21, 22]⟩,⟨[17, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 21, 22]⟩,⟨[18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,⟨[5, 18, 20],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,
⟨[1, 5, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 6, 18, 20],[2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 5, 6, 18, 20],[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 8, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 5, 8, 18, 20],[2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,⟨[6, 8, 18, 20],[1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 6, 8, 18, 20],[2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 5, 6, 8, 18, 20],[2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22]⟩,
⟨[1, 14, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 8, 14, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 11, 14, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 8, 11, 14, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 5, 8, 11, 14, 18, 20],[2, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[12, 14, 18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 12, 14, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 5, 12, 14, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,
⟨[1, 6, 12, 14, 18, 20],[2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 5, 6, 12, 14, 18, 20],[2, 3, 4, 7, 8, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 8, 12, 14, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 5, 8, 12, 14, 18, 20],[2, 3, 4, 6, 7, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[6, 8, 12, 14, 18, 20],[1, 2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 6, 8, 12, 14, 18, 20],[2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 5, 6, 8, 12, 14, 18, 20],[2, 3, 4, 7, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[1, 11, 12, 14, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 17, 19, 21, 22]⟩,
⟨[1, 6, 8, 11, 12, 14, 18, 20],[2, 3, 4, 5, 7, 9, 10, 13, 15, 16, 17, 19, 21, 22]⟩,⟨[17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[5, 17, 18, 20],[1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 17, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 6, 17, 18, 20],[2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[5, 6, 17, 18, 20],[1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 6, 17, 18, 20],[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,
⟨[8, 17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 8, 17, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 8, 17, 18, 20],[2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[6, 8, 17, 18, 20],[1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 6, 8, 17, 18, 20],[2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[5, 6, 8, 17, 18, 20],[1, 2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 6, 8, 17, 18, 20],[2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 11, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 19, 21, 22]⟩,
⟨[1, 5, 11, 17, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 6, 11, 17, 18, 20],[2, 3, 4, 5, 7, 8, 9, 10, 12, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 11, 12, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 11, 12, 17, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 6, 11, 12, 17, 18, 20],[2, 3, 4, 7, 8, 9, 10, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 8, 11, 12, 17, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 8, 11, 12, 17, 18, 20],[2, 3, 4, 6, 7, 9, 10, 13, 14, 15, 16, 19, 21, 22]⟩,⟨[14, 17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 19, 21, 22]⟩,
⟨[1, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 14, 17, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 6, 14, 17, 18, 20],[2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 6, 14, 17, 18, 20],[2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 8, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 8, 14, 17, 18, 20],[2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 6, 8, 14, 17, 18, 20],[2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 6, 8, 14, 17, 18, 20],[2, 3, 4, 7, 9, 10, 11, 12, 13, 15, 16, 19, 21, 22]⟩,
⟨[12, 14, 17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 12, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 12, 14, 17, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 6, 12, 14, 17, 18, 20],[2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 6, 12, 14, 17, 18, 20],[2, 3, 4, 7, 8, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 8, 12, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 8, 12, 14, 17, 18, 20],[2, 3, 4, 6, 7, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,⟨[6, 8, 12, 14, 17, 18, 20],[1, 2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,
⟨[1, 6, 8, 12, 14, 17, 18, 20],[2, 3, 4, 5, 7, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 6, 8, 12, 14, 17, 18, 20],[2, 3, 4, 7, 9, 10, 11, 13, 15, 16, 19, 21, 22]⟩,⟨[11, 12, 14, 17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 11, 12, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[5, 11, 12, 14, 17, 18, 20],[1, 2, 3, 4, 6, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 5, 11, 12, 14, 17, 18, 20],[2, 3, 4, 6, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 6, 11, 12, 14, 17, 18, 20],[2, 3, 4, 5, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[5, 6, 11, 12, 14, 17, 18, 20],[1, 2, 3, 4, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩,
⟨[1, 5, 6, 11, 12, 14, 17, 18, 20],[2, 3, 4, 7, 8, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[8, 11, 12, 14, 17, 18, 20],[1, 2, 3, 4, 5, 6, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 8, 11, 12, 14, 17, 18, 20],[2, 3, 4, 5, 6, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[6, 8, 11, 12, 14, 17, 18, 20],[1, 2, 3, 4, 5, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[1, 6, 8, 11, 12, 14, 17, 18, 20],[2, 3, 4, 5, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[5, 6, 8, 11, 12, 14, 17, 18, 20],[1, 2, 3, 4, 7, 9, 10, 13, 15, 16, 19, 21, 22]⟩,⟨[19, 20],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22]⟩,⟨[21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩,
⟨[2, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩,⟨[7, 21],[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩,⟨[9, 21],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩,⟨[2, 9, 21],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22]⟩,⟨[13, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 22]⟩,⟨[15, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩,⟨[2, 15, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩,⟨[9, 15, 21],[1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩,
⟨[2, 9, 15, 21],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22]⟩,⟨[17, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 22]⟩,⟨[2, 17, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 22]⟩,⟨[2, 5, 9, 17, 21],[1, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 22]⟩,⟨[2, 11, 15, 17, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 18, 19, 20, 22]⟩,⟨[2, 5, 9, 11, 15, 17, 21],[1, 3, 4, 6, 7, 8, 10, 12, 13, 14, 16, 18, 19, 20, 22]⟩,⟨[18, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 22]⟩,⟨[19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,
⟨[2, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,⟨[2, 5, 19, 21],[1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,⟨[2, 5, 7, 19, 21],[1, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,⟨[2, 9, 19, 21],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,⟨[2, 5, 9, 19, 21],[1, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,⟨[7, 9, 19, 21],[1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,⟨[2, 7, 9, 19, 21],[1, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,⟨[2, 5, 7, 9, 19, 21],[1, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22]⟩,
⟨[2, 11, 13, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 22]⟩,⟨[2, 5, 7, 11, 13, 19, 21],[1, 3, 4, 6, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 22]⟩,⟨[2, 15, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 9, 15, 19, 21],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 11, 15, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 9, 11, 15, 19, 21],[1, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 5, 9, 11, 15, 19, 21],[1, 3, 4, 6, 7, 8, 10, 12, 13, 14, 16, 17, 18, 20, 22]⟩,⟨[13, 15, 19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩,
⟨[2, 13, 15, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 5, 13, 15, 19, 21],[1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 9, 13, 15, 19, 21],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 5, 9, 13, 15, 19, 21],[1, 3, 4, 6, 7, 8, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩,⟨[7, 9, 13, 15, 19, 21],[1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 7, 9, 13, 15, 19, 21],[1, 3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 5, 7, 9, 13, 15, 19, 21],[1, 3, 4, 6, 8, 10, 11, 12, 14, 16, 17, 18, 20, 22]⟩,⟨[2, 11, 13, 15, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 20, 22]⟩,
⟨[2, 7, 9, 11, 13, 15, 19, 21],[1, 3, 4, 5, 6, 8, 10, 12, 14, 16, 17, 18, 20, 22]⟩,⟨[17, 19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 5, 17, 19, 21],[1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 7, 17, 19, 21],[1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 5, 7, 17, 19, 21],[1, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 9, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 5, 9, 17, 19, 21],[1, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,
⟨[7, 9, 17, 19, 21],[1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 7, 9, 17, 19, 21],[1, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[5, 7, 9, 17, 19, 21],[1, 2, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 5, 7, 9, 17, 19, 21],[1, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 11, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 5, 11, 17, 19, 21],[1, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 9, 11, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16, 18, 20, 22]⟩,⟨[2, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 20, 22]⟩,
⟨[2, 9, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 18, 20, 22]⟩,⟨[2, 11, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 18, 20, 22]⟩,⟨[2, 5, 11, 15, 17, 19, 21],[1, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 16, 18, 20, 22]⟩,⟨[2, 7, 11, 15, 17, 19, 21],[1, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 18, 20, 22]⟩,⟨[2, 5, 7, 11, 15, 17, 19, 21],[1, 3, 4, 6, 8, 9, 10, 12, 13, 14, 16, 18, 20, 22]⟩,⟨[2, 5, 9, 11, 15, 17, 19, 21],[1, 3, 4, 6, 7, 8, 10, 12, 13, 14, 16, 18, 20, 22]⟩,⟨[13, 15, 17, 19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 22]⟩,
⟨[2, 5, 13, 15, 17, 19, 21],[1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 7, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 5, 7, 13, 15, 17, 19, 21],[1, 3, 4, 6, 8, 9, 10, 11, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 9, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 5, 9, 13, 15, 17, 19, 21],[1, 3, 4, 6, 7, 8, 10, 11, 12, 14, 16, 18, 20, 22]⟩,⟨[7, 9, 13, 15, 17, 19, 21],[1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 7, 9, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 8, 10, 11, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 5, 7, 9, 13, 15, 17, 19, 21],[1, 3, 4, 6, 8, 10, 11, 12, 14, 16, 18, 20, 22]⟩,
⟨[11, 13, 15, 17, 19, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 11, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 5, 11, 13, 15, 17, 19, 21],[1, 3, 4, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 9, 11, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 5, 9, 11, 13, 15, 17, 19, 21],[1, 3, 4, 6, 7, 8, 10, 12, 14, 16, 18, 20, 22]⟩,⟨[7, 9, 11, 13, 15, 17, 19, 21],[1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20, 22]⟩,⟨[2, 7, 9, 11, 13, 15, 17, 19, 21],[1, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20, 22]⟩,⟨[5, 7, 9, 11, 13, 15, 17, 19, 21],[1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22]⟩,
⟨[20, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22]⟩,⟨[19, 20, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 22]⟩,⟨[18, 19, 20, 21],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 22]⟩,⟨[22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,⟨[3, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,⟨[4, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,⟨[10, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,⟨[3, 10, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,
⟨[4, 10, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩,⟨[16, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,⟨[3, 16, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,⟨[4, 16, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,⟨[10, 16, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,⟨[3, 10, 16, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,⟨[4, 10, 16, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21]⟩,⟨[17, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21]⟩,
⟨[18, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21]⟩,⟨[3, 18, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21]⟩,⟨[3, 6, 10, 18, 22],[1, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21]⟩,⟨[3, 12, 16, 18, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 19, 20, 21]⟩,⟨[3, 6, 10, 12, 16, 18, 22],[1, 2, 4, 5, 7, 8, 9, 11, 13, 14, 15, 17, 19, 20, 21]⟩,⟨[19, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩,⟨[3, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩,⟨[3, 6, 7, 19, 22],[1, 2, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩,
⟨[3, 10, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩,⟨[3, 6, 10, 19, 22],[1, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩,⟨[3, 7, 10, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21]⟩,⟨[3, 12, 13, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 20, 21]⟩,⟨[3, 6, 7, 12, 13, 19, 22],[1, 2, 4, 5, 8, 9, 10, 11, 14, 15, 16, 17, 18, 20, 21]⟩,⟨[3, 16, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 20, 21]⟩,⟨[3, 10, 16, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 20, 21]⟩,⟨[3, 12, 16, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 18, 20, 21]⟩,
⟨[3, 10, 12, 16, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 17, 18, 20, 21]⟩,⟨[3, 6, 10, 12, 16, 19, 22],[1, 2, 4, 5, 7, 8, 9, 11, 13, 14, 15, 17, 18, 20, 21]⟩,⟨[3, 13, 16, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 18, 20, 21]⟩,⟨[3, 10, 13, 16, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15, 17, 18, 20, 21]⟩,⟨[3, 6, 10, 13, 16, 19, 22],[1, 2, 4, 5, 7, 8, 9, 11, 12, 14, 15, 17, 18, 20, 21]⟩,⟨[3, 7, 10, 13, 16, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18, 20, 21]⟩,⟨[18, 19, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,⟨[3, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,
⟨[3, 6, 18, 19, 22],[1, 2, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,⟨[3, 7, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,⟨[3, 6, 7, 18, 19, 22],[1, 2, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,⟨[3, 10, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,⟨[3, 6, 10, 18, 19, 22],[1, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,⟨[3, 7, 10, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,⟨[6, 7, 10, 18, 19, 22],[1, 2, 3, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,⟨[3, 6, 7, 10, 18, 19, 22],[1, 2, 4, 5, 8, 9, 11, 12, 13, 14, 15, 16, 17, 20, 21]⟩,
⟨[3, 12, 13, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 20, 21]⟩,⟨[3, 6, 7, 12, 13, 18, 19, 22],[1, 2, 4, 5, 8, 9, 10, 11, 14, 15, 16, 17, 20, 21]⟩,⟨[3, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 20, 21]⟩,⟨[3, 6, 16, 18, 19, 22],[1, 2, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 20, 21]⟩,⟨[3, 10, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 20, 21]⟩,⟨[3, 12, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 20, 21]⟩,⟨[3, 7, 12, 16, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 17, 20, 21]⟩,⟨[3, 10, 12, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 17, 20, 21]⟩,
⟨[3, 6, 10, 12, 16, 18, 19, 22],[1, 2, 4, 5, 7, 8, 9, 11, 13, 14, 15, 17, 20, 21]⟩,⟨[3, 7, 10, 12, 16, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 13, 14, 15, 17, 20, 21]⟩,⟨[3, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 17, 20, 21]⟩,⟨[3, 7, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 17, 20, 21]⟩,⟨[3, 6, 7, 13, 16, 18, 19, 22],[1, 2, 4, 5, 8, 9, 10, 11, 12, 14, 15, 17, 20, 21]⟩,⟨[3, 10, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 14, 15, 17, 20, 21]⟩,⟨[3, 6, 10, 13, 16, 18, 19, 22],[1, 2, 4, 5, 7, 8, 9, 11, 12, 14, 15, 17, 20, 21]⟩,⟨[3, 7, 10, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 12, 14, 15, 17, 20, 21]⟩,
⟨[3, 6, 7, 10, 13, 16, 18, 19, 22],[1, 2, 4, 5, 8, 9, 11, 12, 14, 15, 17, 20, 21]⟩,⟨[12, 13, 16, 18, 19, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 20, 21]⟩,⟨[3, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 17, 20, 21]⟩,⟨[3, 6, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 7, 8, 9, 10, 11, 14, 15, 17, 20, 21]⟩,⟨[3, 7, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 10, 11, 14, 15, 17, 20, 21]⟩,⟨[3, 6, 7, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 8, 9, 10, 11, 14, 15, 17, 20, 21]⟩,⟨[3, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 7, 8, 9, 11, 14, 15, 17, 20, 21]⟩,⟨[3, 6, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 7, 8, 9, 11, 14, 15, 17, 20, 21]⟩,
⟨[3, 7, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 6, 8, 9, 11, 14, 15, 17, 20, 21]⟩,⟨[6, 7, 10, 12, 13, 16, 18, 19, 22],[1, 2, 3, 4, 5, 8, 9, 11, 14, 15, 17, 20, 21]⟩,⟨[3, 6, 7, 10, 12, 13, 16, 18, 19, 22],[1, 2, 4, 5, 8, 9, 11, 14, 15, 17, 20, 21]⟩,⟨[20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21]⟩,⟨[19, 20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21]⟩,⟨[17, 19, 20, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21]⟩,⟨[21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩,⟨[4, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩,
⟨[4, 10, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩,⟨[4, 8, 10, 21, 22],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩,⟨[4, 9, 10, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]⟩,⟨[4, 16, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20]⟩,⟨[4, 10, 16, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20]⟩,⟨[4, 14, 16, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20]⟩,⟨[4, 10, 14, 16, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 15, 17, 18, 19, 20]⟩,⟨[4, 15, 16, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20]⟩,
⟨[4, 10, 15, 16, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 17, 18, 19, 20]⟩,⟨[4, 8, 10, 15, 16, 21, 22],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 14, 17, 18, 19, 20]⟩,⟨[4, 9, 10, 15, 16, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 19, 20]⟩,⟨[18, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20]⟩,⟨[17, 18, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20]⟩,⟨[20, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,⟨[4, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,⟨[4, 8, 20, 21, 22],[1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,
⟨[4, 9, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,⟨[4, 8, 9, 20, 21, 22],[1, 2, 3, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,⟨[4, 10, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,⟨[4, 8, 10, 20, 21, 22],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,⟨[4, 9, 10, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,⟨[8, 9, 10, 20, 21, 22],[1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,⟨[4, 8, 9, 10, 20, 21, 22],[1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩,⟨[4, 14, 15, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19]⟩,
⟨[4, 8, 9, 14, 15, 20, 21, 22],[1, 2, 3, 5, 6, 7, 10, 11, 12, 13, 16, 17, 18, 19]⟩,⟨[4, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19]⟩,⟨[4, 9, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 17, 18, 19]⟩,⟨[4, 10, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19]⟩,⟨[4, 14, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19]⟩,⟨[4, 8, 10, 14, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 15, 17, 18, 19]⟩,⟨[4, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19]⟩,⟨[4, 8, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 17, 18, 19]⟩,
⟨[4, 10, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 17, 18, 19]⟩,⟨[4, 8, 10, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 14, 17, 18, 19]⟩,⟨[4, 9, 10, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 19]⟩,⟨[14, 15, 16, 20, 21, 22],[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19]⟩,⟨[4, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19]⟩,⟨[4, 8, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 17, 18, 19]⟩,⟨[4, 9, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 17, 18, 19]⟩,⟨[4, 8, 9, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 10, 11, 12, 13, 17, 18, 19]⟩,
⟨[4, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 17, 18, 19]⟩,⟨[4, 8, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 9, 11, 12, 13, 17, 18, 19]⟩,⟨[4, 9, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 17, 18, 19]⟩,⟨[8, 9, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 17, 18, 19]⟩,⟨[4, 8, 9, 10, 14, 15, 16, 20, 21, 22],[1, 2, 3, 5, 6, 7, 11, 12, 13, 17, 18, 19]⟩
]
def keys : List Nat := [
232,123,67,28,73,78,444,445,
446,447,448,449,450,233,105,451,
452,149,234,453,454,455,106,235,
320,456,179,124,125,107,321,126,
236,322,237,323,324,238,180,89,
457,458,90,459,181,46,325,239,
326,327,328,62,329,68,330,460,
461,47,45,462,463,464,91,92,
93,240,182,183,108,241,127,242,
128,129,79,243,184,150,53,80,
465,55,185,31,56,186,109,94,
95,57,96,331,187,151,110,111,
244,466,15,152,188,467,332,153,
97,38,333,245,189,334,246,130,
112,154,81,35,48,58,69,26,
190,155,191,131,247,335,39,248,
249,250,74,70,156,75,336,468,
76,98,132,469,470,133,157,337,
61,40,471,158,192,472,251,473,
159,252,16,113,19,193,474,475,
134,160,253,71,135,136,27,338,
13,161,476,77,32,194,162,195,
36,99,137,196,9,339,14,33,
41,10,49,254,37,42,11,477,
478,255,479,480,256,257,138,340,
72,197,258,341,342,343,344,481,
139,345,482,346,163,347,483,484,
259,260,164,348,485,261,486,487,
100,262,349,350,488,263,489,490,
351,491,492,493,352,165,494,198,
199,495,264,353,354,355,496,356,
497,498,499,200,201,50,357,202,
265,358,500,501,502,503,203,504,
505,506,507,508,509,359,114,510,
204,511,266,205,360,267,512,513,
268,82,514,515,361,516,362,517,
269,166,518,270,167,271,519,43,
520,363,101,521,206,115,522,364,
365,366,367,368,523,272,273,140,
369,370,207,371,372,373,524,274,
141,275,276,208,277,209,525,374,
375,278,376,210,377,211,279,378,
379,526,527,380,280,381,528,529,
530,281,382,531,383,282,384,283,
385,532,386,284,212,533,387,534,
388,535,536,537,538,213,539,540,
541,389,390,391,285,542,543,214,
215,286,287,544,288,289,545,290,
546,547,548,549,291,392,393,550,
551,394,552,553,554,292,555,556,
557,558,559,560,561,562,563,564,
565,566,567,568,569,570,571,572,
573,574,575,576,577,578,579,580,
581,582,583,584,585,586,587,588,
589,590,591,592,593,594,595,596,
597,598,599,600,601,602,603,604,
605,606,607,608,609,610,611,612,
613,614,615,616,617,618,619,620,
621,622,623,624,625,626,627,628,
629,630,631,632,633,634,635,636,
637,638,639,640,641,642,643,644,
645,646,647,648,649,650,651,652,
653,654,655,656,657,658,659,660,
661,662,663,664,665,666,667,668,
669,670,671,672,673,674,675,676,
677,678,679,680,681,682,683,684,
685,686,687,688,689,690,691,692,
693,694,695,696,697,698,699,700,
701,702,703,704,705,706,707,708,
709,710,711,712,713,714,715,716,
717,718,719,720,721,722,723,724,
725,726,727,728,729,730,731,732,
733,734,735,736,737,738,739,740,
741,742,743,744,745,746,747,748,
749,750,751,752,753,754,755,756,
757,758,759,760,761,762,763,764,
765,766,767,768,769,770,771,772,
773,774,775,776,777,778,779,780,
781,782,783,784,785,786,787,788,
789,790,791,792,793,794,795,796,
797,798,799,800,801,802,803,804,
805,806,807,808,809,810,811,812,
813,814,815,816,817,818,819,820,
821,822,823,824,825,826,827,828,
829,830,831,832,833,834,835,836,
837,838,839,840,841,842,843,844,
845,846,847,848,849,850,851,852,
853,854,855,856,857,858,859,860,
861,862,863,864,865,866,867,868,
869,870,871,872,873,874,875,876,
877,878,879,880,881,882,883,884,
885,886,887,888,889,890,891,892,
893,894,895,896,897,898,899,900,
901,902,903,904,905,906,907,908,
909,910,911,912,913,914,915,916,
917,918,919,920,921,922,923,924,
925,926,927,928,929,930,931,932,
933,934,935,936,937,938,939,940,
941,942,943,944,945,946,947,948,
949,950,951,952,953,954,955,956,
957,958,959,960,961,962,963,964,
965,966,967,968,969,970,971,972,
973,974,975,976,977,978,979,980,
981,982,983,984,985,986,987,988,
989,990,991,992,993,994,995,996,
997,998,999,1000,1001,1002,1003,1004,
1005,1006,1007,1008,1009,1010,1011,1012,
1013,1014,1015,1016,1017,1018,1019,1020,
1021,1022,1023,1024,1025,1026,1027,1028,
1029,1030,1031,1032,1033,1034,1035,1036,
1037,1038,1039,1040,1041,1042,1043,1044,
1045,1046,1047,1048,1049,1050,1051,1052,
1053,1054,1055,1056,1057,1058,1059,1060,
1061,1062,1063,1064,1065,1066,1067,1068,
1069,1070,1071,1072,1073,1074,1075,1076,
1077,1078,1079,1080,1081,1082,1083,1084,
1085,1086,1087,1088,1089,1090,1091,1092,
1093,1094,1095,1096,1097,1098,1099,1100,
1101,1102,1103,1104,1105,1106,1107,1108,
1109,1110,1111,1112,1113,1114,1115,1116,
1117,1118,1119,1120
]
def words : List Nat := [
0x10080081682b0520840f81d04805409c622160262e8000480880d01802c0980700c0140180200205a0ac1482103e0740a8130211862f8088bc000120220340600b00e018028130060080081682b0520840f81d02a04c08c60,0x101040809c620000680c01601c0300502600c0100102d0560a41081f0440900e8158c91700845b0000901101a0300580902601c030050060080081682b0520840f81d02a02631c61023180000220340600b00e01802813006,0x100c0100102d0560a41081f03a04a338d5021158000240440600b01404c0740f80e018028108060080081682b052068090088cd160084570000901101a0300580a02603a0380600a00c0100102d0560a41081f02402632c63,0x104a04a338000340600b02204c0900700c0140180200205a0ac1482103e0500ec698b40422c8000480880d01802c0500980e018028030040040b41582904207c1301d0131a2330098ca0001101a0300580a0260480380600a,0x103e05235c52021144000240440700d01802c0980481f01c030050060080081682b0520840a0128d434c0820c0000700481f02804cc5c6902b1900001802c0380600a04c0180200205a0ac148210340881201f03a62a34008,0x103f1b62a0108a6000120220380680c01602a0240700c0140180200205a0ac1482104c07c0946c8d404cc5808054074c50230b406c148030b202c0f80d04003c140250b605c1180505c064120270b801c1600005a0ac14821,0x104609c2e00505c0001682b0520840e0158dd1b40a46b0100a80e98a0000580700c014098030040040b4158290300681102404207c6bc5502234c0946c0000880e01a0300580a82401c030050060080081682b05208413009,0x10b80141700005a0ac14821038632268128980001202203c0700d01802c0980482101c030050060080081682b0520400a46f89c04c898112240206b01f1ae08c2d01b052064120030b202c0f80d04003c140250b601c16017,
0x11ac07c6b8230b406c1481904800c2c80b03e0341000f0500942d80705805c118270b80141700005a0ac148210291c2378158dc044890081ac07c6b8230b406c1481904800c2c80b03e0341000f0500942d80705805c11827,0x104e1700782804a16c0382c0000b41582903c0200ac7119a024a58000560800f01d11b1400822a0291c0098d0038630040d603e35c0000e018028130060080081682b0520600d022048058108d889e044ad8131a0070c6008,0x10228200ac7103a234108d802e08c1185a0360a40c8240061640581f00a0b80682004e1700782804a16c0382c0000b41582903c022394480243540810b03a234108d802e08c1185a0360a40c8240061640581f00a0b806820,0x10520180200205a0ac048148eb110094420000901102003c0700d01802c0980480e018028030040040b4158290280463a443025104000240440800f01c0340600b0260120280700c0520180200205a0ac0a0108e710009846,0x10480881001e0380680c01602a0980700c0140180200205a0ac148090211de2481288c000120220400780e01a0300580a80e018028030040040b41582904c02408c768e8042398000440800f01c0340600b0260480280700c,0x10500942d8070580001682b05207a3d4780291d40002003c0880d01802c0981200a01c030148060080081682b0380263cc770231d8000220400780e01a0300581200e018028030040040b41582904c05404c7888e04a22800,0x104809a3e173025128000240440800d01802c0500481d01c030050060080081682b05207c130108f60a80494d0000b41001f0380863c8088e4074468211b005c118230b406c1481904800c2c80b03e0141700d04009c2e00f,0x10b400c2c80505c01c1600005a0ac148528f8054ba00819a0701081e8f40846c000018028130060080081682b0520600d0220480380b47d896048b90108f6000110200340600b0140120740700c0140180200205a0ac1481f,
0x101607c0b82300a0b8068200061900c8240461c8078280360a40382c03a2340f9240000b415826048080048148fc8780e021010770148520000b41582003e4923e8190480341001704602c0f81b05203c140270b80942d823,0x104808004c8186804d118108fe000120220400780e01a0300581302801c030050060080081682b02a026404350250cc000260480881001e0380680c01602a0a00700c0140180200205a0ac048108ff0c80897f02646814852,0x1056098120201b2354084310000881001e0380680c016028090070020140301402b05a01802026024022414800291f81485201607c0b82300a0b8068200061900c8240461c8078280360a40382c03a2340f9240000b415826,0x10061900c8240461c8078280360a40382c01030c08923040364148520000b4158260480780e0149072080a8c20260c004c8103a2340f9240521480581f02e08c0282e01a080018640320901187201e0a00d82900e0b00002d,0x1018028030040040b4158210120400ec8586e04c8981490602c0f8170460141700d04000c3201904808c3900f05006c14807058020618112460806c8290a40001682b04c0900f01c9090d80991a01607c0b82300a0b806820,0x10140180200205a0ac1081202121e428131a00724201124602c0f8170460141700d04000c3201904808c3900f05006c14807058020618201b20a42900005a0ac1302403d21a1c015872000130240440780d01802c0481400e,0x10000880e01a0300581401f0120380600a00c0100102d056098120219130f00a17f02121c000240440700d01802c0a00f80901c030050060080081682b04c084094888760521d00004c0901101c0340600b02803e0240700c,0x10400780e01a0300580a01204a0380600a0500180202b05a0080848b9120751201e90c020618201b206c1480f05008c390290a402c0f8170460141700d04000c3201904801c1600005a0ac130249150f4088d302846809488,
0x103a3340c8a604273c049c904d2300382c0000b41580b9160446a81d19a06c5280f2180841381510807ce701339a024e402491400c320190480341001704602c0f80505c01c160290a40001682b04d2321f82287c00013008,0x191a0547d81b05203c1401101202c0681f042074050030100141e81701e0ac0581306008c8700005a080040270300181402431a434063f80000a0120220400780e012030058138100040381500a0100180202d03405246a09,0x19212380a8c50220240580d03e0840e80a0060200283d02e03c1580b0260c01190e0362941218d0000b41000804e0600302801d23c8680c812000140220400780e01a030058150120200940300a01009c0200205a0500748e,0x19252400a10c01d23c0d8a50486341190e0260c0088090160340f82103a0280180800a0f40b80f05602c0002d0400201381800c0a248a1d01b044000280440800f01c0340600b012020028040060080081682704a0a80a80f,0x19240348681308c06ce600f396094b501510c0a24881101202c0681f042074050030100141e81701e0ac0580005a080040270300186d4300450bc0002401c0800f01c0340600b0140240401482a014020138040040b40300c,0x1018fec000280480881001e0380680c016024040150070140200200205a09c07015928fe40697e0220240580d03e0840e80a0060200283d02e03c1580b0462cc0d86d0260c01485800c3680002d040020138180480380a493,0x1018ff4000280480881001e0380680c0160240401500a0100100102d04e01c0781592d2500a4930220240580d03e0840e80a0060200283d02e03c1580b0462cc0d86d0260c01485800c3680002d0400201381804803a4abfc,0x101d254088090160340f82103a0280180800a0f40b80f05602c118b30361b409830052160030da0000b41000804e060124987f40308c81592c000140220400780e01a03005809010054028040040040b41380704803e4ba21,
0x104a028040040040b41380705003e4dc12019040000280440800f01c0340600b0120200a8050080080081682704a01c078159350340640c0000a01102003c0700d01802c0a80901004a028040040040b41380701e0524cc97,0x1814000140220400780e01a030058070120200941500a0100100102d04e01c0a49d81e032070000500881001e0380680c016024040070250140200200205a09c1500702b2724d0149320001102003c0700d01802c0a809010,0x100a0f40b80f05602c0002d040020138181b727807c9b0000800f01c0340600b02a0240401280a0100100102d04e01c1102893f2740ac9c0000881001e0380680c016024040070250140200200205a09c1502800f27a0580c,0x18260348781101202c0681f0420141e81701e08c188030100740502b0160544581a0d804c180290b0018530181b60001682001009c1280e94127c124980260c00d86d052160118b300c368088090160340f82103a02801808,0x10160544581a0d804c180290b0018530181b6094c700005a0800402701f2860a00c22003a5001101202c0681f0420141e81701e08c188030100740502b0160544581a0d804c180290b0018530181b60001682001009c1298e,0x111eff80690f01f2841298e0260c00a88b0341b01485800c2981183103036c0b80f00a0f4088090160340f82103a0280180805602c0002d0400201388e7fe0308801101202c0681f0420141e81701e08c188030100740502b,0x1042074050030100ac0580508408c7701b0da0644782711c04c180292920001682001001c124a37d4051f3800050098120220400780e01a0300581501202001c0200a0100081680e0192883601b22e0181200005a08013019,0x1028844064a40000981102003c0700d01802c0380901004a01c0500805400816828009294be8147e8000140260440800f01c0340600b00e024040128070140201500205a010064a494405c4a80f406034b401101202c0681f,
0x10060201580b03223c0682004e2380b8fd0260c0038dc0000b4100080340a012ca694a03c8c0171380925181306006c3682929208c770050840440480b01a07c1081d01400c0402b0160644782711c0001682001001c6e3f5,0x10480381001e0380680c0160500980800c00c0280402d05400809004950fa40a3e60000981200e0400780e01a030058140120200300300a0100b41500200808a53bf301e43011a0500a8100a8840220240580d03e0840e80a,0x103a0280180805602c0c88f01a080038dc04e2380002d0400200d4aa950014a900f050096530171fa04c1801101202c0681f042074050030100ac0581911e034100071b809c4700005a0800401a0512a5f90151f008a53800,0x1028fa00002804c0901102003c0700d01802c0240900a01c0300102a0200b403004958294120290352a8038dc03223c1388e0000b4100089570b80295201e0a00984602e21c1296a04681c0a8860512a4088090160340f821,0x10480880f01c0340600b0120120380602a0420100102d020028034ad9580a5030132d206c370190ba05c1a00f0fc03435827290094a382328a01c268050900225580b01a07c108030100440481d0140ac0580005a08015beb,0x100c078090100100381500a0040840202d01805a574ad03e8400996901e1f80686b0162d41394804a51c119450361f40c86a02e1ec0384d0060200880903a0280282d0520301002b05602c0002d0120d5f70157e200014026,0x10240401500a0100840200205a01c064b095c06c148171fa0941382309403c1c80d0400440480505a0a4060130320801580b01a07c1500906a074050030100ac0580005a0980c00695efbc0a3ec0000a0130240440700d018,0x1048060c780005a098064b1960034b400f1180950901b41e08c7701716401a578110120141682901804c0c82005602c0681f0540241a81d01400c0402b0160001682603063df80147da000140260480880f01c0340600b00e,
0x103063c0880900a0b41480c0260641002b0160340f82a0120d40e80a0060201580b0000b41303e7ec054be8110120141682901804c0c80b01a07c1500906a074050030100ac0581728808ca302005606c8b80f230090be006,0x105a09c0c82101c03259c1b02833c0880900a0b41480c0260640580d03e0a80483503a0280180802e03c1580b04610c1303e0400ac0002d03201c0d02501c036593f702833c064b101e4601217c03645c030240465180b944,0x10420640382501f2d65980d9640440480505a0a40601303202c0681f0540241a81d01400c0401701e0ac058230860981f0200560001681900e0681280e9690680a4180000a01101e0380680b02a0240401280701402002002,0x100e06807cb696a0348f00e9680440480505a0a40601303202c0681f0540241a81d01400c0401701e0ac058230860981f0200560001681900e068129908320560e0000500880f01c03405809010018028040040040b41382a,0x102833c064b70000901101e0380a00b02a024040038190140200200205a09c1081a01d2e201814804000140240440780e01a02c0a80901000e0640500800800816827042038064b72320551400d23c0801582532000016819,0x184c0001402203c0700b02a0240400380a0100100102d04e0941081b03203806cba97003e5b0253200440480505a0a40601303202c0681f0540241a81d01400c0401701e0ac058230860981f0200560001681900e06a5cc04,0x10080081682704a084150190360325ecbb01b2e80002203c0700b02a0240400380a0100100102d04e0941082803206c074bc852052128000500880f01c02c0a80901004a06c050080080081682700e0840c80e0192ee15014,0x197a0001101e0380580781202001c05008008008168270500841501904a06e5fc2d0290a0000280440780e01601e0480800a0100100102d04e0941081b0320a80380d97d0ac0a4270000a01101e0380580781202001c05008,
0x19800911101a9720440480505a0a40601303202c0681f0540241a81d01400c0401701e0ac058230860981f0200560001681900e6465f80e9780000f01c02c0a80901000e028040040040b4138220420a00c8250373025f00c,0x10120d40e80a0060200b80f05602c1184304c0f81002b0000b40c8a7858030620140700440480505a0a40601303202c0681f0540241a81d01400c0401701e0ac05823086068630241800801582607c01cc880005a06407cc1,0x183a0001402203c0700c01605404808025036028040040040b413807042038064c214a068630241800801582607c0645380005a0186ec2401a0bc0a8c501f3040d0c6048300039910220240282d052030098190160340f82a,0x10040b41382a04206c1280c98b08c0a41f0000a01101e0380600b00f02404005008008008168270540840d80704a03662421028450064c20000880f01c030058150120200a00d80a0100100102d04e01c1082501d30e10014,0x19860000f01c030058150120200a01100a0100100102d04e01c1081b04a64a6280d9880001101e0380600b02802404005008008008168270540840d80701e09663422029078000280440780e01802c03c0901000e02804004,0x10380600b00e024040150070140200200205a09c1081b01932204014232035148253240186e80505a02c0680301008c21829018044048130320801581701e0981f01914e07c1500906a0740502b0160001681b01f31e6300e,0x105a09006cca99203e638253240000e01802c0a809010050088050080080081682700e0840f01b24b01c0a114019320000240440780e01802c0a00901005401c05008008008168270420380dcc980c052028000500901101e,0x18000001402a0440780e01a0300580701202001c1380a0100100102d042090064cb2fc0548880f11806c9280505a02c0681f05400c040230860a40601101204c0c80906a05c0782607c0740502b0160801581914e0186e800,
0x10380680c01601c0480802500e028040040040b41382105403266ccb01b3280788c0364940282d0160340f82a00602011843052030088090260640483502e03c1303e03a0281580b0400ac0c8a700c3740002d04933200814,0x10000b4154d099c0926600f11806c92800030058150120200a01100a0100100102d04e01c1081c03d33e0b015222032668000440780e01a030058070120200940380a0100100102d04e0841402a99d05c0a4150000a01101e,0x10160881284b04e2fc1480c0462f8158510121340e8eb01e230168000000840c00703403668cd005602c0002d00133c030dd03229c1184302e03c1303e0160340981903e0a8048350520300282d0400ac0e80a02202401808,0x104a12c138bf052030118be0561440484d03a3ac168000000840c00703534d710145ba0b4000000500981202203c0700d01802c0a80901000e028040210080080700c9a4b7c0a9110061e80284202e2c80f8ec0221100984e,0x10440780e01802c0a80901003601c050080080081082801d355778145d80b4000000500981202203c0700c0160540480801b00e028040040040840700c9a934806cd101e2300187a00a1080b8b203e3b00884402613805822,0x15e20517682d000000140260480880f01c0300580781202001c050080080081081b0540326baf2028bb8168000000a0130240440780e01802c03c090100140200200204206c0382a01b359780142280326a02d00000013024,0x103a3ac0b8b2012134028420061e8168000000840c007075360074d50000901101e0380600b02a0240400d80701402002002042098144d99ae0366b00004c0901101e0380600b00f024040050080080081081b00e0a0154d8,0x10080080b01a9b6bac0a89701a0bc078390160881282700618c1184a00a1400383a05203008844026064168000000840c0260100a80e01e02c06e6d4d903534c118be052030058220221101585104e2fc1284b0261380f8ec,
0x10300980402a03807a6ecdb0373680682f01e0e40582204a09c018630461280285000e0e81480c022110098190000840c0260100a80e01e02d3716e0155c20b4000000500981202203c070150180200480400e01802810806,0x10100a80e0de6120598182d000000140260480880d01803e0400902a0100380600a042018020020380526f2e40364100a81e02d3700682f01e0e40582204a09c018630461280285000e0e81480c0221100981905a00000021,0x104a09c018630461280285000e0e81480c0364140b943038378168000000840c0260100a80f8129bf3780a8990364140f4dd0221100981901a0bc078390160881282700618c1184a00a1400383a052030168000000840c026,0x1038378168000000840c0260100a80d4e06280410a01404a04a6f81728606c8280d05e03c1c80b044094138030c608c250050a001c1d0290180706f02d0000001081804c0201501f326c300884402a4080682f01e0e405822,0x10740001081804c020154e26040598082d000000140260480880f0180200500901d01c0300500800c0100102105406e70afd02e7940682f01e0e40582204a09c018630461280285000e0e81480c0221100982502a5300f993,0x10500981202203c0700d01802c0a80482101c03005006008008080129c61440e88805538816800000060108260102a27081a9c00442201304a054a601f3260706f0030c608c250290180142800d05e03c1c80b04409413807,0x10440941380707400c0d80509005c3d81b0fa08c4102910a0ac260081500b4000000420601301c03c4997001522604a7182d000000130240440a00e01a030058150090420380600a00c0100101e021391718145bc0b400000,0x10300581501f0120380600a00c0100102102004a7330802862c0682f01e0e40582204a09c0383a00606c0284802e1ec0d87d04620814885056130040a803c498168000000840c02603804009ce59c80448900d05e03c1c80b,
0x101c030050060080081082a01207c08ce89cc04e7280d05e03c1c80b0440941380707400c0d80509005c3d81b0fa08c4102910a0ac260081500789302d0000001081804c070084e760c0518202d000000140260480880e01a,0x10080081081d012044094ea9d004c698109ce0789300d05e03c1c80b0440941380707400c0d80509005c3d81b0fa08c4102910a0ac260081500b4000000420601301c9d2c140ab0705a0000002804c0901101c0340600b012,0x10440680c0160540a00700c014018020020420740481f0233b18a8146200b400000050098120220340600b02a01c030050060080081081f03a024088139d6c480a30e05a0000002804c0901101a0300581501f01c03005006,0x10120400fcef6220518682d000000140260480880d01802c0401501d01c030050060080081080903e04a77313028c3c168000000a0130240440680c0160200a80700c014018020020420740481f0273b6758129d400013024,0x10500981202203c0680c0160240740480e01802803004004084150109e33bc08cec0000901101a0300581502801c030050060080081081d0120980fcf09dc04e7680004c0901101a0300581402a01c030050060080081081d,0x10000001081804d3d2790131a007e780000440680c0160540a00700c014018020020420740482404d3cd800142b60427882d000000130240440780d01802c0480e80901c03005006008008108280553c97f8145fc0b400000,0x10280481400603202804021008008150169ed3d4134f400e0e8000210302406301b2a00906002d0000001080604f3d67981c9d20ac2602910a08c4101b0fa05c3d80509000c0d80815002c1102504e0341780f07201c1d02d,0x10c4054a50030f80243500b044094138270e00604802d000000108060346518581e3c805a7b02d0000001301a0440400e00e0180500902800c06405008042090010040553dd8501e5ca0b4000000480980d0220200700700c,
0x10220381585103a5040486a0302400d19405a0000002100c03a7c8c4028bcc168000000a0130240440780e0160540480801b00c028040190080081080e0193e27b81108804c0c8230940341781d3cc0a4060050a003c1c02b,0x107003a7c81101c0a4060130320ac288230e205c8201f284074a0805280068ca00b044094138030f8024350270e00604802d0000001080624f3e00682f0061f00582204a09c1387000a5000b9040461c40f9420260641480c,0x10500640381b01f3f17d0145ec0b4000000500981202203c0700b02a0240400380a010010010210360640780c9f6bf00a2f705a0000002804c0901101e03805815012020028040040040840d81900e03c06cfa5f603062014,0x10480880f01c02c0380901000e02804004004084150190360367f2f402abe0168000000a0130240440780e0160240400702a0140200200204201c0c81b0193f67d80d9f4000130240440780e0160540480800a01001001021,0x100c49c168000000840700da013fc07cfc0000901101e03805815012020028040040040841401900e0980d9289fc0327e80004c0901101e038058090100500a805008008008108070320380dcff5f20517a82d00000014026,0x101d409740145cc0b4000000500981202203c0700d01605404808007032028040040040840700ca02ba40a0cf0364a01480c00a1080585e0221fc13870026138158510121a80b8e803e3a81183103a2500187c0302401284b,0x1000000140260480880f01c0340580201202001c0500801e0081081905403281d0101b4000d928052030028420161780887f04e1c00984e0561440486a02e3a00f8ea0460c40e8940061f00c09004a12c0312705a00000021,0x10460c40585e0561440887f04a12c0984e03e3a80e89402e3a00284200c49c138700121a80187c05a000000210334168180d23c03a8101b2500001101e03805815012020028040040040841401900e090135045d40517382d,
0x11de094258210020b40000004c01c0cd0751c030880050840242681309c07c5e0110fe05c4a80b1de094258230620744a02b0c40a40d01511600c3d01a0d80840082d0000001300703203e83505030240000210034101480c,0x100403806d094ba0511702d000084008000500981202203c0700d01802c0a80901000e010050080040380650851a0348780fa0c0a40d02b0c4054458230620683601d12800c3d0050840242681309c07c5e0110fe05c4a80b,0x10440780e01a030058078120200280400400401c1500da17424065080000981202203c0700d01802c0a80901000e010050080040a00750a4c20511a82d000084008000480981502203c0700d01802c0a00901000e02804004,0x105143a8600da16000130240440780e01a030058078120200280400400401c1402aa1a9900a23a05a000108010000a01300f0440780e01a0300580501202001c120080080081500ca1899c0a23e05a000108010000a013024,0x105a0000002600e01a8701d3a40a4ed02317c00c3d0050840242681309c07c5e0110fe05c4a80b1de0942581b0da066838210020b40000004c01c1550fa1a03a850000480880f01c0340600b026024040038040140200102a,0x1014008030040560480d5107c603c7e00d18204c2301b0340643101704602c0f81521608d0081f2a2014e500700c00c500090980445081d1100b400021002000130240560a494a0005076c1550f02e2541284b03e2f010801,0x10500600b00c0100400a00a0040181202b00808a8939701e7e40d51005a000108010000901301e0380a00c01601802008014014008030040560880951172403dca02d0000840080004c0901101e0380a00c01601802008014,0x103c0700d01802c0500281001c0301400800c0081580a047451ce01b0e203cb30131ee08a8902d0000840080003c0701401802c03004010028098010060480ac05004a26e540d9fa01e7dc0951105a000108010000980f01c,
0x103c02a8bd150474500002403c0700d01802c0500281004c0301400800c0081580e015459cb0127260b4000210020001302400a0780e01a0300580a02b020038060280100180100a045454bd01273a0b40002100200013024,0x11140100f80004c0ac0b01f016659cf0122f203c690223ec06c4b00403e02a8b82d000084008000500600b01c0100400a0260040181202b018078cad1601e3480d89600944c0001c0500600b00c0100400a0260040181202b,0x11a402ccb01e32a0346080700c0445081d11006431015184024260031400a49482d0000840080004c0901581600b465cc8137360b400021002000130240440700d01802c05008028018028040060040ac0f80e00b4608b01a,0x102d4728d01b3f803cfd8231360168c80b32c078ca8000300a00e0080200501300200c0901581601946dcc0137340b400021002000130240200700d01802c0500400e0180280f8060500081580404546a8c02341c06c8b00f,0x10100180102b0460980b828a3c5e80939f05a000108010000981201c0340600a01f020038060050100180102b04605c1400aa3b46c068c100e018088a103a2200c86202a30814929012130018a0042004168000000981202b,0x100407c0b80e01747e8f01e41a06c8b00f1a4088fc00404603427816a38064310151840a49481d1100445080909800c5000700c0b40000004c09015807740048bc80aa3a0b4000210020001201c0340600a01f02003806005,0x1030050028100540300400600407c0b81a01d4856081257a0b400021002000140260480880e01a0300500f8100540300280800c0080b80e0154816101257c0b400021002000140260480880e01a0300500281005403004006,0x100a03e91d22026338075210000901101c0500600a0260200a80600800c0080f81700a068cbac0014afc168000420040002804c0901101c0340600a02a0200300280800c0080f81702403e9152001747c000260480880e028,
0x10254956980a5a40b400021002000140260480880e0180280400700c0360200300203e0a80b8050274916a80b2440488d81a32e01c030090680342781106c0540f0231340ac038210020b40000004c090140170300700101f,0x10500600a0260200a80600800c0080f81704401693d25027490000260480880e0180280400700c0500200300203e0a80b81b00b4996880a5a00b400021002000140260480880e0180280380801b0180a80400600407c0b805,0x101d4a45100a59e0b400021002000140260480880e0180280a80801b0180100400603e0080b81201d4a29382313401c0302b00e0241a01503c0342781106c0001302405005c0c01c00407c0292aa4c03e9181a32e0001201c,0x102e0600e00203e06e95ad6014b50168000420040002804c0901101c0300500800c01e0200300400407c1501703604e9552802611c0380605601c0483402a0780684f0220d81189b00a4a8000260480a00b8180380080f81b,0x106c0001302405005c0c01c00407ccc15901caf0168000420040002804c0900a01c0340600f8120200880602a0100180101700802a9652a0245640752900e018158070120d00a81e01a13c0883604626c0292a00009812028,0x101c0600a0120200a00600800c05c010040454b93a00b4ee0b400021002000140260480a80f01c01c0600a0120200100600800c05c010220354b69601317002c7a81ba5608c4d80525401c0302b00e0241a01503c03427811,0x10454b8000240540780e00e030050130100500300400602e00809004a60c640531805a000108010000a01302403c0700d0180280480800e0180a80400602e00802023a5ea24058f30354b416800042004000260480a80f01c,0x102e0380dd334f20293b02d000084008000500981201203c070110180280140802a01805c040060040380d532a6004c2380f3a001c0302b00e0241a01503c0342781106c07ccc00004c0901401703007001004a634bc0d849,
0x10500780e022030050028100540300b80800c09801012a6b4cc0d5320000981202803c070110180280140802a01805c04006004048075342de0294502d000084008000500981201203c0700c0140540401100c00a02003002,0x106c0342780700c0ac038090680540f00004c09014017030070015374f603c7f80b2da06d05012a6a0b4000210020001401e0380880c01400a0401502402e0200302601800a9b28b0345b0050ff01d4d01680004200400024,0x12d60293d02d000084008000500981202203c0700d0180280480800e02e0200300405400c06d394f00293a82d000084008000500981202203c0700d0180280480800e00605c0400605401006538a6c08c4d004a6207ccc011,0x105005c0c0030214ee9d0131000448001f1e806c5d02317a03c780051ce00a9b80700c0ac038090680540f0210020001302405005c0c01c2574e4065380000981202203c0700d0180280480800e05005c0400605400c0253a,0x10074f54e80a5380b4000210020001402604805c0901a0300500e80e01807804006008088150030234f14d80b2e001c0300517603c3002b00e08c2281304a0540f00906807c8181b174034b881c2560840082d00000013024,0x1258a680dab605a000108010000a01302402e0780c01402404007002014020030040440a80e80ca7d4f00853b01a5c40d8ba00e018028bb01e180158070461140982502a0780483403e40c0e12b042004000260480a00b818,0x1a80aa405aab05a000108010000a0130240440780d014024074070190100180200202e0a80800ca7f4f806955016260088360074f40f9030260941184501e180028bb0384ac0380605601c0483402a078000260480a00b818,0x100c01001017054044065425680295902d000084008000500981202203c0680a01201c064040060080080b82a03a04406d4155c028aa80ca7e0b400021002000130240440780d014024074070190100180202802e0a801010,
0x1021500000240440780d014024098070190100180202802e0a80e80233350806d410000981202203c0680a01201c064040060080a00b82a03a00808d434260295802d000084008000500981202203c0680a01201c0740c808,0x123a008cc82b00e0241a00f07001c030131700145c81503c07c5181b2020609602308a0840080004c0901401703a046a2ab101aacc168000420040002804c0901101e0340500900e0320200300402e0a80181d02202aa2543,0x102e0a01500303b5215600d55e0b400021002000140260480880f01a0280480c80e0100180201702000c1501d01751d5500d55a0b400021002000140260480880f01a0280480800e0320200300402e00c1501d01551aa200b,0x106803c1c01503c01c0301317006c80805172060960210020001302405005c0ed4aa90046a2802332000110240340500902601c064040060080a00b82a03c076a4d47015518000260480880f01a0280480800e03202003004,0x12dc0314002d00008400800050098120170540700d01402407807019044020030040060400554c5020354102d00008400800050098120170240700d0140320a80700800c0100f02200604005d4ba9207c5182308a0ac03809,0x10280641500e0100180201e04c0a011003a9ea140528405a000108010000a01302401805c0e01a0280480701903c020030040440a801811a9d53005d4b000098120170240700d0140320a80700800c0100f02205000c0854d,0x1aa002c2f00d09e00ea780002e0480e01a0280641500e0100180202404c0a00f022aa2a0c0827f05a000108010000a01302402e0300e01a0280481100e0080180401903c0a80100aaa1538068890215340002402e0480e01a,0x107006c808051720609601503c0241a00700c0ac038210020001302405005c0c2c40163d40886f01a204018f403d54416800042004000120380680a019054038040060080901302802e08aa90f90062f40002405006411865,
0x11be74c168000000940292e29a084008000380240f99b1e80840080004800c0f92d296084008000120780e99a3a20840080000c0340d8531740840080005000c0d8a91720840080004c06402873aa408c3281da9404c5c00f,0x13b20b400000052014ce07005a00000027032044ec02d0000001380d02875c108010000901380902a2fc1680000009c038103ac0b40000000609c0995005a000000250360c8ea8210020001281c0260fcea02d0000001280f,0x104a09c0e00933e77c168000000540980f33c220168000000ac0ed551420b400000056044550c10420040001c05605806d540980b400000056024ce8a005a0000000305754ca882d0000001481f0cc214168000000a404854,0x12e8084008000120740ad5a2e6084008000200240e813ab25c8108010000240901f022684fe82d00000015825047560fa02d0000001382904755cf80210020001200c0060a40dd563dc0840080004e094119a03da08400800,0x1abc8b0168000420040002804c0901101e0380680c0160280480700c0080180400a05404001d5d4560840082d000000130240340780e01603004006028054050040220140180200202403aae20b0420040001d01005409d5b,0x10280380800c0100180200201604ab022f05a000108010000a8110260480480f01c0340600b0100120300a02800c0100100a01d57d1682d000084008000540a01302400a0780e01a0300580a00c0200380302201000805012,0x10540a0130240440780e01a0300580a00502002c0600800c0080900eac48c4168000420040002a0500981202203c0700d01802c0500901001c00c0400601801005d614600b4000210020001502804c0901101e0380680c016,0x100403405d654680b4000210020001502804c0901101e0380680c0160280480800e00602003004014036b223305a000108010000a8140260480880f01c0340600b0140240400500800c0100100e01b58d1902d00008400800,
0x10340400b00a0100301201400c0100101201f59d1b82d000084008000540a0130240440780e01a0300580a012006038040060080400580dacc8d8168000420040002a0500981202203c0700d01802c0500901001c02003004,0x10420040002a0500981202203c0700d01802c050090100180200300400402c07d694720b4000210020001502804c0901101e0380680c0160280480800c00a0200300201403eb423805a000108010000a8140260380880f018,0x10100180201e02202ab623d05a000108010000a8140260480880f01c0340600b0140240400500800c0100100f01b5ad1e02d000084008000540a0130240440780e01a0300580a012020030040060040140580fad48ec16800,0x10240780e01a03005808809018050140060080080700aadc900168000420040002a0500981202203c0700d01802c0500900e01800c0400600802808d6d47e0b4000210020001502804c090110140380680c01602403806002,0x14860b4000210020001502804c0901101e0380680c0160280480700c01001802003016046b824205a000108010000a8140260480880f01c0340600b0140240380880800c0100100c0175bd2082d0000840080005408813024,0x1024038040060080080581101b5cd2282d000084008000540a0130240440780e01a0300580a01201c0440400600800c0500dae4910168000420040002a0500981202203c0700d01802c0500900e0220200300400402806d71,0x10500981202203c0700d01802c0500900c0140200300400404407d7548e0b4000210020001502804c0901101e0380680c00d0280480700800c01005816006046ba24605a000108010000a8140260480880f01c0340600b014,0x101c02abc24a05a000108010000a8140260480880f01c0340600b014024028040060080080880f01b5dd2482d000084008000540a0130240440780e01a0300580a012018020030040040440780baec920168000420040002a,
0x10300580800901c0300200600405005013af4930168000420040002a0500981200503c0700d01802c0500800e0180880400600402809d794960b4000210020001502804c0900801e0380680c01604404c0600401001801014,0x10020001502804c0901101e0380680c0160280400700c0100180100501604ebe24e05a000108010000a8140260480880f01c0340600b01402004c0600800c0100100e0175ed2682d000084008000540a0130240440780e01a,0x100c0100100a0275fd2882d000084008000540a0130240440780e01a0300580a01001c0200300400404c0680bafc940168000420040002a0500981202203c0700d01802c0500800e0140200300400404c06d7d49e0b400021,0x103c0700d01802c0500800c0100180200201e02c09d814a60b4000210020001502804c0901101e0380680c0160280400600f0100180100501404ec025205a000108010000a8140260480880f01c0340600b01402003007808,0x105a000108010000a8140260480880f01c0340600b014020028040060080080980f01b60d2a82d000084008000540a0130240440780e01a0300580a010018020030020260140580fb04950168000420040002a05009812022,0x10140200300400404c0880db0c960168000420040002a0500981202203c0700d01802c0440700c0140180200201205009d854ae0b4000210020001502804c0901101e0380680c0160100380600a02601802002028046c2256,0x104c0901101e0380680c016028028040060080080981101e036c425a05a000108010000a8140260480880f01c0340600b014018028040060080080981101f61d2c82d000084008000540a0130240440780e01a0300580a00e,0x101762d2f02d000084008000540a0130240240780e01a0300580800901c0300500600800811015b14970168000420040002a0500981201e0380680b0180200480700c014020030040040880ad894b60b40002100200015028,
0x102c0480800e0100180200202a03405d8d4c00b4000210020001502804c0901101e0380680c0160240400700a0100180200202a036c625f05a000108010000a8140260480880f01c0340600b0120200380600800c01001015,0x10000a8140260480880f01c0340600b012020030040060080080a80f01763d3182d0000840080005403c130240440780e01a030058090100500280400600800806015b1c988168000420040002a0500981202203c0700d018,0x10040240a811b249a0168000420040002a0500981202203c0700d01802c0200700c0140540300400404808d914cc0b4000210020001502804c0901101e0380680c0160240400500800c0100100f02a036c826505a00010801,0x10380680c0160240300500800c0100101502203eca26a05a000108010000a8140260480880f01c0340600b01201c030040060080080a81101764d3482d000084008000540a0130240440780e01a0300580900e01802803004,0x1000084008000540a0130240200780e01a0300580400e018028110060080080a813b2c9b0168000420040002a0500981202203c0700d01802c0480600800c0100101502203c05d954d60b4000210020001502804c0901101e,0x10100180200202a04c06d994de0b4000210020001502804c0901101e0380680c0160200380600800c0100101502602ecc26e05a000108010000a8140260480880f01c0340600b01001c030050060080080481302b65d3682d,0x10480880f01c0340600b00e018028098060080080401502366d3882d000084008000540a0130240440780e01a0300580800e0100180200202a04c0680bb349c0168000420040002a0500981202203c0700d01802c0400700a,0x1b3c9f0168000420040002a0480980a01a03c0700b00c0240a007002044020030040320400559d4e60b4000210020001502804c0901101e0380680c01601c030050060080080880902a04ece27205a000108010000a814026,
0x105006c060220100180200201c02ad027e05a000108010000a8140260480880f01c0340580a00401c0300500800c0640101202367d3e82d000084008000540a0130240440780e01a02c0500901000c028040190080080700d,0x10540a0130240440780e01802c0500801b0180280400600800807013b44a1c168000420040002a0500981201e0180700c0160280480801b0440200300400402807da150c0b4000210020001502404c0500c01e03805808012,0x1008030055a551e0b4000210020001501a04c0900b00e0300480a01e03a028060280100180200202008ad228c05a000108010000a8140260480880f01c02c0500d810018018050080320100101201d68d4402d00008400800,0x10300580a0120200380500800c0100e80201b69d4882d000084008000540a0130240440780d01802c0500901001c0740400600800c0600bb4ca40168000420040002a0500981202203c0680c0160280480800e00607404006,0x10420040002a0500981202203c0680c0160280480e80e0100180200b00604006da95260b4000210020001502804c0901101e0340600b0140240400701d01001802003014036d429205a000108010000a8140260480880f01a,0x100c01005803024046d629605a000108010000a8140260480880f01a0300580a01101c0300500800c0100181203b6ad4a82d000084008000540a0130240440780d01802c0500400e0180280e80600800809011b54a5016800,0x10440780d01802c0500900e010018020110060740680bb5ca60168000420040002a0500981202203c0680c0160280740700a0100180200d00604808dad52e0b4000210020001502804c0901101e0340600b01403a03806008,0x153e0b4000210020001502804c0901101e0340580a0120180380e8190100180200302002ad829e05a000108010000a8140260480880f01a02c0500901001c0740c80800c0100100c0156bd4c82d000084008000540a013024,
0x103a06404006008034018100156cd5082d000084008000540a0130240440780d0160280480e80e0320200300401600c0800cb64a80168000420040002a0500981202203c0680b0140240740701901001802002016040065b1,0x10500981202203c0680b01402403806019010018020110060280edb55460b4000210020001502804c0901101e0340580a0120320380400600803405803020076da2a205a000108010000a8140260480880f01a02c0500900e,0x1014076dc2a605a000108010000a8140260480880f01a02c0500900e032020030040040440680a03b6dd5282d000084008000540a0130240440780d016028048070190100180201101600c0601db6ca90168000420040002a,0x10280480e80c0100a0150060080080800ab74aa0168000420040002a0500981202203c0680b014024038040060080440680b0060640edb954e0b4000210020001502804c0901101e0340580a01201c0640400600804406803,0x10020001502804c0901101c0340600b01400a0400700c03e0200300201404ade2b705a000108010000a8110260480580d0180240400701c0180501400800c0100101f0156ed5a82d0000840080004406c1302402c0780c00e,0x100c0080f80a0276fd5d02d000084008000540a0130240200700f81802c0500401a0180281100600800807013b7cae4168000420040002a050098120220380680c0160280480800c0080200301f00402807dbd5700b400021,0x10380600b0140240400d80c0080200301f004038055c15860b4000210020001502804c0900b01c03407c0a012008038060220100180c80202002ae02bb05a000108010000a8140260480880e01a0300580a01001c03002808,0x105a000108010000a8140260480880e01802c050070100360300400600407c0281201770d6302d000084008000540a0130240440700c0160280380801b0180140400600407c0900ab84b14168000420040002a05009812022,
0x10360200300203e01405013b8cb24168000420040002a050098120220380600b0140240400600800c0080f81b00a02c07dc55900b4000210020001502804c0901101c0300580a0120200300d80800c0080f80501403ee22c7,0x104c0901101c0300580a01001803c040060080080f81b01404ee42cb05a000108010000a8140260480880e01802c0500801b0180200300203e0140580e02771d6502d000084008000540a0130240440700c0160280400700c,0x103f72d6702d000084008000540a0130240440700c0160280400600800c0080f81b0260140580fb94b34168000420040002a050098120220380600b0140200300780800c0080f81b00a02809dc95980b40002100200015028,0x101c030050060080080f81d01205009dcd5b00b4000210020001502204c0900901a0300580801f03a0380600a00c01001028012052e62d705a000108010000a0130240440680c0160280480800801c0300e82a00c0100100a,0x10000a8140260480880b0140240400700c0140200300400407c0c81d03773d6d02d000084008000540a0130240440600b0140240400700c014020030040040740f81bb9cb64168000420040002a050098120220340600b011,0x100800811025ba4c5c168000420040002a0500981201e0380680c0160280480800e0180200300400402c11dd162c0b4000210020001502804c0780e016030050080120100380601a0480180200204602ae82db05a00010801,0x10340600b0140240380600a01001802002038046ea31b05a000108010000a8140260440780e01a0300580a0120200940500800c0100100e01b74d8d02d000084008000540a01301e0380680c0160280480800e01802804006,0x1000084008000540a01301a03c0700701604a0480800601a0200c80400408805014bacc74168000420040002a0500980d01e0380380b014024040128060440200c804004028065d56380b4000210020001502804c0880f025,
0x10140200300400609411dd96400b4000210020001502804c0780e01a0300580a01204a028060100100180200201c08eec31f05a000108010000a8140260440780d01802c0500902501c0300500800c0100101003b75d8f02d,0x103c0700d01802c0500900e018028040060080081281104776d9102d000084008000540a01301e0380680c0160280480800e0100180200d01600c12823bb4c84168000420040002a0500980f01c0340600b0140240400700c,0x1bbcc94168000420040002a0500980f01c0340500901001c0200300403205c0680b00609411ddd6480b4000210020001502804c0780e01a0280480800e018028040060080640b80304a08eee32305a000108010000a814026,0x10240400300a0100300200204e092f032705a000108010000a81402203c0700d01802c0500901001c0300500800c09c0100404977d9302d000084008000540a01301e0340600b0140240400700c014020030040040941181d,0x10540a01202203c0700c0160360480800c00c0280402700800807014bc4ca4168000420040002a0500901101e0380680c016020030070060140201380202801009de16500b400021002000150280280880f01c0340600b00f,0x100401011de56580b400021002000150280480880e01a0300580a0120200380600a0100181380200807ef232b05a000108010000a81402403c0300e01802c05009010036028040060080081382201f78d9502d00008400800,0x10520400900801c0300502600c0100b00202979d9702d000084008000540a01101e0380680c0160280480802500c09c0600e00800805008bcccb4168000420040002a0180900f01c0340600b0140240400700601402013828,0x10420040002a04c0901101e0380680c016028048080290140200300400403806de96600b400021002000150260480880f01c0340600b0140240400700c014020030040060a6f432f05a000108010000a81202203c0700d018,
0x1010018020030240a6f633305a000108010000a8130240440780e01a0300580900801c0300502900c010010140237ad9902d000084008000540981202203c0700d01802c0501481001c0200300401600c0900dbd4cc416800,0x103c0700d0160280480800e052028040060080080c80cbdccd4168000420040002a04c0901101e0380680c016028028070290100180200302403408ded6680b400021002000150260480880f01c0340600b0140220380600a,0x16700b400021002000150260480880f01c0340a40c81001c0200300402e0480181401a02ef833705a000108010000a8130240440780e01a0280480800e0520280400600805c018190197bd9b02d0000840080005409812022,0x10180280e806008008040290237cd9d02d000084008000540981202203c0680c0160280480800e0180280400600800c1481dbe4ce4168000420040002a04c0901101a0300580a0120200200700c014078030040040a40edf1,0x104c0901101e0340580a0120200380600a010018020190060a40edf56780b400021002000150260480880f01a0300580a01201c0300500800c01014803022076fa33b05a000108010000a8130240440780d01802c0500900e,0x1052096fc33f05a000108010000a81302403c0700d01802c0500901001c0a40500800c008060040477dd9f02d000084008000540981202203c0680b0140240380500800c0100c81101a00c1481dbeccf4168000420040002a,0x10280480800e0180200300400402c14825bf4d04168000420040002a04c0880f01c0340600b0140240400700c014020030040060a412df96800b400021002000150260440780e01a0300580a0120200380600a01001802002,0x1002000150260440780e01a0300580a0120200380500800c01006803052096fe34305a000108010000a81302203c0700d01802c0500901001c0300400600802c0182904b7eda102d000084008000540981101e0380680c016,
0x102202c0182904b7fda302d000084008000540981101e0380680c0160280480700c0140200300402200c14825bfcd14168000420040002a04c0880f01c0340600b0140240400700800c0100680b0060a412dfd6880b400021,0x10340600b0140240380500800c0100880d0060a412e016900b400021002000150260440780e01a0300580a01201c028040060080080880d0520970034705a000108010000a81302203c0700d01802c0500900e01802003004,0x105a000108010000a81302203c0680c0160280480800e018028040060080a40182503b80da502d000084008000540981101e0380680c0160280480700800c0100880d01600c14825c04d24168000420040002a04c0880f01c,0x100c0101481702200c1281dc0cd34168000420040002a04c0880f01a0300500901001c0300500800c010148170060940ee056980b400021002000150260440780d01802c0500900e018028040060080a4128030220770234b,0x10440780d0160280480800e018028040060080081481904a0770434f05a000108010000a81302203c0680c0140240380600800c0101481702202c0182503b81da702d000084008000540981101e0340600a01201c03005008,0x103b82da902d000084008000540981101e0340580a0120200380600800c0101481901600c1281dc14d44168000420040002a04c0880f01a02c0500901001c0300500800c010148190060940ee096a00b40002100200015026,0x1018028040060080a40c8110060940ee0d6a80b400021002000150260440780d0160280480800e010018020290320340580304a0770635305a000108010000a81302203c0680b0140240400700a0100180202903203401825,0x10000a81302203c0680b0140240380500800c010010290320440682503b83dab02d000084008000540981101e0340580a01201c030040060080a40c81101600c1281dc1cd54168000420040002a04c0880f01a02c0500900e,
0x102e00c1281dc24d64168000420040002a04c0880f01a02c0500900e010018020290320440680b0060940ee116b00b400021002000150260440780d0160280480700a010018020290320440680304a0770835705a00010801,0x102c0500901001c0300500800c0100102904a08f0a35b05a000108010000a81302203c0680a01201c028040060080a4128170220340181903b84dad02d000084008000540981101e0340500901001c0300500800c01014819,0x1000084008000540980f01c0340600b0140240400700c0100180200205202c12823c2cd74168000420040002a04c0780e01a0300580a0120200380600a0100180202900609411e156b80b4000210020001502603c0700d018,0x10080081480d01609411e196c00b4000210020001502603c0700d01802c0500901001c028040060080a40680304a08f0c35f05a000108010000a81301e0380680c0160280480800e0180200300405202c0182504785daf02d,0x10380680c0160280480700c014020030040040a41281104786db102d000084008000540980f01c0340600b0140240400700800c0101480d01600c12823c34d84168000420040002a04c0780e01a0300580a01202003804006,0x1c3cd94168000420040002a04c0780e01a0300580a01201c030040060080a41280b00604411e1d6c80b4000210020001502603c0700d01802c0500900e018028040060080a41280302208f0e36305a000108010000a81301e,0x1010018020020520940680b02208f1036705a000108010000a81301e0380680c0160280480700a0100180202904a0340181104787db302d000084008000540980f01c0340600b0140240380500800c0100102904a03408823,0x10540980f01c0340600a0120200380600a0100180202902e00c12823c44da4168000420040002a04c0780e01a0300580a01201c020030040520940680b00604411e216d00b4000210020001502603c0700d01802c0500900e,
0x100609411e256d80b4000210020001502603c0700d0180280480800e0140200300405205c0680304a08f1236b05a000108010000a81301e0380680c0140240400700c0100180202902e02c0182504788db502d00008400800,0x1020038040060080a40c81701a02c0182504789db702d000084008000540980f01c0340500901001c030040060080a40c81701600c12823c4cdb4168000420040002a04c0780e01a0280480800e018028040060080a40c817,0x10420040002a04c0780e01a0280480700c0100180202904a05c0880b00606411e296e00b4000210020001502603c0700d0140240380600a0100180202903205c0880304a08f1436f05a000108010000a81301e0380680a012,0x1052094058030460771637305a000108010000a81301e0340600b0140240400700c014020030040520940182303b8adb902d000084008000540980f01a0300580a0120200380600a010018020020520941181dc54dc416800,0x10300580a012020038040060080a41280d01600c1181dc5cdd4168000420040002a04c0780d01802c0500901001c028040060080a41280d00608c0ee2d6e80b4000210020001502603c0680c0160280480800e01802003004,0x16f00b4000210020001502603c0680c0160280480700c0100180202904a044058030460771837705a000108010000a81301e0340600b0140240380600a0100180202904a0440182303b8bdbb02d000084008000540980f01a,0x1010018020020520940c82303b8cdbd02d000084008000540980f01a0300580a01201c020030040520940880d01600c1181dc64de4168000420040002a04c0780d01802c0500900e014020030040520940880d00608c0ee31,0x104c0780d0160280480800e018020030040520940c80b00608c0ee356f80b4000210020001502603c0680b0140240400700c014020030040520940c8030460771a37b05a000108010000a81301e0340580a0120200380600a,
0x10460771c37f05a000108010000a81301e0340580a012020038040060080a41281901a02c0182303b8ddbf02d000084008000540980f01a02c0500901001c028040060080a41281901a00c1181dc6cdf4168000420040002a,0x1014020030040040a4128190220341181dc74e04168000420040002a04c0780d0160280480700c0100180202904a0640880b00608c0ee397000b4000210020001502603c0680b0140240380600a0100180202904a06408803,0x10020001502603c0680b014024038040060080a412819022034058030460771e38305a000108010000a81301e0340580a01201c028040060080a4128190220340182303b8edc102d000084008000540980f01a02c0500900e,0x103205c0582303b8fdc302d000084008000540980f01a0280480800e018028040060080a41281902e00c1181dc7ce14168000420040002a04c0780d0140240400700c014020030040040a41281902e08c0ee3d7080b400021,0x10240400700a0100180202904a0640b80d00608c0ee417100b4000210020001502603c0680a0120200380600800c0101482503205c058030460772038705a000108010000a81301e0340500901001c0300400600800814825,0x105a000108010000a81301e0340500901001c020030040520940c81701a02c0182303b90dc502d000084008000540980f01a0280480800e010018020020520940c81701a02c1181dc84e24168000420040002a04c0780d014,0x10520940c8170220341181dc8ce34168000420040002a04c0780d0140240380600a0100180202904a0640b81100608c0ee457180b4000210020001502603c0680a01201c0300500800c0100102904a0640b8110460772238b,0x103c0680a01201c020030040040a41281902e0440680b0460772438f05a000108010000a81301e0340500900e014020030040520940c8170220340182303b91dc702d000084008000540980f01a0280480700a01001802002,
0x103592dd082d000084008000500980401e0380680c0160280481280c0440ac010060080400500ec94e44168000420040002a0480380f01c0340600b0140240401480601409c06004004020116497200b40002100200015026,0x10240400700c0100180102b04e02c02e4d7460b400021002000140240440780e01a0300580a0120200380600a01001801027056017263a205a000108010000a01202203c0700901802c09c0800201c0500500800c0101580c,0x10000a01202203c0700d01802c0500800e018028040060040ac1381300b93dd282d000084008000500901101e0380680c0160280480800c0100180102b04e0140580fc9ce9016800042004000280480880f01c0340600b014,0x104e0140980fca4ea016800042004000280480880f01c0340600b0140200300500800c0100102b04e04c07e5174e0b400021002000140240440780e01a0300580a01001c030040060040ac1380501604f283a605a00010801,0x10280480800e018028040060040ac138170360172a3aa05a000108010000a01202203c0700d01802c0500800c0100180102b04e04c0280b01f94dd482d000084008000500901101e0380680c0160280400600a0100180102b,0x1000084008000500901101c0340600b0140240400700c0140200300205609c0f805caceb016800042004000280480880f01c030050090100180200300205609c0d81700a02c07e557560b400021002000140240440780e018,0x10040ac1381f02e04c02e5975e0b400021002000140240440700d0180280480800e018028040060040ac1381703e0172c3ae05a000108010000a0120220380680c0160280400700c0140200300205609c0f81300b95dd682d,0x10380600b0140240400700c014020030040040ac1381f03796dd882d000084008000500901101c0340600a01001c030040060040ac1381f02e01405813cb4ec016800042004000280480880e01a0300500800e01802804006,
0x1cbced016800042004000280480880e01802c0500901001c030040060040ac1381f00a02c0de5d7660b400021002000140240440700c0160280480800e018028040060040ac1381f0360172e3b205a000108010000a012022,0x10100180200205609c0f81b02603f303b605a000108010000a0120220380600b0140200380600800c0081582703e06c0280b02797dda82d000084008000500901101c0300580a01001c0300500800c0081582703e0140d813,0x10500901101c0300580a0100180200300205609c0f81b0260140580fcc4ee016800042004000280480880e01802c0500800c0140200300205609c0f81b00a04c07e6176e0b400021002000140240440700c0160280400600a,0x104e0ac11e657760b400021002000140240440700c0140200300500800c0081582703e06c0b80502603f323ba05a000108010000a0120220380600a0120200380600a0100180102b04e07c0b81b00b98ddc82d00008400800,0x10280480800e0180200300205609c0280b04799dde82d000084008000500900f01c0340600b0140240400700c0140200300205609c11805cccef016800042004000280480780e01a0300580a0120200380600a01001802002,0x1042004000280480780e01a0300580a012020030040060040ac1382300a02c07e6977e0b4000210020001402403c0700d01802c05009010018028040060040ac1382301e017343be05a000108010000a01201e0380680c016,0x10040ac1382302603f363c205a000108010000a01201e0380680c0160280400700c0100180102b04e08c0280b0279ade082d000084008000500900f01c0340600b0140200380600a0100180102b04e01411813cd4f0016800,0x10340600b014020030040060080081582704603c05813cdcf1016800042004000280480780e01a0300580a010018028040060040ac1382300a04c07e6d7860b4000210020001402403c0700d01802c0500800c01402003004,
0x178e0b4000210020001402403c0700d0180280480800e018028040060040ac13817046017383c605a000108010000a01201e0380680c0160280400600800c0081582704604c0280b01f9bde282d000084008000500900f01c,0x10140200300205609c0f82300b9cde482d000084008000500900f01c0340600a01001c0300500800c0081582704605c09805ce4f2016800042004000280480780e01a0300500901001c030040060040ac1382302e02c02e71,0x10480700d0180280480800e018028040060040ac1382302e07c02e757960b400021002000140240380680c0160280400700c0140200300205609c1181f0260173a3ca05a000108010000a01201c0340600b0140240400700c,0x101603f3c3ce05a000108010000a01201c0340600a0120200300500800c0081582704607c0b80f00b9dde682d000084008000500900e01a0300500901001c030040060040ac1382303e05c05805cecf301680004200400028,0x101c0300500800c0100102b04e07c1181bcf4f4016800042004000280480700d0180280400700c0100180102b04e08c0f81700a02c09e7979e0b400021002000140240380680c0140240400600800c0081582704607c0b805,0x1002000140240380600b0140240400700c0100180102b04e08c0f80501606f3e3d205a000108010000a01201c0300580a0120200380600a0100180102b04e08c0f81b00b9ede882d000084008000500900e01802c05009010,0x104607c0281b0279fdea82d000084008000500900e01802c050090100180200300205609c1181f0360140580fcfcf5016800042004000280480700c0160280480800c0140200300205609c1181f00a06c07e7d7a60b400021,0x10280400600a0100180200205609c1181f03604c07e817ae0b400021002000140240380600b0140200380600800c0081582704607c0d80501604f403d605a000108010000a01201c0300580a01001c0300500800c00815827,
0x105a000108010000a01201c0300580a0100180200300205609c1181f03604c0280b01fa0dec82d000084008000500900e01802c0500800c0140200300205609c1181f0360140980fd04f6016800042004000280480700c016,0x105609c1181f00a05c0d80bd0cf7016800042004000280480700c0140240400700c0140200300205609c1181f02e06c02e857b60b400021002000140240380600a0120200380600a0100180200205609c0f81704606f423da,0x10380600a01001c030040060040ac1382303e06c0b80501604f443de05a000108010000a01201c0300500800e018028040060040ac1382303e0140b81b027a1dee82d000084008000500900e0180280480800e01802003002,0x1027a2df082d000084008000500900e0180280400600a0100180102b04e08c0f81b02e0140980fd14f8016800042004000280480700c0140200300500800c0100102b04e08c0f81b02e04c07e897be0b40002100200014024,0x101c0300500800c0100102b04e0a412e8d7c80b4000210020001202203c0700d01802c0500901001c0300500800c010010270560a7463e205a000108010000a01201c0300500800c0100180200205609c1181f03605c0780b,0x102c0280902801c0081100800c0100c81e019a3ee00110de0344082b00e014398090ba04c2f8230ca02c2f00306e05c0c00f07001c0300004c090140190380500d01fd1cf94168000420040002203c0700d01802c05009010,0x10480a00c81c02806b49690019a3c000260280901501c02c0280902801c0081100800c0100c81a03da4444810b3c000140260480880d01c01c0580a012054018050080320100101e01ba42cf810b3a000120260280681501c,0x102ba4ed181101c07cf180d0a606b4900f07001c0302b00e014398090ba04c2f8230ca02c2f00306e05c0c00004c090140190380507069103fa381580700a1cc0485d02617c118650161780183702e0600783800e01800026,
0x103a0380c80800c0101500c0040434a5cf016288089c503c780068530063a41580700a1cc0485d02e0600985f046194078380383800a85500e018000260480a00c81b25fa4c0d14a0000180c8150aa14c060c40000180c81b,0x103400c0b0140240a80701d0320200300403c03008696d28044ab82b00e014398090ba05c0c0130be08c3280f07007c5181b25e070700150aa01c0300004c0901401901800b4adaf0176c40002804c0901101e0340580a012,0x100e018000260480a00c80cd33a5c08696000098120220340a00b0140240a80701d0320200300403c00c06698b6c02ada8000500981202203c0740b014024038060190100180202a03400c08e97b6402ad800005009812022,0x10540580a01201c0740c80800c0100681e0060434ddb80176e40002804c0901101d0320580a01201c020030040540340f01a0060474d698005a541580700a1cc0485d02e0600985f0461940783803e28c0d92f0383800a855,0x1000098120280320cedb80b300040ab003d380001202203a0640b014024038040060080a8068260500780d69dd360474d00004c0901101d0320580a01201c020030040540340f02803400f4e5b40156cc0002804c0901101a,0x1021a7ed38112a802c4c00700c05c0c0190660145b00f0c004c128090d60ac0381f10208c2280004c090140140340340e802d3da740669903e28c0d92f0383800783802a1540985f0461940485d00a1cc0380605601c0b818,0x10480880681a0300580a01203a038040060080a01500303da86d700ab5a000140260480880f01a0300580a01d01c00c0400600803415012023a82d400bb52000140260480880681a0300580a01203a0380400600800c1501e,0x100604351d720175d00002804c0901101e0380680c00d0280480700800c01015016006047516a1005a780f8810260941184501e1800380602e0600c83300a2d80486b05601c000260480a00a01a01a074d16a0021a7c00026,
0x1050098120220380340d01802c050090020540200300403c038086a5d460475100004c0901101e0380680c00d0280481400800c0101501601c00f525640175980002804c0901101c01a0680c0160280481500e0100180201e,0x10300340a026050020030040540580900ed51a98086a5000098120220380340d01802c050090280540200300403c008076a7ae202eb9800050098120220380340d01802c0500900e0100180202a03c00808ea6aca02ab1800,0x10080080680f015aab5480b3ba00c7800ed50000110240380680c00d0280981400800c0101501603c048d1d770215ac0002804c0901101e0380680c0160280480780d0100180202a00402b54ea7007a90000240440780e01a,0x10300580a00e0040a8040060080340980ad59aa8059bb006200091a303e2040b81800a2d8038060121ac158070320cc0e9a2000098120280280680682201faaec4010b06000140260480880f01c0340600b01405404c04006,0x1034034116afd5a03f55803100048d18000480700d01801a050130280100180202a02c0880f6aeafc0447f00ad58000130240440780e01a0300580a00e0500a80400600803401013d5b6180857d0000a0130240440780e01a,0x10500500d02312374005dd10000a01302403c0700d01802c0500901001c030040060080a801023d603d8018bd045abc000240500501301a01a1d35701f10201c030170300641980516c0243582b00e074d100004c09014014,0x10540780100800c0100e00e023acab000aab8000120120380300b01803c0681402a0280201102600c0100100e021ac75801f136074228131ee0441300f29c0244100513400c5e80700c0ac038170300641980d0e800013024,0x101e0435ad760155d40002804c0901101e0380680c0160280480602a0100180200201e0475a6b2021ac4000240380300b01803c0681402a0280201102600c0100101201daceb780aad8000140260480880a00c0340600b012,
0x1d660000e00c02c0601201a0500a80a00804409803004004078091a4d6a0475a00004c0901101e0380680c0160280a00602a0100180200202403f5b5670175a40002804c0901101e0380680c0160280481500c01001802002,0x100009812028028068010080380100f011d7161c058fe021adc000260480880f01c0340600b0140540301400800c0100101301e696c080aafe000140260480880f01c0340600b0140540300980800c0100100f021adf5b00e,0x101e694000240440980e01a0300580a02a0180a0040060080080f013d755ec055780000a01302401c0780e01a0300581102a0180100400600405009810d73610058fe01e694091a400e0180687405601c0b8180320cc11891,0x10380680c0160280280800c0080200302a00407c096bd3c203adf0000500981201003807c0c0160280200d00c0140880302a00401009ebcd74048d20000180580c0240340a015014010088130060380080201ed77ae408eb8,0x10500500d0020100700f812d7faf8058f50221bc0f6bb0000580c0240340a015014010088130060180080e004261af409ebc0000981201003807c0c0160280200d00c0500880302a004028026beb7603ede80005009812022,0x100e06419817030000130240500500d0020100700fec119c03adf800050098120220380680c0160280400500c00a0200300205407c09ec0b7803cac0111e202c450042600343a00700c08c4882b00e0641981703000013024,0x1ad003aaf0000500981200503c0700d01802c0500601005401811008004028096c3b0003abc8000500981200503c0700d01802c0500802a0180880400600402809ec2d8004b5f80b114044788042600343a00700c08c4882b,0x10440780e01a0300580a010016030040060040a802813d8d58807d6a0000a0130240440780e01a0300580a00b020030040060040a802812d8bb0c09ec20000981200503c0700d01802c0501402a01808804006004040056c4,
0x10500a80a0160440980300c0040200e6c9d8e02b620000480140f0260340600b0140500a8060220100180101c021b2363012d8a000130240440780e01a0300580a00b050030040060040a808005d8f6080757c0000a013024,0x103000804131b960443781ed94000130240440740d01802c0500400e018028010060500a802012d9769008daa0000a0130240440740d01802c0500400e018028010060080a80901ed95b200fec10223c4021300000601201a,0x10480a00a01a00407766dcc022684028480162d40787e03c668041310320cc0687400e0181189102e06015807000098120280280680101d025b336580b13004c1280f0c00145d81cd920001201a0500a80a0160440980300c,0x1014024060140500180202a00404b67d7a0236140002804c0901101e0380680c0160120380600a00c0101501400404f675cd021564096cc03c668028480162d40787e0104c40c83301a1d0038060462440b81805601c00026,0x1da5b400f99b03bb340787e0162d4028480104c40001a0500a80a01604409803024030030016d1d9e04f6700004c0901101e0380680c0160120380600a00c0a01501400800b6856e02157c0002204c0900e01e01c0680c016,0x10440781501a0300580a01201c0300180800c0a00201cda95c0085610000a0130240440a80201a0300580a01203c0380180800c0300e00bda757408d6d0000a0130240440781501a0300580a01201c0300180800c0100e00a,0x103a0380f00800c0a015004007b5ed5810b4a000140260480880601a0300580a01203c0380181d01001815004015b5ad6010b4c000140260480880601a0300580a01203a0380f00800c01015003017b576980ada400013024,0x102806855ed80262000f92d01e3c00481b00a39c016d10000a01501402c088130060480600d00cdb3b5c0e6d40000901101e0540680c0160280480700c006098030280100136c6d6017b54000260480880601a0300580a012,
0x104a04b6d00004c0500c0240540580800205006c060220100180200e01407b6ddba0396800002404c0500c00a0540580800205006c060220100180200e03c04b6d6d90462440687400e0181580702e0600c83300009812028,0x10480a00a00401c69ae701cb82000140260480880901802c0500f8100360300200800c0081500e015b776d80b1e605c0c01906600c548090dc0342980700c044070230920685582b00e000130240500500200e03db72d101d,0x1302048ad017030064198031520243700d0a601c0301101c08c2481a1560743000e34c0ac0380004c0901401400807f6f6dd016288099e203db700b8180320cc018a90121b80685300e0180880e0461240d0ab05601c00026,0x1b8804ee4800050098120220380600b0140200301500800c0080f81b00a03c056e0b4204ca980b1e607f6f01d0c0038d3017030064198031520243700d0a601c0301101c08c2481a1560ac0380004c09014014009b7ee400b,0x10440700c0160280380801b0180200300203e0a80280bdc7b84056e0000098120220380600b0140200301500800c0080f81b05001407ee2b9404ae2800050098120220380600b0140540400600800c0080f81b00a03c05ee1,0x10540200300203e0981401b00bb9b7200bdc6000130240440700c0160280380801b018020030020500a80f805dcb718095c20000a0130240440380c0160280700801b018014040060040a80f80adc971c095c30000a013024,0x101e6780002602a0301100802604773d5b0244080001501007470ee603c2580e9c4009b7c11849022038068530121b8018a90342ac0380605601c0b8180320cc000260480a00a01cdca03f710000480880e01802c0500800c,0x110801c0301f1320747080004c0540602201004f74d980156580002804c0900e01e0100680c01602a0380602a044018020020260437459b0167040d8970321540b81e00a2dc018f20522181580704a2100380603e2640e8e1,
0x10500981202203c0700d01802c0481500c0100180200202a04007eebb1602ac48000500981201e0380680b0180540480601504402003004004040076eadd00477380f33c06c4b8190aa05c0f00516e00c7902910c0ac03825,0x1030058040110180080a8060080a80900eddd654055940000a0130240440780e01a0300580900c0220a8030040040540400fddbbac076ea0000981201e0380680b018054048060150440a003004004020086ecb1c02ec7800,0x100c00013015018088046f1dde043760000480780e01a02c060150260180541102800c01001012011bc37700fdda000130240440780e01a0300580900c0500a80300400405408808ddf64c055910000a0130240440780e01a,0x10380540d01802c0380600a00c0100101e0120a809ef3b14046c90000500981202203c0700d01802c0240700c0140180200202a0a8096f2de004f7481f1320747081b12e0642a81703c0145b8031e40a44302b00e09442007,0x103c09c7d81f336094628190aa02cde81dab406c3700f0fc0343582b33a0a42a00709a014240030360000a809debbcc096f20000981202203c0700d01802c0240700c0140180200202a0a0156f4b2e046ce00005009812022,0x102c0401500d0100180200202a0a0076f8b3404ac68000500981202203c0700d01802c0a80800d0100180200202a03805ef7b1804ecc8000500981202203c0700d01802c0401500d0100180200202a038056f6de808c7c017,0x116e0337881b12e05c0f02b00e08c7c0190aa0944200700c07c4c81d1c20277a80002a09b7d5900166fc099c001dbe0000240440780e01a0300580802a01a0200300400405413028df3bdc056f60000981202203c0700d018,0x11380acff8070200340a00f1be06c19023340024cf80b1960149701307e0740901113c07c1e0030260640881500400013825051bf37d80702009b7d00002a0086280f1be0907d80002a01813efbdf2044ef00337c0a443005,
0x10040001200e03c0700d0180140480802200c09c0400c00800814816dfba34151f502e420146fc022278058cb03e0f00983f01267c119a00360c8078df00a4b80381001a0500c81103a0480181302a0080002704a05af3017,0x1bbe054010000500880f01c0340600b01001c0200602404e0180200201404b7f6fd0222780984601627c0b88704755c0f86600a6700381001a0500c81103a048018130120541281602a0080002701c06814856d180ab24815,0x1022074090030260240a82502c0a42b00b1c40540100004e0380d02202c0100f7002120a87d0121960001380e044010058e2bc20ac84812dfc054010000440780e01a0300581400e0100301202700c01001010015bff2582a,0x13d607b8000b1c401c0800d0280640881d02400c0980902a0940b0290ac0540100004e0380d02202c010d386f0217900a8020000a0120220380680c0160240280700c008020030270040a80ff01dfe0444f0070200340a019,0x1e0402c450070200340a019022074090030260240a82502c0a42b0111540a84e80434e0540100004e0380d02202c07f81e570259580a8020000901101c0340600b028020038060050100180102b04e07c05702e020ac85013,0x10300581582401c0301400800c0081381000bc1b28012c9a054010000480880f01c0340600b01000a0380600800c0081402705602f82e4f0259300a8020000901101e0380680c0160560400700c0500200300204e01405704,0x105403c0883600604c0c81103c5ec0b13202a0080002701c06811005017c1f8301fe060445502a13a010d38070200340a019022074090030260240a82502c0a42b0150040001380e0340880b132e0a02b820000440780e01a,0x102a0940b0290ac0a80781106c05899003026064088150040001380e03408802f09cb204b2c015004000120220380680c01f020038060280100180102b04e05c0280ae119680912100e0400681403a0480481504a05814856,
0x144e04b3a8150040001201c0340601401001c0300280800c0081582704605c0f80ae162900f0cc05403c0002703408c0b804e144280f0cc00bc241500f02c4c80000e04e06811133e1002f8381e2f601c0800d02807409009,0x10380680c01000a0380600800c008158270460a00b80be1dc300570b0000700d0180500400700c00a0200300205609c1182402e07f86e790259d80a8020000900e01a0300400280e0180200300205609c1182802e07c05f0c,0x100c0080e02704609015817e23c3c05f0e0000780e01a0300400280e0180200300204809c1182805605f886700279c80a8020000900f01c0340600800e018014040060040ac1382305005c0570f2da04b388150040001201e,0x10480a00e01a0300580281001c0301580800c0081182703c02b89711009c281500f00e040068140320440e81200604c04815052158088260444cc1281602a0080002701c0680b9a8e2007f868000340601401001c03002808,0x100a0200300205609c1182803e02b8af13015c48000280380680c01600a0400700c0480200300204609c1581ee299ac0966702a008000240500700d01802c0ac0800e0180200300204609c0281e017c4f35012ccc05401000,0x10280640881d02400c0980902a0a42b01104c0889982502c05cd40150040001380e0340178bf150162280f7140000700d01802c0a00800e0180900400600408c13805057c5b39813ce8054010000480700d01802c0400700c,0x102657c02f1702e6a0088260444cc1485600e040068140320440e81200604c0481504a0580a80200009c0701a0af994155e502a0080000c0480780e01a0300580201001c0181180804e0a001012015c638b02a13401c0800d,0x12be01c0800d0280640881d0240240a82903400c0981104c0940b02a0920783881a0ae0540100004e03811816009c685100acf4054010000480700c0160500400700c03e020030230040ac1381b0240138cf1801632c0f8a4,
0x10180200300205609c0d81f05005802f1dd0002b3f8150040001201c0300580800e01808c040060040ac1381b03e0a002813e399ec05e7c02a008000240380600b0230200380600800c0081582703607c14005025c6f8c813,0x10480700c01001c0301180800c0081582703607c1401700a04f8ff1d009c680381001a0500c81103a0480481505206801813022098128160541240f07103415c0a80200009c0702302dc7b8e012e360000e01804808c0800e,0x10100181180205609c0d82802e01391720027c7c0001c0300400700c0460200300205609c0d81f0500900b805e43a1405e8602a008000240380601181001c030040060040ac1381b03e0a00b805025c834400ad0e05401000,0x10220980381001a0500c81103a0480481504a0581481a03415c0181302a0080002701c08c5672202611c02f210000600800e01808c040060040ac1381b0380a01201f02fc8c5100ad08054010000480700c0120200380601f,0x102a0940b0290340682b80302608c560150040001380e02e4d33180b24201c0800d0280740900902a0940b0290340441b003026064088042380a80781331208c5601a0ae0540100004e0380b81fe49c8c0b71e03c1c415049,0x10340682b80302608c560172680540100004e0380801e352578095e202a008000280480880b01c03006c0400a01c0300301e04e04001004055c972a00b2de07f920133120108e01106c0a8078070200340a01902207409009,0x11c401c0800d0280640881d0240240a82502c0a40d00302608c560172680a89a81e3520682b8150040001380e020013931ec00a2740002703607c15135e4a0acb380b1c40144b0070200340a0190220740900902a0940b029,0x10480200300203609c1402b03fca72e813cbe054010000480880e01802c0400700c0100180102b04e07c0d82800a02f9465e0259700a8020000901101c0300580281001c0301580800c0080d82705007c05727cb604c8480b,
0x11540000d811124038158aa021ca80d05700009c0703be520139302a26a078d48070200340a0190220740900902a0940b0290340682b80302608c560172680540100004e0380872ae5002b938000440700c01600a0400700c,0x10240240a82502c0381d82903400c098111240a8568150040001381b03c38ef181f26a04caf02309205c0780b1f40144e8070200340a0190220740900902a0940b00e0760a40d003026044490150040001381b0542b40702b,0x101c0ec1481a00604c088920542b40f0e302a0080002703601411017e584880566402a008000240440700c0100180ac0400600403c1381f0360a002817027caf2a81612c028650042ce04ca98230e201c0800d0280640881d,0x144c02865013e5a0001201c0300a00800c0560200300201e09c0f81b00a0880b72ecc402b3081500400012022038060140100180ac0400600403c1381f0360140b013e5bcac0911b00e040068140320440e81201205412816,0x100a05809f31cfc02b3e8150040001201c0300a0118100180ac0400600406c1380f03e0140b012e61cb80bf2c00e040068140320440e8120120541281601c0ec1481a00604c088920542b40f0e302a008000270360141172f,0x10040001201c030040060230100180102b04e03c0f81b02e0a002813e67cc4097300000700c0280460400602b0100180101b04e03c0f82400a05b99683015a080a8020000900e018050040060230100180102b04e03c0f81b,0x104605f9b734045cbc0381001a0500c81103a0480481504a0580703b05206801813022248150ad03c38c0a80200009c0d805e6bccc0911b02dcc8000180500700800c0560200300203609c0781f04808c02f3424402b45015,0x1020030040060080081582705007c0e00f04806c09f38d0202cc0817e6c054010000380600800c0100180200205609c1401f03603c12013047cdf4480bd16054010000480700c010018020030040040ac1382803e06c07813,
0x10361d40002703e0140b73a148088850000340ac1381f009ce79c0122b40179a81e1c60a8568111240a40d0070200340a019022074090030260240a82502c0381d8150040001381b0eb9800598602e47011f3702a00800018,0x102a008000270200ac0f93619402c90823e760000e01a0300a00800c00a0200300205609c0781f0480480bf3ccf002b3b8150040001201c03406014010018014040060040ac1380f03e04811817e765600588a0263380703b,0x10459380a8020000901401e0380680c0160560400600800c0080782700a04805f3e2d80287f80e07606c3a80004e07802817e7bcf00b73a0263380273900e040068140320440e81200604c0481504a0580d8750522d00703b,0x1020030040060040ac1380f05001405f41cda08b290150040001201303c0700d01802c0400602b0100180100f04e0a00280ae819a0110ca017cf80a8020000a00f01c0340600b02b0200300400600403c1382400a04b9fe69,0x102a008000270200ac02937e8404b9f80003c0700d0180500ac0800c0100180100f04e0900b005e87d040574000004c0f01c034060120100180ac0400600403c1382802c017a166f04594c0a8020000900981e0380680c016,0x1e8b9b81118600e040068140320440e81200604c0481504a0580d8750522d00703b02e3300293703e4d80a80200009c0802b02602fa274302fcf40381001a0500c81103a04801813012054128160361d4148b401c0ec0f936,0x100804ba3f45017d100381001a0500c81103a04801813012054128160361d4148b401c0ec0b8cc00a4dc0f93602a008000270200ac09f46cd808b288150040001201603c0700d018050040060040100181580201e09c0980a,0x100400013803bc00a47e01f3d404cf482329c05c0780b1f40144e82be9001c0800d0280640881d02400c0980902a0940b00e07606c3a81500400013810e93d1c09f4600a4dc0703b00009c0802be90598111fe0000ac07827,
0x1bd809c0181500403c0200700a0001202203c0a40d0160220481500a0100100e00c031d287e01710e07c330280380641c0251be0540102700601c0280001e010030270060000380513c07c37810e920240a82502c06408815,0x10080881201c3562240c5ed04e00c0a80201e010038050000901101e03806805016052044040040540480180de986a80c74a0000880f02903405808812054028040040480700674b3de00d0b8000520441200c0326aaf5803,0x10440780d01d02c0481480a0100100882a018063a75f6030858011610386ac048540166080d80e0500700380501e0100a80204e00c0002a0080480882203c0581200de9bd3001161019d2c0001e0520680b0110240a805008,0x10080940882a006077a874f016608048540500700d80e02a008138030000a8020120220880f0160481dba7019354037a681c3560001481a02c0440902a01407802022010093a7df30077d01380302a0080780400e01400024,0x103c06811016024028148080080940882a01800fa90370317f81380302a0080780400e0140002203c0300d00a02c0481480804a0100882a006073a8e0d0318101380302a0080780400e0140002203c0680601602402814808,0x1010094020110440a80680335a0dc0c60104e00c0a80201e010038050000880f00a0340a40b0120100940201101a0a80181cea7d48010c9036038048610481d8138030000a8020120220880f016052028061acea2077a8000,0x102c048040250080441102a014037aae0f030418019ad0186b0048610481d80d80e00e0140780402a008138030000a8020120220880f0160520280ef54c200608f81cea609c0181500403c0200700a0000f00a0340a40b012,0x102a0080780400e0140002203c0a40d00802c048128040220340582a006073ab7550186b00d80e0121841207604e00c0002a0080480882203c0581480a2718000c88903bd50019ad04e00c0a80201e010038050000780d029,
0x10440780b02903bd63ab80243206c070090c20903b00a27009c01800054010090110440780b02901a6bb0881823e073ab0270060540100f00801c0280003c0a40d00802c048128040220880582a01a00fab83703180813803,0x10080480882203c05814f5a06e062ff8270060540100f00801c028000440780601a0520580900804a0100880b05400c0e759c1c0610f81b01c0243080a2700086480d35c0903b00700a03c0201500409c0180005401009011,0x113800c8a80002205c128280ef7500e90601620c0c95d01a57001915053d68048610481d80d80e00e0140780402a008138030000a8020120220880f016273d640ef58004324069ae0144e00d80e0121841207604e00c0002a,0x10123b414077038350011af02c4e40002a0080480882203c09406f5c30e02b098270060540100f00801c028000440780d01203a0200202904a05c0882a0060340cf5b2c4074c200c1920601b0280ee0000882202e094011af,0x10220a81101e081d740ca2501bd700e0d40046bc140770123b40d80e02c4e40002a0080480882203c097af6070158181380302a0080780400e0140002203c0680c01203a0a40400404a05c0882a006033aef5b03047c0d80e,0x12ba034ae00322a06c0700903a0901302208007c2080700a03c0201500409c018000540100901102c0a04986102e3b4138030000940481d342020378150040000901103e1050a828038097af01627209c0181500400002012,0x10220580101dec055c0c178039d7c1104003e1040002a00804808816004030d861b0320c40d80e0120741202605024c059850441000f84100e0140780402a008138030000a8020120220580100c039d7eed81d2f002c41819,0x10240440b00227587805e2004e00c0a80201e010038050000780101a052058090080080941181101a0a80e018ec38e80c1540166000d80e012074120260441000f84105024c061b000e0140780402a008138030000a802012,
0x10820a049802274000150040240440b00d039d8f0f80bc4209c0181500403c0200700a0000f0290340580401204a0101181101a0a80181c031d8bb0819112077b000c36006c0700903a0901302208007c2082812600015004,0x10060540100f00801c0280003c0680b01203a0200202904a08c0882a0060340cf65c6202f190270060540100f00801c0280003c068148160240200202304a0440682a0060740c764ec40641b81b01c0240e82404c0882001f,0x103c0680b0120180a804004052094118110060740cf68ecc073b181b01c0240e82404c0882001f0820a049802274000150040240440b00decfd940c764000068148160240200202304a0440f02a0060340ef66c7802b1d827,0x10380a801818ed7da40cf680000680b0120180a8040040520941181103c00c0ef6ac5e02f180270060540100f00801c0280003c068060160240a4040040460940882a0060740c769c7202b1c0270060540100f00801c02800,0x10044e8140930360380481d0480981104003e1040002a0080480881615ddac0c83703bda800016024030150080080681282302207814803ed987005e1d04e00c0a80201e010038050000780601a0520580900804a01011811,0x105401009011006030d8f6d0304000d80e0120741407702c2b8120260441000f8410000a80201202200c0601cedd8a005e2904e00c0a80201e010038050000780601a0240a4040040460940b81105400c0e019edbdb006f67,0x10304800d80e0120741407702c2b8120260441000f8410186c40380501e0100a80204e00c0002a0080480880303bdbf2280b23a0609001cedc06c0700903a0a03b81615c0901302208007c2080700a03c0201500409c01800,0x100a0000d0120100100102904a08c0b8110320a80f01dee591805e4804e00c0a80201e010038050000780d0120100100102904a08c0b8110320a80e80dee24000c88903bdbc061b102c2b80002a00804808803ee191c0591d,
0x104e00c0a80201e010038050000640e81202008c040040040a41501a02e0781280cee9dc80e0310300d801f700501dc0b0ae012074120260441000f8410360380002a00804808f73c8802cc280dee209c0181500403c02007,0x10540100101003a067bbf750503e41204502611c049c303e71c0d9c601e0100001002e0a80200203a06411f76c840286400cee809c0181500403c0200700a0000e81202008c040040040641501a02e07814825eeb8f405e3f,0x104bde41380302a00800017004070d91650460c40c1080502700001700407012f792100a04e0241c8067bb8000540100b810004077bc2180500700a80204e00c0001703a0907216305007012984047dd81380302a00800017,0x100a03c02027006000080170540100e0243677bc0589f02611c0481b0361a00f86904631c0107803021c1401c00e0140780402a008138030000400b82a0080701200cef46c80ef780000a80b8100080083c16303021c1401c,0x10200a4118080080940d0170060640677c2dc02f138270060540100f00801c0280003c070150120200200202504605c1481a00606406f7bbe00288380cef40604382318e0a00e01308e0240d81b0d007c348020f005401007,0x1eff88c0562204e00c0a80201e010038050000600e02a0460480802502e0200201e03400c1480cefddf006f7b000070150120200200202504605c0f01a0060a40cf7dc4c02b128270060540100f00801c0280003c07015012,0x1f00067be800054048080080080941181703c0680181c0526d3bf80cefc0000e02a0460480802502e0200201e03400c0c029f005ac0562404e00c0a80201e010038050000780e01a030048080170100101282305400c1480d,0x1f02060bb82936809c0181500403c0200700a000090100100101282a02e0780d003046073c15dd0145d80c1770526d00d86803e1a4110d401206c098470041e0121b300e0140780402a008138030000400b82a00807006f81,
0x104a0780b81a00608c06f84c8002b1f0270060540100f00801c02800032074090100520a80400404a0780d01700608c06783f040886a02436604c2380903606c3401f0d20083c00f008000080170540100e13bbb802cba80d,0x102611c0481b0361a00f869050344120e40384ec0107801e0100001002e0a80202336be1006783000074090100520a80400404a0780d01700606411f85c8602b208270060540100f00801c02800032074090100520200202a,0x10d206c340090360083c01308e01c0280f0080540102700600008017054013c3e1201661c0984701206c0d86803e1a4069880466d4140d1048390010780384ec0380501e0100a80204e00c0001002e0a802019f0de140c120,0x10cc04c230090a806c0d02803801c028270060540100f0080000802a0080080e02404406006789f0e0ac11805f1009c0180002005c0b9b203a708018e700005c02f88c0a02cb8019f0c034c402336a0a0688241c80709d81f,0x10121500d81a0500700380501e0100a80204e00c000100540100101c048088db5e90165800678902e05c0f866026118048540360681401c00e0140780402a008138030000401500400407012022031e2af380b13e05c0b81f,0x136c0a00e01500409c018000200a80200203809057df701627c0b81703e198098460121500d81a0500700c8310446d80380501e0100a80204e00c000100540100101c048033c5dee01617806962031e280b81703e19809846,0x102a0080780400e0140001e0380680c0160240400102a01001012823052033c6e190143200b8170360c80983f03e0f00481d0482bc0c83100e0140780402a00813803000040150040040701182901be306400b2c0033c5822,0x1f1c0641881702e06c1901307e07c1e00903a0905780700a03c0201500409c018000200a80200203808cdbf8d01be300b8170360c80983f03e0f00481d0482bc0c83102a008000100540100101c0460a7c761601585013803,
0x1051e46eb018ba609c0180f0080540100700a0001402203c0700d02502c0480802a0100100100a01be42ea818ba409c0180f0080540100700a0000801e038068050160240880402500401015028019e3eec00b1060347b029,0x100801c028000340300e0290440080901003c0941500402c0200c793f2202c4181702e06c1901307e07c1e00903a0905782336e054010000200a8020020380a3c9790019e3c0001e03806808016024088040250040101500a,0x1c1009c0181500403c0200700a0000d01e03a058090100180a80400400408812829033e53c980d2c8064b2828f2408cdb80903a07c1e01307e06c1902415e05c0b8150040000802a0080080e079bf402afc0270060540100f,0x101a79c05883053e540b8170360c80f83c0260940481d0381e40380501e0100a80204e00c0001005401001025044397ca0183e6034b201702e06c1901f07804c1280903a0703c8150040000802a00800812822053e550e00a,0x103a0703c8221ca0a09e00700a03c0201500409c018000200a80200204a0300c796bbc0647c80b1060347b01702e06c1901f07804c1280903a0703c8221ca01c0280f008054010270060000802a0080081282827975c0c9e8,0x10504f0110e502e05c0e07900004015004004097cc6330168800c79602e05c0d83203e0f0098250120740e0790443941413c00e0140780402a008138030000401500400409406797c5402c4c01702e06c1901f07804c12809,0x100a0001202203c068018160240400e80a01001015029019e66f88193e4034f881b03404c2301f0cc0242a00b30608c22828038097cc01c0f205c0b80700a03c0201500409c018000200a8020020ce2600c95601432006797,0x100403c0200700a0000d01e03a05809010054088040040520940180c015e6fcc80d20e02cc182308a0a00e01702e06c7481f27e04c128090360083381500409c018000200a80201d049e6afa818be409c0181500403c02007,
0x1f3d8300560b04e00c0a80201e010038050000680f01d02c0480800d0100101482505400c11019f3b8280c21a015e6c1380302a0080780400e0140001e03a058090100540680400405209401822019e7301819c1209c01815,0x10000780d01d02c0480802a0100101482504600c06818f418dc0563604e00c0a80201e010038050000780e816024040150080080a41282303400c06819f3fe740c21b019e700001d02c0480802a0340200202904a00c0f022,0x104a0a80181a033e8f1600ac5609c0181500403c0200700a0000f01a03a0580901001800c0400405209415023031e8bd0019f3e0000e816024040150080080a41282303400c0f00df438b80562d04e00c0a80201e01003805,0x104a00c0e81ef4de9006fa1000058090100540200202904a08c0d00303a07bd2fa3031e880001a03a0580901001800c040040520941501e047e931a80ac6809c0181500403c0200700a0000f01d02c0480800c04602002029,0x10158541380302a0080780400e0140001e0380680c016024040018290100101282a046033d3fa60503441279a0260940f93f0363a40b81701206c0106702a008000100540100e8b0f4a08bcf00002c0480802a03402002029,0x103c0600e01a052058090100100101282a00608806faaf50033d38000380680c016024040018290100101282a03c08fd4e180178681380302a0080780400e01400018038068148160240400400404a0a80f003046037d4617,0x104a0a81481ef5beac06faa0000600e01a052058090100100101282a006078117acbf602afc8270060540100f00801c0280003c0600e01a006058090100440a80400404a0a4067abbf802efe8270060540100f00801c02800,0x103a2c00f8a404453c149b800419c0d83200e0140780402a008138030000401500404a033d77ad03e1980481b0320dc0b81700419c0d8320260fc0e8b00000401500404a0a4dc7ac047ea40001a0300580901000607004004,
0x100a03c0201500409c018000200a80201a01bebeed00a2ec033d701f148088a782937004c1f81b0640240d81906e0745801702e0083380700a03c0201500409c018000200a80202527b7640597501206c0c83702e05c0983f,0x100419c0a80204e00c000100540100d7b113e02af40270060540100f00801c028000480780c01c05400c0b01202008814808008068067b0bd4028838090360641b81d16005c0b82803807c9682318e04c4002527a00833807,0x101e0100a80204e00c000101cc0701499c04a4b80a80204e00c0000527d55806853035ec41401c04a4f40106704e00c0a80200e01400010054013d97b001bebc0481b0320dc0e8b002e05c1401c03e4b4118c70262001293d,0x10242c400003f683dc1380300a4f8090b100008cdcf73057ecc0293e020398000121622a8080e60000afd9e4a03e0f00983f0475600d83201b5500581f03218814a0204801c0ed5501267401d53055ec80b81700a4f803805,0x108c04858815004027db828374003dc0540506e800009f6e0701380302a00812fb60000a0dd1060380fc080e60466e401fb4033ed4090b1000097db05f04e00c090b10466e400019f6a6f0080e6
]
def formula := (rootSpans.map spanClause ++ blocks.map blockClause) ++ groups.map exactClause
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem goodSpans : rootSpans.all spanGood=true := by decide +kernel
set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
theorem infeasible : ¬ FormulaSat formula := checkW_sound _ keys 11 words (by decide +kernel)
theorem third_owner {chosen region prev} (O : Later prev chosen region) (inset : prev∈priors)
    (disj : ∀ i∈prev, chosen i=false) : ∃ g∈groups, Matches chosen g := by
  classical
  by_contra h
  apply infeasible
  refine ⟨chosen,?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hp | he
  · rcases List.mem_append.mp hp with hs | ht
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hs
      exact reject_neg _ _ (later_span O (List.all_eq_true.mp goodSpans _ hw))
    · obtain ⟨t,hw,rfl⟩ := List.mem_map.mp ht
      apply clause_or
      by_cases yes : AllOn chosen t.lo
      · exact Or.inr (accept_pos _ _ (project_sound O inset disj (List.all_eq_true.mp checkedBlocks _ hw) yes))
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
