import PEqualNP.Defs

namespace PHP169Color

abbrev Pigeon := Fin 3
abbrev FirstArm := Fin 3

def bit (b : Bool) : Nat := if b then 1 else 0

def hit (i a b c : Pigeon) (x y z : Bool) : Bool :=
  (x && (a == i)) || (y && (b == i)) || (z && (c == i))

-- A bottom two-pigeon packet costs two physical resolutions. Its row
-- implication may be oriented either way and credited once to a request.
def pairPrice (bottom left right : Bool) : Nat :=
  2 * bit bottom + ((bit left + bit right) - bit bottom)

def atHole (a b c : Pigeon) (x y z : Bool) : Nat :=
  let bottom := fun i => hit i a b c true true true
  let asked := fun i => hit i a b c x y z
  pairPrice (bottom 0) (asked 1) (asked 2) +
  pairPrice (bottom 1) (asked 0) (asked 2) +
  pairPrice (bottom 2) (asked 0) (asked 1)

-- Three two-hole domains touch each hole. At a hole assigned all three
-- of its incident domains the lower bound loses at most one unit.
theorem local_bound (a b c : Pigeon) (x y z : Bool) :
    2 + bit x + bit y + bit z ≤ atHole a b c x y z + bit (x && y && z) := by
  revert a b c x y z
  decide

def left (f : FirstArm) : Bool := f == 1
def right (f : FirstArm) : Bool := f == 2

-- The six edges are 01,02,03,12,13,23. A first arm has one endpoint.
theorem at_most_one (s t u v w z : FirstArm) :
    bit (left s && left t && left u) +
    bit (right s && left v && left w) +
    bit (right t && right v && left z) +
    bit (right u && right w && right z) ≤ 1 := by
  revert s t u v w z
  decide

def totalPrice (a b c d e f : Pigeon) (s t u v w z : FirstArm) : Nat :=
  atHole a b c (left s) (left t) (left u) +
  atHole a d e (right s) (left v) (left w) +
  atHole b d f (right t) (right v) (left z) +
  atHole c e f (right u) (right w) (right z)

def transferred (s t u v w z : FirstArm) : Nat :=
  bit (left s) + bit (left t) + bit (left u) +
  bit (right s) + bit (left v) + bit (left w) +
  bit (right t) + bit (right v) + bit (left z) +
  bit (right u) + bit (right w) + bit (right z)

theorem six_states (a b c d e f : Pigeon) (s t u v w z : FirstArm) :
    7 + transferred s t u v w z ≤ totalPrice a b c d e f s t u v w z := by
  have h0 := local_bound a b c (left s) (left t) (left u)
  have h1 := local_bound a d e (right s) (left v) (left w)
  have h2 := local_bound b d f (right t) (right v) (left z)
  have h3 := local_bound c e f (right u) (right w) (right z)
  have ho := at_most_one s t u v w z
  unfold totalPrice transferred
  omega

def difference (a b : Fin 4) : Nat := if a = b then 0 else 1
def splits (a b c d : Fin 4) : Nat :=
  difference a b + difference a c + difference a d +
  difference b c + difference b d + difference c d

theorem split_or_same (a b c d : Fin 4) :
    (a = b ∧ b = c ∧ c = d) ∨ 3 ≤ splits a b c d := by
  revert a b c d
  decide

-- With a single donor at the four-pigeon level its primitive transfers
-- have no deeper source. A hole belongs to at most three of the domains.
theorem common_upper (chosen paid : Nat) (cap : chosen ≤ 3 * paid) :
    48 ≤ (48 + 3 * paid) - chosen := by omega

theorem different_upper (a b c d : Fin 4) (hne : ¬(a = b ∧ b = c ∧ c = d)) :
    162 ≤ 45 + 20 + 4*11 + (6 + splits a b c d)*5 + 4*2 := by
  rcases split_or_same a b c d with h | h
  · exact False.elim (hne h)
  · omega

-- Five raw rows and forty collision axioms. One twenty-step root.
-- Four ordinary upper packets of twelve each, six three-row packets of six
-- each, and a jointly charged selection of lower branches and implications.
theorem common_cost (a b c d e f : Pigeon) (s t u v w z : FirstArm)
    (chosen paid : Nat) (cap : chosen ≤ 3 * paid) :
    156 ≤ 45 + 20 + ((48 + 3*paid)-chosen) +
      (36 + totalPrice a b c d e f s t u v w z - transferred s t u v w z) := by
  have hs := six_states a b c d e f s t u v w z
  have hu := common_upper chosen paid cap
  omega

-- Pick zero as donor at each two-hole state, and transfer toward hole zero
-- on its three incident edges. These choices attain the lower bound.
theorem attained : 45 + 20 + 48 +
    (36 + totalPrice 0 0 0 0 0 0 1 1 1 0 0 0 - transferred 1 1 1 0 0 0) = 156 := by decide

end PHP169Color
