import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18855

namespace TriangleMessages

abbrev Atom := Nat × Nat × Nat
abbrev Lit := Atom × Bool
abbrev Clause := List Lit

def pos (k i j : Nat) : Lit := ((k,i,j), true)
def neg (k i j : Nat) : Lit := ((k,i,j), false)
def flip (l : Lit) : Lit := (l.1, !l.2)
def value (h : Nat → Nat → Bool) (a : Atom) : Bool :=
  decide (h a.1 a.2.1 ≠ h a.1 a.2.2)
def good (v : Atom → Bool) (c : Clause) : Prop :=
  c.any (fun l => decide (v l.1 = l.2)) = true

theorem good_iff {v : Atom → Bool} {c : Clause} :
    good v c ↔ ∃ l ∈ c, v l.1 = l.2 := by
  simp only [good, List.any_eq_true, decide_eq_true_eq]

def taut : Clause := [pos 0 0 0, neg 0 0 0]
theorem good_taut (v : Atom → Bool) : good v taut := by
  cases e : v (0,0,0) <;> simp [taut, good, pos, neg, e]

def fetch (db : Array Clause) (n : Nat) : Clause :=
  if h : n < db.size then db[n] else taut

theorem fetch_good (v : Atom → Bool) {db : Array Clause} (h : ∀ c ∈ db, good v c)
    (n : Nat) : good v (fetch db n) := by
  unfold fetch
  split
  · apply h
    simp
  · exact good_taut v

def propagate (db : Array Clause) (ban : Clause) (last : Nat) :
    List (Nat × Lit) → Bool
  | [] => (fetch db last).all (fun l => decide (l ∈ ban))
  | (j,l) :: t =>
      (fetch db j).all (fun m => decide (m = l ∨ m ∈ ban)) &&
      propagate db (flip l :: ban) last t

theorem propagate_sound (v : Atom → Bool) (db : Array Clause)
    (hd : ∀ c ∈ db, good v c) (last : Nat) (hs : List (Nat × Lit)) :
    ∀ (ban : Clause), (∀ l ∈ ban, v l.1 ≠ l.2) →
      propagate db ban last hs = true → False := by
  induction hs with
  | nil =>
    intro ban hb h
    obtain ⟨l,hl,hv⟩ := good_iff.mp (fetch_good v hd last)
    exact hb l (of_decide_eq_true (List.all_eq_true.mp h l hl)) hv
  | cons u hs ih =>
    rcases u with ⟨j,l⟩
    intro ban hb h
    simp only [propagate, Bool.and_eq_true] at h
    obtain ⟨hc,ht⟩ := h
    obtain ⟨m,hm,hv⟩ := good_iff.mp (fetch_good v hd j)
    have hh : m = l ∨ m ∈ ban := of_decide_eq_true (List.all_eq_true.mp hc m hm)
    have hv' : v l.1 = l.2 := by
      rcases hh with e|e
      · simpa [← e] using hv
      · exact False.elim (hb m e hv)
    apply ih (flip l :: ban) _ ht
    intro n hn
    rcases List.mem_cons.mp hn with he|ho
    · subst n
      simp [flip, hv']
    · exact hb n ho

def decLit (n : Nat) : Lit :=
  ((n / 128, (n / 16) % 8, (n / 2) % 8), decide (n % 2 = 0))

def decHint (n : Nat) : Nat × Lit := (n / 1024, decLit (n % 1024))

abbrev Step := List Nat × List Nat × Nat

def verify (db : Array Clause) : List Step → Bool
  | [] => false
  | (raw,hs,j)::rest =>
    let c := raw.map decLit
    propagate db c j (hs.map decHint) &&
      (if c.isEmpty then true else verify (db.push c) rest)

theorem verify_sound (v : Atom → Bool) (steps : List Step) : ∀ (db : Array Clause),
    (∀ c ∈ db, good v c) → verify db steps = true → False := by
  induction steps with
  | nil => simp [verify]
  | cons u rest ih =>
    rcases u with ⟨raw,hs,j⟩
    intro db hd h
    let c := raw.map decLit
    simp only [verify, Bool.and_eq_true] at h
    obtain ⟨left,right⟩ := h
    change (if c.isEmpty then true else verify (db.push c) rest) = true at right
    have hg : good v c := by
      by_contra bad
      apply propagate_sound v db hd j (hs.map decHint) c _ left
      intro l hl hv
      exact bad (good_iff.mpr ⟨l, hl, hv⟩)
    cases he : c with
    | nil => simpa [he, good] using hg
    | cons l ls =>
      refine ih (db.push c) ?_ ?_ 
      · intro d hd'
        have hor : d ∈ db ∨ d = c := by simpa using hd'
        rcases hor with hm|hm
        · exact hd d hm
        · simpa [hm] using hg
      · simpa [he] using right

def matching (a : Nat) : Bool :=
  (a.testBit 0 && a.testBit 5) || (a.testBit 1 && a.testBit 4) ||
    (a.testBit 2 && a.testBit 3)

def faceEdges : Nat → Nat × Nat × Nat
  | 0 => (3,4,5)
  | 1 => (1,2,5)
  | 2 => (0,2,4)
  | _ => (0,1,3)

def projection (face a : Nat) : Nat :=
  let e := faceEdges face
  (a.testBit e.1).toNat + 2 * (a.testBit e.2.1).toNat + 4 * (a.testBit e.2.2).toNat

def projected (faces : List Nat) (k a : Nat) : Nat :=
  projection (faces.getD k 0) a

def messages (faces : List Nat) (h : Nat → Nat → Bool) (a : Nat) : List Bool :=
  (List.range 5).map (fun k => h k (projected faces k a))

def decodes (faces : List Nat) (h : Nat → Nat → Bool) (d : List Bool → Bool) : Prop :=
  ∀ a : Fin 64, d (messages faces h a.val) = matching a.val

def pairClause (faces : List Nat) (a b : Nat) : Clause :=
  ((List.range 5).filter (fun k => decide (projected faces k a ≠ projected faces k b))).map
    (fun k => pos k (min (projected faces k a) (projected faces k b))
      (max (projected faces k a) (projected faces k b)))

theorem pair_good (faces : List Nat) (h : Nat → Nat → Bool) (d : List Bool → Bool)
    (hd : decodes faces h d) (a b : Fin 64) (ha : matching a.val = true)
    (hb : matching b.val = false) : good (value h) (pairClause faces a b) := by
  by_contra bad
  have eqm : messages faces h a = messages faces h b := by
    apply List.map_congr_left
    intro k hk
    by_contra differ
    have distinct : projected faces k a ≠ projected faces k b := fun e => differ (congrArg (h k) e)
    apply bad
    apply good_iff.mpr
    refine ⟨_, List.mem_map_of_mem (List.mem_filter.mpr ⟨hk, by simpa using distinct⟩), ?_⟩
    by_cases le : projected faces k a ≤ projected faces k b
    · simpa [pos, value, Nat.min_eq_left le, Nat.max_eq_right le] using differ
    · have ge : projected faces k b ≤ projected faces k a := by omega
      simpa [pos, value, Nat.min_eq_right ge, Nat.max_eq_left ge] using Ne.symm differ
  have r := congrArg d eqm
  rw [hd a, hd b, ha, hb] at r
  contradiction

def tri (k i j : Nat) : Fin 4 → Clause
  | 0 => [pos k 0 i, pos k 0 j, neg k i j]
  | 1 => [neg k 0 i, neg k 0 j, neg k i j]
  | 2 => [pos k 0 i, neg k 0 j, pos k i j]
  | _ => [neg k 0 i, pos k 0 j, pos k i j]

inductive Base where
  | z (k : Nat)
  | x (k i j : Nat) (mode : Fin 4)
  | p (a b : Fin 64)

def initial (faces : List Nat) : Base → Clause
  | .z k => [neg k 0 0]
  | .x k i j mode => tri k i j mode
  | .p a b =>
    if matching a.val = true ∧ matching b.val = false then pairClause faces a b else taut

theorem initial_good (faces : List Nat) (h : Nat → Nat → Bool) (d : List Bool → Bool)
    (hd : decodes faces h d) (z : Base) : good (value h) (initial faces z) := by
  cases z with
  | z k => simp [initial, good, neg, value]
  | x k i j mode =>
    fin_cases mode <;> cases e : h k 0 <;> cases f : h k i <;> cases g : h k j <;>
      simp [initial, tri, good, pos, neg, value, e, f, g]
  | p a b =>
    simp only [initial]
    split
    · rename_i yes
      exact pair_good faces h d hd a b yes.1 yes.2
    · exact good_taut _

def checked (faces : List Nat) (rows : List Base) (steps : List Step) : Bool :=
  verify (rows.map (initial faces)).toArray steps

theorem checked_sound (faces : List Nat) (rows : List Base) (steps : List Step)
    (pass : checked faces rows steps = true) :
    ∀ h d, ¬ decodes faces h d := by
  intro h d hd
  apply verify_sound (value h) steps _ _ pass
  intro c hc
  have hm : c ∈ rows.map (initial faces) := by simpa using hc
  obtain ⟨z,_,hz⟩ := List.mem_map.mp hm
  subst c
  exact initial_good faces h d hd z

private def r3200c0 : List Base := [
  .p 33 32]

private def r3200 := r3200c0

private def s3200c0 : List Step := [
  ([],[],0)]

private def s3200 := s3200c0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no3200 : ∀ h d, ¬ decodes [0,0,0,1,1] h d :=
  checked_sound _ r3200 s3200 (by decide +kernel)

private def r3110c0 : List Base := [
  .z 3,
  .x 3 0 1 0,
  .x 3 0 2 0,
  .x 3 1 2 1,
  .x 4 4 5 0,
  .x 4 4 5 1,
  .x 4 4 7 0,
  .x 4 4 7 1,
  .x 4 5 7 0,
  .x 4 5 7 1,
  .p 18 16,
  .p 18 21,
  .p 19 21,
  .p 29 24,
  .p 29 25,
  .p 49 48]

private def r3110 := r3110c0

private def s3110c0 : List Step := [
  ([386,387],[385],1),
  ([388,389],[385],2),
  ([386],[10626],16),
  ([526,591,607],[15946,6664,8714],5),
  ([591,607],[15946,19982,7689,9739],4),
  ([590],[18818,11668,13700,17796],3),
  ([607],[22094],20),
  ([404],[23135],12),
  ([388],[23135],14),
  ([389],[18818,23956],3),
  ([],[24964,25989],17)]

private def s3110 := s3110c0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no3110 : ∀ h d, ¬ decodes [0,0,0,1,2] h d :=
  checked_sound _ r3110 s3110 (by decide +kernel)

end TriangleMessages
end PEqualNP.Outside.L_meta_18855
