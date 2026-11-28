import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_178_affine


def smear (s a : Nat) : Nat := a ^^^ (a >>> s)

def parity (a q : Nat) : Bool :=
  (smear 1 (smear 2 (smear 4 (smear 8 (smear 16 (a &&& q)))))).testBit 0

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
abbrev V := Fin 5 × Fin 4

def idx (v : V) : Nat := 4 * v.1.val + v.2.val
def assignment (a : Nat) (v : V) : Bool := a.testBit (idx v)
def formMask (S : Finset V) : Nat := S.fold (· ^^^ ·) 0 (fun v => 2 ^ idx v)

theorem idx_lt (v : V) : idx v < 20 := by
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

theorem mask_lt (S : Finset V) : formMask S < 1048576 := by
  change formMask S < 2 ^ 20
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

theorem parity_unit (a j : Nat) (hj : j < 20) : parity a (2 ^ j) = a.testBit j := by
  have hb : a &&& (2 ^ j) = if a.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases h : j = i
    · subst i
      cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow]
    · cases ht : a.testBit j <;> simp [ht, Nat.testBit_two_pow, h]
  have hp : ∀ k : Fin 20, parity (2 ^ k.val) (2 ^ k.val) = true := by decide +kernel
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

theorem flat_closed (D : LinClause V) (x y z : Nat)
    (hx : ¬ LinClauseSat (assignment x) D) (hy : ¬ LinClauseSat (assignment y) D)
    (hz : ¬ LinClauseSat (assignment z) D) :
    ¬ LinClauseSat (assignment (x ^^^ y ^^^ z)) D := by
  rintro ⟨e,he,sat⟩
  have no (a : Nat) (h : ¬ LinClauseSat (assignment a) D) :
      parity a (formMask e.1) ≠ e.2 := fun eq => h ⟨e,he,(linEqSat_iff _ _).2 eq⟩
  have nx := no x hx
  have ny := no y hy
  have nz := no z hz
  have val := (linEqSat_iff _ _).1 sat
  rw [parity_left,parity_left] at val
  cases heq : e.2 <;> cases h1 : parity x (formMask e.1) <;> cases h2 : parity y (formMask e.1) <;>
    cases h3 : parity z (formMask e.1) <;> simp_all


abbrev Code := Fin 128
def off (t : Code) (i : Fin 5) : Bool := if i=4 then true else if i=3 then false else t.val.testBit (4+i.val)
def potential (t : Code) : Finset V := Finset.univ.filter fun v => off t v.1 != t.val.testBit v.2.val
def occ (x : Nat) (i : Fin 5) (h : Fin 4) := assignment x (i,h)
def hitRow (x : Nat) (i : Fin 5) := (List.finRange 4).any fun h => occ x i h
def cleanPair (x : Nat) (i j : Fin 5) := (List.finRange 4).all fun h => !(occ x i h && occ x j h)
def cleanStar (x : Nat) (i : Fin 5) := hitRow x i &&
  (List.finRange 5).all fun j => decide (j.val ≤ i.val) || cleanPair x i j
def safe (x : Nat) := cleanStar x 0 && cleanStar x 1 && cleanStar x 2
def missingThree (v : V) : Bool :=
  decide ((v.1=0 ∧ v.2=0) ∨ (v.1=1 ∧ v.2=1) ∨ (v.1=2 ∧ v.2=2) ∨ (v.1=4 ∧ v.2=3))
def sideThree (t : Code) :=
  decide (Odd (((potential t).filter fun v => missingThree v = true).card))
def childClean (t : Code) (x : Nat) : Bool :=
  let p : Fin 5 := if parity x (formMask (potential t)) == sideThree t then 3 else 4
  hitRow x p && (List.finRange 4).all fun h =>
    decide ((p,h) ∈ potential t) || !(occ x 3 h && occ x 4 h)
def forced (t : Code) (x : Nat) := cleanStar x 0 && cleanStar x 1 && childClean t x
def initial : List Nat := (List.range 20).map (fun i => 2^i)
theorem zeroSpan (bs : List Nat) : 0 ∈ span bs := by
  induction bs with
  | nil => simp [span]
  | cons b bs ih => exact List.mem_append_left _ ih

theorem ofSpan (bs : List Nat) (q : Nat) (hq : q∈bs) : q∈span bs := by
  induction bs with
  | nil => simp at hq
  | cons b bs ih =>
    rcases List.mem_cons.mp hq with rfl|old
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨0,zeroSpan _,by simp⟩)
    · exact List.mem_append_left _ (ih old)

theorem xorSpan (bs : List Nat) {x y} (hx : x∈span bs) (hy : y∈span bs) : x ^^^ y ∈ span bs := by
  induction bs generalizing x y with
  | nil => simp [span] at hx hy; simp [hx,hy,span]
  | cons b bs ih =>
    simp only [span, List.mem_append, List.mem_map] at hx hy ⊢
    rcases hx with hx|⟨v,hv,rfl⟩ <;> rcases hy with hy|⟨w,hw,rfl⟩
    · exact Or.inl (ih hx hy)
    · exact Or.inr ⟨x ^^^ w, ih hx hw, by ac_rfl⟩
    · exact Or.inr ⟨v ^^^ y, ih hv hy, by ac_rfl⟩
    · have eq : (v ^^^ b) ^^^ (w ^^^ b) = v ^^^ w := by
        calc
          _ = (v ^^^ w) ^^^ (b ^^^ b) := by ac_rfl
          _ = _ := by simp
      left; rw [eq]; exact ih hv hw

theorem allForms (S : Finset V) : formMask S∈span initial := by
  have num : ∀v:V, 2^idx v∈initial := by decide +kernel
  induction S using Finset.induction_on with
  | empty => simpa [formMask] using zeroSpan initial
  | @insert v S hn ih => rw [mask_insert S hn]; exact xorSpan _ (ofSpan _ _ (num v)) ih


def privatePerm (p : Fin 5) (x : Nat) : Bool :=
  (List.finRange 5).all (fun i => if i=p then !(hitRow x i) else hitRow x i) &&
  (List.finRange 5).all (fun i => (List.finRange 5).all (fun j => decide (i=j) || cleanPair x i j))
def seedSide (b : Bool) : Nat := if b then 33825 else 525345
def omitted (b : Bool) : Fin 5 := if b then 4 else 3
def samples : List (Bool × Nat) := [(false,264225),(false,524865),(false,133185),(false,262785),(false,525330),(false,524610),(false,67650),(false,524820),(false,262680),(true,18465),(true,10305),(true,6210)]
def d (z : Bool × Nat) : Nat := z.2 ^^^ seedSide z.1
theorem privateSeeds : ∀ b, privatePerm (omitted b) (seedSide b) = true := by decide +kernel
theorem privateSamples : ∀ z∈samples, privatePerm (omitted z.1) z.2 = true := by decide +kernel
def pivots := samples.foldl (fun b r => basisStep (d r) b) initial
def decode (q : Nat) : Code := ⟨(((q >>> 12) % 16) +
    (if q.testBit 0 != q.testBit 12 then 16 else 0) +
    (if q.testBit 4 != q.testBit 12 then 32 else 0) +
    (if q.testBit 8 != q.testBit 12 then 64 else 0)) % 128, Nat.mod_lt _ (by decide)⟩
def accepts (q : Nat) := (parity (seedSide false) q == parity (seedSide true) q) ||
    (q == formMask (potential (decode q)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem exhaustive : (span pivots).all accepts = true := by decide +kernel

theorem shrink (rs : List (Bool × Nat)) (bs : List Nat) (q : Nat) (mem : q∈span bs)
    (zeros : ∀r∈rs, parity (d r) q = false) :
    q ∈ span (rs.foldl (fun b r => basisStep (d r) b) bs) := by
  induction rs generalizing bs with
  | nil => exact mem
  | cons r rs ih => exact ih _ (step_sound _ _ _ mem (zeros r (by simp))) (fun v h => zeros v (by simp [h]))

theorem rootPotential (S : Finset V) (side : Bool) (priv :
    ∀ (b : Bool) (x : Nat), privatePerm (omitted b) x = true →
      parity x (formMask S) = (side ^^ b)) :
    S = potential (decode (formMask S)) := by
  have mem := shrink samples initial (formMask S) (allForms S) (by
    intro z hz
    rw [d,parity_left,priv _ _ (privateSamples z hz),priv _ _ (privateSeeds z.1)]
    cases side <;> cases z.1 <;> rfl)
  have ok := List.all_eq_true.mp exhaustive (formMask S) mem
  have ne : parity (seedSide false) (formMask S) ≠ parity (seedSide true) (formMask S) := by
    rw [priv _ _ (privateSeeds false),priv _ _ (privateSeeds true)]
    cases side <;> decide
  have masks : formMask S = formMask (potential (decode (formMask S))) := by
    simpa [accepts,ne] using ok
  ext x
  have h := congrArg (fun n : Nat => n.testBit (idx x)) masks
  change (formMask S).testBit (idx x) = (formMask (potential (decode (formMask S)))).testBit (idx x) at h
  simpa only [bit_mask,decide_eq_decide] using h
end PEqualNP.Outside.L_pcx_178_affine
