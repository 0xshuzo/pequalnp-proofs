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



abbrev Key := Fin 45
abbrev Row := Fin 5
abbrev Hole := Fin 4
def rowKey (i : Row) : Key := ⟨i.val,by omega⟩
def pairPos (i j : Row) : Nat :=
  let a := min i.val j.val
  let b := max i.val j.val
  a * (9-a) / 2 + (b-a-1)
def edgeKey (i j : Row) (h : Hole) : Key := ⟨(5 + 10*h.val + pairPos i j)%45,Nat.mod_lt _ (by decide)⟩
theorem edgeSymm (i j : Row) (h : Hole) : edgeKey i j h = edgeKey j i h := by
  simp [edgeKey,pairPos,min_comm,max_comm]
def ij : Array (Row × Row) := #[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def bad (x : Nat) (k : Key) : Bool :=
  if k.val < 5 then ((x >>> (4*k.val)) &&& 15) == 0
  else let v := ij[(k.val-5)%10]!
       let h := (k.val-5)/10
       x.testBit (4*v.1.val+h) && x.testBit (4*v.2.val+h)

def onlyMask (m x : Nat) := (List.finRange 45).all fun k => !(bad x k) || m.testBit k.val
def noHit (m x : Nat) := (List.finRange 45).all fun k => !(bad x k) || !m.testBit k.val
def miss (C : LinClause V) (a : Nat) := ¬ LinClauseSat (assignment a) C

set_option maxHeartbeats 1600000 in
theorem twoSummaries (D E : LinClause V)
    (neededD : ∀x, onlyMask 515899884001 x = true → miss D x)
    (allowedD : ∀x, noHit 515899884001 x = true → ¬miss D x)
    (neededE : ∀x, onlyMask 4367952351203 x = true → ¬miss D x → miss E x)
    (allowedE : ∀x, noHit 3852052467202 x = true → ¬miss D x → ¬miss E x) : False := by
  have d74880 : miss D 74880 := neededD _ (by decide)
  have d74881 : miss D 74881 := neededD _ (by decide)
  have d74882 : miss D 74882 := neededD _ (by decide)
  have d74884 : miss D 74884 := neededD _ (by decide)
  have d74888 : miss D 74888 := neededD _ (by decide)
  have d75840 : miss D 75840 := neededD _ (by decide)
  have d82560 : miss D 82560 := neededD _ (by decide)
  have d84000 : miss D 84000 := neededD _ (by decide)
  have d136320 : miss D 136320 := neededD _ (by decide)
  have d147840 : miss D 147840 := neededD _ (by decide)
  have d149520 : miss D 149520 := neededD _ (by decide)
  have good74752 : ¬miss D 74752 := by
    intro hyp
    exact allowedD 69992 (by decide) (flat_closed D _ _ _ (flat_closed D _ _ _ (flat_closed D _ _ _ hyp d74880 d74888) d75840 d84000) d136320 d147840)
  have good75776 : ¬miss D 75776 := by
    intro hyp
    exact allowedD 70052 (by decide) (flat_closed D _ _ _ (flat_closed D _ _ _ hyp d74884 d84000) d136320 d147840)
  have good76816 : ¬miss D 76816 := by
    intro hyp
    exact allowedD 139489 (by decide) (flat_closed D _ _ _ (flat_closed D _ _ _ hyp d74881 d75840) d84000 d149520)
  have good83968 : ¬miss D 83968 := by
    intro hyp
    exact allowedD 70082 (by decide) (flat_closed D _ _ _ (flat_closed D _ _ _ hyp d74882 d75840) d136320 d147840)
  have good92176 : ¬miss D 92176 := by
    intro hyp
    exact allowedD 131809 (by decide) (flat_closed D _ _ _ (flat_closed D _ _ _ (flat_closed D _ _ _ hyp d74880 d74881) d75840 d82560) d84000 d149520)
  have good149504 : ¬miss D 149504 := by
    intro hyp
    exact allowedD 139969 (by decide) (flat_closed D _ _ _ (flat_closed D _ _ _ hyp d74880 d74881) d75840 d82560)
  have good215056 : ¬miss D 215056 := by
    intro hyp
    exact allowedD 8929 (by decide) (flat_closed D _ _ _ (flat_closed D _ _ _ (flat_closed D _ _ _ hyp d74880 d74881) d75840 d82560) d84000 d149520)
  have good16 : ¬miss D 16 := by
    intro hyp
    exact allowedD 18 (by decide) (flat_closed D _ _ _ hyp d74880 d74882)
  have b74752 : miss E 74752 := neededE _ (by decide) good74752
  have b75776 : miss E 75776 := neededE _ (by decide) good75776
  have b76816 : miss E 76816 := neededE _ (by decide) good76816
  have b83968 : miss E 83968 := neededE _ (by decide) good83968
  have b92176 : miss E 92176 := neededE _ (by decide) good92176
  have b149504 : miss E 149504 := neededE _ (by decide) good149504
  have b215056 : miss E 215056 := neededE _ (by decide) good215056
  exact allowedE 16 (by decide) good16 (flat_closed E _ _ _ (flat_closed E _ _ _ (flat_closed E _ _ _ b74752 b75776 b76816) b83968 b92176) b149504 b215056)
end PEqualNP.Outside.L_pcx_178_affine
