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

abbrev Row := Nat × List (Fin 45 × Nat)
def samples : List Row := [(540705, [(2,540690)]), (532545, [(2,532500)]), (270465, [(2,270360)]), (541185, [(1,540930)]), (533505, [(1,532740)]), (272385, [(1,270600)]), (533505, [(1,529410)]), (541185, [(1,528900)]), (295425, [(1,266760)]), (164865, [(1,99330)]), (295425, [(1,98820)]), (541185, [(1,82440)]), (69924, [(12,528706), (13,98626), (14,71746)]), (69928, [(12,528706), (13,98626), (14,71746)]), (69932, [(12,528706), (13,98626), (14,71746)]), (69960, [(12,528706), (13,98626), (14,71746)]), (69992, [(12,528706), (13,98626), (14,71746)]), (70472, [(12,528706), (13,98626), (14,71746)]), (77828, [(1,541185), (2,540705), (14,71746)]), (196612, [(1,541185), (2,540705), (3,525345)])]
def firsts := samples.take 12
def tails := samples.drop 12
def diff (r : Row) := r.1 ^^^ (r.2.headD (0,0)).2
def matchR (q : Nat) (r : Row) := r.2.any (fun p => parity r.1 q == parity p.2 q)
def reflected := (span (firsts.foldl (fun bs r => basisStep (diff r) bs) initial)).all
  (fun q => q == 0 || !(tails.all (matchR q)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem numerical : reflected = true := by decide +kernel

theorem shrink (rs : List Row) (bs : List Nat) (q : Nat) (mem : q∈span bs)
    (zeros : ∀r∈rs, parity (diff r) q = false) :
    q ∈ span (rs.foldl (fun b r => basisStep (diff r) b) bs) := by
  induction rs generalizing bs with
  | nil => exact mem
  | cons r rs ih => exact ih _ (step_sound _ _ _ mem (zeros r (by simp))) (fun v h => zeros v (by simp [h]))

theorem nonzeroCut (S : Finset V) (nz : S.Nonempty) :
    ∃ r∈samples, matchR (formMask S) r = false := by
  classical
  by_contra! hn
  let q := formMask S
  have h : ∀ r∈samples, matchR q r = true := by
    intro r hr
    cases hz : matchR q r <;> simp_all [q]
  have singleton : ∀r∈firsts, ∀p∈r.2, p=(r.2.headD (0,0)) := by decide +kernel
  have mem := shrink firsts initial q (allForms S) (by
    intro r hr
    obtain ⟨p,hp,tag⟩ := List.any_eq_true.mp (h r (List.mem_of_mem_take hr))
    rw [singleton r hr p hp] at tag
    rw [diff,parity_left,beq_iff_eq.mp tag]
    simp)
  have pass := List.all_eq_true.mp numerical q mem
  have ok : tails.all (matchR q) = true := List.all_eq_true.mpr fun r hr => h r (List.mem_of_mem_drop hr)
  have neq : q ≠ 0 := mask_nz nz
  simp [ok,neq] at pass

def axisBank : List (LinClause V) := [linOfClause (Finset.univ.image (fun j : Fin 4 => ((0,j),true))), linOfClause (Finset.univ.image (fun j : Fin 4 => ((1,j),true))), linOfClause (Finset.univ.image (fun j : Fin 4 => ((2,j),true))), linOfClause (Finset.univ.image (fun j : Fin 4 => ((3,j),true))), linOfClause (Finset.univ.image (fun j : Fin 4 => ((4,j),true))), linOfClause {((0,0), false), ((1,0), false)}, linOfClause {((0,0), false), ((2,0), false)}, linOfClause {((0,0), false), ((3,0), false)}, linOfClause {((0,0), false), ((4,0), false)}, linOfClause {((1,0), false), ((2,0), false)}, linOfClause {((1,0), false), ((3,0), false)}, linOfClause {((1,0), false), ((4,0), false)}, linOfClause {((2,0), false), ((3,0), false)}, linOfClause {((2,0), false), ((4,0), false)}, linOfClause {((3,0), false), ((4,0), false)}, linOfClause {((0,1), false), ((1,1), false)}, linOfClause {((0,1), false), ((2,1), false)}, linOfClause {((0,1), false), ((3,1), false)}, linOfClause {((0,1), false), ((4,1), false)}, linOfClause {((1,1), false), ((2,1), false)}, linOfClause {((1,1), false), ((3,1), false)}, linOfClause {((1,1), false), ((4,1), false)}, linOfClause {((2,1), false), ((3,1), false)}, linOfClause {((2,1), false), ((4,1), false)}, linOfClause {((3,1), false), ((4,1), false)}, linOfClause {((0,2), false), ((1,2), false)}, linOfClause {((0,2), false), ((2,2), false)}, linOfClause {((0,2), false), ((3,2), false)}, linOfClause {((0,2), false), ((4,2), false)}, linOfClause {((1,2), false), ((2,2), false)}, linOfClause {((1,2), false), ((3,2), false)}, linOfClause {((1,2), false), ((4,2), false)}, linOfClause {((2,2), false), ((3,2), false)}, linOfClause {((2,2), false), ((4,2), false)}, linOfClause {((3,2), false), ((4,2), false)}, linOfClause {((0,3), false), ((1,3), false)}, linOfClause {((0,3), false), ((2,3), false)}, linOfClause {((0,3), false), ((3,3), false)}, linOfClause {((0,3), false), ((4,3), false)}, linOfClause {((1,3), false), ((2,3), false)}, linOfClause {((1,3), false), ((3,3), false)}, linOfClause {((1,3), false), ((4,3), false)}, linOfClause {((2,3), false), ((3,3), false)}, linOfClause {((2,3), false), ((4,3), false)}, linOfClause {((3,3), false), ((4,3), false)}]
def axis (i : Fin 45) : LinClause V := axisBank.getD i.val ∅
def sat (a : V → Bool) (C : LinClause V) : Bool :=
  decide (∃ q ∈ C, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true))
theorem sat_true {a : V→Bool} {C : LinClause V} : sat a C = true ↔ LinClauseSat a C := by
  unfold sat LinClauseSat LinEqSat
  rw [decide_eq_true_eq]
def certified (r : Row) : Bool := decide
  ((∀i : Fin 45, sat (assignment r.1) (axis i) = false → ∃p∈r.2, p.1=i) ∧
    ∀p∈r.2, ∀j : Fin 45, sat (assignment p.2) (axis j) = false → j=p.1)
set_option maxHeartbeats 0 in
theorem certAll : samples.all certified = true := by decide +kernel

theorem noTags (S : Finset V) (nz : S.Nonempty) (tags : Fin 45→Bool)
    (hit : ∀a, ∃i, tags i=parity a (formMask S) ∧ ¬LinClauseSat (assignment a) (axis i)) : False := by
  obtain ⟨r,hr,hbad⟩:=nonzeroCut S nz
  have ok := of_decide_eq_true (List.all_eq_true.mp certAll r hr)
  obtain ⟨i,ct,ci⟩:=hit r.1
  have ns {a : V→Bool} {C : LinClause V} (no : ¬LinClauseSat a C) : sat a C=false := by
    cases ht : sat a C <;> simp_all [sat_true]
  obtain ⟨p,hp,eq⟩:=ok.1 i (ns ci)
  obtain ⟨j,jt,ji⟩:=hit p.2
  have je := ok.2 p hp j (ns ji)
  have matched : matchR (formMask S) r = true := List.any_eq_true.mpr ⟨p,hp,beq_iff_eq.mpr (by rw [←ct,←jt,je,eq])⟩
  simp [matched] at hbad

end PEqualNP.Outside.L_pcx_178_affine
