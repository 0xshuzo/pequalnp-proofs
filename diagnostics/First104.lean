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


structure FirstWitness where
  mask : Nat
  start : Nat
  pairs : List (Nat × Nat)

def combine (v : Nat) : List (Nat × Nat) → Nat
  | [] => v
  | (a,b)::rest => combine (v ^^^ a ^^^ b) rest

theorem combine_miss (D : LinClause V) (v : Nat) (l : List (Nat × Nat))
    (hv : miss D v) (hl : ∀p∈l, miss D p.1 ∧ miss D p.2) : miss D (combine v l) := by
  induction l generalizing v with
  | nil => exact hv
  | cons p l ih =>
    exact ih _ (flat_closed D _ _ _ hv (hl p List.mem_cons_self).1 (hl p List.mem_cons_self).2)
      (fun p h => hl p (List.mem_cons_of_mem _ h))

def goodWitness (w : FirstWitness) : Bool :=
  onlyMask w.mask w.start && (w.pairs.all fun p => onlyMask w.mask p.1 && onlyMask w.mask p.2) &&
    noHit w.mask (combine w.start w.pairs)

theorem reject (w : FirstWitness) (valid : goodWitness w=true) (D : LinClause V)
    (needed : ∀x, onlyMask w.mask x=true → miss D x)
    (allowed : ∀x, noHit w.mask x=true → ¬miss D x) : False := by
  obtain ⟨⟨one,rest⟩,no⟩ := (show
    (onlyMask w.mask w.start=true ∧ (w.pairs.all fun p => onlyMask w.mask p.1 && onlyMask w.mask p.2)=true) ∧
    noHit w.mask (combine w.start w.pairs)=true by simpa only [goodWitness,Bool.and_eq_true] using valid)
  apply allowed _ no (combine_miss D _ _ (needed _ one) ?_)
  intro p hp
  have hh := List.all_eq_true.mp rest p hp
  simp only [Bool.and_eq_true] at hh
  exact ⟨needed _ hh.1,needed _ hh.2⟩

def block0 : List FirstWitness := [⟨608,164161,[(270616,426257)]⟩,⟨1184,137281,[(266776,399377)]⟩,⟨2336,74776,[(149521,215057)]⟩,⟨4288,135496,[(266881,397697)]⟩,⟨5632,135496,[(266776,397592)]⟩,⟨5856,135496,[(266776,397592)]⟩,⟨5888,74881,[(75841,82561),(84001,136216),(266536,397592)]⟩,⟨6336,74776,[(75796,82456),(83986,135496),(135556,136321),(266626,397697)]⟩]
theorem valid0 : block0.all goodWitness=true := by decide +kernel
def block1 : List FirstWitness := [⟨6432,74776,[(149521,215057)]⟩,⟨8512,74056,[(147841,213377)]⟩,⟨9376,74056,[(74116,136216),(136321,137236),(266776,399377)]⟩,⟨9536,74056,[(147841,213377)]⟩,⟨10752,74056,[(147736,213272)]⟩,⟨10880,74056,[(147736,213272)]⟩,⟨11104,74056,[(147736,213272)]⟩,⟨16768,70216,[(136321,201857)]⟩]
theorem valid1 : block1.all goodWitness=true := by decide +kernel
def block2 : List FirstWitness := [⟨16992,70216,[(70276,147736),(147841,164116),(270616,426257)]⟩,⟨17280,70216,[(136321,201857)]⟩,⟨19456,70216,[(136216,201752)]⟩,⟨19520,70216,[(136216,201752)]⟩,⟨19872,70216,[(136216,201752)]⟩,⟨28672,70216,[(135496,201032)]⟩,⟨28704,70216,[(135496,201032)]⟩,⟨29120,70216,[(135496,201032)]⟩]
theorem valid2 : block2.all goodWitness=true := by decide +kernel
def block3 : List FirstWitness := [⟨32256,70216,[(135496,201032)]⟩,⟨32736,70216,[(135496,201032)]⟩,⟨622592,98882,[(266792,360994)]⟩,⟨1212416,74792,[(268322,337954)]⟩,⟨2392064,84002,[(136232,215074)]⟩,⟨4390912,74312,[(266882,336514)]⟩,⟨5767168,74312,[(266792,336424)]⟩,⟨5996544,74312,[(266792,336424)]⟩]
theorem valid3 : block3.all goodWitness=true := by decide +kernel
def block4 : List FirstWitness := [⟨6029312,74312,[(266792,336424)]⟩,⟨6488064,74312,[(266882,336514)]⟩,⟨6586368,84002,[(136232,215074)]⟩,⟨8716288,82562,[(135752,213634)]⟩,⟨9601024,74792,[(268322,337954)]⟩,⟨9764864,82562,[(135752,213634)]⟩,⟨11010048,82472,[(135752,213544)]⟩,⟨11141120,82472,[(135752,213544)]⟩]
theorem valid4 : block4.all goodWitness=true := by decide +kernel
def block5 : List FirstWitness := [⟨11370496,82472,[(135752,213544)]⟩,⟨17170432,74882,[(136322,205954)]⟩,⟨17399808,98882,[(266792,360994)]⟩,⟨17694720,74882,[(136322,205954)]⟩,⟨19922944,74792,[(136232,205864)]⟩,⟨19988480,74792,[(136232,205864)]⟩,⟨20348928,74792,[(136232,205864)]⟩,⟨29360128,74312,[(135752,205384)]⟩]
theorem valid5 : block5.all goodWitness=true := by decide +kernel
def block6 : List FirstWitness := [⟨29392896,74312,[(135752,205384)]⟩,⟨29818880,74312,[(135752,205384)]⟩,⟨33030144,74312,[(135752,205384)]⟩,⟨33521664,74312,[(135752,205384)]⟩,⟨637534208,98884,[(136264,230468)]⟩,⟨1241513984,82504,[(137284,215108)]⟩,⟨2449473536,75844,[(266824,337988)]⟩,⟨4496293888,82564,[(136324,214148)]⟩]
theorem valid6 : block6.all goodWitness=true := by decide +kernel
def block7 : List FirstWitness := [⟨5905580032,82504,[(136264,214088)]⟩,⟨6140461056,82504,[(136264,214088)]⟩,⟨6174015488,82504,[(136264,214088)]⟩,⟨6643777536,82564,[(136324,214148)]⟩,⟨6744440832,75844,[(266824,337988)]⟩,⟨8925478912,74884,[(266884,337028)]⟩,⟨9831448576,82504,[(137284,215108)]⟩,⟨9999220736,74884,[(266884,337028)]⟩]
theorem valid7 : block7.all goodWitness=true := by decide +kernel
def block8 : List FirstWitness := [⟨11274289152,74824,[(266824,336968)]⟩,⟨11408506880,74824,[(266824,336968)]⟩,⟨11643387904,98884,[(136264,230468)]⟩,⟨17582522368,82564,[(266884,344708)]⟩,⟨17817403392,98884,[(136264,230468)]⟩,⟨18119393280,82564,[(266884,344708)]⟩,⟨20401094656,82504,[(266824,344648)]⟩,⟨20468203520,82504,[(266824,344648)]⟩]
theorem valid8 : block8.all goodWitness=true := by decide +kernel
def block9 : List FirstWitness := [⟨20837302272,82504,[(137284,215108)]⟩,⟨30064771072,82984,[(267304,345128)]⟩,⟨30098325504,82984,[(267304,345128)]⟩,⟨30534533120,82564,[(136324,214148)]⟩,⟨33822867456,82504,[(136264,214088)]⟩,⟨34326183936,82504,[(136264,214088)]⟩,⟨652835028992,74888,[(75848,82568),(136328,215176)]⟩,⟨1271310319616,98888,[(136328,230536)]⟩]
theorem valid9 : block9.all goodWitness=true := by decide +kernel
def block10 : List FirstWitness := [⟨2508260900864,74888,[(528968,599176)]⟩,⟨4604204941312,98888,[(137288,231496)]⟩,⟨6047313952768,98948,[(137348,231556)]⟩,⟨6287832121344,74888,[(75848,82568),(136328,215176)]⟩,⟨6322191859712,98948,[(137348,231556)]⟩,⟨6803228196864,98888,[(137288,231496)]⟩,⟨6906307411968,74888,[(528968,599176)]⟩,⟨9139690405888,75848,[(528968,600136)]⟩]
theorem valid10 : block10.all goodWitness=true := by decide +kernel
def block11 : List FirstWitness := [⟨10067403341824,98888,[(136328,230536)]⟩,⟨10239202033664,75848,[(528968,600136)]⟩,⟨11544872091648,75908,[(529028,600196)]⟩,⟨11682311045120,75908,[(529028,600196)]⟩,⟨11922829213696,74888,[(75848,82568),(136328,215176)]⟩,⟨18004502904832,98888,[(528968,623176)]⟩,⟨18245021073408,74888,[(75848,82568),(136328,215176)]⟩,⟨18554258718720,98888,[(528968,623176)]⟩]
theorem valid11 : block11.all goodWitness=true := by decide +kernel
def block12 : List FirstWitness := [⟨20890720927744,98948,[(529028,623236)]⟩,⟨20959440404480,98948,[(529028,623236)]⟩,⟨21337397526528,98888,[(136328,230536)]⟩,⟨30786325577728,100388,[(530468,624676)]⟩,⟨30820685316096,100388,[(530468,624676)]⟩,⟨31267361914880,98888,[(137288,231496)]⟩,⟨34634616274944,98948,[(137348,231556)]⟩,⟨35150012350464,74888,[(75848,82568),(136328,215176)]⟩]
theorem valid12 : block12.all goodWitness=true := by decide +kernel
end PEqualNP.Outside.L_pcx_178_affine
