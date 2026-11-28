import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_178.StarOrder

abbrev Row := Fin 5
abbrev Hole := Fin 4
def precedes (u v : Row) : Prop := u=v ∨ (u.val<3 ∧ u.val<v.val)
def active (owner : Row → Row → Hole → Row) (p : Row) (h : Hole) : Prop :=
    ∃ q : Row, q≠p ∧ owner p q h = p

/-- The first three proper stops are sorted shared vertices. The two final
vertices are the incomparable root children. The two geometric hypotheses
say that an edge belongs to an endpoint and that every active endpoint is
downstream of all four owners of its incident edges in that column. -/
theorem peeling (owner : Row → Row → Hole → Row)
    (symm : ∀ i j h, owner i j h = owner j i h)
    (endpoint : ∀ i j h, i≠j → owner i j h=i ∨ owner i j h=j)
    (broadcast : ∀ i j h, i≠j → active owner i h → precedes (owner i j h) i) :
    (∀ i j h, i.val<3 → i.val<j.val → owner i j h=i) ∧
    ∀ h, (active owner 3 h ∧ ¬active owner 4 h) ∨ (active owner 4 h ∧ ¬active owner 3 h) := by
  have served (i j : Row) (h : Hole) (ne : i≠j) : active owner i h ∨ active owner j h := by
    rcases endpoint i j h ne with hi|hj
    · exact Or.inl ⟨j,Ne.symm ne,hi⟩
    · exact Or.inr ⟨i,ne,(symm j i h).trans hj⟩
  have exclusive (h : Hole) : ¬(active owner 3 h ∧ active owner 4 h) := by
    rintro ⟨a,b⟩
    have l := broadcast 3 4 h (by decide) a
    have r := broadcast 4 3 h (by decide) b
    rw [symm 4 3 h] at r
    rcases endpoint 3 4 h (by decide) with s|s
    · rw [s] at r
      exact (by unfold precedes; decide : ¬precedes 3 4) r
    · rw [s] at l
      exact (by unfold precedes; decide : ¬precedes 4 3) l
  constructor
  · intro i j h ii ij
    have activeI : active owner i h := by
      by_contra no
      have p := served i 3 h (by intro eq; rw [eq] at ii; omega)
      have q := served i 4 h (by intro eq; rw [eq] at ii; omega)
      exact exclusive h ⟨p.resolve_left no,q.resolve_left no⟩
    have ne : i≠j := fun eq => (Nat.ne_of_lt ij) (congrArg Fin.val eq)
    have l := broadcast i j h ne activeI
    rcases endpoint i j h ne with hi|hj
    · exact hi
    · rw [hj] at l
      rcases l with eq|⟨_,lt⟩
      · exact False.elim (ne eq.symm)
      · omega
  · intro h
    rcases served 3 4 h (by decide) with a|b
    · exact Or.inl ⟨a,fun b => exclusive h ⟨a,b⟩⟩
    · exact Or.inr ⟨b,fun a => exclusive h ⟨a,b⟩⟩
end PEqualNP.Outside.L_pcx_178.StarOrder
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
def before (i j : Row) : Prop := i=j ∨ (i.val < 3 ∧ i.val < j.val)
instance instBefore (i j : Row) : Decidable (before i j) := inferInstanceAs (Decidable (i=j ∨ (i.val < 3 ∧ i.val < j.val)))
def only (x : Nat) (i j : Key) := (List.finRange 45).all fun k => !(bad x k) || k == i || k == j
theorem only_spec {x : Nat} {i j : Key} (h : only x i j = true) (k : Key) (b : bad x k = true) :
    k=i ∨ k=j := by
  have one := List.all_eq_true.mp h k (List.mem_finRange k)
  simpa [b] using one
structure Model where
  K : Row → LinClause V
  owner : Key → Row
  row : ∀ i, owner (rowKey i)=i
  root : ∀ x : Nat, ∃ i : Row, ¬LinClauseSat (assignment x) (K i)
  trace : ∀ x : Nat, ∀ i : Row, ¬LinClauseSat (assignment x) (K i) →
    ∃ k : Key, bad x k = true ∧ before (owner k) i ∧ ¬LinClauseSat (assignment x) (K (owner k))

theorem gather (M : Model) {x : Nat} {i : Row} (take : ∀ k, bad x k=true → M.owner k=i) :
    ¬LinClauseSat (assignment x) (M.K i) := by
  obtain ⟨u,badU⟩ := M.root x
  obtain ⟨k,fb,_,hit⟩ := M.trace x u badU
  exact (take k fb) ▸ hit

def view (i j k p : Row) (h : Hole) : Key :=
  if i=j ∨ i=k then edgeKey i p h else rowKey p
-- Per ordered owner, collision, and target label, the table points are private
-- to that owner and the hypothesized edge. Their XOR has only the target fault.
def boards : Array Nat := #[0,4396,4456,4636,4652,4680,4681,4682,4684,4696,4712,4740,4748,4801,4802,4804,4808,4936,5160,5162,5164,5194,5224,5250,5282,5284,5656,5672,5704,5761,5762,5764,5768,6180,6188,6248,6278,6308,6724,6728,6788,7202,8476,8492,8520,8521,8522,8536,8552,8641,8642,8732,8792,9032,9240,9241,9345,9361,9496,9512,9601,9602,11281,12616,12872,13336,13352,13384,13441,13442,13444,13448,14404,14408,14468,16680,16684,16714,16744,16804,17224,17284,17434,17464,17704,21032,21064,21122,21124,21544,22562,24856,24961,26641,33060,33068,33128,33158,33188,33608,33668,34838,34868,35108,37448,37508,38948,65836,65896,66076,66092,66120,66121,66122,66124,66136,66152,66180,66188,66241,66242,66244,66248,66376,66600,66602,66604,66634,66664,66690,66722,66724,67096,67112,67144,67201,67202,67204,67208,67620,67628,67688,67718,67748,68164,68168,68228,68642,69676,69736,70156,70216,70276,70336,70696,71176,71296,73756,73772,73800,73801,73802,73804,73816,73832,73860,73868,73921,73922,73924,73928,73996,74056,74116,74176,74252,74312,74372,74432,74760,74761,74762,74764,74776,74792,74824,74880,74881,74882,74884,74888,74896,74912,74944,75016,75136,75272,75392,75780,75788,75796,75812,75840,75841,75842,75844,75848,75908,75968,76801,76802,76804,76808,76816,76832,76864,76928,77896,78856,78976,81960,81962,81964,81994,82024,82050,82082,82084,82216,82306,82440,82442,82444,82456,82472,82504,82560,82561,82562,82564,82568,82592,82624,82954,82984,83074,83104,83464,83584,83970,83986,84000,84001,84002,84004,84008,84034,84098,84482,84484,84512,84544,90136,90152,90184,90241,90242,90244,90248,90376,90496,90632,90752,91144,91264,92161,92162,92164,92168,92176,92192,92224,92288,98340,98348,98408,98438,98468,98820,98828,98852,98880,98882,98884,98888,98948,99008,99362,99364,99368,99394,99458,99848,99968,100358,100388,100418,100448,100868,100928,106564,106568,106628,107524,107528,107584,107648,108548,108608,114722,115202,115232,131356,131372,131400,131401,131402,131416,131432,131521,131522,131612,131672,131912,132120,132121,132225,132241,132376,132392,132481,132482,134161,135196,135212,135240,135241,135242,135256,135272,135361,135362,135436,135496,135556,135616,135692,135752,135812,135872,136200,136201,136202,136216,136232,136264,136320,136321,136322,136324,136328,136336,136352,136456,136576,136712,136832,137236,137252,137281,137282,137284,137288,137348,138241,138242,138256,138272,139292,139352,139532,139592,139652,139712,140312,140552,140672,143432,144392,144512,147480,147481,147585,147601,147720,147721,147736,147752,147784,147840,147841,147842,147856,147992,148504,149505,149520,149521,149761,149776,151576,151592,151681,151682,151816,151936,152072,152192,153601,153602,153616,153632,164116,164161,164228,164881,165908,180241,180481,180496,196936,197192,197656,197672,197704,197761,197762,197764,197768,198724,198728,198788,200776,201736,201856,204872,205832,205952,213016,213032,213064,213121,213122,213124,213128,213256,213376,213512,213632,214024,214144,215041,215042,215044,215048,215056,215072,215104,215168,229444,229448,229508,230404,230408,230464,230528,231428,231488,262440,262444,262474,262504,262564,262984,263044,263194,263224,263464,266280,266284,266314,266344,266404,266760,266764,266776,266792,266824,266880,266881,266882,266884,266944,267274,267304,267394,267424,267784,267904,268322,268324,268354,268804,268864,270616,270664,270721,270724,270872,271384,272401,274504,274564,275464,275584,276484,276544,278554,278584,278794,278824,278914,278944,279064,279169,279304,279424,280594,282664,283144,283264,295441,328232,328264,328322,328324,328744,329762,335912,335944,336002,336004,336392,336512,336904,337024,337922,337924,337952,337984,344104,344584,344704,360482,360962,360992,393496,393601,395281,397336,397441,397576,397696,399361,399376,426001,426241,426256,524580,524588,524648,524678,524708,525128,525188,526358,526388,526628,528420,528428,528488,528518,528548,528900,528908,528960,528968,529028,529088,529448,529538,529928,530048,530438,530468,530498,530528,530948,531008,532808,532868,534548,536648,536708,537608,537728,538628,538688,557078,557108,557318,557348,557378,557408,557588,557633,557828,557888,558098,561188,561668,561728,590408,590468,591908,598088,598148,599048,599168,600068,600128,622628,623108,623168]
def triples : Array Nat := #[0,437683617,437682585,437682542,437682362,0,430342553,430336410,430335342,430335162,0,385253742,385246574,385203567,385202362,0,196509882,196502714,196458682,196275387,195225786,432429242,439769290,460740899,615956988,195225786,389393594,405122250,451273964,612754940,195225786,200465594,223534282,292757740,498329966,195225786,372606138,392529082,446006508,610633212,195225786,182628538,204648634,283291884,488871278,195225786,160586938,163732666,229792954,476208494,0,265549053,265546988,265546938,265664763,0,249818348,249805038,249802938,249936108,0,197389498,197374138,197324988,197507258,0,386251003,386250988,386250938,386253168,195225786,252946618,272869578,336832803,603228668,195225786,201515194,224583882,293807340,595797500,195225786,390443194,406171850,452323564,499509484,195225786,186826938,206749882,285393132,590529020,195225786,376804538,394630330,448107756,491099372,195225786,412490938,415636666,418782574,479599802,0,215168205,215165114,215199946,215478474,0,198387898,198374589,198422714,198701242,0,250851530,250851514,250854639,251130092,0,536342730,536342714,536342764,536346111,195225786,202564794,225633482,330491171,507818350,195225786,253996218,273919178,294890698,500433262,195225786,537390266,548924618,562556106,597159114,195225786,258199738,260296940,287559866,493080942,195225786,541591738,543688940,560466106,592971962,195225786,568881338,573075692,577274222,600342714,0,199424190,199436474,199527610,199849146,0,216213690,216217806,216304842,216626378,0,308579514,308579530,308582694,308901155,0,636056762,636056778,636056867,636058206,195225786,218315978,226704570,295910636,501482862,195225786,310680778,318020794,331652282,508861806,195225786,638155978,642350266,655981754,680099002,195225786,322225354,324323564,333760698,510970222,195225786,646551754,648649964,658087098,682204346,195225786,664394954,668590316,672787822,685370554,437683617,0,437681556,437681512,437681331,425093299,187878579,438724806,459719910,614909431,378911923,187878579,403041459,449178854,611708407,188935347,187878579,219360435,288566502,494137704,426147220,0,426138006,426135912,426135731,381058408,0,381047144,381005163,381001907,192314547,0,192303283,192258227,192076983,369461427,187878579,391480499,444957926,609584631,179483827,187878579,203600051,282243302,487821672,157442227,187878579,162684083,228744371,475159912,265549053,0,265544934,265544883,265658617,242464947,187878579,270776518,335843558,602182135,189984947,187878579,220410035,289616102,593703415,379961523,187878579,404091059,450228454,495317222,245621990,0,245606634,245602483,245735654,193193139,0,193173683,193126584,193306803,382050553,0,382050534,382050483,382054764,183682227,187878579,205701299,284344550,589480439,373659827,187878579,393581747,447059174,490050790,409346227,187878579,414588083,417733992,478551219,215168205,0,215161011,215193798,215473350,191034547,187878579,221443270,328398112,505719144,243514547,187878579,271826118,290700486,496236904,529005747,187878579,547880134,561511622,595066054,194189491,0,194176185,194222259,194501811,246651078,0,246651059,246656235,246930662,532143302,0,532143283,532143334,532147707,255055027,187878579,259248358,286511283,492032360,538447027,187878579,542640358,559417523,591923379,565736627,187878579,572027110,576224616,599293107,199424190,0,199432371,199524531,199847091,208877766,187878579,222509235,291715302,497286504,303339718,187878579,316971187,329554099,506763624,633960646,187878579,641300659,654932147,679049395,217258163,0,217267407,217350342,217672902,309625011,0,309625030,309632295,309947680,637103283,0,637103302,637103392,637107807,319080646,187878579,323273958,332711091,509920616,643407046,187878579,647600358,657037491,681154739,661250246,187878579,667540710,671738216,684320947,420906143,423003301,166886559,458673372,613981529,430336410,430328208,0,430328153,430327967,363183263,367377567,166886559,442875100,608695641,167963807,175303839,166886559,278115487,483636569,426133904,426138006,0,426131801,426131615,360033445,365276319,166886559,440773852,607642969,164813989,171105439,166886559,274965663,480486745,370559321,370557273,0,370509153,370500767,180766879,180764831,0,180708511,180531372,155347109,156395679,166886559,227695775,474111321,231994527,237237413,166886559,334800092,601138674,249805038,249791708,0,249791647,249914593,169013407,176353439,166886559,279113948,587395570,364232863,368427167,166886559,443924700,484819164,245597404,245606634,0,245592223,245720284,165863589,172155039,166886559,275964124,585294322,361083045,366325919,166886559,441823452,481669340,184779935,184774815,0,184729776,184902815,374695137,374695132,0,374695071,374707557,407251109,408299679,166886559,416685401,477502623,170079391,177419429,166886559,325358751,502568281,198374589,198349983,0,198406309,198690981,233044127,238287013,166886559,280214687,485735769,523772063,526917797,166886559,558365855,588774559,194155679,194176185,0,194211999,194496671,234094751,235121884,166886559,277064863,482585945,524821663,525855964,166886559,557313183,586673311,256077989,256077983,0,256102644,256362716,539478181,539478175,0,539478236,539494914,563645599,564690140,166886559,575172953,598241439,174258341,178452639,166886559,281264287,486785369,216217806,216175775,0,216296607,216619167,298101925,299150495,166886559,326408351,503617881,628720805,629769375,166886559,652834975,676952223,217224351,217267407,0,217345189,217667749,300201125,301243612,166886559,327457951,504667481,630818981,631864540,166886559,653884575,678001823,320105631,320105637,0,320128305,320428315,644438175,644438181,0,644438299,644455014,659159205,660203740,166886559,670686553,683269279,351700092,353797249,359040124,116505711,606619972,341207151,345401455,356935804,116505711,605567300,385203567,385171790,385171780,0,385171567,117632111,124972143,141749359,116505711,466808132,338057333,343300207,354834556,116505711,604516676,380977486,381005163,380975428,0,380975215,114482293,120773743,138599535,116505711,463658308,370491716,370489668,370509153,0,370479215,112373899,113422460,129151087,116505711,461549892,158679151,158677103,158666863,0,158489751,131331196,136574081,154399868,116505711,584588399,118732911,126072943,142850172,116505711,581433455,197324988,197264508,197264495,0,197464193,342256751,346451055,357985404,116505711,468041839,115583093,121874543,139700348,116505711,579332207,193070204,193126584,193065071,0,193269884,339106933,344349807,355884156,116505711,464892015,184681583,184676463,184729776,0,184881263,347501685,348550255,349541700,116505711,462787695,410325121,410325116,410325103,0,410393991,119747695,127087733,151204975,116505711,471200879,132314236,137557116,143848559,116505711,469091439,250854639,250729583,250736757,0,251109493,513293436,516439164,518536303,116505711,582483055,133358721,134407292,140698735,116505711,465941615,246535279,246656235,246542447,0,246915183,514339969,515388540,517485679,116505711,580381807,255979637,255979631,256102644,0,256352380,519586945,520635516,521668932,116505711,583534703,566730869,566730863,566730876,0,566784540,123926645,128120943,144898159,116505711,470141039,147011723,148060284,152254575,116505711,472250479,308582694,308401263,308423791,0,308883567,618245259,619293820,622439535,116505711,673806447,149109889,150158460,153304175,116505711,473300079,309449839,309632295,309472373,0,309932149,620343425,621391996,623489135,116505711,674856047,319958127,319958133,320128305,0,320417931,624538753,625587324,626628932,116505711,675911791,662253679,662253685,662253707,0,662298231,58098742,60195896,65438774,97944620,5248005,47605804,51800108,63334454,96888876,5248005,6667269,14007301,30784517,71679020,5248005,196275387,196141110,196141100,196141061,0,44576779,49698860,61233206,95836204,5248005,3517451,9808901,27634693,68529196,5248005,191946806,192076983,191944748,191944709,0,1410081,2458642,18187269,66421804,5248005,180412460,180410412,180531372,180400133,0,158392325,158390277,158380037,158489751,0,20182034,25424919,43250706,94630917,5248005,7583749,14923781,31701010,91469829,5248005,48427052,52621356,64155692,72544261,5248005,386253168,385899538,385899525,385921047,0,4433931,10725381,28551186,89368581,5248005,45277278,50520108,62054444,69394437,5248005,381705234,382054764,381700101,381726738,0,54018059,54706230,55754796,67289093,5248005,374365189,374360069,374707557,374386693,0,410038295,410038290,410038277,410393991,0,8598533,15938571,40055813,75707397,5248005,21165074,26407954,32699397,73593861,5248005,79936587,83082315,85179436,92519429,5248005,536346111,535833605,535840779,535899147,0,22209559,23258130,29549573,70444037,5248005,81158167,82029643,84126764,90418181,5248005,531639301,532147707,531646469,531704837,0,86407191,87281718,88330284,93573125,5248005,538986507,538986501,539494914,539044882,0,566307851,566307845,566307858,566784540,0,12777483,16971781,33748997,74643461,5248005,35862561,36911122,41105413,76756997,5248005,99915870,100964427,104110124,109352965,5248005,636058206,635448325,635470853,635533317,0,37960727,39009298,42155013,77806597,5248005,102156311,103062603,105159724,110402565,5248005,636496901,637107807,636519435,636581899,0,106352663,107267126,108315692,111461381,5248005,643859461,643859467,644455014,643921953,0,661747717,661747723,661747745,662298231,0]

def triple (i j k p : Row) (h : Hole) : Nat × Nat × Nat :=
  let v := triples[(i.val*40+10*h.val+pairPos j k)*5+p.val]!
  (boards[v%1024]!,boards[(v/1024)%1024]!,boards[v/1048576]!)
def test (i j k p : Row) (h : Hole) : Bool :=
  let t := triple i j k p h
  let a := rowKey i
  let e := edgeKey j k h
  let target := view i j k p h
  only t.1 a e && only t.2.1 a e && only t.2.2 a e && only (t.1 ^^^ t.2.1 ^^^ t.2.2) target target
set_option maxHeartbeats 0 in
set_option maxRecDepth 5000 in
theorem tests (i : Row) : ∀ j k p : Row, ∀ h : Hole, j.val < k.val →
    ((i=j ∨ i=k) → p≠i) → test i j k p h = true := by
  fin_cases i <;> decide +kernel

theorem predecessor (M : Model) (i j k p : Row) (h : Hole) (ord : j.val < k.val)
    (distinct : (i=j ∨ i=k) → p≠i) (owns : M.owner (edgeKey j k h)=i) :
    before (M.owner (view i j k p h)) i := by
  let t := triple i j k p h
  have good := tests i j k p h ord distinct
  change (only t.1 (rowKey i) (edgeKey j k h) && only t.2.1 (rowKey i) (edgeKey j k h) &&
    only t.2.2 (rowKey i) (edgeKey j k h) &&
    only (t.1 ^^^ t.2.1 ^^^ t.2.2) (view i j k p h) (view i j k p h))=true at good
  simp only [Bool.and_eq_true] at good
  have ff (x : Nat) (w : only x (rowKey i) (edgeKey j k h)=true) :
     ¬LinClauseSat (assignment x) (M.K i) := by
    apply gather M
    intro a b
    rcases only_spec w a b with eq|eq
    · exact eq ▸ M.row i
    · exact eq ▸ owns
  have forced := flat_closed (M.K i) _ _ _ (ff _ good.1.1.1) (ff _ good.1.1.2) (ff _ good.1.2)
  obtain ⟨a,b,pr,_⟩ := M.trace _ _ forced
  obtain eq|eq := only_spec good.2 a b <;> simpa only [eq] using pr

theorem foreign (M : Model) {i j k : Row} (h : Hole) (ord : j.val<k.val)
    (owns : M.owner (edgeKey j k h)=i) : i=j ∨ i=k := by
  by_contra no
  have every (p : Row) : before p i := by
    have z := predecessor M i j k p h ord (fun f => False.elim (no f)) owns
    simpa [view,no,M.row] using z
  have a := every 3
  have b := every 4
  have incompatible : ∀ t : Row, ¬(before 3 t ∧ before 4 t) := by decide +kernel
  exact incompatible i ⟨a,b⟩

theorem endpoint (M : Model) (j k : Row) (h : Hole) (ne : j ≠ k) :
    M.owner (edgeKey j k h) = j ∨ M.owner (edgeKey j k h) = k := by
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact foreign M h lt rfl
  · rw [edgeSymm j k h]
    exact (foreign M h gt rfl).symm

theorem activeBefore (M : Model) (i p : Row) (h : Hole) (ne : i ≠ p)
    (active : ∃ j : Row, j≠i ∧ M.owner (edgeKey i j h)=i) :
    before (M.owner (edgeKey i p h)) i := by
  obtain ⟨j,ji,owns⟩ := active
  rcases lt_or_gt_of_ne ji with lt|gt
  · have own' := (congrArg M.owner (edgeSymm j i h)).trans owns
    have t := predecessor M i j i p h lt (fun _ => Ne.symm ne) own'
    simpa [view] using t
  · have t := predecessor M i i j p h gt (fun _ => Ne.symm ne) owns
    simpa [view] using t
def aa : Array Nat := #[74312,4388,4424,4388,4392,4388,4392,4388,4388,4132,4388,4132,4388,4132,4388,4132,4396,4388,4396,4388,4392,4388,4392,4388,4388,4132,4388,4132,4388,4132,4388,4132,4456,4388,4424,4388,4392,4388,4392,4388,4388,4132,4388,4132,4388,4132,4388,4132,4396,4388,4396,4388,4392,4388,4392,4388,4388,4132,4388,4132,4388,4132,4388,4132,8264,4388,8264,4388,8264,4388,8264,4388,4388,4392,4388,4392,4388,4396,4388,4396,8264,4388,8264,4388,8264,4388,8264,4388,4388,4392,4388,4392,4388,4424,4388,4456,8264,4388,8264,4388,8264,4388,8264,4388,4388,4392,4388,4392,4388,4396,4388,4396,8264,4388,8264,4388,8264,4388,8264,4388,4388,4392,4388,4392,4388,4424,4388,12872]
def bb : Array Nat := #[135240,65828,8776,65608,17448,65576,8776,65576,34852,8264,8776,8264,17448,8264,8776,8264,65580,65580,8776,65580,17448,65576,8776,65576,34852,8264,8776,8264,17448,8264,8776,8264,65640,65640,8776,65608,17448,65576,8776,65576,34852,8264,8776,8264,17448,8264,8776,8264,65580,65580,8776,65580,17448,65576,8776,65576,34852,8264,8776,8264,17448,8264,8776,8264,65572,65572,65572,65572,65572,65572,65572,65572,8264,65576,8264,65576,8264,65580,8264,65580,65572,65572,65572,65572,65572,65572,65572,65572,8264,65576,8264,65576,8264,65608,8264,65640,65572,65572,65572,65572,65572,65572,65572,65572,8264,65576,8264,65576,8264,65580,8264,65580,65572,65572,65572,65572,65572,65572,65572,65572,8264,65576,8264,65576,8264,65608,8264,135240]
def cc : Array Nat := #[204872,69924,12872,69704,21544,69672,12872,69672,38948,12616,12872,12616,21544,12616,12872,12616,69676,69676,12872,69676,21544,69672,12872,69672,38948,12616,12872,12616,21544,12616,12872,12616,69736,69736,12872,69704,21544,69672,12872,69672,38948,12616,12872,12616,21544,12616,12872,12616,69676,69676,12872,69676,21544,69672,12872,69672,38948,12616,12872,12616,21544,12616,12872,12616,74056,69668,74056,69668,74056,69668,74056,69668,12360,69672,12360,69672,12360,69676,12360,69676,74056,69668,74056,69668,74056,69668,74056,69668,12360,69672,12360,69672,12360,69704,12360,69736,74056,69668,74056,69668,74056,69668,74056,69668,12360,69672,12360,69672,12360,69676,12360,69676,74056,69668,74056,69668,74056,69668,74056,69668,12360,69672,12360,69672,12360,69704,12360,143432]


def chooseChild (q : Nat) (b : Bool) (x : Nat) : Row := if parity x q == b then 3 else 4
theorem finalChild (q : Nat) (b : Bool) (x : Nat) : chooseChild q b x = 3 ∨ chooseChild q b x = 4 := by
  unfold chooseChild; split <;> simp_all

theorem endsAgree : ∀ p c : Row, (p=3 ∨ p=4) → (c=3 ∨ c=4) → before p c → p=c := by
  decide +kernel

theorem chosenPrivate (M : Model) (q : Nat) (b : Bool)
    (split : ∀ x, ¬LinClauseSat (assignment x) (M.K (chooseChild q b x)))
    {x : Nat} {k : Key} (single : only x k k=true) (ep : M.owner k=3 ∨ M.owner k=4) :
    M.owner k=chooseChild q b x := by
  obtain ⟨a,hit,ord,_⟩ := M.trace _ _ (split x)
  have eq : a=k := (only_spec single a hit).elim id id
  exact endsAgree _ _ ep (finalChild _ _ _) (eq ▸ ord)

theorem seedRaw : ∀ x : Bool, only (seedSide x) (rowKey (omitted x)) (rowKey (omitted x)) = true := by decide +kernel
theorem sampleRaw : ∀ z ∈ samples, only z.2 (rowKey (omitted z.1)) (rowKey (omitted z.1))=true := by decide +kernel

theorem modelPotential (M : Model) (S : Finset V) (b : Bool)
    (split : ∀ x, ¬LinClauseSat (assignment x) (M.K (chooseChild (formMask S) b x))) :
    S=potential (decode (formMask S)) ∧ parity (seedSide false) (formMask S)=b := by
  let q := formMask S
  have one (t : Bool) (x : Nat) (single : only x (rowKey (omitted t)) (rowKey (omitted t))=true) :
      parity x q = (b ^^ t) := by
    have ep : M.owner (rowKey (omitted t))=3 ∨ M.owner (rowKey (omitted t))=4 := by
      rw [M.row]; cases t <;> decide
    have eq := chosenPrivate M q b split single ep
    rw [M.row] at eq
    cases t <;> cases b <;> cases hx : parity x q <;> simp_all [chooseChild,omitted,hx]
  have mem := shrink samples initial q (allForms S) (by
    intro z hz
    rw [d,parity_left,one _ _ (sampleRaw z hz),one _ _ (seedRaw z.1)]
    cases b <;> cases z.1 <;> rfl)
  have ok := List.all_eq_true.mp exhaustive q mem
  have ne : parity (seedSide false) q ≠ parity (seedSide true) q := by
    rw [one _ _ (seedRaw false),one _ _ (seedRaw true)]
    cases b <;> decide
  have masks : q = formMask (potential (decode q)) := by simpa [accepts,ne] using ok
  refine ⟨?_,?_⟩
  · ext v
    have h := congrArg (fun n : Nat => n.testBit (idx v)) masks
    change (formMask S).testBit (idx v) = (formMask (potential (decode q))).testBit (idx v) at h
    simpa only [bit_mask,decide_eq_decide] using h
  · simpa [q] using one false _ (seedRaw false)

def pairBoard (h : Hole) : Nat := (#[71746,141377,280609,558113] : Array Nat)[h.val]!
theorem pairPrivate : ∀ h, only (pairBoard h) (edgeKey 3 4 h) (edgeKey 3 4 h)=true := by decide +kernel
def selected (t : Code) := chooseChild (formMask (potential t)) (parity (seedSide false) (formMask (potential t)))
def expected (t : Code) (k : Key) : Row :=
  if k.val<5 then ⟨k.val%5,Nat.mod_lt _ (by decide)⟩
  else let a := ij[(k.val-5)%10]!
       if a.1.val<3 then a.1 else selected t (pairBoard ⟨((k.val-5)/10)%4,Nat.mod_lt _ (by decide)⟩)
theorem decodeKey : ∀ k : Key, (∃ p, k=rowKey p) ∨ ∃ i j : Row, ∃ h : Hole, i.val<j.val ∧ k=edgeKey i j h := by decide +kernel
theorem expectedRow (t : Code) : ∀ i, expected t (rowKey i)=i := by
  intro i; fin_cases i <;> rfl
theorem expectedEdge (t : Code) (i j : Row) (h : Hole) (lt : i.val < j.val) :
   expected t (edgeKey i j h) = (if i.val<3 then i else selected t (pairBoard h)) := by
  fin_cases i <;> fin_cases j <;> first | (exfalso; revert lt; decide +kernel) | (fin_cases h <;> rfl)

theorem orderedOwner (M : Model) (t : Code)
    (split : ∀ x, ¬LinClauseSat (assignment x) (M.K (selected t x))) :
    ∀ k, M.owner k=expected t k := by
  let owner := fun (i j : Row) (h : Hole) => M.owner (edgeKey i j h)
  have pe : ∀ (i j : Row) (h : Hole), i.val<3 → i.val<j.val → owner i j h=i :=
    (PEqualNP.Outside.L_pcx_178.StarOrder.peeling owner
      (fun i j h => congrArg M.owner (edgeSymm i j h))
      (endpoint M) (fun i j h ne act => activeBefore M i j h ne act)).1
  intro k
  rcases decodeKey k with ⟨i,rfl⟩|⟨i,j,h,lt,rfl⟩
  · exact (M.row i).trans (expectedRow t i).symm
  · rw [expectedEdge _ _ _ _ lt]
    split
    next small => exact pe i j h small lt
    next large =>
      have ei : i=3 := Fin.ext (by omega)
      have ej : j=4 := Fin.ext (by omega)
      subst i; subst j
      exact chosenPrivate M _ _ split (pairPrivate h) (endpoint M _ _ h (by decide))

def forcedAt (t : Code) (x : Nat) := (List.finRange 45).all fun k =>
  !(bad x k) || !(decide (before (expected t k) (selected t x))) || expected t k == 2
def safeAt (t : Code) (x : Nat) := (List.finRange 45).all fun k =>
  !(bad x k) || !(decide (before (expected t k) 2))
def checkpoint (t : Code) :=
  let a := aa[t.val]!
  let b := bb[t.val]!
  let c := cc[t.val]!
  forcedAt t a && forcedAt t b && forcedAt t c && safeAt t (a ^^^ b ^^^ c)
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem checkpoints : ∀ t, checkpoint t = true := by decide +kernel

theorem noOrderedModel (M : Model) (S : Finset V) (b : Bool)
    (split : ∀ x, ¬LinClauseSat (assignment x) (M.K (chooseChild (formMask S) b x))) : False := by
  let t := decode (formMask S)
  obtain ⟨eq,cert⟩ := modelPotential M S b split
  have sp (x : Nat) : ¬LinClauseSat (assignment x) (M.K (selected t x)) := by
    change ¬LinClauseSat (assignment x) (M.K (chooseChild (formMask (potential t)) (parity (seedSide false) (formMask (potential t))) x))
    have h : S=potential t := eq
    rw [←h,cert]
    exact split x
  have names := orderedOwner M t sp
  have force (x : Nat) (ok : forcedAt t x=true) : ¬LinClauseSat (assignment x) (M.K 2) := by
    obtain ⟨k,hit,ord,badK⟩ := M.trace _ _ (sp x)
    have cond := List.all_eq_true.mp ok k (List.mem_finRange k)
    rw [names] at ord badK
    have eq : expected t k=2 := by simpa [hit,ord] using cond
    exact eq ▸ badK
  have saf (x : Nat) (ok : safeAt t x=true) : LinClauseSat (assignment x) (M.K 2) := by
    by_contra ff
    obtain ⟨k,hit,ord,_⟩ := M.trace _ _ ff
    have cond := List.all_eq_true.mp ok k (List.mem_finRange k)
    rw [names] at ord
    simp [hit,ord] at cond
  have w := checkpoints t
  simp only [checkpoint,Bool.and_eq_true] at w
  exact (flat_closed _ _ _ _ (force _ w.1.1.1) (force _ w.1.1.2) (force _ w.1.2)) (saf _ w.2)
end PEqualNP.Outside.L_pcx_178_affine
