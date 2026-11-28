import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The truth table, restrictions and search certificates below are instance-specific.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_43236
open PEqualNP.CircuitLowerBounds
def natLimbs (xs : List Nat) : Nat := xs.foldl (fun a n => (a <<< 80) + n) 0
def bitLimbs {n : Nat} (xs : List Nat) : BitVec n := BitVec.ofNat n (natLimbs xs)
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [(bitLimbs [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa]),(bitLimbs [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc]),(bitLimbs [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0]),(bitLimbs [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00]),(bitLimbs [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000]),(bitLimbs [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000]),(bitLimbs [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,65535,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000]),(bitLimbs [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,65535,0xffffffffffffffffffff,0xffffffff000000000000,0]),(bitLimbs [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0])]
def graph : Sig := (bitLimbs [0xfeeaeac8,0xeea0ea80feeaeac8eea0,0xea80feeaeac8eea0ea80,0xfeeaeac8eea0ea80feea,0xeac8eea0ea80feeaeac8,0xeea0ea80feeaeac8eea0,0xea80feeaeac8eea0ea80])
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 ∨ 2048≤m then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  if m=6159 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=4141 then (x 0 &&& x 2) ||| (x 3) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=4139 then (x 0) ||| (x 1 &&& x 3) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) else
  if m=4123 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=4111 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  if m=2109 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=2107 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=2105 then (x 0 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) else
  if m=2103 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4 &&& x 5) else
  if m=2095 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=2093 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=2091 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 1 &&& x 5) else
  if m=2087 then (x 0 &&& x 2) ||| (x 0 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) else
  if m=2079 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2077 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) else
  if m=2071 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=2063 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) else
  if m=60 then (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) else
  if m=58 then (x 1 &&& x 3) ||| (x 1 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=57 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4 &&& x 5) else
  if m=54 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 5) else
  if m=46 then (x 1 &&& x 3) ||| (x 1 &&& x 2 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=45 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=43 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 5) else
  if m=42 then (x 1 &&& x 3) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) else
  if m=37 then (x 0 &&& x 2) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=30 then (x 1 &&& x 2) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=29 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=27 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) else
  if m=25 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=23 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) else
  if m=22 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=13 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=11 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  (x 0 &&& x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2 &&& x 3) ||| (x 0 &&& x 2 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 0 &&& x 1 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) ||| (x 0 &&& x 4 &&& x 5) ||| (x 2 &&& x 3 &&& x 4 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => (natLimbs [0x1000000000000,0x10000000000000001,65536,4294967296,0x1000000000000,0x10000000000000001])
  | 1 => (natLimbs [0x10000000000000000,65536,0,0x1000000000000,1])
  | 2 => (natLimbs [1,65536,0,0,0x10000000000000001])
  | 3 => (natLimbs [65536,0,0,1])
  | 4 => (natLimbs [4294967296,0x1000000000000,0x10000000000000001])
  | 5 => (natLimbs [0x1000000000000,1])
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (_ : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := (mask >>> (9+9*i)) &&& 511
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := (hints >>> (9*i)) &&& 511
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  if m=6159 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=4141 then (x 0 &&& x 2) ||| (x 3) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=4139 then (x 0) ||| (x 1 &&& x 3) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) else
  if m=4123 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=4111 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  if m=2109 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=2107 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=2105 then (x 0 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) else
  if m=2103 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4 &&& x 5) else
  if m=2095 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=2093 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=2091 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 1 &&& x 5) else
  if m=2087 then (x 0 &&& x 2) ||| (x 0 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) else
  if m=2079 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2077 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) else
  if m=2071 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=2063 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) else
  if m=60 then (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) else
  if m=58 then (x 1 &&& x 3) ||| (x 1 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=57 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4 &&& x 5) else
  if m=54 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 5) else
  if m=46 then (x 1 &&& x 3) ||| (x 1 &&& x 2 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=45 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=43 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 5) else
  if m=42 then (x 1 &&& x 3) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) else
  if m=37 then (x 0 &&& x 2) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=30 then (x 1 &&& x 2) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=29 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=27 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) else
  if m=25 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=23 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) else
  if m=22 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=13 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=11 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  (x 0 &&& x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2 &&& x 3) ||| (x 0 &&& x 2 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 0 &&& x 1 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) ||| (x 0 &&& x 4 &&& x 5) ||| (x 2 &&& x 3 &&& x 4 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases h0 : m=6159
  · simp only [graphGoal,liftGoal,if_pos h0,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h1 : m=4141
  · simp only [graphGoal,liftGoal,if_neg h0,if_pos h1,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h2 : m=4139
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_pos h2,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h3 : m=4123
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_pos h3,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h4 : m=4111
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h5 : m=2109
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h6 : m=2107
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_pos h6,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h7 : m=2105
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_pos h7,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h8 : m=2103
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_pos h8,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h9 : m=2095
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_pos h9,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h10 : m=2093
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_pos h10,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h11 : m=2091
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_pos h11,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h12 : m=2087
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_pos h12,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h13 : m=2079
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_pos h13,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h14 : m=2077
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_pos h14,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h15 : m=2075
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_pos h15,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h16 : m=2071
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_pos h16,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h17 : m=2063
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_pos h17,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h18 : m=60
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_pos h18,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h19 : m=58
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_pos h19,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h20 : m=57
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_pos h20,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h21 : m=54
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_pos h21,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h22 : m=51
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_pos h22,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h23 : m=46
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_pos h23,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h24 : m=45
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_pos h24,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h25 : m=43
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_pos h25,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h26 : m=42
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_pos h26,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h27 : m=37
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_pos h27,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h28 : m=30
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_pos h28,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h29 : m=29
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_pos h29,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h30 : m=27
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_pos h30,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h31 : m=25
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_pos h31,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h32 : m=23
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_pos h32,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h33 : m=22
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_pos h33,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h34 : m=14
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_pos h34,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h35 : m=13
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_pos h35,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h36 : m=11
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_pos h36,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide)]
  simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
private def limbs80 (pages : Array (Array Nat)) (i : Nat) : Nat :=
  ((pages[i/32]?).getD #[])[i%32]?.getD 0

private def groupedPages (a : Array (Nat → Nat)) (i : Nat) : Nat :=
  ((a[i/512]?).getD (fun _ => 0)) (i%512)

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/80
  let shift := pos % 80
  let lo := word i >>> shift
  if shift+len ≤ 80 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (80-shift))) &&& ((1 <<< len)-1)


private def countLow32 (x : Nat) : Nat :=
  let a := x - ((x >>> 1) &&& 0x55555555)
  let b := (a &&& 0x33333333) + ((a >>> 2) &&& 0x33333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f
  ((c*0x01010101) >>> 24) &&& 255

private def groupLookup (nb slots sw gw bw groups : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let pos := (h/nb + packedAt data (h%nb*sw) sw) % slots
  let start := nb*sw
  let stride := 32*gw+groups*bw
  let tag := start+((slots+31)/32)*stride+3*pos
  if packedAt data tag 3 != h/(nb*slots)%8 then none else
    let here := start+pos/32*stride
    let atBit := pos % 32
    let rec classify : Nat → Nat → Nat → Nat × Nat
      | 0, _, live => (0,live)
      | k+1, j, live =>
        let plane := packedAt data (here+32*j) 32
        let on := plane.testBit atBit
        let next := if on then live &&& plane else live &&& (0xffffffff ^^^ plane)
        let pair := classify k (j+1) next
        (pair.1*2+on.toNat,pair.2)
    let c := classify gw 0 0xffffffff
    if c.1=0 then none else
      let base := packedAt data (here+32*gw+(c.1-1)*bw) bw
      some (base+countLow32 (c.2 &&& ((1 <<< atBit)-1)),0)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))


def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if 8192 ≤ marker then
    let reg := ow/4096
    if reg ≤ i then [] else
      let head := ow % 64
      let rel := ow/64%64
      let off := denseRowStart d raw dict + num*denseRowWidth d flags
      let span := off+((reg+15)/16)*head
      let pairs := span+reg*rel
      let pos := pairs+(marker-8192)*(cw+d)+packedAt data (off+(i/16)*head) head+packedAt data (span+i*rel) rel
      let n := packedAt data pos 5
      let gap := packedAt data (pos+5) 3
      readSortedHints data pairs cw d gap n (pos+8) 0
  else if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4003523200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[⟨.and,[0,5]⟩,⟨.and,[2,5]⟩,⟨.or,[0,7]⟩,⟨.and,[0,4]⟩,⟨.or,[0,4]⟩,⟨.or,[2,6]⟩,⟨.or,[1,9]⟩,⟨.and,[3,10]⟩,⟨.and,[11,12]⟩,⟨.or,[13,14]⟩,⟨.and,[3,12]⟩,⟨.or,[16,8]⟩,⟨.and,[17,15]⟩], 18⟩
theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def instanceInputs : List Sig := vars 63
def sampleInstance (r : Row) (i : Fin 6) : Bool := bit r (instanceInputs.getD i.val zero)
theorem instanceList : List.ofFn (fun i : Fin 6 => instanceInputs.getD i.val zero) = instanceInputs := rfl
theorem instanceSampled (r : Row) : List.ofFn (sampleInstance r) = instanceInputs.map (bit r) := by
  rw [←instanceList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem instanceTable : ∀ r : Row, bit r graph = target (sampleInstance r) := by decide +kernel

theorem instanceEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates instanceInputs).getD i zero) =
      (C.wires (List.ofFn (sampleInstance r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),instanceSampled]
  rfl

def lowRow (i : Fin 6) : Row := Fin.ofNat 512 (([6, 5, 3, 1, 5, 3] : List Nat).getD i.val 0)
def highRow (i : Fin 6) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (([6, 5, 3, 1, 5, 3] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allInstanceRequired :
    (∀ i : Fin 6, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 6, i ≠ j →
      bit (lowRow i) (instanceInputs.getD j.val zero) =
      bit (highRow i) (instanceInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k instanceInputs.toFinset := by
  have goalEq : (execute C.gates instanceInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (instanceEval C legal C.output r).trans ((computes (sampleInstance r)).trans (instanceTable r).symm)
  have out := get_rep (u:=true) (execute C.gates instanceInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates instanceInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : instanceInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ instanceInputs) : ∃ i : Fin 6, instanceInputs.getD i.val zero = a := by
    rw [←instanceList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = instanceInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run instanceInputs (instanceInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allInstanceRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allInstanceRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩
theorem replaceShort 
    (lower : Impossible true graph 11 instanceInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 6 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 6 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,witnessSize.symm ▸ big,witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim

namespace Nat92GE
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 92

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 46 := ((x >>> 46) ^^^ x).setWidth 46
def cuts (ws : List W) : BitVec 46 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 46) ++ (0 : BitVec 46)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 46) (w : W) : Prop :=
  w.getLsbD (46+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 46) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 46+i.val < 92 := by omega
  have hi' : i.val < 92 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 46) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 46)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

noncomputable section Fast

def M120 : ℕ := (0xfffffff * 2^64 + 0xffffffffffffffff)
def M60 : ℕ := 0x3fffffffffff
def P60 : ℕ := 0x400000000000
def gN : ℕ := (0xfffffff * 2^64 + 0xffffc00000000000)

def nsep (x : ℕ) : ℕ := Nat.mod (Nat.xor (Nat.shiftRight x 46) x) P60

def ncuts (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.lor (nsep w) ih) ws

def len (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) ws

def nisGoal (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w t _ => List.rec (motive := fun _ => Bool)
      (Bool.rec (Nat.beq w M60) true (Nat.beq w gN)) (fun _ _ _ => false) t) ws

def frc (w : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k Nat.zero) (fun m _ => k (Nat.succ m)) w

def revK (xs : List ℕ) (acc : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun acc => k acc) (fun x _ ih acc => ih (x :: acc))
    xs acc

def insK (w : ℕ) (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [w])
    (fun x xs ih k => Bool.rec (ih (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x)) l k

def call (next : List ℕ → Bool) (c : List ℕ) : Bool := Bool.rec false true (next c)

def orB (x y : Bool) : Bool := Bool.rec y true x

def one0 (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) : Bool :=
  Bool.rec false
    (frc w (fun w2 => revK mid post (fun m => revK pre m (fun r =>
      insK w2 r (fun c => call next c)))))
    (Nat.beq (Nat.lor (nsep w) base) M60)

def pair0 (next : List ℕ → Bool) (a b _sa _sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orB (one0 next base pre mid post (Nat.land a b))
  (orB (one0 next base pre mid post (Nat.lor a b))
  (orB (one0 next base pre mid post (Nat.land a (Nat.sub M120 b)))
    (one0 next base pre mid post (Nat.land b (Nat.sub M120 a)))))

def reb (pre mid post : List ℕ) (k : List ℕ → Bool) : Bool :=
  revK mid post (fun m => revK pre m k)

def oneG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    Bool :=
  frc w (fun w2 =>
    orB (Bool.rec false (reb pre mid post (fun r => insK w2 r (fun c => call next c)))
      (Nat.beq (Nat.lor (nsep w2) base) M60))
    (orB (Bool.rec false
        (reb pre mid post (fun r => insK a r (fun r1 => insK w2 r1 (fun c => call next c))))
      (Nat.beq (Nat.lor (Nat.lor (nsep w2) base) sa) M60))
    (orB (Bool.rec false
        (reb pre mid post (fun r => insK b r (fun r1 => insK w2 r1 (fun c => call next c))))
      (Nat.beq (Nat.lor (Nat.lor (nsep w2) base) sb) M60))
      (Bool.rec false
        (reb pre mid post (fun r =>
          insK b r (fun r1 => insK a r1 (fun r2 => insK w2 r2 (fun c => call next c)))))
        (Nat.ble 2 extra)))))

def pairG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orB (oneG next extra a b sa sb base pre mid post (Nat.land a b))
  (orB (oneG next extra a b sa sb base pre mid post (Nat.lor a b))
  (orB (oneG next extra a b sa sb base pre mid post (Nat.land a (Nat.sub M120 b)))
    (oneG next extra a b sa sb base pre mid post (Nat.land b (Nat.sub M120 a)))))

def innerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a sa : ℕ)
    (pre : List ℕ) (preCut : ℕ) (rest mid : List ℕ) (midCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun b post ih mid midCut =>
      Bool.rec (ih (b :: mid) (Nat.lor midCut (nsep b))) true
        (P a b sa (nsep b) (Nat.lor (Nat.lor preCut midCut) (ncuts post)) pre mid post))
    rest mid midCut

def outerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (ws pre : List ℕ)
    (preCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun a rest ih pre preCut =>
      Bool.rec (ih (a :: pre) (Nat.lor preCut (nsep a))) true
        (innerAux P a (nsep a) pre preCut rest [] 0))
    ws pre preCut

def stepF (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) : Bool :=
  Bool.rec
    (Bool.rec (outerAux (pairG next (Nat.sub (Nat.succ (Nat.succ k1)) (len ws))) ws [] 0)
      (outerAux (pair0 next) ws [] 0) (Nat.beq (len ws) (Nat.succ (Nat.succ k1))))
    true (nisGoal ws)

def nopt (k : ℕ) (ws : List ℕ) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → Bool) (fun ws => nisGoal ws)
    (fun k1 ih ws => stepF k1 ih ws) k ws

def ins (w : ℕ) : List ℕ → List ℕ
  | [] => [w]
  | x :: xs => if Nat.ble w x = true then w :: x :: xs else x :: ins w xs

def cutR (l : List ℕ) : ℕ := l.foldr (fun x c => Nat.lor c (nsep x)) 0

def baseOf (pre mid post : List ℕ) : ℕ := Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post)

def rOf (pre mid post : List ℕ) : List ℕ := pre.reverse ++ (mid.reverse ++ post)

def opsN (a b : ℕ) : List ℕ :=
  [Nat.land a b, Nat.lor a b, Nat.land a (Nat.sub M120 b), Nat.land b (Nat.sub M120 a)]

abbrev Split := List ℕ × ℕ × List ℕ × ℕ × List ℕ

def innerS (pre : List ℕ) (a : ℕ) : List ℕ → List ℕ → List Split
  | [], _ => []
  | b :: post, mid => (pre, a, mid, b, post) :: innerS pre a post (b :: mid)

def outerS : List ℕ → List ℕ → List Split
  | [], _ => []
  | a :: rest, pre => innerS pre a rest [] ++ outerS rest (a :: pre)

def kids0 (base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  if Nat.beq (Nat.lor (nsep w) base) M60 = true then [ins w r] else []

def kidsG (extra a b sa sb base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  (if Nat.beq (Nat.lor (nsep w) base) M60 = true then [ins w r] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = true then [ins w (ins a r)] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = true then [ins w (ins b r)] else []) ++
   (if Nat.ble 2 extra = true then [ins w (ins a (ins b r))] else [])))

def kidsPair0 (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap (kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsPairG (extra : ℕ) (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap
    (kidsG extra t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
      (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsL (k1 : ℕ) (ws : List ℕ) : List (List ℕ) :=
  if Nat.beq (len ws) (Nat.succ (Nat.succ k1)) = true then (outerS ws []).flatMap kidsPair0
  else (outerS ws []).flatMap (kidsPairG (Nat.sub (Nat.succ (Nat.succ k1)) (len ws)))

theorem brec {α : Type} (f t : α) (c : Bool) :
    (Bool.rec (motive := fun _ => α) f t c) = if c = true then t else f := by
  cases c <;> rfl

theorem frc_eq (w : ℕ) (k : ℕ → Bool) : frc w k = k w := by
  cases w <;> rfl

theorem revK_eq (xs : List ℕ) : ∀ (acc : List ℕ) (k : List ℕ → Bool),
    revK xs acc k = k (xs.reverse ++ acc) := by
  induction xs with
  | nil => intro acc k; rfl
  | cons x xs ih =>
    intro acc k
    have e : revK (x :: xs) acc k = revK xs (x :: acc) k := rfl
    rw [e, ih]
    simp

theorem insK_eq (w : ℕ) (l : List ℕ) : ∀ k : List ℕ → Bool, insK w l k = k (ins w l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : insK w (x :: xs) k =
        Bool.rec (insK w xs (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x) := rfl
    rw [e, brec, ih]
    by_cases h : Nat.ble w x = true <;> simp [ins, h]

theorem call_eq (next : List ℕ → Bool) (c : List ℕ) : call next c = next c := by
  unfold call
  cases next c <;> rfl

theorem orB_eq (x y : Bool) : orB x y = (x || y) := by
  cases x <;> rfl

theorem one0_eq (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    one0 next base pre mid post w = (kids0 base (rOf pre mid post) w).any next := by
  unfold one0 kids0 rOf
  rw [brec]
  generalize Nat.beq (Nat.lor (nsep w) base) M60 = c
  cases c <;> simp [frc_eq, revK_eq, insK_eq, call_eq]

theorem oneG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ)
    (w : ℕ) :
    oneG next extra a b sa sb base pre mid post w =
      (kidsG extra a b sa sb base (rOf pre mid post) w).any next := by
  unfold oneG kidsG rOf reb
  simp only [frc_eq, revK_eq, insK_eq, call_eq, orB_eq, brec, List.any_append]
  generalize Nat.beq (Nat.lor (nsep w) base) M60 = c1
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = c2
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = c3
  generalize Nat.ble 2 extra = c4
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp

theorem pair0_eq (next : List ℕ → Bool) (a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pair0 next a b sa sb base pre mid post =
      ((opsN a b).flatMap (kids0 base (rOf pre mid post))).any next := by
  unfold pair0 opsN
  simp only [orB_eq, one0_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

theorem pairG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pairG next extra a b sa sb base pre mid post =
      ((opsN a b).flatMap (kidsG extra a b sa sb base (rOf pre mid post))).any next := by
  unfold pairG opsN
  simp only [orB_eq, oneG_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

def HP (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (t : Split) : Bool :=
  P t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
    t.1 t.2.2.1 t.2.2.2.2

theorem innerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a : ℕ)
    (pre : List ℕ) : ∀ rest mid : List ℕ,
    innerAux P a (nsep a) pre (cutR pre) rest mid (cutR mid) =
      (innerS pre a rest mid).any (HP P) := by
  intro rest
  induction rest with
  | nil => intro mid; rfl
  | cons b post ih =>
    intro mid
    have e : innerAux P a (nsep a) pre (cutR pre) (b :: post) mid (cutR mid) =
        Bool.rec (innerAux P a (nsep a) pre (cutR pre) post (b :: mid)
            (Nat.lor (cutR mid) (nsep b)))
          true (P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
            pre mid post) := rfl
    have c : Nat.lor (cutR mid) (nsep b) = cutR (b :: mid) := rfl
    rw [e, brec, c, ih]
    simp only [innerS, List.any_cons, HP, baseOf]
    cases P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
      pre mid post <;> simp

theorem outerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) :
    ∀ ws pre : List ℕ, outerAux P ws pre (cutR pre) = (outerS ws pre).any (HP P) := by
  intro ws
  induction ws with
  | nil => intro pre; rfl
  | cons a rest ih =>
    intro pre
    have e : outerAux P (a :: rest) pre (cutR pre) =
        Bool.rec (outerAux P rest (a :: pre) (Nat.lor (cutR pre) (nsep a))) true
          (innerAux P a (nsep a) pre (cutR pre) rest [] 0) := rfl
    have c : Nat.lor (cutR pre) (nsep a) = cutR (a :: pre) := rfl
    have z : (0 : ℕ) = cutR [] := rfl
    rw [e, brec, c, ih, z, innerAux_eq]
    simp only [outerS, List.any_append]
    cases (innerS pre a rest []).any (HP P) <;> simp

theorem HP_pair0 (next : List ℕ → Bool) :
    HP (pair0 next) = fun t => (kidsPair0 t).any next := by
  funext t
  simp only [HP, pair0_eq, kidsPair0]

theorem HP_pairG (next : List ℕ → Bool) (extra : ℕ) :
    HP (pairG next extra) = fun t => (kidsPairG extra t).any next := by
  funext t
  simp only [HP, pairG_eq, kidsPairG]

theorem stepF_eq (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) :
    stepF k1 next ws = (nisGoal ws || (kidsL k1 ws).any next) := by
  have z : (0 : ℕ) = cutR [] := rfl
  unfold stepF kidsL
  rw [brec, brec, z, outerAux_eq, outerAux_eq, HP_pair0, HP_pairG]
  cases nisGoal ws
  · cases Nat.beq (len ws) (Nat.succ (Nat.succ k1)) <;> simp [List.any_flatMap]
  · simp

theorem nopt_succ (k : ℕ) (ws : List ℕ) :
    nopt (k + 1) ws = (nisGoal ws || (kidsL k ws).any (nopt k)) := by
  rw [← stepF_eq]
  rfl

end Fast

noncomputable section Bridge

theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

theorem negOne60 : (-1 : BitVec 46).toNat = M60 := by decide

theorem nsep_toNat (w : W) : nsep w.toNat = (sep w).toNat := by
  simp only [nsep, sep, BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]
  rfl

theorem ncuts_cons (w : ℕ) (ws : List ℕ) : ncuts (w :: ws) = Nat.lor (nsep w) (ncuts ws) := rfl

theorem cuts_cons (a : W) (l : List W) : cuts (a :: l) = sep a ||| cuts l := rfl

theorem ncuts_map (l : List W) : ncuts (l.map BitVec.toNat) = (cuts l).toNat := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, ncuts_cons, cuts_cons, BitVec.toNat_or, ih, nsep_toNat]
    rfl

theorem ncuts_append (l1 l2 : List ℕ) : ncuts (l1 ++ l2) = Nat.lor (ncuts l1) (ncuts l2) := by
  induction l1 with
  | nil =>
    have e : ncuts ([] : List ℕ) = 0 := rfl
    rw [List.nil_append, e]
    exact (Nat.zero_or _).symm
  | cons a l ih =>
    rw [List.cons_append, ncuts_cons, ih, ncuts_cons]
    exact (Nat.or_assoc _ _ _).symm

theorem cutR_eq (l : List ℕ) : cutR l = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : cutR (a :: l) = Nat.lor (cutR l) (nsep a) := rfl
    rw [e, ih, ncuts_cons]
    exact Nat.or_comm _ _

theorem ncuts_reverse (l : List ℕ) : ncuts l.reverse = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e1 : ncuts [a] = nsep a ||| 0 := rfl
    have e2 : ncuts (a :: l) = nsep a ||| ncuts l := rfl
    rw [List.reverse_cons, ncuts_append, ih, e1, e2]
    change (ncuts l ||| (nsep a ||| 0)) = (nsep a ||| ncuts l)
    rw [Nat.or_zero, Nat.or_comm]

theorem baseOf_map (xs ys zs : List W) :
    baseOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat) =
      (cuts (xs ++ (ys ++ zs))).toNat := by
  rw [← ncuts_map, List.map_append, List.map_append, ncuts_append, ncuts_append]
  unfold baseOf
  rw [cutR_eq, cutR_eq, ncuts_reverse, ncuts_reverse]
  exact Nat.or_assoc _ _ _

theorem opsN_map (a b : W) : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp only [opsN, ops, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_not]
  rfl

theorem len_eq (l : List ℕ) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : len (a :: l) = Nat.succ (len l) := rfl
    rw [e, ih]
    rfl

def insW (w : W) : List W → List W
  | [] => [w]
  | x :: xs => if Nat.ble w.toNat x.toNat = true then w :: x :: xs else x :: insW w xs

theorem insW_map (w : W) (l : List W) :
    (insW w l).map BitVec.toNat = ins w.toNat (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [insW, ins, List.map_cons]
    split_ifs
    · rfl
    · rw [List.map_cons, ih]

theorem insW_perm (w : W) (l : List W) : (insW w l).Perm (w :: l) := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insW]
    split_ifs
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem mem_innerS (pre : List ℕ) (a b : ℕ) (zs : List ℕ) : ∀ ys mid : List ℕ,
    (pre, a, ys.reverse ++ mid, b, zs) ∈ innerS pre a (ys ++ b :: zs) mid := by
  intro ys
  induction ys with
  | nil => intro mid; simp [innerS]
  | cons y ys ih =>
    intro mid
    simp only [List.cons_append, innerS, List.reverse_cons, List.append_assoc]
    exact List.mem_cons_of_mem _ (ih (y :: mid))

theorem mem_outerS (a b : ℕ) (ys zs : List ℕ) : ∀ xs pre : List ℕ,
    (xs.reverse ++ pre, a, ys.reverse, b, zs) ∈ outerS (xs ++ a :: (ys ++ b :: zs)) pre := by
  intro xs
  induction xs with
  | nil =>
    intro pre
    simp only [List.nil_append, List.reverse_nil, outerS]
    exact List.mem_append_left _ (by simpa using mem_innerS pre a b zs ys [])
  | cons x xs ih =>
    intro pre
    simp only [List.cons_append, outerS, List.reverse_cons, List.append_assoc]
    exact List.mem_append_right _ (ih (x :: pre))

theorem split_two {α : Type} {a b : α} {l : List α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    (∃ xs ys zs, l = xs ++ a :: (ys ++ b :: zs)) ∨ (∃ xs ys zs, l = xs ++ b :: (ys ++ a :: zs)) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  rcases List.mem_append.mp hb with h | h
  · obtain ⟨s1, s2, rfl⟩ := List.append_of_mem h
    exact .inr ⟨s1, s2, t, by simp⟩
  · rcases List.mem_cons.mp h with h | h
    · exact absurd h.symm hne
    · obtain ⟨t1, t2, rfl⟩ := List.append_of_mem h
      exact .inl ⟨s, t1, t2, rfl⟩

theorem nisGoal_goal {g : W} (hg : g = goal ∨ g = ~~~goal) : nisGoal [g.toNat] = true := by
  rcases hg with rfl | rfl <;> decide +kernel

theorem mem_kids0 {base w : ℕ} {r : List ℕ} (h : Nat.beq (Nat.lor (nsep w) base) M60 = true) :
    ins w r ∈ kids0 base r w := by
  unfold kids0
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG1 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (nsep w) base) M60 = true) :
    ins w r ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_left _ ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG2 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = true) :
    ins w (ins a r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG3 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = true) :
    ins w (ins b r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG4 {extra a b sa sb base w : ℕ} {r : List ℕ} (h : Nat.ble 2 extra = true) :
    ins w (ins a (ins b r)) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsL {k : ℕ} {wsN : List ℕ} {t : Split} {w : ℕ} {c : List ℕ}
    (ht : t ∈ outerS wsN []) (hw : w ∈ opsN t.2.1 t.2.2.2.1)
    (h0 : Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w)
    (hG : ¬ Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kidsG (Nat.sub (Nat.succ (Nat.succ k)) (len wsN)) t.2.1 t.2.2.2.1 (nsep t.2.1)
        (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w) :
    c ∈ kidsL k wsN := by
  unfold kidsL
  split_ifs with hd
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, h0 hd⟩⟩
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, hG hd⟩⟩

theorem guard1 {z : W} {r : List W} (h : cuts (z :: r) = -1) :
    Nat.beq (Nat.lor (nsep z.toNat) (cuts r).toNat) M60 = true := by
  rw [cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, ← nsep_toNat, negOne60] at e
  exact beq_of_eq e

theorem guard2 {z a : W} {r : List W} (h : cuts (z :: a :: r) = -1) :
    Nat.beq (Nat.lor (Nat.lor (nsep z.toNat) (cuts r).toNat) (nsep a.toNat)) M60 = true := by
  rw [cuts_cons, cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, BitVec.toNat_or, ← nsep_toNat, ← nsep_toNat, negOne60] at e
  refine beq_of_eq (Eq.trans ?_ e)
  change (nsep z.toNat ||| (cuts r).toNat ||| nsep a.toNat) =
    (nsep z.toNat ||| (nsep a.toNat ||| (cuts r).toNat))
  rw [Nat.or_assoc, Nat.or_comm (cuts r).toNat]

theorem child_of_split {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws xs ys zs : List W}
    {a b z : W} {needed : Finset W} (hn : ws.Nodup)
    (hsplit : ws = xs ++ a :: (ys ++ b :: zs)) (hz : z ∈ basicOps a b) (hout : z ∉ ws.toFinset)
    (hs : ws.toFinset = insert a (insert b needed))
    (tail : live basicOps g k (insert z needed)) :
    ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  have p1 : (xs ++ a :: (ys ++ b :: zs)).Perm (a :: (xs ++ (ys ++ b :: zs))) := List.perm_middle
  have p2 : (xs ++ (ys ++ b :: zs)).Perm (b :: (xs ++ (ys ++ zs))) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_middle
  have perm : ws.Perm (a :: b :: (xs ++ (ys ++ zs))) := hsplit ▸ p1.trans (p2.cons a)
  obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hs
  have hznew : z ∉ kept := by
    intro hu
    apply hout
    rw [hs]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
  have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
  have hl2 : live basicOps g k (z :: kept).toFinset := by
    simpa [hfin] using tail
  have hc := live_card hl2
  rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
  have hcut := cuts_full hg hl2
  have hlen2 := perm.length_eq
  simp only [List.length_cons] at hlen2
  have hmap : ws.map BitVec.toNat = xs.map BitVec.toNat ++
      a.toNat :: (ys.map BitVec.toNat ++ b.toNat :: zs.map BitVec.toNat) := by
    rw [hsplit]
    simp
  have ht := mem_outerS a.toNat b.toNat (ys.map BitVec.toNat) (zs.map BitVec.toNat)
    (xs.map BitVec.toNat) []
  rw [List.append_nil, ← hmap] at ht
  have hzN : z.toNat ∈ opsN a.toNat b.toNat := by
    rw [opsN_map]
    exact List.mem_map_of_mem (List.mem_toFinset.mp hz)
  have hr : rOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse
      (zs.map BitVec.toNat) = (xs ++ (ys ++ zs)).map BitVec.toNat := by
    simp [rOf]
  have hbase := baseOf_map xs ys zs
  have hlenN : len (ws.map BitVec.toNat) = ws.length := by
    rw [len_eq, List.length_map]
  have live_of (cW : List W) (hp : cW.Perm (z :: kept)) :
      cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset := by
    refine ⟨hp.nodup_iff.mpr hnd, ?_, ?_⟩
    · rw [hp.length_eq, List.length_cons]
      exact hc
    · have e : cW.toFinset = (z :: kept).toFinset := List.toFinset_eq_of_perm _ _ hp
      rw [e]
      exact hl2
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · refine ⟨insW z (xs ++ (ys ++ zs)), (live_of _ (insW_perm _ _)).1, (live_of _ (insW_perm _ _)).2.1,
      (live_of _ (insW_perm _ _)).2.2, ?_⟩
    rw [insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro _
      simp only [hr, hbase]
      exact mem_kids0 (guard1 hcut)
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG1 (guard1 hcut)
  · have hp : (insW z (insW a (xs ++ (ys ++ zs)))).Perm (z :: a :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG2 (guard2 hcut)
  · have hp : (insW z (insW b (xs ++ (ys ++ zs)))).Perm (z :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG3 (guard2 hcut)
  · have hp : (insW z (insW a (insW b (xs ++ (ys ++ zs))))).Perm
        (z :: a :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans (((insW_perm _ _).trans ((insW_perm _ _).cons a)).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map, insW_map]
    simp only [List.length_cons] at hc
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      omega
    · intro _
      simp only [hr]
      refine mem_kidsG4 ?_
      rw [hlenN]
      apply Nat.ble_eq_true_of_le
      change 2 ≤ k + 2 - ws.length
      omega

theorem child_exists {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (hl : live basicOps g (k + 1) ws.toFinset) :
    ws = [g] ∨ ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  rcases first_live hl with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact .inl (singleton_list hn done)
  · right
    rcases split_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab with
      ⟨xs, ys, zs, e⟩ | ⟨xs, ys, zs, e⟩
    · exact child_of_split hg hn e hz hout hs tail
    · exact child_of_split hg hn e (ops_swap a b ▸ hz) hout
        (by rw [hs, Finset.insert_comm]) tail

theorem nopt_complete {g : W} (hg : g = goal ∨ g = ~~~goal) : ∀ (k : ℕ) (ws : List W),
    ws.Nodup → live basicOps g k ws.toFinset → nopt k (ws.map BitVec.toNat) = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    have e := singleton_list hn h
    rw [e]
    exact nisGoal_goal hg
  | succ k ih =>
    intro ws hn hl
    rw [nopt_succ]
    rcases child_exists hg hn hl with e | ⟨cW, hcn, _, hcl, hmem⟩
    · rw [e]
      have := nisGoal_goal hg
      simp only [List.map_cons, List.map_nil, this, Bool.true_or]
    · have := ih cW hcn hcl
      rw [Bool.or_eq_true]
      exact .inr (List.any_eq_true.mpr ⟨_, hmem, this⟩)

def rootsN (n : ℕ) (insN : List ℕ) : List (List ℕ) :=
  insN.sublists.filter (fun ws => Nat.ble ws.length (n + 1) && Nat.beq (ncuts ws) M60)

def allKids (m : ℕ) (insN : List ℕ) : List (List ℕ) := (rootsN (m + 1) insN).flatMap (kidsL m)

def isort (l : List ℕ) : List ℕ := l.foldr ins []

def sortK (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => ih (fun s => frc x (fun x2 => insK x2 s k))) l k

theorem sortK_eq (l : List ℕ) : ∀ k : List ℕ → Bool, sortK l k = k (isort l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : sortK (x :: xs) k = sortK xs (fun s => frc x (fun x2 => insK x2 s k)) := rfl
    rw [e, ih, frc_eq, insK_eq]
    rfl

def isortW (l : List W) : List W := l.foldr insW []

theorem isortW_map (l : List W) :
    (isortW l).map BitVec.toNat = isort (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have e1 : isortW (x :: xs) = insW x (isortW xs) := rfl
    have e2 : isort (x.toNat :: xs.map BitVec.toNat) =
        ins x.toNat (isort (xs.map BitVec.toNat)) := rfl
    rw [List.map_cons, e1, e2, insW_map, ih]

theorem isortW_perm (l : List W) : (isortW l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (insW_perm x (isortW xs)).trans (ih.cons x)

def dead (m : ℕ) (c : List ℕ) : Bool := sortK c (fun c2 => Bool.rec true false (nopt m c2))

theorem dead_eq (m : ℕ) (c : List ℕ) : dead m c = !nopt m (isort c) := by
  unfold dead
  rw [sortK_eq, brec]
  cases nopt m (isort c) <;> rfl

theorem refute (m : ℕ) (inputs : List W) (hnd : inputs.Nodup)
    (h0 : (rootsN (m + 1) (inputs.map BitVec.toNat)).all (fun ws => !nisGoal ws) = true)
    (hk : (allKids m (inputs.map BitVec.toNat)).all (dead m) = true) :
    ∀ t, t = goal ∨ t = ~~~goal → build basicOps t (m + 1) inputs.toFinset → False := by
  intro g hg hb
  classical
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd2 : ws.Nodup := hnd.filter _
  have hl2 : live basicOps g (m + 1) ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl2
  rw [List.toFinset_card_of_nodup hnd2] at sz
  have hroot : ws.map BitVec.toNat ∈ rootsN (m + 1) (inputs.map BitVec.toNat) := by
    unfold rootsN
    refine List.mem_filter.mpr ⟨List.mem_sublists.mpr ((List.filter_sublist).map _), ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · apply Nat.ble_eq_true_of_le
      rw [List.length_map]
      exact sz
    · rw [ncuts_map, cuts_full hg hl2, negOne60]
      exact Nat.beq_refl _
  rcases child_exists hg hnd2 hl2 with e | ⟨cW, hcn, _, hcl, hmem⟩
  · have h1 := List.all_eq_true.mp h0 _ hroot
    rw [e] at h1
    have h2 := nisGoal_goal hg
    simp only [List.map_cons, List.map_nil, h2] at h1
    exact absurd h1 (by decide)
  · have hd := List.all_eq_true.mp hk _ (List.mem_flatMap.mpr ⟨_, hroot, hmem⟩)
    have hp := isortW_perm cW
    have e : (isortW cW).toFinset = cW.toFinset := List.toFinset_eq_of_perm _ _ hp
    have run := nopt_complete hg m (isortW cW) (hp.nodup_iff.mpr hcn) (e ▸ hcl)
    rw [isortW_map] at run
    rw [dead_eq, run] at hd
    exact absurd hd (by decide)

end Bridge
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 92 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 92)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

def faceView (w : W) : Wire (Fin 92) := fun i => w.getLsbD i.val
theorem faceView_inj (a b : W) (h : faceView a = faceView b) : a=b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact congrFun h ⟨i,hi⟩
theorem faceInv (a : W) : inv (faceView a) = faceView (~~~a) := by
  funext i
  simp [faceView,inv,BitVec.getLsbD_not,i.isLt]
theorem faceZero : faceView 0 = fun _ => false := by funext i; simp [faceView]
theorem faceOne : faceView (~~~0) = fun _ => true := by
  rw [←faceInv,faceZero]
  rfl
def FaceBank (A : Finset W) (bs : List (Wire (Fin 92))) : Prop :=
  ∀ v ∈ bs, ∃ w, v=faceView w ∧ holds A w
theorem fromAvailable {A bs v} (stock : FaceBank A bs) (h : Available true bs v) :
    ∃ w, v=faceView w ∧ holds A w := by
  rcases h with hm | ⟨b,e⟩ | ⟨_,hm⟩
  · exact stock _ hm
  · rcases b with _ | _
    · exact ⟨0,e.trans faceZero.symm,Or.inl rfl⟩
    · exact ⟨~~~0,e.trans faceOne.symm,Or.inr (Or.inl rfl)⟩
  · obtain ⟨w,e,hw⟩ := stock _ hm
    refine ⟨~~~w,?_,holds_not hw⟩
    rw [←faceInv,←e]
    funext i
    simp [inv]
theorem faceGrow {w : W} {n k : Nat} {A} (h : build basicOps w n A) (le : n ≤ k) :
    build basicOps w k A := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih
def FaceCarry (roots A : Finset W) (p : Nat) := ∀ (w : W) (n : Nat),
    build basicOps w n A → build basicOps w (p+n) roots
theorem faceReach {roots : List W} {p bs} (prog : Reach true (roots.map faceView) p bs) :
    ∃ A, FaceCarry roots.toFinset A p ∧ FaceBank A bs := by
  induction prog using Reach.ind with
  | start =>
    refine ⟨roots.toFinset,fun _ _ h => by simpa using h,?_⟩
    intro _ hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact ⟨w,rfl,Or.inr (Or.inr ⟨w,List.mem_toFinset.mpr hw,Or.inl rfl⟩)⟩
  | @two p bank a b op prog ha hb ih =>
    obtain ⟨A,before,stored⟩ := ih
    obtain ⟨x,rfl,hx⟩ := fromAvailable stored ha
    obtain ⟨y,rfl,hy⟩ := fromAvailable stored hb
    let z := if op then x ||| y else x &&& y
    have ze : combine op (faceView x) (faceView y) = faceView z := by
      funext i
      cases op <;> simp [z,combine,faceView,BitVec.getLsbD_and,BitVec.getLsbD_or]
    have buy : reachable A z := by
      cases op
      · exact and_reach hx hy
      · exact or_reach hx hy
    rcases buy with old|⟨x',hx',y',hy',ne,w,hw,storedZ⟩
    · refine ⟨A,fun t n h => faceGrow (before t n h) (by omega),?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl|hm
      · exact ⟨z,ze,old⟩
      · exact stored _ hm
    · refine ⟨insert w A,?_,?_⟩
      · intro t n h
        have hh : build basicOps t (n+1) A := Or.inr ⟨x',hx',y',hy',ne,w,hw,h⟩
        simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using before t (n+1) hh
      · intro v hv
        rcases List.mem_cons.mp hv with rfl|hm
        · exact ⟨z,ze,storedZ⟩
        · obtain ⟨w',e,ok⟩ := stored _ hm
          exact ⟨w',e,holds_insert ok⟩

def FacePrice (roots : List W) (L : Nat) :=
  ∀ t, t=goal ∨ t = ~~~goal → build basicOps t (L-1) roots.toFinset → False

theorem facePriceLower {roots L} (price : FacePrice roots L) (invert : Bool)
    {p bs} (prog : Reach true (roots.map faceView) p bs)
    (avail : Available true bs (faceView (if invert then ~~~goal else goal))) : L ≤ p := by
  by_contra! less
  obtain ⟨A,before,stored⟩ := faceReach prog
  obtain ⟨w,eq,ha⟩ := fromAvailable stored avail
  have we := faceView_inj _ _ eq
  rcases ha with hz|hz|⟨u,hu,eq'⟩
  · cases invert <;> simp_all [goal]
  · cases invert <;> simp_all [goal]
  have base : build basicOps u 0 A := hu
  have upper : build basicOps u (L-1) roots.toFinset := faceGrow (before u 0 base) (by omega)
  apply price u _ upper
  cases invert <;> rcases eq' with eq'|eq'
  all_goals simp_all

theorem faceStateCut {roots L T S k} (price : FacePrice roots L) (invert : Bool)
    (rows : Fin 92 → Row) (ws : List Sig) (nd : ws.Nodup) (seteq : ws.toFinset=S)
    (target : restrictRows rows (observe T)=faceView (if invert then ~~~goal else goal))
    (available : supply true (roots.map faceView) ((ws.map observe).map (restrictRows rows)))
    (charge : k < L + mass ((ws.map observe).map (restrictRows rows))) : Impossible true T k S := by
  intro t ht actual
  have run := list_run actual ws nd seteq
  have nonconst : ¬Constant (restrictRows rows (observe T)) := by
    rw [target]
    rintro ⟨b,hb⟩
    have lo := congrFun hb (0 : Fin 92)
    have hi := congrFun hb (91 : Fin 92)
    cases invert <;> cases b <;> simp_all [faceView,goal]
  have h := projected_bound rows run nonconst (p:=0) Reach.start available (L:=L)
    (fun q bs hz ha => facePriceLower price invert hz (target ▸ ha))
  omega

abbrev Probe32 := BitVec 32
def view32 (w : Probe32) (i : Fin 32) := w.getLsbD i.val
def lift92 (select : Fin 92 → Fin 32) (w : Probe32) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => view32 w (select i)))).cast (List.length_ofFn)
theorem view_lift (select : Fin 92 → Fin 32) (w : Probe32) (i : Fin 92) :
    faceView (lift92 select w) i = view32 w (select i) := by
  simp only [lift92,faceView,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def sample32 (rows : Fin 32 → Row) (v : Sig) : Probe32 :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (rows i) v))).cast (List.length_ofFn)
theorem sample32_read (rows : Fin 32 → Row) (v : Sig) (i : Fin 32) :
    view32 (sample32 rows v) i = bit (rows i) v := by
  simp only [sample32,view32,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def atFace (rows : Fin 32 → Row) (select : Fin 92 → Fin 32) (v : Sig) : Wire (Fin 92) :=
  restrictRows (fun i => rows (select i)) (observe v)
theorem atFace_eq (rows select v) : atFace rows select v = faceView (lift92 select (sample32 rows v)) := by
  funext i
  change restrictRows _ (observe v) i = faceView (lift92 select (sample32 rows v)) i
  rw [view_lift,sample32_read]
  rfl
theorem lift92_zero (sel : Fin 92 → Fin 32) : lift92 sel 0 = 0 := by
  apply faceView_inj
  funext i
  rw [view_lift]
  simp [view32,faceView]
theorem lift92_not (sel : Fin 92 → Fin 32) (w : Probe32) : lift92 sel (~~~w) = ~~~(lift92 sel w) := by
  apply faceView_inj
  funext i
  rw [view_lift,←faceInv]
  change view32 (~~~w) (sel i) = !(faceView (lift92 sel w) i)
  rw [view_lift]
  simp [view32,BitVec.getLsbD_not,(sel i).isLt]
def silent32 (w : Probe32) := w==0 || w == ~~~0
def avail32 (base : List Probe32) (w : Probe32) := silent32 w || base.contains w || base.contains (~~~w)
theorem face_available32 {base rows sel v} (ok : avail32 base (sample32 rows v)=true) :
    Available true ((base.map (lift92 sel)).map faceView) (atFace rows sel v) := by
  rw [atFace_eq]
  simp only [avail32,silent32,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at ok
  rcases ok with ((h|h)|h)|h
  · rw [h,lift92_zero,faceZero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [h,lift92_not,lift92_zero,faceOne]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem h))
  · right; right; refine ⟨rfl,?_⟩
    have h' := List.mem_map_of_mem (f:=faceView) (List.mem_map_of_mem (f:=lift92 sel) h)
    rwa [lift92_not,←faceInv] at h'
theorem face_charge32 (rows : Fin 32 → Row) (sel : Fin 92 → Fin 32) (ws : List Sig) : ws.countP (fun w => silent32 (sample32 rows w)) ≤
    mass ((ws.map observe).map (restrictRows (fun i : Fin 92 => rows (sel i)))) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons w ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : silent32 (sample32 rows w)
    · simp_all +arith only [Bool.false_eq_true,ite_false,Bool.toNat_false,Nat.zero_add,Nat.add_zero,Nat.le_add_left,ge_iff_le] <;> omega
    · have hc : Constant (atFace rows sel w) := by
        rw [atFace_eq]
        have v : sample32 rows w = 0 ∨ sample32 rows w = ~~~0 := by
          simpa [silent32] using h
        rcases v with p|p
        · rw [p,lift92_zero,faceZero]; exact ⟨false,rfl⟩
        · rw [p,lift92_not,lift92_zero,faceOne]; exact ⟨true,rfl⟩
      change Constant (restrictRows _ (observe w)) at hc
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def facetOK32 (rows : Fin 32 → Row) (roots : List Probe32) (out : Probe32)
    (T : Sig) (ws : List Sig) (k L : Nat) : Bool :=
  decide ws.Nodup && (sample32 rows T == out || sample32 rows T == ~~~out) &&
    ws.all (fun v => avail32 roots (sample32 rows v)) &&
    decide (k < L+ws.countP (fun w => silent32 (sample32 rows w)))
theorem facetOK32_sound {rows roots out T ws k L sel}
    (hprice : FacePrice (roots.map (lift92 sel)) L) (hout : lift92 sel out=goal)
    (ok : facetOK32 rows roots out T ws k L=true) : Impossible true T k ws.toFinset := by
  simp only [facetOK32,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨nd,sign⟩,covered⟩,hc⟩ := ok
  have bank : supply true (((roots.map (lift92 sel)).map faceView)) ((ws.map observe).map (restrictRows (fun i => rows (sel i)))) := by
    intro v hv
    obtain ⟨_,hmem,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hm,rfl⟩ := List.mem_map.mp hmem
    exact face_available32 (covered a hm)
  have charge := Nat.lt_of_lt_of_le hc (Nat.add_le_add_left (face_charge32 rows sel ws) L)
  rcases sign with hs|hs
  · apply faceStateCut hprice false (fun i => rows (sel i)) ws nd rfl _ bank charge
    change atFace rows sel T = faceView goal
    rw [atFace_eq,hs,hout]
  · apply faceStateCut hprice true (fun i => rows (sel i)) ws nd rfl _ bank charge
    change atFace rows sel T = faceView (~~~goal)
    rw [atFace_eq,hs,lift92_not,hout]
def facet0 : List W := [(BitVec.ofNat 92 ((0x3c03c0 <<< 64) + 0x3c03f77777777777)),(BitVec.ofNat 92 ((0x3c03c0 <<< 64) + 0x3c03e66666666666)),(BitVec.ofNat 92 ((0x3c03c03 <<< 64) + 0xc03c2aaaaaaaaaaa)),(BitVec.ofNat 92 ((0xc03c03c <<< 64) + 0x3c00ccccccccccc))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem facetPrice0 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 4 facet0.toFinset → False :=
  refute 3 facet0 (by decide) (by decide +kernel) (by decide +kernel)
def facet1 : List W := [(BitVec.ofNat 92 ((0x81c0e07 <<< 64) + 0x381edb6db6db6db)),(BitVec.ofNat 92 ((0x81c0e07 <<< 64) + 0x381e49249249249)),(BitVec.ofNat 92 ((0xe07038 <<< 64) + 0x1c0e36db6db6db6d)),(BitVec.ofNat 92 ((0x70381c0 <<< 64) + 0xe0701b6db6db6db6))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem facetPrice1 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 3 facet1.toFinset → False :=
  refute 2 facet1 (by decide) (by decide +kernel) (by decide +kernel)
def facet2 : List W := [(BitVec.ofNat 92 ((0x3c03c03 <<< 64) + 0xc03c2aaaaaaaaaaa)),(BitVec.ofNat 92 ((0x3c03c0 <<< 64) + 0x3c03e66666666666)),(BitVec.ofNat 92 ((0x3c03c03 <<< 64) + 0xc03c3bbbbbbbbbbb)),(BitVec.ofNat 92 ((0xc03c03c <<< 64) + 0x3c00ccccccccccc))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem facetPrice2 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 4 facet2.toFinset → False :=
  refute 3 facet2 (by decide) (by decide +kernel) (by decide +kernel)
def facet3 : List W := [(BitVec.ofNat 92 ((0x3fc3fc3 <<< 64) + 0xfc3feaaaaaaaaaaa)),(BitVec.ofNat 92 ((0x3c03c0 <<< 64) + 0x3c03e66666666666)),(BitVec.ofNat 92 ((0x3c03c03 <<< 64) + 0xc03c3bbbbbbbbbbb)),(BitVec.ofNat 92 ((0xc03c03c <<< 64) + 0x3c00ccccccccccc))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem facetPrice3 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 4 facet3.toFinset → False :=
  refute 3 facet3 (by decide) (by decide +kernel) (by decide +kernel)
def facet4 : List W := [(BitVec.ofNat 92 ((0x3fc03f <<< 64) + 0xc03ff33333333333)),(BitVec.ofNat 92 ((0x3c3c3c3 <<< 64) + 0xc3c3d55555555555)),(BitVec.ofNat 92 ((0x3fc03fc <<< 64) + 0x3fc199999999999)),(BitVec.ofNat 92 ((0xc003c00 <<< 64) + 0x3c002eeeeeeeeeee))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem facetPrice4 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 5 facet4.toFinset → False :=
  refute 4 facet4 (by decide) (by decide +kernel) (by decide +kernel)
def facet5 : List W := [(BitVec.ofNat 92 ((0xe07038 <<< 64) + 0x1c0e092492492492)),(BitVec.ofNat 92 ((0x81c0e07 <<< 64) + 0x381f6db6db6db6d)),(BitVec.ofNat 92 ((0xe07038 <<< 64) + 0x1c0e249249249249)),(BitVec.ofNat 92 ((0x70381c0 <<< 64) + 0xe0701b6db6db6db6))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem facetPrice5 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 3 facet5.toFinset → False :=
  refute 2 facet5 (by decide) (by decide +kernel) (by decide +kernel)
def facet6 : List W := [(BitVec.ofNat 92 ((0xe07038 <<< 64) + 0x1c0e2db6db6db6db)),(BitVec.ofNat 92 ((0x81c0e07 <<< 64) + 0x381f6db6db6db6d)),(BitVec.ofNat 92 ((0xe07038 <<< 64) + 0x1c0e249249249249)),(BitVec.ofNat 92 ((0x70381c0 <<< 64) + 0xe0701b6db6db6db6))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem facetPrice6 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 3 facet6.toFinset → False :=
  refute 2 facet6 (by decide) (by decide +kernel) (by decide +kernel)
def facet7 : List W := [(BitVec.ofNat 92 ((0x8fc7e3f <<< 64) + 0x1f8fedb6db6db6db)),(BitVec.ofNat 92 ((0x81c0e07 <<< 64) + 0x381f6db6db6db6d)),(BitVec.ofNat 92 ((0xe07038 <<< 64) + 0x1c0e249249249249)),(BitVec.ofNat 92 ((0x70381c0 <<< 64) + 0xe0701b6db6db6db6))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem facetPrice7 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 3 facet7.toFinset → False :=
  refute 2 facet7 (by decide) (by decide +kernel) (by decide +kernel)
def teaching0 : List W := [(BitVec.ofNat 92 ((0x7c0007c <<< 64) + 0x7e318c6318c63)),(BitVec.ofNat 92 ((0x7c0007c <<< 64) + 0x7c21084210842)),(BitVec.ofNat 92 ((0x8000f80 <<< 64) + 0xf80e739ce739ce)),(BitVec.ofNat 92 ((0x1f000 <<< 64) + 0x1f0014a5294a5294)),(BitVec.ofNat 92 ((0x3e0003 <<< 64) + 0xe00018c6318c6318))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem teachingPrice0 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 teaching0.toFinset → False :=
  refute 5 teaching0 (by decide) (by decide +kernel) (by decide +kernel)
def teaching1 : List W := [(BitVec.ofNat 92 ((0x3fc03f <<< 64) + 0xc03ff33333333333)),(BitVec.ofNat 92 ((0x3fc03f <<< 64) + 0xc03fd11111111111)),(BitVec.ofNat 92 ((0x3c3c3c3 <<< 64) + 0xc3c3d55555555555)),(BitVec.ofNat 92 ((0x3fc03fc <<< 64) + 0x3fc199999999999)),(BitVec.ofNat 92 ((0xc003c00 <<< 64) + 0x3c002eeeeeeeeeee))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem teachingPrice1 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 5 teaching1.toFinset → False :=
  refute 4 teaching1 (by decide) (by decide +kernel) (by decide +kernel)
def teaching2 : List W := [(BitVec.ofNat 92 ((0x7c1f003 <<< 64) + 0xe0f82739ce739ce7)),(BitVec.ofNat 92 ((0x7c1f003 <<< 64) + 0xe0f806318c6318c6)),(BitVec.ofNat 92 ((0x1ff80 <<< 64) + 0xffeb5ad6b5ad6b)),(BitVec.ofNat 92 ((0x7fe0003 <<< 64) + 0xff001294a5294a52)),(BitVec.ofNat 92 ((0x800007c <<< 64) + 0x1ce739ce739c))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem teachingPrice2 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 teaching2.toFinset → False :=
  refute 5 teaching2 (by decide) (by decide +kernel) (by decide +kernel)
def teaching3 : List W := [(BitVec.ofNat 92 ((0xfc00ffc <<< 64) + 0xffdce739ce739c)),(BitVec.ofNat 92 ((0x7c1f07c <<< 64) + 0x1f07e94a5294a529)),(BitVec.ofNat 92 ((0x7c0007c <<< 64) + 0x7fdef7bdef7bd)),(BitVec.ofNat 92 ((0x801ff80 <<< 64) + 0x1ff80e739ce739ce)),(BitVec.ofNat 92 ((0x3e0003 <<< 64) + 0xe000108421084210))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem teachingPrice3 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 5 teaching3.toFinset → False :=
  refute 4 teaching3 (by decide) (by decide +kernel) (by decide +kernel)
def teaching4 : List W := [(BitVec.ofNat 92 ((0xfff03f <<< 64) + 0x3ffdc71c71c71c7)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff038e38e38e38e)),(BitVec.ofNat 92 ((0xf000000 <<< 64) + 0xfc000d34d34d34d3)),(BitVec.ofNat 92 ((0x3f <<< 64) + 0x124924924924)),(BitVec.ofNat 92 ((0xfc0 <<< 64) + 0x238e38e38e38))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem teachingPrice4 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 teaching4.toFinset → False :=
  refute 5 teaching4 (by decide) (by decide +kernel) (by decide +kernel)
def teaching5 : List W := [(BitVec.ofNat 92 ((0x24d8b62 <<< 64) + 0x6d257b8597bbb6db)),(BitVec.ofNat 92 ((0xc721384 <<< 64) + 0x8e499c289ad2b8e3)),(BitVec.ofNat 92 ((0xf801c00 <<< 64) + 0xf00e2153730fd34d)),(BitVec.ofNat 92 ((0x3e007 <<< 64) + 0x703953e19d638e)),(BitVec.ofNat 92 ((0x18 <<< 64) + 0x8006ac0c600c30))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem teachingPrice5 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 7 teaching5.toFinset → False :=
  refute 6 teaching5 (by decide) (by decide +kernel) (by decide +kernel)
def teaching6 : List W := [(BitVec.ofNat 92 ((0x7c1ff83 <<< 64) + 0xe0ffe739ce739ce7)),(BitVec.ofNat 92 ((0x3e0f80 <<< 64) + 0x1f07eb5ad6b5ad6b)),(BitVec.ofNat 92 ((0x3ff000 <<< 64) + 0x1ff8210842108421)),(BitVec.ofNat 92 ((0x7c00003 <<< 64) + 0xe0001294a5294a52)),(BitVec.ofNat 92 ((0x800007c <<< 64) + 0x1ce739ce739c))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem teachingPrice6 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 teaching6.toFinset → False :=
  refute 5 teaching6 (by decide) (by decide +kernel) (by decide +kernel)
def teaching7 : List W := [(BitVec.ofNat 92 ((0x3ffc03c <<< 64) + 0x3ffc266666666666)),(BitVec.ofNat 92 ((0x3ffc0 <<< 64) + 0x3fd55555555555)),(BitVec.ofNat 92 ((0xc3c0003 <<< 64) + 0xc3c02aaaaaaaaaaa)),(BitVec.ofNat 92 ((0xfc00003 <<< 64) + 0xfc00333333333333)),(BitVec.ofNat 92 ((0x3fc <<< 64) + 0xccccccccccc))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem teachingPrice7 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 teaching7.toFinset → False :=
  refute 5 teaching7 (by decide) (by decide +kernel) (by decide +kernel)
def sixface0 : List W := [(BitVec.ofNat 92 ((0x1f000 <<< 64) + 0xf806318c6318c6)),(BitVec.ofNat 92 ((0x1f000 <<< 64) + 0xf816b5ad6b5ad6)),(BitVec.ofNat 92 ((0x800007c <<< 64) + 0x318c6318c631)),(BitVec.ofNat 92 ((0x3e0000 <<< 64) + 0x1f000a5294a5294a)),(BitVec.ofNat 92 ((0x7c00003 <<< 64) + 0xe0000c6318c6318c)),(BitVec.ofNat 92 ((0x800007c <<< 64) + 0x108421084210))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice0 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface0.toFinset → False :=
  refute 5 sixface0 (by decide) (by decide +kernel) (by decide +kernel)
def sixface1 : List W := [(BitVec.ofNat 92 ((0xf01fc00 <<< 64) + 0xfe0081020408102)),(BitVec.ofNat 92 ((0x3ff <<< 64) + 0xf00037efdfbf7efd)),(BitVec.ofNat 92 ((0xf01fc07 <<< 64) + 0xffe03b76eddbb76e)),(BitVec.ofNat 92 ((0xf000007 <<< 64) + 0xffe0204081020408)),(BitVec.ofNat 92 ((0x7 <<< 64) + 0xf00002850a142850)),(BitVec.ofNat 92 ((0x1fff8 <<< 64) + 0x3060c183060))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice1 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface1.toFinset → False :=
  refute 5 sixface1 (by decide) (by decide +kernel) (by decide +kernel)
def sixface2 : List W := [(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc0037df7df7df7d)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc0037df7df7df7d)),(BitVec.ofNat 92 ((0xffc003f <<< 64) + 0xfff01b6db6db6db6)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff0104104104104)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc00228a28a28a28)),(BitVec.ofNat 92 ((0xfff <<< 64) + 0x30c30c30c30))]
def sixShort2 : List W := [(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc0037df7df7df7d)),(BitVec.ofNat 92 ((0xffc003f <<< 64) + 0xfff01b6db6db6db6)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff0104104104104)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc00228a28a28a28)),(BitVec.ofNat 92 ((0xfff <<< 64) + 0x30c30c30c30))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice2 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface2.toFinset → False :=
by
  have same : sixface2.toFinset=sixShort2.toFinset := by decide +kernel
  rw [same]
  exact refute 5 sixShort2 (by decide) (by decide +kernel) (by decide +kernel)
def sixface3 : List W := [(BitVec.ofNat 92 ((0xfc003f <<< 64) + 0x3f0269a69a69a69)),(BitVec.ofNat 92 ((0xfc003f <<< 64) + 0x3f0269a69a69a69)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc003befbefbefbe)),(BitVec.ofNat 92 ((0xfc0 <<< 64) + 0x124924924924)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff0208208208208)),(BitVec.ofNat 92 ((0xfff <<< 64) + 0x30c30c30c30))]
def sixShort3 : List W := [(BitVec.ofNat 92 ((0xfc003f <<< 64) + 0x3f0269a69a69a69)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc003befbefbefbe)),(BitVec.ofNat 92 ((0xfc0 <<< 64) + 0x124924924924)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff0208208208208)),(BitVec.ofNat 92 ((0xfff <<< 64) + 0x30c30c30c30))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice3 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface3.toFinset → False :=
by
  have same : sixface3.toFinset=sixShort3.toFinset := by decide +kernel
  rw [same]
  exact refute 5 sixShort3 (by decide) (by decide +kernel) (by decide +kernel)
def sixface4 : List W := [(BitVec.ofNat 92 ((0xffe03ff <<< 64) + 0xffe012a54a952a54)),(BitVec.ofNat 92 ((0xffe03ff <<< 64) + 0xffe012a54a952a54)),(BitVec.ofNat 92 ((0xfe03f8 <<< 64) + 0xfe017af5ebd7af5)),(BitVec.ofNat 92 ((0xf0003ff <<< 64) + 0xf0001bb76eddbb76)),(BitVec.ofNat 92 ((0xffe0007 <<< 64) + 0xffe022c58b162c58)),(BitVec.ofNat 92 ((0x3f8 <<< 64) + 0x3060c183060))]
def sixShort4 : List W := [(BitVec.ofNat 92 ((0xffe03ff <<< 64) + 0xffe012a54a952a54)),(BitVec.ofNat 92 ((0xfe03f8 <<< 64) + 0xfe017af5ebd7af5)),(BitVec.ofNat 92 ((0xf0003ff <<< 64) + 0xf0001bb76eddbb76)),(BitVec.ofNat 92 ((0xffe0007 <<< 64) + 0xffe022c58b162c58)),(BitVec.ofNat 92 ((0x3f8 <<< 64) + 0x3060c183060))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice4 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface4.toFinset → False :=
by
  have same : sixface4.toFinset=sixShort4.toFinset := by decide +kernel
  rw [same]
  exact refute 5 sixShort4 (by decide) (by decide +kernel) (by decide +kernel)
def sixface5 : List W := [(BitVec.ofNat 92 ((0xfc0 <<< 64) + 0x71c71c71c71)),(BitVec.ofNat 92 ((0xf000fff <<< 64) + 0x3f0175d75d75d75)),(BitVec.ofNat 92 ((0x3f03f <<< 64) + 0xfc003befbefbefbe)),(BitVec.ofNat 92 ((0xf00003f <<< 64) + 0xfff0104104104104)),(BitVec.ofNat 92 ((0x3f <<< 64) + 0x228a28a28a28)),(BitVec.ofNat 92 ((0x3ffc0 <<< 64) + 0x30c30c30c30))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice5 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface5.toFinset → False :=
  refute 5 sixface5 (by decide) (by decide +kernel) (by decide +kernel)
def sixface6 : List W := [(BitVec.ofNat 92 ((0xffe0007 <<< 64) + 0xffe0008102040810)),(BitVec.ofNat 92 ((0x3f8 <<< 64) + 0x274e9d3a74e9)),(BitVec.ofNat 92 ((0xfe0000 <<< 64) + 0xfe0089122448912)),(BitVec.ofNat 92 ((0xf000007 <<< 64) + 0xf00012a54a952a54)),(BitVec.ofNat 92 ((0xffe03ff <<< 64) + 0xffe022c58b162c58)),(BitVec.ofNat 92 ((0x3f8 <<< 64) + 0x3060c183060))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice6 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface6.toFinset → False :=
  refute 5 sixface6 (by decide) (by decide +kernel) (by decide +kernel)
def sixface7 : List W := [(BitVec.ofNat 92 ((0xffc003f <<< 64) + 0xfff0175d75d75d75)),(BitVec.ofNat 92 ((0xffc003f <<< 64) + 0xfff0175d75d75d75)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc003befbefbefbe)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff0104104104104)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc00228a28a28a28)),(BitVec.ofNat 92 ((0xfff <<< 64) + 0x30c30c30c30))]
def sixShort7 : List W := [(BitVec.ofNat 92 ((0xffc003f <<< 64) + 0xfff0175d75d75d75)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc003befbefbefbe)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff0104104104104)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc00228a28a28a28)),(BitVec.ofNat 92 ((0xfff <<< 64) + 0x30c30c30c30))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice7 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface7.toFinset → False :=
by
  have same : sixface7.toFinset=sixShort7.toFinset := by decide +kernel
  rw [same]
  exact refute 5 sixShort7 (by decide) (by decide +kernel) (by decide +kernel)
def sixface8 : List W := [(BitVec.ofNat 92 ((0xf00003f <<< 64) + 0x3f02fbefbefbefb)),(BitVec.ofNat 92 ((0xf00003f <<< 64) + 0x3f02fbefbefbefb)),(BitVec.ofNat 92 ((0xf03f000 <<< 64) + 0x3f029a69a69a69a)),(BitVec.ofNat 92 ((0x3ffc0 <<< 64) + 0xfc0032cb2cb2cb2c)),(BitVec.ofNat 92 ((0xf000000 <<< 64) + 0xfff0208208208208)),(BitVec.ofNat 92 ((0x3ffff <<< 64) + 0x30c30c30c30))]
def sixShort8 : List W := [(BitVec.ofNat 92 ((0xf00003f <<< 64) + 0x3f02fbefbefbefb)),(BitVec.ofNat 92 ((0xf03f000 <<< 64) + 0x3f029a69a69a69a)),(BitVec.ofNat 92 ((0x3ffc0 <<< 64) + 0xfc0032cb2cb2cb2c)),(BitVec.ofNat 92 ((0xf000000 <<< 64) + 0xfff0208208208208)),(BitVec.ofNat 92 ((0x3ffff <<< 64) + 0x30c30c30c30))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice8 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface8.toFinset → False :=
by
  have same : sixface8.toFinset=sixShort8.toFinset := by decide +kernel
  rw [same]
  exact refute 5 sixShort8 (by decide) (by decide +kernel) (by decide +kernel)
def sixface9 : List W := [(BitVec.ofNat 92 ((0xfc0003f <<< 64) + 0xffc016d6d6d6d6d6)),(BitVec.ofNat 92 ((0x3f <<< 64) + 0xc00016d6d6d6d6d6)),(BitVec.ofNat 92 ((0xfc03fc0 <<< 64) + 0x3fc02dededededed)),(BitVec.ofNat 92 ((0xfc0003f <<< 64) + 0xffc0064646464646)),(BitVec.ofNat 92 ((0x3fc0 <<< 64) + 0x88888888888)),(BitVec.ofNat 92 ((0x3fff <<< 64) + 0xc00030f0f0f0f0f0))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice9 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface9.toFinset → False :=
  refute 5 sixface9 (by decide) (by decide +kernel) (by decide +kernel)
def sixface10 : List W := [(BitVec.ofNat 92 ((0x3fff <<< 64) + 0xc00035b5b5b5b5b5)),(BitVec.ofNat 92 ((0x3f <<< 64) + 0xc000367676767676)),(BitVec.ofNat 92 ((0x3fc000 <<< 64) + 0x181818181818)),(BitVec.ofNat 92 ((0x0 <<< 64) + 0x3fc020a0a0a0a0a0)),(BitVec.ofNat 92 ((0x3f <<< 64) + 0xc000303030303030)),(BitVec.ofNat 92 ((0x3fffc0 <<< 64) + 0xc0c0c0c0c0))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice10 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface10.toFinset → False :=
  refute 5 sixface10 (by decide) (by decide +kernel) (by decide +kernel)
def sixface11 : List W := [(BitVec.ofNat 92 ((0x1f00fc0 <<< 64) + 0x1e072d352f297865)),(BitVec.ofNat 92 ((0xe004000 <<< 64) + 0x80102555240a1126)),(BitVec.ofNat 92 ((0xcc31b8 <<< 64) + 0x690a822a8191e4d0)),(BitVec.ofNat 92 ((0x100be01 <<< 64) + 0x702c12aad1d5e6d8)),(BitVec.ofNat 92 ((0x1f03fc0 <<< 64) + 0x7e0f202425017060)),(BitVec.ofNat 92 ((0xe00c001 <<< 64) + 0x8030000880800080))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice11 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 7 sixface11.toFinset → False :=
  refute 6 sixface11 (by decide) (by decide +kernel) (by decide +kernel)
def sixface12 : List W := [(BitVec.ofNat 92 ((0xb847c72 <<< 64) + 0xcaaa9cb5618b6d68)),(BitVec.ofNat 92 ((0x38001 <<< 64) + 0x1040b442a860631)),(BitVec.ofNat 92 ((0xb83fc71 <<< 64) + 0xc9a6bfffbdf7bfbe)),(BitVec.ofNat 92 ((0xb83fc71 <<< 64) + 0xc9a68a6630d2243c)),(BitVec.ofNat 92 ((0x3840072 <<< 64) + 0xa28900101000800)),(BitVec.ofNat 92 ((0xc07ff83 <<< 64) + 0xf3cf1d99c92fcfc0))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice12 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 7 sixface12.toFinset → False :=
  refute 6 sixface12 (by decide) (by decide +kernel) (by decide +kernel)
def sixface13 : List W := [(BitVec.ofNat 92 ((0xf0003ff <<< 64) + 0xffe037efdfbf7efd)),(BitVec.ofNat 92 ((0xf0003f8 <<< 64) + 0xfe037efdfbf7efd)),(BitVec.ofNat 92 ((0x1ffff <<< 64) + 0xf0003b76eddbb76e)),(BitVec.ofNat 92 ((0x1fc07 <<< 64) + 0xf0001bb76eddbb76)),(BitVec.ofNat 92 ((0xf000007 <<< 64) + 0xffe021c3870e1c38)),(BitVec.ofNat 92 ((0x1fff8 <<< 64) + 0x20408102040))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice13 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface13.toFinset → False :=
  refute 5 sixface13 (by decide) (by decide +kernel) (by decide +kernel)
def sixface14 : List W := [(BitVec.ofNat 92 ((0xe000180 <<< 64) + 0x44082010400b041)),(BitVec.ofNat 92 ((0xfce01 <<< 64) + 0xd88d195760d77295)),(BitVec.ofNat 92 ((0xe0001 <<< 64) + 0x80082dae89660726)),(BitVec.ofNat 92 ((0x70300e <<< 64) + 0x201237f4f7bdcbf8)),(BitVec.ofNat 92 ((0x3000 <<< 64) + 0x2002020004008040)),(BitVec.ofNat 92 ((0x7fc00f <<< 64) + 0xc01c053420350380))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice14 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 7 sixface14.toFinset → False :=
  refute 6 sixface14 (by decide) (by decide +kernel) (by decide +kernel)
def sixface15 : List W := [(BitVec.ofNat 92 ((0x7fefff1 <<< 64) + 0xfcf7bffffffff7fd)),(BitVec.ofNat 92 ((0x60070 <<< 64) + 0x1c10b6c109897ba6)),(BitVec.ofNat 92 ((0xf81f80 <<< 64) + 0xe0632a0e5317a6c8)),(BitVec.ofNat 92 ((0x718e781 <<< 64) + 0x60a511575da7c770)),(BitVec.ofNat 92 ((0x1e07f0 <<< 64) + 0x7c31b20009016380)),(BitVec.ofNat 92 ((0x7e0f801 <<< 64) + 0x80c6000010060400))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice15 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 7 sixface15.toFinset → False :=
  refute 6 sixface15 (by decide) (by decide +kernel) (by decide +kernel)
def sixface16 : List W := [(BitVec.ofNat 92 ((0x3fffc0 <<< 64) + 0x3fc03dfdfdfdfdfd)),(BitVec.ofNat 92 ((0x3fc0 <<< 64) + 0x3fc039f9f9f9f9f9)),(BitVec.ofNat 92 ((0x3fc000 <<< 64) + 0x3fc02cececececec)),(BitVec.ofNat 92 ((0x3fc03f <<< 64) + 0xc0003ebebebebebe)),(BitVec.ofNat 92 ((0x3f <<< 64) + 0xffc0303030303030)),(BitVec.ofNat 92 ((0x3fffc0 <<< 64) + 0xc0c0c0c0c0))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice16 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface16.toFinset → False :=
  refute 5 sixface16 (by decide) (by decide +kernel) (by decide +kernel)
def sixface17 : List W := [(BitVec.ofNat 92 ((0xf00003f <<< 64) + 0xfc00104104104104)),(BitVec.ofNat 92 ((0xfc0fc0 <<< 64) + 0x3f0279e79e79e79)),(BitVec.ofNat 92 ((0xf00003f <<< 64) + 0xfc001a69a69a69a6)),(BitVec.ofNat 92 ((0xfc003f <<< 64) + 0x3f0104104104104)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc00228a28a28a28)),(BitVec.ofNat 92 ((0xfff <<< 64) + 0x30c30c30c30))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice17 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface17.toFinset → False :=
  refute 5 sixface17 (by decide) (by decide +kernel) (by decide +kernel)
def sixface18 : List W := [(BitVec.ofNat 92 ((0xffc003f <<< 64) + 0xfff02db6db6db6db)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff0259659659659)),(BitVec.ofNat 92 ((0x3f <<< 64) + 0x28a28a28a28a)),(BitVec.ofNat 92 ((0xf00003f <<< 64) + 0xfc002aaaaaaaaaaa)),(BitVec.ofNat 92 ((0xfc0 <<< 64) + 0x134d34d34d34)),(BitVec.ofNat 92 ((0xffc0fff <<< 64) + 0xfff0238e38e38e38))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice18 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface18.toFinset → False :=
  refute 5 sixface18 (by decide) (by decide +kernel) (by decide +kernel)
def sixface19 : List W := [(BitVec.ofNat 92 ((0xfe03ff <<< 64) + 0xffe02952a54a952a)),(BitVec.ofNat 92 ((0x1fff8 <<< 64) + 0xfe037efdfbf7efd)),(BitVec.ofNat 92 ((0xfe03ff <<< 64) + 0xf0003bf7efdfbf7e)),(BitVec.ofNat 92 ((0x3ff <<< 64) + 0xffe02142850a1428)),(BitVec.ofNat 92 ((0xfe03f8 <<< 64) + 0x20408102040)),(BitVec.ofNat 92 ((0xfffc00 <<< 64) + 0x3870e1c3870))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice19 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface19.toFinset → False :=
  refute 5 sixface19 (by decide) (by decide +kernel) (by decide +kernel)
def sixface20 : List W := [(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc00082082082082)),(BitVec.ofNat 92 ((0xfc003f <<< 64) + 0x3f037df7df7df7d)),(BitVec.ofNat 92 ((0xffc0fc0 <<< 64) + 0xfff039e79e79e79e)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc003aebaebaebae)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff0208208208208)),(BitVec.ofNat 92 ((0xfff <<< 64) + 0x30c30c30c30))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice20 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface20.toFinset → False :=
  refute 5 sixface20 (by decide) (by decide +kernel) (by decide +kernel)
def sixface21 : List W := [(BitVec.ofNat 92 ((0xffc003f <<< 64) + 0xfff0279e79e79e79)),(BitVec.ofNat 92 ((0xfc003f <<< 64) + 0x3f0269a69a69a69)),(BitVec.ofNat 92 ((0xfc0fff <<< 64) + 0x3f0175d75d75d75)),(BitVec.ofNat 92 ((0xf000fc0 <<< 64) + 0xfc003befbefbefbe)),(BitVec.ofNat 92 ((0xffc0000 <<< 64) + 0xfff0218618618618)),(BitVec.ofNat 92 ((0xfff <<< 64) + 0x20820820820))]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixfacePrice21 : ∀ t, t=goal ∨ t = ~~~goal → build basicOps t 6 sixface21.toFinset → False :=
  refute 5 sixface21 (by decide) (by decide +kernel) (by decide +kernel)
end Nat92GE

def g63Y : Array (Bits × Bits) := #[((bitLimbs [0xde2fffecdfefb7fe24,0xfd0134df79125f96f973]),(bitLimbs [0xa06242024e9910024,0x6100748d00121f84f140])),((bitLimbs [0xf5503c3b283fcee9db,0xc7fedeaad4fda56597ab]),(bitLimbs [0x7018380b000fc7495a,0x8426d28ad4f42520162b])),((bitLimbs [0x2ff76a2be05e6c1477,0x90d689a536f5605be5de]),(bitLimbs [0xf72ca28e016780415,0xf09028243665405be1d6])),((bitLimbs [0x9ba2cff09f04f9c7d8,0x2fffdf7e8f8ddb39423c]),(bitLimbs [0x81a0c1d14a1028c140,0x65d03720b89c011023c])),((bitLimbs [0x31cfad16d8cbe79bed,0x96abe3c1f34fc3ea3e44]),(bitLimbs [0x50dd8c46d808459a8a,0x929bc1c1f34dc3ea1c00])),((bitLimbs [0xe3dc53df34f95ef91f,0xde42373243e2b4ee5dd5]),(bitLimbs [0xe9280351325016b003,0x4c4f27324182b06e4dd5])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,16,2095,0,9),(0,32,2079,0,9),(0,4,2107,0,8),(2,0,61,0,8),(32,0,31,0,8),(0,2,2109,0,7),(1,0,62,0,7),(4,0,59,0,7),(8,0,55,0,7),(16,0,47,0,7),(0,8,2103,0,6),(2,16,45,0,6),(4,32,27,0,6),(0,18,4141,0,5),(0,20,4139,0,5),(0,36,4123,0,5),(0,40,2071,0,5),(0,48,6159,0,5),(1,4,58,0,5),(1,8,54,0,5),(1,16,46,0,5),(1,32,30,0,5),(2,4,57,0,5),(2,32,29,0,5),(8,16,2087,0,5),(16,2,2093,0,5),(16,4,2091,0,5),(24,0,39,0,5),(32,2,2077,0,5),(32,4,2075,0,5),(48,0,15,0,5),(1,2,60,0,4),(1,20,42,0,4),(1,40,22,0,4),(1,48,14,0,4),(2,36,25,0,4),(4,2,2105,0,4),(4,16,43,0,4),(8,2,37,0,4),(8,4,51,0,4),(8,18,37,0,4),(8,32,23,0,4),(16,32,2063,0,4),(24,2,37,0,4),(32,16,4111,0,4),(48,2,13,0,4),(48,4,11,0,4)]
def g63A : List (List Nat) := [[]]
def g63D5 := limbs80 #[#[0xa5f09c8418d3048110]]
def g63D6 := limbs80 #[#[0xcc740480200c74048020,0x10f41c80205944358420,0xd0c43580219d17010c21,0x600214c0306074358021,0x5cc7258031a085458031,0xa0b53580315ce7258031,0x10d700844058c4308440,0x60664580435857008440,0x1c962584439927158043,0x18d200811010d2008110,0x60043481102097010d10,0x18d30481101893048110,0x18a31481102093048110,0x1d0724c11018c724c110,0x18a31c811018d30c8110,0x5c5300c120209300c120,0x1cb414c1201cb304c120,0xd0d70085309917008530,0x21130c82206002110130,0x9d2624c310d0d7008630,0xd0d70087401917008730,0x55b69f53ba6f4be5f4af,0xdb17e27c3f6b6d5d7caf,0x55eaad4fa6b3e67acf19,0x717dd5af35d6b9d67ab7,0xbb4bdcb9d72de4fc6f8d,0x449908b98c3987904fa8,0xb8c6c02c81105087054a,0xec0ad3a0c8304a044a12,0x408c822c90cc2642390e,0xe3a3512e69804b9e2b21,0x8cd008672a422cfac66b],#[0xe8ae321b4336e0eab90c,0x50cec3bb000b205b4b08,0x3494c88a4b2c194c8a0c,0x874bae3b2e93c32c2332,0xc8881529397438476e6a,0xc01128510c8c6c50cc8c,0x280002432bcd908c3a32,0x5a189b50ee090930c916,0xf0230200b03703e820b,0xfc1]]
def g63H6 := limbs80 #[#[0x4000000002]]
private def groupPage0 := limbs80 #[#[0x440105d8430417010c10,0x4130440101c91004043,0x58f4204074cc01058d10,0xc4201503108163d4810,0x82730c4205c03108163,0x98c410816310420d8c31,0x10c205c0430816510c20,0x827110c205d84308171,0x1052008176144209d843,0x48020145200804348020,0x834048020cc52008330,0x98930080744c020d0520,0x584201cd610804358420,0x807158c2058d6108074,0x10e610837158c201d163,0x984209ce610816398420,0x8331c802010f2008274,0xd073008041cc020d0720,0xcc42058f3108054cc420,0x8263cc4205db3108165,0xd8f3108275cc4209d331,0xd0420d074008331d0020,0x8165d042058f4108043,0x9cf4108263d04205c341,0x10c215c04308563d4420,0x874310c219c04308576,0x1516008443580215c054,0x580211d1600847358021,0x8674580219cd6008573,0xdcd600875358021d0d60,0xd4c215db430844398021,0xc170084309d35308576],#[0x85300c17014830d4c21,0x4c030145300c0414c030,0xc0724c0301c5300c052,0x589300c1614c0301d130,0x4c030985300c2214c030,0xc3404c030c85300c262,0xd49300c3514c030d0530,0x4c030dc9300c3714c030,0xc0724c430dd9300c374,0xd4d610c2325843014961,0x98030586310c35388430,0xc321d4030087500c021,0x5d8520c570108319cb51,0x4c4319c8540c57015031,0xc7524c4311c9310c452,0x149600c7764c431dc931,0x580311c9600c45458031,0xc632580314c5600c474,0x5da320c753580319c960,0x190329cb530c576d4c31,0xc87158032dd9320c970,0x10c2110353580329c560,0x84405c0211016108440,0x1016310c405c03110176,0x10d6110170144405c043,0xd00409cb311007258440,0x10563d00405874010021,0x5da32106325804198c52,0x580421c56010973d4841,0x10c72580431c56010f73,0x9856010d625804358560,0x580439916010e6258043],#[0x10c7258443d4d6010e71,0x5866010f705844358961,0x845058c211427198043,0x1437158c5010d6214176,0x5c33114163cc4509cf21,0xd045058f4114162d0450,0x145320c8519cf4114170,0x9cc42145701085158c42,0x58051109601457010c51,0x14742580518c96014443,0x58f4214443980515da32,0x5805258c4314a73d0851,0x1484398052dc16114b73,0x1c96015071580545c264,0x811010c204437258054,0x44173081104802044063,0x18830440520c1109c820,0x10d105c043441700c910,0x44043189105c05244272,0x10d20443631891018c62,0x48110189204405348110,0x44131481104c12044063,0x8c92044231481108c120,0x48110cc1204426348110,0x4436348110d4d2044343,0x18d30440624c11014930,0x4c1101c930440714c110,0x443634c110d893044352,0x1d932443724c110dc530,0x8811018e204404388110,0x440628c11014a3044276,0x18e32440628c5109da30],#[0xc81105c263441708c910,0x44063c811018b2044043,0x58f2044132c81104c320,0xc81108cb2044231c8110,0x44362c8110d0f2044263,0x5c34244170cc91014b30,0xd4d10ccb5044032d4110,0x482730c1204c03048272,0x5c031481310c520d4430,0x101209cc31482320c520,0x48331101205c44048031,0x5c04348232105205c041,0x141209c8434817110d20,0x48273151208c85148331,0x10d30480414c1200c530,0x4c12018d30480514c120,0x480744c1201c93048071,0xcc530483304c1201d930,0x4c120d4530483414c120,0x480434c520dc53048363,0x1d931480744c52015131,0x8c120dc131483314c520,0x481738c1201463048031,0xd4630483318c120cc230,0x8c5205c231480438c520,0x480438c920cc63148173,0x10730482768c9209c632,0xcc520d473048341cc120,0x48270cc5205c33148054,0x9d73148274cc5209cb31,0xcc520d0f3148276cc520,0x48131d01200c74048353],#[0x5c34148331d01209cb40,0xd05208cb4148173d0520,0x48171d0d20d8f4148273,0x10f6048674d8d20cc750,0x853010c214c04208530,0x4c06408530188214c054,0x9c8214c264085305c021,0x8530d4c214c34208530,0x4c0620c530148314c362,0x84404c1710c930d8831,0x10530188414c17110130,0x4c353109309cc424c132,0x84504c27210d305c443,0x14530d04504c32114130,0x4c04314530108514c032,0xd08514c3321453018851,0x14930188524c04314930,0x4c171149305c0524c064,0xcc8614c042185309d052,0x18930150624c04318930,0x4c171189305c0624c064,0x5c4644c170191309c462,0x88530189314c37048530,0x4c06288530152214c043,0xc6304c0218c130d4e21,0x8c130106304c0328c130,0x4c0648c13018a304c051,0xcc2304c3218c1309ca30,0x98530d06304c3318c130,0x4c170c85301d3214c042,0x18b314c052cc53008730,0xcc5309cb314c064cc530],#[0x4c362cc530d4b314c276,0x9db324c064cc930d9331,0xd0130087404c364cc930,0x4c062d0130187404c052,0x10f414c341d01309cf40,0xd05304cb414c062d0530,0x4c342d05309cb414c262,0x9db424c170d0930d8b41,0xd4530d0b504c353d0930,0x4c462d49309cb514c062,0x5c0524c67210d315c043,0x1813110c604c67215131,0x4c443189319c8604c462,0x10f604c570cc9315c062,0xd81311cb604c462d8131,0x4cb62d8131d0b604c732,0x10c604c971151325c443,0x10e105c03284043d8132,0x84130482105c05284170,0x98930842634821058d20,0xc421058e628413258610,0x88163c821010f1084032,0xc72088031982205c031,0xc82204c32088043c8220,0x88351c8220d032088331,0xc74088176cc62015331,0x10e219cf4188331d0220,0x88570152215c05388570,0xd4d60884535822110d60,0x863010c218c04398221,0x8c17008630150218c053,0xd0c218c265086305d821],#[0xc630148318c35308630,0x8c2620c6305c0318c162,0x8c8418c1701063014841,0x10e30d4c428c35310630,0x8c042146300c8518c176,0xcc8518c1761463010c51,0x14a3010c528c34214630,0x8c353486309d0528c170,0x14e218c16358a3014961,0x986309d2328c35388630,0x8c353c863058e618c043,0x58b308c051cc23008730,0xcc63098b308c261cc230,0x8c262cc63058b318c052,0x8cb418c043d06309cb31,0xd0630d0b418c262d0630,0x8c353d0a3058f428c353,0x9d3538c272d463008750,0x10e315c0428c5700ca31,0x8c97110e329c8548c672,0x992608c843982325c454,0x831010c20c417099232,0xc41300c31098c20c4173,0x4c832c40740cb105c430,0xcb105d832c41700cb10,0xc41711031010c40c4353,0x5c443c417010f1098840,0x10f109c843c417610f10,0xc4172143100c850c4343,0x4c120c4043483105d850,0x483108c920c413148310,0xc434348310cc120c4262],#[0x1c930c40434c3100c930,0x4c3109d130c40744c310,0xc43724c310d0930c4332,0xd0931c43324c7101c931,0x88310dc963c40434cb10,0xc42628c31010e30c4043,0x5da32c40548cb1010e32,0x98b1010e62c42748cb10,0xc4130c831010f20c4343,0xd0f20c4232c83104cb20,0xcc310dcf20c4353c8310,0xc4232d031098b30c4074,0x9cf42c4343d03109cb40,0xd4f100cb50c4272d0f10,0xc8274d4f109cb53c4176,0x15031c81710c3204c030,0xc7204c831c81310c720,0xc83530c7208c831c8170,0x5c041c81711032010c40,0x10f205c443c817010f20,0xc833114320d0c43c8264,0x10530c80314c32098c51,0x4c3201c530c80514c320,0xc82634c3201d130c8072,0xdc930c83714c320cc530,0x4cb2015131c80434c720,0xc80518c3200c630c8043,0x98e31c80548c72010e31,0xcc7201d331c8054cc720,0xc8272cc7205c331c8132,0x4c740c8353cc7209d331,0xd4f209cf41c8043d0720],#[0xc8570193215c043c8674,0x19021cc17098f2110d60,0x1433008450cc17008730,0xcc34114330c8450cc041,0x14b40cc170193305c052,0xd433008750cc272d0730,0xcc321d433088750cc121,0x5cc52cc57014b319cb51,0x583315c064cc67215331,0xcc6725833198960cc452,0x5c262cc6729833198a60,0x583329cb53cc67098b31,0xd0343087405c021d0353,0xdc131d00724c7405c031,0x10f415cf41d0272cc740,0xd057314b415c052d0570,0x9c232d04438cb4198c52,0xd0b415c342d057098f41,0xd0a63d4b415cf52d0673,0x5c221d417098f42d4d60,0xd0b509cf41d4273c8750,0x9de6f8fe2f5c264d4e73,0xab6aba7e8f9fe7e9f67b,0xb7edeafebeaf6bbadeaf,0xbeaf9bdef6bbeedbaae7,0xc9f1fc6f0fbfafdbf2fb,0xcf73bceb37cbf2ecb72b,0xdbf6ddaf67d7f5dcff3e,0xdfb7ddf37bdeb79ddf76,0xebfadeafa7e7f9ee7797,0xef7bceefbaedfb6ed7b3,0xfdbf4fcfeefafe7f3fbe],#[0x63a1de8e73273fcfebf9,0x776070a908f4a51d05e4,0x30c1d23e106b47bb0d4a,0x5ccd318c0953016323c6,0xbb3d2dc724ba44c669b7,0x801b55ac22a1b2091390,0xec7f279d9a890319a63d,0xe8a60b9d503d811355c,0x922c173a1620c673946,0x49b198e948aa1c8ad56b,0x4e97210e3234110c5c8,0xce35b3b34ee2324748b0,0x40fd6509cfb006fc718,0x34598e878bf1953022c3,0x6c91a08805a3b1e21d87,0x5322c04d2fd65081d904,0xeeb78332c3d0e75c7d8d,0xfc8f0c1391a193f0ec3a,0xb076007998c00a01d800,0xe5ab1bf8b7832c8e504a,0xe1d8765578ea74bf5940,0x4fb011391a1987a610b3,0x7a1e5a23432fcb66459,0x5a4115c1f83115fcca07,0x1f808d2a8ca69c358c3a,0xc0e492c75ccdd5a4182c,0x7602328fb19e70c438a1,0xf3ac081c8793d69056c0,0x482ad96ae642ad18cdb5,0x8c472ad9d93b2341896b,0x191c2a6319c64580136a,0x3a53eb786151c4e551c3],#[0x317acfb00d291a18d167,0xeca62f215cd8eb989157,0x15c5ab9cc8b682b056c,0x235925821216cea2407e,0x33564ae4521161855863,0x335ad5da668632316b46,0x88d7621aca6683588f30,0x32c708238d6b00214998,0x6183d0e7107602493ec0,0xbdada11fd67ba1e26683,0x3e3fc054e45867e4cd06,0x5eb4814b4e504a907602,0xda48c870976003a5a42b,0xe116183e5abb41ab4764,0x4762a3f92463385d906f,0x846864bd6cece0389d2a,0xc3b00f887a1967663234,0x2d9d9476ab9d72d4655c,0xec39a444871348b0e40,0x4580b54e5048e11602c2,0x98c8df07e0ed38e319d6,0xf6027492311c71f7618d,0x2c0214b4741288b0d2b1,0xa863996ee45a2d9d9742,0xcec9f2da11ee97b91067,0x988f03ec0410b6844dd6,0xc3d18cd80961d0e4784b,0x7628c3b0029ad9d94a0e,0xe40211602af3342340b7,0x18f89ab28744586a7ab0,0x3d62b573b103b00dd91a,0x652c3b00e1b310ed70ec],#[0x840ad98c545bbb4c0b67,0xd923ec01ad0c646d168e,0x3fe47860496ec6ab8761,0x10a5ae441c958c175abb,0xe8ad5da0f5b3b1f6b780,0x9c7e32a4ecf74a5a6300,0x8eb77328c3b005ac3a09,0x608f0e231f6020723c01,0xa2da09015b3b29e1d878,0x339431ceb4870ed68ec9,0xae971919af06b2b85caa,0x6b70271ad992b0234322,0x4ca004622c18981d80aa,0x5a4241c1d8760969031c,0xb6867396ce8252d9d9b8,0x6ee642ad20a0a8fb19be,0xd9d982923230325860ad,0xabb0830e81629c705412,0x681828fb010ead208015,0xb0ec02d9d94e5bbb154b,0x20a7a0fc02dc1d876783,0xc0cd91e640c48d0825ad,0x7664d6b0e232d5d8143d,0xc812da191f8642b14b6,0xdfc86c0b1445802788d,0xdbcb6648e9aae75e3b1,0x69964ec6818761d6f5a4,0x67e11210285a3a91a458,0x18492c0a8d0d630e56ae,0x8271c731343b0f1c87e0,0x3d96aed05c31917d5b40,0x553a5ca475b3b54a4686],#[0x3792311d2798097d6ee6,0xb2e272a20fb002bade01,0x156eec1db3191a97642b,0x54189085bc0110b4867,0xe5bc1490b7878ac8d0e4,0x71c633cc8d0ca02d20a0,0x9d908b291a193e0ec3ad,0xad5d9ed234333c1e87a3,0x5b321a8e9715be488670,0x1d80b888b0c07ba204d9,0x8b0d5007a1e8f5bb1a40,0x7602b89341090b48104c,0xbc18ec7d806c599044a8,0x47413ce70d512d5d8006,0xb015eb81d29271a1a9ab,0x1d0462ec05507d808b43,0xc353ab4829356cecd5c3,0x853ea1f00c507601c622,0xe4419f602095a41c9ab4,0xa885a42b541e8793a58,0x90fe4580b148f0021382,0x333c3b01172d21641923,0x903ad85a423432bab77,0x2c60f43cc0d783ac03f0,0xb4c1f808d48d0cc9ad99,0x69d6aecbd91a1c860ec3,0xca0761d618742b150c64,0x5777422cb1f7311a4886,0xe61d806a43b0ebc4cdd8,0x8d6aed08550c5eb5abb0,0xc2d191cd9239150b4740,0x75b3a09eb5767f9690b6],#[0x70c646e1c08695ada153,0x25b02249c60544743980,0xad1d44f5a3a3231f634c,0x8f3989047802b43b0e9d,0xb582405fcca13ad5da00,0xfb01002d9d8149299118,0x32058e5b42c14cc82b48,0x2c03a6b481229c105414,0xd805bc8b01619f601532,0xf0d092d5da4227429c47,0xdccc45b3a06ecc743d96,0xc353245869d25b064c2d,0x855408b0cc9b310c9122,0xc449cb6044d76429b0b4,0x96c78e42062b6857b96c,0x231ace74b5c9d0b472d9,0x2839d908fe0761e01863,0x2a31ca08eb22c34ccb58,0x6de92b1370b58104e4d0,0x22f27723b96cec9d2da0,0xb643b013dbb211175b43,0x214b1c4a55abb3f4cd83,0x4b5a411fab7733396d00,0x5ccd80a4d6eec2bad5da,0x348d0e232d10dcd5bc11,0x3ad58c915b41002b662b,0x46ab9d74b7803156cc96,0x8b5768121cc81dc3990a,0xe1d02c72d211fd0ec3af,0x2d1d4a28742091246340,0x5ab187ab57610d6d0505,0x46863aab10271ada052d],#[0x6cc405ad1d0859232206,0xd205af70413e6b685b79,0x24114a46865596b0d582,0x5761d03f06fa11a19c12,0xb0ec54c601ca92322c6b,0x61eb35bc33f8e881aae1,0xc0234eb819021ec8d607,0x864203b0f1111602dc3e,0xca112da15af5b325907a,0x2ad92c1314d48360dfa,0x2ae6e0821043b003a916,0x4b2d6aed028761df96b3,0x46c9f6021c5a32560cc8,0xd4822c30e0ee847f1db0,0x81268451a1b082447d8,0x7f218c8b899a0d935b3a,0xc07602255bc15b0ec85,0x920ec01901d809dd6aed,0x42b4747443f016dad60c,0xd03b006d07602c99c21b,0xb916055e76bb43a46864,0xe5bc3876b47512c8b00f,0x2cf646908b0c183a2167,0x96d0a7b9161a4e234189,0x3be0d655a321a81d8765,0x8fb19dc7d803ac8d0626,0x45868421904c73be19fc,0xdb06fe07602a15bbb428,0xda14335ac35564587135,0x2c3530b6731288b0d2aa,0xf6340a630025addcca12,0xaecfdd5190d36ab9d771],#[0x2126777a1acb0e741256,0x415a44682209d90567ad,0x8162a38c67687a1c2067,0xed63f1952f22c34ff0f,0x1c86aa319a6b57685c3b,0x2388b5760c03b0134116,0x311a4ce45213a169b923,0xd40ada103323432390f4,0xac5a41b9b3180740e70,0x9ecb4829216905718760,0x2f5d0c2d21f601108e31,0x31c9194e15a3914eb787,0xd0ec04f01d8068c3b0f,0x66b6826a96ac6091161a,0x208d0c8891a1c8e0ec04,0xc2f1d6535abb4232d811,0x3ab98838e272531af063,0xeb7826a9ace6d9cb9c88,0xdd6e47ab520d655a4258,0x47dd8655bc082645867e,0x5bc141cfd650848b0cf8,0xb5760d83b0f06c718d2a,0x68e81213216236a39c9e,0x32058a5b42d5d1c634a1,0x2c391d1c7308e1e8734c,0x483ad638c682c31916c2,0xd0e242d58edf0ec030ad,0x9d9805b42b553c430b48,0xc344c1d809f03d0e97ad,0x809c9690afec3601642e,0xd55c7dcc4a5b3a89e1d,0x1a5b8fb1a8e1d80b856f]]
private def groupPage1 := limbs80 #[#[0x3deb6740c56aec1a916,0x48903b00bb2da0ad83ec,0x8c51ca092f92c14d2b67,0x1905a421f4ef4345e1ce,0x761d80b396903053319,0x1208d0c9111a10268642,0x501161a1d22c34b44684,0xda3f431cad7733883f00,0x151c540c43f0144bb209,0x3d6aec08ad216de86c03,0x891e00bd5b3b2f670829,0x922c342ab5767e59d084,0xab663244bb01131f201b,0x5dd06b2c9d89ba5a4239,0x389c94b5ac1964b78333,0xec3d08458311d6ce814,0xec847948d0ca507e01d5,0x3b01682d9d8f82ec3074,0x761e9c0ec3ad32662230,0xe32a7cb77312c8d0cbf8,0xf437f0fb010a2d208887,0xd04c73f61448aba0bd2e,0x6064e713aa9a1e8796e1,0x4115e7d86876a886699e,0x8737e4d04c511a197b22,0xd16addccd05b3b1a21e,0xd9625abb54cd483ac08b,0x2a8b5762c16d0b6c2d9,0x3205c0e497c9d8d0c3fc,0x67391e1c4d5b3b2a2b57,0xe7587b234f253223688c,0x9c31c731188b0d3cad58],#[0x11a3cc7362dd8e8793a1,0x2c2d5da8423432f44587,0xf75b4182d53624223eec,0xece0724c16b056c2d214,0xb88b00742d9d83522c03,0x3b89d14d0ec017f1c633,0xc5bc30ad0f630e9690a4,0x46863c4fb00703ba15f,0x968ea2411e00a599bb0c,0x2da196567a1d961d8748,0x5ac3cd30c436e16d0907,0x45869bd6ac65d2d20052,0x6d05072d60eac5b3a896,0xd5cc483ec04311d73379,0x94127c1d802648d0827a,0x78021cfb01160761e2c3,0xb0c0491a190b0ec0112b,0x191896bb99bf4f6338c8,0x411c445868456aec0943,0x73134fb007691a193539,0xb911601cc5a429fb1f,0xc9bd5abb4181d80b80f9,0xb27eb481b8c8b0624b89,0x44dd6aec17876015a5b3,0x82691600805b42b7eb48,0x9595ab115cee837f21ce,0x9e21d804488d0cd949a1,0x6896904d53ba09da8e31,0x9391a193197c09626683,0xe96bc1c632c821788d0c,0x46fd650ec3b0f0055105,0x2cf70327badc5285a391],#[0xfad58cbe5a3a91845801,0xb5a419f4fe650ec8d0c6,0x246865896906591161a6,0x88d0e26ada15fd93b19c,0xada048a5e3a9c6458011,0xaa18838b773306a8c471,0xb4854dd6900212d206b6,0x6d0e23116042539411be,0xde1cb922c34e0b773205,0x2c34c04c8580aa0c4732,0xc633a9dccafe11618382,0x8c8ca2da05af0fc05a91,0x1c9267f428901f805d64,0x42c14b67669a18c8cb38,0x86769dea6fe4718cf25a,0xe895ade19f396c0130b7,0x15022c304eb6766f5c0,0x1406b48599d6aed51ade,0x364e6300232d5da2c5b3,0x8e6b82091f0ec0554658,0x18870413e4b6766b16d0,0x2cab46472d68e4554319,0x6a96ceca94798e91762a,0x692da05bf0f439dcb582,0xbc5a42d5d1f7312daae6,0xcb1e63a40fb008697601,0x196d035b2d9d9487641a,0x3addcc485bc00a444871,0xc5b41964b4845416f0e0,0x845865896f0649389c9a,0x618c8c62dd0ec77629bf,0x9f600fb3ec0454b5837f],#[0xec017645868683d0f4a,0xb5760b88d0ca4cb58c03,0x3ac61c47dd857934323c,0x81ca9177411b2b5804de,0x2b183a1f80759f8ca9d3,0xc64692610c71ad61c509,0xb0e2705e1e8003432329,0xdd8692442c3e05873700,0xc0004a37618d16ec192c,0x73375b1048d8e600b33a,0xf4d285ce8d663a24aa1,0x91735a3b26a9e766b425,0x849c7477d2ce838b01,0x5450370f3ec210c9803c,0xaaa8161cc24ebb11e886,0x4d93ac03c4ab8022d08c,0xd6458037152c45d3920,0x21953004590602ca59c1,0x14aa9d94572b8a260587,0xa4663a52ae172ac912ca,0xa44180b161086482a5c8,0x5d44e61432606589221c,0xe8fa086f463a264e5314,0xb1ac343a0687389f0ca9,0x63186aa136ec3528e046,0x220c684b95c63c50b9c7,0xa25942a56bb120a3761a,0x4e32353046458d08ca90,0x5873483300d4ac5da20,0xd0ee99f6013a1dc34da,0x8dcc4b82c13140a84964,0x4c0ac0a2732f5410435a],#[0x27356d10caac2be007e3,0x6ec332b2087e02c3beaa,0x61a6e20c0586967326d4,0x4237ea9622dc0d0ee90e,0x761907504fb8e618194e,0xf1b289cc081d431cf1b,0x1ecc4f320d832866dc0b,0xa2847538538e831026,0x495cbb034581a1c8e03c,0x76fba209701b43d28cc7,0xde00b43cbc308441d6cc,0xa16b37615e08c8e20121,0xb78090cae2a2148b8e31,0xf32219541803232e9c84,0x9a803a1de07861500b0e,0xa5088226d28e8308c618,0xbc790c8b285cc484fc35,0xb83e0c7603c357e79819,0xc59bb0b8a16330083011,0x8b4743280b0e422ce19f,0x53ae2c72a98e4c4f320a,0xa2215cd04c05b4058703,0x57bb0f90961268330112,0xf1650c46700c7bc99431,0x630d148521ce44232a56,0x7990564f4212480654b0,0x942090ef8236504ca2ea,0x5630b5370835a32106b1,0x30c0d9060236144131f2,0x6064a86322dab37619c7,0xc013e318025c3b0e7c16,0x821fa15084c23dd85d03],#[0x8210ea095f7441d0caf,0xcd7b443abbc0f831e13d,0x32a806872ad46e682355,0x2a18630d133d19543224,0xcd8275c98f663a51cd88,0x98aaba08340a849c53ce,0x1564180752870871c1a0,0x6d8730cf528dd85b2140,0xad0c211e108c3a30c273,0x65443abbaa37616510ca,0x369c7428c090ce3b420d,0x1d46c66c8361d9a80323,0x74458c1b8621c8a07802,0x33ec056e5c8441483004,0x66d8079c0b0c06271918,0x95102458f21c0550408d,0x8261c8f4e3a03ee372a5,0x3c380e3d8678d18e894,0x5873e40f0029289cc3b,0x988743271d0aa3ec19ca,0xca19bc32c1ac49e7435d,0xeb287c0687760710c830,0x232a1c0f003ba75dacc7,0x10435a8dd865543914ce,0x1d273573147a058684d6,0xbb442078732550c4872d,0x8034539096c0ae098f58,0xe4a385ca894e424147d,0x88513981441807e11f,0x834af761f4c300cb01e,0x31186b0d0f2e1d650aa2,0xe4a0161df803c33e6a37],#[0x8645bb0211473014070,0x89c6464180c8da9060,0x4a4b3033b0c2121b95bb,0x848c2098e5abb4050074,0x7e60b9c860786848750c,0x88438029608c8ca2b214,0x180b0f6e81e00c56421c,0xc311d12b603a0b841803,0x34e3a1dc3a865a0730c0,0x8aa8522c1d0cdaab5849,0xe708713a7dda9345328a,0x2b21c5e2ec05ac05868b,0x51bb0b49074188750cb0,0xaa732e162ed0f8761dc0,0x8300e4a75d8443ec01f0,0x72124f09c39784280200,0x34388cfd6503d20e82f9,0x3878fc730cf401a1c9e0,0x6ec2c10600803cc0ccc1,0x2106b19422cc17874594,0xbb0ba88654e4c300cca8,0x743bc830025aaa048b51,0xea76311d2974c420d703,0x1df759bb0c007867f110,0x9808418011946e671016,0x60b00b0e0aa2dd83ca43,0xc0126dd85d7e32a90398,0x573ec02041b8744c7b0,0x5803e871b970ea731860,0x6606d0e779f602bb0ec0,0xee0f6066a20c01990064,0x5f663a52cb386768d904],#[0x9406864cd98e89785a1e,0x4d66ec2c86e19fc20c03,0x88161e3b30c00b49e86a,0xf08c3d061b878f140c67,0xa9f769600b0e2810601c,0x158e42f2cdd85b4232a9,0xfe042844b284a418014,0x20c03a42d8025c730cf6,0x886547c4d0a24082158f,0x42e67cac2046b214011c,0x36041e02c39988965089,0x7432e6e1725e4fb0147b,0x8479162c6fe289ccb90,0xb00e4221d61656b092c3,0x195574f3246007872d83,0xc03a00687218730d28a2,0x6551d40c68009a166120,0xc8c0a79d1ca2cc0888fc,0x1d23762940c0786afa08,0x3ae896509a08c8b5046,0x7940070d68abdd87b20c,0xeeb9b208e351bb0ae148,0x421803a528c843a180b0,0x9ba428021910ea712259,0x63d10ca9e1e606541342,0x7fbd1951645328423082,0x2436c03d0a86243c6b0e,0xc4a376170090ca101a19,0xe9c2e55a281cc230ec3c,0xa01e19db214008caf761,0xd02432400786159e2ca1,0x439860ac0b0c03271919],#[0x918e87a2bdda5d623a52,0x331d25c02c3432f8654b,0x4432a96ae629100b0e23,0xce81a4d3cecd755208e3,0x83003940dd129a0421c6,0x36069302c39860587318,0x9bb0b40d87658810052b,0xc764e138ec96229d4d25,0x2e66934e0d654ec3526a,0xc31064000fa41c000014,0xeb348ab248841d85910,0x420840064d6e5413544,0x55b4c9083c0d12ac821a,0xc3b08000825e26f9a962,0xd41480f835cbb2808418,0x1af042001c136797d59,0xe48e10169080ad0421b0,0x24721a0684b078202d10,0xe400641ec0c490a24902,0x54491182625886054100,0x4231181f11f802200921,0xc5d109bd0c22c1a4322,0x3058282441c1261785f0,0x38212f04071475081b31,0xe83b060930b8344892a3,0x84a09c800100fc081d0a,0x48a1e8240a4b0150510,0xf8411245d0200b088242,0x3217c6491e31770cb1c,0x88e37f044a48a9226f91,0xef0308d2ca083007fe22,0x917c4c2256011095984f],#[0xabc93dd605006606fd81,0xc0c23067f191977e5400,0x76faed8c00bd56166007,0x2027e3c80cdbf03fb164,0xa479019eb8418c23fd83,0x6cd6d113f961e42906f,0x65007a1829c104200670,0x14257e41cc0662f06f52,0xb1ec14183dc5142001cf,0x326de72951a3fb012799,0x1002f660e5ee541b361d,0x14267ea3c4033009ec82,0x8b7a89bf0cf4265002df,0x9c24c66e2d8a84]]
def g63D7 := groupedPages #[groupPage0,groupPage1]
def g63H7 := limbs80 #[#[0x86bc11048823300f1205,0x8000800f7df86bc77df,0xf37f7807fb7ff8b040c0,0x1a00b991000000800006,0x57558a7819090006e043,0x1158142dfcc7694cca00]]
private def groupPage2 := limbs80 #[#[0x1481010c10108100c810,0x4c010480104401014c10,0x980108c81058c104c810,0xcc810cc010c801098810,0xd4010d0c10d0810d0010,0x104200c420d4c10d4810,0x18c20150201442010c20,0x584204c4204c02048020,0x98820984208c42058c20,0xcc020c80209902098c20,0xd0c20d0420d0020cc420,0x10821d4c20d4420d4020,0x580211502114c2110c21,0x98c21988219802158c21,0x1043008430d4c21d0c21,0x15030148301443010830,0x4c4304c0304843019030,0x8843058830584304c830,0x980308c8308c4308c030,0xc8430990309883098430,0xd0830d0430d0030cc030,0xd4830d4430d4030d0c30,0x150311483110831d4c30,0x8c831580314c8314c431,0xd0c31d08319883198031,0x1903215032d4c31d4831,0x9803258432580324c832,0x8440d4c32d0c3299032,0x1444010c400c8400c440,0x4c8404c44014c4014840,0x8c440884405884058440,0xcc440c84409884098440],#[0xd4440d4040d0040cc840,0x148410c841d4c40d4840,0x58c41580414c84114c41,0x98c4198841980418c841,0x14c42d4c41d4841cc841,0x9804258c425844258042,0x5844358043d4c4298c42,0x98843984439804358843,0x8450d4c43d0c4399443,0x10850104500c8500c450,0x4c8504c4504845010c50,0x8845058c505885058450,0x99050988508c8508c450,0xd0450cc850cc450c8450,0x10c51108510c851d0850,0x8c85158c51580514c851,0xcc85198c519885198051,0x5805210c52d0c51d0851,0x98c529805258c5258452,0x5845358053d0c5299052,0x58454580549905398853,0x98c54988549805458c54,0x101100c9100c11008110,0x149101411010d1010910,0x18d10189101511014d10,0x4c5104c1104811019110,0x881108411058d104c910,0x989108c9108c5108c110,0xcc110c81109911098d10,0xd0d10d0910d0110cc910,0xd8910d4d10d4910d4110,0x101200c5200c120d8d10],#[0x145201412010d2010520,0x4c120191201512014d20,0x8c9208c5208c1204c520,0xd0520d0120cc520cc120,0xd4d20d4520d4120d0d20,0x14d2110d21d8d20d8520,0xd4d211912118d2115121,0xc53008530d8d21d8121,0x1093010530101300c930,0x14930145301413010d30,0x18930185301513014d30,0x4c9304c5304853019130,0x8c130885305893058530,0x98930985308c9308c530,0xcc530cc130c853099130,0xd0930d0530d0130cc930,0xd4930d4530d4130d0d30,0xd9130d8930d8530d4d30,0x1493110d31109310c931,0x19131189311813115131,0xcc531991318c9314c931,0xd4d31d4931d0931cc931,0x1513210d32d8931d8131,0xd4d32d0d321913218132,0x10e100ca10d8532d8132,0x48210192101521014a10,0x58a10586104ca104c210,0x9921098a108ca1058e10,0xcca10cc210c8210c4210,0xd4a10d4210d0e10d0a10,0x10e20106200c620d4e10,0x4c2201522014e2014620],#[0x8c62058e20586204c620,0xcc220c82209922098220,0xd0e20d0620d0220cc620,0x10e2110a21d4e20d4620,0x58e21582211522114e21,0xd4e21d0e2198e2198221,0x106300ca300c63008630,0x14a301463010e3010a30,0x48630192301523014e30,0x58a30586304ca304c630,0x8ca308c6308863058e30,0xc863098a309863098230,0xd0230cca30cc630cc230,0xd4230d0e30d0a30d0630,0xca31d4e30d4a30d4630,0x14e3114a3110e3110a31,0x8ca31582314ca3115231,0xcca31cc63198a3198231,0xd4e31d4a31d0e31d0a31,0x58232192321523210e32,0x99232986329823258632,0x8310d4e32d0e32cca32,0x10b10103100cb100c310,0x14f1014b101431010f10,0x4c7104c3104831015310,0x8c3108831058f104cb10,0xcc310c831098b108cb10,0xd0f10d0b10d0310ccb10,0xc320d4f10d4b10d4310,0x10f2010720103200c720,0x1532014f201472014320,0x4cb204c7204c32019320],#[0x8c7208c32058f2058720,0x9932098f20987208cb20,0xd0720d0320cc720cc320,0xd4f20d4720d4320d0f20,0x1532114f2110f21d8f20,0x58f21583211932118f21,0xd0f219932198f2198321,0x1033008730d8f21d4f21,0x147301433010b3010730,0x48730193301533014b30,0x8c73088730587304c730,0xd0330c87309973098730,0xd4330d0f30d0b30d0730,0x10b31d4f30d4b30d4730,0x4cb31193311533114b31,0x983318cb3158b3158331,0xd0b31997319933198b31,0x5833215332d4f31d4b31,0xd4f32d0f329933258732,0x143400cb400c74008740,0x4c74014f4014b4014740,0x8874058b40587404cb40,0x98f4098b408cb408c740,0xccb40cc740c874099740,0xd4b40d4740d0f40d0740,0x14b4110f410cb41d4f40,0x58f41583414cb4114f41,0x98f4198b41983418cb41,0xd4f41d4b41d0b41ccb41,0x58f42587425834214f42,0x14f43d4f4298f4298342,0x98b439834358b4358743],#[0x107500cb500c75008750,0x4c7504875010f5010b50,0x8875058f50587504cb50,0xc8750993508cb508c750,0xd0b50d0750ccb50cc750,0x10f5110b510cb51d0f50,0x8cb5158f51583514cb51,0x9935198f5198b5198351,0x10f52d0f51d0b51ccb51,0x9835258f525875258352,0x58353d0f529935298f52,0xe6f2f9935398b5358753,0xdeef377b7d7e7f3e9ece,0xddedf5fadd3e7eff7ebe,0xf6f9fbfdde7efeff7dbd,0xd85cffffbfbfcfdfebef,0x7168801d16c41612043d,0x9d13808723a495c42f0d,0xd7159801d0e913761080,0x2dd86840431e009d2100,0x3d631c81dd8423d63998,0x55d82c446451859d8f4,0x91770a6855d8b4157696,0x8a9c91615733bd34c86,0x362d7176145845573431,0x41c75ce6015708e855cc,0x8e31770320e594244863,0x67dc55c09f157087459d,0xd85f157687c5dce16157,0x709c455d97315765ec55,0x9d9393a6508059d9201d,0x5769785dccc722734f45],#[0x55d9dd15734e14584421,0x15762ec59d8ee386543c,0x5dc0d3792036055c1d3,0xc287241c55d98d17700d,0x6455d8021c7441c59d90,0x81676410c5d9b015767,0x4ec55c26e157609c51d9,0xe21157658c55da8d4464,0x44cce594221570a7485c,0xcd1c516160c55ce8e446,0x7644079d203793061855,0x5da9715737a455c0d616,0xa756c855d83944644ac5,0x55c279177334c55ce071,0x53731e055d86516764f0,0xd45847b15768a859d93f,0xc1576884a1c98015761b,0x345dc26b15761cd15cd2,0x232d717cd41c87815760,0x67c55daa1157665c55da,0x6a177660055d8b11576,0x64c55da50177026c5dc,0xd47844644e451d8e8177,0x7387855c14e16763d941,0x58c811676550e1950121,0xa6507c59d91316763dd1,0x55c0671c745b05dce993,0x157663c8dcda3227348c,0x11d8d4751631e055d988,0x8157073855d990157033,0x7055d80e45714b055d83,0x1c15767d0e195097b300],#[0x43459d95a5161145358c,0x168177033ca5c9dd3865,0x31e059d905177334871d,0xce1515765e0c5c164177,0x737f139d90b4e621a455,0x5d9a95376171498c7815,0x67649055c2ad1c743985,0x55da57157666c59d8ec1,0x157687885ce237b40618,0x85dd8421e743658dd042,0xd17703a45dc0be157054,0x9455d9911570851298df,0x2215709bc55d82815768,0xa313d4c464863398a5ca,0xda21770a9855d8541576,0x389455d8c553531e055c,0x1c157628c55c0d0217,0x732f455d9e01576735ed,0xdce6a157693855d9fb17,0x67648c89cd4b15767c85,0x55d8194d621545dc0961,0x187559c55cdce5776108,0x115c12c157683c59d94b,0x351612085dd9e4157659,0x14b5c5da15766f119904,0x981773250b5c5ef53431,0xf911913a45631c855c0,0x913157684455da391576,0x211455da4c2a72364a9c,0x94201576700a5ca4f523,0x7037455cd661576230e5,0x5d88515765d0c5c1ba32],#[0x5761453188e515760c85,0xa9c904157667855d81a1,0x177035071d1fd1576090,0xc5dce7644431e055c240,0xf1d712845dc0952d7187,0x5455d97515767a055d83,0x5b1576675258deb15708,0x825458449516301469d6,0x9df1c74108c9c0da1576,0xab8c5c16351611cc55d,0x9508157684c55da8b157,0x717d545846f1576890e1,0x5d8b5167640485ce2f2d,0xa7243455d9db157660c5,0x55d98c157616875c2662,0x16763ac51d9073170374,0x455da8115769e855d9b8,0x54d622dc55c22615767e,0x4455d849157606204c00,0xc2f7170455d82d1576a,0x9fc59d9124963314e195,0x4215766fc5dd9a31570,0x615455d830157677191d,0xcd81396507d458c7c157,0x76128c5c1ab73401085d,0x5daa015762a055d81015,0x5767d855d9ee157680c5,0x5dcc33157694885ce331,0x1576a15258cbb1676374,0xc61d5a750521153989c1,0x715767b059d8d815766b,0x1455da3816764ed218cf],#[0x4515765b4c5c19b15736,0x2b4add9ff177085d4150,0xd0c446448144c45e4c43,0x33c4c1c12f3a651452d8,0x950e157600455d82e157,0x703252dd8421676434e1,0x5d9b53170661218cee17,0x35311539885115766605,0x59d9091576a4055d8585,0x1576a013588b51570864,0x459d95515761ec55d8bf,0x4596304455da2e15761d,0x4d9d1ab58521816dcc9,0x18631395a10db435714,0x7a96dccd235704e56d8d,0xc0d35707dd61d0c98531,0x3814d5cdf936764ed658,0xc9e18a30394d5c28b357,0x430a961ccc75b63435f8,0x10cca58633ad610d2b68,0xb712b961cc3335703d96,0x658c223570640d5c1f45,0x59630a8d5cc325963041,0xcd5c19f77324b8d5c06f,0x85a64080d5ce5035737e,0xce11c9e35a62274ddc10,0x3887314216d895858740,0x41165d8285a64744d5c2,0xd6e58742f8d5c1563570,0x3744d5c0f45863389610,0xc24d357055561d0ae584,0x704fd61d0345a62268d5],#[0x5c5105876421a1913b35,0x9630c0d5ce5159630b4d,0x6992405963060d9d93c5,0x58722f8d5c1545b633c9,0xd610cc059632e4d5c14e,0x53570428d9d1ba377141,0x916d8ce25b710816dc9e,0x3f5865539658c2835705,0x21e14c4e535709016992,0x99d5961268d5c0df5a63,0x6061658ded357381cd5d,0x49b03570879f9c90d597,0x43179658cbb893039621,0x5d8305963050d5c1bb5b,0x570675610d5c34722696,0x18c4f284721721dc9e33,0x58624b961d0205b730ce,0x965c515357049cd5c14b,0x258540821188ed35700e,0x89698c035963319698c2,0xb73573360d5c24c58433,0x890d5c1997c62395658c,0x5095862534d5c2113570,0x44cd5d9995863394d5c,0xce3858437a4d9d1b1357,0x644ccddc1fe5a63394d5,0x58cba5b6343969d90d58,0x47226d658c0358751a56,0xd5cdd75843538d5d9983,0x5843651618cd835737d4,0xd61c9587e32434d5c163,0xd35700f961912b596226],#[0xa4d5c0dd5a74454ddc12,0x1d58540256d8cfb5b531,0x6c0d5c070357092cd1d0,0xc1f585217969809a8821,0x256161914d5b63395658,0x505e5a730ccd5c282586,0x632d56d8d0f5b430cd61,0x9d0335a32228d5c1d959,0xb7331cd9cd05367467d6,0x6d4c5e3570529d149b05,0x5864389610c337d7142d,0xdf8c8e535737821d88ed,0x158430d561c89a357667,0x48d5ce4c3670288d5c28,0x9859630a561d05e5b536,0x7f639c4188c54478d5c1,0xf28c6449e3d493e8f71,0x239a31493d8f4141e34c,0xc6028c624fa310ce58c6,0x624ee34c1ea8c4336230,0x10dd78f307aa31493e8f,0xf3141e31c5fd8e626663,0x35c10d8c4307e31893b8,0x8f7239a310d278c547a2,0x630c5fd8f6239a315132,0x58f417f631c8e68d3039,0x963151988f437aa3cc0e,0xea8e3266e310c228c633,0x6238c9ed8c417f6310d,0x2098f317f63d8ce58d71,0x33963d893e8c4249a35c,0x40f28e3182a3151fe8f4],#[0x537aa39d52c8c7407e3d,0x1d8e68e6267a30c9e78f,0xf414ce39d1e88c547f63,0x3d4d1e8c6539a3d0d328,0x8c5482239d5888c526c6,0xe3d89428f4278a310de8,0x68c214963d41ea8e6480,0x263194eb8c54436310d4,0x368c633ae39d9398e648,0x87a39c89a8c326b63109,0xd328e758263085418f53,0x54e631491f8e656be310,0xca3c8c4379e3086228e6,0x3267a3105338f5343639,0x10d438c653ca31d5a68c,0xc218ce31d1e28e6548e3,0x310d078f5141e35899e8,0x8e658aa30c50e8f424aa,0xa3194e88f436623d4c3a,0xa8c6250a3d01e28c533c,0x323d493b8c317d630853,0xaf8c436b639d12b8f514,0x6230c4298c434ae3d4d,0xdd98c52116398dfe8d76,0x11563148ec8f536723d4,0x50288f5180a35c0188c2,0x4367a31912a8e7196631,0x150e58c4366230c9dd8c,0xf216de314dea8c517f63,0x39c1398c2110a35ca3c8,0x8c614f63146088c6449a,0x23d44fd8c747f631911e],#[0x98c327c23151468f537d,0x663d4ce58f214ce31450,0xf88c514f63149e78e707,0x4f63190e58d7076630c5,0x92c8f433fa30c9e28c21,0x26e235c0008f424da39c,0x493b8e7443630c60d8e6,0x503963145f38e7077231,0x991fe8c6436239c4698f,0xe3143a3d48e68c5441e3,0x3149ad8f3267a39953f8,0x8e6566231512b8e740a2,0xe3d49998c324aa3d4e2a,0x28c544323151888f523c,0x723194ee8d7038a310de,0x298d637d230c9268d707,0x69a3d49e28f323e23cc4,0x1fe8d7000a3589b88c52,0x347a39c0308c5482631d,0xcc1f8f5311e39d50d8f4,0x653963d49eb8c653b231,0xd89268f5366238853a8c,0xf534e63188ec8c316263,0x310d2a8e750a231c89a8,0x8f538263148e68d764e6,0x63d4d238f2149635c12b,0xd8c53396310d268f517f,0x2a3194d88c4347a310df,0xd8c6451a3085b78c318,0xa23cc9e28d707de3d0d,0xde48c52666318cd88e64,0x24b23c86228c523ce310],#[0x46088c5141e35c14e8d7,0x4278a3109418c644ca3d,0xd45098c214ce3c85418c,0xc5278a3991f48e624fa3,0x3c86338e6587a31484c8,0x8d624fa3191438c711a6,0xa31450c8e654fa318926,0x18c7441e310a338c5478,0xc23190eb8f324aa3d49b,0xeb8c523663150f28c216,0x7ce31c49a8d700c23149,0x12b8c5180a358e098f51,0x380e31092a8f3249a319,0xc9dc8d704e639d1888e6,0x533ca39c49d8c654e635,0x190f28e727723c84558f,0xc624f639c49a8f707423,0x39c8028c6548e3085218,0x8e748263151ea8c7269a,0xe3149d88f3162635cce2,0xf8c4367e314d988e711a,0x64d5c0b94e622d4d5cd0,0x6836702e5658dde15704,0x2cd6dc85e3a65928d5c2,0xcf836729f96191581573,0x5f0e194fe35707c9618,0xc465963a4169916d317,0x6329cd5c50c17739553d,0x5d9b034744b4d9c8ec59,0x9611addd04424e732c92,0x79d13459768f879d22c5,0x31705116d0d2b5b728f0],#[0x939d04d5963311658d9e,0x88f534fcd5c02a5a6207,0x8cd9cdf85843860d5c18,0xd58528fcd5c59d5a632,0x1a4d1d01e584112cd5c6,0x4ce367255e31891f5961,0x376d119135347482561c,0xcc7367090235c52b596,0x623b161d15836720556d,0x5c2415963660d1cdea5a,0x5724b1f8ca0b15767205,0x6149c44571139f5c9f74,0x44645091d913736721c1,0xcd5c0bb58763996d0a3c,0x45a62074d9c94d496303,0x80c5c17936726e0d9c94,0x4c35700c1f9c9f735714,0x4bd6d444b5a643614d0c,0x8b0367277e3cc60a3370,0x44ca11485c5854795698,0x8cc35a62a04d5c017446,0x7346969d23c466403d25,0xd8cf7466551cd1d1e215,0xb604a869d61917709d92,0x3cc4ff8b30788ddc1e45,0x76630a0d5c533177307e,0x69d4905976621d0c9aa,0x568644f855c1fc34729f,0xf14984824664128d9c24,0x3859632a485cd235a758,0x788d9c92235705f085ce,0xc0d1573300d5c2234a63]]
private def groupPage3 := limbs80 #[#[0x13fa3d4d9b5b43030d1c,0xc1335a622d4d9d13b536,0x70509610ea75862399cc,0x98a3047644c0d5c0dc35,0x66415869d4d84c624c96,0x658c16686448135883b4,0x3a651496988701e7460d,0x561d9fe4a633163d8922,0xe36709b16585cf5b422f,0x479d22b4d6215965d8e,0x635a630f519904715733,0x62a3d0de1446450cd9c9,0x4183674760d5c0f93673,0xa7d6151cf35705e4d5c,0xd1a85862488d5c209157,0x536a4d5c52552321e161,0xd0dd45b329a969d0bd8f,0xc623d8d5c1cd47644c5b,0xd1c0bc36724b0d5ccde4,0x8e32488d9ce052273504,0xd48c84c5b53251698c3a,0x2584161161d2165a6209,0xcd5d86f15768d075c07,0x5e36709c23d4a3046640,0xce31d10835717456d08,0xaa02d711891191345875,0x14f549947c4b633b9398,0xc51536728d96dc49a6b4,0x7169e3d094159637e569,0x9ccb83672384b9c52137,0x570568d5c132347401cd,0xd9c2125854609d10dab3],#[0x35717356991c317732b0,0xd9c9b4157665961ccd2,0x68f303c945847a584356,0xda2589b0367279df0c42,0x5f59769b169d45e4e622,0x91459d91f36723756990,0xcc73370690d5c1911576,0x305d61c68a367381d610,0x8e91587108161d0ce8d6,0x633b969923c467213965,0x9c219367479919905777,0xe6214a2142085963a3cd,0x5dc08b84721e0d5c1f94,0x5b435b8d9d8ee6b437b4,0xd614a6a8f41074d9ccfe,0x28f41431610d8474614c,0x9855c1c537733c969904,0x1835703b969d49a36724,0x78d5d9b45a627897594,0x44235708d1698ceb4963,0x54b0d9c93b59636cdd10,0xc24e58623cd698df9687,0x70221658c7a3670910d5,0x1488a4b6337455c0c135,0xb52560d9c9b685317b56,0xd9cdee3a65150d9ce935,0x5a62691698a4d8e70824,0x51990491a7571dad911f,0x85963945dd44425b7180,0xe8d5d99b157693e24c1d,0xc535709e9f188f235717,0x8bd398a435874794d5c0],#[0xfd15736516d4e758c52,0x6289a9c52c7c547fc79d,0xc22e367382d64ca3c157,0x7474615c5ef58624d0d5,0x1903a584303210c97036,0x67016d4d084521734796,0x55c06158624ce21853a3,0x8f428ccbdc40836744c8,0x1a19146386544161d49a,0x636724cd658e84535213,0x34d1d1393474765f8c9f,0x9b2a7257cd5cceb58525,0xe0b9c61f8b5082055da,0x20c1a7547d61912a3570,0x33f965c85e35733e4d5c,0xc03d3570a114d48784b6,0x214cc55c0d7357076cd5,0x9d1ea367375df4c8f274,0xd62124d5c0393670870d,0x61524749631dd1d91464,0x3571808d5c1c034724b9,0xd658e6758633c9d14533,0x95a645fcddc4205a6479,0x753d0c4d357083cb5c5c,0xff5963211a191221c740,0x10855ce6e1776950b5c4,0xde159322f56991e85961,0x3800d5c10558624ee310,0xc49a3673045a5c92c377,0x4141d68c878367449961,0x9888937718056dc4698c,0x674824c9c1341e741253],#[0xd5c20e35708a85dc2a53,0x5a628f055d97e3570978,0x4b9c4fd6864509199015,0x251610f4d1d0005a6527,0x60d5c2393571755f1893,0x99367288c55cd0658646,0x98d5c04f2d7176d61d2,0x44a84523b621453a7f41,0x50791dd16c58516b0e99,0xd1c5a751a4d9d1aa3a6,0x6538d698cf215702396d,0x991c136702316985d158,0xa627acd5c1f158216b11,0x20853a74436a855d9295,0x7f327a2310d088f3140a,0x145843a7c4381135ccb2,0x15a62148d5c5f837702f,0xb4d9d1eb3570525658d7,0x863a650762cc1fd35737,0x24455ce9d5864479658e,0x29b3672160ddcdea5a63,0x40ccd1d1fd5a647f4d9c,0xccff6864490d5c52b585,0x539a91991bf34763a0d5,0x1950068644c9698c7a5b,0xf4109d6194e23674664e,0x5dc27c35733ecd5c1e88,0x2d7170d64c85e3672770,0xb9c5f55853858e99447,0xe4e742c8d1cca9167653,0x296989b03570a4cd5c1e,0x9035709413189556b418],#[0x108d5c5051a755e4d9c0,0x5b04963a516d4c8a6074,0x50edd191335b5391dd14,0xc1435a626b53988a93a6,0x7048e1148456f3270cd5,0x9d9207c6250dfd091e35,0x5701b0c5c1357753664d,0xf8c90344644f160c8c01,0x2972378d9c94c3673059,0x161d1828f5288169c49a,0x3674764d9cde05d650a,0x8055da1c36764e62885b,0x43347409d4d85343670a,0x7dcd1ca283a65189a191,0x5b05b63058d5ccf88d71,0x251569d2ab6b64481d08,0x8cb53672780d5c5d35b6,0x635dd6d0c4d357015925,0x9c9294a631dd69c8bd5a,0x573238d9c06615764fcd,0x39883b35702dd64c9a61,0x1770922318cf28f42499,0x8d5c54458711a56991d7,0x95b2112cd5c5b9357379,0x1231050c357097455cea,0x3b5a325153988565a632,0x4b0d9cd008f31445d4c9,0x6b3670281698df16b71,0x3244d9c8025873859699,0xc0a6597191d65889a596,0x74758d9c9244a632a8d5,0x5c5dc2d717acd5ce1836],#[0x87110a3d0e095a769b0b,0x2d49b07c7241c59d8d98,0x5a641a56dc68a37714be,0x9698e8b3670994d9d127,0x5367328d61c88a367236,0xae2d41f34e6211d44c84,0xbe59322b1d1c84259635,0x8256d4c3353614016dc8,0x88d5074114d9c9e87e32,0x270d5cdf17d327a9614,0xd828466413ccdc076347,0x642c4d5c2653473a18d5,0x1c05d36747e561ca8a5a,0x674000d9c2385a6359cd,0xd9d120466404ce994273,0x46754b0e99449596305c,0x4d9d1e72a72444bdc4bc,0xf5872338d5c5b6367408,0x95a5903e35713fcd9ccf,0x784435c0d9d0164e626,0x9d4a9c8de1a7575da1d1,0xd007f6249d44c87c1773,0x449d65d88c5854454d5c,0x8db45a73649658dee446,0x7477cd9cd7c584347165,0x5c0c2297675161484b36,0xa757d1ad0e0a5a637845,0xd9c91f2a724316188d91,0x1a753f45dc1d05a658f0,0x4e1950a207368d69823c,0x91573234d5c2648b3042,0xd9d1f0357098965da5],#[0xa59637d0d9cc2d1a752,0x762144425a620ecd9c8,0x2355b630a965c6755a64,0x23796989a650531f0d5c,0xc87836720f5f14586367,0x7028d65c46915765954c,0x5849d35707b0d5c24635,0x96369d6190ee8c528c16,0xd9ce803570a0cd9ccc45,0x357084cd5c2914b63440,0x4d5c58d873180d69949a,0x24c62541614d925a732f,0x96dca8a36708f855daa,0xb367227610c9e388211,0x95d61ccbd68644ada992,0xd265a62760d9d1423573,0x47d1f1093235716ac85c,0x8e85586248455d9268c5,0x307cd1990074e6212525,0x9ca257c4109855d9a189,0x9632e1f5ca091576768d,0x65d9e85a63064d5c0745,0x5b7385915848144644b5,0xd5c0ba36744ccc5c122,0x8157648cd5c29251621f,0x9d19903e3670a5e15c43,0xfd5963000d5cddd8c410,0x2616109585a644aca9c8,0x1aa367344475c6611a75,0x305cd9c94a3773394c5c,0xe4c1570aa231953f367,0x7234a310e036b64519ad],#[0x988163570849adc12c5b,0x6764fcd5c23135704f96,0x6d49c234764e455d9223,0x2a727763d4d3e8c62489,0xa35c26c1776174d5c523,0x93570885658dea36726a,0x95218cfa44645156d0c6,0x1e47644acd5cdf036721,0xa016d8533847478cc5c1,0x5f38f633c8d1c8433570,0x488d1d12e5042130d5c,0x8d8658525616dd9fd357,0x62a40d1d020772110935,0x10e6d74314cd6188f55a,0xd622a855da1b8d728fd1,0xd5c0655b722b8e9945d4,0x1576975698dd77f322fc,0x8c9c10358653f139c44d,0x234709a469d5737c4309,0x78d9cdf97e32438d5c1d,0x2b3573971158e6636744,0x561658e50596328cd5c4,0x14250521e0d5c5275b32,0x37e16585678f41495ad9,0xda365a6439969887b357,0x627b5658e4c466410455,0x5c0df157032cd9d1d75a,0x67297a3d4da336747a0c,0x55ce1836737c541484c3,0x367379964c8455a62880,0x93988aa30704b9258dfd,0x5357024c79d1984c5411],#[0xa055da7b327037ca5c92,0x1e157303165c89a34725,0x664d9d20836727656992,0xc4466403969956e8d62,0x2495658e0b5a62124d5c,0xc0bf2d71241ad91322a7,0x7325c09d04015768c8d5,0x9c4b25a621fd11914435,0x27047855c11a2d717a93,0x61515885317d1658c743,0x58644d8c9c1445a646b5,0xd9d8ec844301455d829,0x63576678a9c90e1a753d,0x296dc88a3570478d5c60,0x13670219a1913c35706,0x51485cd2937701752d8d,0xd7c7c51071a191395862,0x151869d64d58643b1658,0xc60f36730ca3d8945357,0x726a0d9d00a4a63020d5,0x5c2305054130d5c1185b,0x776018a5c8d959730ccd,0x69c85e347307cd5c0861,0x5a728f0d5c52435705e9,0x634c60a8f31808d9c9dd,0xb36744d5d148428c536a,0x49698c145a611acd9cdf,0xe6347294e3d05418c521,0x8f1614c941576680d1c8,0x2955872024d9c0c45b43,0x24b0ddc41d5a620a8d9c,0x944f596366cd5c295687],#[0x611a51991bb6b6450ce9,0xcc42659633c960c8bd5a,0x773785a10d3e4664161f,0xddd8285a6239a35c60c3,0x3570730d9d02e3673050,0x485cd4b36746bcd5c117,0x87d327e56d8c17446449,0x8d61c85e5a622a9658db,0x225a632bcd9c94268644,0x3f9698a58357090a3d06,0x5338c5288169c89a7e32,0x48a39c52b5a635b9dd0,0xc2735e650a9498878327,0x64036398c2a1573390d5,0x5c55f6b43771698c0646,0x96382161913759636a4d,0xf1892736748385dd81d4,0x15739e224c1673672495,0x8e994297463398d5c0a0,0x13570384d9ccb4367290,0x29add107157325d398aa,0x975b432f5a191274b634,0x7816991985a63590d5c2,0x18f8d702314584212d71,0x47e9ad913b3a650f0d5c,0xd52c5976824a9ca22367,0x702e9698a5e36744ada9,0xdc44236740c4d5ce6736,0xe622e16589a6844378dd,0xd9c2395b63060d5c06e4,0x38653fc55da645b61424,0xd6dc89a8571765119141],#[0xc59631f5698c7474324c,0x4cd5c20b35703814d4c4,0xde5a64a00b5c1c65963a,0x7dcd5c57b5b60519698d,0x20d8e728fd65c49a8e71,0x30092d8cfa5a628fcd9d,0xce4f5a328f0d5c0c3596,0x747f96989993773250d5,0x14e756a647de3d063334,0xb43859d1485035707d96,0x658c8769714b160ca995,0x5a65900d1ca3c37709a5,0x9658db936727be3d4d32,0xb35716d63151081c7478,0xa5a1912d875278d69c6a,0x8958643616d0c2368644,0x4ad41cc783673a3cd1c0,0x12e3570668d9ccaf6b64,0x3a71258c085a645a1119,0xd5ec1c7401d69d675584,0x73a956990f27e323c869,0x1d93e1570aa5f1099817,0x470a61198e603570964d,0xd5c6074664154d5cd0a3,0x8f433c8d9ca4d5961744,0x5258cbc45304b1dd05b0,0xc4863440d5c511686451,0x4d5d9b836724f940c87,0xce466402168c8bd3a651,0x49c55ce5a36728d16dc8,0xd098f7141c55d9321576,0x37d879d1d85a32954d5c],#[0x57f3570148d9ca22596,0x72788d5c1bd5a6311e3d,0x9cd025976770a5c9d834,0x531784a9c99733704b8d,0x658e804764514d9c8128,0x7c3161a3dc9e23573835,0x4d1d1eb3570a8da1d0e6,0xf5a741791990045b7202,0x24e9941658722f5f8c90,0x245b63828d5c05959636,0x7f56d0e998f31438e994,0x318c433ad658e0e5961,0x35f21149703672500d9c,0x849d15767bc69d5545a6,0x7503cd5d9cc4d7113569,0xd8c28466470cd5c1011a,0x673a2d658c0615733556,0x64ca6a3670844d9c8f33,0x5b43388d5c60887614e5,0xd5c5f7367649055c195,0xa1a754f23989b1347479,0xc8d5c064357078164c88,0x6a5a631f5658df77f623,0x40d658a3c5a32179614e,0xe0b4664109610cbd3573,0x47416149c28c520ecd5c,0xe0b526115455da94347,0x7201d3588435a6205da1,0x58ca436732996989b434,0xb426d14585aa4a63a516,0x39884134747a9698c576,0x3474039358842357398d],#[0x469d4d918753956d4a3c,0x9367216d31504d8c6251,0x68d5cd918e21505f4c9d,0xd684653b564c12b35737,0xa7d69c675587125055cc,0xcb2157309631099e1573,0x447169d5928c4188855c,0xd17f36700e561d0bd585,0x32699d105335b637d071,0x9c81b357077d61c5825a,0x875470d5c14c317040c2,0x69c6475a76060d5c0925,0x8e6305d610e166b644e5,0xd69963f5b73a65ad913c,0xe8f317d53988ab367238,0x8565ccbd36728c231953,0xb234740a0d9c2132d714,0x788d5c05f8e326d0d5c5,0x628852120d5c1965a64,0x1619610c2352651e0d5c,0xc10d5a648f911912a7f4,0x744bd6d8d0336735e4d5,0x584b08c314263d058734,0x8540d0d9c0c637760614,0x618d025b634a94984425,0x8b624e965ca3c4a63079,0x4c5c0fe36733f4d5c1b1,0x858647f56d0d9235704a,0xec55d9be5b437a4d5d81,0xb677514ccd5c01834708,0x3991991ca8c433c8c5c1,0xe835b4390059d8fd4b63],#[0x34cd698ddd307094cd9c,0xc41c3473801658d79744,0x71569614c335e65061f0,0x5843b35714a4bdc5e235,0xa32a64d9d1347e327a94,0x61d48a537678c5dd8445,0x8c418ccd5c103357065d,0x5d58c283570678e9942a,0xd1576778d9d11f58644d,0xa93d4c4d6821204d9c9a,0x565a6201ddd8ce649632,0x2b0ddc0893570288d9c8,0xe095a639c9ad0df75a32,0x480d6d485e52321f1658,0xe992273498d9c0628c5,0x73a91a8ca605b436b961,0x1d16c4464498d5c2aa17,0x963788ddc29858645391,0xd9c8db2a7293ce994224,0x53721e23d4db5516111c,0xe28853a8e7043479d10a,0x25873471ad9127157023,0xccd5cc646874788d5c27,0x8f85611bc55da598e218,0x479fdc9fd3674789658d,0x82121734f4d5cd057f62,0x6bd11952c177601d698,0x5b05963764e99463357,0x327d1618cf93571411d1,0x9d10b586344561892a7d,0xb53470d9cd0f5b43539f,0x65857f8f624a8d9c9cb5],#[0x177364911911e3673769,0xcd5c028582112cd9c8d9,0x357376df9c50b35766b,0x9961893a1776a1d610d6,0xfb32704d4d5c59a8c437,0x7c169904a3672479618c,0x935585112c69d5d85a63,0x30c169849a35703f9bcc,0xc9eb337069631057f6b4,0x3079e3d060877516c0d9,0x5da2215766f5658ca58b,0x87517855d939873278c5,0x81913315768316988285,0x157338961c8d2357150d,0x515c84e3570440d9cded,0x88d30784d5c225367016,0x991990391576a4d6d095,0xb3672938a9c95e87713,0x914d1c9a635733896d8e,0x912347648d658c0f3672,0x57852d8cf346640f5f8c,0xc4d23473019ad912d187,0x76521610d9222734a561,0x58d7751615f1218d0a16,0x67648cd9cc221a7538d6,0xc5c16236726ea2d493a3,0x15767d4d9c99b4d620f4,0x8d5c26c36737c16990bf,0xa596330c79d14d6a640f,0x156188ec535211519903,0xa41e747ccd5c1b835709,0x785658d9c5e650a13588],#[0x1463a6510e39c60c3473,0x25a1f8c9008c72788d9d,0x880e58654adf5883e5a6,0x71484a9c90369704b169,0xd487c8d324f85dd9fe35,0x7314ccd5d82a7c4342d4,0x69899b35709d21109e37,0x5963628d5c0194e62155,0x4d9c8522a727613989e1,0xb1e746a965d9d958741a,0xbce994423571500e9942,0xa34e625d161c8ae4c624,0xa90d1d2081773a2479d0,0xd9f35701c561921e5b43,0x439879d0218b3041d658,0xc8f51875018b9d8ed6b7,0x624ddfd041c5963004d9,0x5c4c536727c0d9cd7a4f,0x4644bcd5c5022d713f4b,0xd1c4423770a194d084c4,0x596359e1149e35a32115,0xe11d0058b721093988a4,0x75874024d5cdee3a6517,0x861cc5fe6b64514e1950,0x1a36730a991913a8f307,0x9c919c92c35700c855c2,0x52c6b416ccd5c1fb3573,0x59f1058674624ccd5c,0xdae357031855d9f8357,0x63a05f4ca0b8c4161d61,0x9d1f22e713fcddc23b59,0x4644a1f4c8b92e717ccd]]
private def groupPage4 := limbs80 #[#[0x6150693570588d5ce0e4,0x15731f5658c735b732f5,0x4bdc5e12d710e211484c,0xa7f516185dcc955a656b,0x68c5c1348d626c56991e,0x5847746a055d88231703,0x23cc5f84e6210d6dc9,0xc80347026cd5c07f4664,0x6638d9c9da596368d258,0xc4b259631bd6cc8bd4d7,0x437f8d9d2035a6408935,0x151e358428f0d5c5fb8c,0x67477479d2808a2110a1,0xd1c8427451108d5c5353,0x36747d0d9c99e5b43184,0xcd9d8eb4664110d5c031,0x62d717b855c0d13a6505,0xe9f10d864e62020d5c11,0x5f68644fd3188f435707,0x9c055ccca5a625c965d8,0xde63672761a1912a3570,0x1aac89cd1e58712b9698,0xc58b35700b621893a597,0x6051d614a3c3570a58d5,0x84428a616c1a10dda47,0x570024d9d0153670195d,0xd9ce0e36740a160ca6a1,0x2d7172cd9d1448e709b0,0xd9d1ec5a62290d9d92a,0x3466471d4d85265a6336,0x78d9c9b13570244cdc25,0xec36728b4d9d19e15764],#[0x6be1d49c635701ccd5cc,0xc75a6279dfcc9d23474,0x514e31c5072d717c161d,0xd8ee3674088d9c9343a6,0x767dce99418596329969,0x58c285a626a944c87859,0x361478d9d12536737d92,0xd9c9215963770d5c5d65,0x4e6210969887658422f4,0x8d5c15b357074cd5c0da,0x91a7597d69889b8d3248,0xa0d9c268513213069d59,0x85b637d93988b758546,0x73c85cd415a626c63106,0x44e5a6210dadc92c5a71,0x4498d1c9a41e7447919c,0x8caf5a6173c69d4fe686,0x62479dc853350531e165,0x58e9236764f9698c3e7c,0x57023161523c5843a916,0xd5c21c7c727f4d5c07e3,0x367090855d99c59739d4,0x62d48424d62145618d03,0xe15730d61cc50a6b410a,0xf919909a68644796d8cf,0x42357156d658ca832703,0x3f5a1d1fd35732e96988,0x29b5a739d5698c733571,0x27b56d8cf98f31834d5c,0x90e62a7241561085e367,0x516c05dc2ac59637c561,0xd4c9a4b63380ddc25388],#[0x6702fd39885335709456,0xd9d1fd6b74789d144503,0x36744f0ddc57f5a635c4,0xd698c6f5b624c0d5c5f5,0x25963a091991be446551,0x9611853936737d5d1d04,0xfd59635e8d5c2a136729,0x4793989697f3161a24c0,0xd327f4266231892a5a64,0x591ca5c1d44a632f2314,0x8df71e70284d5c60c5a7,0x65085698e50377089d6d,0x5c29e347407d698e673a,0x8748f14588787c410705,0xddc09c58624f455d9b35,0x59636322cc202446447c,0x5fd441c5871804d5cdf6,0x335706f0d9cd91774366,0x44d5c0a55a6473c69d5f,0x4c63644cd3d0cad52611,0x26565d8025854805698e,0x81c3570336310d0a3570,0x698855c0f03a650e82dd,0xd1392d717b1658c79157,0x4373d658de17421140d9,0x9d44e2a72405698a5358,0x67030d698dea46640291,0x69929b35702a0d9c2733,0x44644d96188db53321f1,0x4d5c237357020c55d9cc,0x93570728d5cc91367406,0x8455cc235a72aacd1ca2],#[0x5c5b722f5610a993670a,0xa10b5ccea74524ce1d48,0xc1c586337cd9ce0d3673,0x20f4d9cddb5b767f9f10,0xca1f5972aadf4c9f64e6,0x526d08dcc41157053cd9,0xd4e3c5b4391d3d0cb28c,0x6724f4d5c2525a646ad6,0xe994284d6309969d1cf3,0x7e620f96152168872108,0xcddc27c157057469d416,0x277216c0d5ccf2367340,0xf8d9c06e2d7054cd5cd0,0x1e3570910d9cddd2a723,0x115658d6e5a329a879d2,0xd7b8f42678d9c9c05042,0x24b12d8d072d717b5658,0xcd6f35716e8d9d1ad6a7,0x63a019d913a34747a055,0x98d6b58624d8d9c9785a,0x5765d911913735733116,0xd9c9bd5b6141cd5c5131,0x5873a6561915115703bc,0xc55cd1458526b161891f,0xd5a601a4ddc23d5963a8,0xf4d5c1c885313f8d9c99,0x167c437fcd5c09015765,0x838ddc5a588524ea3150,0x92b357046d658d647d32,0x864d5cde73570771358,0x8e0936747c4d1c23d357,0x72664d9d03952631f16d],#[0x8c9998772170d5c55e36,0x5705223d891f59321e1d,0xd5c2857e32828d9d20f3,0x1e73204e194fd5963064,0xddc27d3070a20d5d9b1,0xe3570a813588a68e7023,0x591191313570000d1d8e,0xb535708f961cc943670a,0x3b949847846654b0d5c0,0xd9250521f0d9c8d85a64,0x177d45847015704e165c,0x9444357080ddd85332d7,0x714fcd9d19a357016ce9,0xdc5fd5a6428cd5c24335,0x57056560c5841773800d,0x61d9076a749b0d9c8fa3,0x2d7176634c50e36728e5,0xd9c088377395965c8bd,0x48f31425f8c9d9367636,0x2d3988778471399a991b,0x1444644c16989da5b411,0x1fd1991cb17733211990,0x277177694c55d9b73672,0x229855cccc7c424785dc,0x4e1668644f5698c794e6,0x51120d5c0fa59633956d,0x5d83e8d218cd658d8888,0x6728bd6995ae7f31070d,0xd9cc1936702ecd9c2723,0x5a628bddd0d9a3570008,0xdad912a5963a0cd1d1e1,0x367450cd5ccdf68431b],#[0xf1a10df55b529a961516,0x8236746e169c46958758,0x66a20844858728f16dc5,0xf236700c055cc0b3576,0x64b431d8e73571731619,0x952b4e622bcd9c243177,0x640196991d23570a4169,0x10d4d1e742c0d1d1a646,0x9303acd9cdd85b522296,0x55d86d35710b9658e8b8,0x5b7347069d47068439b0,0xddc09b85313c8d9d1fe,0x43672219310cb2357391,0x24d1c876585464939884,0xb46a640a965c5cf7d328,0xaa2989b0585464cd5c0,0xdb43570291658e853776,0x59c1458d7035706d23d4,0xc56015709253588521a7,0x74748ddc0e858534716d,0x1d44559325a961893e36,0xb424f879d03a7c5442d4,0x55d9895372114d1d1a46,0x357071df8c9f458624c0,0xd6191073773858d5c19b,0x735737a965841d36732d,0x48cdc0ab6b64498d5c26,0xf4587279611cc0536702,0x315d18cee36723823d0d,0x9e236746616dc4943670,0x99d698c0d15735b96dd,0x945937766bcd9c237367],#[0x738693588b052621f0e9,0x5942a8452719add1fd15,0xa767dd658dad35704017,0x61c560177610d618cde5,0x5b71339658dec357167d,0x99dd0426b644796990ec,0x635714f0d9c0328e324f,0x10d9c0388472015658cb,0x72686447d69da095b416,0x66cddd9b41a75819658e,0x17b59632d0d5c10f8c52,0x32296dc4d23770740d5c,0xc5dc587464cd5c28f177,0x531f161c5a836728fe15,0x9c9125a6383560c95853,0x6640c455d942874278ca,0x69d06959636d4d9ce924,0x8c3141d69da597e72825,0x9a1c52c5b634013988b0,0x150321e055c11d36737a,0xb141c845357019855c16,0x405a760a055c03746714,0xa969889e8852108c5c1,0xcba59325161d48ed8d63,0x275cd9c05f2a72408d9c,0xc12635707bcd9c9f2367,0x6344961d4945b6337cd5,0x9ce713370a20d9d02d5b,0x5734452d8cda35714f47,0xa00005a750cc79d28c3,0x1e0ad008a6064a040802,0xd215cc13dc11a20f760d],#[0xc20081df51bf219e617,0xa02ac828912647242122,0xab35b932c7309d2eab2c,0xbb441741703e8c3bb138,0xa652ac4fac4ce349c546,0xa044005dc25b2a58a055,0x468f839cc32948a1943,0x108000785c567d8e57d4,0xc428f7350c22b0881a04,0xf08400769b76356b5051,0x750117400d52b8871904,0x20980089205795c36396,0xc56d22418d32b4811a44,0xd07c008da147d1d76d58,0x54dd183e8d12a4821a04,0x309000815e66ed985c15,0x55191437ccb2a48b1d04,0xf0b8008a5f6755af6356,0x952d27410e5310a61dc4,0x9098008e21d7c1cc6956,0x75392b41ce7314a91e84,0x70b000845ef74dae64d6,0x64c103394c62cc941a44,0x205800851eb731b05d95,0x8458f7348b123c761583,0x707000731b8659725353,0xb458f3344b427c791683,0xc03400795c369d885993,0xe44cf836cca2887e1682,0xf068007d5d06a5885792,0x8410ec314ab2507a1643,0x607000775b666d715352],#[0xc444f6394c62b4881984,0x30a000781b86817e58d3,0xc4a1103a4d62fc961c84,0xd074007c1d5699845813,0x7464f0324ad238791743,0xc0b4007b9bb65d7e5693,0x152d273dcdf2e89c1f05,0xf06c007cdda715b162d7,0x24d10f3ccd22607f17c3,0x507800811e26f1af6295,0xe52d293f4d72f8a31e04,0xd0bc0088202751ae6496,0x84d9173e0dd300911c84,0xd09400831e9701995ad5,0x7460f936cc02848316c3,0xd06000715aa6216352d3,0xe4b11239ccc2b48318c3,0x4040007b1d06a1905a54,0xd3ece33149f2206c14c3,0x20740073dae649604e92,0x35091b3e8da2b08a1a84,0x20f0007f9dc6cd905f56,0x46d19b5c54841ccd2907,0x10a400b1a9b9e64c8a1f,0xd6595d50521394b321c6,0xf0d000aa685976347f9c,0x36ed9959d2b3d4c62645,0xf0c400b62aa9b23884de,0x46796c4cd17360ae1d04,0x60a000ab678952297d5d,0x3645695010934cae1c45,0x60e800ac68694e1b775c],#[0xd5c94d4b0fe340a92245,0x80b0009c243889ec719a,0xb5c941444f0354b02145,0x90ac009b24484de97119,0xe635664e50e398c12406,0x70e400b3a9a97e2479db,0x67219c58937418e52806,0xe08800bb2c3a626a8de0,0xa5e96b5050434c9e1a44,0x30bc00a8a7392202741a,0x5725985792c3ccb82506,0x80bc00b5eaea02588adf,0x729a160157470dd2946,0x411000b62a19e64d855f,0x76f184525253d0bf2747,0xf0b400b4eaea0a5d885f,0x8635674e103364a61d44,0xf0a80099e4488df6765b,0x5dd4b484e5304971b44,0xf084009ba46871f5729a,0x35b135418e2308961d44,0x20e0f004213829df6c59,0x1043a00a00a1b048640e,0x82042a0870890301a0c,0xd11c1448090b68781c1e,0xc03600081ea13008a2b0,0xc4911a0a88028141c440,0x43e8843a110b84623045,0x410008061a1912c28441,0x58588c2786104490620,0x14a392e8a0f0c4050201,0x1b85132302e2514c2600],#[0x76250b89d201cc826044,0x396238cca6630a415458,0x32546d8b4b4542859876,0x87121217839e340911e2,0x5c221936b2501a90be3a,0xf119de7e1613cff3208b,0x51f94068122f2781c278,0x8fbd571db20346fe0284,0xea7fc4899f1db2033478,0x19572233918bc162018c,0x811993cbd713317b4e8,0x245d610da59641d947fb,0x7342d69041c3868196b2,0x7c3e9924157b57a30216,0xabf1c52cb2407ec380ca,0x459eb714a47cf8ec80c,0xc218e71f05bd2923fdf1,0x2c1ed4433870e1a0659a,0xe780b8a0903e37965923,0x8474fced5013387a263d,0x99a7718cf10238f8e921,0x8cbda88723c703f8a341,0xf93045d99f268ba73ba0,0x47d1f864515f3a1411e7,0xd1824dd99922fd75142,0x88e4949f3aae4334ff2a,0xa04b2a6b96483f911e,0xb0f2e48164d1bffd79d0,0x9bd4621232fcdcf1951c,0xa1411947cfc114be820c,0x5f2e189ca1c03a0661fa,0xd66b422af4a2df05c95],#[0x421238f6af50248a7d8a,0x970645e34ab18a38ff95,0x2247fe284c07eba917b0,0x7c41187bc42f551c67ad,0x87c0640f0f024d6cd35f,0xcec5584660bfd4c82397,0xef3c62e549344f0fc245,0xec380cb2865ec2461263,0xefea94029c134a3a4107,0x4ca7649f7fdc7d14dc49,0x42af3e108d7fcbb51853,0x4124788a948c217b5272,0xa2bfc8c80cdbffbf5164,0xcd1fe8a2654fe2321b99,0xdf9108bc5c949ffc8c80,0x18320bea70a12767a845,0xac96c4cd39ea269193d3,0x5add1016035cf81c48b5,0xccc411e78aeb1023f7f1,0x1ec8c1e531f16b519f63,0x461c3f59411d7f5c8916,0xa538f9a2c82258fabc42,0x32ad468a2a1d4798b964,0x4a4eca239bc48d5a70d1,0x93551d6413df8d48d90f,0xc86515f3488be8b7b8a0,0x768e80ca3d63488dfb79,0x92bc9b95a019d1e5041c,0x4840434fb3e208d18e01,0xf456ce083f5285161e88,0xcdd0849316d63234d565,0x6582884dfe1fe811a631],#[0xc0a0eb4e2311400286bd,0xbec5b92cce3fc86115df,0xc0990f06250eac0dd99b,0xc7bc8191b1e2cd2215b1,0xe0b08a5f90203287c098,0x8923fc13eaa9a096157f,0x46b108fb8a439ff04091,0x51fbc21180ef7b2d1d57,0xe41064d8d77104746982,0x6115bb579032d72e0648,0x59ac21efd7f3408c3fc8,0x3403307b34a0cba3f464,0x1af1124765c9a219a23d,0x6c720745cbe2205197a1,0x8848d97256823ae7f122,0x82c926602fc22b408578,0x510475fcaca0475ffda8,0x8b66235f8e041048dfa3,0xad7f41065aa65927fa68,0x50baf56484bc720e8424,0xb57d62a123dc85fe09d7,0xa0e0ff3922c703cb819,0x2e26bcc93c6a85047678,0x714c18f527c83ce74e03,0x9c18d79c1c68a3d3ec50,0xa8e6e0d51c4fc940d1cb,0x81fe4d262b36fd1a8823,0x103456b25d8067a8ac2c,0xf3191e3969193be3c26a,0xc1f065dbcaea465fa11,0x845b9ae12e89fc2691ca,0x3033abc2283ac310ff21],#[0x4507bc77c4811f3e95d4,0x999b0c98f7f553046578,0xc85296e9ea1948b2e5ec,0x42a406787a05077cfa42,0xa8a323edc2a8c23b7ff6,0x5c891f3931263063dfaf,0xf108c8e9041e58c63dfa,0x8dc0e8d4f160690a96ba,0x2ea460d3f28fc50133a8,0x9c8abede4459bf458a8f,0x734bf089b5da4a8cb1ef,0xe5c700c99f10dd907a08,0x838f8bcb0485f72302e8,0xac91c4fa5b523f61ed0c,0x5aea8623b5bc98e2fc8,0x68eec18d25f2e521c134,0xf55c76c80d15ab065a84,0x646a791428411fb1845e,0x8636b1cfc5bf811a6384,0xc7f6b9234fbe77142124,0x514afd84883e6bd01a30,0x9094ecc483c2877ff430,0x66c3be689866f03239c3,0xc2659e7f0245efc59a2,0xfac800100d497f0444c7,0x5aa7dc648ff45132e7d3,0xd02597df80c9caa68258,0x2dd47925238fefc1ea82,0xba53c4230f8f96028ed0,0xe8913606323265f144cb,0x3e07f091d6406950a327,0x2688efd8a0fb0e2146a3],#[0x5e4aaa49ae83c1059874,0x5f225859577e62a46dd2,0xa52b51a28ab83fce48d,0x48a9f6741148341ffd50,0xa0492a3e3a4b5244f8ac,0xd3091e38ae2651fdfe00,0xecd6561a07898c22a99f,0x8b8a45e0e6b9308a0df,0xfac81236e9d46461ee2b,0x920719adc5964a4d6c4b,0x11d3eb554d4cfbcd6d9b,0x66ce9ab6840cf31e048,0x8e7a08a16f0c75d6d2c,0x84f3e071228c6750a124,0xa3f91122a3e5483a3fb2,0x43041339034849e2df68,0x88a66de0462823dd9992,0xf50630e4c5283820e229,0xbb7706110a3dff6a2462,0xca1e45dd5133af9f20a2,0x7c6491523ca083ef0890,0x917d721846775a60cf6f,0xf2c635e33b8848f9c9a1,0x45dbff044de789c42470,0x2d79533932d9118f56f8,0x2f0be2257da18f359813,0xc6461cfa59411f63422,0xf8f6ee921128bae18e6c,0xc501348af9d0a08ed025,0x2dedc8e3c68c8b5f8ad2,0x19ab54c2c92078c191c6,0x9230fd215042417b9688],#[0x18888932bea31234dddf,0x5e221236f037c22ee2b8,0x455fcd9236612ed02661,0x889dfe644f9c98b2aa36,0x33b536e0cca3dc01e6e4,0xc0c28e40426961e62e9a,0xc97b5ea3960237262f18,0x589c769024894b69fa4f,0x2125427fe3579273604b,0x4e8df393361c72f40e98,0x26c4bc18d62478320496,0x803340ff9e22a220010,0xec2413a1cec9447f0875,0xd7125938f3165cbe7358,0x903f4ed4c209387c120,0xe4e85e0f661314f9117a,0x91feed8484d2de8099a2,0x82a13528a5f5f6f04a1a,0xd160dd7e11478286bde2,0x52f8db465762113444f6,0x33a620b07c7bfb583c82,0x90a3bea3012daa5db7fb,0x9473f818811c0ef55e20,0x903dc49360d3da59fdc1,0x40eb18ea6bd0254ffc87,0x649102b09316bfd804c2,0x360d15f4c908a0685fc6,0x368437510806a8a7b171,0x528ff6f33e32d910ba,0x3921be5602651d715559,0x206b39f50281286ab6ba,0xf03017c5b92588d6dc81]]
private def groupPage5 := limbs80 #[#[0x20923f550331a8e04264,0x7ede5ba4915e417eb3c,0x6e87f4191ba65c60864d,0xb5fc04b0ca9950e6f286,0x6af1e9c5874c284b3ceb,0xa94bcf170645a82008d0,0xf552838694bd7cfa8241,0x708cb1f68555642a5af5,0x19d7ef182411b52f7607,0x9798f6604cc1c72b478,0xfb19f009a16bdc6b9051,0x673240680fc5a9b066e6,0x9e28c5109a1ca3c9a309,0xd852597fc23319667c6a,0x2e74c4b2c09b3e6afd9a,0xc47204cfd861f520669f,0xf78222e4afdcb9309458,0x426573f799f50d6485fb,0xea11530258ff892109c9,0x2c40d1bf0b19c41227db,0x5dceab096154cafe36c3,0x3538eb90412e3d509927,0x8ef97b598cdde4904cb2,0x9c48c812975af5c5c44,0x563535e48f412ccf655f,0xe5664b86303337502253,0x685c1e784aafac82419a,0xc57b8224e9ff2611657c,0xb38af08e8f80e04c431,0x40fd3d690824b76e0e31,0x37302fd067db8e73b7c2,0x6b2a785864efd1c28330],#[0xa492e58e093e868c8ec9,0xc7f5d144091b8227e4f3,0x9cf82b10330e7fae0411,0x8c7958b1125624783204,0xf88d0c2547cd0cd033af,0x93a781a5e3d23eeb897,0x3a163066dfd6a491184c,0x500966188c6709032586,0x67220932b13c47a8e5ee,0x4948eb9d93a2884a03bd,0x901c2986225c689afc6,0xfc38a85d941337e62304,0x1330d40d614659da6afa,0x4c32a0973f3d3f316e04,0x3cf5a924461349abf7e9,0x2812845fbf90a881098,0x7cfb3ea1ac882f59ae35,0x49cfa4e2f76fe6312a64,0x678ed62c5640349e1cb6,0xc48d11e4ca6a76cc0a25,0x332a5fa333d2e2093b74,0xb19ae51925149c5ff7f2,0xbe2248e377d354864b9e,0x86cc2b0cac0cea34718,0xed15cbf5284972c35174,0xb5a7e53422ce9526f932,0x7a8746aeb3a04cd8e8c8,0x661910ad7e11d4493a09,0x1e0a1af782204269ffbb,0x7b3092b40db904f3d067,0x44a5a9fe3f048dbf82f0,0xb031da0040a127687aa0],#[0x45246338191124aeb22a,0x4a0c742c60ccbf7fa0c9,0x8d97eab4256ffb21484d,0x3b1465dceab0969a50fd,0x6a1cfa090851594d18de,0xa5078499fa808b102ec2,0x4edd0383a5f81a857afa,0x8be804cf58417aa02869,0x524afe057f2a220949f9,0x4aef97b1a0669abe7ad8,0x4fa78be691d66b8d40a0,0x9a4717c16818f2ba2224,0x4b4e599c60d11c7b2647,0x13863a098a659035d65d,0xf8475124812209eb51ab,0xc3338855181f1e4154c5,0x9d96537d3da327ec355a,0x97c2664d39a4099ae661,0x921f3af8912880d5541,0x99bd1cdfc08e20afe0aa,0xfe57632799c60d11e2ec,0x1277f3f2a5efba152534,0xfbb07841207ff210d9a,0x2e63f9004096bef0e8a3,0xf7e1234e306af8b81297,0x12d6c7d492100a3a6e03,0x7129c5d337f18eae08e8,0xc260e7527d1c90375e24,0xfde1a323c8f80352f515,0x835c19471f0378ea9489,0x66f8c63672fc488a0cdb,0x3dd075c23c9c4bde8c56],#[0xb2f581a638f1459542d1,0x53a64cfaf2832901ac28,0x632e8042d6818bc2a944,0x93f64570901c67588334,0x7d9e2b6aec9ba0eb8461,0x1966ab513832d5938507,0xa8d419f7030aba3367d9,0x700c6c9be32d9b47ec97,0xf1acb70905e104568b3d,0x6e03838a6ec6f853a325,0x5e9150accbb033ee111c,0x120385d3118cf17a13c4,0x32f84f165849190b8de6,0x78cbe8bda19aa12e5283,0x578dc9ad94843ce39b84,0xd27a46125c25756070d9,0x949c0c794b294035ae2c,0x5865caaf60655e3749ad,0xc2524297b5a1b4acf85e,0xb13aea611e7fc5f6e125,0xed24fc7114342621e0c9,0xb1f3165848ae2b222dac]]
def g63D8 := groupedPages #[groupPage2,groupPage3,groupPage4,groupPage5]
def g63H8 := limbs80 #[#[0x43819108003060010083,0x480000410200103000,0x60800f044848002,0xf80020410a140,0x100100024c303820434,0x30028080020028004444,0x2189810014002022c08,0xc30004242810008002,0xc0060050101040c4020,0x41030404180002801b02,0x30526000800005000083,0x4020000b02040051004,0x4004831c002810c04007,0x1200380000c105000400,0x20200001000408084,0x41041a00180142428b0,0x1061c0140e0008200,0x8820034802020828f040,0x821200009063c1950c24,0xe28080020898900782,0x20042822244000007878,0x2001080810000065000c,0x48086020541116040820,0xc48d062c80e00080012c,0x59602000000018099020,0x83040008410080000214,0x80c0c101000030400080,0x4141870208084001828,0x8438406081000004b02,0x10001540410112084820,0x828706040041e0008300,0xc0c000010614985166],#[0x880800186050410d3818,0x21808203020068500000,0x1a04188025051a0c1002,0xa041860414585042c18b,0x1405060058406404800,0x80008b4e0081f02,0x70312080011834480029,0x200100030a10085160c,0x3062c1800e6030006001,0x4705000c04009001020,0x1001008011010024400,0xb80d807000fa65fe040,0xe0000000010340780786,0xc507c07403800d53ffff,0xbf30010000440c231443,0x4de685003a01c007febf,0xf5fa7c00000000070008,0x224f543101e010001af,0x38f0062f400000005020,0xd421e27b81cc0f008000,0xf7f6bde700000000c1,0x430a4143e10f607c048,0x24007ffe6fff80008000,0x910f00841f708703e0,0x12003f7fe8ff408000,0x82a40a00fd44e82,0xc1000b000d6bedf1c000,0x281000408b087fa2b,0x17a0800580079dfd78b0,0xb0000000008209912404,0x48ce0420340029ee9bd,0xa7bc000000000900454a],#[0x210446d02101a003119f,0x9dfefc004000011150d2,0x482a3a81080d007fb,0xfbfbc29f000010006812,0xb87d2041e1f608806803,0x1dffffff38000000006,0x1031821821210c044038,0x1c00fdfff7bfc0000000,0x40168414490c48e0220,0x100e007bedf3d9e00000,0x654e01e8724c41,0x208c070039ffdffff000,0x2241000a44128,0x95204603801ab41d72e0,0x74000000000c49051226,0x14cae02301c00d2d7f8d,0xf8a0000000002832c081,0x8b65a01180e007ff3b,0xeda19000020000018d20,0x4fc74632ea08c07003f7,0xe3edbdef000042004000,0x258354a3498104603c01,0xc027af7fe000000020,0x126de13111c8c782501e,0xf00777ffb77a0000000,0x824908d8f8660130,0x9807803effddabf00000,0x8048a3480,0x504c03c01cf3900ff800,0x24084a602499b,0xe302601e00ffcfde6ac,0xfe000000000441009925],#[0x9387581300f006faedd5,0x76860000000084404000,0x514a13d209807804f7ff,0xf0fff78000000025c05b,0x126529fc04c03c0277,0x3ddd97bfc20008000108,0x20416c92c90482601e01,0x9fffd5fce00000000a,0xa8a4e0e096e87413011,0x8804ecfffff00000000,0x21018919cc145c098,0x4c0440267efdfdf80000,0x4011834050a66a3b0,0x60260220111f7ffbbc00,0x4040004135d2,0xe97413811009ffdea4fa,0x7b00000004520c08499b,0xce24e409c08804db9fff,0xd2378100000024701220,0x40275a8304e048027cfe,0xdfbfc640000000221201,0x5b0153d148027026013f,0x9ffcffffe00300000b1a,0x5c01cd9f4a8c1381300,0x4875e07fb000000048,0x8405c408c50656a0a00a,0x50026edf6dc58000001,0x62419222882be052,0x2a02a012ef5ff7700000,0x101042804d5461660,0x6c15015009fe281efe00,0x20420c0248a42b],#[0xa5ce0a80b004fb397bc8,0xbf8000000018713504d2,0x2982f505405c02bdfb7f,0xbe3b400000000001281a,0x6114f18202a02e01755b,0x81c353c0020000108140,0x18110a84c4c1501700b8,0x6d5d6ff952001000071d,0x80104005486360a80c00,0x3666f7f0a080000002,0x2800011aa8b2805806,0x3001bee2a3b98000000,0x20c40d035519c02d,0x1681800ce4d6cd9e0000,0x10ab2d18,0xa20b40c00654ca133700,0x100000000c6020025616,0x135f05a060036ee63963,0x93c000000012c00e902b,0x35a1b582d032019bdffe,0x9db3b000000008201480,0xae8ae2de81681900cb2b,0xf7858ff0000020084505,0x8c8857770e0b40d006f,0x379f5fecf0000010040a,0x23d1f112c139305c0680,0x601a37dbfffc00000000,0xa5a60241629d182e03,0x1b00da7f6f354000000,0xda00bb2eec017,0xb80d8060017f86f0000,0x470f60b50000c5a1776],#[0x856787f6c029f21002b,0x9984600c284201311ebc,0xea3976450518ace3b0e5,0x401046ba028e70c8303e,0xaa00000000080285905,0x2031f3217b8064c1a320,0x1995923c9a97b8726130,0x646470f7d56f7487a1f8,0x90524aa462019bb04015,0x80060a3b328fc7178003,0x5c2afc457c8490171707,0x408028624100e80e7e00,0x40379c2a70420056a28,0x8fdf207a00f80dc0a229,0xc8d64c01ca01ec731e61,0xe90f94051bd020184008,0x2d533157a16d7b40e215,0xe5123b2c558971515f6e,0x33e060c305203022fd72,0x751334c403f604073be0,0x80003ef75ad3209ae963,0x283410001a21c07c0037,0x819139c00148e022288,0xc1fd09c00e1800020610,0xc000c028004a8875303b,0xb017d0329036f34181e1,0x36b800e62e2e0c35e8bc,0x201d30611722a221,0x10f648463f1d61e722f0,0x366041c705eca80ef01,0x17768ab06c52b4805,0xd0011ea02f7c04980400],#[0x7c3b974b81af138b2c03,0x71488658506d461c7f41,0x1cb0cd0c48c86000b80e,0x2fc4e79acc6ac63a087,0x4f745bca5fec473f0340,0x83c07aa0ac9b0540b007,0x4a0a55bd33d830878c,0x5a024820061daabe1d0,0xd423b9511364b1451c46,0x57bc8569bdc4176e04a4,0x300c062cc18a002c8e12,0x3b079bb5146e4c0a908,0x3386321a20218aedc9a7,0xce0c9a65e0a040400646,0x36aa41e7115803902c6,0xdba2307ed43645e08aef,0xb9f51cde5c43935989,0xe08905a0002f0c0cd400,0x807c18633099b412081f,0xf61058302af150616022,0x80086000038fa271b8a1,0xe18ae711d946002e659d,0x24c684b40fbe1a1200c9,0x500722009e0c9d18ec51,0xe00a388208405c30bb00,0x600010e0003f1b1007,0xc20137fc4c1502000fe,0xf40c81980028805ea022,0x4285d4084002b807a13,0x202a3e30d0fe0071460,0xd300700407830508003c,0x38c02e030c00280100c0],#[0x8800e008c01036004c06,0x3b3fc7180a0748689641,0xc680a026228d8241058d,0xf0ab39004020437800b,0x1c289c790a4e0004141c,0xe00f50c317f72af50016,0x7bc0084c5d4b03778ce9,0x1706550051c5181002e0,0x780009c667481814946b,0x3085a7]]
private def groupPage6 := limbs80 #[#[0x104400c8310c02108010,0x4405414c521445010c42,0x88620841324c53048520,0xcc730c8720c42328c630,0xd4b51d4343d0b41d0332,0xefdfbf7efef6eebe7f53,0x6504d611826513fffbf7,0x640c46448a6228664002,0x6408d610ce61189620c6,0x620c66464e610c065406,0x639496228265802650ca,0x64091609126371163051,0x621e6103d262011602d2,0x43852626d26031262192,0x6471163222321526261b,0x630a5316d26269360450,0x639e04209160111631d1,0x605d1608116179064452,0x632a0425db401a120051,0x647d3637516031160351,0x63311618d262352646d0,0x638d2638e5313d2620d1,0x6331160690623d1633d1,0x61366313d063450644d2,0x60652646916115064751,0x63711610526449263552,0x32165611926465263951,0x624d2603536149161961,0x6455264951632e7314d0,0x60392632e731651610d2,0x601d260151639e232411,0x30612640516375262112],#[0x626506249063751600ab,0x602d2623d2600d264112,0x615116169864492605d2,0x633d1612126039b41853,0x42091607d163193633d0,0x636db42892642eb304a3,0x622d26319f30629300d1,0x64292636d06451262a12,0x60751608d16099264352,0x432506441b6449160151,0x60012644d2633906461b,0x60892608d2627d060512,0x62865311266119161811,0x4319064151609dd300d2,0x6205161312631e232718,0x62391613926021163652,0x6171161291619d264612,0x60812602526305262891,0x635926471263991601d2,0x62251638536051163611,0x61592620926309263592,0x63893637126459262291,0x64790645536345161911,0x64691606633269161552,0x60092641526011263750,0x632a1327126499263212,0x61852607d163012649d2,0x633d2625516021260691,0x61a1160a126299262792,0x63992630116161161191,0x635d26311263893604d1,0x63412648184389160251],#[0x647926475e3049064493,0x63393635526215264310,0x6371063412630d0643d1,0x60a126291163552647d0,0x61252643d264a12645d2,0x52892635d26075361411,0x326ef535af3106f217af,0x527ac424ae6372c643ee,0x5386e323ec439ef306ef,0x534ee6076e607ef4106c,0x531af5372c3266f303ef,0x4366d324ed3042c5162f,0x3006f5366c436ec306ec,0x304ac217ad3266c3196f,0x5042c5392c624ae6356e,0x535ae217ac4376c433ef,0x5186f5062c5442d6306c,0x627ac326ec4306e6092f,0x536ec430ad6372f4042e,0x326ee327ef4062c5462f,0x429ae6456f5376c435ed,0x4342f5382d2056c5366f,0x439ad323ec624ec3172f,0x531ac604ef5306e328af,0x4262e6022f417af515ac,0x4266f530af4362c5256f,0x6026f3002f535ec5086c,0x327ae6386e647ec623ed,0x320ed6292d3142c5186e,0x404ac4302c536ee321ee,0x627ee3072c436ac524ef,0x6322e6462c426ed3162d],#[0x5266d6106f5086d6126e,0x432ec511af537ec5172c,0x424af538ad3056e617af,0x328ac535ef5262d327ef,0x627ad6376d305ac5072d,0x4396e606af536af4296d,0x526ef2162d631af5056f,0x329ae306ef537ae3162c,0x314ac5456d327af505af,0x6022f5106f4056d203ed,0x3262c545af530ed617ad,0x3196f5326e303ef405af,0x212ac4352f501af5072d,0x2162e3196d606ad3072f,0x624ac5472f4356e646ac,0x3186c544ee6192e631af,0x4072e6286c506ef4256d,0x2162c5106e3186c5466f,0x6162f214ac633ef633ee,0x3212f424ec4202f3142d,0x2056f5286e657ef4372e,0x527ef506ef324ad303ef,0x3162e6556c427af4142c,0x5476d6172d315af4366f,0x329ac212ae315af4266c,0x6386f406ef4162d6262e,0x4072f5006c546ef5256d,0x403ee6586c654ef2186c,0x624ee3262f517af3296f,0x527ae311af312af3042f,0x6226d3172f426ec5406c,0x3172f3062f4006e2196d],#[0x540ad607ee6126f4376e,0x2186d6322c4162c520ec,0x616ad6192f524ee6162c,0x5312c439ac4342e6472d,0x6172c517ac545ee2186f,0x6016f436ef314ae322ae,0x507ad6076f433ee206ee,0x412af3196f414af3256c,0x206ee322ed6186f423ef,0x432ec406ef430ac644af,0x3262c2196e6562f5342c,0x6262f3186f435ed6256c,0x432ae203ed6286f304ae,0x3266c547ef5362f4196c,0x203ee3296f324ef526ef,0x6256c4362f507ad300ef,0x211ae6306f4002c546ae,0x434ac547ae6186f500ec,0x6376e3286f315ae627ec,0x407ac5342e657ac4396e,0x540ef437ef400ef326ef,0x324ae3256f604ef415ac,0x323ec206ed6092f3172c,0x4172c203ef3056f437af,0x616ad324af305ad6356f,0x430ec3162c5362f623ee,0x3286e324ec4262f2002f,0x3072e6526f527ec5212c,0x6292c435ac4356f5142f,0x6106f5386d317ac407ae,0x3042d3286d6016d2162e,0x5162e317ac3072c4172e],#[0x310ec434ef4316c4372f,0x6026f5356c5262f538ee,0x3256e647ae6226f5392e,0x314af614af435271056d,0x5042f520ef521ee621ac,0x3202f328ae6476d614ac,0x210ec321ac324ed212af,0x6122c614ad214ac4296f,0x303ee650ec5412d321ae,0x524ad2196c3186f321ec,0x609df300ec5356c538ec,0x4212d2186c4105363052,0x644ec5446c210d2608af,0x315ae210ec4256f4312c,0x323ec534e6610ec5372c,0x620ec514ac504ac5286c,0x5452d620ee6416f533e2,0x611ac424ec311af4346c,0x650d9640ee32010604ee,0x6092d624af4332f410d6,0x5376f5172f5049063552,0x511af5212d211ac4042c,0x521af422e320595650ef,0x533d06406c544ac417ac,0x640ec515af432af422ac,0x514ac328ac410ee3142e,0x3202c423ec530aa300ef,0x5302d206ec3106c5306c,0x3202f434906256d312af,0x321d2609ae6406e312ad,0x523ec404926386c653ec,0x320ee314af531e51002c],#[0x538ae624926296d321ed,0x427ef322ee620e32006c,0x435af524ac536ac5302c,0x531566506d621ac503ef,0x531ed306ee614af322af,0x3006f5352f434ef2196c,0x610ed2002f503ec528ad,0x5202d6116c214ac420ed,0x543ee214af439ed217ac,0x3042d210ed311ac5482c,0x6592c654ac4142f510ec,0x3286f521ae654ac5352e,0x640ed3212f5322f4382f,0x5266f211ac521ef43050,0x4332f5346c329ac4346f,0x403ec510ed3002e212ac,0x329ad3106c412ae324ac,0x3262e3106f5002f321ad,0x605ac322ec414926402d,0x427ee211ac5322e610d2,0x523d56506c4196c322af,0x4212c5346d322ec5402f,0x436906306e6116d611ac,0x534ac3142f311af427af,0x620ec429ad322af4302f,0x651af420ef4202c32961,0x3296c541506046c415ae,0x310ec422ee3266e321ad,0x3129a640ef52025610ed,0x640ec422ae644ac3256c,0x514126062d6122c53492,0x1ef82bc838702d80002c],#[0xd2580421c7320c40142c,0x3f1e2b37dc6684ba394f,0xb1f550ba7d54adc8b590,0x3703ed7859d431565dc6,0x5fc4248364fd69e64ba7,0x4a7a81a4dcd96e723f63,0x30a812002cbbd732a9a9,0x338ccf2dca3230791844,0x60b4120015a50d284510,0x355d31440f2340aa1f45,0xa0f419001fa751bb6457,0x46d043c0cc2c09f1f05,0xa11c26001d26c98e5a14,0x75bd4c488ff364b62346,0xe1081b002197d9d66c99,0x55530428f1338b02586,0x12021002207e9d469d8,0x65793444cf1358ab2146,0x11c1d0020c799c46b18,0x851d2d440f4364b222c7,0xf0e413001fc765ba6256,0x956d47498ff360b222c5,0x20f81d00201771b565d7,0xb5893d450ea31cad21c6,0x415c270020a79dc169d8,0xf5dd5f4dd113b4c92b88,0x611420002237f5e17019,0x55a546490fd360b12306,0x914c2b0022b809d96c99,0x55bd4e4c90b3b4c62807,0xd14c260022b809e36f59,0xe5d54f490fd384ba28c7],#[0x6100140022a81dee7159,0x55893f460fb358b32486,0xd12c25002167add16ad8,0x75b9484ad0437cb82386,0xd130270022b82ddf7099,0x85cd49488ff368bd2586,0x4164350022e80de96f59,0xb6ad765412c3e4c72a08,0xf13824002759362d805c,0x6631624e1113b8c22606,0xe0dc27002558da08789b,0xd57536434f5354ae2145,0xd108190021d7e9cf6797,0x65f15b4cd0b390b924c6,0x31502c00235835e16d99,0xa5f1644dd123d8d22b47,0xb118290024f88dfe751a,0x85f15b4a90a39cc225c6,0x615c350024b89dfd755a,0xe62d6651120418dd2c08,0xe13c270023b871fd73da,0xa5fd63505233d8cf2a47,0x21441c002187e9e26ed9,0xa57d3d488ff384b92647,0x913c280021a801d96e58,0xd5994349d00388c32607,0x91241e0022b7f1d97018,0x45e9544c50f39cbd2487,0x3158210023382dea71da,0x16697d54d213d8d62c88,0x1502d002678ea12795c,0x959d4348902390c92808],#[0x2124260023a861f06e18,0x45c546490f9354bb2507,0x9164230024e86dfd74da,0x669178541263dcd32bc8,0xc13c260026d90a2b7f1c,0x958d3f478fa340b121c6,0xd11823002197c9cc67d7,0x362164515213c8c92486,0x411c240024c8ae05765b,0x5f9514a5113acc928c7,0xb1202500237861f0725a,0x75d15a4dd103c0cc2987,0x9184320023b85df1741a,0x55bd4f4c50a39cbc2707,0x1242100234819dc7019,0x45653243cf830c962087,0x81702d002177e9d66d98,0x36516c521263ccd62bc8,0xe0e81b00231861f2739b,0x85a944488ef334b82245,0x18201f00224801da6b58,0x41c13020c840c081424,0x84e08306c81010d10a3,0x7804700212050600ac65,0x1d20402c8c4888b868b4,0x6222321c7459302a1515,0x362c56189d1890512c7c,0xa781e251f52443781094,0x970e21eea5224fd6048,0xcde80a3ae488dd80b4f0,0x9111b7014a6473f40c88,0x453b810fc04bce0493f5],#[0x8900b3eef0201158f1a2,0x22b7d7fef0e0073ff7f,0xf128279da51b11eefc10,0xc73c64bd14df1f200a2f,0x880015d9f8404f767a04,0x8dc6cf00aaf2504c7eef,0x84a8aa0ee64b7c7c0228,0x37ce884149c5f109eca7,0x2fe132129406bc33c005,0xa19ba8819013673840c5,0x18fff8eac018bfdefc00,0x4145f3a800153f5fe184,0xe3679148e7151235f3a9,0x6fbfe3002c7236828e66,0x527efe04082a7fff1001,0x711edfd03202abd1e184,0x9014defe100005829758,0xfb0024fd87c608a8ef91,0x537ca8405278c974054b,0x83c2ebc1812cb2fc814,0xc000b1ffbfc4105bfe42,0x1802abfa84408b0f8f38,0x4ceffe20032e6ca0287d,0x85822b7edfc34030afc0,0xf8200c3afd821005b7b6,0xd00db8bc4e50096bffd,0x50002dafd84008adfb7e,0x245429751c463fffc79c,0xbfe9820c3b542633d1bb,0xd7d9800159f7fc38616b,0x114971e4c850ff90420f,0x58831fbbd79820dbbc09],#[0xe0c257effc30031fff1c,0x73ebf2810a4f3c480293,0xcb00162ff34420ff5102,0xfb201eeefc10205675c3,0xeda16002c5eefd26218f,0xcc009dfc36822b868325,0x4118cece44517900935b,0x8273cf7cc2800168ade3,0xc8200aabb6640155db3c,0x859f6fc3821b8650ccff,0x547c4f89b2456fdff260,0x35ef6e1f40bbeb79840,0x40b5effd2021afff7c10,0x228f76828c0c0147ff18,0x72e52248c8e788b3c8ec,0xbe2160235ff08008ab72,0x20143ff86102e7d3808a,0xd4022bbdfe20114deff1,0x6b7e7bc20a7c3202ae72,0xfdfc081054fddfbcc00,0xa3dff0204155f3fa810a,0xcb5020af368c647f0d00,0x738ca011746e3cf828b9,0xdaf3c21c7d7e3080a899,0xadf9f5fc3901c7b3f,0xfc81014bfe600833ff20,0xfdffa6005cfc011023d9,0x408e7c184a67a249e454,0xf020a27888808cbfa8e0,0xd2a2a18e24537d013df1,0xf4f8059f85081457d204,0xf5fe1801b7c7c08285db],#[0x9f5f83202ab33c250153,0x4dce50a012b3ebf2d014,0x82d77fd580175bee001,0xd1201b67ea0273977814,0xa000577e9e14202b7feb,0x9e2000577c0a50a0eb9f,0xc80002a3bde85882b3e7,0xec201056fffde20030ff,0xcb3f0809df3f7cc08657,0x20142f86c052ffded800,0xc4000adfbfe4c00cbb67,0xebcc127bded4000aef7d,0x99f850a2ab9f9c205155,0xdae3c01b19f310115dff,0xe0c00d5febdc70835fbf,0x87efff10416775095fbf,0x40163ff5f0700ca2bea2,0x402bbf481608acff4c02,0x2b7dfdc388197fb810,0xf7ab002ebe204c73ce44,0x1600d0880a6fdff8012f,0x20035efee1c60b7efeef,0x20014bfbc71825effdfe,0x5ff61041cf81420aaf8f,0xa9f7fc60855efe05002a,0x863dffc388175be3008,0xbc601163e11016fdff06,0xc224054ffffe0082cf89,0xffc822287effc3802ecf,0x725495e52253ffc71024,0x577fc20022a3f84a8045,0xa0057a773a45af7a1402],#[0x6002c8f3d0a04165fac2,0xf83022c5ff60049fa719,0xea11082c0de50a293c2e,0xfef2e005affde9800daf,0xabfd0880059786788287,0x32ece144ebdffa4003,0x3008aa57032a23afbbe7,0xa10151dbf50308567373,0xff060185de54082b33f0,0xee1c376953e99012f7fe,0x261c602ebfeb70f80a4c,0xc0605674ece26516e7e5,0xa4b145a39c96d29bfadc,0x30e5a1ff5181660172f,0x3848557ce3c0c3feda42,0x35fffaae50180bb56421,0x77497b282f097ac2f212,0xa5edaa2cbbe642e0c092,0x47ad6594056fa87bcac1,0x11ce9d430902c1f34089,0x3e0eb76287181624b673,0x4a2d9f0be510adf0f61b,0xc02b2f5075dc567ee0ca,0x949bb020665caee7eb54,0xa099864371cad7e54580,0x6fc906007c2cb3c83bdc,0xe444942459a473e17011,0x400564e9cf88ca5650b7,0x8f857b8fa2930493f527,0xbaddc251de82146bb140,0x60cbc3b0e535e4805772,0x4a85b24681c47585e424],#[0x8f7fd5728b8aef77a702,0xe84d7a6173129dfa2550,0x665815ee8f92c3126ab,0x247b029b7e91bb8a4ce6,0x4bc20535fd6d30b0acfe,0x3cf7e0b397f2a9929a7f,0x9456b10c87f20bd273e6,0xdcb6ff1e428715185303,0xcb6f630e600ac3a940a1,0xde70be52151f4fae2454,0xbd7d942235d573030165,0xea197293fc74f0437d20,0x5143c9c4d7e59e2a5143,0x253f7505708b4dfeec0a,0x8c5573edc2a48160a53a,0x8547fc21199151e73ec4,0xd8cfcf41d664aabb1986,0x49e1c988732cc3855900,0xfd21f4aa2b8f5c9e0149,0x49913c94efd20b39848b,0x170581ee236fd12a8472,0x597970b9273ec0930e30,0x728693260967f8d344a8,0xd9c95960aefd433038aa,0x1ce9c1204935e1f3a0cb,0xc5860527dfdcf806542c,0x76680acf9a72f23215c7,0x74907e7a3226e2bbfc0,0x38fd9829a11fc9463880,0x3ef4b2d292024b3cc47a,0xe166f80e891c766282a,0x190465ccd148d7ee8053],#[0x543f20902520d9212cfd,0xb9f6b0a9805b4e94dcf0,0x79fa2ce145f776c42c2b,0xdbce1f482b37ad830e55,0xc97f4b03939d46664e1,0x59476c947a6ad84ede9a,0x73446add325a1f50c265,0x1708fc822c66579c9e70,0x22878c546b03fe03c5f0,0x2ba1217c28bfc14b3c5,0x761c9e57c1145bd4cac3,0xac6701ae47a6b584f778,0xee2190b545c7f203b310,0x2eede03294998933a46b,0x1efc1c3fa2a508e747f1,0x19c2a8f66b65254b983,0x32186058a6a2f51af81f,0x573839323291b7846bc4,0x19c27d11b9453a5d1646,0x4950b57fb4bb123df99,0x64971ca2b74c4d7fe4c8,0x8274737e6e04720587,0xc800598960e56088d3ff,0x88fd1103fbe6045b0b0f,0xc905b090b17a1a59a224,0x4796a4647b9089f002bb,0x960faddca88e7a515dca,0x92818ad4688f7cc02098,0x12c048dbc054a39929de,0x4f2d514dcb96a02a1f34,0x5e05607fc15807a030b,0x2531eca4c89a8b8fb3dc]]
private def groupPage7 := limbs80 #[#[0x9858578680fc8d6e4353,0x1263fdfb009292cbf0b6,0x11290b81b145dd60d118,0x8e3e0e5574e140fdc2e0,0xa609513d86b0e54ff0dd,0x2bb6e7803f4a8639d30,0x2bdc68c54c917fd4644f,0x5299ee88c463f87443ac,0x446b45ec8b2c879f2771,0x948c6c3651c632791186,0x1e05648d9961499b4179,0xea6e1e00bc8300f7e7c4,0x89f0cf82727a32b322b3,0x251ebea1aee2a3ea9bc9,0xdc4a23c9c161c562262a,0xa56e22ee3462a648b87a,0x24cdec4d8567c65e8252,0xd5fe5d8240acf832ec28,0xe2032c2eb934e0791485,0x1c488d7b30299e151ec2,0xb61ca0fbeb690a16170e,0x4c34485a07d5c091cef4,0x9487f3c1c4bc1659f9e6,0x584e7d891ee501866173,0x4493f3eda068e567fc66,0x12471ab9841237d89148,0x430d8c4a311e7e42e0a0,0xc0f117c0b0fbea1c8225,0x59e643c4f12a0bf84879,0x53d27c58527a7fe22701,0xe8842ddc275e8686b224,0x90611aef6c0e682b5f04],#[0xf913c945d9814c3857a7,0x4bd143ac2a5ad22ea394,0x91ac2c33ea604ca68fd2,0x5b4239ed60ca4567f268,0x73a094575bac38a97fc4,0xd2080ee58bbf96691af8,0xeea0ae0060785f2e528a,0x4384957b38a66c2a3ea7,0x36447a7d77aa29df862c,0xcca09315d27de1614453,0x32030c4aaf584760aefe,0xcfd1411a9eaeb0e2adf6,0xb02edae8e4e9c7c4815a,0x7e1d8032c2c89e4b8e51,0xf482992abfa70b847459,0x67d0530048b9abf08a0b,0x438b27f54c1b120ecc09,0xc9a555d9d9e13deb32e1,0xbc2575a050cb8b0864fa,0x98aee290dc30e4e75905,0xd23edc7283eb7033941e,0x4540c0b6bf9864030517,0xb039d0605e19858557c7,0x6fd08596151f687293bf,0x60e25c1a9e4c04e6ca4a,0x9386198761ca878c6041,0xce830cf419ec29376770,0xe34b37be80718124f5c3,0x9cf01ea4a82ebe7b2930,0x85f0a2b3f66c1437a8b1,0x647b05449d39f118ae84,0xa0495e235b9e13d0290c],#[0x951c743ce4531a6836c,0x8914a83f8a89e92fcc1f,0x94bafc8d8032c2d3fe0f,0x546f70f227b3e9e64c8a,0x233eb70b545777add61c,0x75778970c38b25650eec,0x941b2425a7b4ff005709,0xc0916792ec5ca6fe3503,0xf9a70f08aa2e1ff0328,0xd1187567af82ec0ccb0a,0x4f106c0acae6c393a995,0xfb88aa8ff0be202169ff,0x3909038a1e3151cf9e03,0x1044a85ca46f8455f4e9,0x84cc8a26dac11473cfef,0xa789511aefc61cd0a4fc,0xc0291fd152847153e88a,0xfc01c81556ce89a394f9,0x2a7296a231aefc073fc,0x65b3acc2084d247fa7cf,0x3d78166ec243f8e80012,0x2b198fbbf604134172a7,0xe9b2c9ecf853f8288f8a,0xa978b2205b4e6573c288,0x3c1c4f829ad007874aef,0xec245ad5e08cb419cc47,0x6]]
def g63D9 := groupedPages #[groupPage6,groupPage7]
private def groupPage8 := limbs80 #[#[0x24040000c0080000001,0x40000000008c000280a,0x34010040800c000480f,0x6004000140081201419,0x20381c0440400001,0x18070342d008000000e,0x40a01c0302c1900001,0x200800028020403e,0x4058110001100801,0xc001014020140100007,0xf000008090700001004,0x40314c080140d07804,0x1802020000000000001,0xc040200600c0000c01,0x801010080041800400,0xc120645d0002905801,0x78210500f0180100000,0xd401014000080000007,0x40000c000040b02800,0x50010000a0081505805,0x3400004190040101001,0x60740403c0301000,0x84a0080b000000401b,0x2000014050040b00006,0x70000e098580d003,0xc8020100001c0f00430,0x2c0a014000000600c01,0x120001807005,0xd094000a00e0002e,0x4000180d00431,0xc020000080801401,0x410000000600200009],#[0xa01c100000b00403,0x481c000070081100401,0x4040d40004cc40541c,0x400011c120300102c09,0x1403010040000101800,0xa01c01000001ac04,0x1800000040000201c06,0x10030001a0000000803,0x48000500300c0308c00,0x403028200002401007,0x8180080b0100700400,0x100900c000000000001,0xc040cc127a00500406,0x300c0000d30,0x41b07812024020101d,0x402010011380800c01,0x8000180101c1f0000d,0x190780207c0404000,0x24010b00702c001b00b,0x2e01c12080020002b,0x2006000130381600002,0x20000042408c0100456,0x401004000401b00401,0x3801004020140c01c00,0x80a05c51000020188d,0x3400098290140c00c04,0x40004c000001206400,0xc80508804008974700f,0x3000030002001c01,0x20a1040300240602811,0x140507816004050000d,0x68240300008c0f],#[0x10210c0381643a0081a,0x10000004503c2e0340f,0x406160030380e00407,0x10000080c0284e0340a,0xa41e0082400c15,0x2c1808001004250d806,0x9414030080001500800,0x404000060080504dfb,0x24390440002c0f0d802,0x51423088090100501000,0x11c011fc010000103800,0x1300000c0c0301c02c13,0x280f0ac040141800805,0x4010020440501800,0x640605c030101f00876,0x181400032014041000f,0x8110240d0f00303407,0x4010102d008013c007,0x2c0070a00a0000300402,0xa0f42602c000000d,0x880f008020000402407,0x180a0680203c070182f,0x5c00020040040100847,0x4803000030009700005,0x40f02c06008e901c36,0x294150000204c0104c3c,0x4c0101c09000000042e,0x740e0240c0280b00c9a,0x144050480601c0500834,0x4200a8250c8000000a,0x1e02b020060243907c00,0x1c00178041147a01403],#[0x480200000020020280b,0x4c6b000080ec5929801,0xc0c0100c0000704802,0x40000c1100c2716009,0x1640104407048020042e,0x40680106c031e800,0xc0070880e16c00038c7,0x2c423fc0004c0600000,0x409809a040300007,0x20001e81f0ac090202c,0x1a00119c020380b02c02,0x70120904705c0b00413,0xc401c80700c0500c20,0xa807054000102403801,0x141000800088e00e807,0x5c0056c8a0200002400,0x3012020130043501415,0x10820010490241400404,0x800074be00013,0x30630100d0040024c00,0x3c0007c010000206405,0x1c052084290080101400,0xc00004032100500002,0xc57000630000704400,0xc0e018040f8f10680a,0x2089301035068060ec5c,0x60641d01c2b02c2a,0x6883509c4f0000202c34,0x5f220090bc14168a0,0xec020e8211900709c3a,0xb48508817078070dc04,0x2000014000f0220103d],#[0x10e00500413,0x680e040000c8006c843,0x14070600701c0f06c02,0x1340e2d00f0100d04429,0x14800005880e42704460,0xc05160350003302403,0x5020048000e00907000,0x6818000541b0180d,0x6801010001680202c08,0xf37d5fd0002000202c42,0x4d17d010000ff3591be7,0xddd7f0404400038527e2,0x17e014000ebb9957ecfb,0xd7fa901002239827f24e,0x10160007fdead51d6ffa,0xd00c011223ac27f24f18,0x19000ff3f7fdfedffeeb,0xc0603be28224f1850,0x67f9e9bb3fff3bdb5,0x3d428525218801a,0x366e73fb3fecfffb008,0x2803e628925218a01f00,0x691c4f05f92d67488010,0x3fa28925318b024000f,0x25ceff7a65def0210010,0x628c25418d028000e4b,0xf62dcecdf62801020004,0x28d25418f02b0005cd06,0xbfff6f77720080028418,0xf254190030000cfff7ec,0xbdffaff1822000042628,0x57192035000f365f2eee],#[0xfb1fc1010080043a2912,0x19403b000e6fbb8fcdee,0xfef4102001044d293257,0x503e0006f7defffbefff,0xf0820040046029525819,0x42000f7f27bfeffdffff,0x38824782982581960,0xbdfeeb47ffffd7fd0,0x260490299258198047,0xebf5fff3fbddfd1f002,0x1404a429c25819a04e00,0xfdf3f5dbfd7fe3e40000,0x4b92a025919a052000f,0xff3ddffffbfdd43004c0,0xce2a325b19a05600098f,0xbf7fffeffefe00b00184,0x2a425b19f0580001ce5f,0xeffaef7ff285908004e4,0x625b1a505c000d777fff,0xeffffffa11080104f82a,0x5b1a805e000dfaf7c667,0xcb7df0020082450f2aa2,0x1ac064000fffcbf6bffd,0xfff004200005232ac25b,0xd0660005fbffffffffdf,0xf0112008053a2af25b1a,0x68000ff67ff66feedfff,0x50100605562b025b1ae0,0x197fc7ffbfaffff9f6,0x400a56d2b225b1af06d,0x1f397bf9cffffbef7042,0x4005822b625b1b207100],#[0xffbffff77fffbff00040,0x5962b725c1b5077002b,0xffb5ffbfdffff0402000,0xb12b825e1b6078002f7f,0xbfbeffffe4f100101805,0x2ba25e1b607c002dfbef,0xefffffa5f000505a05cb,0xd2601b7080002d7b2fff,0xfbffddf000002205e12b,0x601b9085002cefbffeff,0xdffff132610205f62c12,0x1b908a002efb9efdffcd,0xfff0045000060e2c3261,0xd08b003ffbbfebebffaf,0xf050411006252c62611b,0x8e004fffbe6fffafffff,0xa0063e2c72621be0,0x4fcfdddfffffff5ff0,0xa06582c92621c108f,0x59cfcff5f7f2fffff82d,0x2406722ca2621c109300,0x5ffbfff7bbefdbf8c410,0x6862ce2621c40980057,0xfffeffff7ffff0008000,0x9d2d32621c509a006eff,0xaaf7fb7fdfdc04824006,0x2d42621c509c0061bffd,0xdf7effed70850c1226ba,0x62641c80a1007f6bd3b7,0xbf7ffbf840000446cd2d,0x651cc0a5008ffffdffb7,0xffe7f01c001806e02d92],#[0x1cd0a6008eebfffdfff7,0x7eb000098146fa2dc266,0xf0a8008fd067ffffd87e,0xd00404a027132df2661c,0xaa008dfffbb3bdfbff5f,0xc0000817272e32661d00,0x8f04fd164745fd1e70,0x802073d2e72661d10ae,0x97f3fc7d5fdff7fff024,0xc174c2e72671d40b000,0xbf777ef35f3ff3e42048,0x7612e92671d60b70093,0x9fff083efffd00016002,0x742ee2681d70ba00a83f,0x7347ff37f34800008007,0x2f02681d90ba00aeef1d,0xfd7fcb77f08020280787,0x12691da0be00adffeb5d,0xc43bddf048800007992f,0x691db0bf00a10cbbddb5,0xffeef000000207b02f42,0x1dc0c200acffffacfeff,0xff620c043087c02f6269,0xd0c400ab7a7f4fe9f67b,0xf440100007da2f62691d,0xc600adbe6ebcd9ff3ebd,0x4c002007ed2fa2691e00,0xace1f17a6cadfb5ee0,0x10308012fb26a1e20c9,0xab7469ca5b3768c95040,0x48112fd26a1e40cd00,0x8f9fc6eaffbec6a30000],#[0x481f30026a1e50cf00a9,0xe3f9bf7ffaf9f0800100,0x3030226b1e60d300abff,0xffffffffffe240010018,0x30426b1e70d600a9bf7e,0x7da3dffff06000000847,0x526b1ea0d800adc1ff3f,0xd9d3ff71010000086130,0x6c1eb0dc00abd8d29e3a,0xff77f000802948763062,0x1ec0e100aeff7d5e9fff,0x7cf0808882088730726c,0xe400ad2c5cfafd2cd4,0xa1034000089e30826c1f,0xe500baffb7bbaffcb7bb,0x4029208af30b26c1f10,0xce6f69ef56fb6b7d58,0x8c530d26c1f20e6,0xceffbfff7feff7ffd110,0x5008d731126c1f40e800,0xd8d1fcd3daf5add40020,0x8f131226e1f50ea00cf,0x953fffffd57ff0000000,0x231526f1f60ed00cfbb,0xb9ebffdfdfe000602009,0x31526f1f60f100cbfbbb,0xafb7ae7a6c400080c91a,0x726f1f70f600c2fba4fa,0xf7efefd4080000093031,0x701fa0fa00cbffefefff,0xfff7f00120f8093f31a2,0x1fb0fa00ccfbce0feffe],#[0xfff8004000095a31b271,0x10000cfafb7fdf7ffbf,0xf0002002096d31d27120,0x400ddffd6fffffffffd,0x420400898731e2712001,0xd9b9ffeb5ffbfbebf4,0x21509a231f271201107,0xdfd7f77bfcfdfdeef30a,0x1809b832027120510900,0xffdfbffffffbe7f00000,0x49cd32627120710c00df,0x3bbe3ff7f76ff00800d1,0xe832827220710e00d64f,0x9e73ddfffff062002009,0x32b27320a11700dfbfff,0xfffffffff000060009f8,0xd27520c11a00d7ffe1fd,0xfbeabfa1a435404a0f32,0x7520e11e00de5fdf79ff,0x7aefe12040100a2932d2,0x21212100d9970affa8ff,0xc3f10001002a3b333276,0x412600dafadfc3dffafe,0xb01114400a4c33527621,0x2800ddbebfa4bdeeabe4,0xa2904a613362762161,0xedcf7fdf9ecfdd6ff3,0xd105a74339276217129,0xedb66bcfbd7f76ffe080,0x20a8833e27621a12b00,0xcfff58fffffffbf12000,0x1a9a34227621d13000e6],#[0x7775cfff6dd7d0021282,0xb134227622013500effd,0xdfde7f7bf6f08084292a,0x34427722413600eefdbf,0xfd6a7fdfa01080605ac6,0x927722613800e962efbe,0xedfafff01200000adc34,0x7722713c00fff7bef77f,0x7fbfeb10a0001aee34d2,0x22714000f5ffdfbffeef,0xfff40380800b0634f278,0xa14000ffeeaf7ffbfd7f,0xf00a80004b1e35327822,0x4300ffbfdfffbff57fff,0x18000b3635627822c1,0xfffff33fffffefdfd0,0xb5035927822d145,0xfdf62fefdff7bfffd201,0x102b6935a27a22e14800,0xfb8bfd14f38def700806,0x2b8135a27a23014b00f4,0x2fded3fb2fbff0020061,0x9235d27a23214d00fbf0,0xfeafefff0ff01200f10b,0x35e27b23614f00fffdf7,0xffffffeff00000100ba5,0x327b23815200ffbf7ffe,0x6f7ffff01090000bbb36,0x7b23815500fc7fa7fffc,0xf3ff70000c008bd73642,0x23915700febbdfbffebb,0x736c0c84c14bef36627b],#[0x915900fff9ac9223f53b,0xf00803000c0736927b23,0x5d00f7af9b72b7b79cf7,0x400200c1336f27b23d1,0xfe4db6f9164bbedd18,0x4000c2537227b23d163,0xfe16d7bff617fbbff800,0x80c3537527b23d16600,0xfe7fb61cbdffbe500280,0x6c4a37727b23d16900f8,0xfcd63b712ef710089000,0x5d37827c23f16c00fb79,0x4f7f7ffb4f708200000c,0x37c27d23f16f0107fcf9,0xf5ebffbffa8000400c6d,0xd27d240172010f6bfcff,0xa67ecff10042300c8337,0x7d241174010e263cfeff,0xeffdf030000b1c9b3802,0x244176010cebeff6ccdf,0xffb00020092cae38227d,0x8178010fcdfed6dfefdf,0xe00000050cc338427d24,0x7c0100000002a0000007,0x136d412cd938527e24b1,0xa422cf9240131bed831c,0x80b4e637947a44c07019,0x24963224305451ddc442,0xecd481e84e7acb5df7c4,0x3da2acfa611a4241e2eb,0xe1724161f294641468c9,0x1fc5dce0e306d778],#[0x1163de0702ab81138101,0xc6301c80843c0a8074a9,0x6009faab40b001097401,0x8db344c4012845e406e1,0x8fee0f3fe2a017370744,0x809ab22b97325c7d8e1,0x4ff284a559d230c00eaa,0x5346d34acf716674190f,0x8e5822b931034c74088b,0x156f5b53066b983bd33b,0xfa0e98e7d6ec5d25d9b4,0x1583baa0c723940a39ee,0xa15181419c31e7e42072,0x849680f6125067c3d877,0x36fb101c6d90b17887b5,0x631b645db4417a4ef898,0x59fd9b8d95864fe3a207,0x62d6a73ad5cee6cfda05,0x36bf2b14280e390366b2,0xbbe6593e5c3d6115e8f2,0x8d8a87f696f728f82b2,0x982de1e1c00fd431d810,0x3bcc87859b5811e30053,0x5661559c4eb7adc4c2d9,0x88f52c4b429f63981922,0x4ac75aa6dfa5ce907140,0xac5dce87f59e48162fd3,0x8d42f832d856017a1227,0xe19d002e546493bfc450,0xd5074687c92209b9fbdd,0x59d071bf997a0623a6ca,0x942770e5f094d00592e],#[0xf44c5a5346abf35df9ca,0xe8d958abc9393ca517ac,0x1b5772a1cabc85e6a3b,0xc83c218e5c9e1a1deb91,0x69646a9a09c186d0b568,0x37f741707c45442c1ec8,0x59a95a6a7332436a3744,0x5f0d6b3aac961b6d0415,0x41671d3286d1c1d3a71,0x228ae0b754867474c392,0x4f69a4aa892729193c6e,0x5e001a805c9c61214538,0x259c4dec73cc7d084c84,0xc40034281641c3ef7267,0x87dab9fd3e4c01421ad0,0xf71c57636ccaae9fae01,0xfe4941721bc6c979870c,0x7d51dd1aa09eddf40000,0x382b966e00808000002,0x8196970abec3c359128,0x61467a1fc4de207c608e,0x5f9005100f8001be00c0,0xa04ea0f35403f8030a40,0xf91808c2b83572a1748e,0x10adf8e16f8079a233de,0x3b1fd6308406c1e5a9d1,0xc170c6a808c8303af8a,0xdd8239133101140a070c,0x3a215fd96262a2900188,0x1703f9be07167803c25e,0x98306b3553d3603913d9,0xf6992f03261d01b418d8],#[0xc2b51b32847980053f4d,0x66962bfc7003e8400534,0x80b636f905667211a70b,0x7c0641d80cd5fe07af9,0xbd506be2ce0a408b43e0,0x29bb15c004132cdfb4b3,0xa55ca29c98ff87e61e04,0x281188b35703baf2eb5b,0x194846201fe146cc0400,0x12741870031b93fc7b65,0x8ed22bb27adca60a7f3d,0x7086841807801081845d,0x8a10098d22ef2bb10080,0x2398699e3829ca0db967,0x805776e4461114b1f71,0xe6477ed3059361319eb0,0xa594eb1f1b91abc36082,0x6a4f0e1666da19b2475e,0x63e7add47c3d8e3b8e57,0x574994bb36430d68ca36,0x5bd738dacd58f63124ff,0x9900380d7890f3d739ec,0x1b2d27defd37f337303,0x440d432fdc33f0c6a0b2,0x241e1ce7780b6d053300,0x5701957347d1d78fb64d,0x78d92321b922863e112,0x41820597fb400125fea,0x61d827ae800042824d07,0xc774b0996f5682d14b51,0x4104ed9850940260a461,0xd366c741d23b0b4e91ed],#[0x1284ab1a51d5e385f00e,0x6931f72d81de188d001,0xc5b88dee482c3f900415,0xfb029bda119385d8037,0xec43580831d9a18b572,0x7b7a03099b9746ca80b4,0x74f29b7becfe4be026ce,0xd90aa536c1b5c6138053,0xa6ed5a5ae462d5eed8ce,0x2df362681f7b7c344ac2,0xdeea30136d894d3c05ff,0x850048670ea817e933c,0x80cce80aa004438aa9f9,0x1a3e010b8d116cd34f30,0x14fbffd0a2f87e083f50,0x9de81a686a49caf6d4a,0x119f1e4dbb9c703884b7,0x92864004daedb7e0ce3f,0x3021c62654eeee944258,0xb1c3624ad211c0301f0d,0xc07ab58a70959011f302,0xa83cd4420010a341523b,0xa44748252004095342e4,0xc1b5000201dd5d81060,0xc008a52ab1dbdc817688,0x980595bd1842d1d617ef,0x75f4130c00ed1d780b0f,0x1b940ce9dc26adc46cc3,0x6bf2f542e4f4823ef2ce,0x505b6b8300c0057c48e3,0x1a7f50b18c892f11f1,0x81d02da3732ae0c17cb9]]
private def groupPage9 := limbs80 #[#[0xa7f58ad24d]]
def g63H9 := groupedPages #[groupPage8,groupPage9]
def g63D10 := limbs80 #[#[0x221a42188a628220207f,0x5a96651086098440106a,0x5a868190e842146398c6,0x2a64020e21a0ea7980a,0x61086490461080a29902,0xc442100043c8680098e8,0x6aed589c449e0cc55218,0x6218d04212003e9d8da6,0x4df6830d5a9f469e0d45,0x8ba4a1e0b0360d00405e,0x50c000c18010182431c,0x80338018a01858712304,0x19a80670033800ee8032,0xa001280198019a803b40,0x7003bd0064015c007002,0xcb401d402b9806400c,0x74015e0067e803200af5,0x300af80194028015ea80,0x660063003a00a0052007,0x19ea019f400e7401c00,0x38]]
def g63H10 := limbs80 #[#[0x84800030082c0c0c,0x402018080a000180c22,0x8040204020040700024,0x6824220100018020a010,0x488c02020001800070,0x1000160105060060,0x50e010000c000080,0x80468000880828020381,0x1780c0001058080c0f04,0x12800061b078102200,0xc010288c4408010000c,0x20080d000180a000a014,0x480c0201000100200000,0x3028b8460b0403834050,0x110e000025d0080c040,0x680209030040e0388c3,0x34d018010b806101802,0x1054364405000020102,0x9000980606058140000,0x261e000040c360292c03,0x780405020200a0301010,0x40180c00010140a1a158,0x40100042080191c08510,0x4000c9460000000020,0x634060081604000040,0x8c41a050708804430500,0x1c0202068c404000f,0xa048141e0000800dc06,0x2000c440001507806,0x420070280c003e06818,0xb00c080d000083619050,0x904c580701021e6090],#[0xb28addc0004d03058120,0xc0900115201f48eadfe0,0xafdf95c287988741391f,0x2f3f2120d00050206831,0x291541d2d6ca3e90c042,0x148117d43228120022c,0x6802fe26420101d9bdfe,0xdebffec04a34c74823c1,0x4e2501b80315214000ea,0xea21dfdb15de9fdb10c1,0xa3d3151a68220022020,0x28701800878fe7ff648,0xe4596a04c05355a86260,0x29c2c80291f319056a0c,0x49d60bb5b7840221b159,0xda015fab02e80421d408,0x1086006b6d39ff116530,0x4c3d00fe41642c233804,0xa37005820300903d04ff,0x9ff00eead4f10ceb682d,0xa16baf4390042006d111,0x4b00136cb0dfac7c109f,0x245885236fb103b80880,0xe80a00213015775ac563,0x1a09fe980a09ff7332a3,0x763404200a2061d60099,0x8ac17503052f5503002f,0xd75d317ab5c4300a8200,0xa100000c16f7fff3fc4,0x3f30d56e28917e372448,0xb904a80f0811c04c77ee,0x93f6df3e6d2ed82c697f],#[0xda5f843a84e8120120c1,0x210025a1d6ffda5f5caf,0xf764c960b7883c453014,0xc550168b30820974cf7d,0xe57ef7f6646217d78bbe,0x899040a590161a810809,0xc013ffff3fecbd2616,0x4503840993c285e01600,0x5016189848d785079708,0x7863e6f05923e795c446,0x9bc526801802860c197d,0x840cb73f68c8f32b489,0x5944039fc6e6b01c3084,0x1e5022aa4926dd558627,0x633dcd546211a2c886e0,0xc9c71820000b8401fd74,0x9b4fb9e3620b99027a7,0x24d5aa4b675020490000,0x95d229bf6a29d11620,0x2e00000027ac4cc7a020,0xe7e82400000010000000,0x8fd448173ebf1b09b14d,0x6955cee728098fddb6b4,0xa0c36344f625bc185250,0xe0143244543fd12cd112,0x5718d9121e8e98789636,0x58d3ab1b5186c65411d2,0x2d0092e92b846caa4284,0xdf5d8839cc7ac629622e,0xd1c011ea25b87b39a1b7,0xce474e2c865585b85c8f,0xcaf403ec0f0060e601f6],#[0x41084fd6bde9e940ce08,0x664bf872ea0b40c5ca,0x9a1043c6b982881c6c40,0x33b83324583b8d0ff875,0x481c185f6032a58f471e,0x817c7940e10cf6581103,0xc4c58f571a768d787f,0x4a00255fb413428d9,0x5e02b05604db7940f40,0xba61f4317122ed880895,0x5929cdc3c2d033c3e46f,0x57d1fddd0063fe7be25f,0x2569c6aa362752863dac,0xe57ec5f0f609149135b0,0xe77365e2da82257db5de,0xb50012eecdb03830e44a,0x1b84df7049a5810db142,0x401f7180171b3e1231fe,0x175c4d7702e25610e0f8,0x415984946370080268a,0xe321773203cc15b4ee36,0x6f004a5047d43d5dcada,0xb6c6d31ae14517cc1020,0x932e10b1f68fa016da00,0x380b24f36e312583d251,0xda13a056]]
def g63D11 := limbs80 #[#[0x8103f]]
def g63H11 := limbs80 #[#[0x40d0e9102044040600,0x700079f42c0ff73ff7f0,0x91e301796dea609b782,0xe60176b4300062398cd]]
def g63L : Nat → Packing
  | 5 => (1,6,6,65537,0,0,8192,g63D5)
  | 6 => (47,5,6,2293802,102,16777,8202,g63D6)
  | 7 => (1448,4,6,5702372,122,189070,8291,g63D7)
  | 8 => (3292,3,6,2359983,106,2613904,8312,g63D8)
  | 9 => (867,2,6,786473,70,2564751,8255,g63D9)
  | 10 => (41,1,6,65537,0,168522,8206,g63D10)
  | 11 => (1,0,6,65537,0,4096,8194,g63D11)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => groupLookup 1 2 0 1 1 1 g63H6
  | 7 => groupLookup 16 59 4 3 6 4 g63H7
  | 8 => groupLookup 483 1973 7 3 11 5 g63H8
  | 9 => groupLookup 1098 3623 10 3 12 6 g63H9
  | 10 => groupLookup 289 967 9 3 10 4 g63H10
  | 11 => groupLookup 14 53 6 1 6 1 g63H11
  | _ => fun _ => none
def g63 : Forest := ⟨63,11,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
abbrev SixBits := Bool × Bool × Bool × Bool × Bool × Bool
abbrev SixRows := Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512
def readSix (r : SixRows) (v : Sig) : SixBits := ⟨bit r.1 v,bit r.2.1 v,bit r.2.2.1 v,bit r.2.2.2.1 v,bit r.2.2.2.2.1 v,bit r.2.2.2.2.2 v⟩
def sixCost (x : SixBits) : Nat := (#[0,2,1,1,1,1,2,0,2,2,2,2,2,2,3,2,1,2,1,2,2,1,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,1,2,2,1,2,1,2,3,2,2,2,2,2,2,0,2,1,1,1,1,2,0] : Array Nat)[1 * x.1.toNat+2 * x.2.1.toNat+4 * x.2.2.1.toNat+8 * x.2.2.2.1.toNat+16 * x.2.2.2.2.1.toNat+32 * x.2.2.2.2.2.toNat]?.getD 3
def crossOp (d : Nat) (a b : Bool) :=
  if d=0 then a && b else if d=1 then a || b else if d=2 then a && !b else !a && b
def applySix (d : Nat) (a b : SixBits) : SixBits := ⟨crossOp d a.1 b.1,crossOp d a.2.1 b.2.1,crossOp d a.2.2.1 b.2.2.1,crossOp d a.2.2.2.1 b.2.2.2.1,crossOp d a.2.2.2.2.1 b.2.2.2.2.1,crossOp d a.2.2.2.2.2 b.2.2.2.2.2⟩
theorem readSix_bin (r : SixRows) (d) (a b : Sig) :
    readSix r (bin d a b) = applySix d (readSix r a) (readSix r b) := by
  simp only [readSix,applySix,bit_bin,crossOp]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem six_cost_binary : ∀ (d : Fin 4) (a b : SixBits),
    sixCost (applySix d a b) ≤ sixCost a + sixCost b := by decide +kernel

theorem measure_live_tree (w : Sig → Nat) (hb : ∀ {d u} (a b), allowed u d →
    w (bin d a b) ≤ w a + w b) {u T k S} (h : Live u T k S) :
    S.card = k+1 → w T ≤ ∑ s ∈ S, w s := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb' ab fr tail ih =>
    intro saturated
    have zU : bin d a b ∉ U := fun m => fr (by simp [m])
    have bound := live_size tail
    rw [Finset.card_insert_of_notMem zU] at bound
    have bc := Finset.card_insert_le (a:=b) (s:=U)
    have ac := Finset.card_insert_le (a:=a) (s:=insert b U)
    have aU : a ∉ insert b U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated
      omega
    have bU : b ∉ U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated ac
      omega
    rw [Finset.card_insert_of_notMem aU,Finset.card_insert_of_notMem bU] at saturated
    have tp : (insert (bin d a b) U).card = k+1 := by rw [Finset.card_insert_of_notMem zU]; omega
    have step := ih tp
    rw [Finset.sum_insert zU] at step
    rw [Finset.sum_insert aU,Finset.sum_insert bU]
    have price := hb a b hd
    omega

theorem six_cut {u T k S} (r : SixRows) (size : S.card = k+1)
    (cost : (∑ s ∈ S, sixCost (readSix r s)) < sixCost (readSix r T)) :
    ∀ t, t ≤ k → ¬ Live u T t S := by
  intro t ht live
  have wid := live_size live
  have eq : S.card=t+1 := by omega
  apply Nat.not_lt_of_ge (measure_live_tree (fun a => sixCost (readSix r a)) (by
    intro d v a b h
    rw [readSix_bin]
    obtain h|h|⟨_,h⟩|⟨_,h⟩ := allowed_four h
    all_goals subst d
    · exact six_cost_binary 0 _ _
    · exact six_cost_binary 1 _ _
    · exact six_cost_binary 2 _ _
    · exact six_cost_binary 3 _ _) live eq) cost
def cubWitness : Array Nat := #[15217471879,37699309116,11929603644,8104396604,22667372058,8104412988,42128253575,28104597041,32152700017,14077486878,11929412238,28104480533,11929408589,15219627797,15253772451,49336631637,22766732377,8104329638,14077420302,64918461745,27857732721,12046590151,37766417724,37934190140,37699308604,22768034970,37699217574,53209245210,15219627285,52970154150,27200540220,15151403785,49621899427,28154811477,64935180387,52970245692,14077470234,28104596529,40921217187,41038761276,8155514684,53309908122,65207838234,15151411851,44619343386,15151403529,8104321446,15219569031,22768033946,40921275441,40921275697,63145775625,22768176444,14312350362,15151536681,37732772646,64918403235,37699217446,28104596657,37766471753,37699284150,44619293454,64851352881,14077603386,22700926106,32152633766,64918461489,15251558791,63145783947,9781928590,22768168122,28343146659,22667505210,23375349564,42262403185,65191040277,28070925717,37766326950,41532535175,23460467110,14077420046,11929412110,32599716491,15219635607,15186547079,7869923994,28104613173,27200348814,14077419790,14077158158,12250221372,22701067580,32706154887,48982418190,14381289813,57827942727,64935192870,14077569123,15150354953,28104480021,58850816391,46817370766,7701541511,28104595505,29432222217,15151553325,63196127886,28154973756,15150895885,22768043097,58884903303,53037354300]
def fusedTag (k i : Nat) : Nat :=
  match k with
  | 5 => ((#[0] : Array Nat)[i-0]?.getD 0)
  | 6 => ((#[1,2,2,3,4,5,1,6,7,8,9,1,10,3,11,12,4,1,1,13,14,1,1,15,16,17,10,18,1,1,19,20,4,21,22,4,23,17,1,4] : Array Nat)[i-4]?.getD 0)
  | 7 => ((#[24,25,26,27,4,28,22,29,30,31,25,1,32,33,34,35,26,1,1,36,26,14,37,36,14,25,4,4,38,19,14,34,1,22,26,4,33,4,18,1,4,39,1,40,4,41,1,4,22,1,6,1,42,1,1,4,25,4,5,43,44,5,37,4,45,25,7,1,46,35,25,1,1,47,26,48,1,4,35,18,10,19,26,36,18,22,49,1,14,1,50,4,51,36,1,26,26,22,4,35,1,26,2,52,10,31,33,53,1,26,26,4,1,26,10,25,9,54,52,55,45,56,49,1,57,58,10,41,4,35,10,26,35,59,60,18,22,1,1,27,61,4,1,56,1,22,14,33,4,1,28,1,62,55,35,28,4,18,48,34,35,4,26,63,1,1,34,4,1,49,37,22,64,1,10,4,1,65,22,1,1,10,1,1,66,10,26,67,34,4,18,14,26,22,56,35,29,1,26,10,1,1,26,26,25,1,68,25,56,1,25,4,1,22,1,56,1,27,14,26,35,4,4,25,56,4,14,34,26,66,1,56,4,4,4,1,66,26,69,4,42,1,18,25,4,14,10,70,52,26,26,36,4,1,11,33,1,1,25,26,45,31,35,14,10,14,36,1,51,60,56,5,1,18,1,26,10,37,1,31,71,4,4,18,1,33,2,1,1,14,22,2,34,55,1,2,18,1,1,52,10,4,4,4,57,36,1,66,14,30,72,1,2,63,56,4,35,73,1,1,35,27,1,27,74,14,14,18,18,2,4,1,75,34,14,76,41,2,1,36,4,4,1,1,4,28,1,46,22,35,18,1,10,22,10,10,22,1,1,22,10,4,43,14,14,38,45,60,1,22,4,25,1,22,45,56,36,4,61,56,33,1,4,72,25,34,56,77,26,56,4,22,22,25,26,4,10,35,26,1,41,35,18,36,18,2,22,1,1,1,4,78,18,14,22,72,1,10,37,1,4,1,35,66,26,79,22,22,22,22,36,80,26,1,1,34,36,37,27,73,42,14,81,1,27,82,26,22,33,1,52,61,36,22,4,14,10,4,73,4,35,83,2,1,27,1,1,41,1,1,84,14,7,14,4,22,1,14,26,36,38,1,18,26,75,1,1,35,1,1,4,37,85,86,26,1,36,52,1,14,1,1,25,4,1,18,87,33,18,1,1,10,25,26,1,1,26,1,88,35,22,4,2,1,45,89,22,1,22,13,14,60,33,4,14,90,1,10,25,14,4,5,1,1,56,91,34,4,92,18,36,11,25,57,4,56,36,26,26,60,87,37,22,30,36,4,1,93,33,26,4,94,55,26,22,1,1,43,37,56,26,45,37,4,26,72,25,26,33,56,4,4,14,71,37,36,56,7,4,26,1,1,18,2,26,22,10,26,35,4,10,4,1,10,2,1,26,56,14,22,22,1,14,71,4,14,95,22,26,26,18,14,14,4,2,26,1,1,24,39,96,36,68,34,36,18,25,96,63,2,1,33,97,26,1,18,98,1,26,99,41,14,1,70,4,100,22,18,45,1,46,27,4,36,1,33,70,101,1,102,1,1,26,4,25,20,1,25,9,14,1,56,4,4,1,37,45,2,10,89,34,19,4,1,1,3,46,103,4,10,1,31,1,104,1,4,18,26,52,4,52,22,19,18,14,25,7,4,31,45,14,4,4,25,34,35,10,4,105,1,1,1,14,71,25,33,51,4,26,4,4,35,1,2,1,4,106,34,107,75,22,86,40,0,4,56,87,22,100,33,1,1,34,97,4,14,73,1,10,4,22,14,49,36,26,1,1,9,84,26,25,11,1,22,26,99,4,1,35,26,102,27,32,66,108,25,1,25,4,22,14,22,36,25,30,4,4,2,1,33,10,90,14,109,10,35,75,25,37,1,4,25,47,52,33,4,106,4,110,2,26,73,26,1,19,35,33,87,13,4,10,22,18,34,22,56,1,1,45,22,87,1,96,18,18,18,22,80,14,34,71,4,26,4,22,43,26,107,1,4,26,33,4,1,1,10,2,25,1,26,1,99,4,22,22,4,1,56,1,1,33,22,26,2,76,4,14,84,35,106,42,1,37,33,72,62,29] : Array Nat)[i-46]?.getD 0)
  | 8 => ((#[68,111,25,22,35,25,26,4,26,4,66,26,35,33,27,33,107,4,66,26,4,111,25,27,34,110,25,68,26,107,26,26,1,27,27,37,35,27,33,27,27,26,1,75,26,4,33,25,96,34,26,27,4,4,34,26,111,110,27,35,52,25,26,4,35,111,33,4,34,26,27,34,111,18,37,33,75,27,33,27,18,4,68,38,26,35,41,35,25,4,25,27,1,35,26,35,4,26,35,34,4,37,4,41,4,26,25,26,33,35,52,26,22,35,26,110,35,26,26,4,52,110,33,10,4,25,26,22,68,4,33,111,34,4,33,68,4,27,110,26,33,33,106,4,26,22,107,10,4,37,106,52,33,33,4,10,68,68,35,35,75,110,37,33,33,25,35,27,4,111,39,27,18,37,26,26,33,37,4,27,27,4,35,25,34,35,25,111,27,34,110,18,26,68,107,33,66,33,27,35,42,4,4,35,27,26,27,35,4,1,111,33,33,27,27,26,96,1,4,1,4,26,27,34,33,26,22,35,25,33,33,35,10,4,37,4,34,4,26,37,106,26,66,27,10,25,27,66,22,107,10,34,35,27,96,39,25,68,38,106,33,26,27] : Array Nat)[i-638]?.getD 0)
  | _ => 0
def spanOK (g : Forest) (k start n : Nat) : Prop :=
  ∀ i, start ≤ i → i < start+n →
    nodeVerified g k i = true ∨ Impossible g.mode (targetOf g) k (stateSet g k i).toFinset

theorem spanOld {g k a n} (h : block g k a n = true) : spanOK g k a n :=
  fun i lo hi => Or.inl (block_at h i lo hi)

namespace Nat92GE

def viewBank32 (rows : Fin 32 → Row) (ws : List Decor) : List Probe32 :=
  ws.map (fun w => sample32 rows w.1)
theorem sample32_zero (rows : Fin 32 → Row) : sample32 rows zero = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have v := sample32_read rows zero ⟨j,hj⟩
  simpa [view32,bit_zero] using v
theorem bankGet32 (r : Fin 32 → Row) (ds : List Decor) (i : Nat) :
    (viewBank32 r ds).getD i 0 = sample32 r (ds.getD i defaultDecor).1 := by
  simp only [viewBank32,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ds[i]? with
  | none => exact (sample32_zero r).symm
  | some v => rfl

def program32 (n bits : Nat) (ws : List Probe32) : List Probe32 :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) 0
    let b := ws.getD ((bits >>> 4) &&& 15) 0
    program32 k (bits >>> 10) (ws++[bv ((bits >>> 8) &&& 3) a b])
theorem program32_ok (r : Fin 32 → Row) (n bits : Nat) (ds : List Decor) :
    viewBank32 r (decodeBank n bits ds) = program32 n bits (viewBank32 r ds) := by
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [program32,decodeBank,ih,bankGet32,bankGet32]
    simp only [viewBank32,List.map_append,List.map_cons,List.map_nil,dbin]
    have congrOp (d : Nat) (a b : Sig) : sample32 r (bin d a b) = bv d (sample32 r a) (sample32 r b) := ofRows_bin r d a b
    simp only [congrOp]

def programmed32 (g : Forest) (raw : List Probe32) (k i : Nat) : List Probe32 :=
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  let recp := forestRecord (g.levels k) raw.length i
  selectLive (recp >>> len) (program32 depth (recp &&& ((1 <<< len)-1)) raw)
theorem programmed32_ok (g : Forest) (k i) (raw : List Probe32) (r : Fin 32 → Row)
    (hw : viewBank32 r (wiresOf g) = raw) :
    (stateSet g k i).map (sample32 r) = programmed32 g raw k i := by
  have len : (wiresOf g).length=raw.length := by
    rw [←hw]; simp [viewBank32]
  unfold stateSet readNode programmed32
  rcases g.levels k with ⟨a,d,b,c,e,f,m,data⟩
  simp only [storedDepth,len,List.map_map,selectLive_map]
  rw [←hw,←program32_ok]
  rfl
end Nat92GE

namespace Nat92GE
structure TeachingShape where
  roots : List Probe32
  out : Probe32
  price : Nat
  select : Fin 92 → Fin 32

def TeachingShape.good (s : TeachingShape) : Prop := FacePrice (s.roots.map (lift92 s.select)) s.price ∧ lift92 s.select s.out=goal
def shp0 : TeachingShape := ⟨[0xffffff97,0x16,0x2a,0x4c],0x70,5,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp0V : shp0.good := by
  constructor
  · have eq : shp0.roots.map (lift92 shp0.select) = facet0 := by decide +kernel
    rw [eq]
    exact facetPrice0
  · decide +kernel
def shp1 : TeachingShape := ⟨[0xffffffcb,0xffffffc9,0xffffffd5,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp1V : shp1.good := by
  constructor
  · have eq : shp1.roots.map (lift92 shp1.select) = facet1 := by decide +kernel
    rw [eq]
    exact facetPrice1
  · decide +kernel
def shp2 : TeachingShape := ⟨[0x2a,0x16,0xffffffab,0x4c],0x70,5,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp2V : shp2.good := by
  constructor
  · have eq : shp2.roots.map (lift92 shp2.select) = facet2 := by decide +kernel
    rw [eq]
    exact facetPrice2
  · decide +kernel
def shp3 : TeachingShape := ⟨[0x3a,0x16,0xffffffab,0x4c],0x70,5,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp3V : shp3.good := by
  constructor
  · have eq : shp3.roots.map (lift92 shp3.select) = facet3 := by decide +kernel
    rw [eq]
    exact facetPrice3
  · decide +kernel
def shp4 : TeachingShape := ⟨[0xffffff33,0xffffff55,0xffffff69,0x8e],0xf0,6,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp4V : shp4.good := by
  constructor
  · have eq : shp4.roots.map (lift92 shp4.select) = facet4 := by decide +kernel
    rw [eq]
    exact facetPrice4
  · decide +kernel
def shp5 : TeachingShape := ⟨[0x12,0xffffffcd,0xffffffd1,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp5V : shp5.good := by
  constructor
  · have eq : shp5.roots.map (lift92 shp5.select) = facet5 := by decide +kernel
    rw [eq]
    exact facetPrice5
  · decide +kernel
def shp6 : TeachingShape := ⟨[0xffffffd3,0xffffffcd,0xffffffd1,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp6V : shp6.good := by
  constructor
  · have eq : shp6.roots.map (lift92 shp6.select) = facet6 := by decide +kernel
    rw [eq]
    exact facetPrice6
  · decide +kernel
def shp7 : TeachingShape := ⟨[0xffffffdb,0xffffffcd,0xffffffd1,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp7V : shp7.good := by
  constructor
  · have eq : shp7.roots.map (lift92 shp7.select) = facet7 := by decide +kernel
    rw [eq]
    exact facetPrice7
  · decide +kernel
def shp8 : TeachingShape := ⟨[0xfffffe23,0x22,0x4e,0x94,0x118],0x1e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp8V : shp8.good := by
  constructor
  · have eq : shp8.roots.map (lift92 shp8.select) = teaching0 := by decide +kernel
    rw [eq]
    exact teachingPrice0
  · decide +kernel
def shp9 : TeachingShape := ⟨[0xffffff33,0xffffff31,0xffffff55,0xffffff69,0x8e],0xf0,6,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp9V : shp9.good := by
  constructor
  · have eq : shp9.roots.map (lift92 shp9.select) = teaching1 := by decide +kernel
    rw [eq]
    exact teachingPrice1
  · decide +kernel
def shp10 : TeachingShape := ⟨[0xfffffd47,0x146,0xfffffc6b,0x192,0x21c],0x3e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9,9,9,9,9,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp10V : shp10.good := by
  constructor
  · have eq : shp10.roots.map (lift92 shp10.select) = teaching2 := by decide +kernel
    rw [eq]
    exact teachingPrice2
  · decide +kernel
def shp11 : TeachingShape := ⟨[0x7c,0xfffffea9,0xfffffe3d,0xce,0x110],0x1e0,6,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp11V : shp11.good := by
  constructor
  · have eq : shp11.roots.map (lift92 shp11.select) = teaching3 := by decide +kernel
    rw [eq]
    exact teachingPrice3
  · decide +kernel
def shp12 : TeachingShape := ⟨[0xfffffac7,0x18e,0xfffff913,0x224,0x438],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp12V : shp12.good := by
  constructor
  · have eq : shp12.roots.map (lift92 shp12.select) = teaching4 := by decide +kernel
    rw [eq]
    exact teachingPrice4
  · decide +kernel
def shp13 : TeachingShape := ⟨[0xffff255b,0xffff49a3,0xffff0e0d,0x700e,0x8030],0xffc0,8,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,0,3,0,2,3,1,4,5,1,3,0,4,5,0,2,2,1,3,2,4,5,2,5,2,4,3,4,5,1,1,3,6,7,8,9,10,11,12,13,14,15,6,7,8,8,9,10,10,11,12,13,14,15,15,6,6,7,8,8,9,10,11,12,12,13,13,14,6,6,7,7,8,9,9,10,11,11] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp13V : shp13.good := by
  constructor
  · have eq : shp13.roots.map (lift92 shp13.select) = teaching5 := by decide +kernel
    rw [eq]
    exact teachingPrice5
  · decide +kernel
def shp14 : TeachingShape := ⟨[0xfffffd67,0xfffffcab,0xfffffcc1,0x112,0x21c],0x3e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9,9,9,9,9,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp14V : shp14.good := by
  constructor
  · have eq : shp14.roots.map (lift92 shp14.select) = teaching6 := by decide +kernel
    rw [eq]
    exact teachingPrice6
  · decide +kernel
def shp15 : TeachingShape := ⟨[0x2e6,0xfffffc35,0x14a,0xfffff983,0x60c],0x7f0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,8,8,8,8,9,9,9,9,10,10,10,10,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp15V : shp15.good := by
  constructor
  · have eq : shp15.roots.map (lift92 shp15.select) = teaching7 := by decide +kernel
    rw [eq]
    exact teachingPrice7
  · decide +kernel
def shp16 : TeachingShape := ⟨[0x46,0x56,0xfffffe11,0x8a,0x10c,0x210],0x3e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9,9,9,9,9,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp16V : shp16.good := by
  constructor
  · have eq : shp16.roots.map (lift92 shp16.select) = sixface0 := by decide +kernel
    rw [eq]
    exact sixfacePrice0
  · decide +kernel
def shp17 : TeachingShape := ⟨[0x902,0xfffff67d,0xb6e,0x308,0x250,0xc60],0xf80,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9,9,9,9,10,10,10,10,10,10,10,11,11,11,11,11,11,11,7,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp17V : shp17.good := by
  constructor
  · have eq : shp17.roots.map (lift92 shp17.select) = sixface1 := by decide +kernel
    rw [eq]
    exact sixfacePrice1
  · decide +kernel
def shp18 : TeachingShape := ⟨[0xfffffd3d,0xfffffd3d,0x3b6,0x184,0x528,0x630],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp18V : shp18.good := by
  constructor
  · have eq : shp18.roots.map (lift92 shp18.select) = sixface2 := by decide +kernel
    rw [eq]
    exact sixfacePrice2
  · decide +kernel
def shp19 : TeachingShape := ⟨[0xfffffaa9,0xfffffaa9,0x53e,0x424,0x188,0x630],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp19V : shp19.good := by
  constructor
  · have eq : shp19.roots.map (lift92 shp19.select) = sixface3 := by decide +kernel
    rw [eq]
    exact sixfacePrice3
  · decide +kernel
def shp20 : TeachingShape := ⟨[0x754,0x754,0xfffffd75,0x676,0x358,0x460],0x780,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9,9,9,9,10,10,10,10,10,10,10,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp20V : shp20.good := by
  constructor
  · have eq : shp20.roots.map (lift92 shp20.select) = sixface4 := by decide +kernel
    rw [eq]
    exact sixfacePrice4
  · decide +kernel
def shp21 : TeachingShape := ⟨[0xfffff431,0xfffff6b5,0xb3e,0x384,0x228,0xc30],0xfc0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,11,11,11,11,11,11,6,6,6,6,6,6,7,7,7,7] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp21V : shp21.good := by
  constructor
  · have eq : shp21.roots.map (lift92 shp21.select) = sixface5 := by decide +kernel
    rw [eq]
    exact sixfacePrice5
  · decide +kernel
def shp22 : TeachingShape := ⟨[0x310,0xfffffc69,0x112,0x254,0x758,0x460],0x780,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9,9,9,9,10,10,10,10,10,10,10,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp22V : shp22.good := by
  constructor
  · have eq : shp22.roots.map (lift92 shp22.select) = sixface6 := by decide +kernel
    rw [eq]
    exact sixfacePrice6
  · decide +kernel
def shp23 : TeachingShape := ⟨[0xfffffbb5,0xfffffbb5,0x53e,0x184,0x528,0x630],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp23V : shp23.good := by
  constructor
  · have eq : shp23.roots.map (lift92 shp23.select) = sixface7 := by decide +kernel
    rw [eq]
    exact sixfacePrice7
  · decide +kernel
def shp24 : TeachingShape := ⟨[0xfffff2bb,0xfffff2bb,0x89a,0xd2c,0x188,0xe30],0xfc0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,11,11,11,11,11,11,6,6,6,6,6,6,7,7,7,7] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp24V : shp24.good := by
  constructor
  · have eq : shp24.roots.map (lift92 shp24.select) = sixface8 := by decide +kernel
    rw [eq]
    exact sixfacePrice8
  · decide +kernel
def shp25 : TeachingShape := ⟨[0x6d6,0x4d6,0xfffffaed,0x646,0x888,0xcf0],0xf00,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,11,11,11,11,11,11,11,11,8,8,8,8,8,8,8,8,9,9,9,9,9,9] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp25V : shp25.good := by
  constructor
  · have eq : shp25.roots.map (lift92 shp25.select) = sixface9 := by decide +kernel
    rw [eq]
    exact sixfacePrice9
  · decide +kernel
def shp26 : TeachingShape := ⟨[0xffffecb5,0x476,0x1018,0x2a0,0x430,0x18c0],0x1f00,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,11,11,11,11,11,11,11,11,12,12,12,12,12,12,12,12,8,8,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp26V : shp26.good := by
  constructor
  · have eq : shp26.roots.map (lift92 shp26.select) = sixface10 := by decide +kernel
    rw [eq]
    exact sixfacePrice10
  · decide +kernel
def shp27 : TeachingShape := ⟨[0xffff1c65,0x4026,0x2ad0,0xb0d8,0x3c60,0xc080],0xff00,8,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,7,1,3,4,0,5,6,6,4,6,1,3,2,4,0,3,7,6,0,5,0,3,5,3,7,2,4,5,7,2,6,1,3,2,4,2,0,3,5,8,9,10,11,12,13,14,15,8,8,9,10,10,11,12,13,13,14,15,8,8,9,9,9,10,11,11,12,12,12,13,13,14,15,8,8,9,9,10,10,11,11,12,14,14,14] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp27V : shp27.good := by
  constructor
  · have eq : shp27.roots.map (lift92 shp27.select) = sixface11 := by decide +kernel
    rw [eq]
    exact sixfacePrice11
  · decide +kernel
def shp28 : TeachingShape := ⟨[0x2ad68,0xfffd0631,0x1afbe,0x1a43c,0x22800,0x3cfc0],0x3f000,8,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,7,8,9,10,11,1,3,6,7,8,10,9,6,2,7,2,5,11,0,1,9,2,5,6,7,11,2,5,7,8,3,4,8,9,4,8,10,11,1,12,13,14,15,16,17,12,13,14,15,16,17,12,13,14,14,15,15,16,17,12,12,13,13,13,14,14,14,15,15,15,15,15,16,16,16,17,12,12,12,12,13,13,13,14,15] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp28V : shp28.good := by
  constructor
  · have eq : shp28.roots.map (lift92 shp28.select) = sixface12 := by decide +kernel
    rw [eq]
    exact sixfacePrice12
  · decide +kernel
def shp29 : TeachingShape := ⟨[0xfffff77d,0xfffff57d,0xe6e,0xa76,0x338,0xc40],0xf80,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9,9,9,9,10,10,10,10,10,10,10,11,11,11,11,11,11,11,7,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp29V : shp29.good := by
  constructor
  · have eq : shp29.roots.map (lift92 shp29.select) = sixface13 := by decide +kernel
    rw [eq]
    exact sixfacePrice13
  · decide +kernel
def shp30 : TeachingShape := ⟨[0xfffe0841,0xfffed295,0x8326,0x123f8,0x2040,0x1c380],0x1fc00,8,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,7,8,9,1,3,0,0,4,6,7,2,9,3,7,8,2,4,5,3,6,1,3,7,4,5,0,2,9,1,7,8,4,5,9,6,8,2,4,5,10,11,12,13,14,15,16,10,11,12,10,10,11,12,12,13,14,15,15,16,16,16,10,10,10,11,11,12,12,12,13,13,14,14,14,15,15,15,16,16,16,10,10,11,11,11] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp30V : shp30.good := by
  constructor
  · have eq : shp30.roots.map (lift92 shp30.select) = sixface14 := by decide +kernel
    rw [eq]
    exact sixfacePrice14
  · decide +kernel
def shp31 : TeachingShape := ⟨[0xfffff7fd,0x13a6,0x66c8,0xa770,0x3380,0xc400],0xf800,8,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,7,8,9,10,1,2,7,8,6,9,10,10,2,3,4,0,5,9,3,4,8,10,0,6,0,5,6,6,3,4,0,5,2,4,7,2,3,8,7,11,12,13,14,15,11,12,13,14,15,11,11,12,12,12,13,13,14,15,11,11,11,12,12,12,13,13,13,13,14,14,15,15,15,11,12,12,13,13,14,14,14,15,15,15,11] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp31V : shp31.good := by
  constructor
  · have eq : shp31.roots.map (lift92 shp31.select) = sixface15 := by decide +kernel
    rw [eq]
    exact sixfacePrice15
  · decide +kernel
def shp32 : TeachingShape := ⟨[0xfffffafd,0xffffeaf9,0x12ec,0x14be,0x630,0x18c0],0x1f00,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,2,3,4,5,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,11,11,11,11,11,11,11,11,12,12,12,12,12,12,12,12,8,8,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp32V : shp32.good := by
  constructor
  · have eq : shp32.roots.map (lift92 shp32.select) = sixface16 := by decide +kernel
    rw [eq]
    exact sixfacePrice16
  · decide +kernel
def shp33 : TeachingShape := ⟨[0x304,0xfffffcb9,0x326,0x284,0x528,0x630],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp33V : shp33.good := by
  constructor
  · have eq : shp33.roots.map (lift92 shp33.select) = sixface17 := by decide +kernel
    rw [eq]
    exact sixfacePrice17
  · decide +kernel
def shp34 : TeachingShape := ⟨[0xfffffb9b,0xfffff999,0x20a,0x32a,0x434,0x7b8],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp34V : shp34.good := by
  constructor
  · have eq : shp34.roots.map (lift92 shp34.select) = sixface18 := by decide +kernel
    rw [eq]
    exact sixfacePrice18
  · decide +kernel
def shp35 : TeachingShape := ⟨[0x172a,0xffffed7d,0x167e,0x728,0x1440,0x1870],0x1f80,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9,9,9,9,10,10,10,10,10,10,10,11,11,11,11,11,11,11,12,12,12,12,12,12,12,7,7,7,7] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp35V : shp35.good := by
  constructor
  · have eq : shp35.roots.map (lift92 shp35.select) = sixface19 := by decide +kernel
    rw [eq]
    exact sixfacePrice19
  · decide +kernel
def shp36 : TeachingShape := ⟨[0x502,0xfffffabd,0x59e,0x52e,0x188,0x630],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp36V : shp36.good := by
  constructor
  · have eq : shp36.roots.map (lift92 shp36.select) = sixface20 := by decide +kernel
    rw [eq]
    exact sixfacePrice20
  · decide +kernel
def shp37 : TeachingShape := ⟨[0xfffffbb9,0xfffffaa9,0xfffffeb5,0x53e,0x198,0x620],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem shp37V : shp37.good := by
  constructor
  · have eq : shp37.roots.map (lift92 shp37.select) = sixface21 := by decide +kernel
    rw [eq]
    exact sixfacePrice21
  · decide +kernel
def selectTeaching : Nat → {s : TeachingShape // s.good}
  | 1 => ⟨shp1,shp1V⟩
  | 2 => ⟨shp2,shp2V⟩
  | 3 => ⟨shp3,shp3V⟩
  | 4 => ⟨shp4,shp4V⟩
  | 5 => ⟨shp5,shp5V⟩
  | 6 => ⟨shp6,shp6V⟩
  | 7 => ⟨shp7,shp7V⟩
  | 8 => ⟨shp8,shp8V⟩
  | 9 => ⟨shp9,shp9V⟩
  | 10 => ⟨shp10,shp10V⟩
  | 11 => ⟨shp11,shp11V⟩
  | 12 => ⟨shp12,shp12V⟩
  | 13 => ⟨shp13,shp13V⟩
  | 14 => ⟨shp14,shp14V⟩
  | 15 => ⟨shp15,shp15V⟩
  | 16 => ⟨shp16,shp16V⟩
  | 17 => ⟨shp17,shp17V⟩
  | 18 => ⟨shp18,shp18V⟩
  | 19 => ⟨shp19,shp19V⟩
  | 20 => ⟨shp20,shp20V⟩
  | 21 => ⟨shp21,shp21V⟩
  | 22 => ⟨shp22,shp22V⟩
  | 23 => ⟨shp23,shp23V⟩
  | 24 => ⟨shp24,shp24V⟩
  | 25 => ⟨shp25,shp25V⟩
  | 26 => ⟨shp26,shp26V⟩
  | 27 => ⟨shp27,shp27V⟩
  | 28 => ⟨shp28,shp28V⟩
  | 29 => ⟨shp29,shp29V⟩
  | 30 => ⟨shp30,shp30V⟩
  | 31 => ⟨shp31,shp31V⟩
  | 32 => ⟨shp32,shp32V⟩
  | 33 => ⟨shp33,shp33V⟩
  | 34 => ⟨shp34,shp34V⟩
  | 35 => ⟨shp35,shp35V⟩
  | 36 => ⟨shp36,shp36V⟩
  | 37 => ⟨shp37,shp37V⟩
  | _ => ⟨shp0,shp0V⟩
def chartTeaching : Array (Nat × Nat × Nat) := #[(9,8,0x15260a54735a),(1,6,0xf2d56c705),(0,7,0x1a39529015c),(16,10,0xb478e69ec0c68a5),(9,8,0xea98f1ab8ca1),(0,7,0xb6b12a1c11),(0,7,0x15c76456cb4),(0,7,0x1c58578d1d5),(0,7,0x3459cdbc79d),(0,7,0x23c5a84a613),(11,9,0x298f1eb8cb086a),(0,7,0xe255296445),(22,11,0x55b470737655ef1d),(24,12,0x9b6f1525ed2c05631c),(3,7,0x31f15d11738),(1,6,0x1e6b4616c),(0,7,0x26f3ab2ae32),(0,7,0x724e14630a),(9,8,0xf19571738911),(5,6,0x3891c6303),(0,7,0x38aa1eb18e9),(8,9,0x78e6d431a2d25),(9,8,0x474e1cc5567c),(25,12,0xf2325a921e227010d8),(0,7,0x755a14a613),(25,12,0x28559c2c738d69755e),(4,8,0x878caac698fa),(10,10,0x29148519a389547),(3,7,0x32b21f33b6e),(0,7,0x78e60c68a4),(0,7,0x1957c478d1c),(7,6,0xf3165ce11),(4,8,0x15858a5491da),(0,7,0x32aa1eb1a63),(0,7,0x16d1cd9df15),(23,11,0x3c5661c9c10b06305),(1,6,0x1cd38518c),(1,6,0x2c7383286),(0,7,0x1ce11f15c59),(3,7,0x34e32e76ebc),(1,6,0x347385306),(0,7,0x38711f31559),(12,11,0x2ae25b28eabbbcb69),(0,7,0x25d2cd6df26),(10,10,0x3a93631cc1a2843),(0,7,0x318fa878ab2),(18,11,0x11725b3855dc6df39),(0,7,0x221839a31cb),(30,17,((0x3c39ee5acf <<< 64) + 0xa32c720a18e0aa93)),(0,7,0xe9bc19cd2c),(0,7,0x38713f335d9),(0,7,0x2aca1ea9c63),(0,7,0x298fa878caa),(0,7,0x19c7c45cd38),(10,10,0x55a64e35115628c),(16,10,0xd478e69f40c68a5),(16,10,0x8b4b25923f35b66),(0,7,0x29d7c96cd38),(1,6,0xf2dd6cd25),(0,7,0x38ca1ea98f1),(3,7,0x91ce0c0185),(11,9,0x19571f38d3045c),(0,7,0x2ae21ea3c69),(4,8,0x29444568e2d5),(0,7,0x34711f31655),(4,8,0xf15c59d1cc11),(0,7,0xe69528545c),(10,10,0xf077a3e9ce250e2),(16,10,0x1462b20953b6e87),(35,13,0x3c9953473b4864144306),(4,8,0xea3a71aa2e21),(3,7,0x9c7c44cd21),(0,7,0x38713f335da),(11,9,0x34e1c45565df31),(12,11,0x31aa8821cb8e6e9a),(31,16,((0x8f125a5e <<< 64) + 0x120a601083452593)),(0,7,0x23c7a86ae32),(1,6,0xb1c17cb55),(7,6,0x878aa3a7a),(7,6,0x86acb18fa),(17,12,0xb254dcd239f15f7f35),(24,12,0x9aef2bc7ab3486ac38),(1,6,0x8c7983886),(35,13,0xc5aae32d0e69eebef36),(0,7,0x23a7a862e2a),(0,7,0x29c7c86cd38),(3,7,0x2a878a7ac63),(0,7,0x23a7a872e2a),(8,9,0x78e6b431a2b25),(0,7,0x755a14a616),(0,7,0x3496cd7cb66),(1,6,0x5b47367bc),(0,7,0x31a7c874930),(0,7,0x164ca5ce2da),(1,6,0x30614e347),(33,11,0x529c4d634755a797),(16,10,0x1b486c90ec7ca66),(12,11,0x2ae05b28eabbbc369),(15,11,0x1a2d534739e4ca15c),(18,11,0x3199a387ca244a181),(3,7,0x328668738b),(10,10,0x3992d51ca19c445),(24,12,0xa8a0cc9462e3b4e9c7),(1,6,0x3872c6283),(22,11,0x6b3494e1fc9add67),(31,16,((0x7054ea19 <<< 64) + 0x5cfa8d7f9e1ee98e)),(12,11,0x261f18e71a4883865),(7,6,0x14c28724e),(28,18,((0x85ce11a93a7 <<< 64) + 0xc779671f9ee9a6d7)),(0,7,0x3459cdbc795),(0,7,0x78e60c68b4),(1,6,0x18a0ce1cb),(9,8,0x465e1cc5567c),(0,7,0x1af36716d32),(20,11,0x3c65a8dc9180f8862),(0,7,0x31a7c874938),(16,10,0x47459c519dbc795),(1,6,0xab887a8f1),(11,9,0x34738471679f15),(9,8,0xea98f1ab88a1),(1,6,0x843323a4e),(4,8,0xea3a71ab2e21),(0,7,0x34cb8dbceb1),(20,11,0x2339a56a84a703151),(0,7,0x221839a31da),(3,7,0x91ce0cc185),(9,8,0x29c44568e2d5),(24,12,0x9aeeadc7cab286cc38),(0,7,0x388a1eb18e9),(9,8,0x872e2ac63a7a),(1,6,0x14630734e),(0,7,0x2dd7c96cd38),(0,7,0x15c664468a5),(1,6,0x2da5ca0d2),(0,7,0x3167c474738),(9,8,0xf15671734e11),(1,6,0xe2a87ac63),(11,9,0x318e9eb8aa8862),(1,6,0xbbaf2ab38),(36,11,0x2a0ec9462e3b6fb87),(1,6,0xcd7d93c96),(11,9,0x2acb8869c79ea3),(8,9,0x231e6a43886a21),(8,9,0x221836268c765a),(0,7,0x3496cd7cb6e),(0,7,0x724e0c628c),(0,7,0xe6bc2ace1c),(18,11,0x36c5a655cb0598454),(8,9,0x221832a68c72da),(16,10,0x874cb8c29dbceb1),(0,7,0x38713f335db),(18,11,0x368da2c7ca258a0c6),(1,6,0xb3497cb75),(16,10,0x878b2aa23f3aba9),(0,7,0x23c5a842613),(26,13,0x2115c4d11c97bcc5d655),(26,13,0x345c945c49f1e1d9355),(21,12,0x8e668b387ca244a0c6),(1,6,0xb2286eb63),(1,6,0x73847c771),(0,7,0x15c7c45ce34),(9,8,0xf31559d38711),(8,9,0x231e6a43886b25),(1,6,0x8e6562874),(9,8,0xf19571738d11),(0,7,0x734e14630a),(3,7,0xdc7c44cc21),(7,6,0x4f2e1bc7a),(0,7,0x38d11f19571),(0,7,0x263bc1b472c),(20,11,0xa71615a2de54e347),(27,16,((0x4c2e1cb0 <<< 64) + 0xca8acfc37a68f2ce)),(20,11,0x559329535768738b),(0,7,0x15c7c45cc34),(16,10,0x96ce2aa27f2eea9),(0,7,0x9395291585),(1,6,0xca18b1ce),(0,7,0x1114a55a389),(1,6,0x1ce34614c),(1,6,0xb38abcbba),(0,7,0x298fa878c2a),(3,7,0x1c4f45fccdb),(0,7,0x29c7a86acb8),(0,7,0x2519c9bc795),(16,10,0x86ce2aa23f2eea9),(0,7,0x32d21da39f1),(4,8,0x15848a54d1da),(10,10,0xf885c1631daf0d),(32,13,0x1c14a4c67556cb7de387),(1,6,0x4f25b35f6),(7,6,0x47871567c),(0,7,0x1567c474e1c),(25,12,0x14a59334e1cb55e697),(20,11,0x3d25e156f5f23eb9),(1,6,0x38d1cc185),(0,7,0x9387305183),(0,7,0xb695285511),(24,12,0x69ed9dc7c5b245cc34),(29,12,0xb25a831adacb8efb87),(18,11,0x3c5661cdd14b0614c),(7,6,0x456d31576),(0,7,0x31a7c874b38),(36,11,0x26c4e695870280191),(8,9,0x78e6b431a2925),(9,8,0x15360a54735a),(25,12,0x2857162cd38769d55e),(18,11,0x3199a387c2044a181),(10,10,0x9b18d51e21b4445),(8,9,0x3459c476f1e655),(11,9,0x31a63eb2aa2878),(8,9,0x34b251bcd6d1e6),(14,10,0x156b347073557bc),(9,8,0x86ae32a63c7a),(17,12,0xc939745a3cc7d77d97),(8,9,0x2cab886ef3ac69),(35,13,0x3c566387374594184305),(12,11,0x261e98e71a4883865),(8,9,0x3471617cd9e1d5),(0,7,0x32593db35da),(8,9,0x38b2a87ceae8e9),(35,13,0x3c9953473b4964144306),(15,11,0x151da38b35d4c529c),(19,11,0x3c54e1cdd1c1ac305),(17,12,0x9a368e1f2893282183),(16,10,0x17459c50ddbc795),(16,10,0x632593499db35da),(9,8,0xea3a71ab2e21),(17,12,0x1e368e9930f22821a2),(17,12,0x8e668b1f28962820c6),(9,8,0x878caac698fa),(12,11,0x361f18e75b4c83865),(8,9,0x32593636cd765a),(11,9,0x318e9eb8aa8872),(12,11,0x3cc4d575e2c711165),(8,9,0x1c5b445ef36c55),(26,13,0x110ea9611c9bbac6ba63),(21,12,0x8e668b387ca24ca0c6),(0,7,0xd57c16cd1c),(12,11,0x3c569c7572ce11865),(10,10,0x54e35a645446298),(8,9,0x3892a87ceae8e9),(14,10,0xf0dc5956cd1c151),(16,10,0x432593499db35da),(17,12,0x1e668b8d61b22820e2),(10,10,0x54e35a645456298),(8,9,0x2cd25abcb75ae6),(22,11,0x573458d1fc55ed97),(10,10,0x86aa32c29c63eb6),(8,9,0x34b251bcd691e6),(23,11,0x3cc668e9d30b22a21),(9,8,0x478d1cc5957c),(4,8,0x478d1cc5957c),(12,11,0x22e25b28ea39bcb69),(32,13,0x2a0cc946ae3b4dbee387),(35,13,0x366a31cb3b24d20c218a),(8,9,0x324d62b3d9739a),(10,10,0x15850a1951c968e),(23,11,0x11725b3855dc6de7c),(22,11,0x21e2cab18fca7abab),(8,9,0x16c937365f375e),(4,8,0x47891cc5957c),(10,10,0x8728b8a23a71ebc),(1,6,0xb2a86eb63),(4,8,0x872ab88f1a7a),(8,9,0x34b258bcd6d8e6),(10,10,0x86a8b8c23c69ebc),(4,8,0xea3c69caac21),(23,11,0x3c5661cdd14b06305),(1,6,0xbbceacab8),(16,10,0x86c8b8831bbcea9),(25,12,0x14a4d634b1ce55b697),(31,16,((0x39a255f0 <<< 64) + 0xa04544810c614d1c)),(16,10,0x2b24d648ecf65da),(8,9,0x325932b6cd72da),(14,10,0x1a5734b073a6b7c),(30,17,((0x3c69eb4e9a <<< 64) + 0xe638724a0cb0aa86)),(5,6,0x8b48639b1),(4,8,0x47473857167c),(16,10,0x1b496c90ed7cb66),(7,6,0xba3a6caa1),(27,16,((0x183b1ce1 <<< 64) + 0x8a8a9bc66e39b2da)),(16,10,0x86cab8a31bbcea9),(24,12,0x70c14a4c63556ce5c7),(1,6,0xd9ef16d1c),(35,13,0x368da38b1f2aa2282183),(8,9,0x38d3287ceb68f1),(0,7,0x182856951c9),(11,9,0x32e2a863a6beb1),(30,17,((0x3c69eb4e9a <<< 64) + 0xe638725a0cb0aa86)),(30,17,((0x69642ac70 <<< 64) + 0xc9c799a3ee3ad37c)),(25,12,0xf2324ec21b227010cc),(16,10,0x478cb4c15ebcdb1),(22,11,0x25e2cab59fca7abab),(12,11,0x3cc49575e2c711165),(8,9,0x2470617c99e1d5),(11,9,0x38caa8698ebeb1),(17,12,0x593974c875e3d77db3),(24,12,0x4c32857062da74778e),(10,10,0x478c1c531559f1e),(8,9,0x2ce2a87cbba8e9),(32,13,0x132857066da74d7d71ce),(22,11,0x11e32d1957ac7cdb5),(28,18,((0xf0755ec5ad0 <<< 64) + 0x519459c04345348a)),(8,9,0x16d1c4f67bc6d5),(10,10,0x6a32f164a632851),(28,18,((0xf23c7a55ad2 <<< 64) + 0x18b0cb804345348a)),(23,11,0x3399a387ca24ca0c6),(22,11,0x11d1673167657c79d),(21,12,0x9a368e2c7ca258a183),(11,9,0x31655f34714478),(14,10,0x2940c615a2ce547),(8,9,0x38cb447af36571),(10,10,0x3a93631cc1aa843),(12,11,0x3c6a639ee34b0a196),(34,11,0x5d1618c547d8df0e),(8,9,0x3892287cea68e9),(8,9,0x68832a61e32ce),(29,12,0x8e6a7cd62a38b20874),(18,11,0x3399a387ca24ca183),(37,11,0x25b03a86b632e71ee),(11,9,0x1cd38459c79f15),(22,11,0xa47070b3b169df1e),(12,11,0x2ae25b28ea3bbcb69),(16,10,0x878d32c23f3adb1),(12,11,0x3c99a3aed387062aa),(9,8,0xeb18e9cb8aa1),(18,11,0x35a5d321d78f5db3),(12,11,0x13c9c592cdb5f679a),(12,11,0x13c9c592cd95f679a),(26,13,0x345c945c49f1e1dd355),(34,11,0x3caa2868cbe87d8e),(11,9,0x19c55f1cd14478),(0,7,0x755a14a612),(8,9,0x38b2a83ceae8e9),(10,10,0x9951f18c68b4461),(14,10,0x29687044e2da5f1),(12,11,0x34713594f31d9e5d5),(16,10,0x2b259348bdb35da),(24,12,0x9b6f1735ed2c15631c),(14,10,0x15818c2951c968e),(0,7,0x72ce0c628c),(20,11,0x3c34e8dcc0c0ec862),(10,10,0x8de3fcb4387272c),(12,11,0x1cd13594f197b65d5),(17,12,0x716ab8d0e7a6ebef36),(9,8,0x45ce34655c7c),(8,9,0x34cb8876f3aa71),(8,9,0x38b2287ceae8e9),(8,9,0x2cab896ef3ad69),(30,17,((0x3ca79db157 <<< 64) + 0x5a2ce16930d21951)),(34,11,0x5d1c30654df07d8e),(12,11,0x135b8c925d9cf6e9a),(12,11,0x35aac921cb8f6e9a),(19,11,0x11725b34655b71d7c),(10,10,0x1d935a38519360a),(37,11,0xd1fc99e16cd0c706),(8,9,0x38862a31e638b),(1,6,0xe1c47ce55),(37,11,0x261fc3751ac724d05),(30,17,((0x3c35dd95c7 <<< 64) + 0x532c732914d05951)),(0,7,0xd387305183),(8,9,0x3459c176f1e355),(17,12,0xe2a5b4b1ae8edbef2e),(29,12,0x6716b6f11496c90634),(11,9,0x15671f34e3045c),(18,11,0x3c9951ced2470518c),(8,9,0x3845c2b1f1539a),(13,16,((0x478718c9 <<< 64) + 0x64b4c14c5579af36)),(8,9,0x16d1c4f67bc6d7),(10,10,0x7035a1d1ef098f1),(1,6,0x39a5ca193),(22,11,0x21aace23c6ea7af39),(10,10,0x4f8c9c5b35d9f1e),(18,11,0x3cc668e9d30b22868),(23,11,0x35a5d321d78f5cf6),(20,11,0x11d25a956f5bb1eab),(23,11,0x3c5661c9d14b06305),(14,10,0xf0ecd76ace1c293),(22,11,0x21e34ca98fcc7adb3),(22,11,0x1190673166657c79d),(8,9,0x32e344fadbc5f1),(8,9,0x2ab3886eebcc69),(1,6,0x1e6d46174),(18,11,0x31a59221d78f59b3),(35,13,0x336a61ce2f25921820ca),(19,11,0x3c98d1ced2c15c306),(10,10,0x54e35a645456290),(29,12,0x6556b6f114b2590634),(21,12,0xaac5b2d383ae6b6ebc),(12,11,0x22e25d30ea39bcd71),(22,11,0x6974b073b59adf2e),(16,10,0x1b4b25907f35b66),(17,12,0xd16ab8726d8eebef1e),(12,11,0x11c9c592c5957679a),(5,6,0x19c147395),(14,10,0x29118315a38b547),(11,9,0x1ce34455c75f19),(9,8,0x15858a5491da),(34,11,0x6d2c30598ef07d4d),(8,9,0x34cb8476f3a671),(13,16,((0x874b24ca <<< 64) + 0xa8b8c28c69ba6f3a)),(34,11,0xac930c668bcced87),(19,11,0x11e25b34671b55d7c),(33,11,0xa1537162ce6955de),(26,13,0x3478961549f3a8f9a71),(22,11,0x21cb4e23a76c7af39),(24,12,0x575f273add1c1a532c),(8,9,0x3496c1b5f2d3a6),(11,9,0x31559f38718474),(8,9,0x1673445edbcc55),(17,12,0xb2a5b4e0eb9adbef3a),(18,11,0xab16d383ae6b6f3a),(8,9,0x3abbcdaae2cd32),(15,11,0x1a25534739e44a15c),(14,10,0x156b347072557bc),(8,9,0x34b211bcc691e6),(10,10,0x878c2a8b18e9ea6),(12,11,0x21d2ab24d63a7cba6),(14,10,0x29118315a389547),(4,8,0xf19c55e1cc11),(10,10,0x1d935a38519160a),(0,7,0x78e60c68a5),(1,6,0xd6df25d2c),(10,10,0x45c538c15c59f3a),(36,11,0x1c46c970655b7df31),(14,10,0x1a847084e1e6a71),(12,11,0x115b8c925d9c76e9a),(8,9,0x3ceaed78b2a974),(8,9,0x78e6b431a2b24),(8,9,0x32e344fadbc5f3),(4,8,0xea9c63e2ac21),(8,9,0x325912b6c552da),(11,9,0xd1d569849014a),(9,8,0xf19c55e1cd11),(1,6,0x30518d387),(13,16,((0x974b24ca <<< 64) + 0xa8b8c28d6dba6f3a)),(37,11,0x268fca758ace24d21),(32,13,0x9c5e9bc06119610c734),(8,9,0x2ce2a97cbba9e9),(12,11,0x21b32d24a63c7cda6),(12,11,0x64eac921ce9b3e9a),(4,8,0x4f8d1ccdb5fc),(5,6,0x8ac8639a9),(15,11,0x21d0a6164419b1689),(16,10,0x870b2a823f3aba9),(12,11,0x135b8c925dbcf6e9a),(35,13,0x3399a2ce1f2aa22820c6),(9,8,0x6891d5298485),(13,16,((0x472592e1 <<< 64) + 0xc634c14c5579adbc)),(31,16,((0x68e255f0 <<< 64) + 0xa051148418314d1c)),(0,7,0x96b12a1c91),(16,10,0x45c5b45317bcd95),(10,10,0xf0da55c6cd1c151),(10,10,0x3992d51ca19c405),(13,16,((0x4f2592e1 <<< 64) + 0xc634c14cd779adbc)),(12,11,0x21d2ab24c63a7cba6),(13,16,((0x45ce185b <<< 64) + 0x24b4530571e9af36)),(31,16,((0x1d525acc <<< 64) + 0x520a601083452c93)),(12,11,0x115b8c92559c76e9a),(13,16,((0x2a1ca215 <<< 64) + 0x619105225ada6c55)),(10,10,0x6872d564a616151),(12,11,0x5b16d2434757cda6)]
def pickTeaching (k i : Nat) : Nat :=
  match k with
  | 6 => ((#[0,1,2] : Array Nat)[i-44]?).getD 0
  | 7 => ((#[1,3,4,5,6,7,8,9,10,9,11,12,13,14,15,16,17,18,19,20,21,20,22,23,24,25,23,26,27,28,29,11,30,31,9,20,32,33,34,35,10,36,37,38,23,39,40,41,42,43,44,45,8,4,46,47,48,49,10,50,51,47,52,53,54,20,20,55,20,56,57,58,59,41,38,60,9,61,62,63,64,65,26,63,66,67,41,68,20,69,70,71,33,72,64,6,73,74,26,23,20,75,20,76,37,77,20,78,79,26,80,81,20,9,82,32,83,84,41,25,85,4,86,87,88,52,41,89,90,91,41,92,59,41,9,76,93,94,95,96,41,85,74,7,39,52,63,10,3,97,98,99,100,101,87,102,101,103,104,105,106,107,108,109,96,66,15,110,111,112,41,105,52,63,82,113,114,115,116,117,51,118,19,63,41,52,82,41,119,41,120,20,1,121,122,123,68,124,125,20,64,66,126,24,127,41,128,41,41,41,40,96,129,37,130,102,10,131,123,132,28,133,20,23,88,41,6,134,20,135,1,41,37,26,136,137,81,59,138,23,139,140,12,47,9,141,45,40,20,41,24,142,3,31,41,37,143,41,42,41,20,144,120,145,146,60,147,41,148,132,149,22,72,102,150,41,151,24,152,20,33,76,153,63,38,41,3,41,59,41,154,155,156,38,20,157,72,32,95,20,158,41,159,160,20,101,66,77,8,30,103,114,122,161,32,40,162,163,164,49,165,166,167,168,47,144,20,72,169,170,72,32,20,86,171,20,172,76,8,33,173,41,132,53,149,174,36,171,175,8,176,24,177,160,178,179,86,128,41,180,181,72,37,145,178,182,183,76,66,20,66,10,51,55,184,41,41,41,27,6,45,41,149,185,186,187,20,101,95,188,76,6,86,85,41,31,189,190,20,86,20,20,146,126,19,191,3,64,125,161,7,192,173,36,193,26,20,146,194,195,20,10,122,196,67,80,9,33,197,198,20,85,172,199,53,200,126,20,6,90,51,59,165,4,127,9,40,201,36,63,95,182,10,4,182,20,6,149,20,202,203,204,41,40,7,52,205,1,3,37,1,24,4,41,6,37,122,20,66,6,155,206,41,20,14] : Array Nat)[i-963]?).getD 0
  | 8 => ((#[94,64,207,155,98,4,146,3,88,199,208,102,209,172,22,210,211,212,213,162,214,215,20,33,3,216,217,218,151,21,10,219,220,209,221,41,222,217,223,53,77,220,224,129,129,225,4,226,49,212,151,77,227,147,33,219,4,77,228,102,182,102,4,229,20,230,231,232,233,198,234,226,87,70,101,3,235,41,234,223,20,20,4,210,236,198,41,219,33,192,221,37,229,237,192,90,238,49,85,211,88,41,231,41,239,240,241,231,6,46,41,178,214,236,10,242,228,101,209,208,41,243,26,244,41,219,172,245,146,20,238,146,98,6,209,94,241,3,10,221,20,149,153,246,70,232,247,27,27,248,20,249,210,250,251,77,252,223,253,254,135,33,255,21,256,234,146,226,101,40,135,33,160,226,199,25,231,229,257,41,219,258,94,33,61,259,260,59,261,258,20,146,98,10,262,129,7,263,129,64,85,187,214,87,26,36,164,199,33,19,95,214,264,265,266,244,3,41,129,267,146,268,225,238,33,116,41,46,12,269,270,4,271,73,272,55,273,4,102,274,82,85,229,8,217,235,232,73,33,238,264,168,275,102,141,164,276,3,249,213,26,3,51,26,135,4,4,0,277,33,52,21,3,33,209,278,279,229,41,149,36,3,33,241,20,41,254,149,20,164,280,228,55,218,281,20,126,61,129,3,10,41,3,211,203,282,145,4,170,213,280,55,283,53,223,41,241,214,284,66,4,55,285,49,223,33,102,146,55,261,36,282,214,234,286,41,285,205,250,55,287,6,212,29,224,26,219,21,161,6,4,210,41,288,36,188,289,20,263,4,20,290,229,20,291,258,256,210,0,21,129,41,98,129,33,235,65,274,7,146,64,98,20,292,55,250,76,129,293,294,274,204,20,168,295,41,296,297,164,10,281,298,129,299,219,41,300,274,285,288,236,232,146,40,10,301,287,41,6,41,41,272,77,151,10,210,21,238,198,241,296,229,3,285,229,27,126,241,170,6,302,38,272,55,87,251,129,168,303,55,53,146,177,304,160,214,280,164,155,102,210,33,172,135,49,256,76,229,129,26,164,20,178,19,166,217,281,305,146,33,232,287,306,22,164,20,98,172,41,256,222,41,76,228,3,198,95,98,3,307,308,101,309,22,41,101,164,33,138,22,33,238,229,199,310,251,205,263,311,172,217,250,282,129,198,312,253,49,313,314,105,282,315,146,204,41,251,217,229,20,316,45,155,38,20,20,317,221,231,226,88,195,10,318,27,41,36,319,10,320,3,8,20,264,225,238,149,20,264,129,37,172,85,46,20,102,257,321,229,322,323,209,129,33,324,20,26,325,256,308,191,277,77,82,241,53,147,326,73,4,4,208,3,36,172,27,272,42,178,222,41,10,149,147,55,182,93,12,20,49,280,20,281,20,327,328,232,37,6,255,329,8,236,330,3,3,151,331,33,49,267,217,277,332,307,9,237,222,241,95,10,229,21,170,57,229,149,333,26,10,172,3,212,4,232,56,116,278,6,334,27,3,249,251,101,335,336,164,53,337,20,116,338,76,339,53,340,155,251,27,324,324,20,222,172,341,312,55,33,41,102,146,153,4,342,98,278,198,304,76,343,20,205,238,208,344,216,241,8,102,219,212,3,345,88,85,164,6,49,66,3,59,53,129,244,295,33,186,76,88,346,155,95,55,250,225,36,341,12,222,282,213,347,204,59,188,5,278,33,296,348,349,228,350,9,351,198,49,20,146,319,3,76,98,326,38,82,26,87,44,277,219,24,285,85,129,255,296,222,102,146,229,88,352,353,238,281,7,241,345,251,114,170,26,276,153,6,217,20,102,354,352,355,356,172,318,249,262,98,23,20,82,59,3,20,250,41,296,257,26,20,129,77,357,277,236,210,138,4,4,116,3,238,27,358,164,70,238,50,337,95,76,82,223,263,281,46,20,170,299,9,149,10,212,41,106,283,359,280,256,20,22,360,10,361,277,146,241,149,273,362,33,195,10,41,21,281,363,20,146,55,3,312,126,190,246,20,287,235,285,88,4,212,53,98,27,73,94,212,263,229,219,364,365,22,98,366,280,162,324,20,98,27,311,226,41,361,209,229,209,152,226,21,250,287,164,98,41,264,146,234,367,20,101,10,277,368,208,219,300,296,170,164,221,41,217,175,192,27,369,146,223,46,49,135,3,49,44,296,98,257,20,71,146,49,88,20,77,141,10,324,73,20,170,244,22,95,255,208,3,85,235,49,236,41,237,283,37,94,66,3,141,151,222,370,138,212,33,219,7,153,53,6,151,232,344,20,151,41,304,20,21,151,33,26,10,27,3,353,37,20,10,6,149,371,170,49,372,101,85,286,126,318,373,20,20,374,36,375,53,376,41,36,41,129,77,377,274,53,22,231,138,26,222,3,374,41,41,324,219,198,20,20,307,219,253,235,312,10,237,378,261,219,379,65,20,146,188,129,212,380,381,382,41,354,383,209,207,296,41,3,10,146,164,209,218,145,384,217,129,149,151,337,285,274,101,229,12,20,172,385,244,235,229,350,238,87,10,224,228,37,41,283,87,4,386,6,204,229,281,4,250,212,36,198,282,49,76,3,229,41,93,102,10,10,357,229,20,238,19,225,22,145,98,126,209,49,49,213,88,20,387,388,280,281,361,149,59,214,241,33,33,271,4,208,41,139,389,170,390,27,223,228,212,37,47,98,256,41,391,88,263,20,392,98,33,288,20,129,288,251,26,77,155,226,238,49,129,160,138,22,41,229,293,3,222,221,247,80,6,238,4,4,77,131,235,188,22,6,393,235,195,33,251,281,64,212,334,178,153,236,192,111,4,20,340,146,231,255,164,217,281,244,155,219,10,98,353,213,33,225,205,62,226,209,238,281,226,3,283,98,49,168,250,33,296,385,205,258,220,222,253,98,250,394,129,341,311,244,198,49,255,182,232,387,153,311,395,49,129,229,217,212,293,6,229,27,27,77,27,396,397,179,398,41,20,177,256,64,59,231,94,399,256,36,33,170,146,76,288,41,41,295,73,153,400,211,401,170,22,149,20,20,3,276,383,402,146,33,217,37,262,129,33,219,325,33,225,138,22,41,22,76,250,219,198,165,238,319,220,278,146,281,36,152,271,149,170,403,238,164,222,280,41,20,344,116,210,404,198,20,149,209,264,344,405,126,230,37,101,98,234,209,213,234,387,281,73,296,71,149,95,308,238,236,21,229,41,229,217,328,49,22,406,36,251,146,10,319,41,407,4,87,27,214,235,20,76,102,49,33,198,408,296,263,199,82,53,98,3,209,319,324,129,101,214,212,170,98,251,312,33,409,94,274,210,283,41,238,20,326,232,41,153,36,217,52,319,41,20,20,398,98,287,214,101,410,88,4,47,390,172,57,257,213,195,209,64,170,287,77,258,22,238,324,33,4,229,410,376,411,102,311,129,40,337,219,374,20,319,213,251,146,412,199,41,114,77,324,229,47,82,55,20,231,219,80,251,199,10,234,98,20,59,288,160,116,234,135,149,77,102,399,27,46,288,212,41,308,4,10,6,20,195,27,203,241,98,6,168,98,198,231,241,413,126,27,10,20,20,4,273,414,49,208,232,331,22,76,352,222,26,217,4,401,392,26,415,10,20,55,37,280,20,77,195,20,76,20,129,41,211,236,234,138,263,195,53,344,145,3,49,27,33,73,241,277,76,3,229,324,219,236,98,416,20,417,27,214,198,209,22,3,20,155,219,235,418,244,33,236,362,419,222,85,420,409,237,288,88,170,123,272,145,307,277,9,421,304,73,6,98,41,223,422,221,53,231,59,108,232,59,362,41,20,165,373,407,188,296,36,17,164,296,241,309,263,32,101,287,151,3,146,41,274,45,423,241,345,214,186,232,283,221,273,311,98,424,280,37,26,153,6,88,98,229,425,406,41,217,53,250,37,223,229,145,109,27,191,326,66,76,209,4,250,20,288,228,251,231,426,188,361,165,20,265,3,153,129,98,250,41,229,278,267,238,401,20,85,228,7,229,106,3,55,9,161,309,98,229,363,296,138,281,427,41,237,61,33,238,88,428,49,4,244,164,129,235,146,63,4,166,4,102,429,77,21,20,53,33,222,312,198,274,287,42,296,281,430,10,55,20,33,318,299,151,59,170,77,226,88,313,324,151,126,277,41,82,10,98,22,3,318,234,221,4,41,241,22,222,431,20,20,129,41,164,198,205,22,3,20,129,59,234,243,222,162,66,362,144,219,267,20,187,241,281,314,20,146,20,365,146,59,25,37,172,53,235,336,3,4,238,146,102,386,188,102,217,146,160,41,20,129,228,3,223,7,22,239,312,4,72,296,62,232,282,73,109,432,348,20,77,433,179,256,299,20,223,106,281,326,160,251,172,85,98,71,274,41,285,212,198,88,296,270,4,164,392,216,320,64,304,139,12,88,280,98,160,192,6,129,434,129,435,251,238,346,307,351,3,76,353,139,318,343,234,26,10,146,161,188,436,88,87,98,217,153,55,53,436,287,129,129,324,170,229,33,90,20,418,172,76,172,437,223,61,277,17,424,129,231,21,94,299,198,205,212,281,20,139,438,334,9,205,76,439,251,153,222,192,47,222,328,76,210,55,10,21,229,287,440,287,94,281,441,98,20,164,326,231,229,221,76,226,20,116,146,98,214,278,236,287,241,212,55,257,76,251,281,296,388,4,90,250,219,49,17,442,20,337,286,126,170,443,41,41,20,344,229,10,21,309,4,308,90,444,338,77,151,198,212,188,146,234,67,344,285,198,382,415,204,33,147,312,151,55,254,205,312,352,33,33,263,33,230,88,445,41,129,256,168,225,236,296,191,223,214,85,223,33,232,155,10,19,327,33,281,49,33,229,283,362,46,274,164,87,88,26,214,101,87,285,234,21,20,372,277,116,3,205,7,401,146,446,36,76,96,447,129,232,146,146,41,47,212,64,164,41,23,172,20,170,229,198,205,155,317,446,229,76,388,214,164,49,226,448,98,363,277,20,205,73,208,49,101,6,49,22,258,164,10,234,319,88,424,87,223,3,10,312,73,217,198,87,296,254,53,237,270,8,53,213,199,94,164,238,88,162,208,411,170,411,232,232,246,302,195,21,3,225,409,285,26,184,250,49,4,3,191,236,164,102,41,324,49,132,4,82,33,51,160,64,164,41,324,296,151,151,4,354,263,449,231,20,63,53,49,41,198,172,255,46,326,55,151,192,20,106,262,325,236,222,450,160,53,10,41,408,304,192,94,64,20,12,229,168,324,205,319,3,10,41,244,55,451,452,145,251,27,345,3,155,10,212,77,277,222,41,61,21,431,251,59,305,238,238,10,221,66,73,138,177,308,61,217,135,229,229,22,146,172,7,172,85,453,21,236,266,350,101,95] : Array Nat)[i-901]?).getD 0
  | 9 => ((#[324,454,288,238,238,274,101,217,208,98,231,88,234,98,231,352,255,354,98,238,440,274,88,285,255,264,88,98,98,21,273,367,400,400,455,88,264,367,305,98,231,88,440,234,210,304,448,231,273,312,98,98,456,27,231,217,256,88,88,440,352,367,214,367,367,255,312,98,367,367,98,457,231,274,88,210,352,367,435,211,312,21,98,400,27,217,280,211,234,241,21,273,98,367,304,440,458,304,439,241,244,280,400,219,361,271,399,400,21,27,367,219,27,459,101,214,217,210,400,98,273,400,217,211,440,244,304,98,288,27,274,400,460,217,98,238,101,75,280,256,219,312,27,208,255,440,238,273,244,21,289,238,27,88,352,21,234,255,210,98,219,256,98,274,88,88,354,210,400,219,101,352,271,88,460,98,312,208,214,302,352,219,101,280,256,88,244,214,324,367,238,460,400,255,354,274,21,460,101,400,27,244,256,98,88,352,273,400,219,21,352,210,98,288,256,354,456,460,361,21,219,210,400,460,256,219,214,354,255,448,244,367,461,273,98,354,367,98,440,367,211] : Array Nat)[i-626]?).getD 0
  | _ => 0
def tileRows (w : Nat × Nat × Nat) (r : Fin 32) : Row :=
  Fin.ofNat 512 ((w.2.2 >>> (6*(if r.val<w.2.1 then r.val else 0))) % 64)
def normalLow (w : Probe32) := (w &&& 262143) ||| (if w.getLsbD 0 then 4294705152 else 0)
def lowRows (r : Fin 32 → Row) (i : Fin 32) := if i.val < 18 then r i else r 0

theorem maskLow : ∀ i : Fin 32, (262143 : Probe32).getLsbD i.val = decide (i.val < 18) := by decide +kernel
theorem maskHigh : ∀ i : Fin 32, (4294705152 : Probe32).getLsbD i.val = decide (18 ≤ i.val) := by decide +kernel

theorem normalLow_read (r : Fin 32 → Row) (v : Sig) :
    normalLow (sample32 r v) = sample32 (lowRows r) v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin 32 := ⟨i,hi⟩
  have e := sample32_read r v j
  have z := sample32_read r v 0
  have o := sample32_read (lowRows r) v j
  change (sample32 r v).getLsbD i = bit (r j) v at e
  change (sample32 r v).getLsbD 0 = bit (r 0) v at z
  change (sample32 (lowRows r) v).getLsbD i = bit (lowRows r j) v at o
  rw [o]
  have m : (262143 : Probe32).getLsbD i = decide (i < 18) := maskLow j
  have n : (4294705152 : Probe32).getLsbD i = decide (18 ≤ i) := maskHigh j
  have zs : ∀ t : Fin 32, (0 : Probe32).getLsbD t.val = false := by decide +kernel
  have zi : (0 : Probe32).getLsbD i = false := zs j
  unfold normalLow
  rw [BitVec.getLsbD_or,BitVec.getLsbD_and,m]
  by_cases h : i < 18
  · have hn : ¬ 18 ≤ i := by omega
    rw [show lowRows r j = r j from if_pos h, ← e]
    cases hb : (sample32 r v).getLsbD 0 with
    | false =>
      change ((sample32 r v).getLsbD i && decide (i < 18) || (0 : Probe32).getLsbD i) = _
      rw [zi]
      simp only [h,decide_true,Bool.and_true,Bool.or_false]
    | true =>
      change ((sample32 r v).getLsbD i && decide (i < 18) || (4294705152 : Probe32).getLsbD i) = _
      rw [n]
      simp only [h,hn,decide_true,decide_false,Bool.and_true,Bool.or_false]
  · have hn : 18 ≤ i := by omega
    rw [show lowRows r j = r 0 from if_neg h, ← z]
    cases hb : (sample32 r v).getLsbD 0 with
    | false =>
      change ((sample32 r v).getLsbD i && decide (i < 18) || (0 : Probe32).getLsbD i) = false
      rw [zi]
      simp only [h,decide_false,Bool.and_false,Bool.or_false]
    | true =>
      change ((sample32 r v).getLsbD i && decide (i < 18) || (4294705152 : Probe32).getLsbD i) = true
      rw [n]
      simp only [h,hn,decide_false,decide_true,Bool.and_false,Bool.or_true]

def fusedPass (g : Forest) (k i : Nat) (raw : List Probe32) (s : TeachingShape) : Bool :=
  let vs := programmed32 g raw k i
  let ws := vs.map normalLow
  decide vs.Nodup && ws.all (avail32 s.roots) && decide (k < s.price + ws.countP silent32)

theorem fusedPass_ok (g : Forest) (k i : Nat) (raw : List Probe32) (r : Fin 32 → Row) (s : TeachingShape)
    (base : viewBank32 r (wiresOf g) = raw)
    (tar : sample32 (lowRows r) (targetOf g) = s.out ∨ sample32 (lowRows r) (targetOf g) = ~~~s.out)
    (ok : fusedPass g k i raw s=true) :
    facetOK32 (lowRows r) s.roots s.out (targetOf g) (stateSet g k i) k s.price=true := by
  simp only [fusedPass,Bool.and_eq_true,decide_eq_true_eq] at ok
  rw [←programmed32_ok g k i raw r base] at ok
  have nd : (stateSet g k i).Nodup := List.Nodup.of_map _ ok.1.1
  have mv : (((stateSet g k i).map (sample32 r)).map normalLow) =
      (stateSet g k i).map (sample32 (lowRows r)) := by
    simp only [List.map_map,Function.comp_def,normalLow_read]
  rw [mv] at ok
  simp only [facetOK32,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq,List.all_map,List.countP_map] at *
  exact ⟨⟨⟨nd,tar⟩,ok.1.2⟩,ok.2⟩

def tupleScore (v : Nat) : SixBits := ⟨v.testBit 0, v.testBit 1,v.testBit 2,v.testBit 3,v.testBit 4,v.testBit 5⟩
def sixView (r : Fin 32 → Row) : SixRows := ⟨r 0,r 1,r 2,r 3,r 4,r 5⟩
def scoreAt (v : Nat) := ((#[0,2,1,1,1,1,2,0,2,2,2,2,2,2,3,2,1,2,1,2,2,1,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,1,2,2,1,2,1,2,3,2,2,2,2,2,2,0,2,1,1,1,1,2,0] : Array Nat)[v]?).getD 3
theorem allScores : ∀ i : Fin 64, scoreAt i.val = sixCost (tupleScore i.val) := by decide +kernel
def fusedScore (w : Probe32) := scoreAt (w.toNat % 64)

theorem fusedScore_of (r : Fin 32 → Row) (v : Sig) :
    fusedScore (sample32 r v) = sixCost (readSix (sixView r) v) := by
  let w := sample32 r v
  let j : Fin 64 := ⟨w.toNat % 64,Nat.mod_lt _ (by decide)⟩
  change scoreAt j.val = _
  rw [allScores j]
  have elem (i : Nat) (h : i<6) :
      j.val.testBit i = bit (r (⟨i,by omega⟩ : Fin 32)) v := by
    change (w.toNat % 2^6).testBit i = _
    rw [Nat.testBit_mod_two_pow,decide_eq_true h,Bool.true_and]
    exact sample32_read r v ⟨i,by omega⟩
  simp only [tupleScore,sixView,readSix,elem 0 (by decide),elem 1 (by decide),
    elem 2 (by decide),elem 3 (by decide),elem 4 (by decide),elem 5 (by decide)]
  rfl

theorem listSumDistinct (ws : List Sig) (f : Sig → Nat) (nd : ws.Nodup) :
    ∑ x ∈ ws.toFinset, f x = (ws.map f).sum := by
  induction ws with
  | nil => simp
  | cons a xs ih =>
    have parts := List.nodup_cons.mp nd
    have ha : a ∉ xs.toFinset := by simpa using parts.1
    simp [List.toFinset_cons,ha,ih parts.2]

def fusedCross (g : Forest) (raw : List Probe32) (k i : Nat) : Bool :=
  let ws := programmed32 g raw k i
  decide ws.Nodup && decide (ws.length = k+1) && decide ((ws.map fusedScore).sum < 3)

theorem fusedCross_cut {g k i} (raw : List Probe32) (r : Fin 32 → Row)
    (base : viewBank32 r (wiresOf g)=raw)
    (tar : sixCost (readSix (sixView r) (targetOf g))=3)
    (ok : fusedCross g raw k i=true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [fusedCross,Bool.and_eq_true,decide_eq_true_eq] at ok
  rw [←programmed32_ok g k i raw r base] at ok
  have nd : (stateSet g k i).Nodup := List.Nodup.of_map _ ok.1.1
  apply six_cut (sixView r)
  · simpa only [List.toFinset_card_of_nodup nd,List.length_map] using ok.1.2
  · rw [listSumDistinct _ _ nd,tar]
    have h := ok.2
    simpa only [List.map_map,Function.comp_def,fusedScore_of] using h

def teachingRawPack := limbs80 #[#[0x69000cc008e00154008e,0x3f0000000190000000,0xa00012000d0002a000d8,0x55001a40033001,0x8400375007b803a90,0x2a8007100bcc000,0x55003fc0096003300,0x580033001a00000001a,0x5500058006800,0x7f000a80017000cc007f,0x10000000690013000,0x30007f0005c007f000a8,0x580000001540069001,0x2a401c2001a000330,0x33007fc007c004c4000,0x16001a00055001300,0x29c07ff0095004690000,0x3110018800448039f00,0x54038c0076500b4c0f77,0x7f0008c003a0000000,0x24003f000d0002a001a4,0x1540000000640000000,0x8001fc0033000f800680,0xcc005e00154006,0xaa000000071000000,0xb400190025800fd0033,0xc8002e00,0x4c001a40000000a80017,0x16b0077001b1001fc00,0x8e0039c002200000,0x1a400ff000cc0055000,0x902ca408880144806460],#[0x68001540069033c0092,0x404d6000000033000580,0x30f026e4077702bb,0x1540000000cc008e00,0x6b00ae40147003fc0069,0x160000001920087000,0xfc004c000ac002b00114,0x55001f80068001,0x3000000068000cc00000,0x1900058007f00154003,0x8003f000b80024000000,0x15400aa000cc008e000c,0x1a4001700000006900,0x5001fc004c000a80000,0x7f00058007f0012000,0x28078f0061002c1000a8,0xa80034014a00630011,0x400000000000064003f0,0xa80019000fc003,0x4004c000000017000000,0x580008000a8007f001a,0x1fc007f000ac004500,0xa8003f000640034,0x2a0000000170000000,0xe0011300130007f001a4,0x1ffc022401bfc018e010,0xa00058007f00004004c0,0x2b8009b401e3001fc002,0xc006800518000000e400,0x1fc0055000580000000c,0xb5c03b600000053d00,0x2a001fc00170073c067b],#[0x28010013000000000400,0xa97c997def9c3803701c,0x154007f001a000004b5,0xa000580017000cc00160,0x1700130007f001a4002,0xc002a001300000001a40,0x1540000000cc0068001f,0x68001fc001600,0xb8000cc007f001540016,0x3940078c026d0051802,0x375007b803a900000,0x844005600bcc0210000,0x800ffc010c0022801ef0,0x3300154003e00000006,0x3f000000019001fc0,0xa80017000fc002a000d,0x1fc006900130000000,0x1400033000e80069,0xa90000001c20000000,0x300017001f001ff004c4,0x1fc002a001a40000001,0x90023800550023800330,0x6900000001700000006,0x7100130007f000a80,0x2a800ff0025000cc0000,0x1a40055001a0001600,0x940078c0146000000033,0x211009b402b800ae003,0x18005600228031d007bc,0x4a081fdf026040728001,0x3300071061c014400,0x69003fc0092002a8000],#[0xc003a001500016000000,0x1a4002a0005c0016000c,0x3d00130007f00,0x380060c01ff003380156,0x30044c022401ffc04,0x802264dcec5900638,0x154006831000588f0ce,0xb001fc00330005800000,0x15000d8003f00000000,0xc0000000340026000980,0x6c0026000fc00110006,0xfc000d00044000000,0x9f024080daf009b0067d,0xe30035100188033dc03,0xfc003403ffc02d301d94,0xa80000000000019000,0xf059f818d7035f400000,0x154006801e3c0bb,0x68001fc0012000cc0,0x1fc00330015400160000,0x170000000114002b00,0x1540068001fc0016,0x1b1001fc0016000cc00,0x9c000000088016b00770,0x580069001540068003,0xf00004002a0000000330,0x1fc004c00058007,0x4003f0002c003f000980,0xc000160000000680005,0x1fc002a001fc005500,0xb0000000690005c004c,0x98003f0005400],#[0x98057b00b5c04b900000,0x844008a0000001cf00c,0x3007bc010c0015803750,0x22401bfc018e010e0011,0x401f3019f003ca01bf40,0xfd8044900000051901ad,0x18c005280061002c200,0x8000ac0016001fc0045,0x26d00ae001e30000000,0xdc02bb00000014600e50,0x22680000034b001cf039,0xa80034000fc00190,0x7ff011a400a700000000,0xc66c800e7c0112009500,0xe98a770244d4cc7f0eff,0x67101bb003c704,0x350003400260176c0100,0x5bc30000000000006c00,0xa1d7ff6bef906310c0fe,0x58007f000a80001ab5,0x5001f8006800130007f0,0xb000cc000100000005,0x540026000fc0,0xcc00550000000ce0000,0x1540000001a400bf00,0x8a000cc007f001a0003e,0x75401d5004600062402,0xc400160000000680129c,0x2280211001fc0055000,0xb0043003ff0015801ef0,0x15000d0000000098000,0x8018300000003d000fc0],#[0x2a800710055801ff0033,0x3fc009400330000000,0x2c0009000540036,0x33000710009800,0xa80001003fc0096002a8,0x1fc007f00058004c000,0x900d60028a01d5004a70,0x2a001fc001601180018,0x80069001300001000040,0x1500037000e,0x338005500238003300,0x44038c00188000000069,0x1703ffc02d301d940d,0xfc004c001240000000a8,0xcc000000154008e001,0xf000540026003fc00690,0x680000000000002c003,0xc003300154007e000000,0x55000580069001f,0xfc002a000cc006800,0x68000000019000d00008,0x7f000cc00160000000,0xa800cc00000007100154,0x54000b0025800ff002,0x2000fc0026000d000000,0x130001f00000002a401c,0xc002a000d00000007fc0,0x9dc02bd000fc0019000f,0x16780000014b801cf01,0x3f000000019000fc0034,0x60c003d000a800,0x7001b1007fc00ce00558],#[0x5ac00000008800c4007,0x30008c009400774004e0,0x7f00004002a00460002,0x80068001fc004c0005c0,0xcc00550017,0x1fc0055001a0000000,0x49014a002c2000580033,0x4e018c007ff0061004,0x6000010008c0094007fc,0x158010c002280211004,0xa0005c001700ffc01ef0,0x2c200130007f001a4002,0x52800610044901ffc0,0x98003f00000000b018c,0x1580211000fc001500,0x6900ffc010c007bc008a,0x330004800000015400,0xd80cb500a801bcf001a0,0x40601bcf04060073f011,0xa00a800cb5011d8073b0,0x22800e1004c103fdc094,0x8002600054000b030c00,0xb000fc00000009,0x54003f000d8002600,0x7f000580055000000068,0xaa000000071000cc00,0x7001b10033000ff00258,0x5ac00000008800c7007,0x9000000019000d0002a0,0xaa000000071000dc000,0x400680025800ff003300,0xcc007e0015],#[0x150005400000006900,0xd40026000cc003a,0x170006c003f0003400,0xa4007f00130002a00000,0xcc007f001a00000001,0xf015d400ab0015400160,0xa6000000358019d8039,0xb0d80fdfc1c6530e7c8,0x2ac067600e7c05750ab4,0x6800000035800,0x11000cc007f000500055,0x8a007bc031c0015802,0xa00033000a8005500ffc,0xfc0026000000016001,0x900000000000054000b0,0x4c0005c002a00058006,0x4003f000d0002a000000,0x2c00000000000000006,0xfc0015000fc002600,0x16001540000000c40068,0x5c000ac002b001fc00,0x58006800058007f00114,0x1fc0033001540000000,0x700058007f000a800410,0x10c00158021100130001,0x8001700ffc008a007bc0,0x1fc006900000002a0013,0x154008e000cc008e00,0x6b0087002b9000000069,0xaf90064801460051c00,0x12ec052f819cf01cfc,0xb000fc0026000],#[0xd00000002600054003f0,0x6800044003f0006c000,0x8007f000cc0055000000,0x3580aed01ddc09b90005,0x1098057500000030f01,0x1900e7c02fb002ac0358,0xd0003f000a800,0xa0003e000cc005500000,0x1a00055000000000001,0x8000000033001a000160,0xfff035100765038c0018,0x80cc700efc057d00b4c0,0x61002c2039b80000029d,0x14a006300112407ff00,0x3f00000001b000440026,0x160000000680003400,0x280261001fc0055000cc,0x18c002d1006200542016,0x80016b0077001b10,0x8e0015400ce0039c000,0x404d6000000069000cc0,0x30f02bb40777026e,0x61002c200f18044900,0x6d00ae001e3018c00528,0x2300e5001460000002,0x6001ff0013801dd00250,0x2a40000001f001c2004,0xf0008c004e007fc01310,0x21c0077401180025001f,0x40167002ac03ff004480,0x1a4000000154008e0030,0x33dc067d003fc003300],#[0x2302db80daf00000039f,0x4e0077401180025000,0x81fff01ca00981007fc,0x1bb003c705100187004a,0x30176c00000040006710,0x1dd0025001ff00138002,0x4002a001fc0016004600,0x138002300130007f0000,0x7fc011800774009400,0x4004a081fff026040728,0x6b500f28067c061c014,0x2002c1000000519007cc,0x109006300155807ff006,0xc20098203ffc04910,0x3ff00228021103180025,0xc00560043001ef001580,0x43003ff00844008a007b,0x2a8000000330007100,0x8203ffc0c60003fc0096,0x98201244025000c2009,0x80025000c20049103ffc,0x1540000000cc008e031,0x101bb003c7003fc00690,0x4e0176c053800000067,0x1ff0008c0094007740,0x1f00000002a401c20046,0x3c7007fc013100,0x23019c406ec014e005db,0x1ff0046001dd0025000,0xd802a0032d41bcf00138,0x3ffc094a01cfc1018011,0x8030c0022800e1004c10],#[0x3300154007f00000006,0x6710000003c7000580,0x51802b80176c06ec014e,0x2690078c039400,0x18005740094001380023,0x33e0000001e3007fc01,0xbc005600a6002ed00d50,0x43003ff00044008a007,0xc200c6003ffc09820,0x3940051802b801244025,0xc004e00000026d0078c0,0x7fc0094004e801dd0008,0x95007ff0029c046900,0x10051c021c00448039f,0x4e00ffc006b0064800,0x7401180025001fb0008c,0x112805280061002c1007,0x300000008e01ffc06300,0x8e001a400ff00154003,0x400ff001540033000000,0xb9c018e010e00113001a,0x673c0af901ffc022400,0x2804bb00000052f8073f,0x187002604128207ffc07,0x8c004e007fc009405100,0x1ac021c0046001dd000,0xe0000001920051c02b90,0x67b00b5c03b500000053,0xc01120029c04690073c0,0x774004e01ffc025400e7,0x25001ff0008c013b00,0xdf00154003300000008e],#[0x100648021c001a400,0x54000b00ffc0147001ac,0xfc0000000d80026000,0x5000cc0000001a4008e0,0x1dd0008c004e003fc005,0x8021c007fc0118002500,0xffc006b0051c00010064,0x250000000330007100,0xff0061002c1003fc00aa,0x14a006300112807,0xfc0019000fc0034000a8,0x53c010c002280211000,0x901ddc0aed00ffc00560,0x38000000030f0135809b,0x8588f3b1649937310003,0x844005600ffc008a0200,0x7fc004e0043001ef00,0x120046001dd0008c0094,0xc1002ac03ff0087001,0xf97cd93701c20000059c,0x98000d4b5a9c3807de,0xe000fc00110000000120,0xff000cc006900000008,0x803ff00844008a001540,0xc80019007bc010c0015,0xfc0000000b8002400,0x650fdfcb0d830e7c4026,0x10c0022802110ab401c,0x3c02bb00ffc0056007bc,0x89a034b00e77007,0xf00064003f000d000000,0x28207ffc0981000a8003],#[0x80023061c0144001ca01,0x7fc01dd0046000940013,0x1a40016000a8001700,0x558003d00000004c,0x2040007fc01830033800,0xa9c3807def97cd93701c,0xf1fddfbf48fe083264b5,0x901448064634a5408410,0x211033c0088802ca4092,0xc03ff004300056002280,0xe7c05720029c0469007b,0x3c701ffc025400,0x23019c406ec014e004db,0x950025001ff0013800,0x58000000338003d00460,0x33dc067d007fc0183005,0xc00e7c0daf000000b6e0,0x89a00aec01cf039dc0d2,0xc006b00004021c000000,0x13800230064803ff0051,0x7fc009400774011800,0xec02be4073f0673c14be,0xa70044804690000012,0x5da43c00e7c07ff00950,0xa002f9ce94107cfc054a,0xf0013801dd004e800238,0xe5001e30025001f,0xda43c00518026d00ae00,0xf02f9ce94106280054a5,0x61002c101ffc044af3,0x9f004480469018c00528,0x4c10095007ff0029c03],#[0xc0022800e10094a03ffc,0x2a4007c0000001c2030,0x700b7400ab004c401ff0,0x2300000011200870016,0x401ff00460004e002500,0xe5002b8009b401e30077,0xf1c000000518000000,0x34014e0067101bb005db,0x32a0011c07ff0066404,0x64009400138002300828,0x7fc004e007fc0118004,0x20025000000008c01190,0x19100ce00589031000a8,0x2c201ffc044903ffc0,0x77c053e018c005280061,0x1ad4000000aa4066700,0xff00558018300000003d,0xa7011a402540033801,0xe0011300448039f013bc,0x1ffc022401bbc018e010,0xf00430008a0015802110,0x6ec00f1c000000ffc01e,0x80071019c405380176c0,0x3fc00cc002580000002a,0x3b6019ec053d00,0x8e01bfc04380073c02d7,0x4380089007ff0044c01,0x9007ff0044c018e01bbc,0x11d8073f040601bcf008,0x701ffc043400a800cb50,0x1c200ca8020a00664004,0x401ff004c4007c000000],#[0x580068001540068002a,0x138000300000003300,0xe3007fc0118007740094,0x14600000039400ae001,0x70011200c7800ab009b4,0x6380113003040167008,0x6010e007ff0089006ef0,0x1ef00844008a00ffc005,0xc0fff035100188004300,0x2ac021c038c0076500b4,0x1120059c02d900,0xcc0055001f80068,0x75400624028a0000000,0x5002b80129c046001d50,0x9b401460078c01e300e,0xf010e006ef0063801130,0xcf7019f400000089007f,0x8e00e7c0daf02db80,0xcc00ff001a400550000,0x138011800250002300,0x94001380023007fc01dd,0x23007fc01180067400,0xfc004e00774013a00250,0xe012d6a08100dc07007,0xf0011c04347def97cd97,0x43800828032a0066407f,0x807ff0044c022401bbc0,0x44c022401ffc04380063,0x53e0063802c700,0x940073c067700aa403db,0x1460078c02b8009b403,0x5807ff00b04062000000],#[0x7fc011900660014a015,0xb0025000000008c004e0,0x3f000d8001500000000,0x7ff0188002c1000980,0x100dc0701558014a0066,0x4b5a97cd970e01f7be08,0x1a0007e000cc0055,0x1ff0025000230000000,0xf400000046001dd00138,0x36bc0b6e033dc039f019,0xf02a08019100ce00c400,0x1310000001c2016240ff,0x80184001f001ff002a40,0x8c005280112407ff00b0,0x5ac004e0008c009401,0x5b0383480300046001dd,0x231268cffff1c03825,0x5001ff0013801dd004ec,0x87002b8006480147002,0xa000fc0009001ac02b90,0x469000000019000d0002,0xc00a700e7c0112009500,0x51c006b00ae4021c01ff,0x61002c20064803ff00,0x3e01ffc0630011240528,0x2d70000003b5019ec05,0xac0358002ac05750073c,0x61002c100e7c0676002,0x1014a006300112807bf0,0x2ed00cf803540078c00c,0x1120029c046900a600,0x448046901ffc039f0095],#[0x95004ef0029c039f00,0xff00250004e004e80023,0x940046000230077401,0xd0002a007fc004e00774,0x64000900000003f000,0x50000003b6019ec053d0,0x72807ffc12820073c001,0x40188051001870026040,0x8c004240155807ff00b0,0x78803940051802b801,0x8900ce00c4000000026d,0x6440fff02a0805,0x5c03cf031ec06b502cf8,0x890018e010e00113037,0xf011a4025401ffc02e70,0x5600e7c01120029c07f,0xc010c0022803ff008440,0xe7c0cf7019f40000007b,0xb1c043802db80daf00,0xd0089007ff0044c018e,0x1100048003f0009800,0x7000ab00b74016700000,0x3d000000112008,0xe0033801ff0060c01560,0x690015400aa000cc008,0x407ff010d00047000000,0x250002300ca8020a0066,0x77401ff00138011800,0xa30956c700e038348030,0x4701ffc01993fffc49,0x53e00828032a010d0,0xf6c067700aa401cf000],#[0xf012e402d7015ec03260,0x2a0040601bcf0000001c,0x46901cfc0cb5011d80,0xffc039f0029c01120095,0xb4c0fff006200d4401,0xff0008c009401d940e30,0x1c20077401180013801,0xc401ff001f000a900000,0x25001dd004600023004,0xe019f400000013801ff0,0x36bc039f033dc0b6,0xc01cf019ec03b6014f40,0x77000e6006c4000000b5,0x11d003ca007fc016b00,0x1c00000051901ad401f3,0x167002ac03f70044802,0x5001b30008c004e00304,0x1ac021c007740118002,0x800ffc01920051800010,0x2240063802e70044c043,0xab00b64016701ffc0,0x710000001120087,0x2a800ff00330009400,0x460078c02b8009a40394,0x55001f800690000001,0x34000cc000000000,0xfc002a00064003f000,0xf0051c019200004021c0,0x59e0000002bd001ac03f,0xab0073c0677014b80,0x59c00c100448021c0087,0x44c022400b9c043800],#[0x6b0031000220063807ff,0x1b0007fc01b10077001,0x9c000000088016b00770,0x250004e004ec0023003,0x25000710077401ff0,0x4e003fc00aa00330000,0x1dd0008c0094006cc0,0x4c401c2002a401c20046,0x7100000007c00,0x15002a800ff003300096,0x98003f0002c00,0x6cf03e03834803000000,0x188002c13fffc49a3095,0x1ffc014a0066005560,0xd1305418073f018c018c,0x4013a00138002302d040,0x44c0438007fc00940077,0x1ffc018e0089002c700,0xc70044c043801ffc0224,0x3300238008e0063802,0x98000d001a400ff00154,0xfc0000000440012000,0x60060c02480052804350,0x8a0015802110183002e,0xc043800ffc010c0033c0,0x63807ff0044c022401bf,0x1ca0098107ffc128200,0x31002a80071061c01440,0x80300000000960033000,0x8cffff03834255b1c038,0xb164588f310003380126,0xa800550200899373],#[0x211000580033001a0000,0x803ff0043001ef002280,0xe50035e0000001e30015,0xae001e100ae0026d00,0x3000000014600e50026d,0xffff03834255b3c0f880,0x3802c70044c04381268c,0x3834803001ffc0224006,0x90956cffff1c03849a30,0x88f0ce00c400264dcec5,0xc022400b1c0438020085,0x97049a30063807ff0044,0x1c038255b200c00e0d2d,0x6d00ae0014600e5001e3,0x7ff0044c04380000002,0xb1c018e00890]]
abbrev CellID := Fin 462
def cellData (j : CellID) := (chartTeaching[j.val]?).getD (0,0,0)
def sixRaw (j : Nat) : List Probe32 :=
  let p := ((#[12730325,37700329016,7642897976,22666968632,589268344,22668000824,38659629041,8118603285,23620468771,126875000,9265144,602439189,42294847,132791829,7531104469,60496801827,592920627,22548741880,9434488,38652846101,23620337699,12672995,37703941688,37968763448,37699804728,592937464,37581053944,60718581112,132267541,38520574456,8582418488,9416213,50480777429,601972231,38535398727,38639849528,126846328,8118078997,37581197269,37704171008,22667066912,60722250232,60733490496,9408469,60256159096,9408021,22548725752,14827477,559383032,37698637333,37698645525,61078244885,8109158456,361726456,7525600789,37585714040,38535397845,37581053816,8118079125,38660214587,37698494456,60138747256,38652780565,7643039096,592871928,23503040736,38652837909,12843221,61078245333,9263096,8109130232,8470399189,8105461112,23607521336,37933485623,60731682837,601914005,37585707000,60133883861,23488362212,9426296,9265016,814714837,132267989,14874837,354388216,8118107669,948785656,8910200,9434480,7885045280,8109092920,954464469,60138976632,367177783,61069325667,38535427392,7525860731,9375253,601914901,61069213653,60138807264,4857853,8084524565,952897069,7525629461,61078331328,8120000000,9436181,592953403,61069326549,38643462200] : Array Nat)[j]?).getD 0
  List.ofFn (fun t : Fin 6 => BitVec.ofNat 32 (((p >>> (6*t.val)) &&& 63) |||
     (((#[2190, 2859, 723, 1720, 3060, 1997] : Array Nat)[t.val]?).getD 0 <<< 6)))
def fusedPins (j : CellID) : List Probe32 := List.ofFn (fun t : Fin 6 =>
  let n := (cellData j).2.1
  let v := packedAt teachingRawPack ((6*j.val+t.val)*18) 18
  let pref := ((#[2190,15147,13011,1720,3060,14285] : Array Nat)[t.val]?).getD 0
  BitVec.ofNat 32 ((pref <<< 18) ||| (v ||| (if v%2 = 1 then (262144-2^n) else 0))))
def separatingRow (i : Nat) : Row :=
  Fin.ofNat 512 ((#[38,7,49,43,28,26,52,61,50,62,40,19] : Array Nat)[i]?.getD 38)
def teachRows (w : Nat × Nat × Nat) (i : Fin 32) : Row :=
  if i.val<18 then tileRows w i else separatingRow (i.val-18)
def teachCell (j : CellID) : Bool :=
  let w := cellData j
  let r := teachRows w
  let s := (selectTeaching w.1).1
  viewBank32 r (wiresOf g63) == fusedPins j &&
    (sample32 (lowRows r) (targetOf g63) == s.out || sample32 (lowRows r) (targetOf g63) == ~~~s.out)

def sixInputs (j : Nat) (i : Fin 32) : Row :=
  if i.val<6 then Fin.ofNat 512 (((cubWitness[j]?).getD 0 >>> (6*i.val)) % 64)
  else if i.val<18 then separatingRow (i.val-6) else 0
def sixCell (j : Fin 112) : Bool :=
  let r := sixInputs j.val
  viewBank32 r (wiresOf g63) == sixRaw j.val &&
      decide (sixCost (readSix (sixView r) (targetOf g63))=3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem teachCell_all : ∀ j : CellID, teachCell j=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sixCell_all : ∀ j : Fin 112, sixCell j=true := by decide +kernel

def checkTeach (k i : Nat) : Bool :=
  let j : CellID := Fin.ofNat _ (pickTeaching k i)
  fusedPass g63 k i (fusedPins j) (selectTeaching (cellData j).1).1
def checkSix (k i : Nat) : Bool :=
  let j : Fin 112 := Fin.ofNat _ (fusedTag k i)
  fusedCross g63 (sixRaw j.val) k i
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem proveTeach {k i} (yes : checkTeach k i=true) :
    Impossible true (targetOf g63) k (stateSet g63 k i).toFinset := by
  let j : CellID := Fin.ofNat _ (pickTeaching k i)
  let w := cellData j
  let r := teachRows w
  let s := selectTeaching w.1
  have good := teachCell_all j
  simp only [teachCell,Bool.and_eq_true,beq_iff_eq,Bool.or_eq_true] at good
  exact @facetOK32_sound (lowRows r) s.1.roots s.1.out (targetOf g63) (stateSet g63 k i) k s.1.price s.1.select s.2.1 s.2.2
    (fusedPass_ok g63 k i (fusedPins j) r s.1 good.1 good.2 yes)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem proveSix {k i} (yes : checkSix k i=true) :
    Impossible g63.mode (targetOf g63) k (stateSet g63 k i).toFinset := by
  let j : Fin 112 := Fin.ofNat _ (fusedTag k i)
  have good := sixCell_all j
  simp only [sixCell,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at good
  exact @fusedCross_cut g63 k i (sixRaw j.val) (sixInputs j.val) good.1 good.2 yes
end Nat92GE
theorem spanTeaching {k a n} (h : ((List.range n).all (fun j => Nat92GE.checkTeach k (a+j)))=true) : spanOK g63 k a n := by
  intro i lo hi
  right
  have v := List.all_eq_true.mp h (i-a) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le lo] at v
  exact Nat92GE.proveTeach v

theorem spanSix {k a n} (h : ((List.range n).all (fun j => Nat92GE.checkSix k (a+j)))=true) : spanOK g63 k a n := by
  intro i lo hi
  right
  have v := List.all_eq_true.mp h (i-a) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le lo] at v
  exact Nat92GE.proveSix v

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem smoke_teaching : spanOK g63 6 44 1 := by
  apply spanTeaching
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem smoke_sixPoint : spanOK g63 5 0 1 := by
  apply spanSix
  decide +kernel

end PEqualNP.Outside.L_meta_43236
