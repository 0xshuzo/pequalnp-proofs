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
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1 && x 2) || (x 0 && x 3) || (x 1 && x 2 && x 3) || (x 0 && x 2 && x 4) || (x 1 && x 3 && x 4) || (x 0 && x 1 && x 5) || (x 1 && x 2 && x 5) || (x 0 && x 4 && x 5) || (x 2 && x 3 && x 4 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

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
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

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

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



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


def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
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
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
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
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv



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
abbrev Probe32 := BitVec 32
def sample32 (rows : Fin 32 → Row) (v : Sig) : Probe32 :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (rows i) v))).cast (List.length_ofFn)
def silent32 (w : Probe32) := w==0 || w == ~~~0
def avail32 (base : List Probe32) (w : Probe32) := silent32 w || base.contains w || base.contains (~~~w)
def facetOK32 (rows : Fin 32 → Row) (roots : List Probe32) (out : Probe32)
    (T : Sig) (ws : List Sig) (k L : Nat) : Bool :=
  decide ws.Nodup && (sample32 rows T == out || sample32 rows T == ~~~out) &&
    ws.all (fun v => avail32 roots (sample32 rows v)) &&
    decide (k < L+ws.countP (fun w => silent32 (sample32 rows w)))
end Nat92GE

def g63Y : Array (Bits × Bits) := #[((bitLimbs [0xde2fffecdfefb7fe24,0xfd0134df79125f96f973]),(bitLimbs [0xa06242024e9910024,0x6100748d00121f84f140])),((bitLimbs [0xf5503c3b283fcee9db,0xc7fedeaad4fda56597ab]),(bitLimbs [0x7018380b000fc7495a,0x8426d28ad4f42520162b])),((bitLimbs [0x2ff76a2be05e6c1477,0x90d689a536f5605be5de]),(bitLimbs [0xf72ca28e016780415,0xf09028243665405be1d6])),((bitLimbs [0x9ba2cff09f04f9c7d8,0x2fffdf7e8f8ddb39423c]),(bitLimbs [0x81a0c1d14a1028c140,0x65d03720b89c011023c])),((bitLimbs [0x31cfad16d8cbe79bed,0x96abe3c1f34fc3ea3e44]),(bitLimbs [0x50dd8c46d808459a8a,0x929bc1c1f34dc3ea1c00])),((bitLimbs [0xe3dc53df34f95ef91f,0xde42373243e2b4ee5dd5]),(bitLimbs [0xe9280351325016b003,0x4c4f27324182b06e4dd5])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,16,2095,0,9),(0,32,2079,0,9),(0,4,2107,0,8),(2,0,61,0,8),(32,0,31,0,8),(0,2,2109,0,7),(1,0,62,0,7),(4,0,59,0,7),(8,0,55,0,7),(16,0,47,0,7),(0,8,2103,0,6),(2,16,45,0,6),(4,32,27,0,6),(0,18,4141,0,5),(0,20,4139,0,5),(0,36,4123,0,5),(0,40,2071,0,5),(0,48,6159,0,5),(1,4,58,0,5),(1,8,54,0,5),(1,16,46,0,5),(1,32,30,0,5),(2,4,57,0,5),(2,32,29,0,5),(8,16,2087,0,5),(16,2,2093,0,5),(16,4,2091,0,5),(24,0,39,0,5),(32,2,2077,0,5),(32,4,2075,0,5),(48,0,15,0,5),(1,2,60,0,4),(1,20,42,0,4),(1,40,22,0,4),(1,48,14,0,4),(2,36,25,0,4),(4,2,2105,0,4),(4,16,43,0,4),(8,2,37,0,4),(8,4,51,0,4),(8,18,37,0,4),(8,32,23,0,4),(16,32,2063,0,4),(24,2,37,0,4),(32,16,4111,0,4),(48,2,13,0,4),(48,4,11,0,4)]
def g63A : List (List Nat) := [[]]
def g63D5 := limbs80 #[#[0x5c0211019710d6108440,0xc808418d304811010d61,0x7a2d96992d10c825c440,0x5a9fa5e9a84e80c2]]
def g63D6 := limbs80 #[#[0x58c41480209cd6310420,0xa0c41480206004148020,0xcc740480200c74048020,0x58c41c80205944358420,0x10f41c8020a0c41c8020,0xa0043580219d17010c21,0xa005358021d0c4358021,0xdcc73580215cc7358021,0x1d0214c0306074358021,0xdd8214c030600214c030,0x213764c030a08744c030,0xa0854580316002198030,0x5ce72580315cc7258031,0x58c4308440a0b5358031,0x60043084405d84308440,0x10d610844061c4308440,0x585700844010d7008440,0x606645804310c7258440,0x1c962584439927158043,0x18d200811010d2008110,0x60043481102097010d10,0x18d30481101893048110,0x18a31481102093048110,0x18c724c11018b3048110,0x18d30c81101d0724c110,0x209300c12018a31c8110,0x1c8314c1205c5300c120,0x1d0724c120600414c120,0x1cb414c1201cb304c120,0x61c6408530604548c920,0x991700853020d7008530,0xa126408530d0d7008530],#[0x20971191306002110130,0x20d700863021130c8220,0x6074348310d0d7008630,0x600424c7109d2624c310,0x2097110320dd8724c710,0xd0d70087401917008730,0xb2fa5dcaf95b1f637c2f,0xbab6d5ea7d4ee9bd2fa5,0x15e27c3f6b6d5d7caf55,0x67ccf59e33b65bc7d8bf,0x3d5dab755eaad4fa7b4d,0x35c5f85eead79aeb5ceb,0xda79d739e5bcaf93f1be,0x1b308a05da128c39bee5,0x839f21158ecb9f688268,0x2640f9d4a43c29290b50,0xd5914a4692830368e8bd,0x44bc55a8660112f1c9a5,0x2a8590820f2078ca55e0,0x6865a212e8c56581c242,0x24532094d64454831ac9,0xb2c26c195c8acb087a65,0x16fa110cb43324e870c8,0x645233b9a96c726d8eec,0x85ab1a062856b7886852,0x4a1949911932c60a29d0,0x8419188db04a2c1d5510,0x94789d0a3cb642560c94,0xab2ec749a6005a4a133a,0x2e2c6a5c68cc817b6922,0x2ddd88a7428e7c846235,0x465994ac359963ce2e30],#[0x2ccc1c499845310cb0d6,0xb37b776284528f48250c,0x3d974c8322fa1a420dd4,0x124b5083d75ccb543aab,0x33206ac1d5763bb049d6,0x8a3990902cc20cd734e,0x4a0c3d0422c149674932,0xdfe421c954927748cade,0x40000ac6570e8cacc065,0xa424c31a189b86d93161,0x5a40143b82c387230281,0x1078218100581b81f410,0x5f249a0879]]
def g63H6 := limbs80 #[#[0x6010000000072]]
private def groupPage0 := limbs80 #[#[0x440105d8430417010c10,0x4130440101c91004043,0x1d330040744c01058d10,0xc42058f5204163d0810,0x81700c42058c3108054,0x58c41083630c4209cc31,0x10420988410817010420,0x816510c209cc4108263,0x5d8430817110c205c043,0x144209d8430827110c20,0x8043480201052008176,0xcc520083304802014520,0x4c020d05200834048020,0x8043584209893008074,0x58d6108074584201cd61,0x58c201d1630807158c20,0x80439842098a3108371,0x9d261082739842058e61,0xc802010f2008041c8020,0x8041cc020d072008331,0x1533108341cc0201d330,0xcc4205973108163cc420,0x8274cc42098f3108176,0xcc74008363cc4209d731,0xd042010f4108341d0020,0x8170d04205974108163,0x58f5108273d042098f41,0x10c215d8430857010c21,0x857015021d0c4308670,0x15160084535802110d60,0x580211d1600847358021,0x8673580215cd6008475],#[0xd0d6008675580219d160,0x58c21dcd600875358021,0x8576d0c2110e6008454,0x190210c274d4c215db53,0x8430588210c16108430,0xc353084305d8210c170,0x5d8510c1701443058451,0x4c030085300c17014830,0xc0524c030145300c041,0x1d1300c0724c0301c530,0x4c030589300c1614c030,0xc2624c030985300c221,0xd05300c3404c030c8530,0x4c030d49300c3514c030,0xc3744c030dc9300c371,0x149610c0724c430dd930,0x584301d5610c07258430,0xc35388430d4d610c232,0x86600c1618c43008630,0xd4030147300c021cc030,0xc672d4430c87500c021,0x5c0540c576148315c042,0x4c431149310c67215031,0xc7724c431d49310c472,0x151600c45258031dd931,0x580311d1600c47258031,0xc672580318c9600c531,0xd4d600c675580319d160,0xd4c315db530c5768c831,0xcb764c8325c0640ca72,0xd4d600ca71580321c560,0x8440584211004308440],#[0x101700c4405d82110170,0x5c0511017010c4058c43,0x5844010d611017014840,0x10272cc4401c96110052,0x58f4010161d004008740,0x580418c9601066314841,0x10973d48415da3210753,0x1c56010f73580421c560,0x580435856010c7258043,0x10e61580435c56010d62,0x9956010e645804398960,0x580439c96010e7158043,0x10c7258443dc56010f53,0x5866010f705844358961,0x84509c66010e6598043,0x14176084505c02114163,0x10d621417010c509cc21,0x8c450dc5631407158c50,0x14163c845010e6214162,0x5c33114163cc4509cf21,0xd045058f4114162d0450,0x145320c8519cf4114170,0x5c04214563108515c032,0x580515c0431467310851,0x14443580511096014432,0xd096014732580518c960,0x980510ca60145768c851,0x14a73d085158f4214443,0x10d601497010c5258c43,0x58052d0d601487458052,0x1484398052dc16114b73,0x1c96015071580545c264],#[0x811010c204437258054,0x44173081104802044063,0x18830440520c1109c820,0x10d109c832441700c910,0x44170149109c84344170,0xd8c62440631891010c62,0x4811014d204404348110,0x44063481101892044054,0x8c12044131481104c120,0x481108c9204423148110,0x4434348110cc12044263,0x149304436348110d4d20,0x4c11018d30440624c110,0x443524c1101c93044071,0xdc530443634c110d8930,0x881101d932443724c110,0x441308811018e2044043,0x18a30440528c1109da20,0x8c91018a31442768c110,0x4417098d105c23244063,0x18f2044062c811010f20,0xc81104cb2044130c8110,0x44232c81108c72044163,0xd8b2044343c811098f20,0xd09105c33244052cc110,0x44332d41100cb5044170,0x18f6244272d4d105c353,0xc1204c030480510c120,0x483510c1209cc3048171,0x8c831481700c5204c431,0x101200c440482730c520,0x4817010520cc44048171],#[0x5c4434817010d208c841,0x14520cc4504827210d20,0x4817114d208c85148170,0xc53048273151205c454,0x4c12010d30480414c120,0x480634c1201513048051,0x1d130480724c1201c530,0x4c120cc130480764c120,0x483514c120d053048331,0xdd130483714c120d8d30,0x4c52015131480434c520,0x483314c5201d93148074,0x14630480318c120dc131,0x8c120cc230481738c120,0x480438c520d463048331,0xcc631481738c5205c231,0x8c92015232480438c920,0x48041cc1209da3248271,0xd073048171cc12014730,0xcc5201533148351cc120,0x48272cc5209c33148170,0x9db3148275cc5209d331,0xd0120d4f3148343cc520,0x48272d01204c74048031,0x5cf4148170d0520cc740,0xd05209cf4148232d0520,0x48171d0d205c34348363,0xcc75048273d41205cf50,0xd81219d36348054d8d20,0x4c04208530dcf6048443,0x188214c0540853010c21,0x85305c0214c06408530],#[0x4c342085309c8214c264,0xd88214c36108530d4c21,0xc530188314c0520c530,0x4c021101305c4324c362,0x4c8414c062105305c440,0x109305c0424c17010530,0x4c17110d30d4c424c273,0xc84504c021141309c843,0x145300c8514c34114130,0x4c0621453010c514c042,0xd84514c34214530cc851,0x14930188524c04314930,0x4c171149305c0524c064,0x148614c042185309d052,0x18530cc8614c06218530,0x4c04318930d48614c342,0x5c0624c0641893015062,0x191309c4624c17118930,0x4c272191305c4644c170,0x1c1314c0624c530dc121,0x88530dc1314c0724c530,0x4c06288530152214c043,0xc6304c0218c130d4e21,0x8c130106304c0328c130,0x4c0628c130186304c051,0xc86304c2728c13019230,0x8c130cc6304c3308c130,0x4c3429853010a614c341,0x87304c170c85301d321,0xcc53018b314c052cc530,0x4c276cc5309cb314c064,0xd93314c362cc530d4b31],#[0xcc9309db324c064cc930,0x4c052d0130087404c364,0x9cf404c062d013018740,0xd053010f414c341d0130,0x4c262d05304cb414c062,0xd8b414c342d05309cb41,0xd0930197424c064d0930,0x4c276d0930997424c170,0x107504c021d4130d4f42,0xd4530187514c342d4130,0x4c361d45309cb514c062,0x18b614c052d853018b52,0x10931d8b614c352d8530,0x4c67210d315c0434c570,0x9c8544c570151315c052,0x18131188604c44318131,0x4c5701893110c624c672,0x10f604c442d81315c332,0xd81311cb604c462d8131,0x4c762d8131d0b604c732,0x5c4434c97010d32dcb60,0xd813210c604c97115132,0x8417010e105c03284043,0x58d2084130482105c052,0x58610989308426348210,0x84032c421058e6284132,0x5c03188163c821010f10,0x982201d1638817010e20,0x88031c82201066088031,0xcc72088130c822010f20,0xcc620d472088340c8220,0x88031d02205db3188054],#[0x5c04388673d0620cc740,0x582215c0548857014e21,0x884545822114d6088443,0x10c218c04398221d4d60,0x8630150218c05308630,0x8c176086305c0218c163,0xd4c218c3430863099421,0xc630588318c0520c630,0x8c3530c630988318c170,0x8c8418c1701063014841,0x10e30d4c428c35310630,0x8c042146300c8518c176,0xcc8518c1761463010c51,0x14a3010c528c34214630,0x8c163486309d0528c170,0x589618c05258630d4d21,0x8863014e218c16358a30,0x8c2748ca30d4e218c163,0xd4f218c1639863010e61,0xcc230147308c021cc230,0x8c262cc230987308c162,0x98b318c162cc63014b31,0xd063010f418c272cc630,0x8c342d063098b418c232,0xd4f428c163d0a30d4f41,0xd4e309cb518c021d4230,0x8c57010a315c0328c674,0x5c3318c672152319c843,0x152325c4438c97010e32,0x8c8545823210d608c971,0x991608c9715823258560,0x9823210e608ca7458232],#[0xc4043083105c2648ca64,0x4c030c4263083105cc20,0xcb101d032c41710c310,0xc41760cb105c032c4132,0x5c440c404310310d4c32,0x10f105c043c426210310,0xc427210f105d843c4171,0x5c850c403214310d0c43,0x4831010d20c417614310,0xc4232483104c520c4130,0xd0d20c43304831098920,0x4c31010d30c40324c310,0xc42744c3101d130c4072,0xdc530c43424c310cc930,0x4c71010931c43724c310,0xc43424c710cc931c4072,0xdc963c405458f1010d32,0x8c31010e30c404388310,0xc40548cb1010e32c4262,0x10e62c42748cb105da32,0xc831010f20c434398b10,0xc4232c83104cb20c4130,0xdcf20c4353c8310d0f20,0xd031098b30c4074cc310,0xc4343d03109cb40c4232,0xcb50c4272d0f109cf42,0xd4f109cb53c4176d4f10,0xc81300c32014430c8274,0x4c431c80540c7205c430,0xc7205c031c81320c720,0xc804310320d4c31c8232,0x5c043c8170107205c440],#[0x10f2099043c817110f20,0xc826314720cc450c8343,0x14530c80414c3200c530,0x4c3201c930c80714c320,0xc83314c32098d30c8074,0x10d31c83724c320dc530,0x58f2010d32c80544c720,0xc80518c3200c630c8054,0x98e31c80548c72010e31,0xcc7201d331c8054cc720,0xc8170cc72058f31c8132,0x9d331c8272cc7208cb31,0xd0320d8f31c8353cc720,0xc8343d0320d0740c8131,0x9cf41c8232d072010f41,0xd4f209d351c8163d4720,0xc8570193215c043c8674,0x5c263c87535832110d60,0x143305c021cc06408730,0xcc3211433010450cc021,0x5c064cc17014b30d0450,0xd43309cb41cc052d0330,0xcc221d433048750cc021,0x9cb51cc342d4330c8750,0x153315cc52cc57014b31,0xcc452583315c064cc672,0x8c960cc562583311d560,0x5833199560cc66258331,0xcc5708cb31d4d60cc672,0x9ca60cc662983319c232,0xd4f319c262cc57098b31,0xd017008740d4d60cca72],#[0x1c931d01700c740d0c21,0xd07409cb31d03704c740,0xd057010f418cb41d0173,0x98c52d057314b415c052,0x8cb4110e32d045258341,0xd057098f419c232d0570,0x5cf52d0673d0b415c342,0x98f42d4d60d0a63d4b41,0xd437158f505c021d4170,0x9cf21d4170c87505c221,0xd0b5058f42d4273d0750,0xd4443583515c043d4673,0x5c043d4970d0b515c232,0x583535c960d4d7158353,0x9de6f8fe2f5c264d4e74,0xab6aba7e8f9fe7e9f67b,0xb7edeafebeaf6bbadeaf,0xbeaf9bdef6bbeedbaae7,0xc9f1fc6f0fbfafdbf2fb,0xcf73bceb37cbf2ecb72b,0xdb76bd9f5fd775bcff3e,0xdf77cdef7ade777ddb6f,0xe9f9fe7b9de6f97e3f7e,0xee7b7edbb5ecfafeb7ab,0xfafe7f3fbeef7bceefba,0x1f7fcfebf9fdbf4fcfee,0x3e8a209db4dbb0de8f84,0x6f463a2428e732dd1908,0xe09b761f14eec1023dd8,0x7d08ea89a3dd87c4a3a0,0x2952124e4c420fa98647,0xd024333888655598ae79],#[0x288655f550e46690a004,0x538c8e5812195d70392d,0x9460f01453ab6205878e,0x1ec08ae42801395cec98,0xcc43bf4630c20cc5da4e,0x3aedaaabddad218c098c,0xe600d78a219531c63465,0x4391840987d54730c0e0,0x2325380f0047385cd035,0x30e54229946220c01eee,0x2195c3641293306340c1,0xb0954c573bf110cac501,0x632a190e8b327191dd56,0xc098121a2219423470d,0xd9fa4f320c432841400b,0x8c4a27303c7b0059279,0x254a64c6818121a2656b,0x3f89a14504ebb150dc8,0x89f024344b14432cc7b0,0x481d87404b9088a91a0,0x48e12ca12398c95422c3,0x811602df3ec0220d074,0xb85b3b3f2468225d6ac6,0x2a5c84b8968ec91bc149,0xe212ca16421956b9431a,0x43c2090a22c0170b4626,0x43ec0524b475151a0e98,0xcef81ace3302eb2d6093,0x43b0ee54d189155b3b31,0x976035b72414b0458013,0x22c0c921f80c00fb0034,0x2b6349668c4e99f60298],#[0xfb014aaddcd005bbb085,0xd5da520ec06324686698,0xb3a65137634fd6aed902,0x586b396cecc8ad1c8bf5,0xb0d44421957a22c045c4,0xdd8775b3a07d297343c8,0x4231e458695582ca1e4a,0x831523504ed2d9d4a65a,0xec34ada0c1a0ec053c46,0x1ad55bb99d6e47257e86,0x852b6855cc8b0c42116,0x28f16887162d61b7722c,0xcd4ade1aa05bc1576f08,0xd135bbb1907d809c56d0,0x20c46867d08b0e774d18,0x2016ee64e34212143ec0,0x9e2da143a6dc191b3d80,0xc92ec0082f085421b2e7,0x48e48256969066a4ddc8,0x916ac6222dd8d570ec04,0x1cd1c8c55a3b2e0b482d,0x85a42ec81e87c19e6a73,0x6458025c8b0d668761d4,0x96f0c312d98caa78c1cc,0xb4208ae5a40d56b6829c,0x39433584580d7d6aed3b,0x4586b6d6d030a2da0049,0x6904982d1d5a33ec037c,0x61920a5a413f90a85141,0x34394f18817688d0cb64,0x78703d6ce90fad5da972,0xb0e26ca18d3869416b8b],#[0x5d83622c3592b7868f08,0xc3b872b731366d08c1ad,0x8378c8f007311a1c580e,0xc899916188a9ec016665,0xd032343c5c4682b596c,0xc027d804443f07aed91,0x7440fb00a187e02375a4,0x7b1876003c5bc01e01e8,0xa763cc05a21d877bda08,0x54246865116f0d95ada0,0x7f0ff00c9addc8c30fc0,0xd4ad58f6d23c389ab682,0x623cc0dc3356306de706,0x2eb7732fde086d4bbdc5,0x948b0d643ca11a9693a6,0xbd06004d22c009f1963c,0x45abb4f0f2824288f0e2,0xe1d877f9a50565b6dcd1,0xdd90aa50761da55ac3db,0xb91d1665abb090b685cb,0x23433c73c813716ce82c,0x46868126e8689ca5cc50,0x8d0ce0b99cb1c9431a50,0xf601485b3a362d274d8c,0xa42ce4f0858ed6ae7a51,0x28254e3504f6ade0b645,0xf0db9bca114e95b1b0e7,0xa0b4ba0c0460ed716d16,0xc01eeb5761908d082b11,0x63389a0c8fd876035222,0x1b7c6191d86821954b5,0x1d6a5bc10ce4586c603b],#[0x1a6a45802e6c0c48c07a,0x15a184eb358761dbf95b,0xe76341d16e22c065ab68,0xcf823c0182b674a3c8b0,0x378d2842a96ee46591a0,0x566c8c48aad98b580fc0,0x35ad9d038a1bb0e44686,0xce2343384b5731416aed,0x8eb7862c214ca212d208,0xea30c8fcbc2114e79424,0xc3b5c5515b42ed445802,0xa78bb510b681cdc8b0d4,0xcb4748c5c8e4b5ad20c1,0x168e4622d9cc530ec008,0x11a089922c06c0458016,0x38c0b0118647516d0ca7,0x7d809bc8b0fa5ad1d4a5,0x8b0c1bc658c400ec05dc,0x761dc8784248eb6764a8,0xab119c45831448b01ba0,0x48499254c77111e00495,0xb01199161c579a3243ab,0x18d0c5ac082eb7802808,0x40ed4b5760548b0351ad,0x841416d0b0a1f602675b,0xb009f601b422c0b4046,0x112d7941479186475d69,0xaa374a821bc8d0e4dad2,0x7108990b474d9ca21603,0x2491208cf5b3b3fab78,0x6722343246b7863596b0,0x4fab6747403b01b92da1],#[0x9c1cce4c5cd5c8c03ec0,0xe5ad618e595bb0d47d80,0x640ec3cea6683739b106,0x4e468414a56ec34ad60e,0xec8b0d6e11a089d5a3a0,0xf3920aff5b3269e46865,0x75a42ed567310808d044,0xeb6742716d0afe2d5d83,0xddec2fb07603295abb4c,0xca18d620ec0121346246,0x76b8d7337722708d0ce2,0x1d805196ac6554a18d1d,0x6d020bd7d8d155a32266,0x1606a839412d4b5832ad,0xa3a1391b63c943b0c1e1,0x472c21dae379ad98c625,0xcec80ada12530ec06aee,0x18d199a9914b19841416,0x42a10f28498de08731d5,0x8265568e829ad5d88b79,0x36134191f65b3a93072,0x32a9e39134d8634ccf7,0x5a8458031c8b0e27076,0x797d690251ad206723cc,0x8822da060172415f21d8,0x5d6a421be4b4871096cc,0x21f807326cc452c6a0,0xc7c3b005a2d21a365a41,0xb6469904272392d4b676,0xba8c3236d18438296ee5,0xb51b807596cecbb3b5ca,0x40e70d7c2da1a368d40b]]
private def groupPage1 := limbs80 #[#[0x1ad9d45322c307e72824,0xd6dc1b52458726d6d0a3,0xab586dcc8d0e77ada1c4,0x16907602d1c8c8733a63,0x876021b6cb9a570a650b,0x3941228b4752708d0ca9,0xb663d756cc9a691a1059,0x3b0eacada0b6423432c2,0xf602ea5bc349128540e0,0xac13f8e443599c904241,0x573b683b00faad20e2c5,0xb002f2de1ce69b40b06b,0x6020d9eb08d246873283,0xb994d1a8468e68ca8987,0x864056b0433ade18685a,0xd3f112102d782a35246,0x91d994b187f3d722688b,0x34beb5760d08d0677c61,0x33216cc535116025b22c,0x98d9fa19173ec0506b77,0xd2039418361d87ab16ce,0x9ff18647f88d0e774a18,0x306d7028aad992ad5bb9,0x4bca1cc4d5bbb4fa4482,0x1595b98a8b482dec8b0e,0x26b48105cfb008f9f602,0x2c8b0e4fcddc9209a322,0x24d18d3622c00ae1d804,0x75ab9930728646656c6c,0x24581a908f01a34f189c,0xc8b01a711600ee2ec3ec,0xade00a122c065cf2858e],#[0x3ec0407286347d6908b9,0x1d806643b0ebb87a1ec1,0x8b002a07600dd9bb143c,0xc20da95ac1e58b66334c,0x34338d646340c8b062ab,0x4801756eed6a99a0dbe2,0xee6282d9d98b9ab1414b,0x5d9c28c3238846873e56,0xc02241d80dc230c8eaad,0x73151e506d4ad20abb3e,0xc48bd310c3377b924eb7,0xb649bb1a267082456c8,0x182c1d87bcd68c8822d6,0x66248f03402d9da135ab,0x52bb91c9605b42a52b67,0xecd9b410a0b67661dc90,0x3ac46840a96d0b2987a1,0x3d9b0e761469d0518cc0,0xfdad21a2239412f4b586,0x4d8d42bac44871343b00,0xc70a6503dd8e601c61d0,0x949d0b82ad9da115bc34,0x42d9d9a65a424ecb6752,0xc8c3240c1d80d648d0cc,0xce6746308b0075395cb1,0x48b072e2d5d83c0ec04a,0x2de1e9673a1b18b485b7,0x5a3a8a646865aa34c860,0x1d87cd16b053b1160c52,0xa504034f1c4c15a42e5e,0x6d0c4d8d3a0aeb782339,0xfc064446865f168ea5f4],#[0x78639668e46111619a63,0xb0d3a916022b0fc0470b,0x5da5f683a2504580da08,0x41be646873de30c90d2d,0x817403b0158ad61c4d33,0xc81c4da19980ec05333d,0x893b5b42074b48688e54,0x19a6f05498d690916581,0x4c25a0c8dcbb216f55ab,0x118cf604570ec05bce47,0xd053ec02c4f0846a6830,0x8aeb674c86830114ad18,0x4748b0d731161a7895b9,0x98addcca65a391b07d80,0x5922c0660b7733bd6b0d,0x1846866556f020bad1d0,0xacfb00f307e02a20f43e,0x391a0b49b439008ec81c,0x80fc06bc4586c5654c78,0xab685d91a6e8b71ea191,0xd6d03392d98f6b6cb9e7,0xade01730fc06ce7d80a5,0xf43a401d806f668c8d3,0xb6849d96ee64c4621042,0x6d0b322de1a7a6cb9a04,0x7e019c5b42c02f2856a5,0xdb1e467c8082d6903bd8,0x7869616ac7b5ad9d02d8,0xec4e3ad988ac9ec1900b,0x9d45922c3582c075b1a7,0x392dc4686440390f612d,0x813496aed7d87a19ab72],#[0xed081f61a886c41e6d3f,0x2f123432381d87795a4,0x2050f3436a4cd08f8876,0x339d6f053b1f6012e234,0xf6ac6e05d67841cc6b56,0x4a6b218ca0ec72b3c3d0,0xad07d8058d6cece14fdc,0x7f9e50731ad5d8d15a40,0xd42de1c080f43d9cb676,0xd9a0c00b6b563bae3300,0x55346273ddf054faddc8,0xcda301852d212dd23432,0xb8761db05bc39c247803,0xa23c305935860c56f0db,0x4b6765e88d0e27116011,0x48b0077cd1c89639c363,0x87602905bc19fab664d4,0x5b424c91b647e5b106d4,0x5d80c948b0cf1ad5da74,0x8b02d0b9e08485b410ce,0x7a1a0e9fb14390965108,0xa42bf8b485ad09d0b899,0x682d0d6e87a83c14da95,0xd06292d9935022c3058b,0x6033f69ba2461d80bc88,0x39244b6766348b0c3487,0x628308d0cbd0761e9776,0x4eb07e0c4c0fc02af37,0x19717630bec45869e66b,0x19f6f182429a6c8fb11a,0x26456d049a0761f035bc,0xd8b1ca10322742a28728],#[0xf3122c308ab5760588b0,0x3ef28635956eec34b6e0,0x38d69059b87a1d1d3ec0,0x1e0761ed95b326ea1d80,0xd195398a05d861056cec,0xded0647748b01a211a19,0xd4f7037107600e822c35,0x93c9d92c9431a4ab576a,0x79a323c845803b1a0c90,0x13c821c08909531f6017,0x96aec452d9d9849a3144,0xbc215a95abb502b76365,0x5b419a87d805448d0e4b,0xf08498cfb00a02d21529,0xa109aa07602bc0ec3b7c,0xd18d3f5b3b3c6f382d61,0xb326632b6348251081c4,0x6822716aed30ad1d74a5,0x90024ad1d45995b1b244,0xa0c4f94b9a1d3d832cd6,0xc3b691a8659c3b0ef111,0x867be36c8ff399c9fe0e,0x8731ada04a38cc36b646,0xd9ca38415844586a15e6,0x1a6c1d87a0d6b066a2d9,0x3155690b322ddccbd9bb,0xd3a876031f0ec3bcc468,0x8ee8432aec458713d6ae,0x5cb6741939a687aa4d1c,0x532c8ca81c25942622c3,0xe6ad9d9909a21a264686,0xc12ec041cb5769cc3b00],#[0x801d803d27ac6019e606,0x756ae697ad9936b9b391,0xc2d5dabe0ec3df672824,0x6234209cb763bfa6ce44,0xa46831448d0e284d1913,0x43b0efc07600ccb440a2,0x91e18166821ec41d8035,0x2343250b6742603b0e95,0xb4740a08d05a2ad5d818,0x6cecdd87603390ec05d0,0xd58f6eb232206f28598d,0xb310181d879a168ecb2a,0xd87c5230c8f307603275,0x8e84c076029d7932cc61,0xe0e5922c04ba1d874096,0x42bac4580da43d0e8a07,0x81c48cd06d32d20a768c,0xea532d18d5a5a3245845,0x152d23432e0c0858b168,0xb4f27c806dd690450ad2,0x4d896ae652b99c98a5ab,0x731d1594410fc0178d27,0xc579ec08a24686749e0a,0x4591b63104fb00c94a1c,0x3363104ed116004e5b42,0xb91f601855b3b4144780,0x105bbb17f286349168ec,0x4ab6764ba7cc4914ad8d,0xcec6c49dcd191c984b28,0xd399d31e5b3a9381f806,0xc0ec3b5ab67402e7ce44,0xcb5760f48d0e2bb6e0e9],#[0x9690ab991606a722c18a,0xad9d97723420a8468315,0x5bbb594b6767e290e834,0x7d80a22330eeb2d61b2b,0x6ce823ad9d8188d420a0,0xfdc89a22c361f4180151,0xa428c67d809508d082c4,0x6756316903b52d9d4505,0x6e6882d1d1de84c28a0e,0x9ca0f5a326627d80a1db,0xbb0eb08655aa50e613b9,0x80859e10b31cda195595,0xd48b420b5c5a324547d,0xc8a65a410cf3c62864bb,0x15f31b43b7ece63284d4,0x29c96f04fe2d2153073c,0xa07ade18f65a41a5ab48,0x56195b98a6d183d9612c,0x5feb6751526cc4534219,0x75a6886f211212a57339,0xc499a0dc26d32b751a74,0x6b0ec0144b48563c8d0c,0x964586985a6e986cad8d,0xa26b02c19161af668c05,0xe1161cef5a426a05d802,0x66d39c0a4580d256ae64,0xf082d626ac610ad98b5,0xc8b0c321160c4f5a415e,0x4d608505bc19567a864e,0x5b3b2f6b57671ab842f8,0x34729fc8d0c9f3cd4da9,0x6d0cab3b2050a69426c5],#[0x9209569ec08a118646c5,0xc41e62b57699a68c4dbb,0x68378db0cadd11618126,0xc68e2d5dadc6c390da6,0x5cf3a0ec05db2a63c225,0x4326a1d87a348d0d0c36,0x767203d0f82ada1a2d23,0xe27bb5c54822c35c2b6,0x1c4d72392cab5769b48d,0x38aeb67414d6b00b991a,0x602980ea8a9161b10224,0x9ecda09d623439d8458,0xf3b5ac38b73582b7c8b0,0x690f38698c8d0ccfb65c,0x23c8b0e539161aea22c0,0x419760291ae31a2adb83,0x9f5abb4cab7733f96aed,0x6ef343538990b3491a1c,0xc96cecc52d20ac05a40e,0xc591064e0f438481d87c,0x1a14009ab7833508b0e2,0x91843a4d6f002ec658c4,0x83b00462d9da0f5abb63,0x4a18d235abb000b48689,0x8c40bacb665d416aec25,0xb7801256d0400ad1d450,0x6ac731ad9da155a42940,0x761e675b422e6b6646a5,0x8323b8b664d32b8c6960,0x78063ec862102d5da606,0x300f3271d0bf58410fab,0x607020ec0027106469cc],#[0xc0e02a3761b944e67317,0x650bd00cab38161cec2e,0xed68166044b214014e89,0x91ee09c39c8208576d6e,0xb2e88865659a0e982a71,0x43ea10cac381e1cde563,0x8402cdd86b50408fab47,0x57f03c01428a650562d0,0xa289c647ee00caa6c019,0x1c944e6691061885443a,0x76a41d0742442d14b376,0x5b47c395a39860740b0e,0x888b760522304eb0161c,0x30830151a79d9ff1cc35,0x101a1cb941328de84656,0x24ec20c6e572701b2e6e,0x435861a618c8f601a1e3,0xc8300272b1c8708c3236,0xb9dcb0d20c019435861a,0x97b135cf46559cfb0080,0x4c43c996cc7b6a75dafc,0x20c8f22aa14a4643a61d,0x29d5024432b32d181c2a,0x63a2da88858b0230ea7a,0x5873f1b4e607a8d8d564,0xc4a090200c102c38320,0xa0e4b60b282614874595,0x394420786358770d7191,0x646bd46ec34aa5c8c055,0xec352b9c8654fbb59710,0x8ab018c316abc7546146,0x3a4206873bc8301a4ab9],#[0x142a40e60284e1eb21b4,0x8f40121e7c20c0460e88,0x8b602c34f6a37345218c,0xbe05860348301554520,0xb60fb018300e1cad1942,0x1d27191f619c03b61d87,0x906c3bcc428031c0d0f,0xfa0f8323566ec3601a19,0xf9e70485259d06050410,0x4aa204a402432fc9e641,0xf034394eaa7660968e97,0x28c745908701bc86e1ea,0x8301a4221d6801cc34a,0xb720afd56b095ef9650e,0xb43da8f9650ec0b0c1a,0x9c7432144e60581a1cee,0x850065289cd9a51bb0d6,0x6023258b1cc71064724,0x1c06f0c4741b473006d9,0xd81c90830026a8dd87a2,0xd0e652b5d8a92cc0eaa5,0xa0a5da421d2442803dc0,0x3a48284655600d0ccf0e,0x821f650c69f2d1d9714e,0xe890cd58c3358bb516b3,0xe5c08c3ab7086561218,0x1102178753510caa591a,0x1524b3035ea858ce91f4,0x9861d600021842274e97,0x2e736c04990c74591a0e,0xdfa1d8089d14ca0982a1,0x508fb068b91219936821],#[0x87106009751bb0f0a862,0x612e42584a0634cc4d0a,0xb49f76c28fb00950261f,0xc00d0ca80161cea01c36,0x88ea0947a719646ac871,0xe03c3cc40e8681c0f0fb,0xc9c741d00f0024ba4c54,0xd14ca12a21d51e4232ac,0x2bdd8935031a8aa1734a,0x1ac3112a962389670d1e,0x41803c55aec300fa1c82,0xe302c0a79da004432b36,0x6004f72b966aa976184,0xcc0db83186c946b0c441,0x18026d3b0d854d10ec53,0x3011a01e1c0851bb0d84,0x606cb06c3bd516842cc8,0x4380ad281c28830043b3,0x8607d20e838d4211151e,0x441a71d967443ac8039,0x9f02c3cb49c84da87d,0x83c3986b9128e839906,0x7b0d66ec3690600d0b3a,0xea79d10720c0552148,0x24302c3ed23a86464db0,0x89b28627ade8cab78c21,0x8c370d318c209db0343,0x9c27a104954394fe9c74,0xba58bb51807803c0b908,0xb83687c2c090cc301a1c,0x5516ec21906005803c00,0x81219574f3a4521d878],#[0x61fc085aaa7338087006,0x8a36342a3ac60fbf1956,0x93ced0844a09d6544294,0x285cd0e08c3df4ad6119,0x30c00d232846a918e893,0x35630c06b0d440161cf2,0x730d27a7191e002c38b1,0x1a1f2e194341c4180978,0x342c6aad612b0730d268,0xd7276c0d0e4fa7212721,0x90a4ab98cafe55316ec9,0xe1d494fc36b841808bd5,0xbb1291843ae130c8f086,0x863940f0c58311920757,0xc4f38e219395531d7e07,0xd16568c084441808a650,0x3412a173409570052341,0x1bb085004fad5da69194,0x985b11d06e0ec0684598,0x6e020c068ed074c3618e,0x54a6981690f303638f60,0x2d508caca01e186221c0,0x4a49d0da20c01e51561,0xc7683a5943186a4544e6,0x96d7836a45b005890600,0x92ce84310a005820c06,0x38161c4d6339c100787a,0xa87ba24230849180b0e4,0xa37313542e6a3a75c5d,0x883011d395cb3303438b,0xacdd87918c0162a27310,0x6621d6e88655d546ec36],#[0x3186a513cc94d81e1a58,0xb0f2ea79da0257c012a,0x5e1ef721c0184ac82254,0x4b288b0f74590630dad8,0x7761da20c90e986006c8,0x3002a2ce1a6303c00bb2,0xa19ba8232ad2d07457c8,0xc069cf0529b88701a303,0x740acfb009aa85cf0420,0x820f285cc5018413b49e,0x4a46132826af7129ac8,0x9600ba7553c0f0c342aa,0x3168d9048a8161e5e72b,0x7574718d3c5b39822368,0x8928ac21003d8174142e,0xb60f8323c2d0f69abdd,0x7ec0b0d4d1f6033e20c0,0x130d61a893ec06781980,0xae02c381c39860c512ca,0x86428025c8b00868161e,0x84830075271d1205e3ad,0x58ba108039418605d80d,0x203c0140a3761d40d0fa,0x6a0841f4790ca68d61d3,0x538ecb78161cef214069,0x90a009b1d43349538445,0x77b959e9d7612d16ec1c,0xa84b308500279020346,0xd904dabe9943803439d8,0x21959721401d80686579,0x64147c39860c9a0e9682,0x8645652c74727213643],#[0xd08318161d2bb24122b4,0x618d503c017607868f53,0xc047289650940d0cb701,0x86008750c9e2cdd86e20,0xe814edd80421406923d,0xcc2754c0148a2733840b,0x6a64180a9d12ca14a81,0x74500f0e058c2128620c,0xb6b8e20a8058408fa068,0x57986323ceab722704d0,0x34406873dd52c46fc119,0xd998ae75b28dd86f1d41,0x9c2add81c03c39ea0980,0x7d57c112a7580910fb01,0x94a3811f481006126e10,0xb03b0e951f6021702c3c,0x4a7990685031a4666829,0x2c39dca3734dda906d,0xa2b8276c0b0d42066029,0xc0f0d3d06e1ef4024333,0x906186984b2824058726,0x1342850b176a28830053,0xe971abd46e62a2b98ab7,0x3d0855a29d40b20c0450,0xb60182443ac7ea3761dd,0x3c34c61287c4596e8b31,0x4646e966ec34a7a1b0a0,0xce65b0161ea93cc0dcac,0x600fc20c01d88a651f92,0x43c852c626b939090a10,0x745a80b0e4f8161d0d02,0xbb2adc8c959bb0f6d0],#[0xcc0444b2854c874c24fb,0x9694af7624512ca17561,0x6d04750cd6106037a55b,0x126bb20efd513985a078,0xe33543968c0786d00db0,0x48a88655e03b0c0981a1,0x7a40b0c039960da61ec3,0x172c1da018500006180,0x4310841381e000ab610c,0xa8ea067a1c86595a498f,0xc4c0d01f826002baa2a6,0xed4b22b82848aa026c17,0xa458d4220540042afa38,0x6caadca22347f9e06b94,0x6500e22985200406ed35,0xf5386cd2eca3a3c7a19,0xa4d0dc28046004e72442,0x4ea360c42d69d22c7719,0xc3b0b21f83c0046d0a3f,0x8b429897a06769945d93,0x5e08101080e09b74d330,0x41583210486050076003,0x323c8924e812470816c2,0x260f030500f10c4481,0x3046060d82da0c84c148,0x4080860e2896088c0089,0x54028743b080ff0023f0,0x58304624005050018150,0x642a1002c270488a1122,0x3031a23004418b02d0,0xac4b02c460a1381ea0f8,0x225c0ee043c66189c1c8],#[0x582125465128321e6118,0x3c2a8b61a900a5888382,0xea3a8420137a1c821270,0x40eb910e6850db82c298,0x8149682d84410850009,0x80b7e20fbb418f62110,0xfbaf2c6bae0898f0489,0x1261c18dbf8806407912,0x22f2d63e75f20f6210e2,0x3cff56960665f64445c4,0x211330fd731859242d34,0x566afd00808f668affb8,0xd2986665c4e113a98242,0xebb72c6014cebb8861fd,0x60c746084af5000097d9,0xa8914338dff248a197cc,0x3afa10880f7d0084ee1f,0x6042f3741061deb20b03,0x87c820d1f124d096f988,0x277d418f382579621068,0x258a8e690c047660c70,0xecbc9acccda82d8b9043,0xc90dcb9f2d0899fde082,0x7e59c199de20a77ac435,0x17a68c9efd0340043000,0xadb1819dbea6092c2b47,0x551359b6f404de0921fb,0x6494ce1e850f9066effd,0xd9248deb9a91460af2fd,0x1b8669eb9eaa48f3d735,0x18bf8790016019a6b979,0x32abd0ec9080468d92c2]]
private def groupPage2 := limbs80 #[#[0x320ebac0171924bc2fe9,0xd02c00274530d5f081,0xecc8fd750840cffae85b,0xcf55e1fc8ca5ee50c6,0x3142c634d19003f0fced,0xed0334f9335c2303cd21,0x98e1d5142671f8c750e9,0xeeca32070e0c91ff898c,0x142f69c85909fa2839c5,0x426da1b39815193cd166,0x8a50268608d58c18e2f1,0x6895c298c8041e4a3e7c,0x32265b15593a054880fc,0x3bf068]]
def g63D7 := groupedPages #[groupPage0,groupPage1,groupPage2]
def g63H7 := limbs80 #[#[0x304800cc025c40e08080,0x1861001e208c0003800,0x2084ec295604ed29560,0x4c6bffff5ac182802001,0x4c28110000000c6bffff,0x1b1bc21b191bc21fb4,0x643e3bfb6ac282000000,0x30300140000a643e3b7a,0x13c45b0013c65bb6e4,0x30e00bb2c304000000a4,0x21a8d4018601320010c1,0x160c37da3c2357cffd04,0x4412bc0038000051bc5,0x103003d421a62001c2d0,0x1706ee2c1a3012808502,0x30219c0]]
private def groupPage3 := limbs80 #[#[0x1481010c10108100c810,0x4c010480104401014c10,0x980108c81058c104c810,0xcc810cc010c801098810,0xd4010d0c10d0810d0010,0x104200c420d4c10d4810,0x18c20150201442010c20,0x584204c4204c02048020,0x98820984208c42058c20,0xcc020c80209902098c20,0xd0c20d0420d0020cc420,0x10821d4c20d4420d4020,0x580211502114c2110c21,0x98c21988219802158c21,0x1043008430d4c21d0c21,0x15030148301443010830,0x4c4304c0304843019030,0x8843058830584304c830,0x980308c8308c4308c030,0xc8430990309883098430,0xd0830d0430d0030cc030,0xd4830d4430d4030d0c30,0x150311483110831d4c30,0x8c831580314c8314c431,0xd0c31d08319883198031,0x1903215032d4c31d4831,0x9803258432580324c832,0x8440d4c32d0c3299032,0x1444010c400c8400c440,0x4c8404c44014c4014840,0x8c440884405884058440,0xcc440c84409884098440],#[0xd4440d4040d0040cc840,0x148410c841d4c40d4840,0x58c41580414c84114c41,0x98c4198841980418c841,0x14c42d4c41d4841cc841,0x9804258c425844258042,0x5844358043d4c4298c42,0x98843984439804358843,0x8450d4c43d0c4399443,0x10850104500c8500c450,0x4c8504c4504845010c50,0x8845058c505885058450,0x99050988508c8508c450,0xd0450cc850cc450c8450,0x108510c851d0c50d0850,0x58c51580514c85110c51,0x98c5198851980518c851,0x10c52d0c51d0851cc851,0x9805258c525845258052,0x58053d0c529905298c52,0x58054990539885358453,0x988549805458c5458454,0xc9100c1100811098c54,0x1411010d101091010110,0x189101511014d1014910,0x4c110481101911018d10,0x8411058d104c9104c510,0x8c9108c5108c11088110,0xc81109911098d1098910,0xd0910d0110cc910cc110,0xd4d10d4910d4110d0d10,0xc5200c120d8d10d8910],#[0x1412010d201052010120,0x191201512014d2014520,0x8c5208c1204c5204c120,0xd0120cc520cc1208c920,0xd4520d4120d0d20d0520,0x10d21d8d20d8520d4d20,0x1912118d211512114d21,0x8530d8d21d8121d4d21,0x10530101300c9300c530,0x145301413010d3010930,0x185301513014d3014930,0x4c530485301913018930,0x8853058930585304c930,0x985308c9308c5308c130,0xcc130c85309913098930,0xd0530d0130cc930cc530,0xd4530d4130d0d30d0930,0xd8930d8530d4d30d4930,0x10d31109310c931d9130,0x18931181311513114931,0x991318c9314c93119131,0xd4931d0931cc931cc531,0x10d32d8931d8131d4d31,0xd0d32191321813215132,0xca10d8532d8132d4d32,0x192101521014a1010e10,0x586104ca104c21048210,0x98a108ca1058e1058a10,0xcc210c8210c421099210,0xd4210d0e10d0a10cca10,0x106200c620d4e10d4a10,0x1522014e201462010e20],#[0x58e20586204c6204c220,0xc822099220982208c620,0xd0620d0220cc620cc220,0x10a21d4e20d4620d0e20,0x582211522114e2110e21,0xd0e2198e219822158e21,0xca300c63008630d4e21,0x1463010e3010a3010630,0x192301523014e3014a30,0x586304ca304c63048630,0x8c6308863058e3058a30,0x98a3098630982308ca30,0xcca30cc630cc230c8630,0xd0e30d0a30d0630d0230,0xd4e30d4a30d4630d4230,0x14a3110e3110a310ca31,0x582314ca311523114e31,0xcc63198a31982318ca31,0xd4a31d0e31d0a31cca31,0x192321523210e32d4e31,0x98632982325863258232,0xd4e32d0e32cca3299232,0x103100cb100c31008310,0x14b101431010f1010b10,0x4c310483101531014f10,0x8831058f104cb104c710,0xc831098b108cb108c310,0xd0b10d0310ccb10cc310,0xd4f10d4b10d4310d0f10,0x10720103200c7200c320,0x14f20147201432010f20,0x4c7204c3201932015320],#[0x8c32058f20587204cb20,0x98f20987208cb208c720,0xd0320cc720cc32099320,0xd4720d4320d0f20d0720,0x14f2110f21d8f20d4f20,0x583211932118f2115321,0x9932198f219832158f21,0x8730d8f21d4f21d0f21,0x1433010b301073010330,0x193301533014b3014730,0x88730587304c73048730,0xc873099730987308c730,0xd0f30d0b30d0730d0330,0xd4f30d4b30d4730d4330,0x193311533114b3110b31,0x8cb3158b31583314cb31,0x997319933198b3198331,0x15332d4f31d4b31d0b31,0xd0f32993325873258332,0xcb400c74008740d4f32,0x14f4014b401474014340,0x58b40587404cb404c740,0x98b408cb408c74088740,0xcc740c87409974098f40,0xd4740d0f40d0740ccb40,0x10f410cb41d4f40d4b40,0x583414cb4114f4114b41,0x98b41983418cb4158f41,0xd4b41d0b41ccb4198f41,0x587425834214f42d4f41,0xd4f4298f429834258f42,0x9834358b435874314f43],#[0xcb500c7500875098b43,0x4875010f5010b5010750,0x58f50587504cb504c750,0x993508cb508c75088750,0xd0750ccb50cc750c8750,0x10b510cb51d0f50d0b50,0x58f51583514cb5110f51,0x98f5198b51983518cb51,0xd0f51d0b51ccb5199351,0x58f52587525835210f52,0xd0f529935298f5298352,0x9935398b535875358353,0x77b7d7e7f3e9ecee6f2f,0x5fadd3e7eff7ebedeef3,0xbfdde7efeff7dbdddedf,0xfffbfbfcfdfebeff6f9f,0x4dd842027484409d139f,0xd7168c3dd85c08723a8,0xcf58c7200743a9010c78,0xf00745b41dd8423d6399,0xa10584810d7159c95c42,0x4015760b055d8850b761,0x11855d851157687c59d9,0xea63a6508055d83f4f53,0x6435458442297288c5dc,0x8c051770a9c55da2f167,0x7089c55d818157667945,0x5da8615762a0a1c98115,0x67645055d8194b761085,0x55d9891576a445dccbe1,0x15765f055d9917343108,0xc55cd392a723693d0cad],#[0xa17739ad3989c2157628,0xccc5c16415766405dc0c,0x963a6507ce1950d17730,0x8c055d83249637b05dc0,0x45553731e0e594242173,0x257c55da8e1476425458,0xc0db51631e055d99c2a7,0x7073c5dc0957b40070c9,0x5d9e15376170c5c1ac15,0x5762d459d94c1570ab85,0x55c1d46074109298dfe1,0x15769ec55d87b2d717d0,0x455c0d115766d85dccac,0xf2273490e19511167649,0x2455da2244644e855d9e,0xd813001455d9b051611,0x82055d84a15760e455d8,0x215157688055d8301573,0x597055da2414763a455c,0x88aa15760e1258c1e1a7,0x704c145843d157359d35,0x5d9f515760e9158c7230,0x57670119c92d15768ac5,0x55da1017702fd3588b51,0x157033451d9081c745a4,0x859d8ec157606855d999,0xb466410c55da92516120,0x9c55d83d3a6507855c23,0xe9734010855cd1d15701,0x3859d8ef466411055d9,0x9bd1e7481055d9751576,0x33c944c45e2a7243855d],#[0xc5f617700d0a5ca50157,0x7663875c2671573618b5,0x191344c623985dd84215,0x57693455c241157054d1,0x59d8f7157697d41c8781,0x1676390a5c9de3865424,0x859d913507211455cdea,0x415761cd218ce7157682,0x6459d90a51611ec85ce3,0xfa44644b0e1950e15769,0x4055da9045734b455d9,0xd05343115458c7c1576,0x11cc55d8c631703785dc,0xd82e16764e9119147516,0x767394584b0327037855,0xdc0d515767e0e9945415,0x5733c0e1950f15738585,0x3588551576a8c71d0421,0x446448455d8b11576779,0x855da82177660455da25,0x15768505dc26c15730d,0xd258cbc2d7188071d18,0x451576594c5d9b14e621,0x43459d956157677548c8,0x8aa4e621a485ce264b63,0x61c55d9b91576681398,0x88b751616105dc2187b4,0x521158dd042157623135,0x5da9815765b95dd84250,0x5762d139885117733205,0x55da814a6307871d1081,0x31706ed45843a1c7439c],#[0x455da04486342071d1fe,0x4157666055d8021576a3,0xc134c8693a6510c5dc19,0xe16763b455d85815709,0x5d855d828287242059d9,0x26f177334c55da581576,0x62f055d9f315766a855c,0xcdcf15739bc55d875157,0x764f055c098317067055,0x58451167656c55d86f16,0x576634adda0015767694,0x85ce222a7245055c2161,0x386544055d82d1576300,0x455da26177325085ce1f,0x150751e191d0422d7176,0xd489cd3e52631e059d91,0x8c5353114e9945116763,0x5a085ce241570a7855da,0x827792036455da511875,0x669055d99217731e055d,0xd93d157396d1d8d48177,0x632a9110c78317066459,0xdc09b157694c55cda34a,0x5762c111913b15709e85,0x55d9dc15765d115c12d1,0x15760f941504551611bc,0xc55d984157087859d921,0x23170595218cf81770a6,0x8855d80115737f455d81,0xaa46640205dc0ea1576a,0x67c75c4a138654285dd8,0xa1c496331855c2af1576],#[0x35c5dd81e15767b455d,0xce8f16765545dce9a157,0x632048dcda4177032455,0x10cad177335055d85545,0xd7176c59d92439650813,0x55d8b9177035069d5b32,0x227353059d8d91576630,0xc75c272157678055cce3,0x615767dd4d4c7848633b,0x9055c2807b3007059d90,0x5a2a7241475ce6115765,0x7f0e59422157619455d8,0x5f02f7102055da391576,0x679455daa14d63070b5c,0xd85415765e4cdc1a5177,0x76408e19502177360855,0x588b0793061ce5941f16,0x57684859d8de50751153,0x15c52d157086879d0da1,0x16763e05dce172a7245d,0xc5dc06a44644bc61d5a8,0x44644f05dce77157617,0x455c09f15768e911913,0x4f4e76430bdc5c215767,0x5b455d824167641455c1,0xe6d157612455da4f1c74,0x3818d5c11459630a5a10,0xc0fb5b71080d5c15b357,0x7145961d1833570680d5,0x9d1a0357043a14c4e659,0x570419f1c9083570a10d,0x698c223573760d5c03a3],#[0x5a64740d5cd923570389,0x161d49a3573418d5c50a,0xc35737f0d5c25a36764f,0x8161d0ae3474075618cf,0x335843655f8c90e58624,0x31cd5c1283570a51610c,0x19158624ad61d9095963,0x4080d5c1053672194d5c,0xd03358710816d4d93585,0x70a05658cbb5b7226969,0xd4c9a35703de2149b135,0x570669618cec35700f96,0xd9d93d5963640d5c0a33,0x5b5385d658cba59630c0,0x5658dee58730ccd5c0a0,0x33570a916151d088216c,0x70d9d20a586253961519,0xe25a74740d5c01884721,0x2fcd5c10b5a751a5f8c9,0xcc86b43935658cbc5872,0x453969904a5a64749610,0xd2ac5a730cd6dca3d586,0x636a0d9d1bb5972ab169,0xd08be5842565610d2c59,0x8432f9618ce659630a96,0x61d63d58437a9ad060b5,0x3570930d9cd065874179,0xd5c2125b7160cd5c506,0xe5a64a71a10c2a357038,0xfcd5ccec585479a1188e,0xf635737e9658d6c58742,0x4d1610c355971ab0d5cd],#[0x21f5a6300cd5c1045864,0x438df9c90e3570a88d5c,0xc2823570904d5cd0a586,0x7042561912c7e71430d5,0xdc1ff37704b8d5c16437,0x570769658c165963044d,0x6990205b7279961d1943,0x3570528d5c1f56b74421,0x565c5d05b430cd68c88a,0xc357667961c9595b531a,0xa169889a3570895a1913,0x3d5b730ccd5c19e89305,0x500d5c14d5b725656996,0x89d8731424d5c2463676,0x363561488a7753669698,0xc27e3674841658c0d596,0x730c8d9cd125b63438dd,0x5856868436d56d0cc835,0xe323fcd5c2655a648fd6,0x610cc15963061a10df67,0x35705596d8ce335704e9,0x961d0ca58521816d8d0f,0xe35705f214c5eb5b322f,0x656dcd1d6a32984d1d1f,0x333573785610dd05b625,0x3d56d4e3d87623b969d4,0xe39586251965d8183570,0x3574d5c50d3573364d5c,0xc28c5a764396d4c8a584,0x71a2d69949a59760a0d5,0xd89465b712b96d0c5e5b,0x5702a161d0203570a196],#[0x61892389303b0d5c06f3,0x8a30398d5c0ef3570a41,0x8d5c10235709356585d0,0x83570530d5c0de58712b,0x996d4e763573948d5c1f,0x9974526c4d5c2395a633,0x4bd658d8959631d0d5d9,0xc3359628f561d4695862,0x47e0d5ce5835739356d4,0xdd2357140968c85e6a6,0x701d1618959893039961,0x9d1ac7e32399698c8735,0xd714316152028631398d,0x61ccc868438316992417,0x877279218c4f33472269,0x5658c2258540ccd9d028,0x58435bcd5c252357394,0x2161d43359632d56d8d1,0x5e5b43475658e6858764,0x900d5c50058740d16148,0x5085874321658c2d5a64,0x353d69c46959760c0ddc,0x5194596307cd5c251584,0x732516dccd358540d161,0x1954f5b4392169d45e5b,0x86338d61d03358633656,0x6d8cfc3571444d5c29c5,0x5a60268d5c0706b4382d,0x1658c0377324bd658d68,0xe585460cd5c298377095,0x222cc10858530ccd5c24,0x93584332d65849a35738],#[0x4916191363570a0d6d0d,0xc1c8472791658e943570,0x305cd9cca35a72179f10,0xc89b596305d6d4c5e367,0x704a8d5d9a068431bcd1,0x5c1575962269658c1035,0x5709a161505e5a74178d,0x6dccc83573448d5c1bc3,0x5872268d5c1553571415,0x4d5c1997c62398d5c14f,0x6596269cd9d1b2357073,0x6cd9d20f35709ed6d8ce,0xa235702e96d8cf359622,0xa169d1163570288d9c0,0x165584338d6dca8b5963,0x4024d5c1405963050d5c,0xc0c759632dd6d8d02585,0x76669a1d1083570374d5,0x8c9f735708fcd5c14b35,0xc624f23d493f3570a45f,0x3cc0e68f717fa3d893c8,0x8f4339a3105fe8c434a2,0x238c9ee8f317fa3cc508,0x98d307ae31893f8c644a,0x723151338f624fe3151e,0xe68c437ae3188e78e326,0x422310cd98e6266a3d8c,0x6038e710623d05fe8f41,0x17fa310c228f307ae30c,0xc1f8c524fa31c8e78c3,0x7239e35c4188c717fa31,0x151998f437ae3d88e78f],#[0xc4249e31511f8c6339a3,0x31493f8d303ce34c0e68,0x8c4376235c10e8c4339a,0xe3191278f5039a35c20a,0xb8c517d23d4d3a8f503c,0x263149ec8c428d238853,0xff8f537ae39d93a8e746,0x4d23d0cff8e656663991,0x9208d7000a3d45088c21,0x47ae3d45fe8e6482a314,0xc12c8f513fa3d4e1f8c5,0x6382a3d45f48f434ce35,0x5c1f88e7443a3cc99f8d,0xe65492310d998e7482a3,0x31d5a78c624fa3d499a8,0x8c216e231853e8c2110a,0x23cc9278c523b630c9ae,0x8c537ae3d4d9d8c327a,0xb239c4698c3162a39954,0xe88c436ba310d1f8f527,0x7763190ec8f323e6310d,0x5428c544b23109e38e72,0x239e3085268e624fe308,0x450d8f5349230c9e38c5,0x700023194ef8c5182631,0x9d1e98c5451e35c0e38d,0xc211563c85348e656c23,0x30c5f68c5236a3d09e38,0x8c3182e310de38c3143e,0x231d01f8e620f631c469,0x38c6439a39c1da8f414d,0x6639c49a8c6447e3190f],#[0xe98e750a23d4df58c633,0x4363085b18c435123194,0x9f18f518263188ed8f51,0x16e23148458c3277a30c,0x4c478e658ae31cc1f8f2,0x514fa31c89a8c7478e3d,0xd0d998c214ee3d48e78c,0xc547fa3cc4298c544223,0x3991f58e744b239c65a8,0x8f2150a39ca3d8c64512,0xe39c89a8f507ae3c8526,0x58f211563194d98f4347,0x8e39c46b8d700c2358df,0xe68c540a238c50f8d733,0x4ea38c60b8e700c23d4c,0xcf38c2188e3086348e70,0x26ca39943a8c523d23d4,0xc9e38c5439a31092b8c5,0x324ae31953a8c543ce3c,0x10d2c8e754b635c1dd8c,0xe7077639c92d8f424ae3,0x398e048c524f2310d2b8,0x8c7269e3149ae8f4343a,0x23dc1d18c527a2310d47,0xa8e740a235d8188d7006,0xa3d4e2b8d620f635c13,0x9a8c5339a318cec8e720,0x812314cf38e7562631c4,0x5228d728f63d4d998e64,0x24de3d48f48d72776308,0x49e38c4250a31510d8c4,0x526ca30853e8c5482631]]
private def groupPage4 := limbs80 #[#[0x1912b8c5269e31912c8f,0xc527663194ed8c437a63,0x3189278c7639e35d93a8,0x8f424de3c86348e640a2,0xe35899f8f2188e319147,0xf8e6267e3d4d1f8c3267,0x9e39d50e8f3162a31d1f,0xa8e6587e3d89278c653,0x7e6310d338c3183a39d6,0xd088f524f235c1da8c31,0x78e310d9f8f530ea310,0xc4298c437fa35c14f8f4,0x3249e310de58c6549230,0x189438c643663194ec8c,0xc546263589b98c536663,0x31450a8c4349e3989b98,0x8e654ea39c49d8c5180e,0xe35c92d8f5278e3d8943,0x88c644ce3d4dda8c5478,0x3a3cc92b8c5213231d10,0xa8c747fa39953f8f534,0x3ce3194e68f536c23d4e,0x93f8c414d23145088c65,0x266a3151ff8c517fa358,0x520a8c5443a398dff8c5,0x5180e3d450a8c513fa31,0x9c83d845211569d0698f,0x1321f0d9cdee8c4342cd,0xd9d13c8c528c23d89465,0x7c5107055d96647745b4,0xa9c92668747f96d4e6b,0x8466470239c20a5a646b],#[0xfd69d49a5a62950d5c19,0x1f3673441258caa59768,0xe8d5c1f244644c8c9c1,0xc783476490d9c2a25a63,0x27814988783571451414,0xc5f88c43810d5c030367,0x76071318930877217239,0x9cc817d620f569c6760b,0x4644d0d9c0c736724b47,0xb5c5e0587133df189337,0x367090cd1c23c1a751c0,0xcbdc4bd3672678d9ce0c,0x3570840b5c154357383,0xe5a9c52d8f52884d5c61,0xaf3570648d9ce8536725,0x97d19903d35707b5698c,0x14749632d4d9cd7d5a62,0x1428d9c0a08f6248cd9d,0xd21f5a626d56151615b6,0x7340d35ccb2157330479,0x5c27535702996d0d4f36,0x67099a31042735706f4d,0x5dcd9336724fe14c4f33,0x1570aa4d1d1a77c727f8,0x615843a35734059dd042,0x74e625d56d4a6b4e6222,0x91398853386542c55ccd,0x48893076568c87835731,0x7f0d9cdf936700c11195,0x1ab5843a74a9c9603570,0x59396d4d1d3570828d9d,0x8cfb4d624b1a1c52d1a7],#[0x6377cd9c08c466401121,0x5c0e08f534fd61511d5a,0x75279148c84c35700a8c,0xd5cdf74c541185dda548,0x5b53920ddcce65a742f8,0x1458878596339855d977,0xd3570a59618934347408,0x19610c0c337069855d86,0x52357180d658d7a5a325,0x77dd145345976625658e,0xd1f8f437d455cd155963,0x405f8c9da31705e889c,0x8cf31a753d61151e4357,0x7449e1148ee74326ad65,0x5ccc55042114d5d99b36,0x57067dad053e8f428d0d,0x79943a1c7478d6190ef3,0x2a724196d8d2b5a627a1,0xcd5c1f71573358d9c852,0x23070951fdc9fe35702e,0xd961d29a4e622e0d9d1f,0x7e4c62558d5c1d415767,0x56ce99442686449cd5c0,0x99c59637e055c0f03571,0x38185dc2ad157688cd9c,0xc9365b63058d5c1c1367,0x7202561c8cf35707a5bc,0x10cb2367022085cd425b,0xc424cc55ce197c3161d3,0xf4c9f7873142dadc52d7,0x8f41074d9c9bb5963935,0xddc1d160644d1f8ca0a],#[0x45a64664d9c8867e727e,0x8d9c92515764a8c5c10,0xb28c41600d5c52a59760,0x51615c5da36744b23589,0x148357097969883b4464,0x18116d0c693a6509d1d8,0xd1287f51071615248873,0x7253568c8ac3673764d9,0xd8df88b52108d5c5d636,0x77169855d8a274436ad6,0xe994225052130e9943c3,0x5a759216d85083570774,0x92d8ce74e621563989b2,0xa59635bd698dfa6a640a,0x9965d9da377325055c11,0x6853531f2310da04e626,0x754d08454e6211d698d,0x5c834728f5658ca45a64,0x384d9d13536728e869d,0xd99f36727b8d1cdeb357,0x635c855c16258732f8d5,0x9cd044664158a9c8fe5a,0xb767fc55c11e35707ecd,0x64c12c367466c5dce015,0x7474108d5c08359321e1,0x4cdc1301d701c9119144,0xa1e746ad6d8d041e748b,0x5944c84c3673820d9cdf,0xef5b71808d9c23f1a750,0x869f9d10c1c74075dd8c,0x6341776174d9ccbb3570,0x44b169882a377385e388],#[0xc8dc357049e35c26d5a6,0x653916989e34963020d9,0xdc26a53521f161c5a958,0x963a493988af5932518d,0x4584707e3243df4c9da5,0x3570888d5ccf37743669,0xc55c1c68472015a5c12d,0x3367248ce994534b6336,0xcd5c5a01576688d5c26,0xff357151cd9cc222a724,0x48115c84e2a7237cc5c0,0x5c4745110a3dc5086b64,0x210c55d8291576994b5c,0xc9455864549dd45345a6,0x53474d1c8425a6315cd9,0xdc9a9347403935885258,0x5733812d8cff36764856,0x3988497e3282cd9c2713,0x35707256108be5a646b9,0x455d93a5a62668d9c05b,0x46b644b1658cc5596359,0xd05dce8a35760616188f,0x9735737ba31c9e35a631,0x7b8d9c03158539acd5c2,0x42b37714c1258e862d71,0x2765f4ca0a44644c4e99,0xd1e81a75868d9c9ab5a6,0x322b0ddccf3686450cd9,0x58ea47e327ae35c5f859,0xa621ecd5c0865a633656,0x61494e15766856d0c615,0x6b644acd5c55f36763b5],#[0x79d1355361405458447,0xa8c414205dd9ff1576a5,0xcd6988aa585485d75943,0xbe3570898d9c8028f303,0x5f1658d9d4b6337960c8,0x85859769b5618cf95963,0x453d618cdf596329cd9c,0x845135709cd19c44e586,0x700f4d5d83e845217149,0x5c4fe4e712c855cc9735,0xe622c221493b5a739d8b,0x698c6f3674484b5c5224,0x35708123cc50a5a647a5,0x939883d2970754d5c17d,0x7587639d69c8be587126,0x68d9c9b736723d1ad914,0xe35a622d56dc8bf34747,0x9c569d59335703163dc9,0x8a65a642c455c24a3570,0x67a63cc6038c528c5358,0x8ca53673044d9d016597,0x634205dc1d136728d565,0x9d1fb36709116995af4b,0xa763bd6191383672784d,0x79d0495a611ad6d8c185,0x21734a8d9cd7b3a6511c,0x8d9c934347201e114971,0xe3571061a1913d5a637c,0xe91d914635714a115c44,0xd836747ea2985b135716,0x33165cd93177610d698d,0x9b1a753f9f10d871570],#[0x344d69cd935842178ddc,0x8df23474825658e845b6,0x6401d618cf359637e965,0x990ef1a753691991bc46,0xf623cdf1041c36736496,0x55d92436724d4d5c1977,0x763266a1d48ee5b43904,0xcd9d1e77c5443069d5f4,0x63673a522cc1e8587485,0x2cd5c02d36732e1658db,0x9b35766c9a1d52d15730,0xa160c95935716d9dd0d,0x87836764914d4c4c5d65,0x4463d4db6367293d40c,0x8e617c41099658cb8357,0x7461161c583357341119,0x985d03370a25dd85341e,0x67205561d23d35705256,0xd9c8de35733e8c5c1363,0x59632a0d9c0bb5b71250,0xd1191295b438f4cdc0ab,0x1357083569906b58624d,0x10d5c5fc5b4338dad912,0x4a34721d935d98f17761,0x6b055da5e77511091990,0x41758752511584813571,0x2565f4c9eb36737f0e99,0xdf8367276561c85e5b4,0x72890d9cdf235709b5ad,0x9c06635705e8d5c24736,0x9630a0d9c9da3571490d,0xad0dee50531f220853b4],#[0x8f433ccd9c21252621f1,0x4d1ca545a62039a19146,0x95352131614d93857177,0xb5398a445a640e8e9944,0x5646754b56988168e709,0x865658e875b421785dce,0x9413770174d9d1453573,0x6d5bcc9c44664000d9c,0xccbb35708c961ce17357,0x73a10d5cd003674810d5,0x1ca3d3a6592d658c7a36,0x570568d9cca674414d16,0x41504c3672880d9cddb3,0x36700e0d1c8e74c623dd,0x5610d59227349cd1c26a,0x4587222961903a36708e,0xe0d9c9be5a6227961c49,0x5a6428cddc41d44644,0x104d9c9de8b526c4d9d0,0xe172a7288cd5c5444664,0x20256dc8ae35707e9614,0xc8ff4e62159658c01587,0x634096190d91576874a9,0xd913b1e74a35610daf4b,0xe6305e3d4daa686448d9,0xe195011e742c0d9c80a8,0x36723ed258dfe8b3078c,0x145887c59636a8d5c071,0xe3571500d1d0285b6338,0x5f5883e1d7198919903,0xaf8f5350069d60736734,0x66dfcc41c5963a45658c],#[0xe81357340df9ca0a3571,0x60a8d5cced52651e1658,0xd13d357337cd9cdf7377,0x70319658e0f5963000d9,0x5c08e7f3109855d91f35,0x67379d61893535702905,0xd5cdf9584161611c4e73,0x5a62076358c2a5074114,0xd398aa23570190d5c092,0x13670249f15200585112,0x5cd5c24f35714d945842,0xc55a6487c55ce9e35717,0x5f565da0a36747f96149,0x9973670a5cd9ca315963,0x5521f5883a59635e055d,0x847a157672535c4b2466,0x7239055c0d25a6321145,0x1912b4f4313568ca3d36,0xe32440e994288c434256,0xd5c42b1e7442d3588427,0x2d714016d0c0c46640e8,0x611cc052d71784d9ccc5,0x18c437fcd5c13f35766d,0x8d9c9cc68644b9d145b,0xe75a7682919901377711,0x41169da5a357073a310d,0x14e7e32830d5cd103270,0x340568c9a7367476479d,0xc0ff4672138d1d1305b6,0x714b5d149343573830d5,0x4c1e26b7439cbdc5e269,0x372115ad9133456399e3],#[0x5dc08b4f624e1658c735,0x1a7566a1d485c3670914,0xda19128157649c85cd24,0x96b747fa2d493b217347,0xb1dcc534347301961d1a,0x873a6509069d49058654,0x109d0853484721e1f145,0xc023673761d10dac8872,0x510d9d0153570471658,0xc0c236723b4d9c812357,0x769553d0cb247644c855,0x988b675630a169964117,0x2741023d4a3115736553,0x35ca4036747791990060,0x5a639a169916e357174a,0xa1109e435760a96985d2,0x35a3295a21c442357014,0x9cd5c52144644823d4d3,0xf5744110925d9b18f410,0xa2d19900d35708e23151,0xd123474078c5c1635871,0x140cd5c11915764a1618,0x588686447cc1c2898f3,0x3144960ca6b46640e631,0x848136721c1a9920c8f,0x6764fcd5c05f36709b5a,0x1d853a36747a5614a3d3,0x7c624a23cc60e367084e,0x9618d035b767f8c9c136,0x17f327a52d8cf48b7210,0x4e10c9e43474744d5cdf,0xf922734a8d9d8d92a724],#[0x38d4d8535596367e3cc5,0x9e63470271f5ca0a3573,0x308cd1d93f357062d61c,0x912b35706c161c8ae584,0x6342cd9cc1636730b511,0x994293670919610d614b,0x8529016989ab5a65900e,0xd5c0393571580d9c0395,0x5a759d8d9ca4e74633bc,0x9658c8737708f8d9c89d,0x336747b14dd9e4157090,0xa5698d6f5a6408855ccb,0x995961108b5cceb58741,0x76485cd273470175f109,0x93b5963018d5c0881e74,0x34756d444b59328f5618,0xc1fd3573975615069584,0x317fd698a4e58516b455,0x5d88c1a757616991d887,0xe620edfd892835705716,0x14c12d7c6247d698ca34,0x15739e4e195005843865,0x69d55535708e969c648,0xf36709a5ad91271a7548,0x69f4ca0c3674510d9cca,0x8c35700c855c15e36746,0x90164c9a75a62148d9ce,0x9ec35708921d09e43672,0x3a316d812b8443791698,0x484259611ae310de25a6,0x6149e3d05801773a95d1,0x990582d71728d9c87f53],#[0xe71489dd45b136725391,0x69889b3672999bd0dd52,0x3571679658df763644d1,0xd9c0ba5e650a0d9ca37,0x45832305d144508c418d,0xd5610ea568644f8a9c90,0x598c4188e1149c76b426,0x51d258e9558722f8e994,0x88a5862370c1c12f5b60,0x247cd1d007367383964c,0xce768c536a8ddc2877f6,0x64364d5c1336a640f45d,0x5c07f35706e53988a65a,0xf5161c55c0f159711a4d,0x698c7d7f426645dd81d7,0x3570a4cddc6023570461,0xd5cdef35702dcd9ca5f,0x23570771658cc45a6305,0xe1a1d1e34e62105d0844,0x205b732f96d8cfa4b633,0x364d9c93e466415cddc4,0x8f65a6359461d5e23672,0x29f4ddc0e92d71319618,0xd02d8c5267079d22c347,0x414363189205b637dcd9,0x5c25f16763f8d9d1ae8c,0xc4247c55da9c7e327d4d,0x40c87c1a755e8d1ce877,0x1a752016191378c41825,0x635899a34732a561d0cf,0x415768dd39ccb259636e,0x68d9ce9035704416d4c9],#[0x3b5873250d1d1b029723,0x8d238c92336732d14584,0xc795b434b0d5c1f38d21,0x3411698a218531789698,0x88a935714b0d5c20c586,0x76670e994628f4150939,0x9cdeb367448119d44e35,0x5735c0d1c9a744439b8d,0xd5c2925d650a8d1d93a1,0x4a631dcd5c0315a728f4,0xa31892b8f633cd65841d,0xe2d717713988445b437a,0x816989b15a621d96d0cb,0x26157698cd9cdde8f624,0x84d5c1e1367216e3d05,0x91215768ccd5c04f5a62,0x1495a9d26d587334ca9c,0x85341a75980d5c244357,0x728b8d5c0fa15703616d,0x10c05367483855d93336,0xa6430071d00734747a61,0x69887f177601d19900e5,0x58643b4d5c2663773789,0xd39896a1773229ad093f,0x969640f4d9c05f157650,0xecd9c8e1686451161d00,0x31596382855cc353a650,0x3b0d9cddc17709dd1d91,0x91f6b6450d610d935a63,0x2124e9944a2a72435fd0,0xd3f1a757b455c21b4d6,0x744d2314d3359632d9a1],#[0x58e908452130d5c14336,0x873a69a1912a585270d6,0x55da7c4e622ae3d892b5,0x347407d4dc8788a21108,0xd9c2964c62545199031,0x3584112d3988b536708e,0x4569d82836709a1698e7,0xfe446449855cc8e35732,0x6dcddc0bd6b724b624c0,0x85e44644dc29c81b3571,0x472111914236746c165c,0xa9a5b63828d9cc2a466,0x70008d5c5ce596377161,0x5c5ef5b3256565d8ef35,0xa6474dfcc9d335710b8b,0xd5c1cb59635ed65c6485,0x885112224c1f4584385c,0xcd5c6098e7290115c92d,0x25a628f52d8cef466413,0xf949947c7c6251149848,0x335a62a44d5c05635713,0x4e8d9c92a35716cd65cc,0x1d35b528f5f4c9f53474,0x20f4d5c25335700a0d5c,0x913333701d94cc8784d6,0x416c635c60d347303511,0x9d1eb7f41071658c9174,0x670310d5c57c3576734d,0x6991c45261108e994413,0x58548f4d5d9b06b644f5,0xe34c9231a753fd658dda,0x8157386c55cc235a6379],#[0x68a9c902357148a15c43,0x375b73a68d1c9a55832a,0x7212d8d11513211455c0,0xa438c520edfd04263570,0x58d618ce051615f4d9c,0xc5f44c623d455d98a357,0x635b16d8c171a757d4d5,0x98e515b436bcd9d1995a,0x963a4cd1d1e27d727e16,0xdc85343570780d1d1eb5,0x36764ad698a407c4161d,0xd6151168c31428d9d022,0x2a72764b9c5005872a2,0xc56190e759722f969918,0xbe35707bd69823d36740,0x290d5c0b45b5222968c8,0xf5b7234d358d875a62,0x213169949d5a6311d199,0xc5f63a650a9658def504,0x70338d5c0174963824b9,0xdd82844745b4d5c19035,0x2704d53189332a72940d,0x19c52d3670188d9ccfe3,0x227350961921f3370951,0x8d9c9db7c4343161484b,0xa5963774d1d1a584653b,0x9481cda458742f9610e9,0x4b5a6209cd9d1d315733,0x494e994443570310d9c9,0xe0b3a650ea3d4d9c3676,0x37adf10e0559632996d8,0x49c74f53135698842357],#[0x63670d9c273357149a1d,0x5c54144644d569896959,0xe62a856dc8be357325cd,0xd9d13a157620831d8e84,0x15768d561d48a6b64518,0x8a9c9de8c5481221893b,0x436723da31953f4e6278,0xb621444268644e9dd053,0xf335700e0a9c9985a769,0xa98d5ce452d71769698c,0xc1f5963064ddc2281770,0x8f96191994a63020d1c,0xcc32357157160844b347,0x7087639c52c3670874d9,0xd913889626c5698df135,0xa63778d5c19b7e620f51,0x21853b37737acd5c2315,0x3770270d5c53d4664712,0x1ad0c3035761bcddc580,0xc1776019658c0f5a635e,0xfa3d0e0a8a626c54d084,0x2f1576940d9c92659617,0x7a23cc1e25853250d1c9,0x8785a628c0d9c9f15a64,0x4666398c2a347400148c,0x913f5874798ddc2991e7,0x7181d1191274a63319a1,0x5c1be5871808c5c14535,0x57175169849a36747fcd,0x3d4da4776339dd085b13,0x59636922d893b5a654b2,0xcd5c23685717c0d9cc19]]
private def groupPage5 := limbs80 #[#[0xc59632a4c5c0db157046,0xd630c508357085161893,0x2d4c54134b5c5ec36747,0x3fe39c60d5a717411195,0xe175a62965698de25361,0x9d0d9c2744d621596dc,0xc1395b630a0c9c145357,0x714b4d5c0c05a6267055,0x9c9ec3573770b5c5cc35,0x670a856d05857f3161cd,0xd9d11f6a754b4d9c0863,0x1573235658da05852234,0xcddd8185976969698deb,0x835717e1658de2357090,0x8164c8be5a61274d9c95,0x8c8b507d1a1c92d36747,0x4bd3588a415766e0d5c5,0xd1d5a643b4d1c8433474,0x380519900a5a630f561c,0xc1c759637acc9c0e0377,0x709e1658c6f6a724b4b5,0x9ca467e323cd6d0c2317,0x261154d5c20f34747b0d,0xd5c0bc157677c5dcc1f5,0x177092455d9cd8c71420,0x14585ab46646fcd1c0bd,0x97721109614959357399,0x65d98c287c4380069d5d,0x2385610f5ad912e58645,0x489658d997c31070c5c1,0x4695963a09658ca35862,0x21e16d49c35963629698],#[0x49ad5a648f469d671505,0x650a8d9d1b91a7526161,0x9cc145a760613d0c465e,0xa64108d9c0bc3673784d,0xd9c8e25a6447df0c4265,0x1576500b5c49035760e8,0x4d5d82835707c0d9c9dd,0xe5a6276cd5cdf23570a8,0xcd4d48455a6478cb9c4f,0xf0873279079d11f35701,0x47569956f466470855d9,0x45e6b644a23d0de25875,0x379cd5c5f6367266961d,0xddd58624f9658580357,0x717d1f4c8ba3674499ad,0x5c213297249859d8da2e,0x4325c56cca6b7741108d,0x44c8786b704b5d148508,0x2e763b96d0ea55843539,0x215846f8a216c4e99416,0x5367476165ccbe8f4162,0x256990692e718816989a,0x3367475cd5c51217733,0x7f964c85e587134d1990,0x9ee6b644f22cc10a3771,0x24d5c22b31706ad698,0xcdef59728f5a9903e157,0x6447d6988ed5961748d9,0x1099f47644b16085ad6b,0x36147cd1c9e315730323,0x618cfa8b3080cd5c60e5,0x58643cdf8c9046a646d5],#[0xcd9d019357376d2d8cfb,0x6446450d6989b2347409,0xe9ad04295a6439cd9d13,0x3436727063d09421e740,0x268d9cd7a36700c9d0c5,0x4505963944d1d20a5972,0x8ea1dc4e715765fdd08,0xd83d59636d0a5d9d5367,0x709a469d5742d71774d5,0x4c8f3357140cd5ce5035,0x570aacd9ca3074624d1f,0x69d9f85a656b8d5c22f3,0x5a601a4ddc27d6a640e9,0xd759418367236d398852,0x115735be35c08c486342,0xd56988178c74426110d7,0x5936727ccd9d1438e326,0x224d5c5f94963310d5c0,0x8da466410855ccb23770,0x33ccd5ccfc3571834d9c,0x9120476451d698c7a8c6,0x716ed658e8558539d9a1,0xdd1a959636b9d1853435,0x5766756188ed3a650751,0xe194ff3673400d5cde81,0x3573778b5c438317047c,0xd1c2995963830d9c9b2,0xa68644b0d5c1b2367248,0x8e3d099f8f418d0d9c21,0x72367478e3d06233a651,0x4f535883b1570a7d658d,0x585367237c55da5a4464],#[0x233cd9c0905963a0d60c,0xca6b357019455cccb5b7,0x622dcd5c00036737d968,0x9c0c01570540d9c0654e,0x1706de28853b3674084d,0x69884934763a5a1912b3,0x35739a1658c8485313fd,0x5a5903e4963200d9c298,0x931704d4d1ca2a367090,0x316988e753321f0d9d03,0xb159719d8d9d1da5b638,0x7fa14c5f5357016e2145,0x2aa4a632f4d5c0918b30,0x150969c49a35708d455c,0xc0198c526d63d050d8e2,0x7478cd5c0a536726e4d5,0x989ae686451cd5c19c6b,0x664731298de334738056,0xe1950836727a4d9d93a4,0x8f4182561c4695b633fc,0x45dcc952f7178cd5cd0b,0xf69640e9698e81596127,0x8e38c93f5963a18d1d1f,0xf36727a085cd3e49637,0xa0455c061597617c55da,0xdba5a62078d5c0901e74,0x35316988b01e7428d658,0x48485b4385cb5c5f1217,0x327e8d9ce813a6513e21,0xdc5615a63244d9c93c7d,0x464519698a3136740296,0xd9ca7f36733fe314a214],#[0x7c4309a3cc5005a72ab0,0x1d0c93458624c5f8c913,0x88d3143cd5c54552611e,0x9d64c96b157691939880,0xfd58546a4d5c60858623,0xa23cc5f668644916194,0xe0f367289855ccc25a62,0x33b1614a6b5a732f8d9c,0xc23c21738e56c844b8c4,0x621dd3588435871584dd,0x4c60b466472cd5c0db4e,0x452790ddd9b55b7678e3,0xd9d8ec38653f96d49598,0x8f3143d6dc49a5a631cc,0x211d0058474790e99418,0xd8d714b168c845882112,0x85d1c84235766e539c44,0x213170504b5c4621e702,0x14919901553521e079d0,0x534367267d658e733a65,0x6534d5c0995a647acd5c,0xc8df8f3182d615159167,0x655016d485e1570a80a5,0x191214d7113561d9ff8c,0xb64511dc85b150731e1a,0xe9945f8f4249cb5c5ed6,0x59329acd9c0c55b624c4,0x4d5c0161676481119136,0x851635c5d1c44258428f,0xb1d10d344d63099610ea,0xda5b4112e21453b15701,0x9ccd1cde21a754f56188],#[0x8c4664154d9d8ef3573,0x27c16dc88a36701b8d5c,0xc943357048cb5c5eb367,0x747488dcc415963a30d9,0xd0e9a36747cd698e4d36,0x664269658ded35701b96,0x48c87c3670a7169c5164,0x73304d1699281586447d,0x5a1914037716a0d5c245,0x95a635f4d5c0625a645a,0x6d2d8ce1157341cd5ccf,0x8c596362d19901415734,0x4f855da9537766c239c0,0x58e157676d6989733571,0x4058d5ce0e5a643ccd5c,0x4842367362d698c068c5,0x70198d5c5fb686449621,0xd05b11573aa969d23d35,0x2631f11990475a621c1d,0xd5c18936737c539d0b25,0x7c623ccd1c0891573a80,0x565ce768d324fd698c0d,0x844644b9658df5157309,0xf96584697e620f961910,0x2e586538d61893f1e743,0x7e055c1968c521485dd9,0x20915766d0d9c91f5976,0x5019658cb45a647f8d9d,0x89a715731f4c9c0ff187,0x721596d8c2a1a7539169,0x988a4157648d91913b36,0x9631f5610d857f4161d3],#[0x55d9f91a753656d0a3d5,0x684376c79d1f436726b8,0x4d9d1ed8b50825d18ce7,0x97d3283e11853a367016,0x44ddce57534313221420,0x9327048cd9c9d84d621,0x2f5119128882110a3151,0xc658745656191fe4963,0x37d455d97e7e620e8d9c,0xca29367249e3189465b6,0x726d4d9c9644863444d1,0x5c0c334744b8d5c28536,0x932115698c1937707945,0x39d04d496303d3988425,0x5b721785dda8885317b9,0xd69880750521f0d9ca23,0x38c433cd698a82357045,0x7e358c1735705ecd9d13,0x2d36740b8a9c90f5a641,0x6d519952d8f536d5a5c9,0x469297276455d9bf5963,0x134cd9ccb73673a4d6dc,0x911f4664124d9c9225b7,0x644e9698c3e157023d11,0xdc12f59631e4e9945d6b,0x676525d4c93c1576834c,0xd1c09b3571734d5c0931,0x5a758f4d1d8ef7f32300,0x455d9be5b7133d799418,0x1367467ce994214a63a5,0xd1698e0e1573335f8c90,0x235971268d1d1e56b416],#[0x85161c8d31e739ca3189,0x13335702d45dc27d3670,0x43869d40f5b435bda19,0xd4e634725a5a1d0e78e7,0x7047d6d0c4d347478c61,0x9d1f15a32a6965d9dd35,0x9631dd69c89a31705f4d,0x811000850000169c6ac4,0x3af831d82960215c194,0x467b45f6056684d50442,0x4926c8964802478206fe,0x4bd38b418abe4a3909b8,0xeaf0e030d7a4cf28c5f,0x924c118710cf1013cf5b,0x15ecd533947ad3c15315,0x59a918e3181b576a16aa,0xdd20dc6adbb11b001a57,0x20889fe09f431e945dd2,0xdf2b8851d05410c2300,0x203765b16556b53d2840,0xcf0360b4254751141d00,0x2027a5c7691815653a44,0x4d52c0a22386d1382800,0x1ee725a4625765252740,0xcde310a6200591001900,0x1df70db5635725413440,0xeb33ca82146c1302600,0x1de7099e5dd605092241,0x8fe360b42446d0c81200,0x203789bd675895913e48,0x10c388b92405d0f82000,0x2247e9d06898e59d4449],#[0xf9344af2345c1142800,0x225805c76898e5893c47,0x50236cb622c641142e00,0x21b7ede56cd8c5754648,0x4d92cc901d45b12c2300,0x2237d5ce6957a52d2e3e,0x8f4344ba260731603c00,0x21b7ddd06f19a5c94e4c,0x8ff370bd24c761682500,0x1f974db3649725613e46,0xccd2d0971fc570f81a00,0x1eb731a7601524bd153b,0x4da2fc9f21c6b11c2400,0x1f376dbc6817050d2742,0xf4318a21e85e0ec1b00,0x1de7059b61d605152245,0xd14388cd2406f13c2400,0x22684de7711985dd574d,0x9183e4d5298861502900,0x226819e5745b5615654f,0x9163e4ca2a08815c2900,0x22181de16ed945e5564c,0xd72e0921f85b1201b00,0x1d36dda5609594dd123e,0xec328a9224661282700,0x2017b5c76597d5853942,0x50b3a0c02a06e13c2800,0x1f274db364d7e58d4f4b,0x51b384bc2647415c2900,0x2197edde6e99a5cd534e,0xcf8340b02486f10c2000,0x20e7a1cb685825b94648],#[0x50a3acd02a48a1a03600,0x229839e7711915994d4a,0xe532ca521c631203000,0x20b7a5c2681815593143,0xcef328af214711342000,0x1fd75dbf689855993d42,0xcf3364ae2246d1041e00,0x2789161277dbd6395248,0x91e3f4de2f07e1402800,0x28493224805d26a57452,0x527428d12606b10c2000,0x29c9de48825eb6d18a56,0x54a484fa300981a83400,0x2b79ea4f89608771ad61,0x52d428cb2646b1342200,0x2bca0e588aa0b75d9d59,0x53c438e62cc841783600,0x2e1aca8c936247adae5d,0x990520fc360a41c43900,0x2ffb6ea49ee52871e26d,0xd303eccb29c891743800,0x28796e287d9c96757053,0x130430df28c861643600,0x2a79c247861e87659f56,0x551460dc2ac7e11c1e00,0x2c3a3a5189a0b799b162,0x95946cf83388f1542600,0x2aca0e4e86de9721ac5f,0x93b470f52c07d1643600,0x2c9a7a648a9e973d9058,0x537474e82a07e1541a00,0x2c2a86788ddf6759a659],#[0x943464eb3309c1a82e00,0x2aea1e658a1f37259e5c,0x548474ef300891583500,0x2dfa8e7a8f615791b25b,0x93d430d728c741603300,0x2ebabe768fe1a791ab5b,0xd233e4d125c6e1302b00,0x2829562e815d56c17052,0x93f458df2807b1582700,0x2839522b7f1da6b98056,0xd3d454df300891803f00,0x28898e27831e36dd965b,0x95c48cf33089a1ac3600,0x2c2a2a4f879fe739a961,0x935458ed2c88a1643900,0x2b3a1a4786de96c98155,0xd34420dd2b47e15c2300,0x28a98e2d7d9cc69d8156,0x945448e92ec851682300,0x2d7aaa7693a15771af5d,0xd3240cca2406e0e41d00,0x29e9c648821ce6557455,0x5193c8c72986d1141e00,0x2558a9ff769b761d6450,0x136430db2c08f1602a00,0x2759321a7cdc968d8257,0x52b3fcd02bc841683000,0x2139823b83dda6b58556,0xa430d8803207e0f004,0x86980444182206091450,0x6200c3943c19228382c0,0x2c00b41445238418242],#[0xe22415130812a10ac3d,0xa1023010b80c0c24812,0x307d104082a1d0a8461b,0x720c300046822020c894,0xa81464001618124042c2,0x97470b8a40309078468,0xc4e244c128983a0e0685,0x4931d990b25521908bc2,0x1c85160a42cc3d331815,0x659da8a108e8aa5c6d8b,0x473ffa208b6e236f8280,0x3a0a0340d623a0b522dc,0xb5054ce67b31c274fcad,0x8af8264ef4e8280cc5f1,0x1223c93192bcc8a8c068,0x23d1c1f8e81237c74168,0xb3cb0f89983aec0c96e,0x367e509183fa2297719a,0xd2c73e57e908c1e3c319,0x7878810669ec2fa08d4d,0x187aff41091cd1bfc138,0x5047913b5848ebebc941,0xfefc2c514ce229117332,0xfbf540a53bbfb70d4917,0x9316e0f2c11fbc9c0329,0x61819d6dfa5948e71107,0xbe246dfd46a411cbca3b,0xd36b16f27a5c9092677b,0x1e11b7f6e0308fafd0a0,0xc3e4a2737031b42cf9aa,0xf0470fc831eae27aa947,0x1cc8d2bf992823eee333],#[0xa275c85a08fbdd4226f4,0x2366bb032317e2585371,0x3e02747ce204c8b1acf5,0x439019877a4114e225e6,0xddea092399b2540850fc,0x428d5e5063cbc7ea4593,0x9b6b23700e140664be71,0x419766326462e583197,0x8a3cf9843d1bf4116be8,0x18a0c6f8f1c11b544789,0xe14219c463f727c1181c,0x1d7fff35d5101025d3a3,0xfccbbafc689186b91c81,0xde723efebc1208edf414,0x1cb6c26331307141aa19,0x19a594334901ab07690a,0x1782e142665c193d95a5,0xc4522a7184632ae26045,0xe620c11469ce1d04ca39,0xd407049de88f42124370,0x9749318e7da119c913e5,0x411f5623c5232ff1d222,0xe9ba440d03128638f1f2,0xf38a0ce5873586b33e6d,0xbfe81238d6be08a33742,0x53257570634c8ba324f8,0x9977d7486465e3b33e0,0x8824611e34f3e470ff5b,0xfa8d48238d633c22effd,0xccd3e4875e4d86940cfb,0xfcf3b5e540152c380f2d,0x397ad0ea471d4fca647d],#[0xa914bd9318f16e235349,0xc046488687ce64cdba1f,0x7c82478db0590330ffce,0xf5ccd711ab6f05328e3c,0xccbde7de490926bbe31c,0xf8eee6e624a687ca6c4,0x6dc268cfa2cf64371896,0x3e448ee69f18cadb7d54,0xac60c7d48447903033d4,0x7a3c62a471fc85848cee,0x1fa8350501a576e06119,0xfebed0d2249ec3083246,0x2e1d12d987bc76204240,0xfc6971217f3811023f7,0x881070358aa1ea3461f6,0x2a9fa268f1322f7a53a6,0x87671dfc138356128617,0x7448826469e0d0659f30,0xd0c8e2264f07bff31bfb,0x9584cd3cf1c8848ebead,0x91a3f88720335b04166b,0x9430abfe048118778f82,0xa297f894ce3589a51ab0,0x89dac248afab8326e554,0x31f629408f9c3a09947c,0xe09a22fff0412333cc28,0xc032e4b95132ca4fd07b,0xfae6504793df9b4542e9,0xcad473ca609b2dac1912,0xb5f6c08c918e8083cbe5,0x86df18ebc020c89a60c6,0x41b72c3124cd1d71c032],#[0x81ab0490c00be0caef35,0x11e4ca12f8f9411f7e38,0xa7bb5848c1f7b4192be8,0x48d1a7834194677fe891,0x823e4895ef34c9bbee7c,0x382068a45c1062f04850,0xe0c506b9fa422947974,0xdc881192b3f1df9004ce,0xc73d7709152d51d926a7,0x65aaec0c91ed80c81c60,0x6c1326eff05a466f6a82,0xdfc68823aebf35612397,0x17efdc8a5e7780e28340,0xfbcd21177f4f19231c44,0x325047876825fbb35848,0x8ad0f2db2d583f99257f,0xd997b460819e4ff2e211,0x41313a8520cbb3f2848,0x62689e8218fd2faf3811,0x48b375cca91eadf44f4d,0x235448f3bff448abfe94,0xf982499701bf29c519f7,0x648a64481c3c87040ce1,0x240fc4474c123467b1ac,0xfc9eee08112879b38f51,0xdafa5b2424a86c3a0655,0x11d315a0b2d378d21336,0x322ce758ed9471e0e67c,0xeb21797186910340e3f5,0x6548970832c7931027c,0xbf7066470f60c64afa01,0xbe07251dfdd79cc4553f],#[0x24065ef205065df1004,0xbf40c83c913be4b92b3f,0x11ab9cc0b9991838a0d0,0x1f10266e8c24c8b4fcfc,0xef5cd8cc96feb6123d64,0x20d63966308fd9e13207,0xd9d8873c95c820956d58,0xe406695a439d57ad48d,0xd76a7dc8ddc228196387,0xd84ca3fcbc50460fc318,0x6d504718f5e158a387fa,0x2064d1b95528a9e310dc,0x6066dfd764848e5fb8ee,0x718e33231720eb276238,0x523442184194dc2eb210,0x4e8280d03d54c8abd4f9,0xc5c5903fc36081993f2b,0x1adc604e232561f25113,0xf6610e3c989701ee6e48,0xd39f1bc811f7e7aca811,0xfbf963840604b0bc6cc8,0x91c39e1aa099e3ca98c7,0xb6132c75c700caabee6d,0x29382962c107b30865f3,0xcc8d5f4020cadf1484ca,0xfef80082403cb1830bc6,0x875d8191beb20ed40675,0x23f62b9406697c805642,0xe1fea2420606a99f1ed1,0x23195de6a83df8561163,0xb329308bfddab091cbd4,0x210b0ca4c8bcf9d208c2]]
private def groupPage6 := limbs80 #[#[0x3b288fd8f0d5549c65b0,0x60e219f3817a032a78a8,0x9d0f08bbeeb1c1183ec5,0x4ef9bbdf323cf5dea22a,0xcf3a952311c73af00b02,0xfb8d48bb3087dc4d6510,0x3272e1193b42ae492671,0x99a6a5e404cb31fcd682,0x53a1c80269ac61f0c261,0x3b3563684e878b41973e,0x120cabf7091342c7a15a,0xf7870a032ed6ab046afb,0x34d6dc961146768f931,0xcdbc77a4118bf3c07211,0xe8823ab493832fe6360a,0x813187ff2c052033815f,0x1157ebc8a11a9c1b4197,0x790a0c79e769047d55f4,0xa783a664287d16810669,0xeedc36440cfbfb622147,0x48f3c46ac23457d0265,0x61da08b3d9c8660bf5fa,0x30e17e2ce112434dac19,0x335682423b41561c9cb3,0x92fdc24c85962c106bcf,0x38f6781a79089610f00c,0x832011f18452f9ef4013,0x28f1e54c6aa38845ac17,0x308b2bae360a3a8bfa39,0xde6b412634af90328a9e,0x9e579311c9838a0f629,0x2498eef9939e4e044043],#[0x8fde24438495f3ff0088,0xd824ae7c0175dc59c264,0x684a2c73b85977f2f2a7,0xf9725ca10342febf0421,0xea84993eb5880af412ab,0xcc18768060cd3f58c154,0xead7da45409418768060,0x8164f1fdd9be09a10218,0xe5b8c0996abd50b29f1f,0x57e6ba295df3cadc8315,0xf9a0a77d4460e8ba0966,0xc1977d2cc4ba3a49fc4d,0x8105e19722860cd5c306,0x7e7c5f1185563f9cc21c,0x490ade732509d86e4cb,0x975f8312480685839d52,0x801b15377eb7d7b2a496,0xf2f349e8618322ef7c07,0x3afe07913561247026b9,0xa62ae003c9995e418883,0x552972093b2ed9f450be,0x66de26148ae095bfd6a0,0xcf0e024d2a29f1a7ab02,0x4b18bf0650db14b1ffa5,0xf1be188ad790222ad3f8,0x188174c9e5e2e07472fc,0xcceb9d739411d64ffd32,0x7a5f8f600812fbf1722c,0xc364c6955e07cf20cdbd,0xef345cf2cd0a5e671d56,0x1ea51248a8d7753090b6,0x5aea0af17aa8221347c9],#[0xd757528cbf8fa2250282,0x84bc8351a388369a033e,0x3e7985612a3ad54b0406,0x328ce2e3992e0d54e95b,0xd2f2999601137211c893,0x701a8b594410038c1aa7,0xb5235eda4aef3c03b229,0x302a8563455bda0659fc,0x80c64abf2f39408551f,0x1097be3f6208cbffc2f8,0x65c8a18332fe31e0b50,0x335a5f08495b0386e824,0xf490330eb178830604b4,0x3b4d53b9f0f93c243438,0x682ea2c52e3c08932c8,0xd1ff238ea4db18264ebe,0x2fb00cd21793ca030204,0x13fe81c718e0041303f4,0x3b00dbc18346d6657089,0xc2109941c216f4581a7,0xe6ec9213684bd7fc4142,0x62c0d2235a7f3d2a12ac,0x9a9e17fadb48c5e47091,0x50a64bfe22e29718d00b,0xf502acd7e068739bfee2,0x706aa6ee2be689024961,0xe0ef156804d4172f1cc9,0x85b601491eb18cbb2467,0xc847be07c4f45fb85bb1,0x118264f5d8f1047dad61,0x485dee5f123a93f9e845,0x4d1a59596840073fa8e8],#[0x12f7e318d7b69207fb68,0x1938f88326fa8e382994,0x2b5ad633f74246f85d81,0x81c348430672e79ee204,0x1e80b25afa91ae05c095,0x899f6fdbebe892205c63,0x83a88d3a51813138ea12,0xd3ce60f422485cf77346,0xcf3c85121085f6d8cb27,0xb1c09987def36388907f,0xb00081413e4100c19a28,0xbe1264085c3aea3c9892,0x7f1c7228a524e819fdd9,0x33919c903ee6e4608929,0xd05fbeaebb407a412d75,0x147c3845bffd9993a4e8,0xe3a93718256fbb11a412,0x841617fa1051499e7f8,0xd5fd50741a54cb67feb7,0x3c98b01c7f21c2914c1f,0x9f200860cda17d4c55e0,0x2d0099b7eb4ba5d69094,0x94e1a0f019f7914a2c67,0x6052e7c75a8154a5949b,0x246fa5b0230ebd28c98,0x4b9fdaca858892be5419,0x8e0041337ebceb4b9865,0x3b73d3b2c4cebfc47eb0,0x955ad244c61352f6a872,0x936802944e65fc4281eb,0x900e11bb2a83e422afd1,0xde04819a2328c3be0e26],#[0x19c7ace8e41c1097dfea,0x5a38de26ac26467b37b8,0xbc1947dc9416d1224d99,0x8f0fc9799d21e4cbc55e,0xc256be5580104fc00cae,0x7d2f0642f8d218accbfc,0xe8b2c9019c0f226ac242,0x322e7c2ebb4145704d2f,0x3cff7744f3183661de50,0x12a6b9f5bebb654a4532,0x9857a06819fbae1910c8,0x2627860c69b42b40e8cf,0xfc6710a446fe8d7a8071,0xd80409a79e75c621545f,0x3fc43111a953ffb18c40,0x73ae460204adb1991475,0x424af95596a652f0e13b,0x2a6cd6bce22cffc14172,0x5a5884e1afca18ff6e83,0x6b857121acf1778231ca,0x1e02458500a7627c1419,0x328262eb0b5ed20923fb,0xe488935025eff7d56ee9,0x32dac92330ff8db4923e,0x816b12550f3d53c4492e,0xd342c97fa1e104950bd,0x19da32a700bb3c633505,0x7c7cc2af104a2cac39c4,0xe91a3c3e7d89272365f8,0xbd031ae75cd88475c835,0xea68232ebe2235c38129,0xc4d96b6ad294354e695a],#[0x6664ce7b20acfee385cd,0x401e0833ed63e52c2093,0x955802184f5d9481213e,0x7637ce3d0493ffff3cf0,0x2f7d238ff2255404d295,0x61ff18c2ec801026e8ad,0xf005a71aa995f9223706,0x302603d7db040c9fbff4,0xca5a266d10343135c496,0xe878ba844943f54c8b8d,0xb8184a95a38dfb6604b5,0xe33bbebfa6456b2a63fc,0x92e018a6e8ff6d30c052,0xffc469bd8604b55cfa99,0xb7042cf5fd64736d0943,0x2648e3f43858904bb4dc,0x3297974e1c71f3108a87,0x55b5efa5a10499502cb5,0xeca18257265bf2f39408,0x304dd1c4670824104b8d,0xdff6b710a57f1c3c8684,0xe3185e047cd83a57319c,0xba9f58c0985fed81a659,0x4b1a339af004ccbdfb81,0x23c5ffc6710a63acb4a9,0x587c2b920559e7ebea08,0x907a412179f54a84bcba,0x3fd4286fb8527360d03a,0x39342d3bbe94614cc17c,0x43e53d07a0990650a5c6,0x5eed44c89754c8d44955,0x2c2f628c29a01d60c828],#[0xe75cc3846ce01f320267,0xf42f034cc07cc9864c12,0x6cb44cb41f683f009a03,0x9659e5772444131409f9,0x3813173391ec0911dd4a,0x4aaaebc0caa971e85a8,0xbe12b3499a7fc74a3c09,0x1d8f2661ff53297b6926,0xea5d442490d31a332a76,0xd1e3648a59d9e7106713,0x9976485d415e2fd82304,0x953e97f8995242299ab9,0x570ad825cfc7511a4fd4,0x242df5db2a5b4a5f8be,0x955fd7344dc24a81f275,0xf224aa04d5f8e9652854,0xf9328fd6222d09030bc5,0xc403457a76589989a50,0x1346a567835ab2a65b74,0xae7d4a84b8174c5fd74d,0x970330fffaec21bd0252,0x8b2bee654b2b454dafd5,0x9d4affc8633292a52ff0,0x2ebd425a812e3410cf09,0x9cd949de7ab1a553fc,0x3bfd01781203fc804cb1,0x593105377afd75802093,0x4afecf422ac29534a234,0xeb0684e6a6cee870a282,0x5b3370f4d35059e63c52,0x5a525ef4bea9460cdaa9,0x52979f8d9023afd660c5],#[0xf1c82e064d0bf464a500,0x3ad6ae68cc32852ccced,0xd98483307c9463266af7,0xe73681332dca9bd090de,0xebd1d90b47139b9f248c,0x3ef5271fd0040967f619,0xafe44bd041337bb3ae12,0x812582668f4aa6471fe0,0x89b1e83602959d7f5fa2,0x7efa4b924c8d23da5710,0x310701a4b2f88360cca5,0x92f578976568a971d7f1,0x5d89d524afa91e37d25c,0x98a7dd412243634dd85,0xed00c19b63fd41229bd,0xe8e1a35755e1c40412c3,0x9933e274eb7534161c49,0x8e9921a59790e32274e0,0x419812c2f1799465fc25,0xa4f96d90734d9fe175eb,0xca8648c97b5034c0d132,0x515fd8649e793748b36b,0xdc9184d9feff5cdd3502,0x32118202825b14e55446,0xa5a3b38ea3127e91ebca,0x34601ec91924764cc437,0x4b3a874419d3c3b27033,0x67d032cd26e38a4c2e53,0x68619a38fa1d52984849,0xd3d8321471cbf9611f7e,0x762921696811ee05e8d2,0x98df84ba308d753846ab],#[0xfb556c7a46768c2bc967,0x27e0ea0aa446538b5956,0x56a288354f1c2ba5aa93,0xf29c242d4999d183db8b,0x63327b94838379a269f1,0x8332c47c22a8e92f9578,0x70859bb01ce0cb52d39a,0x1a419871d33b5848446d,0xb3b5641ea5740d21e72,0xa575b8f079067ce45868,0xd40ac3d033e0bcabf0a1,0x8e1dd6aa416954e914cf,0x6bd02a1c2560533d5967,0xe8029a230ea0e8a9a35,0x53847d5afc929849c06f,0x2e99982e4d1df67d88d7,0x2fe4428e1226d1d2a8c9,0x9a7b8321378b1759b]]
def g63D8 := groupedPages #[groupPage3,groupPage4,groupPage5,groupPage6]
def g63H8 := limbs80 #[#[0x20d0100170c01021605,0x5020500001004010000,0x301202000300000630,0x1000b030103041503,0x9000630000303010002,0x12000015000000140303,0x1000200000500092c2e,0x30807011e060d1002,0xd0003380e0000001006,0x101080303051f0b0c,0x105161106000600,0xd140707030010090011,0x101000e01001c100000,0x161d0200180a0a020003,0x3190d39080100020504,0x501060a3800000e0404,0x11020000053016000d1b,0x3150000020b02090107,0x18070c00090529090501,0x74c020619090d082e01,0x9090002000702030601,0x503030801020100011f,0x15702230a341a3c0202,0xe001000060e09000901,0x7010a0109000c0a0507,0x2f080003001000330306,0x5390804310100010b,0xc0b1905010207200700,0x1f00000d10002c000104,0x2400002706024601141c,0x1205090001030708041a,0x20c00010809132d2326],#[0xd0f0003000186090701,0x14001c02010b550c0800,0x304c000108080804400b,0x30023330b0b01260423,0xd05050600082d0d0006,0xb292123000308160300,0x450700041a0e3300dc0a,0x300170019001000,0x1000009a700003300,0x90204002b263e2a3100,0x28051d020612100f3f97,0x4173707a20c03682100,0x1e0b1720053306133100,0x440313020110010f201b,0x145040f0b00160f000b,0x572500472c0117006200,0x41592e050d151c3e7400,0x113a013c02075711,0x3206160700001e00a225,0x780d044f0809380a1237,0xb302d1f0a0606490100,0x14090121290272040b15,0x3e15020512020c041100,0x230231045d05783a410b,0x43388642031a1c290512,0x1113d20227290c5a37a7,0xc021656030204091000,0x32010000030000b20b06,0x4040f060116050027a8,0x810042c7347007b3e719,0x12807800bfff7eff4000,0x1000002800a2314dd0c0],#[0x71096044003bedffff80,0xc0000000024a82026748,0xc44284b0240033eee7ff,0xfe400000000966048213,0x9f225c25812001f6e3d,0xbdfeb000400008886ec6,0x490d0214a12c09000fff,0xfffffed00000000c92a4,0xd04c4a860b709804800e,0xbf4fbfd7c0000028100,0x8b303d714546504d0240,0x4005ffaffffe00400001,0x40480619a3c36c2681,0x40a803fdf7ffff020800,0x1629381952c1d613,0x9c05801defdffff8000,0x10010010308800699902,0x8984e02c00fbafbedfc0,0xc00000040073184914fc,0x884a027817007fdffdfb,0xbfd0000000034401edba,0x954d27613c0c004fffff,0xfffbf8000004022d1543,0x21aac94d09e0600376f,0x7ffdfef8800201042808,0x8031b598ae84f03201b,0xdfffffffe0000000083,0x404d54c2ad85cc2781d0,0xe806effdff6f00020080,0x35a2b440d7531413c0,0x78036fffffff800000,0x710b02022bf99c0a],#[0x85003c01dbdff37fa000,0x204414429420162cd7,0x7042881f00feffdfbbc1,0xf0080400031810042b24,0x9a3a814411807ff7fbff,0xfff81810000000403005,0xb2d01ec0a409003fe7ef,0x7efffc408100008345a5,0xcae168d0305204e01fbf,0xf7efffbe0000000120a8,0xa4c003b5e85c2982900f,0x8bff3fdeb4004021435,0x14548161dba45214c148,0xb4047fffffdf80000020,0x29e8ac81ae22390a80,0x505a0237ffffff480000,0x8001107223cb7392705,0x2b02d013feff7ffe010,0x8aa0498abb498,0x4e215817809bfffffff4,0xf80001000643884a15e7,0xf92850ac0c004fbffeff,0xfffc0010000292643d36,0x237f14c85606202bffed,0xde7ffe08010000128710,0xac16aa02b032015f7,0x97fbe7ff400008001461,0x88880161357815c1980a,0x57feeffb9800000001b,0x9114b20f0d2cf0ae0d4,0x6a02bfffefffc0000000,0x10a0a90188d708570],#[0xb83501579fffffe06000,0x8cd000cc5cbd42,0x615c1b80a6effcfdf900,0xab90119063561,0xb1d0ae0e4053fb059f84,0xfc000000020861a0871e,0x91d9285707602b797bff,0xeffc00001000edc041e5,0x81ca0cdc2b83b015efff,0xe7ffff00000000082000,0x70c865e68c15c1e00aee,0x5defff5a2000000025a0,0x42db7373135e0ae0f005,0x2ffffffff4000000025,0x400a0459adb6858078,0x3c0173ffbefde0000100,0x12449103cf8dec2c0,0x601e80baefffdff51000,0xcf89a00e817221,0x50b20fc05fffffff9800,0x2088063020d4344ba,0x5db85907e02f6ff5c744,0x7e1008000068021727a5,0xd38f142d840017eff7ff,0x7bff00088000422b4c81,0x646a77ae16c2100bfff7,0xffffff880000002bc530,0x41083583eb0b810c0637,0x3bb7cd99c00000002287,0x7126041af1fe85d08603,0x19577be9da000000000,0xa5108905d8b0282e843],#[0x2180cfffbffff0000000,0x5a8020476cd830174,0xba10c067fffffff80000,0x83089036bc2d0,0x185d086033bf3fff7840,0x40013a00b315b862,0xf1602e8440197ec2bffe,0xbe02000040031214d6dc,0x6f38c81742280cfdfff7,0xfafa80040000038a7260,0x1337e4770be114067ff3,0xffdff7c0002000108238,0x13c1a4385f08c037a,0xbff71a69600004121417,0x20009c7e1d26c3004601,0x80da2e04bff000000000,0x2810423271695018024,0x12406befa7ffa0000000,0x1c081838f4b20c0,0x60092037ff5fff580020,0xd6bc9a610,0x643004a01e00000ffe00,0xee21a9ab903a3b68e553,0x53771e3fd857e1a6492,0x77441c2101f00c2f4433,0xd018780a954224328063,0x6282d1c2002568d25f4,0x3024e0ad2a1202388c3a,0x82ddcbaca9580153281,0xf91981fda021b05489ca,0x92e8d1a818304401d2d0,0x107f2b4a47b1fac2724c],#[0x154c05ceeebb072b208a,0xc6361418565696673061,0x6288f667a818fd8682bf,0x8f04a54131880a860086,0xb22082bab7a8e58f0a8,0xd1b9096811370e0aec2e,0xc107c7d6d88b1715d21c,0x780064a7cf82f0ab2735,0x5dc71fd979fe59d4a983,0x35a0fa85858df06bd60f,0x4fd050eb5a86d4e25a3a,0x5c270f1b09232f87bc8b,0xad83b30c06d2880740db,0xda03e72fbe5363390508,0xc656595cd389e25edaa7,0x5ae0c6f88544121c6765,0xd6426cf2d49272f961fb,0x57c9747c7f42318a30d2,0xde52160af019106c71fa,0x622d21992022e01e3313,0x8ff45a9ef7028e4d3b83,0xdfbc89071ba204babc4c,0xb2bdeb040e8b78921ce3,0xa95069bbae4f5b372dd7,0x4b43ab1807747e485960,0x21743de97f28257abb54,0x18d81417942943d957a6,0x60bfb434f63ff4b2af45,0xc269af218b27d7158271,0x2b2410a3e74420410d,0xcf00b5240483ca721b01,0x60baebe2037928f56011],#[0x3fcffa4ed777566b9592,0x3c0d0a686d98830a7228,0x92e000f2c0088c4272,0xe8a72978de080000a1b0,0x704190182ff0b1337668,0xd005a5e62bb47df27b20,0x122333341bd0bf11e00,0x5f8b0fc01180c38f2053,0xba1485c1f4243e586eac,0x89093a299a4dde0b3953,0xe021aec00985db4d4175,0x7a58d2c1fb2605746ead,0x55be3ddf29b09023fa8c,0xf3f0084e8003c500b071,0x8000b66fd43e25df5ec3,0x868d7d610fa045d4e7a9,0xbf6dedff0b7b6623ce2d,0x19a9f226b237c8a448c8,0x624e02f0d814014c1403,0x6010c018884436036008,0x28d121dd0000030316c4,0x8eb127379070363df63a,0x72461cee8a541b31d32f,0x801c0de84242156c4c30,0x3190b4050cad9434b,0x561134052a0e31c5512,0x851ce100b76ba2ba9b4a,0x2b2176cfd34d2aaf70c1,0x6188088e2004edc41a94,0x1cc31c00b6c00e686e15,0x800018003b3e7db3cbf9,0xd5e0d5771040c00010ad],#[0x39d561c8107a056e01c0,0x68f847f813680c2d90ce,0x24ee]]
private def groupPage7 := limbs80 #[#[0x104400c8310c02108010,0x4405414c521445010c42,0x88620841324c53048520,0xcc730c8720c42328c630,0xd4b51d4343d0b41d0332,0xefdfbf7efef6eebe7f53,0x6504d611826513fffbf7,0x640c46448a6228664002,0x6408d610ce61189620c6,0x620c66464e610c065406,0x639496228265802650ca,0x64091609126371163051,0x621e6103d262011602d2,0x43852626d26031262192,0x6471163222321526261b,0x630a5316d26269360450,0x639e04209160111631d1,0x605d1608116179064452,0x632a0425db401a120051,0x647d3637516031160351,0x63311618d262352646d0,0x638d2638e5313d2620d1,0x6331160690623d1633d1,0x61366313d063450644d2,0x60652646916115064751,0x63711610526449263552,0x32165611926465263951,0x624d2603536149161961,0x6455264951632e7314d0,0x60392632e731651610d2,0x601d260151639e232411,0x30612640516375262112],#[0x626506249063751600ab,0x602d2623d2600d264112,0x615116169864492605d2,0x633d1612126039b41853,0x42091607d163193633d0,0x636db42892642eb304a3,0x622d26319f30629300d1,0x64292636d06451262a12,0x60751608d16099264352,0x432506441b6449160151,0x60012644d2633906461b,0x60892608d2627d060512,0x62865311266119161811,0x4319064151609dd300d2,0x6205161312631e232718,0x62391613926021163652,0x6171161291619d264612,0x60812602526305262891,0x635926471263991601d2,0x62251638536051163611,0x61592620926309263592,0x63893637126459262291,0x64790645536345161911,0x64691606633269161552,0x60092641526011263750,0x632a1327126499263212,0x61852607d163012649d2,0x633d2625516021260691,0x61a1160a126299262792,0x63992630116161161191,0x635d26311263893604d1,0x63412648184389160251],#[0x647926475e3049064493,0x63393635526215264310,0x6371063412630d0643d1,0x60a126291163552647d0,0x61252643d264a12645d2,0x43512635d26075361411,0x535af3106f217af528af,0x424ae6372c643ee326ef,0x323ec439ef306ef527ac,0x6076e607ef4106c5386e,0x5372c3266f303ef534ee,0x324ed3042c5162f531af,0x5366c436ec306ec4366d,0x217ad3266c3196f3006f,0x5392c624ae6356e304ac,0x217ac4376c433ef5042c,0x5442c210ed6306c535ae,0x4306e6092f5186f5062c,0x6372f4042e627ac326ec,0x4062c5462f536ec430ad,0x5376c435ed326ee327ef,0x2056c5366f429ae6456f,0x624ec3172f4342f5382d,0x5306e328af439ad323ec,0x417af515ac531ac604ef,0x4362c5256f4262e6022f,0x535ec5086c4266f530af,0x623ef5172d6026f3002f,0x5186e327ae6386e647ec,0x321ee320ed6292d3142c,0x524ef404ac4302c536ee,0x627ee3072f432ac436ac],#[0x6322e6462c426ed3162d,0x5266d6106f5086d6126e,0x432ec511af537ec5172c,0x424af538ad3056e617af,0x328ac535ef5262d327ef,0x627ad6376d305ac5072d,0x606af536ad312af4296d,0x312ad631af5056f4396e,0x537ae3162c526ef2162e,0x327af505af329ae306ef,0x4056d203ed314ac5456d,0x530ed617ad6022f5106f,0x303ef405af3262c545af,0x501af5072d3196f5326e,0x606ad3072f212ac4352f,0x4356e646ac2162e3196d,0x6192e631af624ac5472f,0x506ef4256d3186c544ee,0x5466f435af4072e6286c,0x633ee2162c5106e3186c,0x3142d6162f214ac633ef,0x4372e3212f424ec4202f,0x2056f5286e657ef2196f,0x506ef324ad303ef434ef,0x6556c427af4142c527ef,0x6172d315af4366f3162e,0x212ae315af4266c5476d,0x406ef4162d6262e329ac,0x5006c546ef5256d6386f,0x654ef439ef2186c4072f,0x517af3296f403ee6586c,0x312af3042f624ee3262f],#[0x426ec5406c527ae311af,0x4006e2196d6226d3172f,0x6126f4376e3172f3062f,0x4162c520ec540ad607ee,0x524ee6162c2186d6322c,0x4342e6472d616ad6192f,0x545ee2186f5312c439ac,0x314ae322ae6172c517ac,0x433ee206ee6016f436ef,0x3256c507af5266d6076f,0x423ef412af3196f414af,0x644af206ee322ed6186f,0x5342c432ec406ef430ac,0x3262c510ec2196e6562f,0x6262f3186f435ed6256c,0x203ed3106d6286f304ae,0x547ef5362f4196c432ae,0x3296f324ef526ef3266c,0x4362f507ad300ef203ee,0x6306f4002c546ae6256c,0x547ae6186f500ec211ae,0x3286f315ae627ec434ac,0x5342e657ac4396e6376e,0x437ef400ef326ef407ac,0x3256f604ef415ac540ef,0x206ed6092f3172c324ae,0x4302f3056f437af323ec,0x305ad6356f4172c203ef,0x5362f623ee616ad324af,0x4262f2002f430ec3162c,0x527ec5212c3286e324ec,0x4356f5142f3072e6526f],#[0x317ac407ae6292c435ac,0x6016d2162e6106f5386d,0x3072c4172e3042d3286d,0x4316c4372f5162e317ac,0x5262f538ee310ec434ef,0x6226f5392e6026f5356c,0x614a71056d3256e647ae,0x520ef521ee621ac314af,0x328ae6476d614ac5042f,0x321ac324ed212af3202f,0x614ad214ac4296f210ec,0x650ec5412d321ae6122c,0x2196c3186f321ec303ee,0x300ec5356c538ec524ad,0x2186c4105363052609df,0x644ec54452608af4212d,0x315ae210ec4256f4312c,0x323ec534e6610ec5372c,0x620ec514ac504ac5286c,0x5452d620ee6416f533e2,0x611ac424ec311af4346c,0x650d9640ee32010604ee,0x6092d624af4332f410d6,0x4042c5376f5049063552,0x650ef511af5212d211ac,0x417ac521af422e320595,0x422ac533d06406c544ac,0x410ee3142e640ec515af,0x530aa300ef514ac328ac,0x3106c5306c3202c423ec,0x434906256f5302d206ec,0x321d2609ae6406d3202f],#[0x523ec404926386c653ec,0x320ee314af531e51002c,0x538ae624926296d321ed,0x427ef322ee620e32006c,0x503ef524ac536ac5302c,0x322af531566506d621ac,0x5352c531ed306ee614af,0x2002f503ec528ad3006f,0x6116c214ac420ed610ed,0x543ee214ad217ac5202d,0x3042d210ed311ac5482c,0x6592c654ac4142f510ec,0x3286f521ae654ac5352e,0x640ed3212f5322f4382f,0x4346f211ac521ef43050,0x212ac4332f5346c329ac,0x412ae324ac403ed3002e,0x3106f5002f321ad329ac,0x322ec414926402d3262e,0x211ac5322e610d2605ac,0x6506c4196c322af427ee,0x5346d322ec5402f523d5,0x6306e6116d611ac4212c,0x3142f311af427af43690,0x620ec429ad322af534ac,0x651af420ef4202c32961,0x3296c541506046c415ae,0x310ec422ee3266e321ad,0x3129a640ef52025610ed,0x640ec422ae644ac3256c,0x514126062d6122c53492,0x1ef02bd038b02d80002c],#[0xd2584421c7338c40142e,0x439e3337e66690ba394f,0xb211517a7f64afe8b710,0x4705cd8259e331645e00,0x41c3f28348fd05e6c3a7,0x4a6a81ccdd796b323d63,0x20a812002cbb5739a9f7,0x3388ce2d8a222c781804,0x70b4120015a50d284510,0x556132440f2340aa1f45,0xa0f419001fd75dbe64d7,0xd465023b8cb2c09f1f05,0x811425001cf6bd8b5953,0x55b54a480fd35cb422c6,0xb1001a002167cdd36bd9,0x456532430f233cb12506,0x11c21002247f9d86ad8,0x557533444ef354ab2146,0xf1181c0020b795c46ad8,0x851d2d43cf4364b02246,0xf0e413001ff76dbb6296,0x756946494fe35cb22285,0x20f81d001ff769b26517,0xf59941460ee32cae21c6,0x415c270020e7adc46a98,0xd5d95d4d9103b0c82b88,0x611020002217f1e06f99,0x55a546490fc35cb02306,0x81482a0022b809d96c99,0x65c14e4c50a3b0c527c7,0xd14c260022e815e56f99,0x15dd50494fe388bb28c7],#[0x6100140022c825f0721a,0x55893f460fc35cb32486,0xd12c25002197b9d16ad8,0x95c1494b10437cb82386,0xd130270022b82de07119,0xa5d54a48d01370be25c6,0x21782a0022c81dea6fd9,0x66857a559233c4d22b48,0x111c240027a9662d7d9d,0x26215d4dd153a0be24c7,0x90e412002588ae0676db,0x55351e418e62fc961bc4,0x1120240020e775bc6717,0x45f5554b90136cb422c6,0x516428002297f9df715a,0xf6456b53d2b418cc2b48,0x91042a002578ba0575db,0x25c94e4a8ff34cab2186,0x61382a0023c839e37099,0x165d6f50d1a3acc92a87,0xd1382f00240875f8759b,0x95f5554bd03350ab2106,0x21282300220815e971da,0x58139460e32f4a11fc6,0x816029002037a1c66a18,0x35e1594bd0837cba2807,0x21642700224821e070da,0x75f1634cd093acc224c7,0x9118290023d86df9745a,0x95ed4e464f8354ad22c6,0xd1182a0024a861ec735a,0x5639614dd0a38cb62486],#[0x610820002468aa02785b,0xd5ed554dd163bcb82206,0x113c2300234835e87199,0x67579519283f4ce2707,0x2168300026e92a257d5c,0x868d7452933414d02b88,0x1382b002538a20d7c1c,0x25c14b494ff348ac2587,0xf16c2b0022c81ddf6d99,0x61d66501143b4c22787,0xf124260024e881f7755b,0x65f9564b50b378b12206,0x51442b0022f831e7715a,0xa5d1534acf937cbc2547,0xe110240024986dea6f99,0xc58d47470f6358b82446,0x1098120023a849f06ed8,0x258930414de2eca41bc4,0xb14c2c0020f789c36998,0x65c5564dd103b4ca2607,0xd138240021e809d56f19,0x5cd4d4bd0939cb42487,0x8142418222a82dea719a,0xd10a3041c13020c840c0,0xac65086c4e083081010,0x86878b40470021205060,0xa1515211c2c408c4888b,0x12c7c622230745a1d302,0x81094362c56189d18905,0xeb0245b81e251f524437,0x5a7804b8710f7529137,0x2064466f4051d72446ec],#[0x49bf59111b7014a6463f,0x8f1a2453b810fc043ce0,0x5fb844005679cf020115,0xefc10022b7d7f7f0e007,0xa2ff128279da91b11e,0xcf4098e73497a293e1f2,0x3e73e2000567be10139c,0x11416e2e78054792826,0xec3b84a8a88ee64a7c3e,0xc00537ce88414d85f109,0x206297e132129406b933,0xc000a956ea206404ddbc,0xfc30832fd2d1000b2bb9,0xbe752828be750002a7ed,0x28f6dc5cf2291ce2a246,0xf8800b7eff18017b2368,0xd70c2293f7f0204153ff,0x51b1c388f6fe8190155c,0x477c8c80a6f7f080002c,0xd0151fd80127ce5e3045,0xbf20514df2a10149cd25,0xb7f90822e164f0604b2c,0x87d778c000b2fdc20082,0x143fd18028be7422045,0xd7e02677ff100197365,0x69e6685822b7eefc3403,0xaffbfe08030ebf608401,0x7eef834034caf0794025,0xfaef14000b6bf610022b,0x7a2f648a946c6388c7ff,0xc2d77fd304197b5426b,0x422fafb30002b3eff87],#[0x39e0488a4b37264287f9,0xfd284420b1fbaf79820d,0x537e0c257effc30032,0xf510273ebf2810a6ef89,0xb38f2e5800b17f34420f,0x98863fd900f777e08102,0xec223fdedc740317bdf4,0x18319e6004efc368217e,0x503e34118ecce4450ff6,0x6667904e79ef9850002d,0x667fe4100551cd990055,0xf93042cfbbe1c10dc328,0xe610151e5bd4d922b7ef,0xff0400d3ba817015df19,0xffc6102d7bff48086bfe,0xbedd845ddda0a3030051,0x154f481e5224acaaf88a,0x3808abf42c046bfe1001,0xdeff120143ff86102f79,0x51e72d4022bbdfe20114,0xcc006b7e7bc20a7f8640,0x810a0fdfc081054fddfb,0xd00a3dff0204155f3fa,0x283ce5a81057db46323f,0x2aad78cca011716cdcf8,0x1ecff3bcf0871f5f8c20,0xffc80002b7e7dbf0e407,0x47b3f9020297f98020c,0x3c8a9fbff4c00bdf8022,0xfcec0811efc184b6f419,0x273e1f020a27888808cb,0x7d204da32cd1c483afa0],#[0x1456dc580159f8508144,0x50153f6fe1801a7c3e04,0x9680a4fafc190155ddc2,0xee00149e728500959f5f,0x77814082d77fd580175b,0xb7fd7d1201a7bea02739,0xe3efa000577cee14202,0x159fbbe2000577c0a50a,0x187fe40001553ef42c4,0x432bf610082b7ffef10,0xf6c0061ef8404ef9fbe6,0x9666720142fc360297f7,0x5defb880015bf7fc9801,0x28a8f8f3049cfbda8001,0xaeffccfc285151f7de10,0xafdfe771e00d8cf98808,0xafdff060069ff6ee3841,0xbea287efff104177ba84,0x4c0240163febf0700c8a,0x702080577e481608aefe,0x791000adf7f70e2061fe,0x25f7f5600597c4098f7,0xfede2c01a11014dfbff0,0xfdfc4006bdfdc38c16fd,0x3e1e400297f78e304bdf,0x54bfd841073e05082a,0x601153f7f8c10abdfc0a,0xfe0c10c7bff87102eb7c,0xf8d3c601163fc2202dfb,0xecfc224054ffffe0082c,0x24ffc822287effc3802,0x4575ca7bec4953ffc71],#[0x402577fc20022abf84a8,0x385400ae4ee748a1f7a1,0x665800b0bcf42810597e,0x85df060458bfd80127ec,0xa5f3a11082c29e50a29b,0x50fefe5c00b5fdfd3001,0xe3fffdc58032e4cf10,0xf380187338513af7fe90,0xdccc022a9de19511d7ed,0xf85080aae9e740c2159c,0xfb801002c2ef2a041599,0x55bc1048c487fa64049d,0xebfeb70f80a6ddcb4dda,0xb6671328b3bf2da1c602,0x9ce4b6949fd6e60302b3,0xff5181660176f84b1450,0xce3c0c3feda12030e5a1,0xca030172c7401384855b,0x85e12f585e4246bfff55,0x2ef990b830249e9a5ec0,0x816fd51de560d087888b,0x902cde681128ebb79f2,0xe302c810d7311cedc43,0x28856f87d0d9f0713d21,0xaee2bbee0ca4a0ccf91f,0x32e577de4d5300acbd55,0xc72bdeab2c04a499c285,0x7c2c33cab7b945ba184d,0x2cd235f0b808a7e4aa00,0x7bc4652b285bf2224a12,0xc8a4c126f249d001593b,0x77a0851aed1023e15ce3],#[0x567e45204598ba377094,0x460c3e5b0e535e680aee,0x24a85ba5481c47585e42,0x8f7fd5728b8accf7a70,0xbe84d7b52e62533c2a55,0x614cb02b158f12c31262,0xe0c7b02937cc0ddc5377,0x92f081493fa8730b0acf,0x428670aef1fcaa64a6df,0x728ad62192fe417a4f59,0x1dcb6ff1e42871558a60,0x4cb6f4d0e600aca6940a,0x48e4298d0255ccf8ea45,0xbe79942235d57303016,0xbe2197293fd4cf042fd2,0xa5065c9c4d7e59e2a514,0x886fd910ae11693fcec0,0x23155cfb70a92058a14e,0x68547fc823322a3ecfb1,0xf43bfbaad664a8b3a98,0x90e3c3931aec330e154f,0x57a3e01b44925eb93c02,0xdf8816730917fa43e954,0x469e152a847a4d627929,0x473ec0da1c602e0b03dc,0x42bbf89744a85935206c,0xaefc653038a8f9e28793,0x4935e1f3a0cbcef15960,0xef660010b04c1ae9c120,0x8571f161814c835cc469,0x67fa2d9a02bbe69cbc8c,0x31d60074917f74644dc5],#[0xcc4709c7ecc14c48fe4a,0x6282a3ef8a2d292040b3,0xd00a61c2c1f00e891d66,0x4b3f46411979745231f3,0x2f3c150fe42409483648,0x1615dcfb5854c02d33a5,0xe547df22ce145f761e2,0x64e53bed3e90566f1983,0x5e1a0c93c0a04a3dc466,0xda9488889c9472ead84f,0x1ba64b4be2184ca8ce0b,0x9045276179c9d7b6688d,0x1e2f80ba86822cf2b11f,0x259e29503c62a31c1ff0,0xa6561815d030be141fe8,0x13acc65128f2be08a2de,0x16cc42b1911ab91cbad6,0x33a46bee2190b545d7e5,0xec8fe25dc3c032949d89,0xa6e60c7bf070f8554a11,0xc7c0f80ce1547ba3b292,0x235e2190c302c53437a8,0xc8b232b5ed932345033c,0x1e7c10c84795139453a1,0xff9b8024a85b3fda1d89,0x720596ec5c7288dd3135,0x24d3ff8042747a7e6e04,0x2d8587f400598965f764,0xcd112447e8885fdf302,0xff805de422d84858bc2e,0xa0aee523cb52323bf61d,0xa8104c4b07c0f72a23dd]]
private def groupPage8 := limbs80 #[#[0x940c56a3447a439493df,0x9602461e01528f4876f4,0x796a8a6f1cb50150f9a0,0x2f02b83fe0ac03d0185a,0x9497b2da44d45c7d9ee0,0x30b0ac752df231b84d4c,0x468ff7ec024a4b0fc287,0x628bbcc1a2302481c649,0x4928448dc2e011291383,0x19f1c7c1cab69c281f3c,0xd30a60955b39561ca9fe,0x44f02b277ba03f4a9635,0x3ac2bdd68c54c917fd46,0x6e2a52b1c88c463f8654,0x18657568a1c0b2c879fb,0x2f32918183651c639791,0xf883c0ac95332c29a4e0,0x567c6dcba02f20c03cfc,0xde4d6f4cf827b7465664,0xde5128f5f19577155f14,0xe1eb71288f3185871588,0x775a31532419dc8fb0a0,0x13615de32f412952b711,0xc12056792976145264f3,0xbaf8d395c8a42e8ff8e,0xbcce02678557b03a80cb,0x7dcda5850b0b84762446,0x2d03eae048e778db0e51,0xf0712f05967e79da1a24,0xb063dca2a1985ce521fe,0x7d32068e577faccb09cf,0x57308244fb0a2908927e],#[0xeacc93cfc85c14024aea,0x7c0b2fb9a5b044a8617e,0x1e2789541b8443ce1751,0xe2c293c9ff889c0567d2,0x1bb84ebc2e6ac890776d,0x63ded81cd0573d09d128,0x4a0ce60530e15e9e4184,0x1d6155f1c6ee4f1bd89e,0x877c4c099491fa487c42,0xba4c1948acfe49523585,0x4575bac38ab7fc8b6847,0xe5701e2124cd7cb3a09,0x94a0da1101dcb0ec2b4c,0x1f1bf6442b80181e17cb,0x8c5187092af332133615,0x114cd911cef5dea8a678,0xb3fb32824c574de78585,0x4fb1101862507d611d82,0xae67e8a08c775758715,0x7285a0bb6ba393b75e24,0x96163f1667af43037c5c,0x47fa7238474587e18601,0xa0e48fe11457c905325,0xa60d8917b3025bff88e4,0x287165bfdb6d014b17c6,0xd934aa0ce51847bd665c,0x6f0959b6021971650cd9,0xb42bb8a4370c3939d611,0xfa579b8e507d6e06728b,0xc4a81816d7f30c8060a2,0xfa073a0c83e530b0aafa,0x4df320b2c2abcd0e5277],#[0xc1c4b2353c9809cd949,0x849c30ecb61ca978f409,0x1e741867894f614dbb3b,0x871a59bdf4038c0927b6,0x63b3c07a92a0b8fdecb6,0x617c28267ecd828af11,0x18c8f60aa93b7bc462ba,0xd14092bc46b73c27a052,0x3e12a38ccb9c8a77bb13,0x1f1229507f15139a5f94,0x152971f910c032c2dbfc,0x38aa9e70f227bb99e769,0xd8467d6e16a8acef5bac,0x970c38b09b94932aca1d,0x84b4e4efe80ae12e2778,0xf31d8b949fd6a0728364,0x1e11545cbfe04518120c,0x5cf5f059c1996145f34e,0x81595cd8727af774930e,0x1afe47c4042d3fe9e20d,0x7503c62a39f3c07f7115,0x17451be115715d972120,0x898718228f7bf3d4112a,0x11a7730998249fc13322,0xe1552847153e88a37895,0x2a8d9d131b0ef380523,0x5a88c4d4e04e7f9f8039,0xdc8213491fe9f3c0a9ca,0xcdd8497f5900024cb675,0xcf7ec082682e5667af02,0x3def827f0513e52aca35,0x88169d981e7851593659],#[0xe0a4da82e1d2bb9a5e2c,0xb5782349157311ef0713,0x1bb0916]]
def g63D9 := groupedPages #[groupPage7,groupPage8]
private def groupPage9 := limbs80 #[#[0xf0603030000002c0a01,0xa0104040601010212,0x5011200000200040300,0x12091501050301000001,0x405020002010c030013,0x4040108000207,0xe071f020b00030902,0x2041a05010200060100,0x2012302060001020016,0x6111506050200020503,0x1909030f0105000e00,0xf0901000002000b0000,0x4000000010206080403,0xf0800031603000d0600,0x10000000000a01000600,0x1050004090100000902,0x8040803010203001312,0x1010101020109000601,0x5150502000904010600,0x202030a000205090100,0x3060100000209060106,0x60000000205000b01,0x1f0108140e0101020102,0x1a04020000170517,0x10202000202030002,0x2050605050b14000501,0x17000101000105010204,0x104040102010b0c0c00,0xb0a0029031c00060200,0xb05120e060000020c02,0x1400310120001160500,0x1f07060c000000000a0b],#[0x3301050a000000030400,0xb0d04060528010411,0x570509010002000c0300,0x8030b000f0110000500,0x1100200041501490408,0xc020003060202040000,0x1060702060002000200,0x7050004000808000002,0x40a0109010007000b01,0x1041004070001200205,0x2f030103000300012201,0x50f041f010000000102,0x3010002051a03000b04,0x500032d00000b02000a,0x111b0c04000b0f1e0300,0xb000702080003020103,0x310d0101230303000002,0x4000301001045030002,0x1002603090103000100,0x201090203040202090b,0x13020600000000080400,0x20301090003010a1317,0x3141902010205080502,0x70b010f00000c170a00,0xf0a0a0d0001050401,0x1b06021e0901010301,0x80320080b00000003,0x180711040e0d230002,0x1e011b15061616160106,0x17040700021000150000,0xc0018002c4900040503,0xb041e2e1b050a0a000d],#[0x2e150204020500070832,0x70036040b02050d0101,0x3040d001103020a0802,0x70b0005050910001f03,0x808000302221001181b,0x1020000120531000300,0x30017041e0111200403,0x15200405000d00001402,0x204000006001d0003,0x8000007170309320616,0x80000100410000f2100,0x6220702010103670f,0x8420205020600450000,0x12905010b0300031601,0xa17000800080a090000,0x20204040d01071c0100,0x23f0006000300090b00,0x4031306070101040a0a,0x10c240601211e1b,0x1902081700021008002e,0x1030e2b000e03080e01,0x50107001634002b0c07,0x70f0809001305020103,0x8370005200503031d,0x25030406000e04060501,0x1407110b010e2e0408,0x1120e24000600090113,0x60a030100003e020001,0x1525000400020d2a2808,0x60200071c000a0000,0x806180900020b2c1d,0x50a021f00050e0a06],#[0xe0622180b0202450304,0x4040722000013001603,0x41eb42b000b050f1504,0x5180608060405013e,0x2050800243a0f081000,0x1c160a01001504140201,0xa1d1a05041b05110114,0x91b040003010f350001,0x73e0481070a280f0207,0x380301070b340f050600,0x1607120d0003131000,0x41b074f020f18220d04,0x272501002a0601000024,0x808010220124f0b0204,0x144803c06282c000210,0x77ff79f7fffebf7f00,0xe11045a34f31e1a80100,0x4ffc0f77dff5ee6f9009,0x8047135231e1a9015000,0xbbe77efbbfebfe00040c,0x48335531e1af016000fb,0x5667fff7daaf0888acc8,0xb35631e1b2016000b76f,0xb7effffffe1402004949,0x5931e1b8018001fbf8bd,0x7ffff7fba08408004ad3,0x31e1bc01c001df7bfffb,0xeedfef0a1108124c335b,0xe1bf01c001b9fbd2bcb3,0xaffb040880044dd35d31,0xc202100156e22f9d52ea,0xf6008900204ee36131e1],#[0x24001b5d66dd6b55f6d,0x200860004fe36331e1c4,0x400181a39abea18bdebe,0x400051136431e1c702,0x29ea7efafb9afafae26,0x24252036431f1ca0250,0x3ffdf555ffffff170002,0x805333673201cb027002,0x3ff64f2c7fdedf084020,0x5493683201ce02a00224,0x789be91438ef43004030,0xb3693201d102c002aa14,0x4a9f3c97ba8114009055,0x6c3201d402e0021e2897,0xbdfeafaed00401445673,0x3211da02f0026d3aaee2,0xa36ff71481010157436c,0x11df032002da226e86ce,0xfdcf500c010058436e32,0xe4035002fc93eccdae9f,0x4f1081288059236f3211,0x38002ca7bd0c7defef9,0x9080005a43713211e7,0xc0025b40ffd96fd17fff,0xad002a5b43733211eb03,0x2ff40cbe5ffedebc700,0x6005c53743221ed0420,0xbd1bf3bbbf6bfdfb0210,0x205d73753221f3043003,0xecd9f8dbdfffcea12026,0x5eb3773221f50470032e,0x7f3bdf3fdfff00c0a0c0],#[0x937a3241fa04e003d7f7,0xa95fdbe7e9a00012405f,0x7d3241fd0510033fdbbd,0xb05ffb976000420860f3,0x3251ff053004d05fb99e,0xfd0bff8041108062237f,0x5202054004429c1978c2,0xfe630004400063338132,0x6059004fd67ae63ff7b,0x9d0002006363f3823252,0x5d0049cedffee9cefff,0x20020070653383325207,0xe004ffbdfaabdffffedf,0xa1604766838632520905,0x4f36fbea8ffdedffc0c,0x7867f38832520c0610,0x58fdfba75f6fffdf0010,0x469138b325212064006,0xb35b2badd3efaf002034,0x6a438d3262150690068d,0x2d9eb4dc0dac40002012,0x438f32621806d006fcd8,0xefefffdf7f180020806b,0x9332721806f006f7bffd,0xbec7ce91002031616c23,0x327219072006bde4ff74,0x5edebfb00084206db396,0x921a076006904e5a1b20,0xd1a300e001806e939c32,0x1e079006715fd043f1bf,0xf801a001006f539e3292,0x7b006bd5bffb8fcfffe],#[0x3080070339f32a222,0xe006503f10ec58fc1dfc,0x80027183a132a22407,0x64fef3a571feffa5550,0x8007243a332a2250840,0xe4136f31667167358062,0x7373a532a227085006,0x1d5438dffd767e608002,0x7443a832a229087006bf,0xdb3cf7ffdbf908280004,0x43a932a22c08d0066ed7,0x66fffbf75d050609a175,0xab32a22e093006f835fe,0xfeffefff010019007673,0x32b233099007bfbdb4fe,0xbbefff100020007773ae,0xb23509f00751bbd7bbe1,0xc9cf0002050078d3b032,0x360a40073170accbb1f2,0xef008100057a03b132c2,0xa8007212bb7fa6dbaf7,0x286c00807ad3b232d238,0xd007d611ed3efffffdfe,0x28047bd3b332e23b0a,0x7feebfe6a7eebd77f80,0x7cf3b332e2420b20,0x9bff63d3bef563db250a,0x7e43b632e2430b5007,0xfb2db7bfbb8fff2040a2,0x7f73b932e2450b60079e,0x636cc971665d20280101,0xb3bb32e2480b9007f859],#[0x9e7fff7b9f1900900080,0xbe33024a0bc00766fbeb,0xbeaabff7008004088173,0x33024e0be007a62e9bff,0xff9da20220000082c3bf,0x12500c10073d5f95a2bf,0xdba90000200083f3c033,0x520c4007dcfcfb2adefd,0x28480000038513c03312,0xc8007bef1d32bf7f1d3,0x100020cc8643c1332252,0x9007102c2f16002c8ffb,0x400018753c43322530c,0x7d2f3e390dffff79108,0x80087e3c73322560cc0,0x92d0b41496b9bc150441,0x5088f3c73322590d1007,0x835fc0fbe3ff91060000,0x89a3c833225c0d4007f5,0x5bf6605053d00800080,0x93ca33225e0da007648c,0xf7f75fff7f80e080888a,0xcc33425e0dc0075fb77f,0x196e7fff001020008b43,0x3352620de007197e5fef,0x31cf9c80000a008ca3cf,0x52630df007fb31859c7b,0xc5ef1600480f8df3d033,0x650e0007fbdf0de0edff,0xbf81805a408ef3d13352,0xe200788b1f5ff69712f,0x110000229003d433526b],#[0x5007e2faad9ffffa8fbd,0x44a90e3d933626e0e,0x72f78db3c2ff8df5700,0x9213da3372710e80,0xdbf7ffb5fbf7ffb50000,0x429323db3382740ea007,0x6aa087ff5ff8dd40b558,0x94c3db3382740eb007bd,0xffeeffdffffe10200000,0xa3dd33827c0ee008ebed,0xa8ef7ffbfe1082044695,0xde33827d0f20087be9bf,0xfee67faf142002509733,0x3382810f8008eac669f9,0x4afff5400010009853e1,0x82850fc008be0ae7b53e,0x7ffd281020809963e333,0x860ff009069b4f6dfeeb,0xb2010084409a83e33392,0x106009ff3e2bf0fefeef,0x1018429b83e433928a,0xa009f37d6fbdfb6df7ff,0x200049cb3e633928c10,0x9dbbdb10fefffb56b14,0x9029e13e833928f10c0,0x2d497ffdac6a76ff8103,0x89f33ea339291111009,0x9663670f9e37ff400040,0xa043ee3392941120094c,0x75367b7fffbf94818889,0x23f0339295119009e79c,0xfffffaff7f40150000a1],#[0xf333929c11e0099fadff,0x77e7bfcf10086012a223,0x33a29e12100966ef9dec,0xff7ffd00008c00a3a3f5,0xb2a112400beffff2abdf,0xe12dc30a2288a4d3f633,0xa312900beed4c3a52dde,0xbea4431008a633f733d2,0x12900bc104ef366547ff,0x27062390a703fc33d2a8,0xa00baa3a98678d9debb7,0x681002a7e3fd33d2af12,0xbea37febffbdf6efd04,0x9022a884003402b712d0,0xab7f73102fbfeff38080,0x4a9c4033412b913100c,0x974754ed7ffbdb00a800,0xaab4053422bd13700cad,0xd1fbfbd7e1ed304a1016,0x94073432bf14100ccf9d,0x6fbdfbffff46000000ab,0xb3442c414200cfafa7f,0xf2976ffd0e014201aca4,0x3442c514700cfd9605fc,0x9f7eff0ae00104ae140d,0x52ca14900ce77f17f8ed,0x41af0168a046af140f34,0xcd14e00cfe4ce169fea4,0x9b00081004b034133452,0x15000df6f7ca1ebffffe,0x5082118cb104183452d0,0x600dccc9fc7fbe5feef3],#[0x644001b234193462d215,0xe879b097f67ff697ee0,0x143b3341e3462d515b0,0x27cf21ef7b9f24ac0440,0x20b434203462db15c00e,0xff97ea3ffbb7de020420,0xb504263462db16100e3d,0x473fff1213160042442,0x54283462dd16300e9ff5,0x8c190675a20800050b6,0x2c3462e016400e291165,0xabf6b437c3000280b734,0x3482e316800e689692b7,0x6f9f3700000081b7a42d,0x82e616c00e316797a631,0xfc5800818200b8743034,0xe716f00efe365a58ffb7,0xff82248000b974313482,0x17200e6dd3db7fffff5b,0x10209800ba84323482ea,0x500ebe98b347aeb82bc7,0x100bbe4333482ee17,0xeb81f3ebf9c1f7fff02,0x80bcd4363482f01760,0x4fbc85a1ff9f852b0021,0x14be14363492f117900f,0xe9fefafffedee6000320,0xbef4383492f217f00f7f,0xdf9366c69f9111614002,0x443b34a2f418200f67a7,0xc8dd3d9ed800a00010c0,0x4034a2f5182010ddcd9e],#[0x7dbfabff11824420c144,0x34b2f71830106c3ce7df,0xbffff8a4008200c25441,0xb2fc18501054bd7df8f0,0x67ce22034031c3844334,0x186010c95f04ffefdc,0xfe08609008c4b44434b3,0x18b010fdd786f2f7bf1e,0xc8801040c5944934b303,0xf0103736edbfffbfffff,0x12c6b44c34b30618,0x10279a4f247fba4f3718,0x4102c8144c34b30c1920,0xf37bfdf7dbe3befd2808,0xc0c9044c34b310195010,0xda5ccb5edadd1b210081,0xca445134c3111980107f,0xc1f75c54c1d740400020,0x545534c3131990100c04,0xe07ef7fff509000004cb,0x5634c31519b010759ffd,0xffdef75b24224084cc14,0x34d3171a1010dbfd3e9d,0xffffff01080080cd4457,0xf31b1a501000f7de6f01,0xb80d08a45acce645a34,0x8f1c9a7dda8bf222d9e1,0x1260582ace1e3cc20900,0x9b421fc24af9040d715f,0x31793c7f7a97d0bb80f8,0x62b1d6e7d3627e8c19d4,0xa8a5ae2f2c255cfeaf86],#[0x8bbfba385225376598f7,0x3cea80a8181fb00d2426,0xc7040c60620e183b82f,0xc7604bd8108bc1800068,0xa1bff8a6020c258a040,0x6a855f4088cda1000542,0x3314303b828bdda080cc,0x39f3c78ff9bb601f443d,0x240116298c3bf005c,0xd00610008b6001f533c,0x64c0e0617f2a64101e0c,0xe30773288548e0640203,0x57e5712c5546c5ca0018,0x457b07d084200381d88,0xb65798a049282eab84f4,0xa020e14e2dc00578035a,0x3a2f03d8c5f8c0c48,0x92001fe405180f9fdeb0,0xce19ea0ae8f0cf2c8e06,0xcbb822a1181b9c1f5401,0x6aade2f339650161fea8,0x466de81459ea8601b419,0x6e193dbcc3958605fc20,0xdd083540460f3b526f48,0xf41211bcf4000140382,0x2fd800186a3ac4004c,0x7f1366191026b1ed1013,0xde8059c17f322b3069,0x947a142508fb9050c045,0x568908ca0fb0a06f50ba,0xdb6acd6812e0eb829c29,0xc090876816e920f157f],#[0x85876980024b761682,0xe43740030145821ef8,0xc6b2edf94aae7ed9c1c,0xe235758fb081e9e16ea1,0x6003cfb5203239d280ab,0x802e23c000181598485d,0xbb00633112f6c3003e4,0xc0b49adbe7194746c800,0xf37a003f40129a40d1bc,0x5e360018204214760084,0x32014184106ac2bf0876,0x7b88db815010803a028a,0x87c6b922c70700f0b808,0x93c5472508103f916346,0x4ebbb41136ce7ebb202f,0x4d7d08c84e0841766e86,0xa4f24f0c6e6216a4a1b3,0xf5a3e7003003401d5e0,0xc1f0037380282f0bc61c,0xc7636e290bb1b782cb99,0x4657d62d007ab428058a,0x431a221f67c60e0d23b0,0x3e143a14185c50c08e3b,0x4e2c22811519ac220f80,0xe3d11d28e82421886f36,0x4171e020f80840ed806,0x64950adc3ec056a008da,0x406b0e929a4c1f976623,0xc543002042c788600ad0,0x61442454d0ef45d4032,0x4819900058c378fe0340,0x48d4d0047c0017008e10],#[0xcc0a08a1c26aa62e99d,0x2cb176c0500700100000,0xc0004143f03cfec5a10d,0x7002a06198718c06439d,0x848ef36e802500627b9c,0xd0e000c2000085831395,0x78820b072f8543a41a80,0x13eba465b447e41b8a38,0xd7e01a40001c02056d38,0x867ee94e340120019c02,0xd06aa305122b680b408e,0x445b0000b41492e7579,0xb628a20c8fe0dc541b02,0xb820e91a30250c0efe1b,0xce22c1c00088b93c0a00,0x4a0553ec39c431911bac,0x56702de3c438fc6800c8,0xd7c5c587f3f03c85f688,0xc758f174b6a3f040da33,0x5f0a8c715fac14a3eed,0x62d310465e9b00c581e8,0x7081b71830140c00fcb2,0x4059c896c82b0879cdf1,0xdde181187a89273f2028,0x7647e269725a8a857382,0x41018316873c60e01607,0x6500856bafc9de678d90,0x4f4e238d420e88101235,0x10062fc06b6012903f1a,0x2346a913facde2c27083,0x97331ddc6165b1786dce,0x8bfb30e070de8fd747f1],#[0x1a01fa4f1481e70e0c8b,0x8a0296b8a15ea8647618,0x19825bc068e89a000e62,0x440400936dfbaec0fbe8,0x1360497a2aead030ee01,0xfac6d808fb4ea30bc023,0x94c002f8f3de90fb153,0x79d5c18517284fbc6f51,0xff0d820d5d18ffa4b064,0x856872fd38d007a9eb15,0xc40fa833dfe8c7da5e76,0x1189c71cfb469be71afe,0xbe9175bbd5f757c011d6,0xc760283a1de20bc0edb,0x56362cf80cc0630006be,0x1fdacd5fc3feb8806c2f,0xe197b04a5cc28326ca0,0x150a04068dfacd2510d4,0x47da0871ea011ab5f106,0xbc8149fe1f0318f0181,0x427ffc50434120a4c2,0x2dab1c50280c40b6003,0x40030d814f1c62185109,0x43f0b880608507040180,0xe861e1afa88426a26168,0x4c000210050984fbe06d,0x1f419ca041f28d8f6010,0xa8a83dfee42c3c151af2,0x6e0060240894002bf84e,0x127a4b1336ac83765062,0x2e20429431a48002ad1,0xf538c99596200337a000]]
private def groupPage10 := limbs80 #[#[0x200b49235c91338e804b,0x650000ee442c3ba00028,0x5e42c018487464000fc0,0xba8b040cbe0cf81303da,0xbc9c9800066b4383ced9,0x75224281800339fa6cad,0x7d861da0340b13808865,0xb39e241dc02540d02580,0x5be70994afa36accb8f8,0x10055d03b09173834ec3,0x356ae5081b711ca04438,0x320b8e680af4261837d2,0xbea9f7432000c0f0244,0x41140140007bd018c,0xc72a990c348010831441,0x9d81ff086ad512a4766c,0x912b5444bd1af12510f,0xc6d98b188b]]
def g63H9 := groupedPages #[groupPage9,groupPage10]
def g63D10 := limbs80 #[#[0x221a42188a628220207f,0x5a96651086098440106a,0x5a868190e842146398c6,0x2a64020e21a0ea7980a,0x61086490461080a29902,0xc442100043c8680098e8,0x6aed589c449e0cc55218,0x6218d04212003e9d8da6,0x4df6830d5a9f469e0d45,0x8ba4a1e0b0360d00405e,0x50c000c18010182431c,0x80338018a01858712304,0x19a80670033800ee8032,0xa001280198019a803b40,0x7003bd0064015c007002,0xcb401d402b9806400c,0x74015e0067e803200af5,0x300af80194028015ea80,0x660063003a00a0052007,0x19ea019f400e7401c00,0x38]]
def g63H10 := limbs80 #[#[0x84800030082c0c0c,0x402018080a000180c22,0x8040204020040700024,0x6824220100018020a010,0x488c02020001800070,0x1000160105060060,0x50e010000c000080,0x80468000880828020381,0x1780c0001058080c0f04,0x12800061b078102200,0xc010288c4408010000c,0x20080d000180a000a014,0x480c0201000100200000,0x3028b8460b0403834050,0x110e000025d0080c040,0x680209030040e0388c3,0x34d018010b806101802,0x1054364405000020102,0x9000980606058140000,0x261e000040c360292c03,0x780405020200a0301010,0x40180c00010140a1a158,0x40100042080191c08510,0x4000c9460000000020,0x634060081604000040,0x8c41a050708804430500,0x1c0202068c404000f,0xa048141e0000800dc06,0x2000c440001507806,0x420070280c003e06818,0xb00c080d000083619050,0x904c580701021e6090],#[0xb28addc1004d03058120,0xc0900115201e48eadfe1,0xafdf95c287988741401f,0x2f45a140d00050206831,0x291541d2d6ca3e90c042,0x1148117d49a2a120022c,0x6802ee26420111d9bdfe,0xdebffec04a34c74ea3e1,0x542541b80315214000ea,0xea21dfdb15de9fdb10c1,0xa3d3157a6c220022020,0x28701800878fe7ff648,0xe4596a24c0535ba8a260,0x2a02c80291d319056a2c,0x49d60bb5b7840221b15f,0xda03652b62e80421d408,0x108600696d39ff136530,0x4c3d00fe4169ac833804,0x237005820300903d04ff,0x9ff08efad4f18cfb6d2e,0xa170afc3900420065101,0x4b00136cb0dfac7c109f,0x2458852373b1c3b80880,0xe80a00213015775ac563,0x3a09fe982a09ff773363,0x7a34c4200a2041d60099,0x8ac1f503052fd503002f,0xd75d717e36a4300a0200,0xa100000816f7fff7fc4,0x3f30d56e289181382448,0x3a24a80f0811c04c77ee,0x91f6df3e6f2ed82c6b82],#[0xda5f86bba4e8120120c1,0x210025a1d6ffda5f5caf,0xf76cc960b78a3d853014,0x55016833082097ccf7d,0xed7ef7f66c6217d78dc0,0x8991c205901612810809,0x8013ffff7fecbd2656,0x4503840994c405e01600,0x5016189848d785079708,0x7863e6f05923e79645e6,0x9c46c6801802860c197d,0x840cb73f68c8f32b489,0x594603a04886b01c3084,0x1e5022a84926dd578627,0x633dcd546211a34a26e0,0xcb871820000b8401fd74,0x9b4fb9e3620b99027a7,0x24d5aa4d275020490000,0x95d229bf6a29d11620,0x2e00000027ac4e87a020,0xa7e82400000010000000,0x8fd448173ebf1b09b14f,0x6955cee728098fddb6b4,0xa0c36344f625bc185250,0xe0143244543fd12cd112,0x5718d9121e8e98789636,0x58d3ab1b5186c65411d2,0x2d0092e92b846caa4284,0xdf5d8839cc7ac629622e,0xd1c011ea25b87b39a1b7,0xce474e2c865585b85c8f,0xcaf403ec0f0060e601f6],#[0x41084fd6bde9e940ce08,0x664bf872ea0b40c5ca,0x9a1043c6b982881c6c40,0x33b83324583b8d0ff875,0x481c185f6032a58f471e,0x817c7940e10cf6581103,0xc4c58f571a768d787f,0x4a00255fb413428d9,0x5e02b05604db7940f40,0xba61f4317122ed880895,0x5929cdc3c2d033c3e46f,0x57d1fddd0063fe7be25f,0x2569c6aa362752863dac,0xe57ec5f0f609149135b0,0xe77365e2da82257db5de,0xb50012eecdb03830e44a,0x1b84df7049a5810db142,0x401f7180171b3e1231fe,0x175c4d7702e25610e0f8,0x415984946370080268a,0xe321773203cc15b4ee36,0x6f004a5047d43d5dcada,0xb6c6d31ae14517cc1020,0x932e10b1f68fa016da00,0x380b24f36e312583d251,0xda13a056]]
def g63D11 := limbs80 #[#[0x8103f]]
def g63H11 := limbs80 #[#[0x40d0e9102044040600,0x700079f42c0ff73ff7f0,0x91e301796dea609b782,0xe60176b4300062398cd]]
def g63L : Nat → Packing
  | 5 => (4,6,6,262148,34,5,8192,g63D5)
  | 6 => (96,5,6,3407948,103,25034,8207,g63D6)
  | 7 => (1841,4,6,5964668,122,393871,8326,g63D7)
  | 8 => (3321,3,6,2359984,106,3469968,8313,g63D8)
  | 9 => (867,2,6,786473,70,2622095,8255,g63D9)
  | 10 => (41,1,6,65537,0,168522,8206,g63D10)
  | 11 => (1,0,6,65537,0,4096,8194,g63D11)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => groupLookup 2 7 0 1 3 1 g63H6
  | 7 => groupLookup 32 149 5 3 7 4 g63H7
  | 8 => groupLookup 614 2027 8 3 11 5 g63H8
  | 9 => groupLookup 1107 4057 8 3 12 6 g63H9
  | 10 => groupLookup 289 967 9 3 10 4 g63H10
  | 11 => groupLookup 14 53 6 1 6 1 g63H11
  | _ => fun _ => none
def g63 : Forest := ⟨63,11,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
namespace Nat92GE
structure TeachingShape where
  roots : List Probe32
  out : Probe32
  price : Nat
  select : Fin 92 → Fin 32

def hintShape0 : TeachingShape := ⟨[0xffffff97,0x16,0x2a,0x4c],0x70,5,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6] : Array Nat)[i.val]?.getD 0)⟩
def hintShape1 : TeachingShape := ⟨[0xffffffcb,0xffffffc9,0xffffffd5,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
def hintShape2 : TeachingShape := ⟨[0x2a,0x16,0xffffffab,0x4c],0x70,5,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6] : Array Nat)[i.val]?.getD 0)⟩
def hintShape3 : TeachingShape := ⟨[0x3a,0x16,0xffffffab,0x4c],0x70,5,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6] : Array Nat)[i.val]?.getD 0)⟩
def hintShape4 : TeachingShape := ⟨[0xffffff33,0xffffff55,0xffffff69,0x8e],0xf0,6,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7] : Array Nat)[i.val]?.getD 0)⟩
def hintShape5 : TeachingShape := ⟨[0x12,0xffffffcd,0xffffffd1,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
def hintShape6 : TeachingShape := ⟨[0xffffffd3,0xffffffcd,0xffffffd1,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
def hintShape7 : TeachingShape := ⟨[0xffffffdb,0xffffffcd,0xffffffd1,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
def hintShape8 : TeachingShape := ⟨[0xfffffe23,0x22,0x4e,0x94,0x118],0x1e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6] : Array Nat)[i.val]?.getD 0)⟩
def hintShape9 : TeachingShape := ⟨[0xffffff33,0xffffff31,0xffffff55,0xffffff69,0x8e],0xf0,6,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7] : Array Nat)[i.val]?.getD 0)⟩
def hintShape10 : TeachingShape := ⟨[0xfffffd47,0x146,0xfffffc6b,0x192,0x21c],0x3e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9,9,9,9,9,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9] : Array Nat)[i.val]?.getD 0)⟩
def hintShape11 : TeachingShape := ⟨[0x7c,0xfffffea9,0xfffffe3d,0xce,0x110],0x1e0,6,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6] : Array Nat)[i.val]?.getD 0)⟩
def hintShape12 : TeachingShape := ⟨[0xfffffac7,0x18e,0xfffff913,0x224,0x438],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
def hintShape13 : TeachingShape := ⟨[0xffff255b,0xffff49a3,0xffff0e0d,0x700e,0x8030],0xffc0,8,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,0,3,0,2,3,1,4,5,1,3,0,4,5,0,2,2,1,3,2,4,5,2,5,2,4,3,4,5,1,1,3,6,7,8,9,10,11,12,13,14,15,6,7,8,8,9,10,10,11,12,13,14,15,15,6,6,7,8,8,9,10,11,12,12,13,13,14,6,6,7,7,8,9,9,10,11,11] : Array Nat)[i.val]?.getD 0)⟩
def hintShape14 : TeachingShape := ⟨[0xfffffd67,0xfffffcab,0xfffffcc1,0x112,0x21c],0x3e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9,9,9,9,9,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9] : Array Nat)[i.val]?.getD 0)⟩
def hintShape15 : TeachingShape := ⟨[0x2e6,0xfffffc35,0x14a,0xfffff983,0x60c],0x7f0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,8,8,8,8,9,9,9,9,10,10,10,10,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,8,8] : Array Nat)[i.val]?.getD 0)⟩
def hintShape16 : TeachingShape := ⟨[0x46,0x56,0xfffffe11,0x8a,0x10c,0x210],0x3e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9,9,9,9,9,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9] : Array Nat)[i.val]?.getD 0)⟩
def hintShape17 : TeachingShape := ⟨[0x902,0xfffff67d,0xb6e,0x308,0x250,0xc60],0xf80,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9,9,9,9,10,10,10,10,10,10,10,11,11,11,11,11,11,11,7,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
def hintShape18 : TeachingShape := ⟨[0xfffffd3d,0xfffffd3d,0x3b6,0x184,0x528,0x630],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
def hintShape19 : TeachingShape := ⟨[0xfffffaa9,0xfffffaa9,0x53e,0x424,0x188,0x630],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
def hintShape20 : TeachingShape := ⟨[0x754,0x754,0xfffffd75,0x676,0x358,0x460],0x780,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,4,5,6,0,1,2,3,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9,9,9,9,10,10,10,10,10,10,10,7,7,7,7,7,7,7,8,8,8,8,8,8,8,9,9,9,9] : Array Nat)[i.val]?.getD 0)⟩
def hintShape21 : TeachingShape := ⟨[0xfffff431,0xfffff6b5,0xb3e,0x384,0x228,0xc30],0xfc0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,11,11,11,11,11,11,6,6,6,6,6,6,7,7,7,7] : Array Nat)[i.val]?.getD 0)⟩
def selectTeaching : Nat → TeachingShape
  | 1 => hintShape1
  | 2 => hintShape2
  | 3 => hintShape3
  | 4 => hintShape4
  | 5 => hintShape5
  | 6 => hintShape6
  | 7 => hintShape7
  | 8 => hintShape8
  | 9 => hintShape9
  | 10 => hintShape10
  | 11 => hintShape11
  | 12 => hintShape12
  | 13 => hintShape13
  | 14 => hintShape14
  | 15 => hintShape15
  | 16 => hintShape16
  | 17 => hintShape17
  | 18 => hintShape18
  | 19 => hintShape19
  | 20 => hintShape20
  | 21 => hintShape21
  | _ => hintShape0
def chartTeaching : Array (Nat × Nat × Nat) := #[(1,6,0x843623a5a),(5,6,0xdb15d6d13),(1,6,0xf2d56c705),(1,6,0x8f1da18b4),(9,8,0x29c44568e2d5),(0,7,0x38aa1eb18e9),(1,6,0x2c7383286),(0,7,0x1a39529015c),(9,8,0x15260a54735a),(0,7,0x23c5a84a613),(0,7,0x38711f31559),(7,6,0xba3a6caa1),(11,9,0x19571f38d3045c),(4,8,0x878caac698fa),(10,10,0x3992d51ca19c445),(0,7,0x19c7c45cd38),(0,7,0x23c7a86ae32),(20,11,0x3d25e156f5f23eb9),(1,6,0x347385306),(4,8,0x15858a5491da),(1,6,0x8c7983886),(0,7,0x34711f31655),(18,11,0x3199a387c2044a181),(0,7,0x1567c474e1c),(1,6,0x1cd38518c),(1,6,0x30614e347),(20,11,0x2339a56a84a703151),(0,7,0xe69528545c),(0,7,0x15c7c45ce34),(4,8,0x29444568e2d5),(0,7,0x3496cd7cb66),(20,11,0x559329535768738b),(0,7,0x3459cdbc79d),(0,7,0x15c76456cb4),(3,7,0x9c7c44cd21),(8,9,0x221836268c765a),(0,7,0x1ce11f15c59),(16,10,0x874cb8c29dbceb1),(3,7,0x91ce0cc185),(9,8,0xf19571738911),(10,10,0x29148519a389547),(0,7,0xe9bc19cd2c),(1,6,0xab887a8f1),(7,6,0x47871567c),(0,7,0x388a1eb18e9),(1,6,0x1e6b4616c),(0,7,0x318fa878ab2),(1,6,0x2da5ca0d2),(7,6,0xf3165ce11),(0,7,0x2ae21ea3c69),(0,7,0xc18538d1d5),(7,6,0x86acb18fa),(1,6,0x8e9ba18ac),(0,7,0x1c58578d1d5),(10,10,0x3a93631cc1a2843),(0,7,0x34cb8dbceb1),(18,11,0x3199a387ca244a181),(0,7,0x29d7c96cd38),(0,7,0x221839a31cb),(0,7,0x1114a55a389),(0,7,0x23a7a872e2a),(0,7,0x32aa1eb1a63),(3,7,0x2a878a7ac63),(3,7,0xdc7c44cc21),(0,7,0x15c664468a5),(0,7,0xe255296445),(15,11,0x1a2d534739e4ca15c),(0,7,0x15c7c45cc34),(11,9,0x2acb8869c79ea3),(0,7,0x298fa878caa),(0,7,0x38ca1ea98f1),(11,9,0x298f1eb8cb086a),(8,9,0x221832a68c72da),(1,6,0x4f25b35f6),(16,10,0xb478e69ec0c68a5),(0,7,0x31a7c874930),(12,11,0x64eac921ce9b3e9a),(1,6,0x3872c6283),(19,11,0x11725b34655b71d7c),(3,7,0x32b21f33b6e),(17,12,0x8e668b1f28962820c6),(16,10,0xd478e69f40c68a5),(8,9,0x78e6b431a2b25),(4,8,0x15848a54d1da),(12,11,0x2ae05b28eabbbc369),(0,7,0xe6bc2ace1c),(0,7,0x724e0c628c),(12,11,0x2ae25b28eabbbcb69),(4,8,0xf15c59d1cc11),(0,7,0x298fa878c2a),(11,9,0x34738471679f15),(20,11,0xa71615a2de54e347),(1,6,0xb2286eb63),(9,8,0xea98f1ab8ca1),(10,10,0x55a64e35115628c),(5,6,0x3891c6303),(7,6,0x14c28724e),(0,7,0x9387305183),(16,10,0x47459c519dbc795),(0,7,0x3496cd7cb6e),(0,7,0x78e60c68b4),(0,7,0x16d1cd9df15),(0,7,0x755a14a613),(0,7,0x2dd7c96cd38),(0,7,0x38d11f19571),(3,7,0x62836872ce),(10,10,0xf077a3e9ce250e2),(0,7,0x38713f335da),(0,7,0x25d2cd6df26),(9,8,0x474e1cc5567c),(0,7,0x15c7c454e34),(0,7,0x1957c478d1c),(9,8,0xea3a71ab2e21),(7,6,0x4f2e1bc7a),(4,8,0xea3a71ab2e21),(8,9,0x231e6a43886b25),(16,10,0x1b486c90ec7ca66),(0,7,0x23a7a862e2a),(16,10,0x1462b20953b6e87),(1,6,0x843323a4e),(0,7,0x34cb8dbceb9),(17,12,0xb254dcd239f15f7f35),(0,7,0x3459cdbc795),(1,6,0xb1c17cb55),(9,8,0xf19571738d11),(3,7,0xd1ce0cc185),(20,11,0x3c65a8dc9180f8862),(0,7,0x29c7a86acb8),(9,8,0x872e2ac63a7a),(0,7,0x32d21da39f1),(9,8,0x29c15139a2d5),(16,10,0x86ce2aa23f2eea9),(3,7,0x31f15d11738),(8,9,0x78e6b431a2925),(18,11,0x11725b3855dc6df39),(11,9,0x318e9eb8aa8862),(0,7,0x734e14630a),(21,12,0x8e668b387ca244a0c6),(9,8,0xf31559d38711),(1,6,0xcd7d93c96),(8,9,0x78e6b431a2b24),(9,8,0xeb18e9cb8aa1),(18,11,0x672ae3439e9baf36),(7,6,0x9a3a648a1),(0,7,0x2519c9bc795),(12,11,0x31aa8821cb8e6e9a),(1,6,0xb3497cb75),(18,11,0x3c5661cdd14b0614c),(18,11,0x368da2c7ca258a0c6),(1,6,0x1ce34614c),(0,7,0x23c5a842613),(7,6,0x456d31576),(8,9,0x34b211bcc691e6),(10,10,0xf885c1631daf0d),(8,9,0x78e6d431a2d25),(0,7,0x221839a31da),(0,7,0x2aca1ea9c63),(3,7,0x91ce0c0185),(0,7,0x3167c474738),(9,8,0x465e1cc5567c),(18,11,0x36c5a655cb0598454),(3,7,0x328668738b),(9,8,0xea98f1ab88a1),(0,7,0xb6b12a1c11),(1,6,0xbbaf2ab38),(9,8,0x15360a54735a),(1,6,0x38d1cc185),(3,7,0x34e32e76ebc),(0,7,0x26f3ab2ae32),(1,6,0xca18b1ce),(0,7,0x755a14a616),(0,7,0x28903b8b1e3),(11,9,0x29c63eaaca2878),(0,7,0x78e60c68a5),(0,7,0xb695285511),(0,7,0x31a7c874938),(1,6,0xbbceacab8),(1,6,0xb38abcbba),(0,7,0x29c7c86cd38),(1,6,0x73847c771),(3,7,0x38cb4cfcdba),(18,11,0x26c5a6558a0198444),(9,8,0xf15671734e11),(0,7,0x34cb8dbcef1),(7,6,0x878aa3a7a),(16,10,0x96ce2aa27f2eea9),(3,7,0x1c4f45fccdb),(0,7,0x9395291585),(0,7,0x38713f335db),(16,10,0x8b4b25923f35b66),(0,7,0x31a7c874b38),(0,7,0x1848578d1d5),(17,12,0x716ab8d0e7a6ebef36),(0,7,0x1af36716d32),(16,10,0x878b2aa23f3aba9),(1,6,0x14630734e),(0,7,0x78e60c68a4),(12,11,0x261f18e71a4883865),(1,6,0x4d6c97cf6),(1,6,0x18a0ce1cb),(8,9,0x231e6a43886a21),(0,7,0x164ca5ce2da),(1,6,0x8e6562874),(0,7,0x38713f335d9),(3,7,0x1c46457cc59),(0,7,0x724e14630a),(1,6,0x5b47367bc),(11,9,0x34e1c45565df31),(4,8,0xea3a71aa2e21),(4,8,0xea9c63e2ac21),(21,12,0x9a368e2c7ca258a183),(4,8,0x15c48a54d1de),(1,6,0xf2dd6cd25),(4,8,0x15c48a54d1da),(1,6,0xe2a87ac63),(0,7,0x263bc1b472c),(1,6,0x30518d387),(12,11,0x3c99a3aed387062aa),(8,9,0x2cab886ef3ac69),(8,9,0x34cb8876f3aa71),(11,9,0x31655f34714478),(9,8,0x86ae32a63c7a),(1,6,0xd9ef16d1c),(18,11,0x3399a387ca24ca183),(8,9,0x38b2a87ceae8e9),(10,10,0x3a93631cc1aa843),(9,8,0x878caac698fa),(8,9,0x325912b6c552da),(16,10,0x1b496c90ed7cb66),(14,10,0x1a5734b073a6b7c),(10,10,0x878c2a8b18e9ea6),(13,16,((0x974b24ca <<< 64) + 0xa8b8c28d6dba6f3a)),(0,7,0x3157c478734),(12,11,0x135b8c925dbcf6e9a),(17,12,0x1e668b8d61b22820e2),(9,8,0x478d1cc5957c),(14,10,0x29687044e2da5f1),(11,9,0x32e2a863a6beb1),(12,11,0x13c9c592cd95f679a),(19,11,0x3c54e1cdd1c1ac305),(12,11,0x2ae25b28ea3bbcb69),(16,10,0x2b259348bdb35da),(11,9,0x318e9eb8aa8872),(8,9,0x3471617cd9e1d5),(11,9,0x31a63eb2aa2878),(5,6,0x8b48639b1),(17,12,0x9a368e1f2893282183),(8,9,0x34b251bcd6d1e6),(12,11,0x21d2ab24d63a7cba6),(10,10,0x15850a1951c968e),(14,10,0xf0dc5956cd1c151),(16,10,0x2b24d648ecf65da),(10,10,0x54e35a645446298),(15,11,0x21d0a6164419b1689),(12,11,0x11c9c592c5957679a),(1,6,0xe1c47ce55),(4,8,0x872ab88f1a7a),(8,9,0x1c5b445ef36c55),(16,10,0x17459c50ddbc795),(11,9,0x38caa8698ebeb1),(4,8,0x478d1cc5957c),(12,11,0x3c569c7572ce11865),(16,10,0x432593499db35da),(21,12,0xaac5b2d383ae6b6ebc),(20,11,0x3c34e8dcc0c0ec862),(12,11,0x34713594f31d9e5d5),(8,9,0x3459c476f1e655),(17,12,0x593974c875e3d77db3),(8,9,0x3abbcdaae2cd32),(14,10,0x156b347073557bc),(21,12,0x8e668b387ca24ca0c6),(10,10,0x9951f18c68b4461),(17,12,0xd16ab8726d8eebef1e),(16,10,0x86cab8a31bbcea9),(8,9,0x38d3287ceb68f1),(10,10,0x1d935a38519360a),(14,10,0x15818c2951c968e),(10,10,0x54e35a645456298),(4,8,0x47473857167c),(16,10,0x632593499db35da),(15,11,0x151da38b35d4c529c),(12,11,0x21b32d24a63c7cda6),(18,11,0xab16d383ae6b6f3a),(8,9,0x3459c176f1e355),(17,12,0xe2a5b4b1ae8edbef2e),(17,12,0xc939745a3cc7d77d97),(9,8,0x15858a5491da),(12,11,0x261e98e71a4883865),(0,7,0x96b12a1c91),(4,8,0xea3c69caac21),(18,11,0x35a5d321d78f5db3),(14,10,0x2940c615a2ce547),(4,8,0x4f8d1ccdb5fc),(8,9,0x32593636cd765a),(0,7,0xd57c16cd1c),(16,10,0x478cb4c15ebcdb1),(8,9,0x1673445edbcc55),(8,9,0x34cb8476f3a671),(8,9,0x2ce2a87cbba8e9),(9,8,0x6891d5298485),(0,7,0x72ce0c628c),(8,9,0x324d62b3d9739a),(11,9,0x1cd38459c79f15),(16,10,0x870b2a823f3aba9),(10,10,0x6a32f164a632851),(12,11,0x22e25d30ea39bcd71),(10,10,0x3992d51ca19c405),(14,10,0x1a847084e1e6a71),(12,11,0x35aac921cb8f6e9a),(18,11,0x3cc668e9d30b22868),(10,10,0x8728b8a23a71ebc),(8,9,0x68832a61e32ce),(19,11,0x3c98d1ced2c15c306),(10,10,0x9b18d51e21b4445),(8,9,0x34b258bcd6d8e6),(0,7,0x182856951c9),(8,9,0x2ab3886eebcc69),(8,9,0x325932b6cd72da),(12,11,0x3cc49575e2c711165),(8,9,0x32e344fadbc5f1),(0,7,0x32593db35da),(4,8,0xf19c55e1cc11),(12,11,0x3c6a639ee34b0a196),(16,10,0x86c8b8831bbcea9),(4,8,0x47891cc5957c),(13,16,((0x478718c9 <<< 64) + 0x64b4c14c5579af36)),(12,11,0x135b8c925d9cf6e9a),(10,10,0xf0da55c6cd1c151),(17,12,0xb2a5b4e0eb9adbef3a),(12,11,0x361f18e75b4c83865),(14,10,0x29118315a389547),(11,9,0x19c55f1cd14478),(10,10,0x478c1c531559f1e),(8,9,0x16c937365f375e),(8,9,0x3892287cea68e9),(8,9,0x3845c2b1f1539a),(9,8,0xf19c55e1cd11),(9,8,0x45ce34655c7c),(8,9,0x3892a87ceae8e9),(10,10,0x1d935a38519160a),(1,6,0xb2a86eb63),(11,9,0x15671f34e3045c),(8,9,0x16d1c4f67bc6d5),(11,9,0x1ce34455c75f19),(8,9,0x2cab896ef3ad69),(12,11,0x1cd13594f197b65d5),(8,9,0x38cb447af36571),(11,9,0x31559f38718474),(13,16,((0x874b24ca <<< 64) + 0xa8b8c28c69ba6f3a)),(12,11,0x115b8c925d9c76e9a),(12,11,0x3cc4d575e2c711165),(18,11,0x3c9951ced2470518c),(16,10,0x878d32c23f3adb1),(14,10,0x156b347072557bc),(8,9,0x38b2a83ceae8e9),(18,11,0x31a59221d78f59b3),(19,11,0x11e25b34671b55d7c),(8,9,0x38b2287ceae8e9),(5,6,0x19c147395),(15,11,0x1a25534739e44a15c),(10,10,0x86a8b8c23c69ebc),(10,10,0x86aa32c29c63eb6),(13,16,((0x472592e1 <<< 64) + 0xc634c14c5579adbc)),(12,11,0x13c9c592cdb5f679a),(1,6,0xd6df25d2c),(12,11,0x22e25b28ea39bcb69),(8,9,0x3ceaed78b2a974),(11,9,0xd1d569849014a),(20,11,0x11d25a956f5bb1eab),(17,12,0x1e368e9930f22821a2),(0,7,0x755a14a612),(8,9,0x3496c1b5f2d3a6),(14,10,0x29118315a38b547),(16,10,0x1b4b25907f35b66),(8,9,0x38862a31e638b),(10,10,0x54e35a645456290),(10,10,0x8de3fcb4387272c),(1,6,0x1e6d46174),(8,9,0x2470617c99e1d5),(10,10,0x45c538c15c59f3a),(8,9,0x34b251bcd691e6),(10,10,0x4f8c9c5b35d9f1e),(8,9,0x32e344fadbc5f3),(8,9,0x2cd25abcb75ae6),(16,10,0x174716507f36795),(8,9,0x2ce2a97cbba9e9),(8,9,0x16d1c4f67bc6d7),(5,6,0x8ac8639a9),(1,6,0x39a5ca193),(14,10,0xf0ecd76ace1c293),(10,10,0x7035a1d1ef098f1),(0,7,0xd387305183),(16,10,0x45c5b45317bcd95),(13,16,((0x4f2592e1 <<< 64) + 0xc634c14cd779adbc)),(12,11,0x21d2ab24c63a7cba6),(13,16,((0x45ce185b <<< 64) + 0x24b4530571e9af36)),(12,11,0x115b8c92559c76e9a),(13,16,((0x2a1ca215 <<< 64) + 0x619105225ada6c55)),(10,10,0x6872d564a616151),(12,11,0x5b16d2434757cda6)]
def pickTeaching (k i : Nat) : Nat :=
  match k with
  | 6 => ((#[0,1,2,3,4,5,6,5,7,8] : Array Nat)[i-86]?).getD 0
  | 7 => ((#[9,10,5,5,11,6,12,9,6,13,14,15,16,17,18,14,19,5,20,21,22,23,24,25,26,27,28,10,10,29,30,5,31,16,5,32,32,14,33,34,35,10,36,37,38,39,10,40,14,41,42,43,16,5,44,9,45,46,5,27,10,47,48,4,49,50,51,52,5,19,36,6,21,33,38,53,54,10,3,10,37,55,5,56,3,3,57,37,5,36,9,5,10,46,58,59,60,46,61,15,62,63,64,65,53,66,44,67,68,69,70,71,13,72,73,18,74,74,70,55,5,61,27,75,9,76,77,13,78,79,18,80,16,81,5,82,83,4,10,84,85,69,37,71,86,85,87,10,27,88,55,5,5,5,36,26,10,58,10,6,89,69,90,91,92,61,93,94,5,95,20,9,81,96,62,24,97,20,98,99,46,10,100,101,13,65,6,102,103,10,33,95,6,95,2,70,27,104,15,67,18,105,77,5,106,61,93,28,52,61,68,107,5,108,109,5,66,31,33,62,110,29,107,111,28,28,28,112,98,74,1,16,24,70,16,41,113,18,10,109,27,33,114,69,10,10,93,6,64,2,115,116,98,74,46,117,13,109,82,118,119,120,33,121,122,13,61,21,70,5,4,123,124,5,16,5,125,126,6,10,102,41,127,5,5,128,15,123,13,127,10,111,129,130,116,10,19,5,74,85,131,132,133,5,102,10,134,96,33,5,118,10,135,16,136,137,91,10,138,10,70,139,29,10,10,32,140,18,99,107,141,112,116,142,143,144,48,123,79,132,145,146,147,148,149,150,5,6,10,89,151,49,10,93,40,69,10,152,33,10,123,10,153,5,10,16,154,10,155,53,93,5,62,10,156,157,16,24,10,158,159,27,26,91,74,160,74,161,29,162,61,29,10,163,105,102,164,27,5,107,5,16,5,45,165,5,61,166,167,168,169,5,5,170,119,171,3,19,93,97,6,10,61,172,20,156,71,173,28,174,121,175,10,176,10,5,177,85,178,37,178,71,48,138,86,5,61,179,3,76,71,9,10,156,30,107,180,13,181,2,5,182,71,126,123,183,141,10,85,71,184,93,85,21,18,185,186,74,123,2,2,182,16,127,10,5,127,178,55,9,61,187,183,188,189,62,19,190,37,70,5,10,71,93,33,93,78,191,10,32,192,91,193,107,194,145,10,136,195,196,29,197,55,58,178,198,199,143,156,91,102,156,13,167,10,200,16,102,16,201,202,9,128,32,85,69,157,203,55,85,60,58,4,61,204,205,16,5,9,5,206,207,106,16,10,10,208,209,210,53,61,149,9,211,212,5,71,64,71,29,213,53,36,10,87,20,136,85,71,70,3,4,10,214,33,215] : Array Nat)[i-1245]?).getD 0
  | 8 => ((#[74,46,16,216,28,217,123,24,74,218,219,34,220,5,66,221,222,14,109,223,10,71,218,21,224,225,226,128,91,5,227,228,229,226,10,20,6,30,230,231,70,232,106,5,91,10,36,160,233,82,192,234,235,93,236,237,238,128,71,24,10,112,31,104,239,235,40,71,85,240,5,123,37,241,91,242,154,66,243,239,244,41,74,21,245,148,246,5,217,5,41,66,197,239,28,247,226,248,249,250,243,194,251,81,252,124,128,70,249,37,124,226,91,82,10,253,40,254,41,71,91,255,40,15,256,86,257,115,93,61,31,165,218,53,229,37,93,148,257,217,258,251,207,259,93,80,10,93,260,20,261,247,226,41,86,40,13,262,59,10,263,76,85,24,74,85,264,261,16,93,124,265,16,66,41,53,5,257,226,243,104,266,70,225,74,10,66,210,250,267,41,224,261,71,104,178,268,109,5,33,66,41,225,103,224,36,10,99,205,93,93,11,71,66,226,267,207,221,269,13,5,33,270,123,222,74,226,14,41,74,197,271,74,163,165,272,74,109,61,223,251,27,273,124,274,241,275,256,260,10,270,5,222,40,66,15,12,237,66,93,226,276,25,277,98,278,154,74,194,71,250,71,10,148,226,15,85,85,260,128,243,40,239,5,154,246,218,279,5,210,194,107,14,153,280,154,85,217,71,68,217,281,80,282,156,224,97,5,12,247,24,93,242,5,164,85,61,283,5,31,10,256,284,210,278,285,286,97,82,287,282,98,10,288,250,289,154,5,74,274,290,243,71,5,247,40,257,10,123,27,291,274,243,223,4,221,5,128,16,91,115,33,5,5,88,31,124,221,278,124,61,235,138,235,260,4,239,5,128,37,218,31,123,124,53,81,93,292,54,270,224,82,267,16,93,293,124,4,61,294,6,226,273,61,74,237,244,224,295,241,210,10,296,250,224,297,257,123,16,74,223,20,127,37,61,133,5,273,31,242,16,5,31,221,257,242,82,30,16,85,224,278,296,70,5,278,224,74,109,242,222,128,85,298,278,10,61,134,5,61,93,226,239,71,123,235,61,235,266,221,152,24,222,226,15,33,5,128,261,66,299,148,244,226,10,61,37,148,154,260,239,66,300,127,5,71,74,112,257,74,261,93,81,242,71,301,61,66,136,266,74,270,61,31,124,267,93,85,267,224,154,40,61,302,34,61,109,5,260,244,59,303,304,97,182,21,81,285,74,98,178,218,4,192,58,279,81,71,277,5,227,221,25,98,239,178,305,239,207,247,10,306,109,148,10,127,280,61,61,21,85,273,217,194,14,5,160,128,5,244,246,243,307,60,13,27,283,290,308,53,260,68,57,81,309,226,267,109,226,128,81,147,141,270,226,87,5,277,74,256,279,6,10,128,221,74,267,256,260,28,310,164,235,14,218,147,31,5,273,267,5,13,311,124,81,267,85,235,312,285,10,82,226,10,239,246,109,128,277,310,61,28,284,66,81,228,13,41,21,207,237,66,192,23,33,32,294,82,5,313,81,61,5,33,270,40,247,314,41,54,267,14,280,10,25,245,33,14,14,10,66,61,74,10,250,31,61,270,13,308,16,239,304,123,239,285,116,241,71,239,93,224,134,15,267,31,74,33,272,85,277,71,247,147,237,109,134,178,5,154,164,5,109,235,310,85,315,41,316,290,74,71,249,244,112,5,267,85,128,148,317,4,16,252,243,293,229,31,293,61,226,298,10,95,271,97,318,247,192,13,244,229,239,319,64,124,10,6,85,66,237,320,40,71,18,70,221,250,21,242,308,28,259,239,273,13,147,235,5,10,250,134,123,154,10,296,10,321,154,71,30,322,224,13,5,224,5,5,10,33,192,5,14,271,83,69,5,9,323,81,33,91,220,5,33,61,269,324,298,274,71,71,243,218,24,325,266,23,222,61,221,31,182,15,86,28,33,112,255,82,270,164,287,320,20,81,13,124,317,221,285,260,91,149,274,5,24,40,226,149,41,60,60,182,109,10,226,207,49,93,6,5,224,5,239,9,133,63,124,264,326,327,61,66,6,10,261,210,267,37,93,182,10,267,5,328,261,178,71,88,267,234,225,85,237,93,16,228,128,156,221,70,267,267,201,329,238,109,266,15,128,74,330,270,93,189,66,261,74,78,128,192,279,290,74,273,266,28,15,246,15,260,264,91,5,278,128,5,66,258,229,224,5,81,293,66,10,148,239,5,205,124,260,70,285,242,210,71,86,85,128,86,33,331,18,148,27,217,164,261,60,332,40,246,58,261,333,242,112,66,41,279,128,71,85,24,28,112,269,74,267,41,29,24,275,61,334,258,335,60,41,16,10,5,91,25,217,28,134,61,278,272,194,74,261,83,224,336,312,91,71,337,221,23,207,239,239,21,9,243,10,338,31,85,71,13,5,61,250,128,221,339,282,244,154,25,178,10,123,24,124,257,74,131,247,5,31,322,256,20,10,82,74,31,146,4,243,274,53,21,285,301,93,81,154,294,340,24,109,244,98,121,341,239,226,66,243,164,314,41,257,10,12,197,93,293,5,15,165,10,5,217,270,20,123,244,243,342,85,223,128,123,81,219,43,343,104,237,81,257,265,81,242,270,267,82,241,66,61,128,13,60,187,226,218,242,154,218,71,78,74,41,74,217,344,260,182,28,33,5,61,260,224,267,208,250,12,80,267,4,36,345,304,318,293,250,74,239,177,273,194,46,93,128,4,81,123,243,346,122,229,178,40,344,148,148,313,41,347,148,71,239,249,14,122,74,85,241,348,66,147,41,14,82,15,71,226,93,251,10,61,81,349,71,63,207,5,207,237,74,102,85,350,222,112,13,289,226,277,5,277,351,352,71,134,279,5,5,57,226,61,226,273,353,82,354,261,33,6,58,201,284,235,273,80,85,66,261,207,355,328,74,93,250,123,228,217,293,126,270,345,226,93,356,261,243,357,235,15,358,71,359,31,148,274,360,246,304,178,98,124,244,28,267,21,124,226,194,5,136,93,10,15,146,31,93,250,278,273,61,74,244,192,235,61,41,294,294,298,70,82,109,91,256,81,260,256,217,41,128,10,218,71,225,361,261,98,15,261,140,109,66,93,97,226,59,279,81,74,85,287,293,242,128,223,165,249,273,25,260,221,239,273,124,5,40,29,270,242,10,5,218,270,5,61,360,362,346,74,10,41,218,5,20,278,250,340,61,10,5,27,242,361,128,61,363,71,250,290,85,178,217,60,192,93,210,68,16,123,128,285,32,208,232,263,192,109,10,33,224,270,267,80,60,126,128,33,266,82,32,6,270,5,274,5,53,364,124,178,221,224,33,164,217,91,81,10,365,14,246,280,124,10,60,10,251,134,134,25,5,5,66,85,33,128,266,317,31,71,70,123,235,363,40,14,109,6,250,228,15,78,301,138,109,280,71,329,41,85,10,366,282,226,367,15,279,41,10,10,91,5,224,71,221,37,368,78,112,369,124,85,194,5,370,80,274,152,273,16,241,290,85,13,237,40,93,261,5,10,154,244,61,71,109,226,277,218,371,10,123,243,250,85,225,372,221,91,9,260,205,71,81,66,28,261,34,5,60,5,124,148,273,128,225,82,74,16,275,279,15,115,37,33,302,85,74,178,5,61,16,314,13,226,109,71,165,226,60,250,10,243,85,280,121,301,249,112,91,18,5,147,93,246,207,270,221,74,273,19,256,301,66,5,320,12,196,16,74,229,33,244,330,260,32,69,24,61,15,246,154,74,218,373,273,13,104,147,246,32,355,221,374,267,66,16,10,81,80,93,5,16,208,25,283,226,209,112,267,31,284,97,41,375,10,15,37,71,14,74,74,284,154,176,237,10,141,228,10,61,85,16,274,134,148,376,273,28,238,317,74,273,294,142,5,128,128,81,337,267,16,194,263,278,61,37,250,377,217,300,95,41,164,74,226,21,269,61,41,249,66,61,246,61,20,109,378,10,267,93,290,10,10,66,66,93,257,10,98,247,261,379,194,93,124,91,5,192,5,93,24,25,82,24,10,237,66,380,82,243,61,178,93,41,5,66,109,226,267,160,278,138,293,85,15,10,329,10,210,237,30,312,124,91,82,16,80,128,280,220,82,5,10,74,70,85,104,267,5,41,249,266,81,10,177,24,25,61,93,263,10,41,5,226,267,261,14,5,226,66,78,160,20,78,261,218,279,16,16,221,285,340,66,66,226,371,194,247,40,41,246,5,40,294,381,382,74,16,304,285,315,5,239,282,207,242,261,24,228,244,128,149,37,97,13,5,308,290,95,283,314,210,5,246,4,85,5,6,71,249,128,267,61,226,199,93,383,267,134,301,229,148,14,6,10,241,86,91,257,80,85,10,149,225,203,173,16,251,123,278,272,9,197,314,280,224,229,40,260,347,93,270,242,128,346,91,6,40,293,147,340,246,243,5,82,58,5,326,123,304,53,15,384,224,261,309,226,26,261,37,385,273,293,85,124,16,66,81,242,61,40,109,16,41,226,386,134,5,124,154,221,28,220,194,128,81,153,78,80,256,10,60,280,71,279,74,273,235,85,31,260,375,293,13,207,377,93,346,270,128,301,228,61,93,387,239,182,27,74,246,70,10,266,58,235,257,154,243,331,192,293,41,61,267,164,70,297,124,82,74,16,148,257,242,61,66,388,261,267,5,274,244,74,5,277,250,229,259,40,15,16,280,13,278,136,37,312,74,40,371,93,13,74,270,8,12,182,49,315,8,224,273,115,226,389,95,9,225,249,5,81,28,16,224,10,123,5,128,82,112,93,53,74,66,134,85,351,298,257,243,86,346,147,128,256,5,290,178,6,10,41,245,207,390,37,10,25,225,10,314,318,148,337,23,104,5,218,261,261,128,5,249,312,280,257,87,293,5,112,33,391,61,10,37,148,293,346,260,124,97,381,392,284,74,10,123,154,70,141,261,192,10,244,277,222,134,112,40,10,244,134,74,226,337,269,10,229,109] : Array Nat)[i-1114]?).getD 0
  | 9 => ((#[217,393,261,261,229,14,243,266,66,293,82,257,66,293,308,301,275,66,261,76,229,82,274,301,314,82,66,66,154,317,325,348,348,394,82,314,325,66,293,82,76,257,247,304,362,293,317,225,66,66,395,40,293,243,249,82,82,76,308,325,218,325,325,301,225,66,325,325,66,293,229,82,247,308,325,231,269,225,154,66,348,40,243,269,257,250,154,317,66,325,304,76,396,304,281,250,277,348,224,283,297,348,154,40,325,224,40,397,14,218,243,247,348,66,317,348,243,269,76,277,304,66,40,229,348,398,243,66,261,14,249,224,225,40,266,301,76,261,317,277,154,261,40,82,308,154,257,301,247,66,224,249,66,229,82,82,275,247,348,224,14,308,82,398,66,225,266,218,308,224,14,249,82,277,218,217,325,261,398,348,301,275,229,154,398,14,348,40,277,249,66,82,308,317,348,224,154,308,247,66,249,275,395,398,283,154,224,247,348,398,249,224,218,275,301,362,277,325,399,317,66,275,325,66,76,325,269] : Array Nat)[i-640]?).getD 0
  | _ => 0
def selectedTeaching (k i : Nat) := (chartTeaching[pickTeaching k i]?).getD (0,0,0)
def tileRows (w : Nat × Nat × Nat) (r : Fin 32) : Row :=
  Fin.ofNat 512 ((w.2.2 >>> (6*(if r.val<w.2.1 then r.val else 0))) % 64)
def teachingTest (g : Forest) (k i : Nat) : Bool :=
  let w := selectedTeaching k i
  let s := selectTeaching w.1
  facetOK32 (tileRows w) s.roots s.out (targetOf g) (stateSet g k i) k s.price
def viewBank32 (rows : Fin 32 → Row) (ws : List Decor) : List Probe32 :=
  ws.map (fun w => sample32 rows w.1)
def program32 (n bits : Nat) (ws : List Probe32) : List Probe32 :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) 0
    let b := ws.getD ((bits >>> 4) &&& 15) 0
    program32 k (bits >>> 10) (ws++[bv ((bits >>> 8) &&& 3) a b])
def programmed32 (g : Forest) (raw : List Probe32) (k i : Nat) : List Probe32 :=
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  let recp := forestRecord (g.levels k) raw.length i
  selectLive (recp >>> len) (program32 depth (recp &&& ((1 <<< len)-1)) raw)
def cachePass (g : Forest) (k i : Nat) (raw : List Probe32) (r : Fin 32 → Row) (s : TeachingShape) : Bool :=
  let ws := programmed32 g raw k i
  decide (stateSet g k i).Nodup && ws.all (avail32 s.roots) &&
    decide (k < s.price + ws.countP silent32)

def teachingRawPack := limbs80 #[#[0x9000b000000150036,0x2e002d00190026,0x3f000000190032003f,0x2a00340034002a0036,0x33003f001900000009,0x6900ce0055008e,0x4c00690000002a0017,0x2a0019003f0034007f,0x330068001200000000,0x55008e000000550069,0x69000000690033008e,0x680033001600000055,0x7f0069002a00000017,0x2e002400320019004c,0xa9000001c2003f0000,0x33008e007c01ff0131,0x1e300ff006900550000,0x1460394026d02b8,0x7f0055001600000068,0x160000005500680033,0x35804260575007f0033,0x190034039f02fb00ab,0x8e00000000002a003f,0x69005500aa0033,0x19003f0034,0x2a006900000017002a,0x2c203c60449004c007f,0x68063005280184,0x340016007f00330055,0x19003f002a,0x26003f0015000b,0x358028a075404a70000],#[0x550068001604600189,0x68000000330069,0x330033007f00160055,0x69008e0055008e,0x4c0016007f0001002a,0xab0676039f0575007f,0x7f002a000100000358,0x160068004c007f0017,0x690033007f00000055,0x33003a005400160000,0x230023009401dd004e,0x69004c000000170118,0x10c008a0211002a007f,0x3a006903ff01ef0056,0x710000000000540037,0x9600fd00cc00aa0000,0x192021c006b02b90147,0x55007f006800000000,0x26000b00330016,0x26003f00150034,0x170011003f001b000d,0x7f004c00490000002a,0x9003f0034002a,0x160000003300680019,0x8003f002a007f0055,0x19000000190034,0x170032003f002e0024,0x7f002a00690000004c,0x1004c007f002a0017,0x110000001b00260000,0x9002a0034003f000d,0x2a0017003f00000019],#[0x1e300000069004c007f,0x1460000039002b8026d,0x7f0016004c002a0001,0x18402c203f60449007f,0x3e0000006806300528,0x7f0017007f00330055,0x69004c00000001002a,0x4c0017002a0016,0x160033000000550068,0x2a000000690017007f,0x45002b007f004c,0x69007f0016005c,0x690033003a00540054,0x330068000000550016,0x1600680055004c0033,0x6b501f3067c03ca0000,0x550000006800000519,0x183003d0033007f0014,0x6801ff00ce01560000,0x7f0016005500000033,0x69004c0000002a0017,0x131000000a901c2007f,0x9401ff004e01ff007c,0x3f0026011800010023,0x3a90015003f0000000b,0x2f300000210037501ee,0x550030001600000068,0x113043807ff0224007f,0x34003f0019018e02c7,0x53e00000000002a,0x1601cf067702a903db,0x7f004c002b002b0045],#[0x250030804910fff0982,0x37501ee03a90c60,0x16b01dc01b102f30210,0x33008e00e700000022,0x113000000690055008e,0x6fd022406ff018e0438,0x33007f005500680000,0x330055005e00680016,0x18e0438011300000000,0x7107ff022406ff,0x6800aa00ff009400cc,0x7f0016005500000031,0x1ff00ce01830000003d,0x676039f057500ab0156,0x260015000b00000358,0xaa0071003f00000026,0x2b800ff009600cc0000,0x39401e3026d0146,0x32002e002d0019,0x1b0035000d00260000,0x3e0033005500000000,0x8a0211000000000068,0x2a010c03ff005601ef,0x7f004c0017007f0001,0x100000055007e0068,0x16007f004800050033,0x6800550069002a007f,0x68000000330016,0x17007f00330055007e,0x69007f004c002a0000,0x8002b0045007f0016,0x2b8039401e301460000],#[0x2a00170016026d02b8,0x1004c004c007f0069,0x8e007f002a0016007f,0x6900ff003300550000,0x7f0012005500000068,0x550033000000680033,0xcc00710016007f,0x35002600ff009600aa,0x71001b003f000d0000,0xff009600aa000000cc,0x2200c701dc01b1,0x5603750211008a016b,0x55006801ef010c,0x1ef0211007f00120033,0x3600460056008a031d,0x260000000b00090015,0x7f0017004c002a0001,0x9020daf026c067d007f,0x7f002a00010cf7039f,0xb004c007f0016,0x71002600150036003f,0x9600ff00cc00aa0000,0x540077003a0069,0x75404600189028a0000,0x16006804a70754,0x55008e007f00330055,0x1700ff006900330000,0x7f00690000002a004e,0x5500ce0069008e0033,0x1ef010c005602110000,0x3a0000005403ff008a,0x1dc01b10069007f0023],#[0x53d00e700000020016b,0x1cf067b02d703b60000,0x130007c000000a901c2,0x33007e0055006801ff,0x4c10ff7094a00000000,0x710c3002280384,0x3400cc00ff009600aa,0x2a003f00000019003f,0x22016b01dc01b0,0x96000000aa007100e7,0x67b053d000000ff00cc,0x32001901cf02d703b6,0x41003f000000080024,0x4c00170016007f002a,0x30113022407ff0438,0x26003f0000000b018e,0x7ff018402c2003f0015,0x7ff02c2052806300449,0x2a0630052801840449,0x19003f0034,0x330012000000550069,0x1b001100260068,0x1b30023004e000d003f,0x21c02b901dd01180094,0x1b1019201460147006b,0xe700220000016b01dc,0x10001002a007f0016,0x4c000000690017004c,0x33003a0069007f002a,0x68000000000050,0xce0055007f00330016,0x6900bf003300550000],#[0x7ff01840449052802c2,0x2b0016007f00450630,0xaa007100000008,0x68005500ff009400cc,0x16003300680000,0x3f0019003f002a0034,0x690033008e005500ce,0x34003f002a00190000,0x450016000800000000,0x550000007f007f002b,0x26007f0033003e0068,0x15000b003f,0x330016006900550068,0x4c002a001f00170000,0x7c01c200690000,0x7e006901ff00a90131,0x550033000000000055,0x33006800160068,0x550031001600000068,0x3f0034002a0000007f,0x26000b0000003f0019,0x68003f0015003f,0xb007f003300550016,0x15003f003600260000,0x7f00450016002b0008,0x1840449052802c2007f,0xcc00000071063003c6,0x2a0003009600ff00aa,0x26007f007f0016004c,0x3f0011001b0000000d,0x8a01ef031c00560211,0x45005c002b002b03ff],#[0x33002a00550016007f,0x170017000000160068,0x56004c007f0069002a,0x3ff010c008a01ef0211,0x550033001600000068,0x4c001f002a0017007f,0xcf7067d000000000069,0x550000039f0daf0b6e,0x2110033007f0068003e,0x3ff010c01ef008a0056,0xb003f00150026,0x55007e00680000,0x67106ec03c700330000,0x3f002605db01000000,0xb000b003f00000015,0x150026003f,0x2200c401dc01b1,0x17004c007f002a016b,0x190034002a00000069,0x160017003700090000,0x2b004c007f0069002a,0x16006f0045005c0000,0x33005e00550068,0xb003f002600000000,0x1560000003d0015003f,0xcc0071018301ff00ce,0x7100ff009200aa0000,0xff00aa00cc00000094,0x2280384094a0fff04c1,0x5500cf0033008e0c30,0x3f0000001900000069,0x33008e003f002a0034],#[0xb00000069005500ce,0x3f0026003400000015,0x160033007f00680000,0x26003f000b00150055,0x6ec03c7000000000000,0x9400230671053805db,0x2301ff004e01dd0118,0x1ff01dd004e01180094,0x1ff00a9007c000001c2,0x6900000055008e0131,0x3f0034000000ff0033,0x7ff0449002a003f0019,0x2306300528018402c2,0x1ff011801dd0094004e,0x39402b8026d01e3,0x5500000033008e0146,0x9401b3004e00ff0069,0x211008a011801dd0023,0x11201ef010c005603ff,0x16700c100ab03ff021c,0x19201460001006b021c,0x255bf03e0e0d803003ff,0x3300000068ffff49a3,0x6ff04380055007f0016,0x982018e07ff01130224,0x491025003080c600fff,0xff005500330000008e,0x21c0112031e00ab0069,0x156003d00c10167,0x6ef043801ff018300ce,0x2c1022407ff0113018e,0x4240630055607ff0188],#[0x22406ef018e04380113,0x211008a03ff005607ff,0xa901c2010c01ef,0x4e002301ff0131007c,0x1c2011801dd009401ff,0x1ff013100a90000007c,0x11000000120026000d,0x30809820fff0491003f,0x1ff0023004e0c600250,0x113043801dd01180094,0x21c07ff0224018e02e7,0x192014702b9006b,0x2ed0354033e000001e3,0x211005603ff008a0298,0x394014602b8010c01ef,0x14a04350000026901e3,0x438060c02e601830248,0x22407ff0113018e02c7,0x3f003600150000000b,0x3300000069008e0026,0x1dd0094002300ff0055,0x8a0211004e01ff0118,0x3d010c01ef005603ff,0x1ff01830156000000ce,0xff005500330000008e,0x5380671000003c70069,0x8a01ef005605db06ec,0xb3e0000010c03ff0011,0x28a0dd703cf0c7b06b5,0x4a70460075407540189,0x7ff022406ef018e0113,0x4e01dd009400230438],#[0xb6e0cf7067d011801ff,0x1b10000039f0daf0000,0x21c01ff016b01dc00e6,0xc1016700ab03ff0112,0x228038404c10fff094a,0x39402b801e30c30,0xcf7067d0000026d0146,0x8a02110b6e0daf039f,0x2303ff005601ef010c,0x1ff01dd01180094004e,0x14601e302b8026d0394,0x16702d900ab021c0000,0x394014602b800000112,0x8e0000026d01e3,0x56005500ff00330069,0x10c03ff0211008a01ef,0x51901f306b503ca067c,0x22402c7011304380000,0x3b6053d000007ff018e,0x94002302d701cf067b,0x11801dd004e01ff,0xdaf0b6e0cf7039f067d,0xdaf0000039f0cf7067d,0x5500aa0033008e0b6e,0x67106ec03c700000069,0x2a005505db00000100,0x710016003300680000,0xff00aa0094000000cc,0x2d7000003b6067b053d,0x21c016702dd00ab01cf,0x33008e008e00000112,0x1dd004e006900ff0055],#[0x68011801ff00230094,0x1600330055007f0000,0x3ff010c0056008a0211,0x9401dd0118002301ef,0x11800940023004e01ff,0x4e002301dd01ff004e,0x7101ff009401dd0118,0x9600cc003100aa,0x330055007e0068,0x23004e01ff00940000,0x1830000003d011801dd,0x56021100ce01ff0156,0x1e303ff010c00cf008a,0x146026d02b800000394,0x2e70224018e04380113,0x394026d02b801e107ff,0x21c021c00ab00000146,0x7ff0438016700c10112,0x2c2018e02c701130224,0x7ff0630044905280184,0x147006b00010192021c,0x23011901ff004e03ff,0x7ff02c1018800940000,0x2b801e3063004240556,0x4e039401460000026d,0x1ff0118009401dd0023,0x4c00690016002a0017,0x1dd0094011800230000,0x9401ff004e01ff004e,0x3c7011801dd0023,0x23067106ec053804db,0x1dd01ff0094004e013a],#[0x7f0001002a007f0016,0xcc009400000071004c,0x5db03c7000000aa00ff,0x8a02110538067106ec,0x8e03ff0056014f010c,0x6900df005500330000,0xffff700e255b0e0d8030,0x113022406ef043849a3,0x35e000001e3018e07ff,0x67d000002b8026d0394,0x3c70daf039f0cf70b6e,0x5db05380000067106ec,0x112021c00ab02d90167,0x131007c000001c20000,0x6b0001021c00a901ff,0x1dd004e019203ff0147,0x23009401ff0023013b,0x1ff011801190094004e,0x1dd016b004e00230094,0xcc0096000000710118,0x550000008e00aa00ff,0x4e0023003300ff0069,0x39401ff0118015d0094,0x14601e302b80269,0x3600260015000b,0xa90131000001c2003f,0x1dd013a0023007c01ff,0x3d009401ff004e,0x2300ce01ff01830156,0x1ff004e01dd013a0094,0x7ff043806ef018e0113,0x118004e009400230224],#[0xa9000001c201dd01ff,0xe0d8030013101ff007c,0x438ffff49a3255b700e,0x18e07ff0113022402e7,0x6ec053805db000003c7,0x44907ff02c201840671,0x8a0056021106300528,0x112021c03ff01ef010c,0x300c1016700ab03f7,0x1ff011801dd0094004e,0x15000003b6067b053d,0x2a901cf0000053e01cf,0x94004e002303db0677,0x26000d01ff0118019d,0x3ca000000110012003f,0x51906b501f30474,0x6b014700010192021c,0x19200010147021c03ff,0x255b700e803003ff006b,0x6ff043849a3ffff0e0d,0x34022407ff0113018e,0x3f002a0019003f0000,0x22402e7018e04380113,0x1dc016b00c4002207ff,0x1c200a901c201ff01b1,0xab05750000007c0131,0xc60039f067600ab0358,0x4910250030809820fff,0x330016006800550068,0x4e01ff002300940000,0xab02dd016701dd0118,0x211005600000112021c],#[0x11901ef010c008a03ff,0x9400000023004e01ff,0x26d01e20394014602b8,0x1e301e3039402b80000,0x3f0034002a026d0146,0x4e0023001900090000,0x21c01180095009401ff,0x6b03ff014701920001,0x118009401fb0023004e,0x147006b02b9021c01dd,0x4e013b0023019203ff,0x23004e01dd01ff0094,0x21101ff0094013a01dd,0x10c01ef008a03ff0056,0x9401dd013a004e0023,0x4e01dd013b002301ff,0x120026000d009401ff,0x3f0009003f00000011,0xc1000000190034002a,0x29802ed033e035401e3,0x2b9021c02b801920147,0x68007e00330055006b,0x1ef008a021100000000,0xf03e8030005603ff010c,0x43849a3ffff0e0d255b,0x7ff0224018e02c70113,0xffff700e49a30e0d8030,0x113022402c70438255b,0xe0db65c49a3018e07ff,0x39401e3700e255b8030,0x4380000026d02b80146,0x2c7018e022407ff0113]]
abbrev CellID := Fin 400
def cellData (j : CellID) := (chartTeaching[j.val]?).getD (0,0,0)
def cellRaw (j : CellID) : List Probe32 := List.ofFn (fun t : Fin 6 =>
  let n := (cellData j).2.1
  let small := packedAt teachingRawPack ((6*j.val+t.val)*16) 16
  BitVec.ofNat 32 (small ||| (if small % 2 = 1 then (4294967296-2^n) else 0)))
def cellTest (j : CellID) : Bool :=
  let w := cellData j
  let s := selectTeaching w.1
  let r := tileRows w
  viewBank32 r (wiresOf g63) == cellRaw j &&
    (sample32 r (targetOf g63) == s.out || sample32 r (targetOf g63) == ~~~s.out)
def cacheTeaching (k i : Nat) : Bool :=
  let j : CellID := Fin.ofNat _ (pickTeaching k i)
  let w := cellData j
  cachePass g63 k i (cellRaw j) (tileRows w) (selectTeaching w.1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
example : ∀ j : CellID, cellTest j=true := by decide +kernel
end Nat92GE
end PEqualNP.Outside.L_meta_43236
